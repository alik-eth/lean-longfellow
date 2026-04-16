import LeanLongfellow.Circuit.ECDSA.Spec
import LeanLongfellow.Circuit.ECDSA.Circuit
import LeanLongfellow.Circuit.ECDSA.FieldOps
import LeanLongfellow.Circuit.ECDSA.PointOps
import LeanLongfellow.Circuit.ECDSA.EqualityCheck
import LeanLongfellow.Circuit.EC.ScalarMul

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Circuit Composition

Assembles a concrete `ECDSACircuitSpec` instance with a proven non-vacuous
`extraction` field.

## Architecture: Non-Vacuous Extraction Circuit

The circuit has NL = 1 layer with s = 1 (2 wires per layer).  The single
layer embeds the ECDSA verification predicate through a coefficient in
`add_poly`:

  `coefficient = sig.s * xCoordCheck`

where `xCoordCheck = 1` when the abstract x-coordinate check passes, and
`xCoordCheck = 0` otherwise.

### Soundness

Layer consistency at wire 0 gives:

  `V₀(wire0) = coefficient · (V₁(wire0) + V₁(wire1))`

Wire 1 is uncovered, so `V₀(wire1) = 0`.  If `eval = 1`, then
`V₀(wire0) ≠ 0`, hence `coefficient ≠ 0`, which forces both
`sig.s ≠ 0` and the x-coordinate match — exactly `ecdsaVerify`.

### Completeness

If `ecdsaVerify z Q sig` holds, set `V₁(wire0) = sig.s⁻¹` and
`V₁(wire1) = 0`.  Then `V₀(wire0) = 1` and `eval(boolToField wire0) = 1`.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: The ECDSA recovery point and x-coordinate
-- ============================================================

/-- The ECDSA recovery point R = u₁·G + u₂·Q where u₁ = z·s⁻¹ mod n,
    u₂ = r·s⁻¹ mod n, with arithmetic in `ZMod groupOrder`. -/
noncomputable def ecdsaRecoveryPoint [ec : EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) :
    EllipticCurve.Point (F := F) :=
  let n := ec.groupOrder
  have : Fact (Nat.Prime n) := ec.hGroupOrder
  let z_n : ZMod n := (ec.fieldToNat z : ZMod n)
  let r_n : ZMod n := (ec.fieldToNat sig.r : ZMod n)
  let s_n : ZMod n := (ec.fieldToNat sig.s : ZMod n)
  let s_inv := s_n⁻¹
  let u₁ := z_n * s_inv
  let u₂ := r_n * s_inv
  EllipticCurve.pointAdd
    (EllipticCurve.scalarMul (ZMod.val u₁) EllipticCurve.generator)
    (EllipticCurve.scalarMul (ZMod.val u₂) Q)

/-- The x-coordinate of the recovery point. -/
noncomputable def ecdsaRecoveryXCoord [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) : F :=
  EllipticCurve.xCoord (ecdsaRecoveryPoint z Q sig)

/-- `ecdsaVerify` unfolds to `sig.s ≠ 0 ∧ ecdsaRecoveryXCoord z Q sig = sig.r`. -/
theorem ecdsaVerify_iff [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) :
    ecdsaVerify z Q sig ↔
    sig.s ≠ 0 ∧ ecdsaRecoveryXCoord z Q sig = sig.r := by
  unfold ecdsaVerify ecdsaRecoveryXCoord ecdsaRecoveryPoint
  simp only

-- ============================================================
-- Section 2: Coefficient and layer construction
-- ============================================================

open Classical in
/-- The indicator for the x-coordinate check: 1 if xCoord(R) = sig.r, 0 otherwise. -/
noncomputable def xCoordIndicator [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) : F :=
  if ecdsaRecoveryXCoord z Q sig = sig.r then 1 else 0

/-- The coefficient: `sig.s * xCoordIndicator`. -/
noncomputable def ecdsaCoefficient [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) : F :=
  sig.s * xCoordIndicator z Q sig

theorem ecdsaCoefficient_ne_zero_s [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (h : ecdsaCoefficient z Q sig ≠ 0) : sig.s ≠ 0 := by
  intro hs; apply h; unfold ecdsaCoefficient; rw [hs, zero_mul]

open Classical in
theorem ecdsaCoefficient_ne_zero_xcoord [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (h : ecdsaCoefficient z Q sig ≠ 0) :
    ecdsaRecoveryXCoord z Q sig = sig.r := by
  by_contra hne; apply h
  unfold ecdsaCoefficient xCoordIndicator; rw [if_neg hne, mul_zero]

theorem ecdsaCoefficient_ne_zero_verify [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (h : ecdsaCoefficient z Q sig ≠ 0) :
    ecdsaVerify z Q sig := by
  rw [ecdsaVerify_iff]
  exact ⟨ecdsaCoefficient_ne_zero_s z Q sig h,
         ecdsaCoefficient_ne_zero_xcoord z Q sig h⟩

section PedagogicalToyCircuit
/-! ### Pedagogical 1-layer circuit (NL=1, s=1)

    This is the simplest working example of an `ECDSACircuitSpec` instance.
    It demonstrates non-vacuous extraction with a single layer.
    It is NOT used in the end-to-end proof chain — see
    `GateComposition.lean` for the gate-level circuit (NL=14n+7, s=5). -/

open Classical in
theorem ecdsaCoefficient_of_verify [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (hv : ecdsaVerify z Q sig) :
    ecdsaCoefficient z Q sig = sig.s := by
  have ⟨_, hxr⟩ := (ecdsaVerify_iff z Q sig).mp hv
  unfold ecdsaCoefficient xCoordIndicator; rw [if_pos hxr, mul_one]

-- ============================================================
-- Section 3: The circuit layer
-- ============================================================

/-- The canonical triple `(g=wire0, l=wire0, r=wire1)` as a `Fin 3 → Bool` vector. -/
private def targetTriple : Fin (3 * 1) → Bool := concat3 wire0 wire0 wire1

/-- The single circuit layer for the non-vacuous ECDSA circuit.
    `add_poly` has one nonzero entry at `targetTriple` with value `ecdsaCoefficient`. -/
noncomputable def ecdsaRealLayer [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) :
    CircuitLayer F 1 where
  add_poly := ⟨fun glr =>
    if glr = targetTriple then ecdsaCoefficient z Q sig else 0⟩
  mul_poly := ⟨fun _ => 0⟩

-- ============================================================
-- Section 4: Wire and triple helpers
-- ============================================================

private theorem wire0_ne_wire1' : (wire0 : Fin 1 → Bool) ≠ wire1 := by
  intro h; have := congrFun h 0; simp [wire0, wire1] at this

private theorem wire_cases' (f : Fin 1 → Bool) : f = wire0 ∨ f = wire1 := by
  rcases hf : f 0 with _ | _
  · left; funext ⟨i, hi⟩
    have : (⟨i, hi⟩ : Fin 1) = (0 : Fin 1) := Fin.ext (by omega)
    rw [show f ⟨i, hi⟩ = f 0 from congrArg f this]; exact hf
  · right; funext ⟨i, hi⟩
    have : (⟨i, hi⟩ : Fin 1) = (0 : Fin 1) := Fin.ext (by omega)
    rw [show f ⟨i, hi⟩ = f 0 from congrArg f this]; exact hf

/-- concat3 wire1 l r ≠ targetTriple for any l, r (first component mismatch). -/
private theorem concat3_wire1_ne_tt (l r : Fin 1 → Bool) :
    concat3 wire1 l r ≠ targetTriple := by
  intro heq
  have := congrFun heq ⟨0, by omega⟩
  simp [concat3, wire1, targetTriple, wire0] at this

/-- concat3 wire0 wire0 wire1 = targetTriple (definitionally). -/
private theorem tt_eq : concat3 wire0 wire0 wire1 = targetTriple := rfl

-- ============================================================
-- Section 5: The canonical lr pair and its properties
-- ============================================================

/-- The lr pair corresponding to (l=wire0, r=wire1). -/
private def lr₀ : Fin (2 * 1) → Bool := fun k =>
  if k.val = 0 then false else true

private theorem lr₀_splitL : splitL lr₀ = wire0 := by
  funext ⟨j, hj⟩; simp [splitL, lr₀, wire0]; omega

private theorem lr₀_splitR : splitR lr₀ = wire1 := by
  funext ⟨j, hj⟩
  simp only [splitR, lr₀, wire1]
  have hj0 : j = 0 := by omega
  subst hj0; rfl

private theorem lr₀_concat3_eq_tt :
    concat3 wire0 (splitL lr₀) (splitR lr₀) = targetTriple := by
  rw [lr₀_splitL, lr₀_splitR]; rfl

/-- If splitL lr = wire0 and splitR lr = wire1, then lr = lr₀. -/
private theorem lr_unique_of_splits (lr : Fin (2 * 1) → Bool)
    (hL : splitL lr = wire0) (hR : splitR lr = wire1) : lr = lr₀ := by
  funext ⟨k, hk⟩
  simp only [lr₀]
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · -- k = 0: lr(0) = splitL lr ⟨0, _⟩ = wire0 ⟨0, _⟩ = false
    have := congrFun hL ⟨0, by omega⟩
    simp [splitL, wire0] at this; simp [this]
  · -- k = 1: lr(1) = splitR lr ⟨0, _⟩ = wire1 ⟨0, _⟩ = true
    have := congrFun hR ⟨0, by omega⟩
    simp [splitR, wire1] at this; simp [this]

/-- For lr ≠ lr₀, concat3 wire0 (splitL lr) (splitR lr) ≠ targetTriple. -/
private theorem concat3_ne_tt_of_ne_lr₀ (lr : Fin (2 * 1) → Bool) (hlr : lr ≠ lr₀) :
    concat3 wire0 (splitL lr) (splitR lr) ≠ targetTriple := by
  intro heq
  apply hlr
  -- From concat3 wire0 (splitL lr) (splitR lr) = concat3 wire0 wire0 wire1,
  -- injectivity of concat3 gives splitL lr = wire0 and splitR lr = wire1
  have hL : splitL lr = wire0 := by
    funext ⟨j, hj⟩
    have hj0 : j = 0 := by omega
    subst hj0
    have := congrFun heq ⟨1, by omega⟩
    simp [concat3, targetTriple, splitL, wire0] at this ⊢
    exact this
  have hR : splitR lr = wire1 := by
    funext ⟨j, hj⟩
    have hj0 : j = 0 := by omega
    subst hj0
    have := congrFun heq ⟨2, by omega⟩
    simp [concat3, targetTriple, splitR, wire1] at this ⊢
    exact this
  exact lr_unique_of_splits lr hL hR

-- ============================================================
-- Section 6: Layer consistency analysis
-- ============================================================

/-- Wire 1 is uncovered: V_curr(wire1) = 0. -/
private theorem ecdsaRealLayer_wire1_zero [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (V_curr V_next : LayerValues F 1)
    (hcons : ∀ g, layerConsistent (ecdsaRealLayer z Q sig) V_curr V_next g) :
    V_curr.table wire1 = 0 := by
  have h := hcons wire1
  simp only [layerConsistent, ecdsaRealLayer] at h
  rw [h]
  apply Finset.sum_eq_zero
  intro lr _
  have hne := concat3_wire1_ne_tt (splitL lr) (splitR lr)
  simp [hne]

/-- The consistency equation at wire0. -/
private theorem ecdsaRealLayer_wire0_eq [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (V_curr V_next : LayerValues F 1)
    (hcons : ∀ g, layerConsistent (ecdsaRealLayer z Q sig) V_curr V_next g) :
    V_curr.table wire0 =
    ecdsaCoefficient z Q sig * (V_next.table wire0 + V_next.table wire1) := by
  have h := hcons wire0
  simp only [layerConsistent, ecdsaRealLayer] at h
  rw [h]; clear h
  -- Isolate the lr₀ term using sum_eq_single
  rw [Finset.sum_eq_single lr₀]
  · -- Main term: lr = lr₀
    rw [lr₀_splitL, lr₀_splitR]
    have : concat3 wire0 wire0 wire1 = targetTriple := rfl
    rw [this]; simp
  · -- Off-diagonal: lr ≠ lr₀
    intro lr _ hlr
    have hne := concat3_ne_tt_of_ne_lr₀ lr hlr
    simp [hne]
  · -- lr₀ ∈ univ
    simp

/-- If eval = 1 and wire1 = 0, then wire0 ≠ 0. -/
private theorem eval_one_wire0_ne_zero (p : MultilinearPoly F 1)
    (h1 : p.table wire1 = 0) (target : Fin 1 → F)
    (heval : p.eval target = 1) : p.table wire0 ≠ 0 := by
  intro h0
  have : p.eval target = 0 := by
    unfold MultilinearPoly.eval
    apply Finset.sum_eq_zero
    intro b _
    rcases wire_cases' b with rfl | rfl
    · rw [h0, zero_mul]
    · rw [h1, zero_mul]
  rw [this] at heval; exact one_ne_zero heval.symm

-- ============================================================
-- Section 7: The concrete non-vacuous ECDSACircuitSpec
-- ============================================================

/-- The non-vacuous ECDSA circuit specification.

    **Soundness (extraction):** consistency + output = 1 implies
    `ecdsaCoefficient ≠ 0`, which implies `ecdsaVerify z Q sig`.

    **Completeness:** see `ecdsaCircuitSpec_complete`. -/
noncomputable def ecdsaCircuitSpec [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) :
    ECDSACircuitSpec F 1 1 z Q sig where
  layers := fun _ => ecdsaRealLayer z Q sig
  extraction := by
    intro values target hcons hout
    have hcons_all : ∀ g, layerConsistent (ecdsaRealLayer z Q sig)
        (values ⟨0, by omega⟩) (values ⟨1, by omega⟩) g := by
      intro g; have := hcons ⟨0, by omega⟩ g; convert this using 2
    have hw1 := ecdsaRealLayer_wire1_zero z Q sig
      (values ⟨0, by omega⟩) (values ⟨1, by omega⟩) hcons_all
    have hw0_ne := eval_one_wire0_ne_zero (values ⟨0, by omega⟩) hw1 target hout
    have hw0_eq := ecdsaRealLayer_wire0_eq z Q sig
      (values ⟨0, by omega⟩) (values ⟨1, by omega⟩) hcons_all
    have hcoeff : ecdsaCoefficient z Q sig ≠ 0 := by
      intro h0; apply hw0_ne; rw [hw0_eq, h0, zero_mul]
    exact ecdsaCoefficient_ne_zero_verify z Q sig hcoeff

-- ============================================================
-- Section 8: Completeness theorem
-- ============================================================

/-- Helper: the layerConsistent equation for a specific (V_out, V_in, g) at wire0
    in the ecdsaRealLayer, with V_out(wire0) = coeff * (V_in(wire0) + V_in(wire1)). -/
private theorem ecdsaRealLayer_consistency_wire0 [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (V_out V_in : LayerValues F 1)
    (h : V_out.table wire0 =
         ecdsaCoefficient z Q sig * (V_in.table wire0 + V_in.table wire1))
    (h1 : V_out.table wire1 = 0) :
    ∀ g, layerConsistent (ecdsaRealLayer z Q sig) V_out V_in g := by
  intro g
  simp only [layerConsistent, ecdsaRealLayer]
  rcases wire_cases' g with rfl | rfl
  · -- g = wire0
    rw [h]
    rw [Finset.sum_eq_single lr₀]
    · rw [lr₀_splitL, lr₀_splitR]; simp [tt_eq]
    · intro lr _ hlr
      have hne := concat3_ne_tt_of_ne_lr₀ lr hlr
      simp [hne]
    · simp
  · -- g = wire1
    rw [h1]; symm
    apply Finset.sum_eq_zero
    intro lr _
    have hne := concat3_wire1_ne_tt (splitL lr) (splitR lr)
    simp [hne]

/-- **Completeness:** If `ecdsaVerify z Q sig` holds, there exist wire
    values making the circuit consistent with output evaluating to 1. -/
theorem ecdsaCircuitSpec_complete [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (hv : ecdsaVerify z Q sig) :
    ∃ (values : Fin 2 → LayerValues F 1),
      (∀ k : Fin 1, ∀ g : Fin 1 → Bool,
        layerConsistent ((ecdsaCircuitSpec z Q sig).layers k)
          (values k.castSucc) (values k.succ) g) ∧
      (values ⟨0, by omega⟩).eval (boolToField wire0) = 1 := by
  have hcoeff : ecdsaCoefficient z Q sig = sig.s :=
    ecdsaCoefficient_of_verify z Q sig hv
  have hs_ne : sig.s ≠ 0 := ((ecdsaVerify_iff z Q sig).mp hv).1
  -- Define wire values
  let V_in : LayerValues F 1 := ⟨fun b => if b = wire0 then sig.s⁻¹ else 0⟩
  let V_out : LayerValues F 1 := ⟨fun b => if b = wire0 then 1 else 0⟩
  let values : Fin 2 → LayerValues F 1 := fun k =>
    if k.val = 0 then V_out else V_in
  use values
  refine ⟨?_, ?_⟩
  · -- Layer consistency
    intro ⟨k, hk⟩ g
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [ecdsaCircuitSpec, values]
    show layerConsistent (ecdsaRealLayer z Q sig) V_out V_in g
    have hw1_ne_w0 : wire1 ≠ wire0 := fun h => wire0_ne_wire1' h.symm
    apply ecdsaRealLayer_consistency_wire0
    · -- V_out(wire0) = coeff * (V_in(wire0) + V_in(wire1))
      show (if wire0 = wire0 then (1 : F) else 0) =
        ecdsaCoefficient z Q sig *
          ((if wire0 = wire0 then sig.s⁻¹ else 0) +
           (if wire1 = wire0 then sig.s⁻¹ else 0))
      rw [if_pos rfl, if_pos rfl, if_neg hw1_ne_w0, hcoeff, add_zero, mul_inv_cancel₀ hs_ne]
    · -- V_out(wire1) = 0
      show (if wire1 = wire0 then (1 : F) else 0) = 0
      rw [if_neg hw1_ne_w0]
  · -- Output evaluation = 1
    show V_out.eval (boolToField wire0) = 1
    rw [eval_boolVec]; simp [V_out]

-- ============================================================
-- Section 9: Convenience theorems
-- ============================================================

/-- The extraction property holds. -/
theorem ecdsaCircuitSpec_sound [EllipticCurveGroup F]
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (values : Fin 2 → LayerValues F 1) (target : Fin 1 → F)
    (hcons : ∀ k : Fin 1, ∀ g : Fin 1 → Bool,
      layerConsistent ((ecdsaCircuitSpec z Q sig).layers k)
        (values k.castSucc) (values k.succ) g)
    (hout : (values ⟨0, by omega⟩).eval target = 1) :
    ecdsaVerify z Q sig :=
  (ecdsaCircuitSpec z Q sig).extraction values target hcons hout

-- ============================================================
-- Section 10: Integration with Longfellow soundness
-- ============================================================

/-- If the GKR verifier accepts but ECDSA doesn't verify, a sumcheck
    challenge hit a root. -/
theorem ecdsaComposition_longfellow_soundness [DecidableEq F] [EllipticCurveGroup F]
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (values : Fin 2 → LayerValues F 1)
    (targets : Fin 1 → (Fin 1 → F))
    (claimed_vals : Fin 1 → F)
    (reductions : Fin 1 → LayerReduction F 1)
    (hcons : ∀ k : Fin 1, ∀ g : Fin 1 → Bool,
      layerConsistent ((ecdsaCircuitSpec z Q sig).layers k)
        (values k.castSucc) (values k.succ) g)
    (haccept : ∀ k : Fin 1,
      layerReductionAccepts ((ecdsaCircuitSpec z Q sig).layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k))
    (hdeg : ∀ k : Fin 1, ∀ i : Fin (2 * 1),
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    (hclaim : claimed_vals ⟨0, by omega⟩ = 1)
    (hfalse : ¬ ecdsaVerify z Q sig) :
    ∃ k : Fin 1, ∃ i : Fin (2 * 1), ∃ diff : Polynomial F,
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((reductions k).rounds i).challenge = 0 :=
  ecdsa_longfellow_soundness (ecdsaCircuitSpec z Q sig) values targets
    claimed_vals reductions (by omega) (by omega) hcons haccept hdeg hclaim hfalse

end PedagogicalToyCircuit
