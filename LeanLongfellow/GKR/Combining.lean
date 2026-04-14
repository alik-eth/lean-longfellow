import LeanLongfellow.GKR.Circuit
import LeanLongfellow.MLE.Props

open Finset MultilinearPoly

variable {F : Type*} [Field F] {k depth : ℕ}

/-- The combining polynomial for GKR at layer j, given random point g*.
    f(l, r) = Q[j](g*, l, r) · V[j+1](l) · V[j+1](r) -/
def combiningPoly (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F) : MultilinearPoly F (2 * k) where
  table b_lr :=
    let lr_field := boolToField (F := F) b_lr
    let l : Fin k → F := fun i => lr_field (Fin.cast (by omega) (Fin.castAdd k i))
    let r : Fin k → F := fun i => lr_field (Fin.cast (by omega) (Fin.natAdd k i))
    let glr : Fin (3 * k) → F := fun i =>
      if h : i.val < k then gStar ⟨i.val, h⟩
      else lr_field ⟨i.val - k, by omega⟩
    (circuit.quads j).quad.eval glr *
    (circuit.wires ⟨j.val + 1, by omega⟩).eval l *
    (circuit.wires ⟨j.val + 1, by omega⟩).eval r

/-- When a layer is consistent at g*, the combining polynomial's hypercube sum
    equals V[j](g*). -/
theorem combiningPoly_sum (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F)
    (hcons : layerConsistentAt circuit j gStar) :
    ∑ b : Fin (2 * k) → Bool, (combiningPoly circuit j gStar).table b =
      (circuit.wires (Fin.castSucc j)).eval gStar :=
  hcons.symm

/-- Contrapositive: if the hypercube sum differs from V[j](g*),
    the layer is not consistent at g*. -/
theorem combiningPoly_sum_ne (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F)
    (hne : ∑ b : Fin (2 * k) → Bool, (combiningPoly circuit j gStar).table b ≠
      (circuit.wires (Fin.castSucc j)).eval gStar) :
    ¬ layerConsistentAt circuit j gStar :=
  fun hcons => hne (combiningPoly_sum circuit j gStar hcons)
