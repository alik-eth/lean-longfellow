import LeanLongfellow.Ligero.Constraints

variable {F : Type*} [Field F]

/-- Abstract Ligero commitment scheme interface.
    Parameterized by field F and dimensions n (witness), m (linear), q (quadratic).

    This typeclass is an abstraction boundary.  The actual binding proof goes
    through the probabilistic path: `niLigero_binding_or_bad` (in
    `ProbabilisticBinding.lean`) proves binding from first principles with
    concrete error bounds, bypassing this typeclass entirely.  The
    `trivialLigeroScheme` instance in `Soundness.lean` witnesses inhabitedness. -/
class LigeroScheme (F : Type*) [Field F] (n m q : ℕ) where
  Commitment : Type
  Proof : Type
  commit : (Fin n → F) → Commitment
  verify : Commitment → LinearConstraints F m n →
           (Fin q → QuadConstraint n) → Proof → Prop
  /-- Binding: if verify accepts on commit(w), then w satisfies all constraints. -/
  binding : ∀ (w : Fin n → F) (lcs : LinearConstraints F m n)
              (qcs : Fin q → QuadConstraint n) (π : Proof),
    verify (commit w) lcs qcs π → satisfiesAll w lcs qcs
