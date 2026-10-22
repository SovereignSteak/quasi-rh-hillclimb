import Mathlib

set_option autoImplicit false

namespace IndependentAudit

def Target : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    (8747729897 / 10000000000 : ℝ) < s.re →
    ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0

end IndependentAudit
