-- Written for this audit, independently of PR #8/#10. Mathlib-only statement.
import Mathlib.NumberTheory.LSeries.DirichletContinuation
set_option autoImplicit false
namespace QRHAudit
/-- Tracker canonical challenge (verifier/upstream-challenge.lean, sha 8fb13ad9…) with 7/8 replaced by the PR #8 boundary. -/
def Target : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    (8747729897 / 10000000000 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0
/-- Corollary sanity target: ζ is the L-function of the trivial character mod 1. -/
def ZetaTarget : Prop := ∀ {s : ℂ}, (8747729897 / 10000000000 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0
end QRHAudit
