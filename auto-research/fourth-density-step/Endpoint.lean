/- Copyright (c) 2026 Sil. Apache-2.0.
The Dirichlet nonvanishing boundary 174797/200000 from the two generic source
steps: the native cube-free common-divisor step and the two variable-density
transitions. Everything else in the chain (initial fourth-power source, finite
native bootstrap, subface inclusions, final return, Dirichlet transfer) is proved. -/
import Submissions.density_split_third_20261026.Source.Assembly
import Submissions.density_split_third_20261026.Return.Endpoint

set_option autoImplicit false
namespace QRH.DensitySplitThird

theorem dirichlet_of_steps (hstep : NativeStepStatement)
    (h1 : HybridStepFor bootstrapFace hybridFace1 (6/5) 140)
    (h2 : HybridStepFor hybridFace1 hybridFace2 (7/10) 70)
    (h3 : HybridStepFor hybridFace2 hybridFace3 (3/5) 35)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174797 / 200000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Return.dirichlet_of_source (fun hβ => final_source hstep h1 h2 h3 hβ) χ hs hpole

end QRH.DensitySplitThird
