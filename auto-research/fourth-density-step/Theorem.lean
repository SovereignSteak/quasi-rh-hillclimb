/- Copyright (c) 2026 Sil. Apache-2.0.
Unconditional Dirichlet nonvanishing for Re s > 174797/200000, with the principal
pole excluded: the density-split common-divisor bootstrap closed by the diagonal
supplier of the cube-free step. -/
import Submissions.density_split_third_20261026.CubeFree.Assembly.Closed
import Submissions.density_split_third_20261026.CubeFree.Second.ProviderDiag9

set_option autoImplicit false
namespace QRH.DensitySplitThird

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174797 / 200000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  CubeFree.Assembly.dirichlet_of_diag
    (fun _ G => CubeFree.Second.ProviderDiag.diag_supply G) χ hs hpole

end QRH.DensitySplitThird
