/- Copyright (c) 2026 Sil. Apache-2.0.
The Dirichlet boundary 174797/200000 from the diagonal supplier of the cube-free
step: every step's raw-side provider is `contrary_raw_side_provider` from the
step's Seam A leaf (proved in `Assembly/Leaves`) and the diagonal supplier. -/
import Submissions.density_split_third_20261026.CubeFree.Assembly.Final
import Submissions.density_split_third_20261026.CubeFree.Second.ProviderGeoSupply

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Assembly
open QRH.DensitySplitThird.CubeFree.Second.Provider

theorem dirichlet_of_diag
    (hdiag : ∀ (D : StepData) (G : StepGates D), DiagSupply G)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174797 / 200000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_of_providers
    (fun _ _ _ h => ⟨4, fun _ hleaf =>
      contrary_raw_side_provider (stepGates_of_native h) 4 le_rfl hleaf (hdiag _ _)⟩)
    ⟨4, fun _ hleaf => contrary_raw_side_provider _ 4 le_rfl hleaf (hdiag _ _)⟩
    ⟨4, fun _ hleaf => contrary_raw_side_provider _ 4 le_rfl hleaf (hdiag _ _)⟩
    ⟨4, fun _ hleaf => contrary_raw_side_provider _ 4 le_rfl hleaf (hdiag _ _)⟩
    χ hs hpole

end QRH.DensitySplitThird.CubeFree.Assembly
