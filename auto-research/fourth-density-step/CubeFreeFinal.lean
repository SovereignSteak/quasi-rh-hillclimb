/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L: the target statement from the remaining step inputs.

`dirichlet_of_step_inputs` is the Candidate-shaped theorem (Dirichlet `L`-functions do not
vanish for `Re s > 174797/200000`, away from the pole) conditional only on
`CubeFree.AllStepInputs`: the root chain's restricted source for every native step and for
the two density transitions. It joins `Endpoint.dirichlet_of_steps` (PR76 source, bootstrap,
return) with `CubeFree.Step`.

This module necessarily sees both PR76's FP source (through `Source.Assembly`) and the
cube-free forks; it opens no FP or fork namespace. -/
import Submissions.density_split_third_20261026.Endpoint
import Submissions.density_split_third_20261026.CubeFree.Assembly.Provider

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Assembly

/-- The native step statement of `Source.Assembly` from the native inputs. -/
theorem nativeStepStatement_of_inputs (I : NativeInputs) : NativeStepStatement :=
  fun p n a h hβ hp => native_step I p n a h hβ hp

/-- **Conditional target**: Dirichlet nonvanishing for `Re s > 174797/200000` from the
remaining step inputs. -/
theorem dirichlet_of_step_inputs (I : AllStepInputs)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174797 / 200000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_of_steps (nativeStepStatement_of_inputs I.native)
    (fun hβ hp => hybrid_step_first I.first hβ hp)
    (fun hβ hp => hybrid_step_second I.second hβ hp)
    (fun hβ hp => hybrid_step_third I.third hβ hp) χ hs hpole

/-- **Conditional target from the root chain's providers** (WP-M's `contrary_raw_side_provider`
for the native steps with the parent leaf and for the two density steps with the density
leaves). -/
theorem dirichlet_of_providers
    (hnat : ∀ (p n : Face) (a : ℝ) (h : NativeGates p n a), ∃ Lplain : ℝ,
      QRH.Record1252270103Source.GlobalSource p.B p.L p.c →
      PricedPackedSource (nativeData p n a h).price (nativeData p n a h).Hmin
        ((nativeData p n a h).Hmax+1) Lplain →
      FP.RepairedSourceSideSupply.ContraryRawSideProvider (stepGates_of_native h))
    (h1 : ∃ Lplain : ℝ, QRH.Record1252270103Source.GlobalSource dsFirst.B₀ dsFirst.L₀ dsFirst.c₀ →
      PricedPackedSource dsFirst.price dsFirst.Hmin (dsFirst.Hmax+1) Lplain →
      FP.RepairedSourceSideSupply.ContraryRawSideProvider Density.dsGates_first)
    (h2 : ∃ Lplain : ℝ,
      QRH.Record1252270103Source.GlobalSource dsSecond.B₀ dsSecond.L₀ dsSecond.c₀ →
      PricedPackedSource dsSecond.price dsSecond.Hmin (dsSecond.Hmax+1) Lplain →
      FP.RepairedSourceSideSupply.ContraryRawSideProvider Density.dsGates_second)
    (h3 : ∃ Lplain : ℝ,
      QRH.Record1252270103Source.GlobalSource dsThird.B₀ dsThird.L₀ dsThird.c₀ →
      PricedPackedSource dsThird.price dsThird.Hmin (dsThird.Hmax+1) Lplain →
      FP.RepairedSourceSideSupply.ContraryRawSideProvider Density.dsGates_third)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174797 / 200000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_of_step_inputs (allStepInputs_of_providers hnat h1 h2 h3) χ hs hpole

end QRH.DensitySplitThird.CubeFree.Assembly
