/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L (B): the step inputs from the raw-side provider of the root chain.

WP-K2b's top statement `RepairedSourceSetupBound.uniform_setup_of_side_provider` bounds the
literal restored row of every root `Setup M H D` with `s₀ ≤ markedWidth`, given a
`ProviderAt G (ε/12) meshCap`. As in FP's `restricted_unit_source_of_raw_sides`, the restricted
input data of one restored row `(T, w, r, A)` is packed into a `Setup` (window cap
`windowCap G N (ε/12)`, mesh `min (mesh G (ε/12)) meshCap` chosen after `ε`, before the slot
type), which gives `HighRestrictedUnitSource` (the row width condition `s₀ ≤ rowWidth` is the
setup's `s₀ ≤ markedWidth`). Hence `StepInputs` follows from a provider, and the whole chain
from providers for all steps. -/
import Submissions.density_split_third_20261026.CubeFree.Step
import Submissions.density_split_third_20261026.CubeFree.FP.RepairedSourceSetupBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Assembly
noncomputable section
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.DensitySplitThird.CubeFree.FP
open KernelCollisionEnergy RestoredInitialSource RestoredRootEnergy RecenteredRootSetup
open RepairedSourceSideSupply RepairedSourceSetupBound RepairedSourceRootGeometry
open QRH.DensitySplitThird.CubeFree.RootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

set_option maxHeartbeats 1600000 in
/-- **The root chain's provider gives the high restricted source.** -/
theorem high_of_provider {D : StepData} (G : StepGates D) (hsupply : ContraryRawSideProvider G)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    HighRestrictedUnitSource (globalFace D.B D.L D.c) D.s₀ := by
  intro ε hε
  obtain ⟨meshCap, hmc, hP⟩ := setup_mesh_of_contrary G hsupply hβ ε hε
  have hε12 : 0 < ε/12 := by positivity
  refine ⟨min (mesh G (ε/12)) meshCap, lt_min (mesh_spec G (ε/12) hε12).1 hmc, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  have : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  have hQM : internalQ Q η₀ ≤ rayM := inf_le_left.trans hQray
  have hQη : internalQ Q η₀ ≤ η₀.modulus := inf_le_right
  obtain ⟨J, control, C, hC, hbound⟩ := uniform_setup_of_side_provider G ε hε meshCap hP α
    rayM H hH W hW hWs bΦ hbΦ η η₀ (internalQ Q η₀) hQt hQ72 hQM hQη
  refine ⟨J, control, C, hC, ?_⟩
  filter_upwards [hbound] with Z hz
  intro T w r A hs₀ θ σ v t height hw hwm hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm
    rows tc ti hti Y₁ Y₂ hY₁ hy₁ hY₂ hy₂
  let s : Setup rayM H D T :=
    { Z := Z
      hZ := by linarith [hz.1]
      Lcap := windowCap G (Fintype.card α) (ε/12)
      hLcap := windowCap_ge_eight G _ (ε/12) hε12
      W := W
      hW := hW.continuous
      hWs := hWs
      η₀ := η₀
      θ := θ
      w := w
      σ := σ
      v := v
      hw := hw
      hσlo := hσlo
      hσhi := hσhi
      t := t
      p := p
      X₁ := X₁
      X₂ := X₂
      Y₁ := Y₁
      Y₂ := Y₂
      hY₁ := hY₁
      hY₂ := hY₂
      hy₁ := hy₁
      hy₂ := hy₂
      hface := hadm
      hD := face_facts G
      r := r
      tc := tc
      A := A
      ti := ti }
  have hmw : D.s₀ ≤ markedWidth rayM H s := by
    change D.s₀ ≤ ∑ i : RestoredRootDictionary.remainingSet r A, w i.val
    rw [Finset.sum_coe_sort (RestoredRootDictionary.remainingSet r A) w,
      ← RestoredRootDictionary.remaining_sum r A w]
    exact hs₀
  exact hz.2 T s rfl rfl rfl rfl height hh hv hwm hmw Q Φ hΦ hΦp rows

/-- **`StepInputs` from the root chain's provider** (the provider may use the parent source
and the Seam A leaf of the step). -/
theorem step_inputs_of_provider (D : StepData) (G : StepGates D) (Lplain : ℝ)
    (hprov : GlobalSource D.B₀ D.L₀ D.c₀ →
      PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain → ContraryRawSideProvider G) :
    StepInputs D G Lplain :=
  ⟨fun hβ hparent hleaf => high_of_provider G (hprov hparent hleaf) hβ⟩

/-- **All step inputs from providers** for every native step and the two density steps. -/
theorem allStepInputs_of_providers
    (hnat : ∀ (p n : Face) (a : ℝ) (h : NativeGates p n a), ∃ Lplain : ℝ,
      GlobalSource p.B p.L p.c →
      PricedPackedSource (nativeData p n a h).price (nativeData p n a h).Hmin
        ((nativeData p n a h).Hmax+1) Lplain → ContraryRawSideProvider (stepGates_of_native h))
    (h1 : ∃ Lplain : ℝ, GlobalSource dsFirst.B₀ dsFirst.L₀ dsFirst.c₀ →
      PricedPackedSource dsFirst.price dsFirst.Hmin (dsFirst.Hmax+1) Lplain →
      ContraryRawSideProvider Density.dsGates_first)
    (h2 : ∃ Lplain : ℝ, GlobalSource dsSecond.B₀ dsSecond.L₀ dsSecond.c₀ →
      PricedPackedSource dsSecond.price dsSecond.Hmin (dsSecond.Hmax+1) Lplain →
      ContraryRawSideProvider Density.dsGates_second)
    (h3 : ∃ Lplain : ℝ, GlobalSource dsThird.B₀ dsThird.L₀ dsThird.c₀ →
      PricedPackedSource dsThird.price dsThird.Hmin (dsThird.Hmax+1) Lplain →
      ContraryRawSideProvider Density.dsGates_third) :
    AllStepInputs where
  native := fun p n a h => by
    obtain ⟨Lplain, hp⟩ := hnat p n a h
    exact ⟨Lplain, step_inputs_of_provider _ _ Lplain hp⟩
  first := by
    obtain ⟨Lplain, hp⟩ := h1
    exact ⟨Lplain, step_inputs_of_provider _ _ Lplain hp⟩
  second := by
    obtain ⟨Lplain, hp⟩ := h2
    exact ⟨Lplain, step_inputs_of_provider _ _ Lplain hp⟩
  third := by
    obtain ⟨Lplain, hp⟩ := h3
    exact ⟨Lplain, step_inputs_of_provider _ _ Lplain hp⟩

end
end QRH.DensitySplitThird.CubeFree.Assembly
