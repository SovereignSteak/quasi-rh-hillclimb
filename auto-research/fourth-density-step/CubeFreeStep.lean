/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L: the generic cube-free common-divisor step and its three instances (design L7).

`StepInputs D G Lplain` is the single remaining analytic input of one step: the top output
of the root chain (WP-K2a/K2b with Seam 0 of WP-M, the diagonal budget, the label budget and
the root data), namely the restricted cube-free source on all roots of width `≥ s₀`, from
`51/100 ≤ β`, the parent source and the Seam A leaf at the envelope `[Hmin, Hmax+1]`.
Everything else is proved here: the inherited roots (`∑ w < s₀`, CF crossing), the per-T
restoration, the merging of constants, and the leaves of the native and density steps.

This module deliberately does not import `Source.Assembly` (which imports PR76's FP source and
would put FP copies of forked modules next to the forks); the conclusions are stated in the
shapes of `NativeStepStatement` and `HybridStepFor`, which `Assembly/Final.lean` plugs in. -/
import Submissions.density_split_third_20261026.CubeFree.Assembly.Combine
import Submissions.density_split_third_20261026.CubeFree.Assembly.Leaves

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source QRH.DensitySplitThird.CubeFree.Assembly

/-- The remaining input of one cube-free step (the root chain's top statement). -/
structure StepInputs (D : StepData) (G : StepGates D) (Lplain : ℝ) : Prop where
  restricted : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
    GlobalSource D.B₀ D.L₀ D.c₀ →
    PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain →
    HighRestrictedUnitSource (globalFace D.B D.L D.c) D.s₀

/-- **The generic cube-free step.** -/
theorem cubefree_step (D : StepData) (G : StepGates D) (Lplain : ℝ) (I : StepInputs D G Lplain)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : GlobalSource D.B₀ D.L₀ D.c₀)
    (hleaf : PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain) :
    GlobalSource D.B D.L D.c := by
  obtain ⟨hB, hB₀, hLL, hL1, -⟩ := G.face
  exact global_source_of_parent_and_high D.B D.L D.c D.B₀ D.L₀ D.c₀ D.s₀ (by linarith)
    (by linarith) (by linarith) (fun P S hS0 hS hroot => G.inherit hS0 hS hroot) hparent
    (I.restricted hβ hparent hleaf)

/-- The inputs of all native steps. -/
def NativeInputs : Prop :=
  ∀ (p n : Face) (a : ℝ) (h : NativeGates p n a), ∃ Lplain : ℝ,
    StepInputs (nativeData p n a h) (stepGates_of_native h) Lplain

/-- **The native step**, in the shape of `Source.Assembly.NativeStepStatement`. -/
theorem native_step (I : NativeInputs) :
    ∀ p n : Face, ∀ a : ℝ, NativeGates p n a →
      (51/100:ℝ) ≤ HeckeZeroSupremum.beta → GlobalSource p.B p.L p.c → GlobalSource n.B n.L n.c :=
  fun p n a h hβ hp => by
    obtain ⟨Lplain, hI⟩ := I p n a h
    exact cubefree_step (nativeData p n a h) (stepGates_of_native h) Lplain hI hβ hp
      (native_leaf h hβ hp Lplain)

/-- Step data of the first density transition `G(.9999,2.58,.12) → G(.9959,2.5,.1)`. -/
abbrev dsFirst : StepData :=
  Density.dsData (9999/10000) (129/50) (3/25) (9959/10000) (5/2) (1/10) (6/5) 140 (by norm_num)

/-- Step data of the second density transition `G(.9959,2.5,.1) → G(.9934,2.45,.1)`. -/
abbrev dsSecond : StepData :=
  Density.dsData (9959/10000) (5/2) (1/10) (4967/5000) (49/20) (1/10) (7/10) 70 (by norm_num)

/-- Step data of the third density transition `G(.9934,2.45,.1) → G(.99,2.39,.1)`
(added 2026-10-26). -/
abbrev dsThird : StepData :=
  Density.dsData (4967/5000) (49/20) (1/10) (99/100) (239/100) (1/10) (3/5) 35 (by norm_num)

/-- **The first density step**, in the shape of `HybridStepFor bootstrapFace hybridFace1`. -/
theorem hybrid_step_first (I : ∃ Lplain : ℝ, StepInputs dsFirst Density.dsGates_first Lplain) :
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      GlobalSource (9999/10000) (129/50) (3/25) → GlobalSource (9959/10000) (5/2) (1/10) :=
  fun hβ hp => by
    obtain ⟨Lplain, hI⟩ := I
    exact cubefree_step dsFirst Density.dsGates_first Lplain hI hβ hp
      (density_leaf_first hβ hp Lplain)

/-- **The second density step**, in the shape of `HybridStepFor hybridFace1 hybridFace2`. -/
theorem hybrid_step_second (I : ∃ Lplain : ℝ, StepInputs dsSecond Density.dsGates_second Lplain) :
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      GlobalSource (9959/10000) (5/2) (1/10) → GlobalSource (4967/5000) (49/20) (1/10) :=
  fun hβ hp => by
    obtain ⟨Lplain, hI⟩ := I
    exact cubefree_step dsSecond Density.dsGates_second Lplain hI hβ hp
      (density_leaf_second hβ hp Lplain)

/-- **The third density step**, in the shape of `HybridStepFor hybridFace2 hybridFace3`. -/
theorem hybrid_step_third (I : ∃ Lplain : ℝ, StepInputs dsThird Density.dsGates_third Lplain) :
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      GlobalSource (4967/5000) (49/20) (1/10) → GlobalSource (99/100) (239/100) (1/10) :=
  fun hβ hp => by
    obtain ⟨Lplain, hI⟩ := I
    exact cubefree_step dsThird Density.dsGates_third Lplain hI hβ hp
      (density_leaf_third hβ hp Lplain)

/-- All remaining inputs of the source chain. -/
structure AllStepInputs : Prop where
  native : NativeInputs
  first : ∃ Lplain : ℝ, StepInputs dsFirst Density.dsGates_first Lplain
  second : ∃ Lplain : ℝ, StepInputs dsSecond Density.dsGates_second Lplain
  third : ∃ Lplain : ℝ, StepInputs dsThird Density.dsGates_third Lplain

end
end QRH.DensitySplitThird.CubeFree
