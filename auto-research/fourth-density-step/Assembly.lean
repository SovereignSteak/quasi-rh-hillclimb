/- Copyright (c) 2026 Sil. Apache-2.0.
Assembly of the source chain
  G(99999/100000,93/25,3/50) → (26 native steps) → G(9999/10000,129/50,3/25)
    → G(9959/10000,5/2,1/10) → G(4967/5000,49/20,1/10)
from the generic analytic step statements. The initial face is the actual
fourth-power source of PR76 (contrary branch 51/100 ≤ beta). The two step
statements are explicit hypotheses here; they are discharged in the endpoint. -/
import Submissions.density_split_third_20261026.Source.NativeBootstrap
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedRestrictedSource

set_option autoImplicit false
namespace QRH.DensitySplitThird
noncomputable section
open OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Record1252270103Source

/-- The literal global ordinary source on a face. -/
def Face.Source (f : Face) : Prop := GlobalSource f.B f.L f.c

theorem globalFace_restricts {q p : Face} (h : q.Sub p) :
    (globalFace p.B p.L p.c).Restricts (globalFace q.B q.L q.c) := by
  obtain ⟨hB, hL, hc⟩ := h
  constructor <;> simp only [globalFace] <;> linarith

/-- A source on a face gives the source on every literal subface, with the same mesh. -/
theorem Face.source_mono {q p : Face} (h : q.Sub p) (hp : p.Source) : q.Source := by
  intro ε hε
  obtain ⟨mesh, hmesh, hs⟩ := hp ε hε
  refine ⟨mesh, hmesh, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree, S, C, hC, hsource⟩ :=
    hs α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree, S, C, hC, hsource.mono (fun Z hZ => initialAffineAt_restrict rayM H hH
    (globalFace_restricts h) W 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q
    degree S C (by norm_num) hZ)⟩

/-- The generic native cube-free common-divisor step (proved in `CubeFree`). -/
def NativeStepStatement : Prop :=
  ∀ p n : Face, ∀ a : ℝ, NativeGates p n a →
    (51/100 : ℝ) ≤ HeckeZeroSupremum.beta → p.Source → n.Source

/-- One variable-density transition with selection parameters `A`, `D`. -/
def HybridStepFor (p n : Face) (A D : ℝ) : Prop :=
  (51/100 : ℝ) ≤ HeckeZeroSupremum.beta → p.Source → n.Source

def hybridFace1 : Face := ⟨9959/10000, 5/2, 1/10⟩
def hybridFace2 : Face := ⟨4967/5000, 49/20, 1/10⟩
def hybridFace3 : Face := ⟨99/100, 239/100, 1/10⟩

theorem face0_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) : face0.Source := by
  have h := Candidate.FourthPower.RepairedRestrictedSource.actual_global_source hβ
  simpa only [Face.Source, face0] using h

theorem bootstrap_source (hstep : NativeStepStatement)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) : bootstrapFace.Source :=
  bootstrap Face.Source (fun p n a hg hp => hstep p n a hg hβ hp)
    (fun _ _ h hp => Face.source_mono h hp) (face0_source hβ)

/-- The final source `G(99/100, 239/100, 1/10)` from the generic steps
(modified 2026-10-26: a third density-split transition after `hybridFace2`). -/
theorem final_source (hstep : NativeStepStatement)
    (h1 : HybridStepFor bootstrapFace hybridFace1 (6/5) 140)
    (h2 : HybridStepFor hybridFace1 hybridFace2 (7/10) 70)
    (h3 : HybridStepFor hybridFace2 hybridFace3 (3/5) 35)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99/100) (239/100) (1/10) := by
  have h := h3 hβ (h2 hβ (h1 hβ (bootstrap_source hstep hβ)))
  simpa only [Face.Source, hybridFace3] using h

end
end QRH.DensitySplitThird
