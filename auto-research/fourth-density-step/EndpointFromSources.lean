/- Repeated marks: fork of Collet's final-stage module EndpointFromSources (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. Single stage: the two-stage
theorems (Collet's intermediate return) are removed. -/
/- Modified by Sil (2026-10-26): physical face cap `3/50 ≤ 31/500` of P; instances at theta = 174799/200000; single mesh for the windows -/
import Submissions.density_split_third_20261026.Return.FinalSchedule
import Submissions.density_split_third_20261026.ReturnD.PhysicalDirect.ChosenSource
import Submissions.density_split_third_20261026.Return.EndpointFromNumerator
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensitySplitThird.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.BoundsN := Geometry.finalBounds
local instance : CountScheme := finalCountScheme
local instance : GenericArithmetic.PhysicalSchedule := finalPhysicalSchedule

theorem literal_numerator_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.DensitySplitThird.Return.naturalK/6) : LiteralNumeratorInput := by
 have hc : ∀ε:ℝ,0<ε → ∃mesh:ℝ,0< mesh ∧
   ∀w∈finalCountScheme.windows,UnitFaceSource w.face mesh ε := by
  intro ε hε
  obtain ⟨mesh,hm,hw⟩ := final_windows_common_mesh hC hP hε
  exact ⟨mesh,hm,hw⟩
 have hr : physicalGlobal.Restricts GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalGlobal.Restricts
   ⟨QRH.DensitySplitThird.Return.physicalB,QRH.DensitySplitThird.Return.physicalLambda,0,1/2,0,QRH.DensitySplitThird.Return.numeratorCap⟩
  constructor <;> norm_num [physicalGlobal,QRH.Record1252270103Return.globalFace,
   QRH.DensitySplitThird.Return.physicalB,QRH.DensitySplitThird.Return.physicalCap,QRH.DensitySplitThird.Return.numeratorCap]
 have hp : UniformUnitFaceSource GenericPhysical.PhysicalDirect.physicalFace := by
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := hP ε hε
  exact ⟨mesh,hm,unit_source_restrict hr hs⟩
 exact GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
  (GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces hcap hc hp)

theorem beta_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.DensitySplitThird.Return.naturalK/6) :
 HeckeZeroSupremum.beta≤QRH.DensitySplitThird.Return.theta :=
 beta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap)

theorem hecke_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.DensitySplitThird.Return.naturalK/6)
 (χ:Character) (s:ℂ) (hs:QRH.DensitySplitThird.Return.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 :=
 hecke_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) χ s hs hpole

theorem dirichlet_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.DensitySplitThird.Return.naturalK/6)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:QRH.DensitySplitThird.Return.theta<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 dirichlet_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) χ s hs hpole

theorem zeta_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.DensitySplitThird.Return.naturalK/6)
 (s:ℂ) (hs:QRH.DensitySplitThird.Return.theta<s.re) : riemannZeta s≠0 :=
 zeta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) s hs
end Final

end
end QRH.DensitySplitThird.Return
