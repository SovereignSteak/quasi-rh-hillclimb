/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L: the Seam A leaves of the three kinds of steps, at the envelope `[Hmin, Hmax+1]`.

* native steps: the parent leaf `parent_priced_source` when the parent face is positive
  (`0 < B₀`, `0 < c₀`); on a degenerate parent face (`B₀ ≤ 0` or `c₀ ≤ 0`, which
  `NativeGates` does not exclude) the parent price equals the native price on the envelope
  (`M ≥ 0`, lengths `≥ 0`), so the native leaf `native_priced_source` serves;
* density steps: `density_priced_source` on the two certified transitions.
`PricedPackedSource.mono_range` is the price monotonicity of Seam A restricted to the
arguments the contract actually evaluates (`P, s ≥ 0`, `M ≥ Mmin`). -/
import Submissions.density_split_third_20261026.CubeFree.Leaf.Parent
import Submissions.density_split_third_20261026.Density.Leaf
import Submissions.density_split_third_20261026.Density.StepGates

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Assembly
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths HeckeFamily CenteredMomentEnergyBands
open QRH.DensitySplitThird.CubeFree
local notation "O" => HeckeFamily.O

/-- Seam A price monotonicity on the evaluated arguments only. -/
theorem PricedPackedSource.mono_range {price price' : Price} {Mmin Mmax Lplain : ℝ}
    (hprice : ∀ w P s M, 0 ≤ P → 0 ≤ s → Mmin ≤ M → price.f w P s M ≤ price'.f w P s M)
    (h : PricedPackedSource price Mmin Mmax Lplain) :
    PricedPackedSource price' Mmin Mmax Lplain := by
  intro ε hε
  obtain ⟨meshMax, hmesh, h⟩ := h ε hε
  refine ⟨meshMax, hmesh, fun mesh hm α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q
    hQ hQ0 hQt hQ72 => ?_⟩
  obtain ⟨degree, S, C, hC, hev⟩ := h mesh hm α rayM H hH W hW hWs bΦ hbΦ κ anchors η₀ Q
    hQ hQ0 hQt hQ72
  refine ⟨degree, S, C, hC, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (1:ℝ)] with Z hZ hZ1 j w₀
  intro T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  refine (hZ j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p
    X₁ X₂ hX₁ hX₂ hl₁ hl₂).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le hZ1.le
    have hP : 0 ≤ length Z X₁ + length Z X₂ :=
      add_nonneg (length_nonneg Z X₁ hZ1) (length_nonneg Z X₂ hZ1)
    have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
    have := hprice w₀ _ _ _ hP hs hM₁
    linarith
  · have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    have h1 : 0 ≤ 1+|t|+height := by positivity
    positivity

/-- On a degenerate parent face the parent price is the native price on the envelope. -/
theorem native_le_parent_degenerate {B₀ L₀ c₀ : ℝ} (hL : 0 < L₀) (hdeg : ¬(0 < B₀ ∧ 0 < c₀))
    {P s M : ℝ} (hP : 0 ≤ P) (hM : 0 ≤ M) :
    (3/4:ℝ)*max 0 s ≤ (3/4:ℝ)*deletionNeed B₀ L₀ c₀ P s M := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold deletionNeed
  apply max_le_max le_rfl
  apply le_min le_rfl
  by_cases hc : c₀ ≤ 0
  · exact le_max_of_le_left (by nlinarith)
  · have hB : B₀ ≤ 0 := by
      by_contra hB
      exact hdeg ⟨lt_of_not_ge hB, lt_of_not_ge hc⟩
    apply le_max_of_le_right
    rw [le_div_iff₀ hL]
    nlinarith

/-- The native step leaf at the envelope `[Hmin, Hmax+1]` of `nativeData`. -/
theorem native_leaf {p n : Face} {a : ℝ} (h : NativeGates p n a)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource p.B p.L p.c) (Lplain : ℝ) :
    PricedPackedSource (nativeData p n a h).price (nativeData p n a h).Hmin
      ((nativeData p n a h).Hmax+1) Lplain := by
  have hH := h.H_eff
  have hf := (nativeFrac_pos h).le
  have hc := h.cap_pos.le
  have h0 : 0 < (1 - 6*nativeFrac a*n.c)/2 := by linarith
  have h1 : (1 - 6*nativeFrac a*n.c)/2 ≤ 3+1 := by nlinarith
  change PricedPackedSource (parentPrice (3/4) p.B p.L p.c (by norm_num) h.L₀_pos)
    ((1 - 6*nativeFrac a*n.c)/2) (3+1) Lplain
  by_cases hpos : 0 < p.B ∧ 0 < p.c
  · exact parent_priced_source p.B p.L p.c _ _ Lplain hβ ⟨h.L₀_pos, hpos.1, h.B_lt.le, hpos.2⟩
      h0 h1 hparent
  · refine PricedPackedSource.mono_range (fun w P s M hP _ hM => ?_)
      (native_priced_source hβ _ _ Lplain h0 h1)
    exact native_le_parent_degenerate h.L₀_pos hpos hP (h0.le.trans hM)

open QRH.DensitySplitThird.Density in
/-- The leaf of the first density transition. -/
theorem density_leaf_first (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (9999/10000) (129/50) (3/25))
    (Lplain : ℝ) :
    PricedPackedSource
      (dsData (9999/10000) (129/50) (3/25) (9959/10000) (5/2) (1/10) (6/5) 140 (by norm_num)).price
      (dsData (9999/10000) (129/50) (3/25) (9959/10000) (5/2) (1/10) (6/5) 140 (by norm_num)).Hmin
      ((dsData (9999/10000) (129/50) (3/25) (9959/10000) (5/2) (1/10) (6/5) 140
        (by norm_num)).Hmax+1) Lplain :=
  density_priced_source _ _ _ _ _ _ _ _ _ Lplain (by norm_num) hβ ⟨by norm_num, by norm_num, by norm_num⟩
    (by norm_num [dsData]) (by norm_num [dsData]) hparent

open QRH.DensitySplitThird.Density in
/-- The leaf of the second density transition. -/
theorem density_leaf_second (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (9959/10000) (5/2) (1/10))
    (Lplain : ℝ) :
    PricedPackedSource
      (dsData (9959/10000) (5/2) (1/10) (4967/5000) (49/20) (1/10) (7/10) 70 (by norm_num)).price
      (dsData (9959/10000) (5/2) (1/10) (4967/5000) (49/20) (1/10) (7/10) 70 (by norm_num)).Hmin
      ((dsData (9959/10000) (5/2) (1/10) (4967/5000) (49/20) (1/10) (7/10) 70
        (by norm_num)).Hmax+1) Lplain :=
  density_priced_source _ _ _ _ _ _ _ _ _ Lplain (by norm_num) hβ ⟨by norm_num, by norm_num, by norm_num⟩
    (by norm_num [dsData]) (by norm_num [dsData]) hparent

open QRH.DensitySplitThird.Density in
/-- The leaf of the third density transition (added 2026-10-26). -/
theorem density_leaf_third (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (4967/5000) (49/20) (1/10))
    (Lplain : ℝ) :
    PricedPackedSource
      (dsData (4967/5000) (49/20) (1/10) (99/100) (239/100) (1/10) (3/5) 35 (by norm_num)).price
      (dsData (4967/5000) (49/20) (1/10) (99/100) (239/100) (1/10) (3/5) 35 (by norm_num)).Hmin
      ((dsData (4967/5000) (49/20) (1/10) (99/100) (239/100) (1/10) (3/5) 35
        (by norm_num)).Hmax+1) Lplain :=
  density_priced_source _ _ _ _ _ _ _ _ _ Lplain (by norm_num) hβ ⟨by norm_num, by norm_num, by norm_num⟩
    (by norm_num [dsData]) (by norm_num [dsData]) hparent

end
end QRH.DensitySplitThird.CubeFree.Assembly
