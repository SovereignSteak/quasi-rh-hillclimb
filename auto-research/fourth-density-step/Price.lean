/- Copyright (c) 2026 Sil. Apache-2.0.
The density-split leaf price (DS §§3–4, final source audit §§4–5).

At live width `w` the density cut is `q(w) = dens(v)`, `v = (w - s₀)₊` (DS (B)), clipped
to `[13/20, 3/4]` so that the price is defined (and the leaf suppliers apply) at every `w`;
on the certified range the clip is the identity (`HybridGates.dens_floor`, `dens_mem`).

* LOW (`ν < q`): erase the parent deletion need at cost `q` per unit of marked width
  (PR69 LOW erasure, uniform in `q`), i.e. `q · deletionNeed B₀ L₀ c₀ P s M`.
* HIGH (`ν ∈ [q, 3/4]`): the energy is `Z^{ρ(ν) M + ν (P + s)}`, so its excess over `M`
  is `highTerm ν P s M = ν (P+s) - (1 - ρ(ν)) M`, `1 - ρ(ν) = 10ν/(15-6ν)`; the price is the
  supremum over the closed density range.

The price is `max LOW HIGH`; its Lipschitz constant is `needLip B₀ L₀ c₀ ≥ 1`. -/
import Submissions.density_split_third_20261026.CubeFree.Price
import Submissions.density_split_third_20261026.Source.HybridGates
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

set_option autoImplicit false
namespace QRH.DensitySplitThird.Density
noncomputable section
open QRH.DensitySplitThird QRH.DensitySplitThird.CubeFree QRH.DensitySplitThird.Hybrid

/-- The clipped density cut `q(w) = clip_{[13/20,3/4]} dens(B₀,L₀,L,A,D,(w-s₀)₊)`. -/
def densQ (B₀ L₀ L A D s₀ w : ℝ) : ℝ :=
  max (13/20) (min (3/4) (dens B₀ L₀ L A D (max 0 (w - s₀))))

theorem densQ_ge (B₀ L₀ L A D s₀ w : ℝ) : 13/20 ≤ densQ B₀ L₀ L A D s₀ w := le_max_left _ _

theorem densQ_le (B₀ L₀ L A D s₀ w : ℝ) : densQ B₀ L₀ L A D s₀ w ≤ 3/4 :=
  max_le (by norm_num) (min_le_left _ _)

theorem densQ_nonneg (B₀ L₀ L A D s₀ w : ℝ) : 0 ≤ densQ B₀ L₀ L A D s₀ w :=
  le_trans (by norm_num) (densQ_ge B₀ L₀ L A D s₀ w)

/-- On the certified range the clip is the identity. -/
theorem densQ_eq {B₀ L₀ L A D s₀ w : ℝ}
    (h1 : 13/20 ≤ dens B₀ L₀ L A D (max 0 (w - s₀)))
    (h2 : dens B₀ L₀ L A D (max 0 (w - s₀)) ≤ 3/4) :
    densQ B₀ L₀ L A D s₀ w = dens B₀ L₀ L A D (max 0 (w - s₀)) := by
  unfold densQ; rw [min_eq_right h2, max_eq_right h1]

/-- HIGH excess over the envelope at density `ν`: `(ρ(ν)-1) M + ν (P+s)`. -/
def highTerm (ν P s M : ℝ) : ℝ := ν * (P + s) - 10 * ν / (15 - 6 * ν) * M

theorem highTerm_eq_rho (ν P s M : ℝ) :
    highTerm ν P s M = (rhoOf ν - 1) * M + ν * (P + s) := by
  unfold highTerm rhoOf; ring

/-- The HIGH price: supremum of `highTerm` over `ν ∈ [q, 3/4]`. -/
def highSup (q P s M : ℝ) : ℝ := ⨆ ν : Set.Icc q (3/4 : ℝ), highTerm ν P s M

/-- `0 ≤ 10ν/(15-6ν) ≤ 1` for `0 ≤ ν ≤ 3/4`. -/
theorem rhoGap_mem {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 3/4) :
    0 ≤ 10 * ν / (15 - 6 * ν) ∧ 10 * ν / (15 - 6 * ν) ≤ 1 := by
  have hd : 0 < 15 - 6 * ν := by linarith
  refine ⟨div_nonneg (by linarith) hd.le, ?_⟩
  rw [div_le_one hd]; linarith

theorem highTerm_le_abs {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 3/4) (P s M : ℝ) :
    highTerm ν P s M ≤ |P + s| + |M| := by
  obtain ⟨k0, k1⟩ := rhoGap_mem h0 h1
  unfold highTerm
  have e1 : ν * (P + s) ≤ |P + s| := by
    calc ν * (P + s) ≤ ν * |P + s| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ 1 * |P + s| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |P + s| := one_mul _
  have e2 : -(10 * ν / (15 - 6 * ν) * M) ≤ |M| := by
    calc -(10 * ν / (15 - 6 * ν) * M) ≤ 10 * ν / (15 - 6 * ν) * |M| := by
          rw [← neg_mul]
          have : -M ≤ |M| := neg_le_abs M
          nlinarith
      _ ≤ 1 * |M| := mul_le_mul_of_nonneg_right k1 (abs_nonneg _)
      _ = |M| := one_mul _
  linarith

section HighSup
variable {q : ℝ}

theorem highSup_bdd (hq : 0 ≤ q) (P s M : ℝ) :
    BddAbove (Set.range fun ν : Set.Icc q (3/4 : ℝ) => highTerm ν P s M) := by
  refine ⟨|P + s| + |M|, ?_⟩
  rintro _ ⟨ν, rfl⟩
  exact highTerm_le_abs (hq.trans ν.2.1) ν.2.2 P s M

theorem le_highSup (hq : 0 ≤ q) {ν : ℝ} (h1 : q ≤ ν) (h2 : ν ≤ 3/4) (P s M : ℝ) :
    highTerm ν P s M ≤ highSup q P s M :=
  le_ciSup (f := fun ν : Set.Icc q (3/4 : ℝ) => highTerm ν P s M) (highSup_bdd hq P s M)
    ⟨ν, h1, h2⟩

theorem highSup_le (hq : q ≤ 3/4) {P s M a : ℝ}
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → highTerm ν P s M ≤ a) : highSup q P s M ≤ a := by
  have : Nonempty (Set.Icc q (3/4 : ℝ)) := ⟨⟨3/4, hq, le_rfl⟩⟩
  exact ciSup_le fun ν => h ν ν.2.1 ν.2.2

theorem highSup_le_add (hq0 : 0 ≤ q) (hq : q ≤ 3/4) {P s M P' s' M' e : ℝ}
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → highTerm ν P' s' M' ≤ highTerm ν P s M + e) :
    highSup q P' s' M' ≤ highSup q P s M + e :=
  highSup_le hq fun ν h1 h2 => by
    have := le_highSup hq0 h1 h2 P s M
    linarith [h ν h1 h2]

end HighSup

theorem max_le_max_add {a b a' b' e : ℝ} (ha : a' ≤ a + e) (hb : b' ≤ b + e) :
    max a' b' ≤ max a b + e :=
  max_le (by linarith [le_max_left a b]) (by linarith [le_max_right a b])

/-- The LOW part of the density price. -/
def lowPart (B₀ L₀ c₀ q P s M : ℝ) : ℝ := q * deletionNeed B₀ L₀ c₀ P s M

theorem lowPart_lip {B₀ L₀ c₀ q P s M P' s' M' e : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (he : 0 ≤ e)
    (h : deletionNeed B₀ L₀ c₀ P' s' M' ≤ deletionNeed B₀ L₀ c₀ P s M + e) :
    lowPart B₀ L₀ c₀ q P' s' M' ≤ lowPart B₀ L₀ c₀ q P s M + e := by
  unfold lowPart
  have h1 := mul_le_mul_of_nonneg_left h hq0
  have h2 : q * e ≤ e := by nlinarith
  linarith

/-- The density-split price `max (q(w)·deletionNeed) (sup_{ν∈[q(w),3/4]} highTerm)`. -/
def densityPrice (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) : Price where
  f w P s M := max (lowPart B₀ L₀ c₀ (densQ B₀ L₀ L A D s₀ w) P s M)
    (highSup (densQ B₀ L₀ L A D s₀ w) P s M)
  nonneg w P s M := le_max_of_le_left
    (mul_nonneg (densQ_nonneg _ _ _ _ _ _ _) (deletionNeed_nonneg _ _ _ _ _ _))
  mono w P P' s s' M hP hs := by
    have hq0 := densQ_nonneg B₀ L₀ L A D s₀ w
    have hq1 := densQ_le B₀ L₀ L A D s₀ w
    apply max_le_max
    · exact mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) hq0
    · have := highSup_le_add (e := 0) hq0 hq1 (P := P) (s := s) (M := M) (P' := P') (s' := s')
        (M' := M) (fun ν h1 _ => by
          unfold highTerm
          have : ν * (P' + s') ≤ ν * (P + s) :=
            mul_le_mul_of_nonneg_left (by linarith) (hq0.trans h1)
          linarith)
      linarith
  lip := needLip B₀ L₀ c₀
  lip_nonneg := zero_le_one.trans (one_le_needLip _ _ _)
  lipP w P s M δ hδ := by
    have hq0 := densQ_nonneg B₀ L₀ L A D s₀ w
    have hq1 := densQ_le B₀ L₀ L A D s₀ w
    have hK := one_le_needLip B₀ L₀ c₀
    have hKδ : δ ≤ needLip B₀ L₀ c₀ * δ := by nlinarith
    apply max_le_max_add
    · exact lowPart_lip hq0 (by linarith) (by nlinarith) (deletionNeed_lipP hL hδ)
    · refine highSup_le_add hq0 hq1 fun ν h1 h2 => ?_
      unfold highTerm
      have : ν * δ ≤ δ := by nlinarith
      nlinarith
  lipS w P s M δ hδ := by
    have hq0 := densQ_nonneg B₀ L₀ L A D s₀ w
    have hq1 := densQ_le B₀ L₀ L A D s₀ w
    have hK := one_le_needLip B₀ L₀ c₀
    have hKδ : δ ≤ needLip B₀ L₀ c₀ * δ := by nlinarith
    apply max_le_max_add
    · exact lowPart_lip hq0 (by linarith) (by nlinarith) (deletionNeed_lipS hL hδ)
    · refine highSup_le_add hq0 hq1 fun ν h1 h2 => ?_
      unfold highTerm
      have : ν * δ ≤ δ := by nlinarith
      nlinarith
  lipM w P s M δ := by
    have hq0 := densQ_nonneg B₀ L₀ L A D s₀ w
    have hq1 := densQ_le B₀ L₀ L A D s₀ w
    have hK := one_le_needLip B₀ L₀ c₀
    have hδ := abs_nonneg δ
    have hKδ : |δ| ≤ needLip B₀ L₀ c₀ * |δ| := by nlinarith
    apply max_le_max_add
    · exact lowPart_lip hq0 (by linarith) (by nlinarith) (deletionNeed_lipM hL)
    · refine highSup_le_add hq0 hq1 fun ν h1 h2 => ?_
      obtain ⟨k0, k1⟩ := rhoGap_mem (hq0.trans h1) h2
      unfold highTerm
      have e1 : -(10 * ν / (15 - 6 * ν) * δ) ≤ |δ| := by
        have : -δ ≤ |δ| := neg_le_abs δ
        have : δ ≤ |δ| := le_abs_self δ
        nlinarith
      nlinarith

theorem densityPrice_f (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) (w P s M : ℝ) :
    (densityPrice B₀ L₀ c₀ L A D s₀ hL).f w P s M =
      max (densQ B₀ L₀ L A D s₀ w * deletionNeed B₀ L₀ c₀ P s M)
        (highSup (densQ B₀ L₀ L A D s₀ w) P s M) := rfl

theorem densityPrice_lip (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) :
    (densityPrice B₀ L₀ c₀ L A D s₀ hL).lip = needLip B₀ L₀ c₀ := rfl

/-- The density price never exceeds the native-cost bound `(3/4)·s₊ ∨ HIGH`: the LOW part
deletes at most the retained width, at cost `q ≤ 3/4`. -/
theorem lowPart_le_native {B₀ L₀ c₀ q P s M : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 3/4) :
    lowPart B₀ L₀ c₀ q P s M ≤ 3/4 * max 0 s := by
  unfold lowPart
  have h1 : deletionNeed B₀ L₀ c₀ P s M ≤ max 0 s :=
    max_le_max le_rfl (min_le_left _ _)
  have h0 := deletionNeed_nonneg B₀ L₀ c₀ P s M
  calc q * deletionNeed B₀ L₀ c₀ P s M ≤ q * max 0 s := mul_le_mul_of_nonneg_left h1 hq0
    _ ≤ 3/4 * max 0 s := mul_le_mul_of_nonneg_right hq (le_max_left _ _)

end
end QRH.DensitySplitThird.Density
