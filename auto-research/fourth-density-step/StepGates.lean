/- Copyright (c) 2026 Sil. Apache-2.0.
Step data and scalar gates of a density-split transition G(B₀,L₀,c₀) → G(B,L,c)
(DS §§4–5, final source audit §§4–6), from the certified `HybridGates`.

* crossing `s₀ = (B₀-B)/(L₀-L)`, excess `v = (w-s₀)₊`, selection `u(w) = A v/(1+D v)`;
* price `densityPrice` (LOW: `q(w)·deletionNeed`; HIGH: `sup_{ν∈[q(w),3/4]} highTerm`);
* `Hmin = 9/10`, `Hmax = 3`, `κ = 3/4`.

The ledger needs no positive reserve at `v = 0`: the LOW identity (C) gives
`q·defect ≤ L₀ u + q (B₀+1) tl` for every `v ≥ 0` (the defect is `≤ (6B₀-L₀)u + B₀ tl` when
`w ≤ s₀`), and upward greedy overshoot is harmless since `q(6B₀-L₀) ≤ L₀`. The HIGH payment
uses `P_C + s ≤ B - (L-1) max(w,s₀) - u` (root face, `S ≥ max(w,s₀)`, `c_g ≥ f ≥ 0`), the
uniform reserve of `J` on `ν ∈ [q(v),3/4]` (`HybridGates.high_reserve`), the bound
`6(1-ρ)-ν-1 ≤ 6` for the mesh, and `(1-ρ) t ≥ -tl`. The floor is `ε/16`.

`DSFace` records the numerical face facts that are not fields of `HybridGates`. -/
import Submissions.density_split_third_20261026.Density.Price
import Submissions.density_split_third_20261026.CubeFree.StepData
import Submissions.density_split_third_20261026.Source.HybridCertificates

set_option autoImplicit false
namespace QRH.DensitySplitThird.Density
noncomputable section
open QRH.DensitySplitThird QRH.DensitySplitThird.CubeFree QRH.DensitySplitThird.Hybrid

/-- The density selection at live width `w`: `u(w) = A v/(1+D v)`, `v = (w - s₀)₊`. -/
def dsSel (A D s₀ w : ℝ) : ℝ := sel A D (max 0 (w - s₀))

/-- Step data of a density-split transition. -/
def dsData (B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) : StepData where
  B₀ := B₀
  L₀ := L₀
  c₀ := c₀
  B := B
  L := L
  c := c
  κ := 3/4
  s₀ := cross B₀ L₀ B L
  Hmin := 9/10
  Hmax := 3
  sel := fun _ w => dsSel A D (cross B₀ L₀ B L) w
  price := densityPrice B₀ L₀ c₀ L A D (cross B₀ L₀ B L) hL

/-- Numerical face facts of the transition that are not recorded in `HybridGates`. -/
structure DSFace (B₀ L₀ c₀ B L c : ℝ) : Prop where
  B_le : B ≤ B₀
  B₀_lt : B₀ < 1
  L_lt : L < L₀
  one_lt_L : 1 < L
  c_lt : c < 1/6
  c₀_lt : c₀ < 1/6

section generic
variable {B₀ L₀ c₀ B L c A D : ℝ}

theorem sel_zero (A D : ℝ) : sel A D 0 = 0 := by simp [sel]

theorem DSFace.cross_nonneg (hF : DSFace B₀ L₀ c₀ B L c) : 0 ≤ cross B₀ L₀ B L :=
  div_nonneg (sub_nonneg.2 hF.B_le) (sub_pos.2 hF.L_lt).le

theorem DSFace.cross_mul (hF : DSFace B₀ L₀ c₀ B L c) :
    (L₀ - L) * cross B₀ L₀ B L = B₀ - B := by
  have : L₀ - L ≠ 0 := (sub_pos.2 hF.L_lt).ne'
  unfold cross; field_simp

theorem _root_.QRH.DensitySplitThird.HybridGates.dsA_pos (h : HybridGates B₀ L₀ c₀ B L c A D) : 0 < A := by
  have := h.selection_monotonicity.pos 0 le_rfl h.width_pos.le
  simpa [gSelDeriv] using this

theorem _root_.QRH.DensitySplitThird.HybridGates.dsCross_lt_c₀ (h : HybridGates B₀ L₀ c₀ B L c A D) :
    cross B₀ L₀ B L < c₀ := by
  have := h.retained_cap.pos 0 le_rfl h.width_pos.le
  simp only [gRetainedCap, packed, width, sel_zero] at this
  linarith

theorem _root_.QRH.DensitySplitThird.HybridGates.dsSel_nonneg (h : HybridGates B₀ L₀ c₀ B L c A D) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B₀ L₀ B L) : 0 ≤ sel A D v :=
  div_nonneg (mul_nonneg h.dsA_pos.le h0) (h.sel_den_pos v h0 h1).le

theorem _root_.QRH.DensitySplitThird.HybridGates.dsSel_mono (h : HybridGates B₀ L₀ c₀ B L c A D) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ c - cross B₀ L₀ B L) : sel A D a ≤ sel A D b := by
  have da := h.sel_den_pos a ha (hab.trans hb)
  have db := h.sel_den_pos b (ha.trans hab) hb
  unfold sel
  rw [div_le_div_iff₀ da db]
  nlinarith [mul_le_mul_of_nonneg_left hab h.dsA_pos.le]

/-- `q(v)·(6B₀-L₀) ≤ L₀`: the LOW overshoot coefficient is at most one. -/
theorem _root_.QRH.DensitySplitThird.HybridGates.dsDens_overshoot (h : HybridGates B₀ L₀ c₀ B L c A D)
    (hF : DSFace B₀ L₀ c₀ B L c) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ c - cross B₀ L₀ B L) :
    dens B₀ L₀ L A D v * (6 * B₀ - L₀) ≤ L₀ := by
  have hE := h.dens_den_pos v h0 h1
  have hm := dens_mul B₀ L₀ L A D v hE.ne'
  unfold densE densK at hm
  have hA := h.dsA_pos
  have hx := h.sel_den_pos v h0 h1
  have hq := (h.dens_mem v h0 h1).1
  have hLL : 0 < L₀ - L := sub_pos.2 hF.L_lt
  have hL₀ : 0 < L₀ := by linarith [hF.one_lt_L]
  have hp : 0 < dens B₀ L₀ L A D v * ((L₀ - L) * (1 + D * v)) :=
    mul_pos (by linarith) (mul_pos hLL hx)
  have key : (dens B₀ L₀ L A D v * (6 * B₀ - L₀) - L₀) * A ≤ 0 := by
    nlinarith [mul_pos hL₀ hA]
  by_contra hc
  have hc : L₀ < dens B₀ L₀ L A D v * (6 * B₀ - L₀) := lt_of_not_ge hc
  have := mul_pos (sub_pos.2 hc) hA
  linarith

/-! ### Pure scalar steps of the ledger -/

/-- Retained parent cap `s ≤ c₀ H` from the certified cap reserve. -/
theorem ds_cap_aux {c₀ s S f u σ t tl s₀ v rC : ℝ} (hc06 : c₀ < 1/6) (hc00 : 0 ≤ c₀)
    (hs : s ≤ S - f - u) (hwv : S - f - s₀ ≤ v) (hu0 : σ ≤ u) (ht : -tl ≤ t)
    (htl : 0 ≤ tl) (ht2 : tl ≤ rC) (hr : rC ≤ c₀ * (1 - 6 * σ) - (s₀ + v - σ)) :
    s - c₀ * (1 + t - 6 * u) ≤ 0 := by
  have e1 : 0 ≤ (1 - 6*c₀) * (u - σ) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ c₀ * (t + tl) := mul_nonneg hc00 (by linarith)
  have e3 : c₀ * tl ≤ tl := by nlinarith
  linarith

/-- The parent face defect at the side (DS §4 `F`): `F ≤ (L₀-L)v + (6B₀-L₀)u + B₀ tl`. -/
theorem ds_defect_aux {B₀ L₀ B L s₀ PC cg f S u s t tl v : ℝ} (hL₀ : 0 ≤ L₀) (hL1 : 1 ≤ L)
    (hLL : 0 ≤ L₀ - L) (hB₀ : 0 ≤ B₀) (hcross : (L₀ - L) * s₀ = B₀ - B) (hf : 0 ≤ f)
    (hfcg : f ≤ cg) (hroot : PC + (cg - f) + L * S ≤ B + tl) (hs : s ≤ S - f - u)
    (hwv : S - f - s₀ ≤ v) (ht : -tl ≤ t) :
    PC + L₀ * s - B₀ * (1 + t - 6 * u) ≤ (L₀ - L) * v + (6*B₀ - L₀) * u + (B₀ * tl + tl) := by
  have e1 : L₀ * s ≤ L₀ * (S - f - u) := mul_le_mul_of_nonneg_left hs hL₀
  have e2 : (L₀ - L) * (S - f - s₀) ≤ (L₀ - L) * v := mul_le_mul_of_nonneg_left hwv hLL
  have e3 : 0 ≤ (L - 1) * f := mul_nonneg (by linarith) hf
  have e4 : 0 ≤ B₀ * (t + tl) := mul_nonneg hB₀ (by linarith)
  linarith

/-- LOW payment from the identity (C): `q·F ≤ L₀ (u + ε/16)`. -/
theorem ds_low_aux {q L₀ L B₀ v σ u ε tl F : ℝ} (hq0 : 0 ≤ q) (hq34 : q ≤ 3/4)
    (hB₁ : B₀ < 1) (hL₀ : 0 ≤ L₀) (hσ0 : 0 ≤ σ) (hu0 : σ ≤ u)
    (hdef : F ≤ (L₀ - L) * v + (6*B₀ - L₀) * u + (B₀ * tl + tl))
    (hC : L₀ * σ - q * ((L₀ - L) * v + (6 * B₀ - L₀) * σ) = 1 / 1000 * L₀ * σ)
    (hq6 : q * (6 * B₀ - L₀) ≤ L₀) (htl : 0 ≤ tl) (ht4 : tl ≤ L₀ * ε / 24) :
    q * F ≤ L₀ * (u + ε/16) := by
  have e1 := mul_le_mul_of_nonneg_left hdef hq0
  have e2 : q * (6*B₀ - L₀) * (u - σ) ≤ L₀ * (u - σ) :=
    mul_le_mul_of_nonneg_right hq6 (by linarith)
  have e5 : q * B₀ ≤ 3/4 :=
    calc q * B₀ ≤ q * 1 := mul_le_mul_of_nonneg_left hB₁.le hq0
      _ ≤ 3/4 := by linarith
  have e3 : q * B₀ * tl ≤ 3/4 * tl := mul_le_mul_of_nonneg_right e5 htl
  have e3' : q * tl ≤ 3/4 * tl := mul_le_mul_of_nonneg_right hq34 htl
  have e4 : 0 ≤ L₀ * σ := mul_nonneg hL₀ hσ0
  linarith

/-- HIGH payment from the reserve of `J`: `ν (P_C + s) - (1-ρ) H ≤ u`. -/
theorem ds_high_aux {ν k PC s B L W u σ t tl mesh rJ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (k0 : 0 ≤ k) (k1 : k ≤ 1) (hPS : PC + s ≤ B + tl - (L - 1) * W - u) (hu0 : σ ≤ u) (hu1 : u ≤ σ + mesh)
    (ht : -tl ≤ t) (htl : 0 ≤ tl) (hJ : rJ ≤ k * (1 - 6 * σ) - ν * (B - (L - 1) * W - σ) + σ)
    (hres : 6 * mesh + 2 * tl ≤ rJ) :
    ν * (PC + s) - k * (1 + t - 6 * u) ≤ u := by
  have e1 : ν * (PC + s) ≤ ν * (B + tl - (L - 1) * W - u) := mul_le_mul_of_nonneg_left hPS hν0
  have e0 : ν * tl ≤ 1 * tl := mul_le_mul_of_nonneg_right hν1 htl
  have e2 : (u - σ) * (6*k - ν - 1) ≤ (u - σ) * 6 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e3 : 0 ≤ k * (t + tl) := mul_nonneg k0 (by linarith)
  have e4 : k * tl ≤ 1 * tl := mul_le_mul_of_nonneg_right k1 htl
  have e5 : (u - σ) * 6 ≤ mesh * 6 := mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  linarith

/-- The density ledger. -/
theorem ds_ledger (h : HybridGates B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × ℝ × ℝ, LedgerAt (dsData B₀ L₀ c₀ B L c A D hL) ε p.1 p.2.1 p.2.2 := by
  obtain ⟨rH, hrH, hHr⟩ := h.H_lower
  obtain ⟨rC, hrC, hCr⟩ := h.retained_cap
  obtain ⟨rJ, hrJ, hJr⟩ := h.high_reserve
  obtain ⟨m, hm⟩ : ∃ m, m = min rJ rH := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ lt_min hrJ hrH
  have hmJ : m ≤ rJ := hm ▸ min_le_left _ _
  have hmH : m ≤ rH := hm ▸ min_le_right _ _
  refine ⟨(ε/16, m/12, min (m/4) (min rC (min 1 (min (L₀*ε/24) (ε/32))))), by positivity, ?_,
    by positivity, lt_min (by positivity) (lt_min hrC (lt_min one_pos
      (lt_min (by positivity) (by positivity)))), ?_⟩
  · show ε/16 ≤ ε/(16*(3/4))
    apply div_le_div_of_nonneg_left hε.le (by norm_num) (by norm_num)
  intro mesh hmesh hmeshL tl htl htlL g hfloor
  simp only at hmeshL htlL hfloor
  have ht1 : tl ≤ m/4 := htlL.trans (min_le_left _ _)
  have ht2 : tl ≤ rC := htlL.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : tl ≤ 1 :=
    htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht4 : tl ≤ L₀*ε/24 := htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have ht5 : tl ≤ ε/32 := htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  -- the side geometry
  have hS := g.hS
  have hf := g.hf
  have hPC := g.hPC
  have hroot := g.hroot
  have hsel := g.hsel
  have hs := g.hs
  have ht := g.ht
  simp only [dsData] at hS hroot hsel
  have hw : g.w = g.S - g.f := rfl
  have hH : g.H = 1 + g.t - 6*g.u := rfl
  -- scalar facts
  have hLL : 0 < L₀ - L := sub_pos.2 hF.L_lt
  have hL1 := hF.one_lt_L
  have hs0 := hF.cross_nonneg
  have hcross := hF.cross_mul
  have hcs := h.width_pos
  have hc0 := h.dsCross_lt_c₀
  have hc06 := hF.c₀_lt
  -- the excess
  obtain ⟨v, hv⟩ : ∃ v, v = max 0 (g.w - cross B₀ L₀ B L) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := hv ▸ le_max_left _ _
  have hv1 : v ≤ c - cross B₀ L₀ B L := hv ▸ max_le hcs.le (by rw [hw]; linarith)
  have hvS : v ≤ g.S - cross B₀ L₀ B L := hv ▸ max_le (by linarith) (by rw [hw]; linarith)
  have hwv : g.S - g.f - cross B₀ L₀ B L ≤ v := hv ▸ le_max_right _ _
  have hu0 : sel A D v ≤ g.u := by rw [hv]; exact hsel.1
  have hu1 : g.u ≤ sel A D v + mesh := by rw [hv]; exact hsel.2
  have hσ0 := h.dsSel_nonneg hv0 hv1
  have hq := h.dens_mem v hv0 hv1
  have hqf := h.dens_floor v hv0 hv1
  have hq6 := h.dsDens_overshoot hF hv0 hv1
  have hB₀ : 0 ≤ B₀ := by
    have hSf : ε/16 ≤ g.S := by rw [hw] at hfloor; linarith
    have : 1*(ε/16) ≤ L * g.S := mul_le_mul hL1.le hSf (by positivity) (by linarith)
    linarith [hF.B_le]
  have hPS : g.PC + g.s ≤ B + tl - (L - 1) * (cross B₀ L₀ B L + v) - g.u := by
    have : (L - 1) * (cross B₀ L₀ B L + v) ≤ (L - 1) * g.S :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- envelope, lower
    show 9/10 ≤ g.H
    have := hHr v hv0 hv1
    simp only [gHLower, packed] at this
    rw [hH]; linarith
  · -- envelope, upper
    show g.H ≤ 3
    rw [hH]; linarith
  -- the price at the side
  have hQ : densQ B₀ L₀ L A D (cross B₀ L₀ B L) g.w = dens B₀ L₀ L A D v := by
    have := densQ_eq (B₀ := B₀) (L₀ := L₀) (L := L) (A := A) (D := D)
      (s₀ := cross B₀ L₀ B L) (w := g.w) (by rw [← hv]; exact hqf.le) (by rw [← hv]; exact hq.2.le)
    rw [← hv] at this; exact this
  show max (lowPart B₀ L₀ c₀ (densQ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H)
      (highSup (densQ B₀ L₀ L A D (cross B₀ L₀ B L) g.w) g.PC g.s g.H) ≤ g.u + ε/16
  rw [hQ]
  refine max_le ?_ ?_
  · -- LOW: identity (C) and the defect bound
    have hcap : g.s - c₀ * g.H ≤ 0 := by
      have hr := hCr v hv0 hv1
      simp only [gRetainedCap, packed, width] at hr
      rw [hH]
      exact ds_cap_aux hc06 (by linarith) hs.2 hwv hu0 ht.1 htl ht2 hr
    have hdef : g.PC + L₀ * g.s - B₀ * g.H ≤
        (L₀ - L) * v + (6*B₀ - L₀) * g.u + (B₀ * tl + tl) := by
      rw [hH]
      exact ds_defect_aux hL.le hL1.le hLL.le hB₀ hcross hf.1 hf.2 hroot hs.2 hwv ht.1
    have hC := h.low_identity v hv0 hv1
    unfold lowDefect at hC
    have hq0 : 0 ≤ dens B₀ L₀ L A D v := by linarith
    have hqd := ds_low_aux hq0 hq.2.le hF.B₀_lt hL.le hσ0 hu0 hdef hC hq6 htl ht4
    have hneed := deletionNeed_le_defect (B₀ := B₀) (L₀ := L₀) (P := g.PC) hcap
    unfold lowPart
    calc dens B₀ L₀ L A D v * deletionNeed B₀ L₀ c₀ g.PC g.s g.H
        ≤ dens B₀ L₀ L A D v * max 0 ((g.PC + L₀ * g.s - B₀ * g.H) / L₀) :=
          mul_le_mul_of_nonneg_left hneed hq0
      _ = max 0 (dens B₀ L₀ L A D v * (g.PC + L₀ * g.s - B₀ * g.H) / L₀) := by
          rw [mul_max_of_nonneg _ _ hq0, mul_zero, mul_div_assoc]
      _ ≤ g.u + ε/16 := by
          refine max_le (by linarith) ?_
          rw [div_le_iff₀ hL]; linarith
  · -- HIGH: the uniform reserve of `J` on `[q(v), 3/4]`
    refine highSup_le hq.2.le fun ν hν1 hν2 => ?_
    have hJ := hJr v hv0 hv1 ν hν1 hν2
    rw [highJ_eq, one_sub_rhoOf] at hJ
    simp only [width] at hJ
    obtain ⟨k0, k1⟩ := rhoGap_mem (show 0 ≤ ν by linarith) hν2
    unfold highTerm
    rw [hH]
    have := ds_high_aux (show 0 ≤ ν by linarith) (by linarith) k0 k1 hPS hu0 hu1 ht.1 htl hJ
      (by linarith)
    linarith

theorem ds_reference (h : HybridGates B₀ L₀ c₀ B L c A D) (hL : 0 < L₀) :
    ∃ ρ, ReferenceAt (dsData B₀ L₀ c₀ B L c A D hL) ρ := by
  obtain ⟨r1, h1, hr1⟩ := h.principal_reference
  obtain ⟨r2, h2, hr2⟩ := h.second_reference
  obtain ⟨r3, h3, hr3⟩ := h.second_diagonal
  obtain ⟨r4, h4, hr4⟩ := h.reference_upper_positive
  refine ⟨min (min r1 r2) (min r3 r4), lt_min (lt_min h1 h2) (lt_min h3 h4), ?_⟩
  intro ε _ S hS0 hSc
  simp only [dsData, dsSel] at hS0 hSc ⊢
  have hv0 : 0 ≤ S - cross B₀ L₀ B L := by linarith
  have hv1 : S - cross B₀ L₀ B L ≤ c - cross B₀ L₀ B L := by linarith
  rw [max_eq_right hv0]
  have hwS : width B₀ L₀ B L (S - cross B₀ L₀ B L) = S := by unfold width; ring
  have g1 := hr1 _ hv0 hv1
  have g2 := hr2 _ hv0 hv1
  have g3 := hr3 _ hv0 hv1
  have g4 := hr4 _ hv0 hv1
  simp only [gPrincipal, gSecondRef, gSecondDiag, gRefUpper, hwS] at g1 g2 g3 g4
  have m1 : min (min r1 r2) (min r3 r4) ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have m2 : min (min r1 r2) (min r3 r4) ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have m3 : min (min r1 r2) (min r3 r4) ≤ r3 := (min_le_right _ _).trans (min_le_left _ _)
  have m4 : min (min r1 r2) (min r3 r4) ≤ r4 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The certified hybrid gates (with the face facts) imply the generic step gates. -/
theorem dsGates (h : HybridGates B₀ L₀ c₀ B L c A D) (hF : DSFace B₀ L₀ c₀ B L c)
    (hL : 0 < L₀) : StepGates (dsData B₀ L₀ c₀ B L c A D hL) where
  face := by
    have := hF.cross_nonneg; have := h.width_pos
    exact ⟨hF.B_le, hF.B₀_lt, hF.L_lt, hF.one_lt_L, by show 0 < c; linarith, hF.c_lt,
      hF.c₀_lt⟩
  kappa := rfl
  crossing := ⟨hF.cross_nonneg, le_of_eq hF.cross_mul, fun _ => h.dsCross_lt_c₀.le⟩
  envelope := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [dsData] <;> norm_num
  sel_spec := by
    intro ε _
    have hs0 := hF.cross_nonneg
    have hcs := h.width_pos
    simp only [dsData, dsSel]
    refine ⟨fun x hx y hy hxy => ?_, fun w hw0 hwc => ?_⟩
    · exact h.dsSel_mono (le_max_left _ _) (max_le_max le_rfl (by linarith))
        (max_le hcs.le (by linarith [hy.2]))
    · have hv0 : (0:ℝ) ≤ max 0 (w - cross B₀ L₀ B L) := le_max_left _ _
      have hv1 : max 0 (w - cross B₀ L₀ B L) ≤ c - cross B₀ L₀ B L :=
        max_le hcs.le (by linarith)
      refine ⟨h.dsSel_nonneg hv0 hv1, ?_⟩
      rcases le_total w (cross B₀ L₀ B L) with hle | hle
      · rw [max_eq_left (by linarith), sel_zero]; exact hw0
      · rw [max_eq_right (by linarith)] at hv1 ⊢
        have := h.retained_width.pos _ (by linarith) hv1
        simp only [gRetainedWidth, width] at this
        linarith
  ledger := fun ε hε => ds_ledger h hF hL hε
  reference := ds_reference h hL

end generic

/-! ### The two exact transitions -/

/-- G(9999/10000, 129/50, 3/25) → G(9959/10000, 5/2, 1/10), `A = 6/5`, `D = 140`. -/
theorem dsGates_first :
    StepGates (dsData (9999/10000) (129/50) (3/25) (9959/10000) (5/2) (1/10) (6/5) 140
      (by norm_num)) :=
  dsGates hybridGates_first ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩ _

/-- G(9959/10000, 5/2, 1/10) → G(4967/5000, 49/20, 1/10), `A = 7/10`, `D = 70`. -/
theorem dsGates_second :
    StepGates (dsData (9959/10000) (5/2) (1/10) (4967/5000) (49/20) (1/10) (7/10) 70
      (by norm_num)) :=
  dsGates hybridGates_second ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩ _

/-- G(4967/5000, 49/20, 1/10) → G(99/100, 239/100, 1/10), `A = 3/5`, `D = 35`
(added 2026-10-26: third density-split transition). -/
theorem dsGates_third :
    StepGates (dsData (4967/5000) (49/20) (1/10) (99/100) (239/100) (1/10) (3/5) 35
      (by norm_num)) :=
  dsGates hybridGates_third ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩ _

end
end QRH.DensitySplitThird.Density
