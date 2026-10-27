/- Copyright (c) 2026 Sil. Apache-2.0.
Generic exact scalar gates of one variable-density crossing step
G(B0,L0,c0) → G(B,L,c) (density-split argument, Sections 4–5).

With `s0 = (B0-B)/(L0-L)`, the excess `v ∈ [0, c - s0]`, `w = s0 + v`,
`u(v) = A v/(1+D v)`, `q(v) = (999/1000) L0 A/((L0-L)(1+D v)+(6B0-L0)A)`,
`ρ(ν) = 1 - 10ν/(15-6ν)` and `H = 1 - 6u`, the structure `HybridGates` records a uniform
positive reserve for each of the thirteen gates of `certify_density_hybrid.py`
(plus the density floor `q ≥ 13/20`), the LOW identity (C), and the facts used to reduce the
HIGH condition (D) to `ν = q(v)`.  This module proves arithmetic only; the analytic
density-split theorem is not stated here.  It also contains a small proved one-variable
Bernstein lemma used by the instance certificates. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace QRH.DensitySplitThird
noncomputable section

namespace Hybrid

/-! ### Scalar ingredients -/

/-- The crossing slope `s0 = (B0-B)/(L0-L)`. -/
def cross (B0 L0 B L : ℝ) : ℝ := (B0 - B) / (L0 - L)

/-- The marked width `w = s0 + v` at excess `v`. -/
def width (B0 L0 B L v : ℝ) : ℝ := cross B0 L0 B L + v

/-- The selected marked width `u(v) = A v/(1+D v)`. -/
def sel (A D v : ℝ) : ℝ := A * v / (1 + D * v)

/-- Numerator constant of the density threshold. -/
def densK (L0 A : ℝ) : ℝ := 999 / 1000 * L0 * A

/-- Denominator of the density threshold. -/
def densE (B0 L0 L A D v : ℝ) : ℝ := (L0 - L) * (1 + D * v) + (6 * B0 - L0) * A

/-- The variable density threshold
`q(v) = (999/1000) L0 A/((L0-L)(1+D v)+(6B0-L0)A)`. -/
def dens (B0 L0 L A D v : ℝ) : ℝ :=
  999 / 1000 * L0 * A / ((L0 - L) * (1 + D * v) + (6 * B0 - L0) * A)

theorem dens_eq (B0 L0 L A D v : ℝ) :
    dens B0 L0 L A D v = densK L0 A / densE B0 L0 L A D v := rfl

/-- `ρ(ν) = 1 - 10ν/(15-6ν)`. -/
def rhoOf (ν : ℝ) : ℝ := 1 - 10 * ν / (15 - 6 * ν)

/-- The packed radius `H = 1 - 6u`. -/
def packed (A D v : ℝ) : ℝ := 1 - 6 * sel A D v

/-- The HIGH functional
`J(w,ν) = 1-ρ(ν)-νB+ν(L-1)w-[6(1-ρ(ν))-ν-1]u`. -/
def highJ (B L w u ν : ℝ) : ℝ :=
  1 - rhoOf ν - ν * B + ν * (L - 1) * w - (6 * (1 - rhoOf ν) - ν - 1) * u

/-- The LOW defect `L0 u - q((L0-L)v+(6B0-L0)u)`. -/
def lowDefect (B0 L0 L A D v : ℝ) : ℝ :=
  L0 * sel A D v - dens B0 L0 L A D v * ((L0 - L) * v + (6 * B0 - L0) * sel A D v)

/-! ### The gates, as functions of the excess `v` -/

def gQLower (B0 L0 L A D v : ℝ) : ℝ := dens B0 L0 L A D v - 1 / 2
def gQUpper (B0 L0 L A D v : ℝ) : ℝ := 3 / 4 - dens B0 L0 L A D v
/-- Density floor `q ≥ 13/20` (not among the thirteen gates of the JSON). -/
def gQFloor (B0 L0 L A D v : ℝ) : ℝ := dens B0 L0 L A D v - 13 / 20
def gHLower (A D v : ℝ) : ℝ := packed A D v - 9 / 10
def gRetainedCap (B0 L0 c0 B L A D v : ℝ) : ℝ :=
  c0 * packed A D v - (width B0 L0 B L v - sel A D v)
def gRetainedWidth (B0 L0 B L A D v : ℝ) : ℝ := width B0 L0 B L v - sel A D v
/-- `(C)/v` in cancelled form, `(1/1000) L0 A/(1+D v)`. -/
def gLowPerWidth (L0 A D v : ℝ) : ℝ := 1 / 1000 * L0 * A / (1 + D * v)
def gHighAtQ (B0 L0 B L A D v : ℝ) : ℝ :=
  highJ B L (width B0 L0 B L v) (sel A D v) (dens B0 L0 L A D v)
def gHighDeriv (B0 L0 B L A D v : ℝ) : ℝ :=
  25 / 24 * packed A D v - (B - (L - 1) * width B0 L0 B L v - sel A D v)
def gPrincipal (B0 L0 B L A D v : ℝ) : ℝ :=
  1 - B + (L - 2) * width B0 L0 B L v - 9 / 2 * sel A D v
def gSecondRef (B0 L0 B L A D v : ℝ) : ℝ :=
  1 / 20 + 3 / 2 * (1 - B) + (3 / 2 * L - 5 / 2) * width B0 L0 B L v - 9 / 2 * sel A D v
def gSecondDiag (B0 L0 B L A D v : ℝ) : ℝ :=
  1 - B + (L - 1) * width B0 L0 B L v - 4 * sel A D v
def gRefUpper (B0 L0 B L A D v : ℝ) : ℝ :=
  1 / 3 - 2 * width B0 L0 B L v - 3 * sel A D v
/-- `du/dv = A/(1+D v)^2`. -/
def gSelDeriv (A D v : ℝ) : ℝ := A / (1 + D * v) ^ 2

end Hybrid

open Hybrid

/-- Uniform positivity of `f` on `[a,b]`: a fixed reserve `r > 0` with `r ≤ f` there. -/
def UnifPos (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ v, a ≤ v → v ≤ b → r ≤ f v

theorem UnifPos.pos {f : ℝ → ℝ} {a b : ℝ} (h : UnifPos f a b) :
    ∀ v, a ≤ v → v ≤ b → 0 < f v := by
  obtain ⟨r, hr, h⟩ := h
  intro v h0 h1
  exact lt_of_lt_of_le hr (h v h0 h1)

/-- The exact scalar gates of one hybrid (variable-density) transition from the parent
`G(B0,L0,c0)` to the child `G(B,L,c)` with selection parameters `A`, `D`.
Every gate has a uniform positive reserve on the whole closed excess interval
`0 ≤ v ≤ c - s0`. -/
structure HybridGates (B0 L0 c0 B L c A D : ℝ) : Prop where
  width_pos : 0 < c - cross B0 L0 B L
  sel_den_pos : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → 0 < 1 + D * v
  dens_den_pos : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → 0 < densE B0 L0 L A D v
  q_lower : UnifPos (gQLower B0 L0 L A D) 0 (c - cross B0 L0 B L)
  q_upper : UnifPos (gQUpper B0 L0 L A D) 0 (c - cross B0 L0 B L)
  q_floor : UnifPos (gQFloor B0 L0 L A D) 0 (c - cross B0 L0 B L)
  H_lower : UnifPos (gHLower A D) 0 (c - cross B0 L0 B L)
  retained_cap : UnifPos (gRetainedCap B0 L0 c0 B L A D) 0 (c - cross B0 L0 B L)
  retained_width : UnifPos (gRetainedWidth B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  /-- The LOW identity (C): `L0 u - q((L0-L)v+(6B0-L0)u) = (1/1000) L0 u`. -/
  low_identity : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L →
    lowDefect B0 L0 L A D v = 1 / 1000 * L0 * sel A D v
  low_div_eq : ∀ v, 0 < v → v ≤ c - cross B0 L0 B L →
    lowDefect B0 L0 L A D v / v = gLowPerWidth L0 A D v
  low_per_excess_width : UnifPos (gLowPerWidth L0 A D) 0 (c - cross B0 L0 B L)
  high_at_q : UnifPos (gHighAtQ B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  high_density_derivative : UnifPos (gHighDeriv B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  principal_reference : UnifPos (gPrincipal B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  second_reference : UnifPos (gSecondRef B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  second_diagonal : UnifPos (gSecondDiag B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  reference_upper_positive : UnifPos (gRefUpper B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  sel_hasDerivAt : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L →
    HasDerivAt (sel A D) (gSelDeriv A D v) v
  selection_monotonicity : UnifPos (gSelDeriv A D) 0 (c - cross B0 L0 B L)

namespace Hybrid

/-! ### The HIGH functional is increasing in the density on `[1/2, 3/4]` -/

theorem one_sub_rhoOf (ν : ℝ) : 1 - rhoOf ν = 10 * ν / (15 - 6 * ν) := by
  unfold rhoOf; ring

theorem highJ_eq (B L w u ν : ℝ) :
    highJ B L w u ν = (1 - rhoOf ν) * (1 - 6 * u) - ν * (B - (L - 1) * w - u) + u := by
  unfold highJ; ring

theorem one_sub_rhoOf_sub (ν₁ ν₂ : ℝ) (h₁ : 15 - 6 * ν₁ ≠ 0) (h₂ : 15 - 6 * ν₂ ≠ 0) :
    (1 - rhoOf ν₂) - (1 - rhoOf ν₁) =
      (ν₂ - ν₁) * (150 / ((15 - 6 * ν₁) * (15 - 6 * ν₂))) := by
  rw [one_sub_rhoOf, one_sub_rhoOf, div_sub_div _ _ h₂ h₁, mul_div_assoc',
    div_eq_div_iff (mul_ne_zero h₂ h₁) (mul_ne_zero h₁ h₂)]
  ring

theorem highJ_sub (B L w u ν₁ ν₂ : ℝ) (h₁ : 15 - 6 * ν₁ ≠ 0) (h₂ : 15 - 6 * ν₂ ≠ 0) :
    highJ B L w u ν₂ - highJ B L w u ν₁ =
      (ν₂ - ν₁) * (150 / ((15 - 6 * ν₁) * (15 - 6 * ν₂)) * (1 - 6 * u)
        - (B - (L - 1) * w - u)) := by
  have hom := one_sub_rhoOf_sub ν₁ ν₂ h₁ h₂
  rw [highJ_eq, highJ_eq]
  linear_combination (1 - 6 * u) * hom

/-- `150/((15-6ν₁)(15-6ν₂)) ≥ 25/24` for `ν₁, ν₂ ∈ [1/2,3/4]`. -/
theorem density_slope_ge (ν₁ ν₂ : ℝ) (h₁ : 1 / 2 ≤ ν₁) (h₁' : ν₁ ≤ 3 / 4)
    (h₂ : 1 / 2 ≤ ν₂) (h₂' : ν₂ ≤ 3 / 4) :
    (25 : ℝ) / 24 ≤ 150 / ((15 - 6 * ν₁) * (15 - 6 * ν₂)) := by
  have ha : 0 < 15 - 6 * ν₁ := by linarith
  have hb : 0 < 15 - 6 * ν₂ := by linarith
  have hab : 0 < (15 - 6 * ν₁) * (15 - 6 * ν₂) := mul_pos ha hb
  rw [le_div_iff₀ hab]
  have hle : (15 - 6 * ν₁) * (15 - 6 * ν₂) ≤ 144 := by nlinarith
  linarith

/-- Quantitative monotonicity of `J` in the density on `[1/2,3/4]`:
`J(ν₂) - J(ν₁) ≥ (ν₂-ν₁)((25/24)H - [B-(L-1)w-u])`. -/
theorem highJ_mono_quant (B L w u ν₁ ν₂ : ℝ) (h₁ : 1 / 2 ≤ ν₁) (h₁₂ : ν₁ ≤ ν₂)
    (h₂ : ν₂ ≤ 3 / 4) (hH : 0 ≤ 1 - 6 * u) :
    highJ B L w u ν₁ + (ν₂ - ν₁) * (25 / 24 * (1 - 6 * u) - (B - (L - 1) * w - u)) ≤
      highJ B L w u ν₂ := by
  have ha : 15 - 6 * ν₁ ≠ 0 := by linarith
  have hb : 15 - 6 * ν₂ ≠ 0 := by linarith
  have hs := highJ_sub B L w u ν₁ ν₂ ha hb
  have hk := mul_le_mul_of_nonneg_right
    (density_slope_ge ν₁ ν₂ h₁ (by linarith) (by linarith) h₂) hH
  have hd : 0 ≤ ν₂ - ν₁ := sub_nonneg.2 h₁₂
  have := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hk (B - (L - 1) * w - u)) hd
  linarith

theorem highJ_mono (B L w u ν₁ ν₂ : ℝ) (h₁ : 1 / 2 ≤ ν₁) (h₁₂ : ν₁ ≤ ν₂)
    (h₂ : ν₂ ≤ 3 / 4) (hH : 0 ≤ 1 - 6 * u)
    (hK : 0 ≤ 25 / 24 * (1 - 6 * u) - (B - (L - 1) * w - u)) :
    highJ B L w u ν₁ ≤ highJ B L w u ν₂ := by
  have := highJ_mono_quant B L w u ν₁ ν₂ h₁ h₁₂ h₂ hH
  nlinarith [mul_nonneg (sub_nonneg.2 h₁₂) hK]

/-- The density derivative `dJ/dν = 150H/(15-6ν)^2 - [B-(L-1)w-u]`. -/
theorem highJ_hasDerivAt (B L w u ν : ℝ) (h : 15 - 6 * ν ≠ 0) :
    HasDerivAt (fun x => highJ B L w u x)
      (150 / (15 - 6 * ν) ^ 2 * (1 - 6 * u) - (B - (L - 1) * w - u)) ν := by
  have h1 : HasDerivAt (fun x : ℝ => 10 * x) 10 ν :=
    ((hasDerivAt_id' ν).const_mul (10 : ℝ)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => 15 - 6 * x) (-6) ν :=
    (((hasDerivAt_id' ν).const_mul (6 : ℝ)).const_sub (15 : ℝ)).congr_deriv (by ring)
  have hf : HasDerivAt (fun x : ℝ => 10 * x / (15 - 6 * x)) (150 / (15 - 6 * ν) ^ 2) ν :=
    (h1.div h2 h).congr_deriv (by congr 1; ring)
  have hJ := ((hf.mul_const (1 - 6 * u)).sub
    ((hasDerivAt_id' ν).mul_const (B - (L - 1) * w - u))).add_const u
  have hfun : (fun x => highJ B L w u x) =
      (fun x => 10 * x / (15 - 6 * x) * (1 - 6 * u) - x * (B - (L - 1) * w - u) + u) := by
    funext x
    rw [highJ_eq, one_sub_rhoOf]
  rw [hfun]
  exact hJ.congr_deriv (by ring)

/-- The derivative bound `dJ/dν ≥ (25/24)H - [B-(L-1)w-u]` for `ν ∈ [1/2,3/4]`. -/
theorem highJ_deriv_ge (B L w u ν : ℝ) (h₁ : 1 / 2 ≤ ν) (h₂ : ν ≤ 3 / 4)
    (hH : 0 ≤ 1 - 6 * u) :
    25 / 24 * (1 - 6 * u) - (B - (L - 1) * w - u) ≤
      150 / (15 - 6 * ν) ^ 2 * (1 - 6 * u) - (B - (L - 1) * w - u) := by
  have := mul_le_mul_of_nonneg_right (density_slope_ge ν ν h₁ h₂ h₁ h₂) hH
  rw [sq]
  linarith

/-! ### Cleared forms of the gates (used by the instance certificates) -/

section Cleared
variable (B0 L0 c0 B L A D v : ℝ)

theorem sel_mul (hx : 1 + D * v ≠ 0) : sel A D v * (1 + D * v) = A * v :=
  div_mul_cancel₀ _ hx

theorem dens_mul (hE : densE B0 L0 L A D v ≠ 0) :
    dens B0 L0 L A D v * densE B0 L0 L A D v = densK L0 A :=
  div_mul_cancel₀ _ hE

theorem lowDefect_eq (hx : 1 + D * v ≠ 0) (hE : densE B0 L0 L A D v ≠ 0) :
    lowDefect B0 L0 L A D v = 1 / 1000 * L0 * sel A D v := by
  have hs := sel_mul A D v hx
  have hq : dens B0 L0 L A D v * ((L0 - L) * (1 + D * v) + (6 * B0 - L0) * A) =
      999 / 1000 * L0 * A := dens_mul B0 L0 L A D v hE
  apply mul_right_cancel₀ hx
  unfold lowDefect
  linear_combination (999 / 1000 * L0 - dens B0 L0 L A D v * (6 * B0 - L0)) * hs - v * hq

theorem lowDefect_div_eq (hv : v ≠ 0) (hx : 1 + D * v ≠ 0) (hE : densE B0 L0 L A D v ≠ 0) :
    lowDefect B0 L0 L A D v / v = gLowPerWidth L0 A D v := by
  rw [lowDefect_eq B0 L0 L A D v hx hE, div_eq_iff hv]
  unfold gLowPerWidth sel
  ring

theorem sel_hasDerivAt (hx : 1 + D * v ≠ 0) : HasDerivAt (sel A D) (gSelDeriv A D v) v := by
  have h1 : HasDerivAt (fun x : ℝ => A * x) A v :=
    ((hasDerivAt_id' v).const_mul A).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => 1 + D * x) D v :=
    (((hasDerivAt_id' v).const_mul D).const_add (1 : ℝ)).congr_deriv (by ring)
  exact (h1.div h2 hx).congr_deriv (by unfold gSelDeriv; congr 1; ring)

theorem gQLower_mul (hE : densE B0 L0 L A D v ≠ 0) :
    gQLower B0 L0 L A D v * densE B0 L0 L A D v =
      densK L0 A - densE B0 L0 L A D v / 2 := by
  have hq := dens_mul B0 L0 L A D v hE
  unfold gQLower
  linear_combination hq

theorem gQUpper_mul (hE : densE B0 L0 L A D v ≠ 0) :
    gQUpper B0 L0 L A D v * densE B0 L0 L A D v =
      3 / 4 * densE B0 L0 L A D v - densK L0 A := by
  have hq := dens_mul B0 L0 L A D v hE
  unfold gQUpper
  linear_combination (-1 : ℝ) * hq

theorem gQFloor_mul (hE : densE B0 L0 L A D v ≠ 0) :
    gQFloor B0 L0 L A D v * densE B0 L0 L A D v =
      densK L0 A - 13 / 20 * densE B0 L0 L A D v := by
  have hq := dens_mul B0 L0 L A D v hE
  unfold gQFloor
  linear_combination hq

theorem gHLower_mul (hx : 1 + D * v ≠ 0) :
    gHLower A D v * (1 + D * v) = (1 + D * v) / 10 - 6 * A * v := by
  have hs := sel_mul A D v hx
  unfold gHLower packed
  linear_combination (-6 : ℝ) * hs

theorem gRetainedCap_mul (hx : 1 + D * v ≠ 0) :
    gRetainedCap B0 L0 c0 B L A D v * (1 + D * v) =
      c0 * ((1 + D * v) - 6 * A * v) - width B0 L0 B L v * (1 + D * v) + A * v := by
  have hs := sel_mul A D v hx
  unfold gRetainedCap packed
  linear_combination (1 - 6 * c0) * hs

theorem gRetainedWidth_mul (hx : 1 + D * v ≠ 0) :
    gRetainedWidth B0 L0 B L A D v * (1 + D * v) =
      width B0 L0 B L v * (1 + D * v) - A * v := by
  have hs := sel_mul A D v hx
  unfold gRetainedWidth
  linear_combination (-1 : ℝ) * hs

theorem gLowPerWidth_mul (hx : 1 + D * v ≠ 0) :
    gLowPerWidth L0 A D v * (1 + D * v) = 1 / 1000 * L0 * A :=
  div_mul_cancel₀ _ hx

theorem gHighAtQ_mul (hx : 1 + D * v ≠ 0) (hE : densE B0 L0 L A D v ≠ 0)
    (hF : 15 * densE B0 L0 L A D v - 6 * densK L0 A ≠ 0) :
    gHighAtQ B0 L0 B L A D v *
        ((1 + D * v) * densE B0 L0 L A D v * (15 * densE B0 L0 L A D v - 6 * densK L0 A)) =
      10 * densK L0 A * ((1 + D * v) - 6 * A * v) * densE B0 L0 L A D v
        - densK L0 A * (15 * densE B0 L0 L A D v - 6 * densK L0 A) *
            (B * (1 + D * v) - (L - 1) * width B0 L0 B L v * (1 + D * v) - A * v)
        + A * v * densE B0 L0 L A D v * (15 * densE B0 L0 L A D v - 6 * densK L0 A) := by
  have hs := sel_mul A D v hx
  have hq := dens_mul B0 L0 L A D v hE
  have h15 : 15 - 6 * dens B0 L0 L A D v ≠ 0 := by
    intro h0
    apply hF
    linear_combination densE B0 L0 L A D v * h0 + 6 * hq
  have hom : (1 - rhoOf (dens B0 L0 L A D v)) * (15 - 6 * dens B0 L0 L A D v) =
      10 * dens B0 L0 L A D v := by
    rw [one_sub_rhoOf]
    exact div_mul_cancel₀ _ h15
  have hOF : (1 - rhoOf (dens B0 L0 L A D v)) *
      (15 * densE B0 L0 L A D v - 6 * densK L0 A) = 10 * densK L0 A := by
    linear_combination densE B0 L0 L A D v * hom
      + (6 * (1 - rhoOf (dens B0 L0 L A D v)) + 10) * hq
  unfold gHighAtQ
  rw [highJ_eq]
  linear_combination
    ((1 - 6 * sel A D v) * (1 + D * v) * densE B0 L0 L A D v) * hOF
    - ((B - (L - 1) * width B0 L0 B L v - sel A D v) * (1 + D * v)
        * (15 * densE B0 L0 L A D v - 6 * densK L0 A)) * hq
    + (-60 * densK L0 A * densE B0 L0 L A D v
        + densK L0 A * (15 * densE B0 L0 L A D v - 6 * densK L0 A)
        + densE B0 L0 L A D v * (15 * densE B0 L0 L A D v - 6 * densK L0 A)) * hs

theorem gHighDeriv_mul (hx : 1 + D * v ≠ 0) :
    gHighDeriv B0 L0 B L A D v * (1 + D * v) =
      25 / 24 * ((1 + D * v) - 6 * A * v)
        - (B * (1 + D * v) - (L - 1) * width B0 L0 B L v * (1 + D * v) - A * v) := by
  have hs := sel_mul A D v hx
  unfold gHighDeriv packed
  linear_combination (-25 / 4 + 1 : ℝ) * hs

theorem gPrincipal_mul (hx : 1 + D * v ≠ 0) :
    gPrincipal B0 L0 B L A D v * (1 + D * v) =
      (1 - B + (L - 2) * width B0 L0 B L v) * (1 + D * v) - 9 / 2 * A * v := by
  have hs := sel_mul A D v hx
  unfold gPrincipal
  linear_combination (-9 / 2 : ℝ) * hs

theorem gSecondRef_mul (hx : 1 + D * v ≠ 0) :
    gSecondRef B0 L0 B L A D v * (1 + D * v) =
      (1 / 20 + 3 / 2 * (1 - B) + (3 / 2 * L - 5 / 2) * width B0 L0 B L v) * (1 + D * v)
        - 9 / 2 * A * v := by
  have hs := sel_mul A D v hx
  unfold gSecondRef
  linear_combination (-9 / 2 : ℝ) * hs

theorem gSecondDiag_mul (hx : 1 + D * v ≠ 0) :
    gSecondDiag B0 L0 B L A D v * (1 + D * v) =
      (1 - B + (L - 1) * width B0 L0 B L v) * (1 + D * v) - 4 * A * v := by
  have hs := sel_mul A D v hx
  unfold gSecondDiag
  linear_combination (-4 : ℝ) * hs

theorem gRefUpper_mul (hx : 1 + D * v ≠ 0) :
    gRefUpper B0 L0 B L A D v * (1 + D * v) =
      (1 / 3 - 2 * width B0 L0 B L v) * (1 + D * v) - 3 * A * v := by
  have hs := sel_mul A D v hx
  unfold gRefUpper
  linear_combination (-3 : ℝ) * hs

theorem gSelDeriv_mul (hx : 1 + D * v ≠ 0) :
    gSelDeriv A D v * (1 + D * v) ^ 2 = A :=
  div_mul_cancel₀ _ (pow_ne_zero 2 hx)

end Cleared

/-- Transfer a cleared form `g·Dg = Ng` to another representation `g·d = n`
when `Ng·d = n·Dg` is a polynomial identity. -/
theorem mul_eq_of_cleared {g Dg Ng d n : ℝ} (hDg : Dg ≠ 0) (h₁ : g * Dg = Ng)
    (h₂ : Ng * d = n * Dg) : g * d = n := by
  apply mul_right_cancel₀ hDg
  calc g * d * Dg = (g * Dg) * d := by ring
    _ = Ng * d := by rw [h₁]
    _ = n * Dg := h₂

/-! ### A one-variable Bernstein lemma (degrees `0` to `4`) -/

def bern0 (b0 _t : ℝ) : ℝ := b0
def bern1 (b0 b1 t : ℝ) : ℝ := b0 * (1 - t) + b1 * t
def bern2 (b0 b1 b2 t : ℝ) : ℝ := b0 * (1 - t) ^ 2 + 2 * b1 * t * (1 - t) + b2 * t ^ 2
def bern3 (b0 b1 b2 b3 t : ℝ) : ℝ :=
  b0 * (1 - t) ^ 3 + 3 * b1 * t * (1 - t) ^ 2 + 3 * b2 * t ^ 2 * (1 - t) + b3 * t ^ 3
def bern4 (b0 b1 b2 b3 b4 t : ℝ) : ℝ :=
  b0 * (1 - t) ^ 4 + 4 * b1 * t * (1 - t) ^ 3 + 6 * b2 * t ^ 2 * (1 - t) ^ 2
    + 4 * b3 * t ^ 3 * (1 - t) + b4 * t ^ 4

section BernsteinBounds
variable {t m b0 b1 b2 b3 b4 : ℝ}

theorem bern0_ge (h0 : m ≤ b0) : m ≤ bern0 b0 t := h0
theorem bern0_le (h0 : b0 ≤ m) : bern0 b0 t ≤ m := h0

theorem bern1_ge (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : m ≤ b0) (h1 : m ≤ b1) :
    m ≤ bern1 b0 b1 t := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : bern1 b0 b1 t - m = (b0 - m) * (1 - t) + (b1 - m) * t := by unfold bern1; ring
  have := mul_nonneg (sub_nonneg.2 h0) hs
  have := mul_nonneg (sub_nonneg.2 h1) ht
  linarith

theorem bern1_le (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : b0 ≤ m) (h1 : b1 ≤ m) :
    bern1 b0 b1 t ≤ m := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : m - bern1 b0 b1 t = (m - b0) * (1 - t) + (m - b1) * t := by unfold bern1; ring
  have := mul_nonneg (sub_nonneg.2 h0) hs
  have := mul_nonneg (sub_nonneg.2 h1) ht
  linarith

theorem bern2_ge (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : m ≤ b0) (h1 : m ≤ b1) (h2 : m ≤ b2) :
    m ≤ bern2 b0 b1 b2 t := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : bern2 b0 b1 b2 t - m = (b0 - m) * (1 - t) ^ 2 + 2 * ((b1 - m) * (t * (1 - t)))
      + (b2 - m) * t ^ 2 := by unfold bern2; ring
  have := mul_nonneg (sub_nonneg.2 h0) (pow_nonneg hs 2)
  have := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ht hs)
  have := mul_nonneg (sub_nonneg.2 h2) (pow_nonneg ht 2)
  linarith

theorem bern2_le (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : b0 ≤ m) (h1 : b1 ≤ m) (h2 : b2 ≤ m) :
    bern2 b0 b1 b2 t ≤ m := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : m - bern2 b0 b1 b2 t = (m - b0) * (1 - t) ^ 2 + 2 * ((m - b1) * (t * (1 - t)))
      + (m - b2) * t ^ 2 := by unfold bern2; ring
  have := mul_nonneg (sub_nonneg.2 h0) (pow_nonneg hs 2)
  have := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ht hs)
  have := mul_nonneg (sub_nonneg.2 h2) (pow_nonneg ht 2)
  linarith

theorem bern3_ge (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : m ≤ b0) (h1 : m ≤ b1) (h2 : m ≤ b2)
    (h3 : m ≤ b3) : m ≤ bern3 b0 b1 b2 b3 t := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : bern3 b0 b1 b2 b3 t - m = (b0 - m) * (1 - t) ^ 3
      + 3 * ((b1 - m) * (t * (1 - t) ^ 2)) + 3 * ((b2 - m) * (t ^ 2 * (1 - t)))
      + (b3 - m) * t ^ 3 := by unfold bern3; ring
  have := mul_nonneg (sub_nonneg.2 h0) (pow_nonneg hs 3)
  have := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ht (pow_nonneg hs 2))
  have := mul_nonneg (sub_nonneg.2 h2) (mul_nonneg (pow_nonneg ht 2) hs)
  have := mul_nonneg (sub_nonneg.2 h3) (pow_nonneg ht 3)
  linarith

theorem bern3_le (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : b0 ≤ m) (h1 : b1 ≤ m) (h2 : b2 ≤ m)
    (h3 : b3 ≤ m) : bern3 b0 b1 b2 b3 t ≤ m := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : m - bern3 b0 b1 b2 b3 t = (m - b0) * (1 - t) ^ 3
      + 3 * ((m - b1) * (t * (1 - t) ^ 2)) + 3 * ((m - b2) * (t ^ 2 * (1 - t)))
      + (m - b3) * t ^ 3 := by unfold bern3; ring
  have := mul_nonneg (sub_nonneg.2 h0) (pow_nonneg hs 3)
  have := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ht (pow_nonneg hs 2))
  have := mul_nonneg (sub_nonneg.2 h2) (mul_nonneg (pow_nonneg ht 2) hs)
  have := mul_nonneg (sub_nonneg.2 h3) (pow_nonneg ht 3)
  linarith

theorem bern4_ge (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : m ≤ b0) (h1 : m ≤ b1) (h2 : m ≤ b2)
    (h3 : m ≤ b3) (h4 : m ≤ b4) : m ≤ bern4 b0 b1 b2 b3 b4 t := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : bern4 b0 b1 b2 b3 b4 t - m = (b0 - m) * (1 - t) ^ 4
      + 4 * ((b1 - m) * (t * (1 - t) ^ 3)) + 6 * ((b2 - m) * (t ^ 2 * (1 - t) ^ 2))
      + 4 * ((b3 - m) * (t ^ 3 * (1 - t))) + (b4 - m) * t ^ 4 := by unfold bern4; ring
  have := mul_nonneg (sub_nonneg.2 h0) (pow_nonneg hs 4)
  have := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ht (pow_nonneg hs 3))
  have := mul_nonneg (sub_nonneg.2 h2) (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hs 2))
  have := mul_nonneg (sub_nonneg.2 h3) (mul_nonneg (pow_nonneg ht 3) hs)
  have := mul_nonneg (sub_nonneg.2 h4) (pow_nonneg ht 4)
  linarith

theorem bern4_le (ht : 0 ≤ t) (ht' : t ≤ 1) (h0 : b0 ≤ m) (h1 : b1 ≤ m) (h2 : b2 ≤ m)
    (h3 : b3 ≤ m) (h4 : b4 ≤ m) : bern4 b0 b1 b2 b3 b4 t ≤ m := by
  have hs : 0 ≤ 1 - t := by linarith
  have e : m - bern4 b0 b1 b2 b3 b4 t = (m - b0) * (1 - t) ^ 4
      + 4 * ((m - b1) * (t * (1 - t) ^ 3)) + 6 * ((m - b2) * (t ^ 2 * (1 - t) ^ 2))
      + 4 * ((m - b3) * (t ^ 3 * (1 - t))) + (m - b4) * t ^ 4 := by unfold bern4; ring
  have := mul_nonneg (sub_nonneg.2 h0) (pow_nonneg hs 4)
  have := mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ht (pow_nonneg hs 3))
  have := mul_nonneg (sub_nonneg.2 h2) (mul_nonneg (pow_nonneg ht 2) (pow_nonneg hs 2))
  have := mul_nonneg (sub_nonneg.2 h3) (mul_nonneg (pow_nonneg ht 3) hs)
  have := mul_nonneg (sub_nonneg.2 h4) (pow_nonneg ht 4)
  linarith

end BernsteinBounds

/-- One Bernstein box: if on `[lo,hi]` we have `g·d = n`, and after the affine change
`v = lo + (hi-lo) t` the numerator is `≥ m ≥ 0` and the denominator lies in `(0, M]`,
then `g ≥ m/M` on the box. -/
theorem box_lower {g n d : ℝ → ℝ} {lo hi m M : ℝ} (hlh : lo < hi) (hm : 0 ≤ m)
    (hgd : ∀ v, lo ≤ v → v ≤ hi → g v * d v = n v)
    (hn : ∀ t, 0 ≤ t → t ≤ 1 → m ≤ n (lo + (hi - lo) * t))
    (hd : ∀ t, 0 ≤ t → t ≤ 1 → 0 < d (lo + (hi - lo) * t))
    (hdM : ∀ t, 0 ≤ t → t ≤ 1 → d (lo + (hi - lo) * t) ≤ M) :
    ∀ v, lo ≤ v → v ≤ hi → m / M ≤ g v := by
  intro v h0 h1
  have hw : 0 < hi - lo := sub_pos.2 hlh
  set t := (v - lo) / (hi - lo) with ht
  have hv : lo + (hi - lo) * t = v := by rw [ht]; field_simp; ring
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hw.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hw]; linarith
  have hn' := hn t ht0 ht1
  have hd' := hd t ht0 ht1
  have hdM' := hdM t ht0 ht1
  rw [hv] at hn' hd' hdM'
  have hg : g v = n v / d v := by rw [eq_div_iff hd'.ne', hgd v h0 h1]
  rw [hg]
  have hM : 0 < M := lt_of_lt_of_le hd' hdM'
  calc m / M ≤ m / d v := div_le_div_of_nonneg_left hm hd' hdM'
    _ ≤ n v / d v := div_le_div_of_nonneg_right hn' hd'.le

/-- Uniform positivity from one box. -/
theorem unifPos_of_box {f : ℝ → ℝ} {a b r : ℝ} (hr : 0 < r)
    (h : ∀ v, a ≤ v → v ≤ b → r ≤ f v) : UnifPos f a b := ⟨r, hr, h⟩

/-- Gluing two boxes `[a,m]`, `[m,b]` with a common reserve. -/
theorem lower_of_two_boxes {f : ℝ → ℝ} {a m b r r₁ r₂ : ℝ}
    (h₁ : ∀ v, a ≤ v → v ≤ m → r₁ ≤ f v) (h₂ : ∀ v, m ≤ v → v ≤ b → r₂ ≤ f v)
    (hr₁ : r ≤ r₁) (hr₂ : r ≤ r₂) : ∀ v, a ≤ v → v ≤ b → r ≤ f v := by
  intro v h0 h1
  rcases le_total v m with h | h
  · exact le_trans hr₁ (h₁ v h0 h)
  · exact le_trans hr₂ (h₂ v h h1)

end Hybrid

/-! ### Consequences of `HybridGates` -/

namespace HybridGates
variable {B0 L0 c0 B L c A D : ℝ}

theorem dens_mem (h : HybridGates B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) :
    1 / 2 < dens B0 L0 L A D v ∧ dens B0 L0 L A D v < 3 / 4 := by
  have a := h.q_lower.pos v h0 h1
  have b := h.q_upper.pos v h0 h1
  unfold gQLower at a; unfold gQUpper at b
  constructor <;> linarith

theorem dens_floor (h : HybridGates B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) : 13 / 20 < dens B0 L0 L A D v := by
  have a := h.q_floor.pos v h0 h1
  unfold gQFloor at a
  linarith

/-- HIGH monotonicity: for `ν ∈ [q(v), 3/4]`, `J(w,ν) ≥ J(w,q(v))`, quantitatively. -/
theorem high_mono_quant (h : HybridGates B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) (ν : ℝ) (hν : dens B0 L0 L A D v ≤ ν) (hν' : ν ≤ 3 / 4) :
    gHighAtQ B0 L0 B L A D v + (ν - dens B0 L0 L A D v) * gHighDeriv B0 L0 B L A D v ≤
      highJ B L (width B0 L0 B L v) (sel A D v) ν := by
  have hq := h.dens_mem v h0 h1
  have hH := h.H_lower.pos v h0 h1
  unfold gHLower packed at hH
  have := highJ_mono_quant B L (width B0 L0 B L v) (sel A D v) (dens B0 L0 L A D v) ν
    hq.1.le hν hν' (by linarith)
  unfold gHighAtQ gHighDeriv packed
  exact this

theorem high_mono (h : HybridGates B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) (ν : ℝ) (hν : dens B0 L0 L A D v ≤ ν) (hν' : ν ≤ 3 / 4) :
    gHighAtQ B0 L0 B L A D v ≤ highJ B L (width B0 L0 B L v) (sel A D v) ν := by
  have := h.high_mono_quant v h0 h1 ν hν hν'
  have hK := h.high_density_derivative.pos v h0 h1
  nlinarith [mul_nonneg (sub_nonneg.2 hν) hK.le]

/-- The density derivative of `J` along the whole range `ν ∈ [q(v),3/4]` is at least
the (uniformly positive) gate `high_density_derivative`. -/
theorem high_deriv_ge (h : HybridGates B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) (ν : ℝ) (hν : dens B0 L0 L A D v ≤ ν) (hν' : ν ≤ 3 / 4) :
    HasDerivAt (fun x => highJ B L (width B0 L0 B L v) (sel A D v) x)
        (150 / (15 - 6 * ν) ^ 2 * (1 - 6 * sel A D v)
          - (B - (L - 1) * width B0 L0 B L v - sel A D v)) ν ∧
      gHighDeriv B0 L0 B L A D v ≤ 150 / (15 - 6 * ν) ^ 2 * (1 - 6 * sel A D v)
          - (B - (L - 1) * width B0 L0 B L v - sel A D v) := by
  have hq := h.dens_mem v h0 h1
  have hH := h.H_lower.pos v h0 h1
  unfold gHLower packed at hH
  refine ⟨highJ_hasDerivAt _ _ _ _ _ (by linarith), ?_⟩
  unfold gHighDeriv packed
  exact highJ_deriv_ge _ _ _ _ _ (by linarith) hν' (by linarith)

/-- A uniform HIGH reserve valid for every density `ν ∈ [q(v),3/4]`. -/
theorem high_reserve (h : HybridGates B0 L0 c0 B L c A D) :
    ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → ∀ ν,
      dens B0 L0 L A D v ≤ ν → ν ≤ 3 / 4 →
        r ≤ highJ B L (width B0 L0 B L v) (sel A D v) ν := by
  obtain ⟨r, hr, hJ⟩ := h.high_at_q
  exact ⟨r, hr, fun v h0 h1 ν hν hν' => le_trans (hJ v h0 h1) (h.high_mono v h0 h1 ν hν hν')⟩

end HybridGates

end
end QRH.DensitySplitThird
