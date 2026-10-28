/- Copyright (c) 2026 Sil. Apache-2.0.
Exact scalar chain of the finite native cube-free bootstrap
G(99999/100000, 93/25, 3/50) → G(9999/10000, 129/50, 3/25).
Four explicit steps are followed by 22 applications of one geometric recurrence;
the recurrence is handled by finite induction with closed forms. This module
proves arithmetic only: the analytic step is a hypothesis of `bootstrap`. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace QRH.DensitySplitThird
noncomputable section

/-- A global source face `P + L*S ≤ B`, `S ≤ c`. -/
structure Face where
  B : ℝ
  L : ℝ
  c : ℝ

/-- Native prime-slot cost `2*(7/8)-1` from the baseline bound. -/
def nativeK : ℝ := 3/4

/-- The strict scalar gates of one native cube-free step from parent `p` to child `n`
with selected marked fraction `a`. -/
structure NativeGates (p n : Face) (a : ℝ) : Prop where
  retention : 0 < a - nativeK * (p.L - n.L + (6*p.B - p.L)*a) / p.L
  cap : 0 < p.c*(1 - 6*a*n.c) - (1-a)*n.c
  principal : 0 < n.L - 2 - 9/2*a
  diagonal : 0 < n.L - 1 - 4*a
  secondRef : 0 < 3/2*n.L - 5/2 - 9/2*a
  refPos : 0 < 1/6 - (1+3/2*a)*n.c
  H : 0 < 1 - 6*a*n.c
  overshoot : 0 < 1 - nativeK*(6*p.B - p.L)/p.L
  B_le : n.B ≤ p.B
  B_lt : p.B < 1
  cap_lt : p.c < 1/6
  cap_pos : 0 < n.c
  a_pos : 0 < a
  L_lt : n.L < p.L

def face0 : Face := ⟨99999/100000, 93/25, 3/50⟩
def face1 : Face := ⟨9999/10000, 31/10, 3/50⟩
def face2 : Face := ⟨9999/10000, 29/10, 67/1000⟩
def face3 : Face := ⟨9999/10000, 14/5, 73/1000⟩
def face4 : Face := ⟨9999/10000, 68/25, 79/1000⟩

theorem gates01 : NativeGates face0 face1 (6/25) := by
  constructor <;> norm_num [face0, face1, nativeK]
theorem gates12 : NativeGates face1 face2 (9/50) := by
  constructor <;> norm_num [face1, face2, nativeK]
theorem gates23 : NativeGates face2 face3 (3/20) := by
  constructor <;> norm_num [face2, face3, nativeK]
theorem gates34 : NativeGates face3 face4 (31/200) := by
  constructor <;> norm_num [face3, face4, nativeK]

def Bg : ℝ := 9999/10000
/-- The native barrier `18B/7`. -/
def Ls : ℝ := 18*Bg/7

/-- Slope recurrence `L ↦ L* + (43/50)(L - L*)`. -/
def geoL : ℕ → ℝ
  | 0 => 68/25
  | n+1 => Ls + 43/50*(geoL n - Ls)

/-- Cap recurrence `c ↦ c/(47/50 + (9/25)c)`. -/
def geoC : ℕ → ℝ
  | 0 => 79/1000
  | n+1 => geoC n/(47/50 + 9/25*geoC n)

def geoFace (n : ℕ) : Face := ⟨Bg, geoL n, geoC n⟩

theorem geoFace_zero : geoFace 0 = face4 := by
  simp [geoFace, face4, geoL, geoC, Bg]

theorem geoL_closed (n : ℕ) : geoL n = Ls + (43/50:ℝ)^n*(68/25 - Ls) := by
  induction n with
  | zero => simp [geoL]
  | succ n ih => rw [geoL, ih, pow_succ]; ring

/-- Reciprocal cap `1/c_n = 6 + (1/c_0 - 6)(47/50)^n`. -/
def geoInv (n : ℕ) : ℝ := 6 + (1000/79 - 6)*(47/50:ℝ)^n

theorem geoInv_gt (n : ℕ) : 6 < geoInv n := by
  unfold geoInv
  have : 0 < (47/50:ℝ)^n := by positivity
  nlinarith

theorem geoInv_succ (n : ℕ) : geoInv (n+1) = 47/50*geoInv n + 9/25 := by
  unfold geoInv; rw [pow_succ]; ring

theorem geoC_closed (n : ℕ) : geoC n = 1/geoInv n := by
  induction n with
  | zero => norm_num [geoC, geoInv]
  | succ n ih =>
    have h := geoInv_gt n
    rw [geoC, ih, geoInv_succ]
    field_simp

theorem geoL_gt (n : ℕ) : Ls < geoL n := by
  rw [geoL_closed]
  have : 0 < (43/50:ℝ)^n := by positivity
  have hs : Ls < 68/25 := by norm_num [Ls, Bg]
  nlinarith

theorem geoInv_le (n : ℕ) (hn : n ≤ 22) : geoInv 22 ≤ geoInv n := by
  unfold geoInv
  have : (47/50:ℝ)^22 ≤ (47/50)^n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  nlinarith

theorem geoInv_22 : (354/50:ℝ) < geoInv 22 ∧ geoInv 22 < 25/3 := by
  unfold geoInv; norm_num

theorem geo_gates (n : ℕ) (hn : n < 22) :
    NativeGates (geoFace n) (geoFace (n+1)) (3/25) := by
  have hX := geoL_gt n
  have hX1 := geoL_gt (n+1)
  have hLs : Ls = 18*Bg/7 := rfl
  have hBg : Bg = 9999/10000 := rfl
  have hsucc : geoL (n+1) = Ls + 43/50*(geoL n - Ls) := rfl
  have hc := geoC_closed n
  have hc1 := geoC_closed (n+1)
  have hi := geoInv_gt n
  have hi1 := geoInv_gt (n+1)
  have hi22 := geoInv_le (n+1) (by omega)
  have h22 := geoInv_22.1
  have hrec := geoInv_succ n
  have hXpos : 0 < geoL n := by rw [hLs, hBg] at hX; linarith
  simp only [geoFace]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, by norm_num [Bg], ?_, ?_, by norm_num, ?_⟩
  · rw [hsucc, nativeK]
    have : (3/25:ℝ) - 3/4*(geoL n - (Ls + 43/50*(geoL n - Ls)) + (6*Bg - geoL n)*(3/25))/geoL n
        = (21/200*geoL n - 27*Bg/100)/geoL n := by
      field_simp; rw [hLs]; ring
    rw [this]; apply div_pos _ hXpos; rw [hLs] at hX; linarith
  · rw [hc, hc1, hrec]
    have h0 : 0 < geoInv n := by linarith
    have h1 : 0 < 47/50*geoInv n + 9/25 := by linarith
    rw [show 1/geoInv n*(1 - 6*(3/25)*(1/(47/50*geoInv n + 9/25)))
        - (1 - 3/25)*(1/(47/50*geoInv n + 9/25))
        = (3/50*geoInv n - 9/25)/(geoInv n*(47/50*geoInv n + 9/25))
        by field_simp; ring]
    apply div_pos _ (by positivity); nlinarith
  · rw [hLs, hBg] at hX1; linarith
  · rw [hLs, hBg] at hX1; linarith
  · rw [hLs, hBg] at hX1; linarith
  · rw [hc1]
    have h0 : 0 < geoInv (n+1) := by linarith
    rw [show (1:ℝ)/6 - (1 + 3/2*(3/25))*(1/geoInv (n+1))
        = (geoInv (n+1) - 354/50)/(6*geoInv (n+1)) by field_simp; ring]
    apply div_pos _ (by positivity); linarith
  · rw [hc1]
    have h0 : 0 < geoInv (n+1) := by linarith
    rw [show (1:ℝ) - 6*(3/25)*(1/geoInv (n+1)) = (geoInv (n+1) - 18/25)/geoInv (n+1)
        by field_simp; ring]
    apply div_pos _ h0; linarith
  · rw [nativeK]
    have : 1 - 3/4*(6*Bg - geoL n)/geoL n = (7/4*geoL n - 9/2*Bg)/geoL n := by
      field_simp; ring
    rw [this]; apply div_pos _ hXpos; rw [hLs] at hX; linarith
  · rw [hc, div_lt_iff₀ (by linarith)]; linarith
  · rw [hc1]; apply div_pos one_pos; linarith
  · rw [hsucc]; nlinarith

theorem geo_final : geoL 22 < 129/50 ∧ 3/25 < geoC 22 := by
  constructor
  · rw [geoL_closed]; norm_num [Ls, Bg]
  · rw [geoC_closed]
    have h1 := geoInv_22.2
    have h2 := geoInv_gt 22
    rw [lt_div_iff₀ (by linarith)]; linarith

/-- Literal subface: the domain of `q` is contained in that of `p`. -/
def Face.Sub (q p : Face) : Prop := q.B ≤ p.B ∧ p.L ≤ q.L ∧ q.c ≤ p.c

def bootstrapFace : Face := ⟨9999/10000, 129/50, 3/25⟩

/-- Finite native bootstrap, given one generic analytic step and subface monotonicity. -/
theorem bootstrap (P : Face → Prop)
    (step : ∀ p n a, NativeGates p n a → P p → P n)
    (mono : ∀ q p, Face.Sub q p → P p → P q) (h0 : P face0) : P bootstrapFace := by
  have h4 : P face4 :=
    step _ _ _ gates34 (step _ _ _ gates23 (step _ _ _ gates12 (step _ _ _ gates01 h0)))
  have hgeo : ∀ n, n ≤ 22 → P (geoFace n) := by
    intro n hn
    induction n with
    | zero => rw [geoFace_zero]; exact h4
    | succ n ih => exact step _ _ _ (geo_gates n (by omega)) (ih (by omega))
  apply mono _ _ _ (hgeo 22 le_rfl)
  obtain ⟨hL, hc⟩ := geo_final
  exact ⟨by simp [bootstrapFace, geoFace, Bg], hL.le, hc.le⟩

end
end QRH.DensitySplitThird
