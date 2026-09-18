import ErdosLean.Erdos265.Parts.RatTails

/-!
# Erdős #265 — Part U7: analytic upper bound for the second residual

Write `T = x + y` with `x = 1/a_n`, `y = T (n+1)`.  Using
`V n = g x + V (n+1)`, `V (n+1) ≥ T (n+1) = y` (each `1/(a-1) ≥ 1/a`) and `g = x/(1-x)`:
`Eres n ≤ g(x+y) - g x - y = y(x+y)/((1-x)(1-x-y)) + … ≤ 8 T y` once `T ≤ 1/2`.
Precisely `g(x+y) - g(x) - y = y (1 - (1-x)(1-x-y)) / ((1-x)(1-x-y))
 ≤ y · 2(x+y) / (1/4) = 8 T y`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

/-- Pure real inequality behind the residual bound. -/
lemma residual_alg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : x + y ≤ 1 / 2) :
    (x + y) / (1 - (x + y)) - x / (1 - x) - y ≤ 8 * (x + y) * y := by
  have h1 : 0 < 1 - (x + y) := by linarith
  have h2 : 0 < 1 - x := by linarith
  have key : (x + y) / (1 - (x + y)) - x / (1 - x) = y / ((1 - (x + y)) * (1 - x)) := by
    field_simp
    ring
  rw [key]
  have hd : 0 < (1 - (x + y)) * (1 - x) := mul_pos h1 h2
  have : y / ((1 - (x + y)) * (1 - x)) ≤ y + 8 * (x + y) * y := by
    rw [div_le_iff₀ hd]
    have hq : (1 - (x + y)) ^ 2 ≤ (1 - (x + y)) * (1 - x) := by
      nlinarith
    have hf : 1 ≤ (1 + 8 * (x + y)) * (1 - (x + y)) ^ 2 := by
      nlinarith [sq_nonneg (x + y - 1 / 4), mul_nonneg (add_nonneg hx hy)
        (sq_nonneg (x + y - 1 / 4)), mul_nonneg (add_nonneg hx hy) (add_nonneg hx hy)]
    have : y * 1 ≤ y * ((1 + 8 * (x + y)) * (1 - (x + y)) ^ 2) :=
      mul_le_mul_of_nonneg_left hf hy
    have h8 : 0 ≤ y * (1 + 8 * (x + y)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq h8]
  linarith

theorem residual_upper (ha : IsRationalPair a) :
    ∀ᶠ n in atTop, Eres a n ≤ 8 * T a n * T a (n + 1) := by
  have hT : Tendsto (T a) atTop (𝓝 0) := tail_tendsto_zero (recip a)
  have hev : ∀ᶠ n in atTop, T a n < 1 / 2 := hT.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hev] with n hn
  have hr := summable_recip ha
  have hs := summable_recipS ha
  have hA : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  -- decompositions
  have hTn : T a n = recip a n + T a (n + 1) := tail_eq_add_tail_succ hr n
  have hVn : V a n = recipS a n + V a (n + 1) := tail_eq_add_tail_succ hs n
  -- V (n+1) ≥ T (n+1)
  have hVT : T a (n + 1) ≤ V a (n + 1) := by
    unfold T V tail
    refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff (n + 1)).mpr hr)
      ((summable_nat_add_iff (n + 1)).mpr hs)
    have hk : (2 : ℝ) ≤ (a (k + (n + 1)) : ℝ) := by exact_mod_cast two_le_of ha _
    unfold recip recipS
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  -- 1/(a-1) = x/(1-x)
  have hS : recipS a n = recip a n / (1 - recip a n) := by
    unfold recipS recip
    have : (a n : ℝ) ≠ 0 := by linarith
    have : (a n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  have hx : 0 ≤ recip a n := by unfold recip; positivity
  have hy : 0 ≤ T a (n + 1) := T_nonneg ha (n + 1)
  have hxy : recip a n + T a (n + 1) ≤ 1 / 2 := by rw [← hTn]; exact hn.le
  have := residual_alg hx hy hxy
  unfold Eres
  rw [hVn, hS, hTn]
  linarith
