import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P16: final arithmetic

Choose `p = n^{-1/3}/4`: `e ≤ 32 n^{4/3} + n^{4/3}/4`, so `U + S ≤ 36 n^{4/3}` (and everything is `0` for `n = 0`).
-/

namespace Erdos956Upper

open Erdos956 Metric

theorem final_arith (n : ℕ) (U S e O : ℝ) (hU : U ≤ e + n) (hS : S ≤ 2 * n)
    (hO : O ≤ 4 * (n : ℝ) ^ 2)
    (he : ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → e ≤ 8 * n / p + p ^ 2 * O) :
    U + S ≤ 36 * (n : ℝ) ^ ((4 : ℝ) / 3) := by
  set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht3 : t ^ 3 = n := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h43 : (n : ℝ) ^ ((4 : ℝ) / 3) = t ^ 4 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [h43]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hO0 : O ≤ 0 := by simpa using hO
    have he0 := he (1 / 4) (by norm_num) le_rfl
    have he00 : e ≤ 0 := by
      have : (1 / 4 : ℝ) ^ 2 * O ≤ 0 := by nlinarith
      simp at he0; linarith
    have : t = 0 := by
      have : t ^ 3 = 0 := by rw [ht3]; simp
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [this]
    simp at hS hU ⊢
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have ht1 : 1 ≤ t := by
      by_contra h
      push Not at h
      have : t ^ 3 < 1 := by
        have := pow_lt_one₀ ht0 h (by norm_num : (3:ℕ) ≠ 0)
        exact this
      linarith
    have htpos : 0 < t := by linarith
    have hp : 0 < 1 / (4 * t) := by positivity
    have hp4 : 1 / (4 * t) ≤ 1 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have he' := he _ hp hp4
    have h1 : 8 * (n : ℝ) / (1 / (4 * t)) = 32 * t ^ 4 := by
      rw [← ht3]; field_simp; norm_num
    have h2 : (1 / (4 * t)) ^ 2 * O ≤ t ^ 4 / 4 := by
      have hsq : 0 ≤ (1 / (4 * t)) ^ 2 := by positivity
      calc (1 / (4 * t)) ^ 2 * O ≤ (1 / (4 * t)) ^ 2 * (4 * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hO hsq
        _ = t ^ 4 / 4 := by rw [← ht3]; field_simp
    have hn3 : (n : ℝ) ≤ t ^ 4 := by
      rw [← ht3]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ht1 3]
    nlinarith

end Erdos956Upper
