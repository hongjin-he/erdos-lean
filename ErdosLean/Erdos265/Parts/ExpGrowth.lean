import ErdosLean.Erdos265.Parts.LogBound

/-!
# Erdős #265 — Part U8: a positive envelope limit forces `a_m ≥ e^m`

If `log Henv n / 2ⁿ → ℓ > 0` then `log Henv n ≥ (ℓ/2) 2ⁿ` eventually.
Since `Henv n ≤ P n · a_n ≤ a_n^{n+1}` (`Dt n ≥ 1/a_n²`, monotonicity), `(n+1) log a_n ≥
(ℓ/2) 2ⁿ`, so `log a_n ≥ n` eventually.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

theorem P_le_pow (ha : IsRationalPair a) (n : ℕ) : P a n ≤ a n ^ n := by
  unfold P
  have := Finset.prod_le_pow_card (Finset.range n) a (a n)
    (fun k hk => ha.1.monotone (Finset.mem_range.mp hk).le)
  simpa using this

theorem Henv_le_pow (ha : IsRationalPair a) (n : ℕ) :
    Henv a n ≤ (a n : ℝ) ^ (n + 1) := by
  have hD := Dt_pos ha n
  have hs : 0 < Real.sqrt (Dt a n) := Real.sqrt_pos.mpr hD
  have hX : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have hX0 : (0 : ℝ) < (a n : ℝ) := by linarith
  have hinv := inv_sq_le_Dt ha n
  -- 1 ≤ a · √D
  have haD : 1 ≤ (a n : ℝ) * Real.sqrt (Dt a n) := by
    have h1 : 1 ≤ (a n : ℝ) ^ 2 * Dt a n := by
      rw [div_le_iff₀ (by positivity)] at hinv; linarith
    have h2 : ((a n : ℝ) * Real.sqrt (Dt a n)) ^ 2 = (a n : ℝ) ^ 2 * Dt a n := by
      rw [mul_pow, Real.sq_sqrt hD.le]
    nlinarith [mul_pos hX0 hs]
  have hP : (P a n : ℝ) ≤ (a n : ℝ) ^ n := by exact_mod_cast P_le_pow ha n
  have hP0 : (0 : ℝ) ≤ (P a n : ℝ) := Nat.cast_nonneg _
  unfold Henv
  rw [div_le_iff₀ hs, pow_succ]
  have hpow : (0 : ℝ) ≤ (a n : ℝ) ^ n := by positivity
  calc (P a n : ℝ) ≤ (a n : ℝ) ^ n * 1 := by linarith
    _ ≤ (a n : ℝ) ^ n * ((a n : ℝ) * Real.sqrt (Dt a n)) :=
        mul_le_mul_of_nonneg_left haD hpow
    _ = (a n : ℝ) ^ n * (a n : ℝ) * Real.sqrt (Dt a n) := by ring

theorem exp_growth (ha : IsRationalPair a) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlim : Tendsto (logRatio (Henv a)) atTop (𝓝 ℓ)) :
    ∀ᶠ m : ℕ in atTop, Real.exp (m : ℝ) ≤ (a m : ℝ) := by
  have h1 : ∀ᶠ n : ℕ in atTop, ℓ / 2 ≤ logRatio (Henv a) n :=
    hlim.eventually (le_mem_nhds (by linarith))
  have hpoly := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
  have h2 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / (2 : ℝ) ^ n ≤ ℓ / 4 :=
    hpoly.eventually (ge_mem_nhds (by linarith))
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n hn1 hn2 hn3
  have hX : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have hX0 : (0 : ℝ) < (a n : ℝ) := by linarith
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hn1' : ℓ / 2 * (2 : ℝ) ^ n ≤ Real.log (Henv a n) := by
    unfold logRatio at hn1; rwa [le_div_iff₀ h2n] at hn1
  have hn2' : (n : ℝ) ^ 2 ≤ ℓ / 4 * (2 : ℝ) ^ n := by
    rwa [div_le_iff₀ h2n] at hn2
  have hH1 : (0 : ℝ) < Henv a n := by
    have hP1 : (0 : ℝ) < (P a n : ℝ) := by
      have : 0 < P a n := by
        unfold P
        exact Finset.prod_pos (fun k _ => by have := two_le_of ha k; omega)
      exact_mod_cast this
    have hs : 0 < Real.sqrt (Dt a n) := Real.sqrt_pos.mpr (Dt_pos ha n)
    unfold Henv; exact div_pos hP1 hs
  have hlogH : Real.log (Henv a n) ≤ ((n : ℝ) + 1) * Real.log (a n : ℝ) := by
    have := Real.log_le_log hH1 (Henv_le_pow ha n)
    rw [Real.log_pow] at this; push_cast at this; exact this
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hL : 0 ≤ Real.log (a n : ℝ) := Real.log_nonneg (by linarith)
  -- (n+1) log a ≥ (ℓ/2) 2^n ≥ 2 n^2 ≥ n (n+1)
  have key : ((n : ℝ) + 1) * (n : ℝ) ≤ ((n : ℝ) + 1) * Real.log (a n : ℝ) := by
    nlinarith
  have hlog : (n : ℝ) ≤ Real.log (a n : ℝ) :=
    le_of_mul_le_mul_left key (by linarith)
  calc Real.exp (n : ℝ) ≤ Real.exp (Real.log (a n : ℝ)) := Real.exp_le_exp.mpr hlog
    _ = (a n : ℝ) := Real.exp_log hX0

end Erdos265
