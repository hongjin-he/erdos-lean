import ErdosLean.Erdos790.Defs

/-! Part: `K(n) ≤ 64 (log n)²` for `n ≥ 2`, and monotonicity of `K`. -/

namespace Erdos790

theorem K_mono {M N : ℕ} (h : M ≤ N) : K M ≤ K N := by
  unfold K
  have := Nat.clog_mono_right 2 h
  exact Nat.mul_le_mul (by omega) (by omega)

theorem K_le_log_sq (n : ℕ) (hn : 2 ≤ n) : (K n : ℝ) ≤ 64 * Real.log n ^ 2 := by
  unfold K
  have hpow' : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  rw [Nat.pred_eq_sub_one] at hpow'
  set c := Nat.clog 2 n with hc
  set p := c - 1 with hp
  have hpow : 2 ^ p < n := hpow'
  have hcp : c ≤ p + 1 := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hpl : (p : ℝ) * Real.log 2 < Real.log n := by
    have h1 : ((2 : ℝ) ^ p) < n := by exact_mod_cast hpow
    have h2 := Real.log_lt_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hcR : (c : ℝ) ≤ p + 1 := by exact_mod_cast hcp
  have hp0 : (0 : ℝ) ≤ p := by positivity
  push_cast
  set L := Real.log n
  have hpL : (p : ℝ) * 0.69 ≤ L := by nlinarith
  nlinarith [mul_le_mul hcR hcR (by positivity) (by positivity)]

theorem K_pos (n : ℕ) : 0 < K n := by
  unfold K; positivity

end Erdos790
