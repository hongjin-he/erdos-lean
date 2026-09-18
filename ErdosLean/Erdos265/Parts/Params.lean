import ErdosLean.Erdos265.Defs

/-!
# Erdős #265 — Part L3: the parameter sequence `m_k`, `N_k = 4^{m_k}`, `M_k = 2^{m_k}`

`m_0 = 40`, `m_{k+1} = m_k + ⌊m_k/10⌋ + 1`.
* `M_k² = N_k`, `m_k ≥ 40`, `N_k ≥ 64`, `2 M_k < N_k`;
* the nesting condition (cf. KT v4 (7.17), with `D = 16`, `ε = 1/16`):
  `16/N_k² ≤ M_{k+1}/(16 N_{k+1}²)` ⇔ `8 + 3 m_{k+1} ≤ 4 m_k`, and
  `16/N_k³ ≤ M_{k+1}/(16 N_{k+1}³)` ⇔ `8 + 5 m_{k+1} ≤ 6 m_k` (true as `m_k ≥ 40`);
* consecutive blocks are separated: `2N_k + M_k + M_{k+1} < N_{k+1}`;
* radii are positive and tend to `0`;
* growth: `m_k ≥ 40 · (21/20)^k`.
-/

open Filter Topology

namespace Erdos265

theorem NN_eq_two_pow (k : ℕ) : NN k = 2 ^ (2 * mSeq k) := by
  unfold NN; rw [pow_mul]; norm_num

theorem MM_sq (k : ℕ) : MM k ^ 2 = NN k := by
  rw [NN_eq_two_pow]; unfold MM; rw [← pow_mul, mul_comm]

theorem mSeq_ge_add (k : ℕ) : k + 40 ≤ mSeq k := by
  induction k with
  | zero => simp [mSeq]
  | succ k ih => simp only [mSeq]; omega

theorem mSeq_ge (k : ℕ) : 40 ≤ mSeq k := by
  have := mSeq_ge_add k; omega

theorem NN_ge (k : ℕ) : 64 ≤ NN k := by
  unfold NN
  calc (64 : ℕ) = 4 ^ 3 := by norm_num
    _ ≤ 4 ^ mSeq k := Nat.pow_le_pow_right (by norm_num) (by have := mSeq_ge k; omega)

theorem MM_ge (k : ℕ) : 4 ≤ MM k := by
  unfold MM
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ mSeq k := Nat.pow_le_pow_right (by norm_num) (by have := mSeq_ge k; omega)

theorem two_MM_lt (k : ℕ) : 2 * MM k < NN k := by
  rw [← MM_sq, sq]
  have := MM_ge k
  nlinarith

theorem block_gap (k : ℕ) : 2 * NN k + MM k + MM (k + 1) < NN (k + 1) := by
  have hm := mSeq_ge k
  have hs : mSeq (k + 1) = mSeq k + mSeq k / 10 + 1 := rfl
  rw [NN_eq_two_pow, NN_eq_two_pow]
  unfold MM
  have h1 : 2 ^ mSeq k ≤ 2 ^ (2 * mSeq k) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ mSeq (k + 1) ≤ 2 ^ (2 * mSeq (k + 1) - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2 * mSeq k) * 2 ^ 3 ≤ 2 ^ (2 * mSeq (k + 1) - 1) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (2 * mSeq (k + 1)) = 2 ^ (2 * mSeq (k + 1) - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have h5 : 0 < 2 ^ (2 * mSeq k) := by positivity
  omega

theorem rad1_pos (k : ℕ) : 0 < rad1 k := by
  unfold rad1
  have : (0 : ℝ) < MM k := by exact_mod_cast (show 0 < MM k by have := MM_ge k; omega)
  have : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  positivity

theorem rad2_pos (k : ℕ) : 0 < rad2 k := by
  unfold rad2
  have : (0 : ℝ) < MM k := by exact_mod_cast (show 0 < MM k by have := MM_ge k; omega)
  have : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  positivity

theorem step_rad1_nat (k : ℕ) : 256 * NN (k + 1) ^ 2 ≤ MM (k + 1) * NN k ^ 2 := by
  have hm := mSeq_ge k
  have hs : mSeq (k + 1) = mSeq k + mSeq k / 10 + 1 := rfl
  rw [NN_eq_two_pow, NN_eq_two_pow]; unfold MM
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem step_rad2_nat (k : ℕ) : 256 * NN (k + 1) ^ 3 ≤ MM (k + 1) * NN k ^ 3 := by
  have hm := mSeq_ge k
  have hs : mSeq (k + 1) = mSeq k + mSeq k / 10 + 1 := rfl
  rw [NN_eq_two_pow, NN_eq_two_pow]; unfold MM
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem step_rad1 (k : ℕ) : 16 / (NN k : ℝ) ^ 2 ≤ rad1 (k + 1) := by
  unfold rad1
  have h : ((256 * NN (k + 1) ^ 2 : ℕ) : ℝ) ≤ ((MM (k + 1) * NN k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast step_rad1_nat k
  push_cast at h
  have a : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  have b : (0 : ℝ) < NN (k + 1) := by
    exact_mod_cast (show 0 < NN (k + 1) by have := NN_ge (k + 1); omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem step_rad2 (k : ℕ) : 16 / (NN k : ℝ) ^ 3 ≤ rad2 (k + 1) := by
  unfold rad2
  have h : ((256 * NN (k + 1) ^ 3 : ℕ) : ℝ) ≤ ((MM (k + 1) * NN k ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast step_rad2_nat k
  push_cast at h
  have a : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  have b : (0 : ℝ) < NN (k + 1) := by
    exact_mod_cast (show 0 < NN (k + 1) by have := NN_ge (k + 1); omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem NN_ge_succ (k : ℕ) : k + 1 ≤ NN k := by
  have h := mSeq_ge_add k
  have : mSeq k < 2 ^ mSeq k := Nat.lt_two_pow_self
  have : 2 ^ mSeq k ≤ NN k := by
    rw [NN_eq_two_pow]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem MM_le_NN (k : ℕ) : MM k ≤ NN k := by
  rw [← MM_sq, sq]; exact Nat.le_mul_of_pos_left _ (by have := MM_ge k; omega)

theorem rad1_le (k : ℕ) : rad1 k ≤ 1 / ((k : ℝ) + 1) := by
  unfold rad1
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ (NN k : ℝ) := by exact_mod_cast NN_ge_succ k
  have h2 : (MM k : ℝ) ≤ (NN k : ℝ) := by exact_mod_cast MM_le_NN k
  have a : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  have hM : (0 : ℝ) ≤ MM k := by positivity
  push_cast at h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul h2 h1 (by positivity) a.le]

theorem rad2_le (k : ℕ) : rad2 k ≤ 1 / ((k : ℝ) + 1) := by
  have a : (1 : ℝ) ≤ NN k := by exact_mod_cast (show 1 ≤ NN k by have := NN_ge k; omega)
  have : rad2 k ≤ rad1 k := by
    unfold rad1 rad2
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [pow_succ]; nlinarith [pow_pos (show (0:ℝ) < NN k by linarith) 2]
  exact this.trans (rad1_le k)

theorem tendsto_one_div_succ' : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem rad1_tendsto : Tendsto rad1 atTop (𝓝 0) :=
  squeeze_zero (fun k => (rad1_pos k).le) rad1_le tendsto_one_div_succ'

theorem rad2_tendsto : Tendsto rad2 atTop (𝓝 0) :=
  squeeze_zero (fun k => (rad2_pos k).le) rad2_le tendsto_one_div_succ'

theorem mSeq_growth (k : ℕ) : (40 : ℝ) * (21 / 20 : ℝ) ^ k ≤ (mSeq k : ℝ) := by
  induction k with
  | zero => simp [mSeq]
  | succ k ih =>
    have hn : 20 * mSeq (k + 1) ≥ 21 * mSeq k := by
      simp only [mSeq]; omega
    have hr : (20 : ℝ) * (mSeq (k + 1) : ℝ) ≥ 21 * (mSeq k : ℝ) := by exact_mod_cast hn
    rw [pow_succ]
    nlinarith
end Erdos265
