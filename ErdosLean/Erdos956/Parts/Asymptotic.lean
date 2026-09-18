import ErdosLean.Erdos956.Defs

/-!
# Erdős #956 — Part 16: from the grids to `h(n) ≫ n^{4/3}` (note, Theorem 1)

`12 M_k = 5k⁴ + 2k³ + k² + 4k ≥ 5k⁴`; for `n ≥ n_2` take the largest `k ≥ 2` with `n_k ≤ n`,
then `n < n_{k+1} ≤ 12 k³`, so `n^{4/3} ≤ 12^{4/3} k⁴ ≤ (12^{7/3}/5) M_k`.

-/

namespace Erdos956

open Filter

lemma altAsymptotic_sum_cubic (A B C D : ℤ) (n : ℕ) :
    12 * ∑ i ∈ Finset.Icc 1 n, (A + B * (i : ℤ) + C * (i : ℤ) ^ 2 + D * (i : ℤ) ^ 3) =
      12 * A * n + 6 * B * n * (n + 1) + 2 * C * n * (n + 1) * (2 * n + 1)
        + 3 * D * (n : ℤ) ^ 2 * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast
    ring

lemma altAsymptotic_Mk_closed (k : ℕ) : (12 * Mk k : ℤ) = 5 * (k : ℤ) ^ 4 + 2 * k ^ 3 + k ^ 2 + 4 * k := by
  have h : (Mk k : ℤ) = ∑ i ∈ Finset.Icc 1 k,
      (((k : ℤ) + 1) * ((k : ℤ) ^ 2 + 1) + (-((k : ℤ) ^ 2 + 1)) * (i : ℤ)
        + (-((k : ℤ) + 1)) * (i : ℤ) ^ 2 + 1 * (i : ℤ) ^ 3) := by
    unfold Mk
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    have h1 : i ≤ k + 1 := by omega
    have h2 : i ^ 2 ≤ k ^ 2 + 1 := by
      have := Nat.pow_le_pow_left hi.2 2; omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    ring
  rw [h, altAsymptotic_sum_cubic]
  ring

lemma Mk_lower (k : ℕ) : 5 * k ^ 4 ≤ 12 * Mk k := by
  have h := altAsymptotic_Mk_closed k
  have : ((5 * k ^ 4 : ℕ) : ℤ) ≤ ((12 * Mk k : ℕ) : ℤ) := by
    push_cast
    rw [h]
    have : (0 : ℤ) ≤ k := by positivity
    nlinarith [pow_nonneg this 3, pow_nonneg this 2]
  exact_mod_cast this

theorem lower_of_grid (g : ℕ → ℕ) (hg : ∀ k ≥ 2, ∀ n ≥ nk k, Mk k ≤ g n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, c₀ * (n : ℝ) ^ ((4 : ℝ) / 3) ≤ g n := by
  refine ⟨5 / 432, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (nk 2)] with n hn
  set k := Nat.findGreatest (fun k => nk k ≤ n) n with hkdef
  have hn2 : nk 2 = 30 := by decide
  have h2k : 2 ≤ k := Nat.le_findGreatest (by omega) hn
  have hkn : nk k ≤ n := Nat.findGreatest_spec (P := fun k => nk k ≤ n) (m := 2) (by omega) hn
  have hk_le : k ≤ n := Nat.findGreatest_le n
  have hk_lt : k < n := by
    rcases lt_or_eq_of_le hk_le with h | h
    · exact h
    · exfalso
      have : nk k ≤ k := h ▸ hkn
      unfold nk at this
      nlinarith
  have hnext : ¬ nk (k + 1) ≤ n :=
    Nat.findGreatest_is_greatest (P := fun k => nk k ≤ n) (Nat.lt_succ_self k) (by omega)
  have hn12 : n ≤ 12 * k ^ 3 := by
    have : nk (k + 1) ≤ 12 * k ^ 3 := by
      unfold nk
      have h1 : k + 1 + 1 ≤ 2 * k := by omega
      have h2 : (k + 1) ^ 2 + 1 ≤ 3 * k ^ 2 := by nlinarith
      calc 2 * (k + 1 + 1) * ((k + 1) ^ 2 + 1) ≤ 2 * (2 * k) * (3 * k ^ 2) := by
            gcongr
        _ = 12 * k ^ 3 := by ring
    omega
  have hM := Mk_lower k
  have hMg := hg k h2k n hkn
  -- real-number part
  have hnR : (n : ℝ) ≤ 12 * (k : ℝ) ^ 3 := by exact_mod_cast hn12
  have hMR : 5 * (k : ℝ) ^ 4 ≤ 12 * (Mk k : ℝ) := by exact_mod_cast hM
  have hMgR : (Mk k : ℝ) ≤ g n := by exact_mod_cast hMg
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hcube : ((n : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 = (n : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hpow : (n : ℝ) ^ ((4 : ℝ) / 3) ≤ 36 * (k : ℝ) ^ 4 := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity)
    rw [hcube]
    calc (n : ℝ) ^ 4 ≤ (12 * (k : ℝ) ^ 3) ^ 4 := by gcongr
      _ = 20736 * (k : ℝ) ^ 12 := by ring
      _ ≤ 46656 * (k : ℝ) ^ 12 := by nlinarith [pow_nonneg hk0 12]
      _ = (36 * (k : ℝ) ^ 4) ^ 3 := by ring
  nlinarith

end Erdos956
