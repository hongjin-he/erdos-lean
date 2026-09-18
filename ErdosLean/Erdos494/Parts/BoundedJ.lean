import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part B2: bounded `j`.

For `j < J` (fixed), `f_s(n,j)` is a polynomial in `n` of degree `s-1` whose leading term is
`C(n, s-1)` (from `i = 1`); every other term is at most `s^J · C(n, s-2)` in absolute value.
Hence `f_s(n,j) ≠ 0` for `n` large (`s ≥ 2`). -/

namespace Erdos494

/-- Binomial coefficients increase in the lower index below `n/2`. -/
private lemma choose_mono_low (n r : ℕ) :
    ∀ k : ℕ, r + k ≤ n / 2 → n.choose r ≤ n.choose (r + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : n.choose (r + k) ≤ n.choose (r + k + 1) :=
      Nat.choose_le_succ_of_lt_half_left (by omega)
    calc n.choose r ≤ n.choose (r + k) := h1
      _ ≤ n.choose (r + (k + 1)) := by rw [← add_assoc]; exact h2

theorem bounded_j (s : ℕ) (hs : 2 ≤ s) (J : ℕ) :
    ∃ N : ℕ, ∀ n j : ℕ, N ≤ n → j < J → gfsPoly s n j ≠ 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  set K : ℕ := (t + 2) ^ J with hK
  refine ⟨2 * (t + 2) + (t + 1) * (t + 1) * K + t + 1, ?_⟩
  intro n j hn hj
  -- split off the `i = 1` term
  unfold gfsPoly
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ t + 2)]
  have hfirst : ((-1 : ℤ) ^ (1 - 1) * ((1 : ℕ) : ℤ) ^ (j - 1) * (n.choose (t + 2 - 1) : ℤ))
      = (n.choose (t + 1) : ℤ) := by
    simp
  rw [hfirst]
  set R := ∑ i ∈ Finset.Ioc 1 (t + 2),
    (-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 2 - i) : ℤ) with hR
  -- bound on the remainder
  have hterm : ∀ i ∈ Finset.Ioc 1 (t + 2),
      |(-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 2 - i) : ℤ)|
        ≤ (K : ℤ) * (n.choose t : ℤ) := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hpow : i ^ (j - 1) ≤ K := by
      calc i ^ (j - 1) ≤ (t + 2) ^ (j - 1) := Nat.pow_le_pow_left hi.2 _
        _ ≤ (t + 2) ^ J := Nat.pow_le_pow_right (by omega) (by omega)
    have hch : n.choose (t + 2 - i) ≤ n.choose t := by
      have := choose_mono_low n (t + 2 - i) (i - 2) (by omega)
      have e : t + 2 - i + (i - 2) = t := by omega
      rwa [e] at this
    have : i ^ (j - 1) * n.choose (t + 2 - i) ≤ K * n.choose t := Nat.mul_le_mul hpow hch
    exact_mod_cast this
  have hRle : |R| ≤ ((t + 1 : ℕ) : ℤ) * ((K : ℤ) * (n.choose t : ℤ)) := by
    calc |R| ≤ ∑ i ∈ Finset.Ioc 1 (t + 2),
          |(-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 2 - i) : ℤ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Ioc 1 (t + 2), (K : ℤ) * (n.choose t : ℤ) := Finset.sum_le_sum hterm
      _ = ((t + 1 : ℕ) : ℤ) * ((K : ℤ) * (n.choose t : ℤ)) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; congr 2
  -- the leading term dominates
  have hlead : (t + 1) * (K * n.choose t) < n.choose (t + 1) := by
    have hrec := Nat.choose_succ_right_eq n t
    have hpos : 0 < n.choose t := Nat.choose_pos (by omega)
    have hnt : (t + 1) * (t + 1) * K < n - t := by omega
    have : (t + 1) * (K * n.choose t) * (t + 1) < n.choose (t + 1) * (t + 1) := by
      rw [hrec]
      calc (t + 1) * (K * n.choose t) * (t + 1)
          = n.choose t * ((t + 1) * (t + 1) * K) := by ring
        _ < n.choose t * (n - t) := Nat.mul_lt_mul_of_pos_left hnt hpos
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
  have hlead' : ((t + 1 : ℕ) : ℤ) * ((K : ℤ) * (n.choose t : ℤ)) < (n.choose (t + 1) : ℤ) := by
    exact_mod_cast hlead
  intro h0
  have : R = -(n.choose (t + 1) : ℤ) := by linarith
  rw [this, abs_neg, abs_of_nonneg (by positivity)] at hRle
  linarith

end Erdos494
