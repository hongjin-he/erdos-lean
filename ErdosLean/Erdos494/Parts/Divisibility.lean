import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part B1: `f_s(n,j) = 0 ⇒ n ∣ (s-1)! · s^{j-1}` ([GFS62] §4).

For `1 ≤ m ≤ s-1`, `(s-1)! · C(n,m)` is divisible by `n` (`m! C(n,m) = n (n-1)⋯(n-m+1)` and
`m! ∣ (s-1)!`); the only other term of `f_s(n,j)` is `(-1)^{s-1} s^{j-1}` (`i = s`). -/

namespace Erdos494

/-- `n ∣ t! · C(n, m)` for `1 ≤ m ≤ t`. -/
lemma dvd_factorial_mul_choose (n t m : ℕ) (hm1 : 1 ≤ m) (hmt : m ≤ t) :
    n ∣ t.factorial * n.choose m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hdv : m' + 1 ∣ t.factorial := Nat.dvd_factorial (by omega) hmt
  obtain ⟨k, hk⟩ := hdv
  rcases n with _ | n'
  · simp
  · have h : (n' + 1) * n'.choose m' = (n' + 1).choose (m' + 1) * (m' + 1) :=
      Nat.add_one_mul_choose_eq n' m'
    -- (n'+1) * C(n', m') = C(n'+1, m'+1) * (m'+1)
    refine ⟨n'.choose m' * k, ?_⟩
    rw [hk]
    calc (m' + 1) * k * (n' + 1).choose (m' + 1)
        = (n' + 1).choose (m' + 1) * (m' + 1) * k := by ring
      _ = (n' + 1) * n'.choose m' * k := by rw [← h]
      _ = (n' + 1) * (n'.choose m' * k) := by ring

theorem gfs_dvd (s n j : ℕ) (hs : 1 ≤ s) (_hn : 0 < n) (h : gfsPoly s n j = 0) :
    n ∣ (s - 1).factorial * s ^ (j - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  unfold gfsPoly at h
  rw [Finset.sum_Icc_succ_top (by omega)] at h
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.add_sub_cancel] at h
  have hrest : (n : ℤ) ∣ (t.factorial : ℤ) *
      ∑ i ∈ Finset.Icc 1 t, (-1) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 1 - i) : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.dvd_sum fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    have := dvd_factorial_mul_choose n t (t + 1 - i) (by omega) (by omega)
    have hz : (n : ℤ) ∣ (t.factorial : ℤ) * (n.choose (t + 1 - i) : ℤ) := by exact_mod_cast this
    exact Dvd.dvd.trans hz ⟨(-1) ^ (i - 1) * (i : ℤ) ^ (j - 1), by ring⟩
  have hlast : (t.factorial : ℤ) * ((-1) ^ t * ((t + 1 : ℕ) : ℤ) ^ (j - 1)) =
      -((t.factorial : ℤ) *
        ∑ i ∈ Finset.Icc 1 t, (-1) ^ (i - 1) * (i : ℤ) ^ (j - 1) *
          (n.choose (t + 1 - i) : ℤ)) := by
    have h' := congrArg (fun x => (t.factorial : ℤ) * x) h
    simp only [mul_zero, mul_add] at h'
    linarith
  have h1 : (n : ℤ) ∣ (t.factorial : ℤ) * ((-1) ^ t * ((t + 1 : ℕ) : ℤ) ^ (j - 1)) := by
    rw [hlast]; exact hrest.neg_right
  have h2 : (n : ℤ) ∣ ((t.factorial * (t + 1) ^ (j - 1) : ℕ) : ℤ) := by
    have h3 := Dvd.dvd.mul_left h1 ((-1) ^ t)
    have e : (-1 : ℤ) ^ t * ((t.factorial : ℤ) * ((-1) ^ t * ((t + 1 : ℕ) : ℤ) ^ (j - 1))) =
        ((t.factorial * (t + 1) ^ (j - 1) : ℕ) : ℤ) := by
      push_cast
      have : ((-1 : ℤ) ^ t) * (-1) ^ t = 1 := by rw [← mul_pow]; norm_num
      linear_combination ((t.factorial : ℤ) * ((t : ℤ) + 1) ^ (j - 1)) * this
    rwa [e] at h3
  exact_mod_cast h2

end Erdos494
