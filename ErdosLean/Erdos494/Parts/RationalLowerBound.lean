import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part D9: Liouville-type lower bound at a rational point.

`q1^{r1} q2^{r2} · D^{(i1,i2)} P(p1/q1, p2/q2)` is an integer (each monomial contributes
`c · C · C · p1^{k1-i1} q1^{r1-k1+i1} p2^{k2-i2} q2^{r2-k2+i2}`), so if nonzero it has absolute
value `≥ 1`. -/

namespace Erdos494

lemma rlb_pow_clear (p : ℤ) (q : ℕ) (hq : 0 < q) (m r : ℕ) (h : m ≤ r) :
    (q : ℝ) ^ r * ((p : ℝ) / q) ^ m = (p : ℝ) ^ m * (q : ℝ) ^ (r - m) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, div_pow, pow_add]
  field_simp

theorem rational_lower_bound (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (p1 p2 : ℤ) (q1 q2 : ℕ)
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hne : hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) ≠ 0) :
    1 ≤ (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      |hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2)| := by
  set N : ℤ := ∑ k1 ∈ Finset.range (r1 + 1), ∑ k2 ∈ Finset.range (r2 + 1),
    c k1 k2 * (k1.choose i1 : ℤ) * (k2.choose i2 : ℤ) * p1 ^ (k1 - i1) *
      (q1 : ℤ) ^ (r1 - (k1 - i1)) * p2 ^ (k2 - i2) * (q2 : ℤ) ^ (r2 - (k2 - i2)) with hN
  have key : (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) = (N : ℝ) := by
    rw [hN, hasseEval]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k1 hk1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k2 hk2 => ?_
    have h1 : k1 - i1 ≤ r1 := le_trans (Nat.sub_le _ _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1))
    have h2 : k2 - i2 ≤ r2 := le_trans (Nat.sub_le _ _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk2))
    have e1 := rlb_pow_clear p1 q1 hq1 _ _ h1
    have e2 := rlb_pow_clear p2 q2 hq2 _ _ h2
    calc (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
          ((c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) *
            ((p1 : ℝ) / q1) ^ (k1 - i1) * ((p2 : ℝ) / q2) ^ (k2 - i2))
        = (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) *
            ((q1 : ℝ) ^ r1 * ((p1 : ℝ) / q1) ^ (k1 - i1)) *
            ((q2 : ℝ) ^ r2 * ((p2 : ℝ) / q2) ^ (k2 - i2)) := by ring
      _ = _ := by rw [e1, e2]; ring
  have hNne : N ≠ 0 := by
    intro h0
    have hq1' : (q1 : ℝ) ^ r1 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq1.ne')
    have hq2' : (q2 : ℝ) ^ r2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq2.ne')
    have : (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
        hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) = 0 := by
      rw [key, h0]; simp
    exact hne (by simpa [hq1', hq2'] using this)
  have hpos : (0 : ℝ) ≤ (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 := by positivity
  have habs : (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      |hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2)| = |(N : ℝ)| := by
    rw [← key, abs_mul, abs_of_nonneg hpos]
  rw [habs]
  have : (1 : ℤ) ≤ |N| := Int.one_le_abs hNne
  exact_mod_cast this

end Erdos494
