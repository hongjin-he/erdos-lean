import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part A2: the Newton recursion satisfied by `gfsPoly`.

For `k ≥ 1`, `j ≥ 1`:
`k · f_k(n,j) = Σ_{i=1}^{k} (-1)^{i+1} (n · f_{k-i}(n,j) + C(n,k-i) · i^j)`, with `f_0 = 0`.
This is exactly the recursion produced by `k e_k = Σ (-1)^{i+1} e_{k-i} p_i` after
linearising at order `t^j` (see `KSumPowerSum`).  Pure finite-sum algebra
(`Finset.sum_comm`, Pascal/absorption identities for `Nat.choose`).  Checked numerically for
`n ≤ 8, j ≤ 6, k ≤ 7`. -/

namespace Erdos494

namespace GfsRecursionAux

lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 m, F i = ∑ i ∈ Finset.range m, F (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `g n m = Σ_{i=1}^m (-1)^{i+1} C(n, m-i)`. -/
def g (n m : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 m, (-1) ^ (i + 1) * (n.choose (m - i) : ℤ)

lemma g_succ (n m : ℕ) : g n (m + 1) = (n.choose m : ℤ) - g n m := by
  unfold g
  rw [sum_Icc_one_eq_range, sum_Icc_one_eq_range, Finset.sum_range_succ']
  have h : ∑ i ∈ Finset.range m, (-1 : ℤ) ^ (i + 1 + 1 + 1) * (n.choose (m + 1 - (i + 1 + 1)) : ℤ)
      = -∑ i ∈ Finset.range m, (-1 : ℤ) ^ (i + 1 + 1) * (n.choose (m - (i + 1)) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : m + 1 - (i + 1 + 1) = m - (i + 1) := by omega
    rw [this, pow_succ]; ring
  rw [h]; simp; ring

lemma key (n m : ℕ) : (m : ℤ) * (n.choose m : ℤ) = (n : ℤ) * g n m := by
  induction m with
  | zero => simp [g]
  | succ m ih =>
    rw [g_succ, mul_sub, ← ih]
    have h := Nat.choose_succ_right_eq n m
    rcases le_or_gt m n with hmn | hmn
    · have h' : ((n.choose (m + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) = (n.choose m : ℤ) * ((n : ℤ) - m) := by
        have := congrArg (fun x : ℕ => (x : ℤ)) h
        push_cast [Nat.cast_sub hmn] at this
        exact this
      push_cast; linarith
    · rw [Nat.choose_eq_zero_of_lt hmn, Nat.choose_eq_zero_of_lt (by omega)]; simp

end GfsRecursionAux

open GfsRecursionAux in
theorem gfs_recursion (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (k : ℤ) * gfsPoly k n j =
      ∑ i ∈ Finset.Icc 1 k, (-1) ^ (i + 1) *
        ((n : ℤ) * gfsPoly (k - i) n j + (n.choose (k - i) : ℤ) * (i : ℤ) ^ j) := by
  -- Step 1: split the right-hand side.
  have split : ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i + 1) *
        ((n : ℤ) * gfsPoly (k - i) n j + (n.choose (k - i) : ℤ) * (i : ℤ) ^ j)
      = (n : ℤ) * ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i + 1) * gfsPoly (k - i) n j
        + ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (k - i) : ℤ)
            * (i : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have e1 : (-1 : ℤ) ^ (i + 1) = (-1) ^ (i - 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
      simp [pow_succ]
    have e2 : (i : ℤ) ^ j = (i : ℤ) ^ (j - 1) * i := by
      rw [← pow_succ]; congr 1; omega
    rw [e1, e2]; ring
  -- Step 2: the swapped double sum.
  have swap : ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i + 1) * gfsPoly (k - i) n j
      = ∑ l ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (l - 1) * (l : ℤ) ^ (j - 1) * g n (k - l) := by
    unfold gfsPoly g
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.Icc 1 k) (s' := fun l => Finset.Icc 1 (k - l))]
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      have : k - i - l = k - l - i := by omega
      rw [this]; ring
    · intro i l; simp only [Finset.mem_Icc]; omega
  rw [split, swap, Finset.mul_sum, gfsPoly, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hkey := key n (k - i)
  push_cast [Nat.cast_sub hik] at hkey
  linear_combination (-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * hkey
