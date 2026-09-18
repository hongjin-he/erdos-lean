import ErdosLean.Erdos612All.Defs

/-!
# Erdős 612 (all `r`), part (ii): degree condition inside the CC period

`r = q+4`, `τ = 2q+7`, `x = 3u`, `δ = τx = (6q+21)u`.  Layer sums in the period:
`m = 3j < 6q+16` ↦ `1`; `m = 3j+1 < 6q+16` ↦ `(2q+6-j)x`; `m = 3j+2 < 6q+16` ↦ `(j+2)x`;
`E` ↦ `3u = x`; `F` ↦ `(2q+1)·3u + 4·4u = (6q+19)u`.
* `m = 3j`, `1 ≤ j ≤ 2q+4`: `(j+1)x + 1 + (2q+6-j)x = δ + 1` (tight at `j = 1`);
* `m = 6q+15` (`j = 2q+5`): `(2q+6)x + 1 + x = δ + 1`;
* `m = 0`: left context has sum `≥ x` (`[δ]` or the previous `E`): `≥ x + 1 + (2q+6)x`;
* `m = 3j+1`, `m = 3j+2`: `1 + (2q+8)x ≥ δ + x`;
* first `E` (`m = 6q+16`): `1 + 3u + (6q+19)u = δ + u + 1`;
* `F`: `3u + (6q+19)u + 3u = δ + 4u` (max weight `4u`);
* last `E`: `(6q+19)u + 3u + 1` (right context is always `[1]`).
-/

namespace Erdos612All

open Erdos612

theorem odBlock_three (q j : ℕ) (h : 3 * j < 6 * q + 16) : odBlock q (3 * j) = [1] := by
  unfold odBlock; simp [h]

theorem odBlock_three_one (q j : ℕ) (h : 3 * j + 1 < 6 * q + 16) :
    odBlock q (3 * j + 1) = List.replicate (2 * q + 6 - j) (odX q) := by
  unfold odBlock
  rw [show (3 * j + 1) % 3 = 1 by omega, show (3 * j + 1) / 3 = j by omega]
  simp [h]

theorem odBlock_three_two (q j : ℕ) (h : 3 * j + 2 < 6 * q + 16) :
    odBlock q (3 * j + 2) = List.replicate (j + 2) (odX q) := by
  unfold odBlock
  rw [show (3 * j + 2) % 3 = 2 by omega, show (3 * j + 2) / 3 = j by omega]
  simp [h]

theorem odBlock_E1 (q : ℕ) : odBlock q (6 * q + 16) = odE q := by
  unfold odBlock; simp

theorem odBlock_F (q : ℕ) : odBlock q (6 * q + 17) = odF q := by
  unfold odBlock; simp

theorem odBlock_E3 (q : ℕ) : odBlock q (6 * q + 18) = odE q := by
  unfold odBlock; simp

theorem odE_sum (q : ℕ) : (odE q).sum = 3 * odU q := by
  simp [odE]; ring

theorem odF_sum (q : ℕ) : (odF q).sum = 6 * (q * odU q) + 19 * odU q := by
  simp only [odF, List.sum_append, List.sum_replicate, smul_eq_mul]; ring

theorem odF_mem (q w : ℕ) (h : w ∈ odF q) : w = 3 * odU q ∨ w = 4 * odU q := by
  simp only [odF, List.mem_append, List.mem_replicate] at h
  omega

theorem odDelta_eq (q : ℕ) : odDelta q = 6 * (q * odU q) + 21 * odU q := by
  unfold odDelta odX; ring

theorem odBlock_deg (q m : ℕ) (hm : m < 6 * q + 19) (a c : List ℕ)
    (ha : m ≠ 0 → a = odBlock q (m - 1)) (ha0 : m = 0 → odX q ≤ a.sum)
    (hc : m + 1 ≠ 6 * q + 19 → c = odBlock q (m + 1)) (hc0 : m + 1 = 6 * q + 19 → c = [1]) :
    DegQ (odDelta q) a (odBlock q m) c := by
  intro v hv
  have hX : odX q = 3 * odU q := rfl
  have hδX : odDelta q = (2 * q + 7) * odX q := rfl
  by_cases hlt : m < 6 * q + 16
  · obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 3 ∧ m = 3 * j + t :=
      ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
    interval_cases t
    · simp only [Nat.add_zero] at ha ha0 hc hc0 hm hv hlt ⊢
      rw [odBlock_three q j hlt] at hv ⊢
      simp only [List.mem_singleton] at hv
      subst hv
      simp only [List.sum_singleton]
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        have h1 := ha0 rfl
        rw [hc (by omega), show 3 * 0 + 1 = 3 * 0 + 1 from rfl, odBlock_three_one q 0 (by omega),
          List.sum_replicate, smul_eq_mul, hδX]
        have : (2 * q + 6 - 0) * odX q + odX q = (2 * q + 7) * odX q := by
          rw [Nat.sub_zero, ← Nat.succ_mul]
        omega
      · rw [ha (by omega), show 3 * j - 1 = 3 * (j - 1) + 2 by omega,
          odBlock_three_two q (j - 1) (by omega), List.sum_replicate, smul_eq_mul,
          show j - 1 + 2 = j + 1 by omega]
        by_cases hj : 3 * j + 1 < 6 * q + 16
        · rw [hc (by omega), odBlock_three_one q j hj, List.sum_replicate, smul_eq_mul, hδX]
          have : (j + 1) * odX q + (2 * q + 6 - j) * odX q = (2 * q + 7) * odX q := by
            rw [← Nat.add_mul, show j + 1 + (2 * q + 6 - j) = 2 * q + 7 by omega]
          omega
        · have hj' : j = 2 * q + 5 := by omega
          subst hj'
          rw [hc (by omega), show 3 * (2 * q + 5) + 1 = 6 * q + 16 by ring, odBlock_E1, odE_sum, hδX]
          have : (2 * q + 5 + 1) * odX q + odX q = (2 * q + 7) * odX q := by
            rw [← Nat.succ_mul]
          omega
    · rw [odBlock_three_one q j hlt] at hv ⊢
      rw [List.mem_replicate] at hv
      rw [hv.2, ha (by omega), show 3 * j + 1 - 1 = 3 * j by omega, odBlock_three q j (by omega),
        hc (by omega), show 3 * j + 1 + 1 = 3 * j + 2 by omega, odBlock_three_two q j (by omega)]
      simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul, hδX]
      have : (2 * q + 6 - j) * odX q + (j + 2) * odX q = (2 * q + 7) * odX q + odX q := by
        rw [← Nat.add_mul, show 2 * q + 6 - j + (j + 2) = 2 * q + 7 + 1 by omega, Nat.add_mul,
          one_mul]
      omega
    · rw [odBlock_three_two q j hlt] at hv ⊢
      rw [List.mem_replicate] at hv
      rw [hv.2, ha (by omega), show 3 * j + 2 - 1 = 3 * j + 1 by omega,
        odBlock_three_one q j (by omega), hc (by omega), show 3 * j + 2 + 1 = 3 * (j + 1) by omega,
        odBlock_three q (j + 1) (by omega)]
      simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul, hδX]
      have : (2 * q + 6 - j) * odX q + (j + 2) * odX q = (2 * q + 7) * odX q + odX q := by
        rw [← Nat.add_mul, show 2 * q + 6 - j + (j + 2) = 2 * q + 7 + 1 by omega, Nat.add_mul,
          one_mul]
      omega
  · have hF := odF_sum q
    have hδ := odDelta_eq q
    have hE := odE_sum q
    rcases (show m = 6 * q + 16 ∨ m = 6 * q + 17 ∨ m = 6 * q + 18 by omega) with h | h | h <;>
      subst h
    · rw [odBlock_E1] at hv ⊢
      rw [ha (by omega), show 6 * q + 16 - 1 = 3 * (2 * q + 5) by omega,
        odBlock_three q _ (by omega), hc (by omega), show 6 * q + 16 + 1 = 6 * q + 17 by omega,
        odBlock_F]
      have hv' : v = odU q := (List.mem_replicate.mp hv).2
      simp only [List.sum_singleton]
      omega
    · rw [odBlock_F] at hv ⊢
      rw [ha (by omega), show 6 * q + 17 - 1 = 6 * q + 16 by omega, odBlock_E1, hc (by omega),
        show 6 * q + 17 + 1 = 6 * q + 18 by omega, odBlock_E3]
      have := odF_mem q v hv
      omega
    · rw [odBlock_E3] at hv ⊢
      rw [ha (by omega), show 6 * q + 18 - 1 = 6 * q + 17 by omega, odBlock_F, hc0 (by omega)]
      have hv' : v = odU q := (List.mem_replicate.mp hv).2
      simp only [List.sum_singleton]
      omega

end Erdos612All
