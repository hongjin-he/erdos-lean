import ErdosLean.Erdos612All.Defs

/-!
# Erdős 612 (all `r`), part (i): degree condition inside the CSS block

Every clump of layer `m` of the block has neighbourhood weight `≥ δ = 2s·w`, whatever the
outside neighbours of the two end layers are (the end layers are the weight-`1` layers `m = 0`
and `m = 6s`, whose inner neighbour already has total weight `2s·w = δ`).
Layer sums: `m = 3i` ↦ `1`, `m = 3i+1` ↦ `(2s-i)w`, `m = 3i+2` ↦ `(i+1)w`.
* `m = 3i` (`1 ≤ i ≤ 2s-1`): `i·w + 1 + (2s-i)w = δ + 1` (tight);
* `m = 3i+1`: `1 + (2s-i)w + (i+1)w = δ + w + 1`;
* `m = 3i+2`: `(2s-i)w + (i+1)w + 1 = δ + w + 1`;
* `m = 0`: `≥ 1 + 2s·w`; `m = 6s`: `≥ 2s·w + 1`.
-/

namespace Erdos612All

open Erdos612

theorem evBlock_three (s i : ℕ) : evBlock s (3 * i) = [1] := by
  unfold evBlock; simp

theorem evBlock_three_one (s i : ℕ) :
    evBlock s (3 * i + 1) = List.replicate (2 * s - i) (evW s) := by
  unfold evBlock
  rw [show (3 * i + 1) % 3 = 1 by omega, show (3 * i + 1) / 3 = i by omega]
  simp

theorem evBlock_three_two (s i : ℕ) :
    evBlock s (3 * i + 2) = List.replicate (i + 1) (evW s) := by
  unfold evBlock
  rw [show (3 * i + 2) % 3 = 2 by omega, show (3 * i + 2) / 3 = i by omega]
  simp

theorem evBlock_deg (s m : ℕ) (hs : 1 ≤ s) (hm : m ≤ 6 * s) (a c : List ℕ)
    (ha : m ≠ 0 → a = evBlock s (m - 1)) (hc : m ≠ 6 * s → c = evBlock s (m + 1)) :
    DegQ (evDelta s) a (evBlock s m) c := by
  intro v hv
  have hδ : evDelta s = 2 * s * evW s := rfl
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 3 ∧ m = 3 * i + t :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
  interval_cases t
  · -- weight-one layer
    simp only [Nat.add_zero] at ha hc hm hv ⊢
    rw [evBlock_three] at hv ⊢
    simp only [List.mem_singleton] at hv
    subst hv
    simp only [List.sum_singleton]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [hc (by omega), show 3 * 0 + 1 = 3 * 0 + 1 from rfl, evBlock_three_one]
      simp [List.sum_replicate, hδ]
    · rw [ha (by omega), show 3 * i - 1 = 3 * (i - 1) + 2 by omega, evBlock_three_two,
        List.sum_replicate, smul_eq_mul, Nat.sub_add_cancel h0]
      by_cases hi : 3 * i = 6 * s
      · have : i = 2 * s := by omega
        subst this; rw [hδ]; omega
      · rw [hc (by omega), evBlock_three_one, List.sum_replicate, smul_eq_mul, hδ]
        have : i * evW s + (2 * s - i) * evW s = 2 * s * evW s := by
          rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
        omega
  · rw [evBlock_three_one] at hv ⊢
    rw [List.mem_replicate] at hv
    rw [hv.2, ha (by omega), show 3 * i + 1 - 1 = 3 * i by omega, evBlock_three,
      hc (by omega), show 3 * i + 1 + 1 = 3 * i + 2 by omega, evBlock_three_two]
    simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul, hδ]
    have : (2 * s - i) * evW s + (i + 1) * evW s = 2 * s * evW s + evW s := by
      rw [← Nat.add_mul, show 2 * s - i + (i + 1) = 2 * s + 1 by omega, Nat.add_mul, one_mul]
    omega
  · rw [evBlock_three_two] at hv ⊢
    rw [List.mem_replicate] at hv
    rw [hv.2, ha (by omega), show 3 * i + 2 - 1 = 3 * i + 1 by omega, evBlock_three_one,
      hc (by omega), show 3 * i + 2 + 1 = 3 * (i + 1) by omega, evBlock_three]
    simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul, hδ]
    have : (2 * s - i) * evW s + (i + 1) * evW s = 2 * s * evW s + evW s := by
      rw [← Nat.add_mul, show 2 * s - i + (i + 1) = 2 * s + 1 by omega, Nat.add_mul, one_mul]
    omega

end Erdos612All
