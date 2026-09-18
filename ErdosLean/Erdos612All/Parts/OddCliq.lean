import ErdosLean.Erdos612All.Parts.OddDeg

/-!
# Erdős 612 (all `r`), part (ii): positivity, clique and tightness inside the CC period

Clump counts (`r = q+4`, `2r+1 = 2q+9`): `1`, `2q+6-j`, `j+2` for `m = 3j, 3j+1, 3j+2 < 6q+16`,
then `3`, `2q+5`, `3`.  Consecutive pairs: `2q+7-j`, `2q+8`, `j+3`, `4`, `2q+8`, `2q+8`, and the
last layer `E` with a right context of length `≤ 1`: all `< 2q+9`.
Tightness: layer `m = 3` has neighbours `2x` (layer 2) and `(2q+5)x` (layer 4), total `δ+1`.
-/

namespace Erdos612All

open Erdos612

theorem odBlock_pos (q m : ℕ) (hm : m < 6 * q + 19) :
    odBlock q m ≠ [] ∧ ∀ w ∈ odBlock q m, 0 < w := by
  have hu : 0 < odU q := by unfold odU; positivity
  have hX : odX q = 3 * odU q := rfl
  by_cases hlt : m < 6 * q + 16
  · obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 3 ∧ m = 3 * j + t :=
      ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
    interval_cases t
    · simp only [Nat.add_zero] at hlt ⊢
      simp [odBlock_three q j hlt]
    · rw [odBlock_three_one q j hlt]
      refine ⟨by simp; omega, fun w hw' => ?_⟩
      rw [(List.mem_replicate.mp hw').2]; omega
    · rw [odBlock_three_two q j hlt]
      refine ⟨by simp, fun w hw' => ?_⟩
      rw [(List.mem_replicate.mp hw').2]; omega
  · rcases (show m = 6 * q + 16 ∨ m = 6 * q + 17 ∨ m = 6 * q + 18 by omega) with h | h | h <;>
      subst h
    · rw [odBlock_E1]
      refine ⟨by simp [odE], fun w hw' => ?_⟩
      rw [(List.mem_replicate.mp hw').2]; exact hu
    · rw [odBlock_F]
      refine ⟨by simp [odF], fun w hw' => ?_⟩
      rcases odF_mem q w hw' with h | h <;> omega
    · rw [odBlock_E3]
      refine ⟨by simp [odE], fun w hw' => ?_⟩
      rw [(List.mem_replicate.mp hw').2]; exact hu

theorem odBlock_cliq (q m : ℕ) (hm : m < 6 * q + 19) (a c : List ℕ)
    (hc : m + 1 ≠ 6 * q + 19 → c = odBlock q (m + 1)) (hc1 : m + 1 = 6 * q + 19 → c.length ≤ 1) :
    CliqQ (2 * (q + 4) + 1) a (odBlock q m) c := by
  unfold CliqQ
  by_cases hlt : m < 6 * q + 16
  · obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 3 ∧ m = 3 * j + t :=
      ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
    interval_cases t
    · simp only [Nat.add_zero] at hc hc1 hm hlt ⊢
      rw [odBlock_three q j hlt, hc (by omega)]
      by_cases hj : 3 * j + 1 < 6 * q + 16
      · rw [odBlock_three_one q j hj]; simp; omega
      · rw [show 3 * j + 1 = 6 * q + 16 by omega, odBlock_E1]; simp [odE]; omega
    · rw [odBlock_three_one q j hlt, hc (by omega), show 3 * j + 1 + 1 = 3 * j + 2 by omega,
        odBlock_three_two q j (by omega)]
      simp; omega
    · rw [odBlock_three_two q j hlt, hc (by omega), show 3 * j + 2 + 1 = 3 * (j + 1) by omega,
        odBlock_three q (j + 1) (by omega)]
      simp; omega
  · rcases (show m = 6 * q + 16 ∨ m = 6 * q + 17 ∨ m = 6 * q + 18 by omega) with h | h | h <;>
      subst h
    · rw [odBlock_E1, hc (by omega), show 6 * q + 16 + 1 = 6 * q + 17 by omega, odBlock_F]
      simp [odE, odF]; omega
    · rw [odBlock_F, hc (by omega), show 6 * q + 17 + 1 = 6 * q + 18 by omega, odBlock_E3]
      simp [odE, odF]; omega
    · have := hc1 (by omega)
      rw [odBlock_E3]
      simp [odE]; omega

theorem odBlock_tight (q : ℕ) :
    TightQ (odDelta q) (odBlock q 2) (odBlock q 3) (odBlock q 4) := by
  refine ⟨1, ?_, ?_⟩
  · rw [show (3 : ℕ) = 3 * 1 by rfl, odBlock_three q 1 (by omega)]; simp
  · rw [show (3 : ℕ) = 3 * 1 by rfl, odBlock_three q 1 (by omega), show (2 : ℕ) = 3 * 0 + 2 by rfl,
      odBlock_three_two q 0 (by omega), show (4 : ℕ) = 3 * 1 + 1 by rfl,
      odBlock_three_one q 1 (by omega)]
    simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul]
    have hδX : odDelta q = (2 * q + 7) * odX q := rfl
    have : (0 + 2) * odX q + (2 * q + 6 - 1) * odX q = (2 * q + 7) * odX q := by
      rw [← Nat.add_mul, show 0 + 2 + (2 * q + 6 - 1) = 2 * q + 7 by omega]
    omega

end Erdos612All
