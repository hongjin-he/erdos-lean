import ErdosLean.Erdos612All.Parts.EvenDeg

/-!
# Erdős 612 (all `r`), part (i): positivity, clique and tightness inside the CSS block

Clump counts: `m = 3i` ↦ `1`, `m = 3i+1` ↦ `2s-i`, `m = 3i+2` ↦ `i+1` (`0 ≤ i ≤ 2s-1`), so two
consecutive layers have `2s+1-i`, `2s+1`, `i+2 ≤ 2s+1` clumps: fewer than `2r = 2s+2`.
Tightness: the weight-`1` layer `m = 3` has neighbours `w` (layer 2) and `(2s-1)w` (layer 4).
-/

namespace Erdos612All

open Erdos612

theorem evBlock_pos (s m : ℕ) (hs : 1 ≤ s) (hm : m ≤ 6 * s) :
    evBlock s m ≠ [] ∧ ∀ w ∈ evBlock s m, 0 < w := by
  have hw : 0 < evW s := by unfold evW; positivity
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 3 ∧ m = 3 * i + t :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
  interval_cases t
  · simp [evBlock_three]
  · rw [evBlock_three_one]
    refine ⟨by simp; omega, fun w hw' => ?_⟩
    rw [(List.mem_replicate.mp hw').2]; exact hw
  · rw [evBlock_three_two]
    refine ⟨by simp, fun w hw' => ?_⟩
    rw [(List.mem_replicate.mp hw').2]; exact hw

theorem evBlock_cliq (s m : ℕ) (hs : 1 ≤ s) (hm : m ≤ 6 * s) (a c : List ℕ)
    (hc : m ≠ 6 * s → c = evBlock s (m + 1)) (hc1 : m = 6 * s → c.length ≤ 1) :
    CliqQ (2 * (s + 1)) a (evBlock s m) c := by
  unfold CliqQ
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 3 ∧ m = 3 * i + t :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
  interval_cases t
  · simp only [Nat.add_zero] at hc hc1 hm ⊢
    rw [evBlock_three]
    by_cases h : 3 * i = 6 * s
    · have := hc1 h; simp; omega
    · rw [hc h, evBlock_three_one]; simp; omega
  · rw [evBlock_three_one, hc (by omega), show 3 * i + 1 + 1 = 3 * i + 2 by omega, evBlock_three_two]
    simp; omega
  · rw [evBlock_three_two, hc (by omega), show 3 * i + 2 + 1 = 3 * (i + 1) by omega, evBlock_three]
    simp; omega

theorem evBlock_tight (s : ℕ) (hs : 1 ≤ s) :
    TightQ (evDelta s) (evBlock s 2) (evBlock s 3) (evBlock s 4) := by
  refine ⟨1, ?_, ?_⟩
  · rw [show (3 : ℕ) = 3 * 1 by rfl, evBlock_three]; simp
  · rw [show (3 : ℕ) = 3 * 1 by rfl, evBlock_three, show (2 : ℕ) = 3 * 0 + 2 by rfl,
      evBlock_three_two, show (4 : ℕ) = 3 * 1 + 1 by rfl, evBlock_three_one]
    simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul]
    have hδ : evDelta s = 2 * s * evW s := rfl
    have : (0 + 1) * evW s + (2 * s - 1) * evW s = 2 * s * evW s := by
      rw [← Nat.add_mul, show 0 + 1 + (2 * s - 1) = 2 * s by omega]
    omega

end Erdos612All
