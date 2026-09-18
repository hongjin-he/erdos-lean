import ErdosLean.Erdos612All.Parts.RangeSum
import ErdosLean.Erdos612All.Parts.EvenDeg
import ErdosLean.Erdos612.Parts.Coeff

/-!
# Erdős 612 (all `r`), part (i): period length, period weight, growth inequality

The block has `6s+1` layers and weight `(2s+1)(δ+1)` (`2s+1` weight-`1` layers and `2s` pairs
of layers of total weight `(2s+1)w` each, `2s·w = δ`).  With
`c = evenCoeff (s+1) = 2s(3s+5)/(2s²+4s+1)` the growth condition
`c·(2s+1)(δ+1) < (6s+1)δ` is equivalent (using `(6s+1)(2s²+4s+1) = 2s(3s+5)(2s+1) + 1`) to
`2s(3s+5)(2s+1) < δ = 2s(3s+5)(2s+2)`.
-/

namespace Erdos612All

open Erdos612

theorem evPer_length (s : ℕ) : (evPer s).length = 6 * s + 1 := by
  simp [evPer]

theorem evPer_total (s : ℕ) : (evPer s).total = (2 * s + 1) * (evDelta s + 1) := by
  rw [evPer, total_map_range, show 6 * s + 1 = 3 * (2 * s) + 1 by ring, Finset.sum_range_succ,
    sum_range_three, evBlock_three]
  have h : ∀ j ∈ Finset.range (2 * s), (evBlock s (3 * j)).sum + (evBlock s (3 * j + 1)).sum
      + (evBlock s (3 * j + 2)).sum = 1 + (2 * s + 1) * evW s := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [evBlock_three, evBlock_three_one, evBlock_three_two]
    simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul]
    rw [Nat.add_assoc, ← Nat.add_mul, show 2 * s - j + (j + 1) = 2 * s + 1 by omega]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]
  simp only [List.sum_singleton, evDelta]
  ring

theorem ev_growth (s : ℕ) (hs : 1 ≤ s) :
    evenCoeff (s + 1) * ((evPer s).total : ℝ) < ((evPer s).length : ℝ) * (evDelta s : ℝ) := by
  rw [evPer_total, evPer_length]
  unfold evenCoeff evDelta evW
  push_cast
  have hS : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : (0 : ℝ) < 2 * ((s : ℝ) + 1) ^ 2 - 1 := by nlinarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  have key : (6 * (s : ℝ) + 1) * (2 * s * (2 * (s + 1) * (3 * s + 5))) * (2 * ((s : ℝ) + 1) ^ 2 - 1)
      - 2 * ((s : ℝ) + 1 - 1) * (3 * ((s : ℝ) + 1) + 2) *
        ((2 * s + 1) * (2 * s * (2 * (s + 1) * (3 * s + 5)) + 1)) = 2 * s * (3 * s + 5) := by
    ring
  nlinarith

end Erdos612All
