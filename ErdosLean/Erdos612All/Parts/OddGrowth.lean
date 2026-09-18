import ErdosLean.Erdos612All.Parts.RangeSum
import ErdosLean.Erdos612All.Parts.OddDeg
import ErdosLean.Erdos612.Parts.Coeff

/-!
# Erdős 612 (all `r`), part (ii): period length, period weight, growth inequality

The period has `6q+19 = 6r-5` layers.  Its weight is
`S = (2q+5)(1 + (2q+8)x) + 1 + 3u + (6q+19)u + 3u = (2q+6) + (12q²+84q+145)u`
(first `3(2q+5)` layers grouped in triples via `sum_range_three`, then `[1]`, `E`, `F`, `E`).
With `c = oddCoeff (q+4) = (3q+11)/(q+4)`, `P = 6q+19`, `δ = (6q+21)u`:
`P·δ·(q+4) - (3q+11)·S = u - (3q+11)(2q+6) > 0` since `u = (3q+11)(12q+38)`.
-/

namespace Erdos612All

open Erdos612

theorem odPer_length (q : ℕ) : (odPer q).length = 6 * q + 19 := by
  simp [odPer]

theorem odPer_total (q : ℕ) :
    (odPer q).total = (2 * q + 6) + (12 * q ^ 2 + 84 * q + 145) * odU q := by
  rw [odPer, total_map_range, show 6 * q + 19 = 3 * (2 * q + 5) + 1 + 1 + 1 + 1 by ring,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_range_three, odBlock_three q _ (by omega),
    show 3 * (2 * q + 5) + 1 = 6 * q + 16 by ring, odBlock_E1,
    show 3 * (2 * q + 5) + 2 = 6 * q + 17 by ring, odBlock_F,
    show 3 * (2 * q + 5) + 3 = 6 * q + 18 by ring, odBlock_E3, odE_sum, odF_sum]
  have h : ∀ j ∈ Finset.range (2 * q + 5), (odBlock q (3 * j)).sum + (odBlock q (3 * j + 1)).sum
      + (odBlock q (3 * j + 2)).sum = 1 + (2 * q + 8) * odX q := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [odBlock_three q j (by omega), odBlock_three_one q j (by omega),
      odBlock_three_two q j (by omega)]
    simp only [List.sum_singleton, List.sum_replicate, smul_eq_mul]
    rw [Nat.add_assoc, ← Nat.add_mul, show 2 * q + 6 - j + (j + 2) = 2 * q + 8 by omega]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]
  simp only [List.sum_singleton, odX]
  ring

theorem od_growth (q : ℕ) :
    oddCoeff (q + 4) * ((odPer q).total : ℝ) < ((odPer q).length : ℝ) * (odDelta q : ℝ) := by
  rw [odPer_total, odPer_length]
  unfold oddCoeff odDelta odX odU
  push_cast
  have hq : (0 : ℝ) ≤ q := by positivity
  have hden : (0 : ℝ) < (q : ℝ) + 4 := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  have key : (6 * (q : ℝ) + 19) * ((2 * q + 7) * (3 * ((3 * q + 11) * (2 * (6 * q + 19))))) *
      ((q : ℝ) + 4) - (3 * ((q : ℝ) + 4) - 1) * (2 * q + 6 + (12 * q ^ 2 + 84 * q + 145) *
        ((3 * q + 11) * (2 * (6 * q + 19)))) = (3 * q + 11) * (10 * q + 32) := by
    ring
  nlinarith

end Erdos612All
