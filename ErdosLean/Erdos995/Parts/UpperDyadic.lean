import ErdosLean.Erdos995.Defs

/-!
# Erdős 995, part U3 (UpperDyadic): from dyadic bounds to little-o (deterministic)

If `‖S_N‖ ≤ G(2^{⌊log₂ N⌋+1})` and, for every `m`, eventually
`G(2^{j+1}) ≤ (m+1)⁻¹ 2^j j^{1/2+ε}`, then `S_N = o(N (log N)^{1/2+ε})`: for
`2^j ≤ N < 2^{j+1}` one has `2^j ≤ N` and `j ≤ log₂ N = log N / log 2 ≤ 2 log N`, so
`2^j j^{1/2+ε} ≤ 2^{1/2+ε} · N (log N)^{1/2+ε}` (`Real.rpow_le_rpow`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Upper

lemma isLittleO_of_dyadic (S : ℕ → ℂ) (G : ℕ → ℝ)
    (hSG : ∀ N : ℕ, ‖S N‖ ≤ G (2 ^ (Nat.log 2 N + 1))) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ m : ℕ, ∀ᶠ j : ℕ in atTop,
      G (2 ^ (j + 1)) ≤ (1 / ((m : ℝ) + 1)) * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    S =o[atTop] (fun N : ℕ => (N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 + ε)) := by
  set a : ℝ := (1 : ℝ) / 2 + ε with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨m, hm⟩ := exists_nat_gt ((2 : ℝ) ^ a / c)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (h m)
  rw [Filter.eventually_atTop]
  refine ⟨2 ^ J + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN1
  have hJN : 2 ^ J ≤ N := le_trans (Nat.le_succ _) hN
  set j := Nat.log 2 N with hj
  have hjJ : J ≤ j := Nat.le_log_of_pow_le (by norm_num) hJN
  have hG := hJ j hjJ
  have h2j : (2 : ℝ) ^ j ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 hN0
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hjlog : (j : ℝ) ≤ 2 * Real.log N := by
    have h1 : (j : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h2j
    have h2 := Real.log_two_gt_d9
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hjrpow : (j : ℝ) ^ a ≤ (2 : ℝ) ^ a * Real.log N ^ a := by
    rw [← Real.mul_rpow (by norm_num) hlogN]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hjlog ha0.le
  have hm1 : (2 : ℝ) ^ a / ((m : ℝ) + 1) ≤ c := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at hm
    nlinarith
  have hnorm : ‖(N : ℝ) * Real.log N ^ a‖ = N * Real.log N ^ a :=
    Real.norm_of_nonneg (by positivity)
  rw [hnorm]
  calc ‖S N‖ ≤ G (2 ^ (j + 1)) := hSG N
    _ ≤ 1 / ((m : ℝ) + 1) * ((2 : ℝ) ^ j * (j : ℝ) ^ a) := hG
    _ ≤ 1 / ((m : ℝ) + 1) * ((N : ℝ) * ((2 : ℝ) ^ a * Real.log N ^ a)) := by
        gcongr
    _ = (2 : ℝ) ^ a / ((m : ℝ) + 1) * (N * Real.log N ^ a) := by ring
    _ ≤ c * (N * Real.log N ^ a) := by gcongr

end Upper
end Erdos995
