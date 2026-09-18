import ErdosLean.Erdos995.Statement

/-!
# Erdős 995, part C (Consequences): critical exponent and the `o(N √(log log N))` question

Pure real analysis on top of the two bounds.
* `θ > 1/2`: `ErdosUpperBound` with `ε = θ - 1/2` gives `o`, hence `O`.
* `θ < 1/2`: take Ho's `f, n` and a point `x` in the intersection of the two full-measure sets
  (Haar measure is a probability measure, so a conull set is nonempty). With `ε = (1/2 - θ)/2`,
  `(log N)^θ ≤ (log N)^{1/2-ε}` once `log N ≥ 1`; the `O`-bound `‖S_N‖ ≤ K N (log N)^θ` contradicts
  `(K+1) N (log N)^{1/2-ε} ≤ Re S_N ≤ ‖S_N‖` for infinitely many `N`.
* `¬ LogLogQuestion`: same, with `ε = 1/4` and `√(log log N) = o((log N)^{1/4})`
  (`isLittleO_log_rpow_atTop` composed with `log`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995

/-- For `N ≥ 3`, `1 ≤ log N`. -/
lemma one_le_log_nat {N : ℕ} (hN : 3 ≤ N) : (1 : ℝ) ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  have := Real.exp_one_lt_d9
  linarith

/-- `√(log y) ≤ 2 y^{1/4}` for `y ≥ 1`. -/
lemma sqrt_log_le {y : ℝ} (hy : 1 ≤ y) : Real.sqrt (Real.log y) ≤ 2 * y ^ ((1 : ℝ) / 4) := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : Real.log y ≤ y ^ ((1 : ℝ) / 2) / (1 / 2) := Real.log_le_rpow_div hy0 (by norm_num)
  have hq : 0 ≤ y ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hy0 _
  have hsq : (y ^ ((1 : ℝ) / 4)) ^ 2 = y ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hh : 0 ≤ y ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0 _
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith

lemma criticalExponent_of (hU : ErdosUpperBound) (hL : HoLowerBound) : Erdos995CriticalExponent := by
  refine ⟨fun θ hθ f n hn => ?_, fun θ hθ hG => ?_⟩
  · have h := hU f n hn (θ - 1 / 2) (by linarith)
    have e : (1 : ℝ) / 2 + (θ - 1 / 2) = θ := by ring
    rw [e] at h
    filter_upwards [h] with x hx using hx.isBigO
  · obtain ⟨f, n, hn, -, -, hlow⟩ := hL
    have hup := hG f n hn.isLacunary
    obtain ⟨x, hx1, hx2⟩ := (hup.and hlow).exists
    obtain ⟨K, hK, hB⟩ := hx1.exists_pos
    have hb := hB.bound
    set ε : ℝ := (1 / 2 - θ) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hfr := hx2 ε hεpos (K + 1)
    obtain ⟨N, hN1, hN2, hN3⟩ :=
      (hfr.and_eventually (hb.and (eventually_ge_atTop 3))).exists
    have hlog := one_le_log_nat hN3
    have hNpos : (0 : ℝ) < N := by have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
                                   linarith
    have hr1 : 0 < Real.log N ^ ((1 : ℝ) / 2 - ε) := Real.rpow_pos_of_pos (by linarith) _
    have hr2 : 0 ≤ Real.log N ^ θ := Real.rpow_nonneg (by linarith) _
    have hmono : Real.log N ^ θ ≤ Real.log N ^ ((1 : ℝ) / 2 - ε) :=
      Real.rpow_le_rpow_of_exponent_le hlog (by rw [hε]; linarith)
    have hnorm : ‖(N : ℝ) * Real.log N ^ θ‖ = (N : ℝ) * Real.log N ^ θ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm] at hN2
    have hre : (lacSum f n x N).re ≤ ‖lacSum f n x N‖ := Complex.re_le_norm _
    have h4 : K * ((N : ℝ) * Real.log N ^ θ) ≤ K * ((N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε)) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      exact mul_le_mul_of_nonneg_left hmono hNpos.le
    have h5 : 0 < (N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε) := mul_pos hNpos hr1
    nlinarith

lemma not_logLogQuestion_of (hL : HoLowerBound) : ¬ LogLogQuestion := by
  intro hQ
  obtain ⟨f, n, hn, -, -, hlow⟩ := hL
  have hup := hQ f n hn.isLacunary
  obtain ⟨x, hx1, hx2⟩ := (hup.and hlow).exists
  have hb := hx1.bound (show (0 : ℝ) < 1 by norm_num)
  have hfr := hx2 (1 / 4) (by norm_num) 3
  obtain ⟨N, hN1, hN2, hN3⟩ := (hfr.and_eventually (hb.and (eventually_ge_atTop 3))).exists
  have hlog := one_le_log_nat hN3
  have hNpos : (0 : ℝ) < N := by have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
                                 linarith
  have hsq := sqrt_log_le hlog
  have hnorm : ‖(N : ℝ) * Real.sqrt (Real.log (Real.log N))‖
      = (N : ℝ) * Real.sqrt (Real.log (Real.log N)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm] at hN2
  have hre : (lacSum f n x N).re ≤ ‖lacSum f n x N‖ := Complex.re_le_norm _
  have e : (1 : ℝ) / 2 - 1 / 4 = 1 / 4 := by norm_num
  rw [e] at hN1
  have hr1 : 0 < Real.log N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have h4 : (N : ℝ) * Real.sqrt (Real.log (Real.log N)) ≤ N * (2 * Real.log N ^ ((1 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_left hsq hNpos.le
  have h5 : 0 < (N : ℝ) * Real.log N ^ ((1 : ℝ) / 4) := mul_pos hNpos hr1
  nlinarith

end Erdos995
