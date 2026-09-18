import ErdosLean.Erdos996.Defs

/-! # Erdős 996: pointwise lower bound for the spike. -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Lower floor of a spike: `φ_d ≥ -g_d` with `g_d = 1/√(2^d - 1)`. -/
lemma spike_ge (d : ℕ) (hd : 1 ≤ d) (x : 𝕋) :
    -(1 / Real.sqrt (2 ^ d - 1)) ≤ spike d x := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have h2 : (2 : ℝ) ^ d * (2 : ℝ)⁻¹ ^ d = 1 := by rw [← mul_pow]; norm_num
  have h1 : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hq : 0 < Real.sqrt (2 ^ d - 1) := Real.sqrt_pos.2 (by linarith)
  have hs : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) =
      (2 : ℝ)⁻¹ ^ d * Real.sqrt (2 ^ d - 1) := by
    rw [show (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) = ((2 : ℝ)⁻¹ ^ d) ^ 2 * (2 ^ d - 1) by
      linear_combination (-(2 : ℝ)⁻¹ ^ d) * h2]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
  have hI : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : 𝕋 → ℝ) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hpq : 0 < (2 : ℝ)⁻¹ ^ d * Real.sqrt (2 ^ d - 1) := mul_pos hp hq
  have he : -(1 / Real.sqrt (2 ^ d - 1)) =
      (0 - (2 : ℝ)⁻¹ ^ d) / ((2 : ℝ)⁻¹ ^ d * Real.sqrt (2 ^ d - 1)) := by
    field_simp
    ring
  unfold spike
  rw [hs, he, div_le_div_iff_of_pos_right hpq]
  linarith

end Erdos996
