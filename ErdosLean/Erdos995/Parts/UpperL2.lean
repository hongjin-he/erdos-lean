import ErdosLean.Erdos995.Defs

/-!
# Erdős 995, part U1 (UpperL2): the `L²` bound for the maximal majorant

Ho, arXiv:2604.18535, Remark 7.1. For every sequence `n` (no lacunarity
needed) and `f ∈ L²`: `∫ G_M² ≤ M² (‖f‖₂² + |f(0)|²)`, where `G_M = ∑_{k<M} ‖f(n_k ·)‖`.
Proof: `(∑_{k<M} a_k)² ≤ M ∑_{k<M} a_k²` (`ENNReal.rpow_sum_le_const_mul_sum_rpow` or
Cauchy–Schwarz) and `∫ ‖f(n x)‖² = ∫ ‖f‖²` for `n ≥ 1` (`x ↦ n • x` preserves Haar measure,
`Erdos996.Asm.measurePreserving_nsmul`), while for `n = 0` the integrand is the constant `‖f 0‖²`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Upper

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Trivial majorisation of the partial sums by the maximal majorant. -/
lemma norm_lacSum_le_sumNorm (f : Lp ℂ 2 μ𝕋) (n : ℕ → ℕ) (x : 𝕋) {N M : ℕ} (h : N ≤ M) :
    ‖lacSum f n x N‖ ≤ sumNorm f n M x := by
  unfold lacSum sumNorm
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
      (fun _ _ _ => norm_nonneg _))

/-- `x ↦ n • x` preserves Haar measure for `n ≠ 0`. -/
lemma measurePreserving_nsmul' (n : ℕ) (hn : n ≠ 0) :
    MeasurePreserving (fun x : 𝕋 => n • x) μ𝕋 μ𝕋 := by
  have hmp : MeasurePreserving (fun x : 𝕋 => (n : ℤ) • x) μ𝕋 μ𝕋 :=
    Measure.measurePreserving_zsmul μ𝕋 (by exact_mod_cast hn)
  have e : (fun x : 𝕋 => n • x) = fun x => (n : ℤ) • x := by
    funext x; exact (natCast_zsmul x n).symm
  rw [e]; exact hmp

lemma aestronglyMeasurable_comp_nsmul (f : Lp ℂ 2 μ𝕋) (m : ℕ) :
    AEStronglyMeasurable (fun x : 𝕋 => f (m • x)) μ𝕋 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_smul]; exact aestronglyMeasurable_const
  · exact (Lp.aestronglyMeasurable f).comp_measurePreserving
      (measurePreserving_nsmul' m hm.ne')

lemma lintegral_comp_nsmul_le (f : Lp ℂ 2 μ𝕋) (m : ℕ) :
    ∫⁻ x, ‖f (m • x)‖ₑ ^ 2 ∂μ𝕋 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ𝕋 + ‖f 0‖ₑ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_smul, lintegral_const, measure_univ, mul_one]
    exact le_add_self
  · have hmp := measurePreserving_nsmul' m hm.ne'
    have hg : AEMeasurable (fun x : 𝕋 => ‖f x‖ₑ ^ 2) (Measure.map (fun x : 𝕋 => m • x) μ𝕋) := by
      rw [hmp.map_eq]; exact (Lp.aestronglyMeasurable f).enorm.pow_const 2
    rw [← lintegral_map' hg hmp.measurable.aemeasurable, hmp.map_eq]
    exact le_self_add

/-- Measurability of the majorant. -/
lemma aemeasurable_sumNorm (f : Lp ℂ 2 μ𝕋) (n : ℕ → ℕ) (M : ℕ) :
    AEMeasurable (sumNorm f n M) μ𝕋 := by
  unfold sumNorm
  exact Finset.aemeasurable_fun_sum _ fun k _ =>
    (aestronglyMeasurable_comp_nsmul f (n k)).norm.aemeasurable

/-- The `L²` norm of `f` is finite. -/
lemma lintegral_enorm_sq_ne_top (f : Lp ℂ 2 μ𝕋) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ𝕋 ≠ ∞ := by
  have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
    (Lp.memLp f).eLpNorm_lt_top
  have e : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [e, ENNReal.rpow_natCast] at h2
  simpa using h2.ne

/-- **Key `L²` estimate.** `∫ G_M² ≤ M² (∫ ‖f‖² + ‖f 0‖²)`. -/
lemma lintegral_sumNorm_sq_le (f : Lp ℂ 2 μ𝕋) (n : ℕ → ℕ) (M : ℕ) :
    ∫⁻ x, ENNReal.ofReal (sumNorm f n M x) ^ 2 ∂μ𝕋 ≤
      (M : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ𝕋 + ‖f 0‖ₑ ^ 2) := by
  set C := ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ𝕋 + ‖f 0‖ₑ ^ 2
  have hpt : ∀ x, ENNReal.ofReal (sumNorm f n M x) ^ 2 ≤
      (M : ℝ≥0∞) * ∑ k ∈ range M, ‖f (n k • x)‖ₑ ^ 2 := by
    intro x
    have hreal : (sumNorm f n M x) ^ 2 ≤ (M : ℝ) * ∑ k ∈ range M, ‖f (n k • x)‖ ^ 2 := by
      unfold sumNorm
      simpa using sq_sum_le_card_mul_sum_sq (s := range M) (f := fun k => ‖f (n k • x)‖)
    calc ENNReal.ofReal (sumNorm f n M x) ^ 2
        = ENNReal.ofReal ((sumNorm f n M x) ^ 2) := by
          have h0 : (0 : ℝ) ≤ sumNorm f n M x := Finset.sum_nonneg fun _ _ => norm_nonneg _
          rw [ENNReal.ofReal_pow h0]
      _ ≤ ENNReal.ofReal ((M : ℝ) * ∑ k ∈ range M, ‖f (n k • x)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = (M : ℝ≥0∞) * ∑ k ∈ range M, ‖f (n k • x)‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  calc ∫⁻ x, ENNReal.ofReal (sumNorm f n M x) ^ 2 ∂μ𝕋
      ≤ ∫⁻ x, (M : ℝ≥0∞) * ∑ k ∈ range M, ‖f (n k • x)‖ₑ ^ 2 ∂μ𝕋 := lintegral_mono hpt
    _ = (M : ℝ≥0∞) * ∑ k ∈ range M, ∫⁻ x, ‖f (n k • x)‖ₑ ^ 2 ∂μ𝕋 := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top M), lintegral_finsetSum']
        intro k _
        exact (aestronglyMeasurable_comp_nsmul f (n k)).enorm.pow_const 2
    _ ≤ (M : ℝ≥0∞) * ∑ k ∈ range M, C := by
        gcongr with k hk
        exact lintegral_comp_nsmul_le f (n k)
    _ = (M : ℝ≥0∞) ^ 2 * C := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul, ← mul_assoc, sq]

end Upper
end Erdos995
