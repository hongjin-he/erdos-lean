import ErdosLean.Erdos995.Parts.GlobalL2

/-!
# Erdős 995, part L7 (MeanZero): `∫ g = 0`

Adapted from the second half of `ErdosLean/Erdos996/Parts/Asm/GlobalL2.lean`
(`tendsto_fourierCoeff_partialSum` at `r = 0` by dominated convergence with majorant
`gPos.toReal + ∑ c_k`, and `∫ F_k = 0`). Only the frequency `0` is needed, so the
Fourier-disjointness step can be skipped: `∫ ∑_{k<K} F_k = 0` for every `K`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma meanZero_integral_blk (k : ℕ) : ∫ x, blk k x ∂μ𝕋 = 0 := by
  have h : fourierCoeff (fun x => (blk k x : ℂ)) 0 = 0 := by
    rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero k q), mul_zero]
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma meanZero_integral_partialSum (K : ℕ) : ∫ x, ∑ k ∈ range K, blk k x ∂μ𝕋 = 0 := by
  rw [integral_finsetSum _ (fun k _ => integrable_blk k)]
  exact Finset.sum_eq_zero fun k _ => meanZero_integral_blk k

lemma meanZero_integral_gFun_real : ∫ x, gFun x ∂μ𝕋 = 0 := by
  have hS : ∀ K, Measurable (fun x => ∑ k ∈ range K, blk k x) := fun K =>
    Finset.measurable_sum _ fun k _ => measurable_blk k
  have hG : Integrable (fun x => (gPos x).toReal + ∑' k, floorC k) μ𝕋 :=
    (integrable_toReal_of_lintegral_ne_top measurable_gPos.aemeasurable
      lintegral_gPos_ne_top).add (integrable_const _)
  have ht : Tendsto (fun K => ∫ x, ∑ k ∈ range K, blk k x ∂μ𝕋) atTop
      (𝓝 (∫ x, gFun x ∂μ𝕋)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (gPos x).toReal + ∑' k, floorC k) (fun K => (hS K).aestronglyMeasurable)
      hG ?_ ?_
    · intro K
      filter_upwards [ae_gPos_ne_top] with x hx
      obtain ⟨hs, htr⟩ := gPos_toReal_eq x hx
      rw [Real.norm_eq_abs, htr]
      have h1 : |∑ k ∈ range K, blk k x| ≤
          ∑ k ∈ range K, (blk k x + floorC k) + ∑ k ∈ range K, floorC k := by
        rw [← Finset.sum_add_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        have h1 := blk_floor k x
        have h2 := floorC_nonneg k
        rw [abs_le]
        constructor <;> linarith
      have h2 : ∑ k ∈ range K, (blk k x + floorC k) ≤ ∑' k, (blk k x + floorC k) :=
        hs.sum_le_tsum _ fun k _ => by linarith [blk_floor k x]
      have h3 : ∑ k ∈ range K, floorC k ≤ ∑' k, floorC k :=
        summable_floorC.sum_le_tsum _ fun k _ => floorC_nonneg k
      linarith
    · filter_upwards [ae_gPos_ne_top] with x hx
      exact tendsto_partialSum_gFun x hx
  simp only [meanZero_integral_partialSum] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma integral_gFun : ∫ x, (gFun x : ℂ) ∂μ𝕋 = 0 := by
  rw [integral_complex_ofReal, meanZero_integral_gFun_real, Complex.ofReal_zero]

end Con
end Erdos995
