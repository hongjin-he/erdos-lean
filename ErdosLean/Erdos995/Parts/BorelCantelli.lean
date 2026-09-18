import ErdosLean.Erdos995.Parts.StageProb

/-!
# Erdős 995, part L4 (BorelCantelli): almost surely every large stage succeeds

First Borel–Cantelli (`MeasureTheory.ae_eventually_notMem`) applied to the
summable failure probabilities of L3 (Ho §7: `Pr(S_kᶜ) ≤ (k+1)^{-8}`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma ae_eventually_stageGood : ∀ᵐ x ∂μ𝕋, ∀ᶠ k in atTop, x ∈ stageGood k := by
  have hsum : ∑' k, μ𝕋 (stageGood k)ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum measure_compl_stageGood_le)
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ?_ ?_
    · rw [ENNReal.tsum_geometric]; simp
    · exact ENNReal.tsum_le_tsum fun k => pow_le_pow_of_le_one (by simp) (by norm_num) (by omega)
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with k hk
  simpa using hk

end Con
end Erdos995
