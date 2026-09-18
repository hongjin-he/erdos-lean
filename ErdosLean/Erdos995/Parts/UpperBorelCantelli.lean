import ErdosLean.Erdos995.Parts.UpperL2

/-!
# Erdős 995, part U2 (UpperBorelCantelli): dyadic almost-sure bound for the majorant

Ho, Remark 7.1. Chebyshev (`meas_ge_le_lintegral_div`) with U1 gives
`μ{G_{2^{j+1}} > δ 2^j j^{1/2+ε}} ≤ 4K / (δ² j^{1+2ε})`, which is summable in `j`
(`Real.summable_nat_rpow_inv` / `Real.summable_one_div_nat_rpow`); Borel–Cantelli
(`MeasureTheory.ae_eventually_notMem`) concludes.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Upper

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma ae_eventually_sumNorm_le (f : Lp ℂ 2 μ𝕋) (n : ℕ → ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᵐ x ∂μ𝕋, ∀ᶠ j : ℕ in atTop,
      sumNorm f n (2 ^ (j + 1)) x ≤ δ * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by
  set p : ℝ := 1 + 2 * ε with hp
  set C : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ𝕋 + ‖f 0‖ₑ ^ 2 with hCdef
  have hC : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨lintegral_enorm_sq_ne_top f, by simp⟩
  set t : ℕ → ℝ := fun J => δ * ((2 : ℝ) ^ J * (J : ℝ) ^ ((1 : ℝ) / 2 + ε)) with htdef
  set s : ℕ → Set 𝕋 := fun j => {x | t (j + 1) < sumNorm f n (2 ^ (j + 1 + 1)) x} with hsdef
  have key : ∀ j : ℕ, μ𝕋 (s j) ≤
      ENNReal.ofReal (4 * C.toReal / δ ^ 2 * ((((j + 1 : ℕ) : ℝ)) ^ p)⁻¹) := by
    intro j
    have hJ : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have ht : 0 < t (j + 1) := by simp only [htdef]; positivity
    have hsub : s j ⊆ {x | ENNReal.ofReal (t (j + 1)) ^ 2 ≤
        ENNReal.ofReal (sumNorm f n (2 ^ (j + 1 + 1)) x) ^ 2} := by
      intro x hx
      simp only [hsdef, Set.mem_ofPred_eq] at hx ⊢
      exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hx.le) 2
    have hne : ENNReal.ofReal (t (j + 1)) ^ 2 ≠ 0 := by
      apply pow_ne_zero; simpa using ht
    calc μ𝕋 (s j) ≤ μ𝕋 {x | ENNReal.ofReal (t (j + 1)) ^ 2 ≤
          ENNReal.ofReal (sumNorm f n (2 ^ (j + 1 + 1)) x) ^ 2} := measure_mono hsub
      _ ≤ (∫⁻ x, ENNReal.ofReal (sumNorm f n (2 ^ (j + 1 + 1)) x) ^ 2 ∂μ𝕋) /
            ENNReal.ofReal (t (j + 1)) ^ 2 :=
          meas_ge_le_lintegral_div
            ((aemeasurable_sumNorm f n _).ennreal_ofReal.pow_const 2) hne
            (by simp)
      _ ≤ ((2 ^ (j + 1 + 1) : ℕ) : ℝ≥0∞) ^ 2 * C / ENNReal.ofReal (t (j + 1)) ^ 2 := by
          gcongr; exact lintegral_sumNorm_sq_le f n _
      _ = ENNReal.ofReal ((((2 ^ (j + 1 + 1) : ℕ) : ℝ)) ^ 2 * C.toReal / (t (j + 1)) ^ 2) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < t (j + 1) ^ 2),
            ENNReal.ofReal_pow ht.le,
            ENNReal.ofReal_mul (p := (((2 ^ (j + 1 + 1) : ℕ) : ℝ)) ^ 2) (by positivity),
            ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hC]
      _ = _ := by
          congr 1
          have hrp : (((j + 1 : ℕ) : ℝ)) ^ p = ((((j + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2 + ε)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hJ.le]
            congr 1; rw [hp]; push_cast; ring
          have hpos : 0 < (((j + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2 + ε) := Real.rpow_pos_of_pos hJ _
          rw [hrp]
          simp only [htdef]
          have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
          field_simp
          push_cast
          ring
  have hs : Summable (fun j : ℕ => 4 * C.toReal / δ ^ 2 * ((((j + 1 : ℕ) : ℝ)) ^ p)⁻¹) :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by rw [hp]; linarith))).mul_left _
  have hsum : ∑' j, μ𝕋 (s j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with x hx
  rw [eventually_atTop] at hx ⊢
  obtain ⟨N, hN⟩ := hx
  refine ⟨N + 1, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have := hN i (by omega)
  simp only [hsdef, htdef, Set.mem_ofPred_eq, not_lt] at this
  exact this

end Upper
end Erdos995
