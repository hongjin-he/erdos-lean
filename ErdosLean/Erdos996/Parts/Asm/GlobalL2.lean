import ErdosLean.Erdos996.Parts.Asm.PartialSumL2

/-!
# Assembly sub-lemma 8 (GlobalL2): the global function `g = ∑ F_k`

Blueprint §8. Ho Prop. 4.3, first paragraph, simplified (no Kolmogorov criterion):
* `∑ (F_k + c_k) ≥ 0` termwise and `∫ ∑ (F_k + c_k) = ∑ c_k < ∞` (monotone convergence,
  `∫ F_k = 0`), so `gPos < ∞` a.e.;
* where `gPos x < ∞`, the partial sums `∑_{k<K} F_k x → gFun x`;
* Fatou (`eLpNorm_partialSum_le`) gives `g ∈ L²`;
* `‖g - ∑_{k<K} F_k‖₁ ≤ 2 ∑_{k ≥ K} c_k → 0`, hence `∫ g = 0` and the Fourier coefficients of
  `g` are the sums of those of the blocks (only one block is nonzero at each frequency).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-! ### Auxiliary facts about the blocks -/

lemma measurable_blk (A k : ℕ) : Measurable (blk A k) := by
  unfold blk block
  refine Measurable.const_mul (Finset.measurable_sum _ fun q _ => ?_) _
  exact (measurable_spike _).comp (continuous_nsmul _).measurable

lemma integrable_blk (A k : ℕ) : Integrable (blk A k) μ𝕋 := by
  refine Integrable.of_bound (measurable_blk A k).aestronglyMeasurable
    (Real.sqrt (lam A k / blockLen A k) * ∑ q ∈ Finset.Icc 1 (blockLen A k), (2 : ℝ) ^ depth A k)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  unfold blk block
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => abs_spike_le _ _)

lemma fourierCoeff_blk_zero (A k : ℕ) : fourierCoeff (fun x => (blk A k x : ℂ)) 0 = 0 := by
  rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero A k q), mul_zero]

lemma integral_blk (A k : ℕ) : ∫ x, blk A k x ∂μ𝕋 = 0 := by
  have h := fourierCoeff_blk_zero A k
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma measurable_gPos (A : ℕ) : Measurable (gPos A) := by
  unfold gPos
  exact Measurable.ennreal_tsum fun k => ((measurable_blk A k).add_const _).ennreal_ofReal

lemma measurable_gFun (A : ℕ) : Measurable (gFun A) := by
  unfold gFun
  exact (measurable_gPos A).ennreal_toReal.sub_const _

lemma lintegral_gPos (A : ℕ) :
    ∫⁻ x, gPos A x ∂μ𝕋 = ∑' k, ENNReal.ofReal (floorC A k) := by
  unfold gPos
  rw [lintegral_tsum fun k => ((measurable_blk A k).add_const _).ennreal_ofReal.aemeasurable]
  congr 1
  ext k
  have hi : Integrable (fun x => blk A k x + floorC A k) μ𝕋 :=
    (integrable_blk A k).add (integrable_const _)
  have hnn : (0 : 𝕋 → ℝ) ≤ᵐ[μ𝕋] fun x => blk A k x + floorC A k :=
    ae_of_all _ fun x => by
      have := blk_floor A k x
      simp only [Pi.zero_apply]
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_add (integrable_blk A k) (integrable_const _), integral_blk, integral_const]
  simp

lemma lintegral_gPos_ne_top (A : ℕ) (hA : 1 ≤ A) : ∫⁻ x, gPos A x ∂μ𝕋 ≠ ∞ := by
  rw [lintegral_gPos, ← ENNReal.ofReal_tsum_of_nonneg (floorC_nonneg A) (summable_floorC A hA)]
  exact ENNReal.ofReal_ne_top

lemma gPos_toReal_eq (A : ℕ) (x : 𝕋) (hx : gPos A x ≠ ∞) :
    Summable (fun k => blk A k x + floorC A k) ∧
      (gPos A x).toReal = ∑' k, (blk A k x + floorC A k) := by
  have hnn : ∀ k, 0 ≤ blk A k x + floorC A k := fun k => by linarith [blk_floor A k x]
  have e : ∀ k, (ENNReal.ofReal (blk A k x + floorC A k)).toReal = blk A k x + floorC A k :=
    fun k => ENNReal.toReal_ofReal (hnn k)
  constructor
  · have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (blk A k x + floorC A k)) hx
    simp only [e] at this
    exact this
  · unfold gPos
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    simp only [e]

lemma hasSum_blk (A : ℕ) (hA : 1 ≤ A) (x : 𝕋) (hx : gPos A x ≠ ∞) :
    HasSum (fun k => blk A k x) (gFun A x) := by
  obtain ⟨hs, htr⟩ := gPos_toReal_eq A x hx
  have h := hs.hasSum.sub (summable_floorC A hA).hasSum
  simp only [add_sub_cancel_right] at h
  unfold gFun
  rw [htr]
  exact h

/-! ### Main statements -/

lemma ae_gPos_ne_top (A : ℕ) (hA : 1 ≤ A) : ∀ᵐ x ∂μ𝕋, gPos A x ≠ ∞ :=
  (ae_lt_top' (measurable_gPos A).aemeasurable (lintegral_gPos_ne_top A hA)).mono
    fun _ hx => hx.ne

lemma tendsto_partialSum_gFun (A : ℕ) (hA : 1 ≤ A) (x : 𝕋) (hx : gPos A x ≠ ∞) :
    Tendsto (fun K => ∑ k ∈ range K, blk A k x) atTop (𝓝 (gFun A x)) :=
  (hasSum_blk A hA x hx).tendsto_sum_nat

lemma memLp_gFun (A : ℕ) (hA : 1 ≤ A) : MemLp (fun x => (gFun A x : ℂ)) 2 μ𝕋 := by
  refine MemLp.ofReal ?_
  show eLpNorm (gFun A) 2 μ𝕋 < ∞
  have hlim : ∀ᵐ x ∂μ𝕋, Tendsto (fun K => ∑ k ∈ range K, blk A k x) atTop (𝓝 (gFun A x)) :=
    (ae_gPos_ne_top A hA).mono fun x hx => tendsto_partialSum_gFun A hA x hx
  have hmeas : ∀ K, AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk A k x) μ𝕋 := fun K =>
    (Finset.measurable_sum _ fun k _ => measurable_blk A k).aestronglyMeasurable
  refine lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _
    (measurable_gFun A).aestronglyMeasurable hlim) ?_
  refine lt_of_le_of_lt (liminf_le_of_frequently_le'
    (Frequently.of_forall fun K => eLpNorm_partialSum_le A hA K)) ?_
  exact ENNReal.one_lt_top

lemma fourierCoeff_blk_eq_zero_of_ne (A k k' : ℕ) (r : ℤ) (hne : k ≠ k')
    (h : fourierCoeff (fun x => (blk A k x : ℂ)) r ≠ 0) :
    fourierCoeff (fun x => (blk A k' x : ℂ)) r = 0 := by
  rw [fourierCoeff_blk] at h ⊢
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Finset.Icc 1 (blockLen A k),
      fourierCoeff (fun x => (atom A k q x : ℂ)) r ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (by rw [Finset.sum_eq_zero hc, mul_zero])
  rw [Finset.sum_eq_zero fun q' hq' => ?_, mul_zero]
  exact (fourierCoeff_atom_disjoint A k q k' q' r hq hq'
    (fun he => hne (congrArg Prod.fst he))).resolve_left hq0

lemma tendsto_fourierCoeff_partialSum (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    Tendsto (fun K => ∑ k ∈ range K, fourierCoeff (fun x => (blk A k x : ℂ)) r) atTop
      (𝓝 (fourierCoeff (fun x => (gFun A x : ℂ)) r)) := by
  have hS : ∀ K, Measurable (fun x => ∑ k ∈ range K, blk A k x) := fun K =>
    Finset.measurable_sum _ fun k _ => measurable_blk A k
  have heq : ∀ K, ∑ k ∈ range K, fourierCoeff (fun x => (blk A k x : ℂ)) r =
      ∫ x, fourier (-r) x • (((∑ k ∈ range K, blk A k x : ℝ)) : ℂ) ∂μ𝕋 := by
    intro K
    have h := congrFun (fourierCoeff.sum (range K) (fun k x => (blk A k x : ℂ))
      (fun k _ => (integrable_blk A k).ofReal)) r
    rw [Finset.sum_apply] at h
    rw [← h, fourierCoeff]
    congr 1
    ext x
    simp only [Finset.sum_apply, Complex.ofReal_sum]
  refine (tendsto_congr heq).mpr ?_
  rw [fourierCoeff]
  have hG : Integrable (fun x => (gPos A x).toReal + ∑' k, floorC A k) μ𝕋 :=
    (integrable_toReal_of_lintegral_ne_top (measurable_gPos A).aemeasurable
      (lintegral_gPos_ne_top A hA)).add (integrable_const _)
  refine tendsto_integral_of_dominated_convergence
    (fun x => (gPos A x).toReal + ∑' k, floorC A k) ?_ hG ?_ ?_
  · intro K
    exact ((map_continuous (fourier (-r))).measurable.smul
      (Complex.measurable_ofReal.comp (hS K))).aestronglyMeasurable
  · intro K
    filter_upwards [ae_gPos_ne_top A hA] with x hx
    obtain ⟨hs, htr⟩ := gPos_toReal_eq A x hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
      htr]
    have h1 : |∑ k ∈ range K, blk A k x| ≤
        ∑ k ∈ range K, (blk A k x + floorC A k) + ∑ k ∈ range K, floorC A k := by
      rw [← Finset.sum_add_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      have h1 := blk_floor A k x
      have h2 := floorC_nonneg A k
      rw [abs_le]
      constructor <;> linarith
    have h2 : ∑ k ∈ range K, (blk A k x + floorC A k) ≤ ∑' k, (blk A k x + floorC A k) :=
      hs.sum_le_tsum _ fun k _ => by linarith [blk_floor A k x]
    have h3 : ∑ k ∈ range K, floorC A k ≤ ∑' k, floorC A k :=
      (summable_floorC A hA).sum_le_tsum _ fun k _ => floorC_nonneg A k
    linarith
  · filter_upwards [ae_gPos_ne_top A hA] with x hx
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_partialSum_gFun A hA x hx)).const_smul (fourier (-r) x)

lemma hasSum_fourierCoeff_gFun_aux (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    HasSum (fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r)
      (fourierCoeff (fun x => (gFun A x : ℂ)) r) := by
  obtain ⟨a, ha⟩ : ∃ a, HasSum (fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r) a := by
    by_cases h : ∃ k0, fourierCoeff (fun x => (blk A k0 x : ℂ)) r ≠ 0
    · obtain ⟨k0, hk0⟩ := h
      exact ⟨_, hasSum_single k0 fun k hk =>
        fourierCoeff_blk_eq_zero_of_ne A k0 k r (Ne.symm hk) hk0⟩
    · push Not at h
      exact ⟨0, by simp [h]⟩
  have := tendsto_nhds_unique ha.tendsto_sum_nat (tendsto_fourierCoeff_partialSum A hA r)
  rwa [← this]

lemma integral_gFun (A : ℕ) (hA : 1 ≤ A) : ∫ x, (gFun A x : ℂ) ∂μ𝕋 = 0 := by
  have h := hasSum_fourierCoeff_gFun_aux A hA 0
  simp only [fourierCoeff_blk_zero] at h
  have h0 := h.unique hasSum_zero
  rw [fourierCoeff] at h0
  simp only [neg_zero, fourier_zero, one_smul] at h0
  exact h0

lemma hasSum_fourierCoeff_gFun (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    HasSum (fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r)
      (fourierCoeff (fun x => (gFun A x : ℂ)) r) :=
  hasSum_fourierCoeff_gFun_aux A hA r

end Asm
end Erdos996
