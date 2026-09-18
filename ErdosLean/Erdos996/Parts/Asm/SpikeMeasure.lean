import ErdosLean.Erdos996.Parts.Asm.Construction

/-!
# Assembly sub-lemma 3 (SpikeMeasure): measure-theoretic facts about spikes

Blueprint §4. Ho §2, (2.1) and Lemma 2.1(a): `|[0,2^{-d})| = 2^{-d}`, `∫ φ_d = 0`,
`∫ φ_d² = 1`, and `x ↦ n x` preserves Haar measure.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma measurableSet_spikeSet (d : ℕ) : MeasurableSet (spikeSet d) := by
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  unfold spikeSet
  rw [← Set.Ioo_insert_left hb, Set.image_insert_eq]
  exact ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _
    isOpen_Ioo).measurableSet.insert _

/-- Haar measure on `𝕋` computed on `[0,1)` in `ℝ`. -/
lemma haar_eq_volume_Ico (U : Set 𝕋) (hU : MeasurableSet U) :
    μ𝕋 U = volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → 𝕋) ⁻¹' U)) := by
  have h1 : (volume : Measure 𝕋) = μ𝕋 := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have h2 := AddCircle.add_projection_respects_measure (T := 1) 0 hU
  rw [← h1, h2, zero_add, Set.inter_comm]
  exact measure_congr ((Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm.inter (ae_eq_refl _))

lemma measure_spikeSet (d : ℕ) : μ𝕋 (spikeSet d) = (2⁻¹ : ℝ≥0∞) ^ d := by
  have ht1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [haar_eq_volume_Ico _ (measurableSet_spikeSet d)]
  have hset : Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → 𝕋) ⁻¹' spikeSet d) =
      Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) := by
    ext x
    constructor
    · rintro ⟨hx01, ⟨u, hu, hux⟩⟩
      have hx' : x ∈ Set.Ico (0 : ℝ) (0 + 1) := by rw [zero_add]; exact hx01
      have hu' : u ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hu.1, by linarith [hu.2]⟩
      have e1 := AddCircle.equivIco_coe_of_mem hx'
      have e2 := AddCircle.equivIco_coe_of_mem hu'
      have hxu : x = u := by
        have : (AddCircle.equivIco 1 0 (x : 𝕋) : ℝ) = (AddCircle.equivIco 1 0 (u : 𝕋) : ℝ) := by
          rw [hux]
        rw [e1, e2] at this
        exact this
      rw [hxu]; exact hu
    · intro hx
      exact ⟨⟨hx.1, lt_of_lt_of_le hx.2 ht1⟩, ⟨x, hx, rfl⟩⟩
  rw [hset, Real.volume_Ico, sub_zero, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma spike_eq (d : ℕ) (x : 𝕋) :
    spike d x = ((spikeSet d).indicator 1 x - (2 : ℝ)⁻¹ ^ d) /
      Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := rfl

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  have : spike d = fun x => ((spikeSet d).indicator 1 x - (2 : ℝ)⁻¹ ^ d) /
      Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := rfl
  rw [this]
  exact ((measurable_one.indicator (measurableSet_spikeSet d)).sub measurable_const).div_const _

lemma abs_spike_le (d : ℕ) (x : 𝕋) : |spike d x| ≤ 2 ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [spike]
  rw [spike_eq]
  set t : ℝ := (2 : ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have hthalf : t ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hct : t ≤ Real.sqrt (t * (1 - t)) := by
    have := Real.abs_le_sqrt (x := t) (y := t * (1 - t)) (by nlinarith)
    rwa [abs_of_pos ht0] at this
  have hc : 0 < Real.sqrt (t * (1 - t)) := lt_of_lt_of_le ht0 hct
  have hnum : |(spikeSet d).indicator 1 x - t| ≤ 1 := by
    by_cases h : x ∈ spikeSet d
    · rw [Set.indicator_of_mem h]
      simp only [Pi.one_apply]
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem h]
      rw [abs_le]; constructor <;> linarith
  rw [abs_div, abs_of_pos hc]
  calc |(spikeSet d).indicator 1 x - t| / Real.sqrt (t * (1 - t))
      ≤ 1 / Real.sqrt (t * (1 - t)) := div_le_div_of_nonneg_right hnum hc.le
    _ ≤ 1 / t := one_div_le_one_div_of_le ht0 hct
    _ = 2 ^ d := by rw [ht, one_div, inv_pow, inv_inv]

lemma measurableSet_hitSet (d v : ℕ) : MeasurableSet (hitSet d v) :=
  (continuous_nsmul (2 ^ v)).measurable (measurableSet_spikeSet d)

lemma measurePreserving_nsmul (n : ℕ) (hn : n ≠ 0) :
    MeasurePreserving (fun x : 𝕋 => n • x) μ𝕋 μ𝕋 := by
  have hmp : MeasurePreserving (fun x : 𝕋 => (n : ℤ) • x) μ𝕋 μ𝕋 :=
    Measure.measurePreserving_zsmul μ𝕋 (by exact_mod_cast hn)
  have e : (fun x : 𝕋 => n • x) = fun x => (n : ℤ) • x := by
    funext x; exact (natCast_zsmul x n).symm
  rw [e]; exact hmp

lemma measure_hitSet (d v : ℕ) : μ𝕋 (hitSet d v) = (2⁻¹ : ℝ≥0∞) ^ d := by
  have hmp := measurePreserving_nsmul (2 ^ v) (by positivity)
  have : hitSet d v = (fun x : 𝕋 => (2 ^ v : ℕ) • x) ⁻¹' spikeSet d := rfl
  rw [this, hmp.measure_preimage (measurableSet_spikeSet d).nullMeasurableSet]
  exact measure_spikeSet d

lemma integral_nsmul_comp (n : ℕ) (hn : n ≠ 0) (g : 𝕋 → ℝ) (hg : Measurable g) :
    ∫ x, g (n • x) ∂μ𝕋 = ∫ x, g x ∂μ𝕋 := by
  have hmp := measurePreserving_nsmul n hn
  rw [← integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable), hmp.map_eq]

lemma integral_indicator_spikeSet (d : ℕ) :
    ∫ x, (spikeSet d).indicator (1 : 𝕋 → ℝ) x ∂μ𝕋 = (2 : ℝ)⁻¹ ^ d := by
  rw [integral_indicator_one (measurableSet_spikeSet d), measureReal_def, measure_spikeSet]
  simp

lemma integrable_indicator_spikeSet (d : ℕ) :
    Integrable (fun x => (spikeSet d).indicator (1 : 𝕋 → ℝ) x) μ𝕋 :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_spikeSet d)

lemma integral_spike_nsmul (d n : ℕ) (hn : n ≠ 0) : ∫ x, spike d (n • x) ∂μ𝕋 = 0 := by
  rw [integral_nsmul_comp n hn _ (measurable_spike d)]
  simp only [spike_eq]
  rw [integral_div, integral_sub (integrable_indicator_spikeSet d) (integrable_const _),
    integral_indicator_spikeSet, integral_const]
  simp

lemma integral_spike_nsmul_sq (d n : ℕ) (hd : 1 ≤ d) (hn : n ≠ 0) :
    ∫ x, spike d (n • x) ^ 2 ∂μ𝕋 = 1 := by
  rw [integral_nsmul_comp n hn (fun y => spike d y ^ 2) ((measurable_spike d).pow_const 2)]
  set t : ℝ := (2 : ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have hthalf : t ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpos : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have hpt : ∀ x : 𝕋, spike d x ^ 2 =
      ((spikeSet d).indicator (1 : 𝕋 → ℝ) x * (1 - 2 * t) + t ^ 2) / (t * (1 - t)) := by
    intro x
    rw [spike_eq, div_pow, Real.sq_sqrt hpos.le]
    congr 1
    by_cases h : x ∈ spikeSet d
    · rw [Set.indicator_of_mem h]; simp only [Pi.one_apply]; ring
    · rw [Set.indicator_of_notMem h]; ring
  simp only [hpt]
  rw [integral_div, integral_add ((integrable_indicator_spikeSet d).mul_const _)
    (integrable_const _), integral_mul_const, integral_indicator_spikeSet, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [div_eq_one_iff_eq hpos.ne']
  ring

end Asm
end Erdos996
