import ErdosLean.Erdos996.Parts.Asm.Params
import ErdosLean.Erdos996.Parts.Asm.SpikeMeasure
import ErdosLean.Erdos996.Parts.SpikeFourierSupport

/-!
# Assembly sub-lemma 6 (Atoms): Fourier decomposition of the blocks into atoms

Blueprint §7. Ho Lemma 3.1 proof and (4.8): the atom `φ_{d_k}(2^{U_k+qD_k} ·)` has Fourier
support in the valuation band `[U_k + q D_k, U_k + q D_k + d_k)`; these bands are pairwise
disjoint over all `(k, q)` with `1 ≤ q ≤ L_k`, and every atom has mean zero.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-! ### Auxiliary lemmas (self-contained; they only use fully proved results of
`Parts/SpikeFourierSupport.lean`). -/

lemma alt_shift_mono (A : ℕ) : Monotone (shift A) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  show shift A n ≤ shift A n + blockLen A n * spacing A n + depth A n
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- Bands of different stages are separated. -/
lemma alt_band_sep (A k k' q q' : ℕ) (hk : k < k') (hq : q ≤ blockLen A k) :
    shift A k + q * spacing A k + depth A k ≤ shift A k' + q' * spacing A k' := by
  have h1 : shift A (k + 1) ≤ shift A k' := alt_shift_mono A (by omega)
  have h2 : shift A (k + 1) = shift A k + blockLen A k * spacing A k + depth A k := rfl
  have h3 : q * spacing A k ≤ blockLen A k * spacing A k := Nat.mul_le_mul_right _ hq
  generalize q * spacing A k = a at *
  generalize blockLen A k * spacing A k = b at *
  generalize q' * spacing A k' = c at *
  omega

/-- Bands of the same stage are separated. -/
lemma alt_band_sep_same (A k q q' : ℕ) (hq : q < q') :
    shift A k + q * spacing A k + depth A k ≤ shift A k + q' * spacing A k := by
  have h1 : (q + 1) * spacing A k ≤ q' * spacing A k := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * spacing A k = q * spacing A k + (depth A k + 2) := by
    rw [add_mul, one_mul]; rfl
  generalize q * spacing A k = a at *
  generalize q' * spacing A k = c at *
  omega

lemma alt_integrable_spike (d : ℕ) : Integrable (fun y : 𝕋 => (spike d y : ℂ)) μ𝕋 := by
  have h : Integrable (spike d) μ𝕋 := by
    unfold spike
    exact (((integrable_const (1 : ℝ)).indicator (Erdos996.measurableSet_spikeSet d)).sub
      (integrable_const _)).div_const _
  exact h.ofReal

lemma alt_integrable_atom (A k q : ℕ) : Integrable (fun x : 𝕋 => (atom A k q x : ℂ)) μ𝕋 := by
  have hn : ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) ≠ 0 := by positivity
  have hmp : MeasurePreserving (fun x : 𝕋 => ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) • x)
      μ𝕋 μ𝕋 := Measure.measurePreserving_zsmul μ𝕋 hn
  have e : (fun x : 𝕋 => (atom A k q x : ℂ)) = (fun y : 𝕋 => (spike (depth A k) y : ℂ)) ∘
      (fun x : 𝕋 => ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) • x) := by
    funext x
    simp only [Function.comp, atom, natCast_zsmul]
  rw [e]
  exact Integrable.comp_measurable (by rw [hmp.map_eq]; exact alt_integrable_spike _)
    hmp.measurable

lemma alt_fourierCoeff_spike_zero (d : ℕ) :
    fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) 0 = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (fun x : 𝕋 => (spike 0 x : ℂ)) = fun _ => 0 := by
      funext x; simp [spike]
    rw [this]; simp [fourierCoeff]
  have hb0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hpt : ∀ x ∈ Set.uIoc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d),
      fourier (-(0 : ℤ)) (x : 𝕋) • (spike d (x : 𝕋) : ℂ) =
        (1 / ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ)) x -
          ((((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ) /
              ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hmem := mem_spikeSet_iff d hd x hx
    rw [neg_zero, fourier_zero, one_smul]
    unfold spike
    by_cases hxI : x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)
    · rw [Set.indicator_of_mem (hmem.mpr hxI), Set.indicator_of_mem hxI, Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxI (hmem.mp h)), Set.indicator_of_notMem hxI]
      push_cast; ring
  have hcont : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have hle : (2 : ℝ)⁻¹ ^ d - 1 ≤ (2 : ℝ)⁻¹ ^ d := by linarith
  have hind : IntervalIntegrable
      ((Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ))) volume
      ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hcont.intervalIntegrable _ _)).indicator measurableSet_Ico)
  have hsub : Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) ⊆ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    fun y hy => ⟨by linarith [hy.1, hb1], hy.2.le⟩
  have hI1 : ∫ x in ((2 : ℝ)⁻¹ ^ d - 1)..((2 : ℝ)⁻¹ ^ d),
      (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ)) x =
      ∫ x in (0 : ℝ)..((2 : ℝ)⁻¹ ^ d), (1 : ℂ) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hb0.le,
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsub,
      integral_Ico_eq_integral_Ioc]
  rw [fourierCoeff_eq_intervalIntegral _ _ ((2 : ℝ)⁻¹ ^ d - 1), sub_add_cancel,
    intervalIntegral.integral_congr_ae (ae_of_all _ hpt),
    intervalIntegral.integral_sub (hind.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hI1, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, sub_sub_cancel, one_div, one_smul, inv_one]
  rw [Complex.real_smul]
  push_cast
  ring

/-! ### Main statements -/

lemma blk_eq_sum_atom (A k : ℕ) (x : 𝕋) :
    blk A k x = Real.sqrt (lam A k / blockLen A k) *
      ∑ q ∈ Finset.Icc 1 (blockLen A k), atom A k q x := by
  rfl

lemma fourierCoeff_blk (A k : ℕ) (r : ℤ) :
    fourierCoeff (fun x => (blk A k x : ℂ)) r =
      (Real.sqrt (lam A k / blockLen A k) : ℂ) *
        ∑ q ∈ Finset.Icc 1 (blockLen A k), fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  have hfun : (fun x => (blk A k x : ℂ)) = fun x => (Real.sqrt (lam A k / blockLen A k) : ℂ) *
      (∑ q ∈ Finset.Icc 1 (blockLen A k), fun x : 𝕋 => (atom A k q x : ℂ)) x := by
    funext x
    rw [blk_eq_sum_atom, Finset.sum_apply]
    push_cast
    rfl
  rw [hfun, fourierCoeff.const_mul,
    fourierCoeff.sum _ _ (fun q _ => alt_integrable_atom A k q), Finset.sum_apply]

lemma fourierCoeff_atom_zero (A k q : ℕ) : fourierCoeff (fun x => (atom A k q x : ℂ)) 0 = 0 := by
  have hmeas : AEStronglyMeasurable (fun y : 𝕋 => (spike (depth A k) y : ℂ)) μ𝕋 :=
    (Complex.measurable_ofReal.comp (Erdos996.measurable_spike _)).aestronglyMeasurable
  have h := fourierCoeff_nsmul_comp_mul (2 ^ (shift A k + q * spacing A k)) (by positivity)
    (fun y : 𝕋 => (spike (depth A k) y : ℂ)) hmeas 0
  rw [mul_zero] at h
  exact h.trans (alt_fourierCoeff_spike_zero _)

/-- Distinct atoms have disjoint Fourier supports. -/
lemma fourierCoeff_atom_disjoint (A k q k' q' : ℕ) (r : ℤ)
    (hq : q ∈ Finset.Icc 1 (blockLen A k)) (hq' : q' ∈ Finset.Icc 1 (blockLen A k'))
    (hne : (k, q) ≠ (k', q')) :
    fourierCoeff (fun x => (atom A k q x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (atom A k' q' x : ℂ)) r = 0 := by
  by_cases hr : r = 0
  · subst hr; left; exact fourierCoeff_atom_zero A k q
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have e1 : (2 : ℤ) ^ (shift A k + q * spacing A k) ∣ r ∧
      ¬ (2 : ℤ) ^ (shift A k + q * spacing A k + depth A k) ∣ r := by
    by_contra h
    exact h1 (fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  have e2 : (2 : ℤ) ^ (shift A k' + q' * spacing A k') ∣ r ∧
      ¬ (2 : ℤ) ^ (shift A k' + q' * spacing A k' + depth A k') ∣ r := by
    by_contra h
    exact h2 (fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  rw [Finset.mem_Icc] at hq hq'
  have sep : shift A k + q * spacing A k + depth A k ≤ shift A k' + q' * spacing A k' ∨
      shift A k' + q' * spacing A k' + depth A k' ≤ shift A k + q * spacing A k := by
    rcases lt_trichotomy k k' with hk | rfl | hk
    · exact Or.inl (alt_band_sep A k k' q q' hk hq.2)
    · have hqq : q ≠ q' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hqq with h | h
      · exact Or.inl (alt_band_sep_same A k q q' h)
      · exact Or.inr (alt_band_sep_same A k q' q h)
    · exact Or.inr (alt_band_sep A k' k q' q hk hq'.2)
  rcases sep with h | h
  · exact e1.2 (dvd_trans (pow_dvd_pow 2 h) e2.1)
  · exact e2.2 (dvd_trans (pow_dvd_pow 2 h) e1.1)

end Asm
end Erdos996
