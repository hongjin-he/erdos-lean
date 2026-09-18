import ErdosLean.Erdos996.Defs

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Fourier coefficients of `x ↦ g (n • x)` vanish off the multiples of `n`. -/
lemma fourierCoeff_nsmul_comp_eq_zero (n : ℕ) (hn : 0 < n) (g : 𝕋 → ℂ) (r : ℤ)
    (h : ¬ (n : ℤ) ∣ r) : fourierCoeff (fun x : 𝕋 => g (n • x)) r = 0 := by
  obtain ⟨a, ha_def⟩ : ∃ a : 𝕋, a = (((1 : ℝ) / n : ℝ) : 𝕋) := ⟨_, rfl⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : n • a = 0 := by
    have e : ((n • ((1 : ℝ) / n) : ℝ) : 𝕋) = n • (((1 : ℝ) / n : ℝ) : 𝕋) :=
      AddCircle.coe_nsmul (1 : ℝ)
    rw [ha_def, ← e, nsmul_eq_mul, mul_one_div_cancel hn']
    exact AddCircle.coe_period (1 : ℝ)
  have hI : fourierCoeff (fun x : 𝕋 => g (n • x)) r =
      fourier (-r) a * fourierCoeff (fun x : 𝕋 => g (n • x)) r := by
    unfold fourierCoeff
    rw [← integral_const_mul]
    have hshift := integral_add_right_eq_self (μ := μ𝕋)
      (fun x : 𝕋 => fourier (-r) x • g (n • x)) a
    rw [← hshift]
    congr 1
    funext x
    have hf : fourier (-r) (x + a) = fourier (-r) x * fourier (-r) a := by
      rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add]
      rfl
    simp only [smul_add, ha, add_zero, smul_eq_mul, hf]
    ring
  have hne : fourier (-r) a ≠ 1 := by
    rw [ha_def, fourier_coe_apply]
    intro he
    rw [Complex.exp_eq_one_iff] at he
    obtain ⟨k, hk⟩ := he
    push_cast at hk
    have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : -(r : ℂ) * (1 / (n : ℂ)) = k := by
      apply mul_left_cancel₀ hpi
      linear_combination hk
    have h2 : (r : ℂ) = -(k : ℂ) * n := by
      rw [← h1]; field_simp
    have h3 : r = -k * n := by exact_mod_cast h2
    exact h ⟨-k, by rw [h3]; ring⟩
  have : (1 - fourier (-r) a) * fourierCoeff (fun x : 𝕋 => g (n • x)) r = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · exact h0

/-- Dilation formula: `\widehat{g(n ·)}(n s) = \hat g(s)`. -/
lemma fourierCoeff_nsmul_comp_mul (n : ℕ) (hn : 0 < n) (g : 𝕋 → ℂ)
    (hg : AEStronglyMeasurable g μ𝕋) (s : ℤ) :
    fourierCoeff (fun x : 𝕋 => g (n • x)) ((n : ℤ) * s) = fourierCoeff g s := by
  have hmp : MeasurePreserving (fun x : 𝕋 => (n : ℤ) • x) μ𝕋 μ𝕋 :=
    Measure.measurePreserving_zsmul μ𝕋 (by exact_mod_cast hn.ne')
  have hF : AEStronglyMeasurable (fun y : 𝕋 => fourier (-s) y • g y) μ𝕋 :=
    (map_continuous (fourier (-s))).aestronglyMeasurable.smul hg
  have hpt : ∀ x : 𝕋, fourier (-((n : ℤ) * s)) x • g (n • x) =
      (fun y : 𝕋 => fourier (-s) y • g y) ((n : ℤ) • x) := by
    intro x
    show fourier (-((n : ℤ) * s)) x • g (n • x) = fourier (-s) ((n : ℤ) • x) • g ((n : ℤ) • x)
    have e : n • x = (n : ℤ) • x := (natCast_zsmul x n).symm
    rw [e, fourier_apply, fourier_apply, smul_smul, show -((n : ℤ) * s) = -s * (n : ℤ) by ring]
  rw [fourierCoeff, fourierCoeff]
  calc ∫ t, fourier (-((n : ℤ) * s)) t • g (n • t) ∂μ𝕋
      = ∫ t, (fun y : 𝕋 => fourier (-s) y • g y) ((n : ℤ) • t) ∂μ𝕋 :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ y, fourier (-s) y • g y ∂(Measure.map (fun x : 𝕋 => (n : ℤ) • x) μ𝕋) :=
        (integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF)).symm
    _ = ∫ y, fourier (-s) y • g y ∂μ𝕋 := by rw [hmp.map_eq]

lemma measurableSet_spikeSet (d : ℕ) :
    MeasurableSet (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set 𝕋) := by
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  rw [← Set.Ioo_insert_left hb, Set.image_insert_eq]
  exact ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _
    isOpen_Ioo).measurableSet.insert _

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  unfold spike
  exact ((measurable_one.indicator (measurableSet_spikeSet d)).sub measurable_const).div_const _

lemma mem_spikeSet_iff (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : x ∈ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d)) :
    ((x : 𝕋) ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set 𝕋)) ↔
      x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) := by
  constructor
  · rintro ⟨u, hu, hux⟩
    have hb : (2 : ℝ)⁻¹ ^ d ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have hux' : ((x : ℝ) : 𝕋) = ((u : ℝ) : 𝕋) := hux.symm
    have h0 : ((x - u : ℝ) : 𝕋) = 0 := by
      rw [AddCircle.coe_sub, hux', sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    rw [zsmul_eq_mul, mul_one] at hk
    have hk1 : (k : ℝ) < 1 := by linarith [hx.2, hu.1]
    have hk2 : (-1 : ℝ) < k := by linarith [hx.1, hu.2]
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast hk1
      have : -1 < k := by exact_mod_cast hk2
      omega
    rw [hk0] at hk
    push_cast at hk
    have : x = u := by linarith
    rw [this]; exact hu
  · intro hx'
    exact ⟨x, hx', rfl⟩

/-- For `d ≥ 1`, the spike `φ_d` has vanishing Fourier coefficients at nonzero multiples of `2^d`. -/
lemma fourierCoeff_spike_eq_zero (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (hm : m ≠ 0) :
    fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) ((2 : ℤ) ^ d * m) = 0 := by
  have hb0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  obtain ⟨C, hC_def⟩ : ∃ C : ℂ, C = 2 * π * Complex.I * (((-((2 : ℤ) ^ d * m)) : ℤ) : ℂ) :=
    ⟨_, rfl⟩
  have hC : C ≠ 0 := by
    rw [hC_def]; simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
  have h2 : (2 : ℂ) ^ d * ((2 : ℂ)⁻¹) ^ d = 1 := by rw [← mul_pow]; norm_num
  have hCb : Complex.exp (C * (((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨-m, ?_⟩
    rw [hC_def]; push_cast
    linear_combination (-2 * π * Complex.I * m) * h2
  have hCb1 : Complex.exp (C * (((2 : ℝ)⁻¹ ^ d - 1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨2 ^ d * m - m, ?_⟩
    rw [hC_def]; push_cast
    linear_combination (-2 * π * Complex.I * m) * h2
  have hC0 : Complex.exp (C * ((0 : ℝ) : ℂ)) = 1 := by simp
  have hpt : ∀ x ∈ Set.uIoc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d),
      fourier (-((2 : ℤ) ^ d * m)) (x : 𝕋) • (spike d (x : 𝕋) : ℂ) =
        (1 / ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y)) x -
          ((((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ) /
              ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            Complex.exp (C * x) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hmem := mem_spikeSet_iff d hd x hx
    have hf : fourier (-((2 : ℤ) ^ d * m)) (x : 𝕋) = Complex.exp (C * x) := by
      rw [fourier_coe_apply, hC_def]
      congr 1
      push_cast; ring
    rw [hf]
    unfold spike
    by_cases hxI : x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)
    · rw [Set.indicator_of_mem (hmem.mpr hxI), Set.indicator_of_mem hxI, Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxI (hmem.mp h)), Set.indicator_of_notMem hxI]
      push_cast; ring
  have hcont : Continuous (fun y : ℝ => Complex.exp (C * y)) := by fun_prop
  have hle : (2 : ℝ)⁻¹ ^ d - 1 ≤ (2 : ℝ)⁻¹ ^ d := by linarith
  have hind : IntervalIntegrable
      ((Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y))) volume
      ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hcont.intervalIntegrable _ _)).indicator measurableSet_Ico)
  have hsub : Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) ⊆ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    fun y hy => ⟨by linarith [hy.1, hb1], hy.2.le⟩
  have hI1 : ∫ x in ((2 : ℝ)⁻¹ ^ d - 1)..((2 : ℝ)⁻¹ ^ d),
      (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y)) x =
      ∫ x in (0 : ℝ)..((2 : ℝ)⁻¹ ^ d), Complex.exp (C * x) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hb0.le,
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsub,
      integral_Ico_eq_integral_Ioc]
  rw [fourierCoeff_eq_intervalIntegral _ _ ((2 : ℝ)⁻¹ ^ d - 1), sub_add_cancel,
    intervalIntegral.integral_congr_ae (ae_of_all _ hpt),
    intervalIntegral.integral_sub (hind.const_mul _) ((hcont.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI1,
    integral_exp_mul_complex hC, integral_exp_mul_complex hC, hCb, hCb1, hC0]
  simp

/-- Fourier support of a dilated spike: `\widehat{φ_d(2^v ·)}(r) = 0` unless
`v ≤ val₂(r) ≤ v + d - 1`. -/
lemma fourierCoeff_spike_dilate_eq_zero (d v : ℕ) (r : ℤ) (hr : r ≠ 0)
    (h : ¬ (2 ^ v ∣ r ∧ ¬ 2 ^ (v + d) ∣ r)) :
    fourierCoeff (fun x : 𝕋 => (spike d ((2 ^ v : ℕ) • x) : ℂ)) r = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (fun x : 𝕋 => (spike 0 ((2 ^ v : ℕ) • x) : ℂ)) = fun _ => 0 := by
      funext x; simp [spike]
    rw [this]; simp [fourierCoeff]
  have hn : 0 < 2 ^ v := by positivity
  rw [not_and, not_not] at h
  by_cases hv : (2 : ℤ) ^ v ∣ r
  · obtain ⟨m, rfl⟩ := h hv
    have hm : m ≠ 0 := by rintro rfl; simp at hr
    have hr' : (2 : ℤ) ^ (v + d) * m = ((2 ^ v : ℕ) : ℤ) * ((2 : ℤ) ^ d * m) := by
      push_cast; ring
    have hmeas : AEStronglyMeasurable (fun y : 𝕋 => (spike d y : ℂ)) μ𝕋 :=
      (Complex.measurable_ofReal.comp (measurable_spike d)).aestronglyMeasurable
    rw [hr']
    refine (fourierCoeff_nsmul_comp_mul (2 ^ v) hn (fun y : 𝕋 => (spike d y : ℂ)) hmeas _).trans ?_
    exact fourierCoeff_spike_eq_zero d hd m hm
  · exact fourierCoeff_nsmul_comp_eq_zero (2 ^ v) hn (fun y : 𝕋 => (spike d y : ℂ)) r
      (by push_cast; exact hv)

end Erdos996
