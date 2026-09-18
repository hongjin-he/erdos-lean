import ErdosLean.Erdos996.Defs

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

namespace SpikeTailAux

lemma mem_spikeSet_iff (d : ℕ) (z : 𝕋) :
    z ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set 𝕋) ↔
      ((AddCircle.equivIco 1 0 z : ℝ)) < (2 : ℝ)⁻¹ ^ d := by
  have hp1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Ico (0:ℝ) (0 + 1) := ⟨hx.1, by linarith [hx.2]⟩
    rw [AddCircle.equivIco_coe_of_mem hx']
    exact hx.2
  · intro h
    refine ⟨(AddCircle.equivIco 1 0 z : ℝ), ⟨(AddCircle.equivIco 1 0 z).2.1, h⟩, ?_⟩
    exact AddCircle.coe_equivIco

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  have hA : MeasurableSet (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set 𝕋) := by
    have : (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set 𝕋) =
        (fun z : 𝕋 => (AddCircle.equivIco 1 0 z : ℝ)) ⁻¹' Set.Iio ((2 : ℝ)⁻¹ ^ d) := by
      ext z; exact mem_spikeSet_iff d z
    rw [this]
    exact (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable)
      measurableSet_Iio
  exact ((measurable_one.indicator hA).sub measurable_const).div_const _

lemma fourier_add_arg (n : ℤ) (x y : 𝕋) : fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma fc_eq_zero_of_not_dvd (d Q : ℕ) (hQ : 0 < Q) (r : ℤ) (h : ¬ (Q : ℤ) ∣ r) :
    fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r = 0 := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hQne : (Q:ℝ) ≠ 0 := hQr.ne'
  set t : 𝕋 := ((1 / (Q : ℝ) : ℝ) : 𝕋) with ht
  have hQt : Q • t = 0 := by
    rw [ht, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div_cancel hQne]
    exact AddCircle.coe_period (p := (1:ℝ))
  have key : fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r =
      fourier (-r) t * fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r := by
    unfold fourierCoeff
    have e := integral_add_right_eq_self (μ := (haarAddCircle : Measure 𝕋))
      (fun x => fourier (-r) x • (spike d (Q • x) : ℂ)) t
    conv_lhs => rw [← e]
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [smul_eq_mul, nsmul_add, hQt, add_zero, fourier_add_arg]
    ring
  have hne : fourier (-r) t ≠ 1 := by
    intro h1
    have h2 : toCircle ((-r) • t) = 1 := by
      rw [fourier_apply] at h1
      exact Circle.ext (h1.trans Circle.coe_one.symm)
    have h3 : (-r) • t = 0 :=
      AddCircle.injective_toCircle one_ne_zero (h2.trans AddCircle.toCircle_zero.symm)
    rw [ht, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at h3
    obtain ⟨m, hm⟩ := h3
    simp only [zsmul_eq_mul, mul_one, Int.cast_neg, one_div] at hm
    apply h
    refine ⟨-m, ?_⟩
    have hmQ : (m:ℝ) * Q = -r := by
      rw [hm, mul_assoc, inv_mul_cancel₀ hQne, mul_one]
    have : (r:ℝ) = (Q:ℝ) * ((-m : ℤ) : ℝ) := by
      push_cast
      linear_combination hmQ
    exact_mod_cast this
  have h3 : (fourier (-r) t - 1) * fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hne
  · exact h4

lemma fc_dilate (d Q : ℕ) (hQ : 0 < Q) (s : ℤ) :
    fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) ((Q : ℤ) * s) =
      fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s := by
  have hQz : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmp : MeasurePreserving (fun x : 𝕋 => (Q : ℤ) • x) (haarAddCircle : Measure 𝕋)
      haarAddCircle := Measure.measurePreserving_zsmul _ hQz
  have hg : AEStronglyMeasurable (fun y : 𝕋 => fourier (-s) y • (spike d y : ℂ))
      haarAddCircle :=
    (map_continuous (fourier (-s))).aestronglyMeasurable.smul
      (Complex.measurable_ofReal.comp (measurable_spike d)).aestronglyMeasurable
  have e := integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg)
  rw [hmp.map_eq] at e
  unfold fourierCoeff
  rw [e]
  congr 1
  funext x
  have hx : ((Q:ℤ) • x) = Q • x := natCast_zsmul x Q
  show _ = fourier (-s) ((Q:ℤ) • x) • (spike d ((Q:ℤ) • x) : ℂ)
  rw [fourier_apply, fourier_apply, smul_smul, hx, show -((Q:ℤ) * s) = -s * (Q:ℤ) by ring]

lemma fc_spike (d : ℕ) (hd : 1 ≤ d) (s : ℤ) (hs : s ≠ 0) :
    fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s =
      (((Real.sqrt ((2:ℝ)⁻¹ ^ d * (1 - (2:ℝ)⁻¹ ^ d)))⁻¹ : ℝ) : ℂ) *
        ((Complex.exp (-(2 * π * Complex.I * s) * (((2:ℝ)⁻¹ ^ d : ℝ) : ℂ)) - 1) /
          -(2 * π * Complex.I * s)) := by
  have hp0 : (0:ℝ) < (2:ℝ)⁻¹ ^ d := by positivity
  have hp1 : (2:ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hc0 : -(2 * π * Complex.I * s) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hs]
  have hE : ∀ x : ℝ, fourier (-s) (x : 𝕋) = Complex.exp (-(2 * π * Complex.I * s) * x) := by
    intro x; rw [fourier_coe_apply]; congr 1; push_cast; ring
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, one_div_one, one_smul,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hpt : Set.EqOn (fun x : ℝ => fourier (-s) (x : 𝕋) • (spike d (x : 𝕋) : ℂ))
      (fun x : ℝ => (((Real.sqrt ((2:ℝ)⁻¹ ^ d * (1 - (2:ℝ)⁻¹ ^ d)))⁻¹ : ℝ) : ℂ) *
        (Set.indicator (Set.Iio ((2:ℝ)⁻¹ ^ d))
            (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * s) * x)) x
          - (((2:ℝ)⁻¹ ^ d : ℝ) : ℂ) * Complex.exp (-(2 * π * Complex.I * s) * x)))
      (Set.Ioo 0 1) := by
    intro x hx
    have hx' : x ∈ Set.Ico (0:ℝ) (0 + 1) := ⟨hx.1.le, by linarith [hx.2]⟩
    have hmem := mem_spikeSet_iff d (x : 𝕋)
    rw [AddCircle.equivIco_coe_of_mem hx'] at hmem
    simp only [hE, spike, smul_eq_mul]
    by_cases hxp : x < (2:ℝ)⁻¹ ^ d
    · rw [Set.indicator_of_mem (hmem.mpr hxp),
        Set.indicator_of_mem (show x ∈ Set.Iio ((2:ℝ)⁻¹ ^ d) from hxp)]
      simp only [Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxp (hmem.mp h)),
        Set.indicator_of_notMem (show x ∉ Set.Iio ((2:ℝ)⁻¹ ^ d) from hxp)]
      push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  have hEint : IntegrableOn (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * s) * x))
      (Set.Ioo 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioo_subset_Icc_self
  rw [integral_sub (Integrable.indicator hEint measurableSet_Iio) (Integrable.const_mul hEint _),
    setIntegral_indicator measurableSet_Iio, integral_const_mul, Set.Ioo_inter_Iio,
    min_eq_right hp1.le]
  have e1 : ∫ x in Set.Ioo (0:ℝ) ((2:ℝ)⁻¹ ^ d), Complex.exp (-(2 * π * Complex.I * s) * x) =
      ∫ x in (0:ℝ)..(2:ℝ)⁻¹ ^ d, Complex.exp (-(2 * π * Complex.I * s) * x) := by
    rw [intervalIntegral.integral_of_le hp0.le, integral_Ioc_eq_integral_Ioo]
  have e2 : ∫ x in Set.Ioo (0:ℝ) 1, Complex.exp (-(2 * π * Complex.I * s) * x) =
      ∫ x in (0:ℝ)..1, Complex.exp (-(2 * π * Complex.I * s) * x) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [e1, e2, integral_exp_mul_complex hc0, integral_exp_mul_complex hc0]
  have h1 : Complex.exp (-(2 * π * Complex.I * s) * ((1:ℝ) : ℂ)) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨-s, by push_cast; ring⟩
  rw [h1]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div, sub_zero]

lemma norm_fc_spike_sq_le (d : ℕ) (hd : 1 ≤ d) (s : ℤ) (hs : s ≠ 0) :
    ‖fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s‖ ^ 2 ≤ 2 * (2:ℝ)⁻¹ ^ d ∧
    ‖fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s‖ ^ 2 ≤ 1 / ((2:ℝ)⁻¹ ^ d * (s:ℝ) ^ 2) := by
  rw [fc_spike d hd s hs]
  have hp0 : (0:ℝ) < (2:ℝ)⁻¹ ^ d := by positivity
  have hp2 : (2:ℝ)⁻¹ ^ d ≤ 2⁻¹ := by
    calc (2:ℝ)⁻¹ ^ d ≤ (2:ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
      _ = 2⁻¹ := pow_one _
  set p : ℝ := (2:ℝ)⁻¹ ^ d with hp
  set σ : ℝ := Real.sqrt (p * (1 - p)) with hσ
  have hσ2 : σ ^ 2 = p * (1 - p) := Real.sq_sqrt (by nlinarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by nlinarith)
  have hsR : (s:ℝ) ≠ 0 := by exact_mod_cast hs
  have hsabs : 0 < |(s:ℝ)| := abs_pos.mpr hsR
  have hs2 : 0 < (s:ℝ) ^ 2 := by
    have := pow_pos hsabs 2
    rwa [sq_abs] at this
  set θ : ℝ := -(2 * π * s * p) with hθ
  have hcp : -(2 * π * Complex.I * s) * (p : ℂ) = Complex.I * θ := by
    rw [hθ]; push_cast; ring
  rw [hcp]
  set A : ℂ := Complex.exp (Complex.I * θ) - 1 with hA
  have hden : 0 < 2 * π * |(s:ℝ)| := mul_pos (by positivity) hsabs
  have hcn : ‖-(2 * π * Complex.I * (s:ℂ))‖ = 2 * π * |(s:ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  have hnorm : ‖((σ⁻¹ : ℝ) : ℂ) * (A / -(2 * π * Complex.I * s))‖ =
      σ⁻¹ * (‖A‖ / (2 * π * |(s:ℝ)|)) := by
    rw [norm_mul, norm_div, hcn, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hσ0.le)]
  rw [hnorm]
  have hA1 : ‖A‖ ≤ |θ| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    rwa [Real.norm_eq_abs] at this
  have hA2 : ‖A‖ ≤ 2 := by
    calc ‖A‖ ≤ ‖Complex.exp (Complex.I * θ)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hθabs : |θ| = 2 * π * |(s:ℝ)| * p := by
    rw [hθ, abs_neg, show 2 * π * (s:ℝ) * p = (2 * π * p) * s by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * π * p)]
    ring
  set B := ‖A‖ / (2 * π * |(s:ℝ)|) with hB
  have hB0 : 0 ≤ B := div_nonneg (norm_nonneg _) hden.le
  have hB1 : B ≤ p := by
    rw [hB, div_le_iff₀ hden]; linarith
  have hB2 : B ≤ 1 / (π * |(s:ℝ)|) := by
    rw [hB, div_le_div_iff₀ hden (by positivity)]; nlinarith [hA2]
  have hq : 0 < p * (1 - p) := by nlinarith
  constructor
  · rw [mul_pow, inv_pow, hσ2, inv_mul_le_iff₀ hq]
    have : B ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hB0 hB1 2
    nlinarith [mul_nonneg (sq_nonneg p) (by linarith : (0:ℝ) ≤ 1 - 2 * p)]
  · rw [mul_pow, inv_pow, hσ2, inv_mul_le_iff₀ hq]
    have h9 : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hπ : 1 ≤ π ^ 2 * (1 - p) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h9) (by linarith : (0:ℝ) ≤ 1 - p)]
    calc B ^ 2 ≤ (1 / (π * |(s:ℝ)|)) ^ 2 := pow_le_pow_left₀ hB0 hB2 2
      _ = 1 / (π ^ 2 * (s:ℝ) ^ 2) := by rw [div_pow, one_pow, mul_pow, sq_abs]
      _ ≤ (1 - p) / (s:ℝ) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) hs2]
          nlinarith [mul_nonneg hs2.le (sub_nonneg.mpr hπ)]
      _ = p * (1 - p) * (1 / (p * (s:ℝ) ^ 2)) := by
          field_simp

lemma tail_nat (K : ℝ) (hK : 0 < K) (L : ℕ) :
    ∑ n ∈ Finset.range L, (if K < (n:ℝ) then 1 / (n:ℝ) ^ 2 else 0) ≤ 2 / K := by
  have e : ∑ n ∈ Finset.range L, (if K < (n:ℝ) then 1 / (n:ℝ) ^ 2 else 0) =
      ∑ n ∈ Finset.Ioo ⌊K⌋₊ L, ((n:ℝ) ^ 2)⁻¹ := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
      rw [Nat.floor_lt hK.le]
      tauto
    · intro n _; rw [one_div]
  rw [e]
  calc _ ≤ 2 / ((⌊K⌋₊ : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ ≤ 2 / K := div_le_div_of_nonneg_left (by norm_num) hK (Nat.lt_floor_add_one K).le

lemma tail_int (K : ℝ) (hK : 0 < K) :
    Summable (fun s : ℤ => if K < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) ∧
    ∑' s : ℤ, (if K < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) ≤ 4 / K := by
  set f : ℤ → ℝ := fun s => if K < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0 with hf
  set g : ℕ → ℝ := fun n => if K < (n:ℝ) then 1 / (n:ℝ) ^ 2 else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hgL : ∀ L, ∑ n ∈ Finset.range L, g n ≤ 2 / K := tail_nat K hK
  have hgL' : ∀ L, ∑ n ∈ Finset.range L, g (n + 1) ≤ 2 / K := by
    intro L
    have := hgL (L + 1)
    rw [Finset.sum_range_succ'] at this
    linarith [hg0 0]
  have hgs : Summable g := summable_of_sum_range_le hg0 hgL
  have hgs' : Summable (fun n => g (n + 1)) := summable_of_sum_range_le (fun n => hg0 _) hgL'
  have h1 : (fun n : ℕ => f n) = fun n => g n := by
    funext n; simp only [hf, hg, Int.cast_natCast, Nat.abs_cast]
  have h2 : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun n => g (n + 1) := by
    funext n
    simp only [hf, hg]
    push_cast
    rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ) + 1), neg_sq]
  have hs1 : Summable (fun n : ℕ => f n) := by rw [h1]; exact hgs
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by rw [h2]; exact hgs'
  refine ⟨Summable.of_nat_of_neg_add_one hs1 hs2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hs1 hs2, h1, h2]
  have t1 := Real.tsum_le_of_sum_range_le hg0 hgL
  have t2 := Real.tsum_le_of_sum_range_le (fun n => hg0 (n + 1)) hgL'
  exact le_trans (add_le_add t1 t2) (le_of_eq (by ring))

end SpikeTailAux

open SpikeTailAux in
/-- Fourier tail of one dilated spike: `‖(I - S_N) φ_d(2^v ·)‖₂² ≤ C₁ min(1, 2^{d+v}/N)`. -/
lemma spike_dilate_tail :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (d v N : ℕ), 1 ≤ d → 1 ≤ N →
      ∑' r : {r : ℤ // (N : ℤ) < |r|},
          ‖fourierCoeff (fun x : 𝕋 => (spike d ((2 ^ v : ℕ) • x) : ℂ)) r‖ ^ 2
        ≤ C₁ * min 1 ((2 : ℝ) ^ (d + v) / N) := by
  refine ⟨10, by norm_num, ?_⟩
  intro d v N hd hN
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 2 ^ v := ⟨_, rfl⟩
  rw [← hQ]
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hQz : (Q : ℤ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hQr : (Q : ℝ) = 2 ^ v := by rw [hQ]; push_cast; ring
  have hQr0 : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have e1 : ∑' r : {r : ℤ // (N : ℤ) < |r|},
        ‖fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r‖ ^ 2 =
      ∑' r : ℤ, (if (N:ℤ) < |r| then
        ‖fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r‖ ^ 2 else 0) := by
    have := tsum_subtype {r : ℤ | (N:ℤ) < |r|}
      (fun r => ‖fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r‖ ^ 2)
    simp only [Set.indicator_apply, Set.mem_setOf_eq] at this
    exact this
  have e2 : ∑' r : ℤ, (if (N:ℤ) < |r| then
        ‖fourierCoeff (fun x : 𝕋 => (spike d (Q • x) : ℂ)) r‖ ^ 2 else 0) =
      ∑' s : ℤ, (if (N:ℤ) < |(Q:ℤ) * s| then
        ‖fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s‖ ^ 2 else 0) := by
    rw [← (mul_right_injective₀ hQz).tsum_eq]
    · congr 1
      funext s
      simp only [fc_dilate d Q hQpos]
    · intro r hr
      rw [Function.mem_support] at hr
      by_cases hdiv : (Q:ℤ) ∣ r
      · obtain ⟨s, rfl⟩ := hdiv
        exact ⟨s, rfl⟩
      · exfalso
        apply hr
        simp [fc_eq_zero_of_not_dvd d Q hQpos r hdiv]
  rw [e1, e2]
  have hbd : ∀ s : ℤ, (N:ℤ) < |(Q:ℤ) * s| → s ≠ 0 ∧ (N:ℝ) / Q < |(s:ℝ)| := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [mul_zero, abs_zero] at hs
      omega
    · have h' : (N:ℝ) < |(Q:ℝ) * s| := by exact_mod_cast hs
      rw [abs_mul, abs_of_pos hQr0] at h'
      rw [div_lt_iff₀ hQr0]
      linarith
  set a : ℤ → ℝ := fun s => if (N:ℤ) < |(Q:ℤ) * s| then
        ‖fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s‖ ^ 2 else 0 with ha
  have ha0 : ∀ s, 0 ≤ a s := fun s => by simp only [ha]; split_ifs <;> positivity
  by_cases hX : (2:ℝ) ^ (d + v) ≤ N
  · have hK : 0 < (N:ℝ) / Q := by positivity
    obtain ⟨hsum, htail⟩ := tail_int ((N:ℝ) / Q) hK
    have hab : ∀ s, a s ≤
        (2:ℝ) ^ d * (if (N:ℝ) / Q < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) := by
      intro s
      simp only [ha]
      by_cases h1 : (N:ℤ) < |(Q:ℤ) * s|
      · obtain ⟨hs0, hK'⟩ := hbd s h1
        rw [if_pos h1, if_pos hK']
        refine (norm_fc_spike_sq_le d hd s hs0).2.trans (le_of_eq ?_)
        rw [inv_pow, one_div, mul_inv, inv_inv, one_div]
      · rw [if_neg h1]
        exact mul_nonneg (by positivity) (by split_ifs <;> positivity)
    have hsb := hsum.mul_left ((2:ℝ) ^ d)
    have hsa : Summable a := Summable.of_nonneg_of_le ha0 hab hsb
    calc ∑' s, a s
        ≤ ∑' s : ℤ, (2:ℝ) ^ d * (if (N:ℝ) / Q < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) :=
          Summable.tsum_le_tsum hab hsa hsb
      _ = (2:ℝ) ^ d * ∑' s : ℤ, (if (N:ℝ) / Q < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) :=
          tsum_mul_left
      _ ≤ (2:ℝ) ^ d * (4 / ((N:ℝ) / Q)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 4 * ((2:ℝ) ^ (d + v) / N) := by
          rw [pow_add, hQr, div_div_eq_mul_div]; ring
      _ ≤ 10 * min 1 ((2:ℝ) ^ (d + v) / N) := by
          rw [min_eq_right ((div_le_one hNr).mpr hX)]
          have : 0 ≤ (2:ℝ) ^ (d + v) / N := by positivity
          linarith
  · push_neg at hX
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ d := ⟨_, rfl⟩
    have hMr : (M:ℝ) = 2 ^ d := by rw [hM]; push_cast; ring
    have hMpos : (0:ℝ) < M := by rw [hMr]; positivity
    obtain ⟨hsum, htail⟩ := tail_int (M:ℝ) hMpos
    set b1 : ℤ → ℝ := fun s => if |s| ≤ (M:ℤ) then 2 * (2:ℝ)⁻¹ ^ d else 0 with hb1
    have hb1fin : ∀ s ∉ Finset.Icc (-(M:ℤ)) M, b1 s = 0 := by
      intro s hs
      rw [Finset.mem_Icc, ← abs_le] at hs
      simp only [hb1, if_neg hs]
    have hab : ∀ s, a s ≤
        b1 s + (2:ℝ) ^ d * (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) := by
      intro s
      have hb1n : 0 ≤ b1 s := by simp only [hb1]; split_ifs <;> positivity
      have ht0 : 0 ≤ (2:ℝ) ^ d * (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) :=
        mul_nonneg (by positivity) (by split_ifs <;> positivity)
      by_cases h1 : (N:ℤ) < |(Q:ℤ) * s|
      · obtain ⟨hs0, -⟩ := hbd s h1
        have hb := norm_fc_spike_sq_le d hd s hs0
        have has : a s = ‖fourierCoeff (fun x : 𝕋 => (spike d x : ℂ)) s‖ ^ 2 := by
          simp only [ha, if_pos h1]
        rw [has]
        by_cases h2 : |s| ≤ (M:ℤ)
        · have : b1 s = 2 * (2:ℝ)⁻¹ ^ d := by simp only [hb1, if_pos h2]
          linarith [hb.1]
        · have h3 : (M:ℝ) < |(s:ℝ)| := by
            push_neg at h2
            exact_mod_cast h2
          have : b1 s = 0 := by simp only [hb1, if_neg h2]
          rw [this, zero_add, if_pos h3]
          refine hb.2.trans (le_of_eq ?_)
          rw [inv_pow, one_div, mul_inv, inv_inv, one_div]
      · have has : a s = 0 := by simp only [ha, if_neg h1]
        rw [has]
        linarith
    have hs1 : Summable b1 := summable_of_ne_finset_zero hb1fin
    have hs2 := hsum.mul_left ((2:ℝ) ^ d)
    have hsb := hs1.add hs2
    have hsa : Summable a := Summable.of_nonneg_of_le ha0 hab hsb
    have hb1sum : ∑' s, b1 s ≤ (2 * M + 1) * (2 * (2:ℝ)⁻¹ ^ d) := by
      rw [tsum_eq_sum hb1fin]
      calc ∑ s ∈ Finset.Icc (-(M:ℤ)) M, b1 s
          ≤ ∑ s ∈ Finset.Icc (-(M:ℤ)) M, 2 * (2:ℝ)⁻¹ ^ d := by
            apply Finset.sum_le_sum
            intro s _
            simp only [hb1]
            split_ifs
            · exact le_rfl
            · positivity
        _ = (2 * M + 1) * (2 * (2:ℝ)⁻¹ ^ d) := by
            rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
            congr 1
            have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
            rw [this, Int.toNat_natCast]
            push_cast
            ring
    calc ∑' s, a s
        ≤ ∑' s : ℤ, (b1 s + (2:ℝ) ^ d * (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0)) :=
          Summable.tsum_le_tsum hab hsa hsb
      _ = ∑' s : ℤ, b1 s +
            (2:ℝ) ^ d * ∑' s : ℤ, (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) := by
          rw [Summable.tsum_add hs1 hs2, tsum_mul_left]
      _ ≤ (2 * M + 1) * (2 * (2:ℝ)⁻¹ ^ d) + (2:ℝ) ^ d * (4 / M) :=
          add_le_add hb1sum (mul_le_mul_of_nonneg_left htail (by positivity))
      _ ≤ 10 * min 1 ((2:ℝ) ^ (d + v) / N) := by
          rw [min_eq_left ((one_le_div hNr).mpr hX.le), hMr, inv_pow]
          have hy : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
          have hy0 : (0:ℝ) < 2 ^ d := by positivity
          have hinv : (2:ℝ) ^ d * ((2:ℝ) ^ d)⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
          have e3 : (2:ℝ) ^ d * (4 / 2 ^ d) = 4 := by linear_combination 4 * hinv
          have e4 : (2 * (2:ℝ) ^ d + 1) * (2 * ((2:ℝ) ^ d)⁻¹) = 4 + 2 * ((2:ℝ) ^ d)⁻¹ := by
            linear_combination 4 * hinv
          have e5 : ((2:ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
          rw [e3, e4]
          linarith

end Erdos996
