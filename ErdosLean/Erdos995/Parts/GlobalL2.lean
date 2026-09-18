import ErdosLean.Erdos995.Parts.Atoms

/-!
# Erdős 995, part L6 (GlobalL2): `g = ∑ F_k` is finite a.e. and lies in `L²`

Adapted from `ErdosLean/Erdos996/Parts/Asm/PartialSumL2.lean` (`‖∑_{k<K} F_k‖₂² = ∑ λ_k ≤ 1`)
and the first half of `ErdosLean/Erdos996/Parts/Asm/GlobalL2.lean` (up to `memLp_gFun`) with `A`
deleted.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

private lemma measurable_atom' (k q : ℕ) : Measurable (atom k q) :=
  (Erdos996.Asm.measurable_spike _).comp (continuous_nsmul _).measurable

lemma measurable_blk (k : ℕ) : Measurable (blk k) := by
  have e : blk k = fun x => Real.sqrt (lam k / blockLen k) *
      ∑ q ∈ Finset.Icc 1 (blockLen k), atom k q x := funext (blk_eq_sum_atom k)
  rw [e]
  exact (Finset.measurable_sum _ fun q _ => measurable_atom' k q).const_mul _

lemma integrable_blk (k : ℕ) : Integrable (blk k) μ𝕋 := by
  refine Integrable.of_bound (measurable_blk k).aestronglyMeasurable
    (Real.sqrt (lam k / blockLen k) * ∑ q ∈ Finset.Icc 1 (blockLen k), (2 : ℝ) ^ depth k)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, blk_eq_sum_atom, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun q _ => Erdos996.Asm.abs_spike_le _ _)

private lemma fourierCoeff_blk_zero (k : ℕ) : fourierCoeff (fun x => (blk k x : ℂ)) 0 = 0 := by
  rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero k q), mul_zero]

private lemma integral_blk (k : ℕ) : ∫ x, blk k x ∂μ𝕋 = 0 := by
  have h := fourierCoeff_blk_zero k
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma measurable_gPos : Measurable gPos := by
  unfold gPos
  exact Measurable.ennreal_tsum fun k => ((measurable_blk k).add_const _).ennreal_ofReal

private lemma measurable_gFun : Measurable gFun := by
  unfold gFun
  exact measurable_gPos.ennreal_toReal.sub_const _

private lemma lintegral_gPos :
    ∫⁻ x, gPos x ∂μ𝕋 = ∑' k, ENNReal.ofReal (floorC k) := by
  unfold gPos
  rw [lintegral_tsum fun k => ((measurable_blk k).add_const _).ennreal_ofReal.aemeasurable]
  congr 1
  ext k
  have hi : Integrable (fun x => blk k x + floorC k) μ𝕋 :=
    (integrable_blk k).add (integrable_const _)
  have hnn : (0 : 𝕋 → ℝ) ≤ᵐ[μ𝕋] fun x => blk k x + floorC k :=
    ae_of_all _ fun x => by
      have := blk_floor k x
      simp only [Pi.zero_apply]
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_add (integrable_blk k) (integrable_const _), integral_blk, integral_const]
  simp

lemma lintegral_gPos_ne_top : ∫⁻ x, gPos x ∂μ𝕋 ≠ ∞ := by
  rw [lintegral_gPos, ← ENNReal.ofReal_tsum_of_nonneg floorC_nonneg summable_floorC]
  exact ENNReal.ofReal_ne_top

lemma ae_gPos_ne_top : ∀ᵐ x ∂μ𝕋, gPos x ≠ ∞ :=
  (ae_lt_top' measurable_gPos.aemeasurable lintegral_gPos_ne_top).mono fun _ hx => hx.ne

lemma gPos_toReal_eq (x : 𝕋) (hx : gPos x ≠ ∞) :
    Summable (fun k => blk k x + floorC k) ∧ (gPos x).toReal = ∑' k, (blk k x + floorC k) := by
  have hnn : ∀ k, 0 ≤ blk k x + floorC k := fun k => by linarith [blk_floor k x]
  have e : ∀ k, (ENNReal.ofReal (blk k x + floorC k)).toReal = blk k x + floorC k :=
    fun k => ENNReal.toReal_ofReal (hnn k)
  constructor
  · have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (blk k x + floorC k)) hx
    simp only [e] at this
    exact this
  · unfold gPos
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    simp only [e]

private lemma hasSum_blk (x : 𝕋) (hx : gPos x ≠ ∞) :
    HasSum (fun k => blk k x) (gFun x) := by
  obtain ⟨hs, htr⟩ := gPos_toReal_eq x hx
  have h := hs.hasSum.sub summable_floorC.hasSum
  simp only [add_sub_cancel_right] at h
  unfold gFun
  rw [htr]
  exact h

lemma tendsto_partialSum_gFun (x : 𝕋) (hx : gPos x ≠ ∞) :
    Tendsto (fun K => ∑ k ∈ range K, blk k x) atTop (𝓝 (gFun x)) :=
  (hasSum_blk x hx).tendsto_sum_nat

/-! ### Partial sums in `L²` -/

private lemma memLp_atomC (k q : ℕ) : MemLp (fun x => (atom k q x : ℂ)) 2 μ𝕋 :=
  MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_atom' k q)).aestronglyMeasurable)
    (2 ^ depth k)
    (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Erdos996.Asm.abs_spike_le _ _)

private noncomputable def aLp (k q : ℕ) : Lp ℂ 2 μ𝕋 := (memLp_atomC k q).toLp _

private lemma coeFn_aLp (k q : ℕ) : ⇑(aLp k q) =ᵐ[μ𝕋] fun x => (atom k q x : ℂ) :=
  (memLp_atomC k q).coeFn_toLp

private lemma fourierCoeff_aLp (k q : ℕ) (r : ℤ) :
    fourierCoeff (⇑(aLp k q)) r = fourierCoeff (fun x => (atom k q x : ℂ)) r := by
  unfold fourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [coeFn_aLp k q] with x hx
  rw [hx]

private lemma inner_fourierBasis_aLp (k q : ℕ) (r : ℤ) :
    inner ℂ (fourierBasis r) (aLp k q) = fourierCoeff (fun x => (atom k q x : ℂ)) r := by
  rw [← fourierBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_aLp]

private lemma inner_aLp_eq_zero (k q k' q' : ℕ)
    (hq : q ∈ Finset.Icc 1 (blockLen k)) (hq' : q' ∈ Finset.Icc 1 (blockLen k'))
    (hne : (k, q) ≠ (k', q')) : inner ℂ (aLp k q) (aLp k' q') = 0 := by
  rw [← fourierBasis.tsum_inner_mul_inner]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  rw [← inner_conj_symm, inner_fourierBasis_aLp, inner_fourierBasis_aLp]
  rcases fourierCoeff_atom_disjoint k q k' q' r hq hq' hne with h | h <;> simp [h]

private lemma inner_aLp_self (k q : ℕ) : inner ℂ (aLp k q) (aLp k q) = 1 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ x ∂μ𝕋, inner ℂ ((aLp k q) x) ((aLp k q) x) =
      ((Erdos996.spike (depth k) ((2 ^ (shift k + q * spacing k) : ℕ) • x) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [coeFn_aLp k q] with x hx
    rw [hx, RCLike.inner_apply', atom, Complex.conj_ofReal]
    push_cast; ring
  rw [integral_congr_ae h, integral_complex_ofReal,
    Erdos996.Asm.integral_spike_nsmul_sq _ _ (one_le_depth k) (pow_ne_zero _ two_ne_zero)]
  simp

private lemma coeFn_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ𝕋) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ𝕋] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ𝕋
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

lemma eLpNorm_partialSum_le (K : ℕ) :
    eLpNorm (fun x => ∑ k ∈ range K, blk k x) 2 μ𝕋 ≤ 1 := by
  set c : ℕ → ℝ := fun k => Real.sqrt (lam k / blockLen k) with hc
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Lp ℂ 2 μ𝕋,
      Gc = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q := ⟨_, rfl⟩
  have hae : ⇑Gc =ᵐ[μ𝕋] fun x => (((∑ k ∈ range K, blk k x : ℝ)) : ℂ) := by
    have h1 := coeFn_finset_sum' (range K)
      (fun k => ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q)
    have h2 : ∀ᵐ x ∂μ𝕋, ∀ k : ℕ,
        (⇑(∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q)) x =
          ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) * (atom k q x : ℂ) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [coeFn_finset_sum' (Icc 1 (blockLen k))
          (fun q => ((c k : ℝ) : ℂ) • aLp k q),
        ae_all_iff.2 fun q => Lp.coeFn_smul ((c k : ℝ) : ℂ) (aLp k q),
        ae_all_iff.2 fun q => coeFn_aLp k q] with x hx hs ha
      rw [hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs q, Pi.smul_apply, smul_eq_mul, ha q]
    filter_upwards [h1, h2] with x hx h2x
    rw [hGc, hx]
    simp only [h2x]
    simp only [blk_eq_sum_atom, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, hc]
  have key : ∀ k ∈ range K, ∀ q ∈ Icc 1 (blockLen k),
      inner ℂ (aLp k q) Gc = ((c k : ℝ) : ℂ) := by
    intro k hk q hq
    rw [hGc, inner_sum, Finset.sum_eq_single k]
    · rw [inner_sum, Finset.sum_eq_single q]
      · rw [inner_smul_right, inner_aLp_self, mul_one]
      · intro q' hq' hne
        rw [inner_smul_right, inner_aLp_eq_zero k q k q' hq hq'
          (fun h => hne (Prod.ext_iff.1 h).2.symm), mul_zero]
      · intro h; exact absurd hq h
    · intro k' _ hne
      rw [inner_sum]
      refine Finset.sum_eq_zero fun q' hq' => ?_
      rw [inner_smul_right, inner_aLp_eq_zero k q k' q' hq hq'
        (fun h => hne (Prod.ext_iff.1 h).1.symm), mul_zero]
    · intro h; exact absurd hk h
  have hinner : inner ℂ Gc Gc = (((∑ k ∈ range K, lam k : ℝ)) : ℂ) := by
    calc inner ℂ Gc Gc
        = inner ℂ (∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen k), ((c k : ℝ) : ℂ) • aLp k q)
            Gc := by rw [← hGc]
      _ = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen k),
            (starRingEnd ℂ) ((c k : ℝ) : ℂ) * inner ℂ (aLp k q) Gc := by
          rw [sum_inner]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_inner]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [inner_smul_left]
      _ = (((∑ k ∈ range K, lam k : ℝ)) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_congr rfl fun q hq => by rw [key k hk q hq]]
          have hL : (blockLen k : ℝ) ≠ 0 := by
            have := one_le_blockLen k
            exact_mod_cast (show blockLen k ≠ 0 by omega)
          have h0 : 0 ≤ lam k / blockLen k :=
            div_nonneg (lam_pos k).le (Nat.cast_nonneg _)
          rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
            Complex.conj_ofReal, ← Complex.ofReal_mul, hc, Real.mul_self_sqrt h0,
            ← Complex.ofReal_natCast, ← Complex.ofReal_mul, mul_div_cancel₀ _ hL]
  have hnorm_sq : ‖Gc‖ ^ 2 = ∑ k ∈ range K, lam k := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Gc
    rw [hinner] at this
    exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact this.symm)
  have hsum : ∑ k ∈ range K, lam k ≤ 1 :=
    (summable_lam.sum_le_tsum (range K) (fun k _ => (lam_pos k).le)).trans tsum_lam_le_one
  have hnorm : ‖Gc‖ ≤ 1 := by nlinarith [norm_nonneg Gc]
  have hmeas : AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk k x) μ𝕋 :=
    (Finset.measurable_sum _ fun k _ => measurable_blk k).aestronglyMeasurable
  have e1 : eLpNorm (fun x => ∑ k ∈ range K, blk k x) 2 μ𝕋 ≤
      eLpNorm (fun x => (((∑ k ∈ range K, blk k x : ℝ)) : ℂ)) 2 μ𝕋 :=
    eLpNorm_mono hmeas fun x => le_of_eq (Complex.norm_real _).symm
  refine e1.trans ?_
  rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hnorm

lemma memLp_gFun : MemLp (fun x => (gFun x : ℂ)) 2 μ𝕋 := by
  refine MemLp.ofReal ?_
  show eLpNorm gFun 2 μ𝕋 < ∞
  have hlim : ∀ᵐ x ∂μ𝕋, Tendsto (fun K => ∑ k ∈ range K, blk k x) atTop (𝓝 (gFun x)) :=
    ae_gPos_ne_top.mono fun x hx => tendsto_partialSum_gFun x hx
  have hmeas : ∀ K, AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk k x) μ𝕋 := fun K =>
    (Finset.measurable_sum _ fun k _ => measurable_blk k).aestronglyMeasurable
  refine lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _
    measurable_gFun.aestronglyMeasurable hlim) ?_
  refine lt_of_le_of_lt (liminf_le_of_frequently_le'
    (Frequently.of_forall fun K => eLpNorm_partialSum_le K)) ?_
  exact ENNReal.one_lt_top

end Con
end Erdos995
