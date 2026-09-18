import ErdosLean.Erdos996.Parts.Asm.Atoms

/-!
# Assembly sub-lemma 7 (PartialSumL2): `L²` norm of the partial sums

Blueprint §7. Ho Lemma 3.1 (3.3) and Prop. 4.3 (orthogonality of the blocks):
`‖∑_{k<K} F_k‖₂² = ∑_{k<K} λ_k ≤ 1`, via Parseval (`tsum_sq_fourierCoeff`), the disjoint
Fourier supports of the atoms (`fourierCoeff_atom_disjoint`), and `‖atom‖₂ = 1`
(`integral_spike_nsmul_sq`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

private lemma measurable_atom' (A k q : ℕ) : Measurable (atom A k q) :=
  (Erdos996.measurable_spike _).comp (continuous_nsmul _).measurable

private lemma memLp_atomC (A k q : ℕ) : MemLp (fun x => (atom A k q x : ℂ)) 2 μ𝕋 :=
  MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_atom' A k q)).aestronglyMeasurable)
    (2 ^ depth A k)
    (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_spike_le _ _)

/-- The atom as an element of `L²(𝕋; ℂ)`. -/
private noncomputable def aLp (A k q : ℕ) : Lp ℂ 2 μ𝕋 := (memLp_atomC A k q).toLp _

private lemma coeFn_aLp (A k q : ℕ) : ⇑(aLp A k q) =ᵐ[μ𝕋] fun x => (atom A k q x : ℂ) :=
  (memLp_atomC A k q).coeFn_toLp

private lemma fourierCoeff_aLp (A k q : ℕ) (r : ℤ) :
    fourierCoeff (⇑(aLp A k q)) r = fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  unfold fourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [coeFn_aLp A k q] with x hx
  rw [hx]

private lemma inner_fourierBasis_aLp (A k q : ℕ) (r : ℤ) :
    inner ℂ (fourierBasis r) (aLp A k q) = fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  rw [← fourierBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_aLp]

private lemma inner_aLp_eq_zero (A k q k' q' : ℕ)
    (hq : q ∈ Finset.Icc 1 (blockLen A k)) (hq' : q' ∈ Finset.Icc 1 (blockLen A k'))
    (hne : (k, q) ≠ (k', q')) : inner ℂ (aLp A k q) (aLp A k' q') = 0 := by
  rw [← fourierBasis.tsum_inner_mul_inner]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  rw [← inner_conj_symm, inner_fourierBasis_aLp, inner_fourierBasis_aLp]
  rcases fourierCoeff_atom_disjoint A k q k' q' r hq hq' hne with h | h <;> simp [h]

private lemma inner_aLp_self (A k q : ℕ) : inner ℂ (aLp A k q) (aLp A k q) = 1 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ x ∂μ𝕋, inner ℂ ((aLp A k q) x) ((aLp A k q) x) =
      ((spike (depth A k) ((2 ^ (shift A k + q * spacing A k) : ℕ) • x) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [coeFn_aLp A k q] with x hx
    rw [hx, RCLike.inner_apply', atom, Complex.conj_ofReal]
    push_cast; ring
  rw [integral_congr_ae h, integral_complex_ofReal,
    integral_spike_nsmul_sq _ _ (one_le_depth A k) (pow_ne_zero _ two_ne_zero)]
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

lemma eLpNorm_partialSum_le (A : ℕ) (hA : 1 ≤ A) (K : ℕ) :
    eLpNorm (fun x => ∑ k ∈ range K, blk A k x) 2 μ𝕋 ≤ 1 := by
  set c : ℕ → ℝ := fun k => Real.sqrt (lam A k / blockLen A k) with hc
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Lp ℂ 2 μ𝕋,
      Gc = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q := ⟨_, rfl⟩
  -- pointwise identification
  have hae : ⇑Gc =ᵐ[μ𝕋] fun x => (((∑ k ∈ range K, blk A k x : ℝ)) : ℂ) := by
    have h1 := coeFn_finset_sum' (range K)
      (fun k => ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q)
    have h2 : ∀ᵐ x ∂μ𝕋, ∀ k : ℕ,
        (⇑(∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q)) x =
          ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) * (atom A k q x : ℂ) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [coeFn_finset_sum' (Icc 1 (blockLen A k))
          (fun q => ((c k : ℝ) : ℂ) • aLp A k q),
        ae_all_iff.2 fun q => Lp.coeFn_smul ((c k : ℝ) : ℂ) (aLp A k q),
        ae_all_iff.2 fun q => coeFn_aLp A k q] with x hx hs ha
      rw [hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs q, Pi.smul_apply, smul_eq_mul, ha q]
    filter_upwards [h1, h2] with x hx h2x
    rw [hGc, hx]
    simp only [h2x]
    simp only [blk_eq_sum_atom, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, hc]
  -- inner product computation
  have key : ∀ k ∈ range K, ∀ q ∈ Icc 1 (blockLen A k),
      inner ℂ (aLp A k q) Gc = ((c k : ℝ) : ℂ) := by
    intro k hk q hq
    rw [hGc, inner_sum, Finset.sum_eq_single k]
    · rw [inner_sum, Finset.sum_eq_single q]
      · rw [inner_smul_right, inner_aLp_self, mul_one]
      · intro q' hq' hne
        rw [inner_smul_right, inner_aLp_eq_zero A k q k q' hq hq'
          (fun h => hne (Prod.ext_iff.1 h).2.symm), mul_zero]
      · intro h; exact absurd hq h
    · intro k' _ hne
      rw [inner_sum]
      refine Finset.sum_eq_zero fun q' hq' => ?_
      rw [inner_smul_right, inner_aLp_eq_zero A k q k' q' hq hq'
        (fun h => hne (Prod.ext_iff.1 h).1.symm), mul_zero]
    · intro h; exact absurd hk h
  have hinner : inner ℂ Gc Gc = (((∑ k ∈ range K, lam A k : ℝ)) : ℂ) := by
    calc inner ℂ Gc Gc
        = inner ℂ (∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q)
            Gc := by rw [← hGc]
      _ = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen A k),
            (starRingEnd ℂ) ((c k : ℝ) : ℂ) * inner ℂ (aLp A k q) Gc := by
          rw [sum_inner]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_inner]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [inner_smul_left]
      _ = (((∑ k ∈ range K, lam A k : ℝ)) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_congr rfl fun q hq => by rw [key k hk q hq]]
          have hL : (blockLen A k : ℝ) ≠ 0 := by
            have := one_le_blockLen A k
            exact_mod_cast (show blockLen A k ≠ 0 by omega)
          have h0 : 0 ≤ lam A k / blockLen A k :=
            div_nonneg (lam_pos A k).le (Nat.cast_nonneg _)
          rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
            Complex.conj_ofReal, ← Complex.ofReal_mul, hc, Real.mul_self_sqrt h0,
            ← Complex.ofReal_natCast, ← Complex.ofReal_mul, mul_div_cancel₀ _ hL]
  have hnorm_sq : ‖Gc‖ ^ 2 = ∑ k ∈ range K, lam A k := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Gc
    rw [hinner] at this
    exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact this.symm)
  have hsum : ∑ k ∈ range K, lam A k ≤ 1 :=
    ((summable_lam A hA).sum_le_tsum (range K) (fun k _ => (lam_pos A k).le)).trans
      (tsum_lam_le_one A hA)
  have hnorm : ‖Gc‖ ≤ 1 := by nlinarith [norm_nonneg Gc]
  have hmeas : AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk A k x) μ𝕋 := by
    have hb : ∀ k, Measurable (blk A k) := fun k => by
      have e : blk A k = fun x => Real.sqrt (lam A k / blockLen A k) *
          ∑ q ∈ Icc 1 (blockLen A k), atom A k q x := funext (blk_eq_sum_atom A k)
      rw [e]
      exact (Finset.measurable_sum _ fun q _ => measurable_atom' A k q).const_mul _
    exact (Finset.measurable_sum _ fun k _ => hb k).aestronglyMeasurable
  have e1 : eLpNorm (fun x => ∑ k ∈ range K, blk A k x) 2 μ𝕋 ≤
      eLpNorm (fun x => (((∑ k ∈ range K, blk A k x : ℝ)) : ℂ)) 2 μ𝕋 :=
    eLpNorm_mono hmeas fun x => le_of_eq (Complex.norm_real _).symm
  refine e1.trans ?_
  rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hnorm

end Asm
end Erdos996
