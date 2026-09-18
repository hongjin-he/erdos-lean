import ErdosLean.Erdos996.Parts.Asm.GlobalL2
import ErdosLean.Erdos996.Parts.SpikeTail

/-!
# Assembly sub-lemma 11 (TailSum): the Fourier tail of `g`

Blueprint §10. Ho Lemma 3.1 (3.5)–(3.6) and (5.4)–(5.5): at each frequency at most one atom is
nonzero, so `|ĝ(r)|² = ∑_k (λ_k/L_k) ∑_q |âtom_{k,q}(r)|²`; summing over `|r| > N` and using
`spike_dilate_tail` with `2^{d_k + U_k + q D_k} ≤ 2^{E_k}` gives
`∑_{|r|>N} |ĝ(r)|² ≤ C₁ ∑_k λ_k min(1, 2^{E_k}/N)`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- If at most one term of a finite sum is nonzero, `‖∑ f‖² = ∑ ‖f‖²`. -/
lemma alt_norm_sum_sq_of_disj {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = 0 ∨ f j = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  by_cases hex : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    have hz : ∀ j ∈ s, j ≠ i → f j = 0 := by
      intro j hj hji
      rcases h i hi j hj (Ne.symm hji) with h1 | h1
      · exact absurd h1 hfi
      · exact h1
    rw [Finset.sum_eq_single i hz (fun h' => absurd hi h'),
      Finset.sum_eq_single i (fun j hj hji => by rw [hz j hj hji, norm_zero]; ring)
        (fun h' => absurd hi h')]
  · push Not at hex
    rw [Finset.sum_eq_zero hex, Finset.sum_eq_zero (fun i hi => by rw [hex i hi, norm_zero]; ring)]
    simp

lemma alt_fc_blk_disj (A k k' : ℕ) (r : ℤ) (hne : k ≠ k') :
    fourierCoeff (fun x => (blk A k x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (blk A k' x : ℂ)) r = 0 := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [fourierCoeff_blk] at h1 h2
  obtain ⟨q, hq, hq0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h1)
  obtain ⟨q', hq', hq0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h2)
  rcases fourierCoeff_atom_disjoint A k q k' q' r hq hq'
    (fun h => hne (congrArg Prod.fst h)) with h | h
  · exact hq0 h
  · exact hq0' h

lemma alt_hasSum_norm_sq (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    HasSum (fun k => ‖fourierCoeff (fun x => (blk A k x : ℂ)) r‖ ^ 2)
      (‖fourierCoeff (fun x => (gFun A x : ℂ)) r‖ ^ 2) := by
  classical
  have hs := hasSum_fourierCoeff_gFun A hA r
  set b := fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r with hb
  by_cases hex : ∃ k0, b k0 ≠ 0
  · obtain ⟨k0, hk0⟩ := hex
    have hz : ∀ k, k ≠ k0 → b k = 0 := by
      intro k hk
      rcases alt_fc_blk_disj A k k0 r hk with h | h
      · exact h
      · exact absurd h hk0
    have h1 : HasSum b (b k0) := hasSum_single k0 hz
    rw [hs.unique h1]
    exact hasSum_single k0 (fun k hk => by
      show ‖b k‖ ^ 2 = 0
      rw [hz k hk, norm_zero]; ring)
  · push Not at hex
    have hb0 : b = 0 := funext hex
    have h1 : HasSum b 0 := by rw [hb0]; exact hasSum_zero
    rw [hs.unique h1, norm_zero]
    have : (fun k => ‖b k‖ ^ 2) = fun _ => (0 : ℝ) ^ 2 := by
      funext k; rw [hex k, norm_zero]
    rw [show (fun k => ‖fourierCoeff (fun x => (blk A k x : ℂ)) r‖ ^ 2) =
      fun k => ‖b k‖ ^ 2 from rfl, this]
    simp

lemma alt_norm_blk_sq (A k : ℕ) (r : ℤ) :
    ‖fourierCoeff (fun x => (blk A k x : ℂ)) r‖ ^ 2 =
      lam A k / blockLen A k *
        ∑ q ∈ Finset.Icc 1 (blockLen A k), ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r‖ ^ 2 := by
  rw [fourierCoeff_blk, norm_mul, mul_pow, alt_norm_sum_sq_of_disj]
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (div_nonneg (lam_pos A k).le (Nat.cast_nonneg _))]
  · intro q hq q' hq' hne
    exact fourierCoeff_atom_disjoint A k q k q' r hq hq' (fun h => hne (congrArg Prod.snd h))

lemma alt_summable_atom (A k q : ℕ) :
    Summable (fun r : ℤ => ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r‖ ^ 2) := by
  have hmeas : Measurable (atom A k q) :=
    (Erdos996.measurable_spike _).comp (continuous_nsmul _).measurable
  have hm : MemLp (fun x => (atom A k q x : ℂ)) 2 μ𝕋 :=
    MemLp.of_bound ((Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable)
      (2 ^ depth A k)
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_spike_le _ _)
  have := (hasSum_sq_fourierCoeff (hm.toLp _)).summable
  rwa [fourierCoeff_congr_ae hm.coeFn_toLp] at this

lemma tail_sum_le : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℕ, 1 ≤ A → ∀ N : ℕ, 1 ≤ N →
    ∑' r : {r : ℤ // (N : ℤ) < |r|}, ‖fourierCoeff (fun x => (gFun A x : ℂ)) r‖ ^ 2 ≤
      C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ logQ A k / N) := by
  obtain ⟨C, hC, hT⟩ := spike_dilate_tail
  refine ⟨C, hC, fun A hA N hN => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set F : ℕ → ℝ := fun k => C * (lam A k * min 1 ((2 : ℝ) ^ logQ A k / N)) with hFdef
  have hF0 : ∀ k, 0 ≤ F k := fun k =>
    mul_nonneg hC.le (mul_nonneg (lam_pos A k).le (le_min zero_le_one (by positivity)))
  have hFle : ∀ k, F k ≤ C * lam A k := fun k =>
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (lam_pos A k).le (min_le_left _ _)) hC.le
  have hFs : Summable F :=
    Summable.of_nonneg_of_le hF0 hFle ((summable_lam A hA).mul_left C)
  rw [← tsum_mul_left]
  refine Real.tsum_le_of_sum_le (fun r => sq_nonneg _) (fun u => ?_)
  have h1 : HasSum (fun k => ∑ r ∈ u, ‖fourierCoeff (fun x => (blk A k x : ℂ)) r.1‖ ^ 2)
      (∑ r ∈ u, ‖fourierCoeff (fun x => (gFun A x : ℂ)) r.1‖ ^ 2) :=
    hasSum_sum (fun r _ => alt_hasSum_norm_sq A hA r.1)
  refine hasSum_le (fun k => ?_) h1 hFs.hasSum
  -- termwise bound for the `k`-th block
  have hL : (1 : ℝ) ≤ blockLen A k := by exact_mod_cast one_le_blockLen A k
  have hq : ∀ q ∈ Finset.Icc 1 (blockLen A k),
      ∑ r ∈ u, ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2 ≤
        C * min 1 ((2 : ℝ) ^ logQ A k / N) := by
    intro q hqm
    rw [Finset.mem_Icc] at hqm
    have hs : Summable (fun r : {r : ℤ // (N : ℤ) < |r|} =>
        ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2) :=
      (alt_summable_atom A k q).comp_injective Subtype.val_injective
    have ht := hT (depth A k) (shift A k + q * spacing A k) N (one_le_depth A k) hN
    have hexp : depth A k + (shift A k + q * spacing A k) ≤ logQ A k := by
      have e1 : logQ A k = shift A k + blockLen A k * spacing A k + depth A k + 2 := rfl
      have e2 : q * spacing A k ≤ blockLen A k * spacing A k := Nat.mul_le_mul_right _ hqm.2
      omega
    have hpow : (2 : ℝ) ^ (depth A k + (shift A k + q * spacing A k)) ≤ (2 : ℝ) ^ logQ A k :=
      pow_le_pow_right₀ (by norm_num) hexp
    calc ∑ r ∈ u, ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2
        ≤ ∑' r : {r : ℤ // (N : ℤ) < |r|},
            ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2 :=
          hs.sum_le_tsum u (fun _ _ => sq_nonneg _)
      _ ≤ C * min 1 ((2 : ℝ) ^ (depth A k + (shift A k + q * spacing A k)) / N) := ht
      _ ≤ C * min 1 ((2 : ℝ) ^ logQ A k / N) :=
          mul_le_mul_of_nonneg_left
            (min_le_min_left _ (div_le_div_of_nonneg_right hpow hNr.le)) hC.le
  calc ∑ r ∈ u, ‖fourierCoeff (fun x => (blk A k x : ℂ)) r.1‖ ^ 2
      = lam A k / blockLen A k * ∑ q ∈ Finset.Icc 1 (blockLen A k),
          ∑ r ∈ u, ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2 := by
        simp_rw [alt_norm_blk_sq, ← Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ lam A k / blockLen A k * ∑ q ∈ Finset.Icc 1 (blockLen A k),
          C * min 1 ((2 : ℝ) ^ logQ A k / N) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hq)
          (div_nonneg (lam_pos A k).le (by linarith))
    _ = F k := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, hFdef]
        field_simp

end Asm
end Erdos996
