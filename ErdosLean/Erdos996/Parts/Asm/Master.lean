import ErdosLean.Erdos996.Parts.Asm.Params
import ErdosLean.Erdos996.Parts.Asm.Sequence
import ErdosLean.Erdos996.Parts.TrialSignal

/-!
# Assembly sub-lemma 9 (Master): the master estimate at the end of a good trial

Blueprint §9. Ho Prop. 4.3, "master estimate" (4.16): if trial `s` (of stage `k`) is good and
the series is finite at all `n_j x`, then with `N = 21^{s+1} - 1`, `P = 21^s - 1`, `ℓ = ℓ_s`:
`∑_{j<N} g(n_j x) ≥ ∑_{r=1}^{ℓ} F_k(2^{M_s + r D_k} x) - N/100 ≥ 200 ℓ - N/100 ≥ N`.
Also the pointwise floors of `g` and the pull-back of a.e. statements along `x ↦ n_j x`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma gFun_ge (A : ℕ) (hA : 1 ≤ A) (x : 𝕋) : -(1 / 100 : ℝ) ≤ gFun A x := by
  unfold gFun
  have h1 := tsum_floorC_le A hA
  have h2 : 0 ≤ (gPos A x).toReal := ENNReal.toReal_nonneg
  linarith

lemma blk_sub_le_gFun (A : ℕ) (hA : 1 ≤ A) (x : 𝕋) (hx : gPos A x ≠ ∞) (k : ℕ) :
    blk A k x - 1 / 100 ≤ gFun A x := by
  unfold gFun
  have h1 := tsum_floorC_le A hA
  have h0 := floorC_nonneg A k
  have hle : ENNReal.ofReal (blk A k x + floorC A k) ≤ gPos A x := by
    unfold gPos
    exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (blk A k x + floorC A k)) k
  have h3 : (ENNReal.ofReal (blk A k x + floorC A k)).toReal ≤ (gPos A x).toReal :=
    ENNReal.toReal_mono hx hle
  have h4 : blk A k x + floorC A k ≤ (ENNReal.ofReal (blk A k x + floorC A k)).toReal := by
    rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
  linarith

lemma ae_forall_nSeq (A : ℕ) {P : 𝕋 → Prop} (h : ∀ᵐ y ∂μ𝕋, P y) :
    ∀ᵐ x ∂μ𝕋, ∀ j, P (nSeq A j • x) := by
  have hv : (volume : Measure 𝕋) = μ𝕋 := by
    rw [volume_eq_smul_haarAddCircle]; simp
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (fun y : 𝕋 => nSeq A j • y) μ𝕋 μ𝕋 := by
    by_cases h1 : 1 < nSeq A j
    · rw [← hv]; exact (ergodic_nsmul h1).toMeasurePreserving
    · have h2 : 1 ≤ nSeq A j := Nat.one_le_two_pow
      have h3 : nSeq A j = 1 := by omega
      simp only [h3, one_smul]
      exact MeasurePreserving.id _
  exact hmp.quasiMeasurePreserving.ae h

lemma master_trial (A : ℕ) (hA : 1 ≤ A) (x : 𝕋) (s : ℕ)
    (hfin : ∀ j, gPos A (nSeq A j • x) ≠ ∞) (hx : x ∈ goodSet A s) :
    ∃ N : ℕ, s ≤ N ∧ (1 : ℝ) ≤ (∑ j ∈ range N, gFun A (nSeq A j • x)) / N := by
  set k := stage A s with hk
  set ℓ := trialLen s with hℓ
  set P := 21 ^ s - 1 with hP
  have ht : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hsl : s < 21 ^ s := Nat.lt_pow_self (by norm_num)
  have hℓP : P + 1 ≤ ℓ := by simp only [hℓ, hP, trialLen]; omega
  have hℓv : ℓ = 20 * 21 ^ s := rfl
  refine ⟨P + ℓ, by omega, ?_⟩
  -- the trial signal
  have hsig : 2 * (100 : ℝ) * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ,
      block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k)
        ((2 ^ (trialStart A s + r * spacing A k) : ℕ) • x) := by
    have hd := depth_spec A k
    apply trial_signal (lam A k) 100 (blockLen A k) ℓ (depth A k) (spacing A k) (shift A k)
      (trialStart A s) (lam_pos A k) (lam_le_one A k) le_rfl (one_le_blockLen A k)
      (trialLen_le A s) (by simp [spacing]) hd.1 hd.2 x
    simp only [goodSet, Set.mem_iUnion] at hx
    obtain ⟨h, hh, hx⟩ := hx
    exact ⟨h, hh, by simpa [hitSet, spikeSet, add_assoc] using hx⟩
  -- reindex the trial
  have hre : ∑ r ∈ Finset.Icc 1 ℓ,
      block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k)
        ((2 ^ (trialStart A s + r * spacing A k) : ℕ) • x)
      = ∑ j ∈ Finset.Ico P (P + ℓ), blk A k (nSeq A j • x) := by
    apply Finset.sum_nbij' (fun r => 21 ^ s + r - 2) (fun j => j + 2 - 21 ^ s)
    · intro r hr; simp only [Finset.mem_Icc, Finset.mem_Ico] at hr ⊢
      omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
      omega
    · intro r hr; simp only [Finset.mem_Icc] at hr; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      unfold blk nSeq
      rw [mExp_trial A s r hr.1 hr.2]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => gFun A (nSeq A j • x))
    (Nat.le_add_right P ℓ)
  have hA1 : -((P : ℝ) * (1 / 100)) ≤ ∑ j ∈ range P, gFun A (nSeq A j • x) := by
    have := Finset.card_nsmul_le_sum (range P) (fun j => gFun A (nSeq A j • x)) (-(1 / 100))
      (fun j _ => gFun_ge A hA _)
    simp only [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hA2 : ∑ j ∈ Finset.Ico P (P + ℓ), (blk A k (nSeq A j • x) - 1 / 100)
      ≤ ∑ j ∈ Finset.Ico P (P + ℓ), gFun A (nSeq A j • x) :=
    Finset.sum_le_sum (fun j _ => blk_sub_le_gFun A hA _ (hfin j) k)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    nsmul_eq_mul, ← hre] at hA2
  rw [← hsplit]
  have hNpos : (0 : ℝ) < ((P + ℓ : ℕ) : ℝ) := by
    have : 0 < P + ℓ := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hNpos, one_mul]
  have hℓP' : (P : ℝ) + 1 ≤ ℓ := by exact_mod_cast hℓP
  push_cast
  nlinarith

end Asm
end Erdos996
