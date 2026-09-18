import ErdosLean.Erdos995.Parts.Sequence
import ErdosLean.Erdos995.Parts.GlobalL2
import ErdosLean.Erdos996.Parts.TrialSignal

/-!
# Erdős 995, part L8 (Master): the master estimate at the end of a good trial

Adapted from `ErdosLean/Erdos996/Parts/Asm/Master.lean`. If trial `s` (stage `k`) is good and
`g` is finite at every `n_j x`, then with `P = 21^s - 1`, `ℓ = 20 · 21^s`, `N = P + ℓ`:
`∑_{j<N} g(n_j x) ≥ 2 B_k ℓ - N/100 ≥ B_k N` (because `2ℓ = 40 · 21^s ≥ 1.01 · 21^{s+1}`).
The signal comes from `Erdos996.trial_signal` with `B = sig k ≥ 128 ≥ 100`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma gFun_ge (x : 𝕋) : -(1 / 100 : ℝ) ≤ gFun x := by
  unfold gFun
  have h1 := tsum_floorC_le
  have h2 : 0 ≤ (gPos x).toReal := ENNReal.toReal_nonneg
  linarith

lemma blk_sub_le_gFun (x : 𝕋) (hx : gPos x ≠ ∞) (k : ℕ) :
    blk k x - 1 / 100 ≤ gFun x := by
  unfold gFun
  have h1 := tsum_floorC_le
  have h0 := floorC_nonneg k
  have hle : ENNReal.ofReal (blk k x + floorC k) ≤ gPos x := by
    unfold gPos
    exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (blk k x + floorC k)) k
  have h3 : (ENNReal.ofReal (blk k x + floorC k)).toReal ≤ (gPos x).toReal :=
    ENNReal.toReal_mono hx hle
  have h4 : blk k x + floorC k ≤ (ENNReal.ofReal (blk k x + floorC k)).toReal := by
    rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
  linarith

lemma ae_forall_nSeq {P : 𝕋 → Prop} (h : ∀ᵐ y ∂μ𝕋, P y) :
    ∀ᵐ x ∂μ𝕋, ∀ j, P (nSeq j • x) := by
  have hv : (volume : Measure 𝕋) = μ𝕋 := by
    rw [volume_eq_smul_haarAddCircle]; simp
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (fun y : 𝕋 => nSeq j • y) μ𝕋 μ𝕋 := by
    by_cases h1 : 1 < nSeq j
    · rw [← hv]; exact (ergodic_nsmul h1).toMeasurePreserving
    · have h2 : 1 ≤ nSeq j := one_le_nSeq j
      have h3 : nSeq j = 1 := by omega
      simp only [h3, one_smul]
      exact MeasurePreserving.id _
  exact hmp.quasiMeasurePreserving.ae h

lemma master_trial (x : 𝕋) (s : ℕ) (hfin : ∀ j, gPos (nSeq j • x) ≠ ∞) (hx : x ∈ goodSet s) :
    ∃ N : ℕ, s ≤ N ∧ N ≤ 21 ^ (s + 1) ∧
      sig (stage s) * N ≤ ∑ j ∈ range N, gFun (nSeq j • x) := by
  set k := stage s with hk
  set ℓ := trialLen s with hℓ
  set P := 21 ^ s - 1 with hP
  have ht : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hsl : s < 21 ^ s := Nat.lt_pow_self (by norm_num)
  have hℓv : ℓ = 20 * 21 ^ s := rfl
  have h21 : 21 ^ (s + 1) = 21 * 21 ^ s := by rw [pow_succ]; ring
  have hℓP : 19 * (P + 1) ≤ ℓ := by omega
  refine ⟨P + ℓ, by omega, by omega, ?_⟩
  have hB := sig_ge k
  -- the trial signal
  have hsig : 2 * sig k * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ,
      Erdos996.block (lam k) (blockLen k) (depth k) (spacing k) (shift k)
        ((2 ^ (trialStart s + r * spacing k) : ℕ) • x) := by
    have hd := depth_spec k
    apply Erdos996.trial_signal (lam k) (sig k) (blockLen k) ℓ (depth k) (spacing k) (shift k)
      (trialStart s) (lam_pos k) (lam_le_one k) (by linarith) (one_le_blockLen k)
      (trialLen_le s) (by simp [spacing]) hd.1 hd.2 x
    simp only [goodSet, Set.mem_iUnion] at hx
    obtain ⟨h, hh, hx⟩ := hx
    exact ⟨h, hh, by simpa [Erdos996.Asm.hitSet, Erdos996.Asm.spikeSet, add_assoc] using hx⟩
  -- reindex the trial
  have hre : ∑ r ∈ Finset.Icc 1 ℓ,
      Erdos996.block (lam k) (blockLen k) (depth k) (spacing k) (shift k)
        ((2 ^ (trialStart s + r * spacing k) : ℕ) • x)
      = ∑ j ∈ Finset.Ico P (P + ℓ), blk k (nSeq j • x) := by
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
      rw [mExp_trial s r hr.1 hr.2]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => gFun (nSeq j • x))
    (Nat.le_add_right P ℓ)
  have hA1 : -((P : ℝ) * (1 / 100)) ≤ ∑ j ∈ range P, gFun (nSeq j • x) := by
    have := Finset.card_nsmul_le_sum (range P) (fun j => gFun (nSeq j • x)) (-(1 / 100))
      (fun j _ => gFun_ge _)
    simp only [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hA2 : ∑ j ∈ Finset.Ico P (P + ℓ), (blk k (nSeq j • x) - 1 / 100)
      ≤ ∑ j ∈ Finset.Ico P (P + ℓ), gFun (nSeq j • x) :=
    Finset.sum_le_sum (fun j _ => blk_sub_le_gFun _ (hfin j) k)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    nsmul_eq_mul, ← hre] at hA2
  rw [← hsplit]
  have hℓP' : 19 * ((P : ℝ) + 1) ≤ ℓ := by exact_mod_cast hℓP
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  push_cast
  nlinarith

end Con
end Erdos995
