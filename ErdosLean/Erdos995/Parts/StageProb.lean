import ErdosLean.Erdos995.Parts.Params
import ErdosLean.Erdos996.Parts.Asm.SpikeMeasure
import ErdosLean.Erdos996.Parts.Asm.HitWindow
import ErdosLean.Erdos996.Parts.DigitIndependence

/-!
# Erdős 995, part L3 (StageProb): each stage fails with probability `≤ 2^{-(k+3)}`

Adapted from `ErdosLean/Erdos996/Parts/Asm/StageProb.lean` (up to
`measure_compl_stageGood_le`) with `A` deleted. The only numeric change: now
`2^{d_k} < 128 · 4^{b_k} · L_k · 2^{a_k}` and `T_k = 2^{a_k + 2b_k + k + 24}`, so
`#pairs · 2^{-d_k} ≥ (7/8) T_k L_k / (128 · 4^{b_k} L_k 2^{a_k}) = 7 · 2^{k+24} / 1024 ≥ 2^{k+3}`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Elementary bound `(1 - r)^n ≤ 2^{-m}` from `n r ≥ 2^m`. -/
lemma one_sub_pow_le_aux (r : ℝ) (n m : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hn : (2 : ℝ) ^ m ≤ n * r) : (1 - r) ^ n ≤ (2⁻¹ : ℝ) ^ m := by
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ r) n
  have h1 : (2 : ℝ) ^ m ≤ (1 + r) ^ n := by linarith
  have h2 : (1 - r) ^ n * (1 + r) ^ n ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - r) ^ n := pow_nonneg (by linarith) n
  have h4 : (1 - r) ^ n * 2 ^ m ≤ 1 := le_trans (mul_le_mul_of_nonneg_left h1 h3) h2
  rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
  exact h4

lemma ennreal_inv_two_pow (m : ℕ) :
    ((2⁻¹ : ℝ≥0∞)) ^ m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ m) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- The (trial, central layer) pairs of stage `k`. -/
def stagePairs (k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Ico (firstTrial k) (firstTrial (k + 1))).sigma
    (fun s => Finset.Icc (trialLen s + 1) (blockLen k + 1))

/-- Start of the digit window of the pair `i = (s, h)`. -/
def pairStart (k : ℕ) (i : Σ _ : ℕ, ℕ) : ℕ :=
  shift k + trialStart i.1 + i.2 * spacing k

lemma stage_of_mem_Ico {k s : ℕ} (hs : s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1))) :
    stage s = k := by
  rw [Finset.mem_Ico] at hs
  exact stage_eq s k hs.1 hs.2

lemma compl_stageGood_eq (k : ℕ) :
    (stageGood k)ᶜ = ⋂ i ∈ stagePairs k, (Erdos996.Asm.hitSet (depth k) (pairStart k i))ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, stageGood, Set.mem_iInter]
  constructor
  · intro h i hi hx
    rw [stagePairs, Finset.mem_sigma] at hi
    apply h
    refine Set.mem_iUnion₂.mpr ⟨i.1, hi.1, ?_⟩
    rw [goodSet, stage_of_mem_Ico hi.1]
    exact Set.mem_iUnion₂.mpr ⟨i.2, hi.2, hx⟩
  · intro h hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [goodSet, stage_of_mem_Ico hs] at hx
    obtain ⟨hh, hhm, hx⟩ := Set.mem_iUnion₂.mp hx
    exact h ⟨s, hh⟩ (by rw [stagePairs, Finset.mem_sigma]; exact ⟨hs, hhm⟩) hx

lemma pairStart_lt_of_lt (k : ℕ) {s h s' h' : ℕ}
    (hs : s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1)))
    (hh : h ≤ blockLen k + 1) (hss' : s < s') :
    pairStart k ⟨s, h⟩ + depth k ≤ pairStart k ⟨s', h'⟩ := by
  have hM : trialStart (s + 1) = trialStart s + (blockLen k + 2) * spacing k := by
    show trialStart s + (blockLen (stage s) + 2) * spacing (stage s) = _
    rw [stage_of_mem_Ico hs]
  have hmono : trialStart (s + 1) ≤ trialStart s' := trialStart_mono hss'
  have e1 : h * spacing k ≤ (blockLen k + 1) * spacing k := Nat.mul_le_mul_right _ hh
  have e2 : (blockLen k + 2) * spacing k = (blockLen k + 1) * spacing k + spacing k := by
    ring
  have hD : spacing k = depth k + 2 := rfl
  simp only [pairStart]
  omega

lemma pairStart_disj (k : ℕ) :
    ∀ i ∈ stagePairs k, ∀ j ∈ stagePairs k, i ≠ j →
      pairStart k i + depth k ≤ pairStart k j ∨
        pairStart k j + depth k ≤ pairStart k i := by
  intro i hi j hj hij
  rcases i with ⟨s, h⟩
  rcases j with ⟨s', h'⟩
  rw [stagePairs, Finset.mem_sigma, Finset.mem_Icc] at hi hj
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · left; exact pairStart_lt_of_lt k hi.1 hi.2.2 hlt
  · subst heq
    have hne : h ≠ h' := by
      intro e; subst e; exact hij rfl
    have hD : spacing k = depth k + 2 := rfl
    simp only [pairStart]
    rcases lt_or_gt_of_ne hne with hl | hl
    · left
      have : (h + 1) * spacing k ≤ h' * spacing k := Nat.mul_le_mul_right _ hl
      have e2 : (h + 1) * spacing k = h * spacing k + spacing k := by ring
      omega
    · right
      have : (h' + 1) * spacing k ≤ h * spacing k := Nat.mul_le_mul_right _ hl
      have e2 : (h' + 1) * spacing k = h' * spacing k + spacing k := by ring
      omega
  · right; exact pairStart_lt_of_lt k hj.1 hj.2.2 hgt

lemma card_stagePairs (k : ℕ) :
    7 * nTrials k * blockLen k ≤ 8 * (stagePairs k).card := by
  have hS : firstTrial (k + 1) = firstTrial k + nTrials k := rfl
  rw [stagePairs, Finset.card_sigma, Finset.mul_sum]
  calc 7 * nTrials k * blockLen k
      = ∑ _s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1)), 7 * blockLen k := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, hS, Nat.add_sub_cancel_left]; ring
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Nat.card_Icc]
        have := trialLen_le s
        rw [stage_of_mem_Ico hs] at this
        omega

lemma stage_count_nat (k : ℕ) :
    2 ^ (k + 3) * 2 ^ depth k ≤ (stagePairs k).card := by
  have hcard := card_stagePairs k
  have hd := (depth_nat k).2
  set X := 4 ^ bExp k * blockLen k * 2 ^ aExp k with hX
  have hT : nTrials k * blockLen k = 2 ^ k * 2 ^ 24 * X := by
    simp only [nTrials, hX, pow_add, pow_mul]; norm_num; ring
  have hd' : 2 ^ depth k < 128 * X := by rw [hX]; linarith
  have h2k : 0 < 2 ^ k := by positivity
  have hle : 2 ^ (k + 3) * 2 ^ depth k ≤ 2 ^ k * 1024 * X := by
    rw [pow_add]
    calc 2 ^ k * 2 ^ 3 * 2 ^ depth k ≤ 2 ^ k * 2 ^ 3 * (128 * X) :=
          Nat.mul_le_mul_left _ hd'.le
      _ = 2 ^ k * 1024 * X := by ring
  have h7 : 7 * (2 ^ k * 2 ^ 24 * X) ≤ 8 * (stagePairs k).card := by
    rw [← hT, ← mul_assoc]; exact hcard
  have : 8 * (2 ^ k * 1024 * X) ≤ 7 * (2 ^ k * 2 ^ 24 * X) := by
    have : 8 * (2 ^ k * 1024 * X) = 8192 * (2 ^ k * X) := by ring
    have h' : 7 * (2 ^ k * 2 ^ 24 * X) = 117440512 * (2 ^ k * X) := by ring
    rw [this, h']; exact Nat.mul_le_mul_right _ (by norm_num)
  omega

lemma stage_count_real (k : ℕ) :
    (2 : ℝ) ^ (k + 3) ≤ ((stagePairs k).card : ℝ) * (2⁻¹ : ℝ) ^ depth k := by
  rw [inv_pow, le_mul_inv_iff₀ (by positivity)]
  exact_mod_cast stage_count_nat k

lemma measure_compl_stageGood_le (k : ℕ) :
    μ𝕋 (stageGood k)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 3) := by
  classical
  have hmeasI : μ𝕋 (⋂ i ∈ stagePairs k, (Erdos996.Asm.hitSet (depth k) (pairStart k i))ᶜ) =
      ∏ i ∈ stagePairs k, μ𝕋 (Erdos996.Asm.hitSet (depth k) (pairStart k i))ᶜ :=
    Erdos996.measure_iInter_of_disjoint_windows (stagePairs k) (pairStart k)
      (fun i => pairStart k i + depth k)
      (fun i => (Erdos996.Asm.hitSet (depth k) (pairStart k i))ᶜ)
      (fun i _ => Erdos996.Asm.DeterminedByWindow.compl'
        (Erdos996.Asm.determinedByWindow_hitSet _ _))
      (fun i _ => (Erdos996.Asm.measurableSet_hitSet _ _).compl) (pairStart_disj k)
  have hEi : ∀ i, μ𝕋 (Erdos996.Asm.hitSet (depth k) (pairStart k i))ᶜ =
      1 - (2⁻¹ : ℝ≥0∞) ^ depth k := by
    intro i
    rw [measure_compl (Erdos996.Asm.measurableSet_hitSet _ _) (measure_ne_top _ _), measure_univ,
      Erdos996.Asm.measure_hitSet]
  have hr1 : (2⁻¹ : ℝ) ^ depth k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ depth k := by positivity
  have hfin := one_sub_pow_le_aux _ (stagePairs k).card (k + 3) hr0 hr1 (stage_count_real k)
  rw [compl_stageGood_eq, hmeasI, Finset.prod_congr rfl (fun i _ => hEi i), Finset.prod_const,
    ennreal_inv_two_pow, ennreal_inv_two_pow, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hr0, ← ENNReal.ofReal_pow (by linarith)]
  exact ENNReal.ofReal_le_ofReal hfin

end Con
end Erdos995
