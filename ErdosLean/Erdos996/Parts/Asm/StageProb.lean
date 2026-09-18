import ErdosLean.Erdos996.Parts.Asm.Params
import ErdosLean.Erdos996.Parts.Asm.SpikeMeasure
import ErdosLean.Erdos996.Parts.Asm.HitWindow
import ErdosLean.Erdos996.Parts.DigitIndependence

/-!
# Assembly sub-lemma 5 (StageProb): each stage succeeds with high probability

Blueprint §5. Ho Lemma 3.7 (probability of a good trial) and Lemma 4.2 (independence, stage
failure `≤ exp(-c₀ T_k λ_k / B²)`), simplified: `(S_k)ᶜ` is the intersection over all pairs
(trial `s` of stage `k`, central layer `h`) of the miss events, all with disjoint digit windows,
so `μ((S_k)ᶜ) = (1 - 2^{-d_k})^{n_k}` with `n_k ≥ 7 T_k L_k / 8`, and `n_k 2^{-d_k} ≥ 2^{k+3}`.
Then a union bound gives `μ(⋂ S_k) ≥ 1 - ∑ 2^{-(k+3)} = 3/4`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Elementary bound `(1 - r)^n ≤ 2^{-m}` from `n r ≥ 2^m` (via `(1-r)^n (1+r)^n ≤ 1` and
Bernoulli). -/
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
def stagePairs (A k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Ico (firstTrial A k) (firstTrial A (k + 1))).sigma
    (fun s => Finset.Icc (trialLen s + 1) (blockLen A k + 1))

/-- Start of the digit window of the pair `i = (s, h)`. -/
def pairStart (A k : ℕ) (i : Σ _ : ℕ, ℕ) : ℕ :=
  shift A k + trialStart A i.1 + i.2 * spacing A k

lemma stage_of_mem_Ico {A k s : ℕ} (hs : s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1))) :
    stage A s = k := by
  rw [Finset.mem_Ico] at hs
  exact stage_eq A s k hs.1 hs.2

lemma compl_stageGood_eq (A k : ℕ) :
    (stageGood A k)ᶜ = ⋂ i ∈ stagePairs A k, (hitSet (depth A k) (pairStart A k i))ᶜ := by
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

lemma pairStart_lt_of_lt (A k : ℕ) {s h s' h' : ℕ}
    (hs : s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)))
    (hh : h ≤ blockLen A k + 1) (hss' : s < s') :
    pairStart A k ⟨s, h⟩ + depth A k ≤ pairStart A k ⟨s', h'⟩ := by
  have hM : trialStart A (s + 1) = trialStart A s + (blockLen A k + 2) * spacing A k := by
    show trialStart A s + (blockLen A (stage A s) + 2) * spacing A (stage A s) = _
    rw [stage_of_mem_Ico hs]
  have hmono : trialStart A (s + 1) ≤ trialStart A s' := trialStart_mono A hss'
  have e1 : h * spacing A k ≤ (blockLen A k + 1) * spacing A k := Nat.mul_le_mul_right _ hh
  have e2 : (blockLen A k + 2) * spacing A k = (blockLen A k + 1) * spacing A k + spacing A k := by
    ring
  have hD : spacing A k = depth A k + 2 := rfl
  simp only [pairStart]
  omega

lemma pairStart_disj (A k : ℕ) :
    ∀ i ∈ stagePairs A k, ∀ j ∈ stagePairs A k, i ≠ j →
      pairStart A k i + depth A k ≤ pairStart A k j ∨
        pairStart A k j + depth A k ≤ pairStart A k i := by
  intro i hi j hj hij
  rcases i with ⟨s, h⟩
  rcases j with ⟨s', h'⟩
  rw [stagePairs, Finset.mem_sigma, Finset.mem_Icc] at hi hj
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · left; exact pairStart_lt_of_lt A k hi.1 hi.2.2 hlt
  · subst heq
    have hne : h ≠ h' := by
      intro e; subst e; exact hij rfl
    have hD : spacing A k = depth A k + 2 := rfl
    simp only [pairStart]
    rcases lt_or_gt_of_ne hne with hl | hl
    · left
      have : (h + 1) * spacing A k ≤ h' * spacing A k := Nat.mul_le_mul_right _ hl
      have e2 : (h + 1) * spacing A k = h * spacing A k + spacing A k := by ring
      omega
    · right
      have : (h' + 1) * spacing A k ≤ h * spacing A k := Nat.mul_le_mul_right _ hl
      have e2 : (h' + 1) * spacing A k = h' * spacing A k + spacing A k := by ring
      omega
  · right; exact pairStart_lt_of_lt A k hj.1 hj.2.2 hgt

lemma card_stagePairs (A k : ℕ) :
    7 * nTrials A k * blockLen A k ≤ 8 * (stagePairs A k).card := by
  have hS : firstTrial A (k + 1) = firstTrial A k + nTrials A k := rfl
  rw [stagePairs, Finset.card_sigma, Finset.mul_sum]
  calc 7 * nTrials A k * blockLen A k
      = ∑ _s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)), 7 * blockLen A k := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, hS, Nat.add_sub_cancel_left]; ring
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Nat.card_Icc]
        have := trialLen_le A s
        rw [stage_of_mem_Ico hs] at this
        omega

lemma real_count_aux (n L P Λ K : ℝ) (hcard : 7 * (Λ * K * 16777216) * L ≤ 8 * n)
    (hspec : P < 128 * 100 ^ 2 * L * Λ) (hK : 0 < K) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ) :
    K * 2 ^ 3 * P ≤ n := by
  have hk := mul_lt_mul_of_pos_left hspec hK
  have hmono : 0 ≤ K * (L * Λ) := mul_nonneg hK.le (mul_nonneg hL hΛ)
  nlinarith

lemma stage_count_real (A k : ℕ) :
    (2 : ℝ) ^ (k + 3) ≤ ((stagePairs A k).card : ℝ) * (2⁻¹ : ℝ) ^ depth A k := by
  have hspec := (depth_spec A k).2
  have hlam : lam A k = ((2 : ℝ) ^ aExp A k)⁻¹ := by simp [lam, inv_pow]
  rw [hlam, div_inv_eq_mul] at hspec
  have hcardR : 7 * (nTrials A k : ℝ) * (blockLen A k : ℝ) ≤ 8 * ((stagePairs A k).card : ℝ) := by
    exact_mod_cast card_stagePairs A k
  have hT : (nTrials A k : ℝ) = 2 ^ aExp A k * 2 ^ k * 16777216 := by
    simp only [nTrials]; push_cast; rw [pow_add, pow_add]; norm_num
  rw [hT] at hcardR
  rw [inv_pow, le_mul_inv_iff₀ (by positivity), pow_add]
  exact real_count_aux _ _ _ _ _ hcardR hspec (by positivity) (Nat.cast_nonneg _) (by positivity)

lemma measure_compl_stageGood_le (A : ℕ) (hA : 1 ≤ A) (k : ℕ) :
    μ𝕋 (stageGood A k)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 3) := by
  classical
  have hmeasI : μ𝕋 (⋂ i ∈ stagePairs A k, (hitSet (depth A k) (pairStart A k i))ᶜ) =
      ∏ i ∈ stagePairs A k, μ𝕋 (hitSet (depth A k) (pairStart A k i))ᶜ :=
    measure_iInter_of_disjoint_windows (stagePairs A k) (pairStart A k)
      (fun i => pairStart A k i + depth A k) (fun i => (hitSet (depth A k) (pairStart A k i))ᶜ)
      (fun i _ => DeterminedByWindow.compl' (determinedByWindow_hitSet _ _))
      (fun i _ => (measurableSet_hitSet _ _).compl) (pairStart_disj A k)
  have hEi : ∀ i, μ𝕋 (hitSet (depth A k) (pairStart A k i))ᶜ = 1 - (2⁻¹ : ℝ≥0∞) ^ depth A k := by
    intro i
    rw [measure_compl (measurableSet_hitSet _ _) (measure_ne_top _ _), measure_univ,
      measure_hitSet]
  have hr1 : (2⁻¹ : ℝ) ^ depth A k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ depth A k := by positivity
  have hfin := one_sub_pow_le_aux _ (stagePairs A k).card (k + 3) hr0 hr1 (stage_count_real A k)
  rw [compl_stageGood_eq, hmeasI, Finset.prod_congr rfl (fun i _ => hEi i), Finset.prod_const,
    ennreal_inv_two_pow, ennreal_inv_two_pow, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hr0, ← ENNReal.ofReal_pow (by linarith)]
  exact ENNReal.ofReal_le_ofReal hfin

lemma measure_iInter_stageGood_pos (A : ℕ) (hA : 1 ≤ A) :
    0 < μ𝕋 (⋂ k, stageGood A k) := by
  set G := ⋂ k, stageGood A k
  have hsum : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 3) = (2⁻¹ : ℝ≥0∞) ^ 2 := by
    calc ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 3) = ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ 3 * (2⁻¹ : ℝ≥0∞) ^ k :=
          tsum_congr fun k => by ring
      _ = (2⁻¹ : ℝ≥0∞) ^ 3 * (1 - 2⁻¹)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = (2⁻¹ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.one_sub_inv_two, inv_inv, pow_succ, mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hc : μ𝕋 Gᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ 2 := by
    rw [Set.compl_iInter]
    calc _ ≤ ∑' k, μ𝕋 (stageGood A k)ᶜ := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 3) :=
          ENNReal.tsum_le_tsum fun k => measure_compl_stageGood_le A hA k
      _ = _ := hsum
  have h1 : (1 : ℝ≥0∞) ≤ μ𝕋 G + (2⁻¹ : ℝ≥0∞) ^ 2 := by
    calc (1 : ℝ≥0∞) = μ𝕋 (G ∪ Gᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ𝕋 G + μ𝕋 Gᶜ := measure_union_le _ _
      _ ≤ _ := by gcongr
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0, zero_add] at h1
  have h2 : (2⁻¹ : ℝ≥0∞) ^ 2 ≤ 2⁻¹ :=
    pow_le_of_le_one (by simp) (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) (by norm_num)
  have h3 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  exact absurd (h1.trans h2) (not_le.mpr h3)

end Asm
end Erdos996
