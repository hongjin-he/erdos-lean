import ErdosLean.Erdos995.Defs
import ErdosLean.Erdos996.Parts.BlockFloor

/-!
# Erdős 995, part L1 (Params): elementary facts about the stage parameters

Adapted from `ErdosLean/Erdos996/Parts/Asm/Params.lean` with the parameter `A`
deleted and `100` replaced by `sig k = 2^{b_k}` in `depth_spec` and `blk_floor`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma lam_pos (k : ℕ) : 0 < lam k := by
  unfold lam; positivity

lemma lam_le_one (k : ℕ) : lam k ≤ 1 := by
  unfold lam; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma lam_eq (k : ℕ) : lam k = (2 : ℝ)⁻¹ ^ (k + 1) := rfl

lemma geomSucc_summable : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1)) := by
  have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right (2⁻¹)
  exact this.congr (fun k => (pow_succ _ _).symm)

lemma geomSucc_tsum : ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma summable_lam : Summable lam := by
  exact geomSucc_summable.congr (fun k => (lam_eq k).symm)

lemma tsum_lam_le_one : ∑' k, lam k ≤ 1 := by
  have : ∑' k, lam k = 1 := by
    rw [show lam = fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1) from funext lam_eq]
    exact geomSucc_tsum
  rw [this]

lemma sig_ge (k : ℕ) : 128 ≤ sig k := by
  unfold sig bExp
  calc (128 : ℝ) = 2 ^ 7 := by norm_num
    _ ≤ 2 ^ (8 * (k + 1) ^ 2 + 7) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma sig_pos (k : ℕ) : 0 < sig k := by
  have := sig_ge k; linarith

lemma floorC_nonneg (k : ℕ) : 0 ≤ floorC k := by
  unfold floorC; exact div_nonneg (lam_pos k).le (sig_pos k).le

lemma floorC_le (k : ℕ) : floorC k ≤ lam k / 128 := by
  unfold floorC
  exact div_le_div_of_nonneg_left (lam_pos k).le (by norm_num) (sig_ge k)

lemma summable_floorC : Summable floorC := by
  exact Summable.of_nonneg_of_le floorC_nonneg floorC_le (summable_lam.div_const 128)

lemma tsum_floorC_le : ∑' k, floorC k ≤ 1 / 100 := by
  have h1 : ∑' k, floorC k ≤ ∑' k, lam k / 128 :=
    Summable.tsum_le_tsum floorC_le summable_floorC (summable_lam.div_const 128)
  rw [tsum_div_const] at h1
  have := tsum_lam_le_one
  have h2 : (∑' k, lam k) / 128 ≤ 1 / 128 := div_le_div_of_nonneg_right this (by norm_num)
  linarith [h1, h2, show (1 : ℝ) / 128 ≤ 1 / 100 by norm_num]

lemma one_le_blockLen (k : ℕ) : 1 ≤ blockLen k := by
  unfold blockLen
  have : 0 < 21 ^ firstTrial (k + 1) := by positivity
  omega

lemma depthArg_gt (k : ℕ) : 1 < 64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k := by
  have hP : 0 < 4 ^ bExp k := by positivity
  have hQ : 0 < 2 ^ aExp k := by positivity
  have hL := one_le_blockLen k
  generalize 4 ^ bExp k = P at hP ⊢
  generalize 2 ^ aExp k = Q at hQ ⊢
  generalize blockLen k = L at hL ⊢
  have : 1 ≤ P * L * Q := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

lemma depth_nat (k : ℕ) :
    64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k ≤ 2 ^ depth k ∧
      2 ^ depth k < 2 * (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k) := by
  have hN1 := depthArg_gt k
  have hd : depth k = Nat.clog 2 (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k) := rfl
  rw [hd]
  generalize 64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k = N at hN1 ⊢
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos := Nat.clog_pos (b := 2) (by norm_num) hN1
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
  have e : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N).pred := by
    rw [← pow_succ']
    exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
  omega

lemma one_le_depth (k : ℕ) : 1 ≤ depth k :=
  Nat.clog_pos (b := 2) (by norm_num) (depthArg_gt k)

/-- The depth choice (Ho (3.2)) with `B = B_k`, in the exact form used by
`Erdos996.block_lower_floor` and `Erdos996.trial_signal`. -/
lemma depth_spec (k : ℕ) :
    64 * sig k ^ 2 * (blockLen k : ℝ) / lam k ≤ 2 ^ depth k ∧
      (2 : ℝ) ^ depth k < 128 * sig k ^ 2 * (blockLen k : ℝ) / lam k := by
  obtain ⟨h1, h2⟩ := depth_nat k
  have hlam : (lam k)⁻¹ = (2 : ℝ) ^ aExp k := by unfold lam; rw [inv_pow, inv_inv]
  have hsig : sig k ^ 2 = (4 : ℝ) ^ bExp k := by
    unfold sig; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : 64 * sig k ^ 2 * (blockLen k : ℝ) / lam k =
      ((64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam, hsig]; push_cast; ring
  have e2 : 128 * sig k ^ 2 * (blockLen k : ℝ) / lam k =
      ((2 * (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k) : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam, hsig]; push_cast; ring
  rw [e1, e2]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma firstTrial_strictMono : StrictMono firstTrial := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  show firstTrial k < firstTrial k + nTrials k
  have : 0 < nTrials k := by unfold nTrials; positivity
  omega

lemma le_firstTrial (k : ℕ) : k ≤ firstTrial k :=
  firstTrial_strictMono.id_le k

lemma stage_spec (s : ℕ) : firstTrial (stage s) ≤ s ∧ s < firstTrial (stage s + 1) := by
  have h0 : firstTrial (stage s) ≤ s :=
    Nat.findGreatest_spec (P := fun k => firstTrial k ≤ s) (Nat.zero_le s) (by simp [firstTrial])
  refine ⟨h0, ?_⟩
  by_contra h
  rw [not_lt] at h
  have hle : stage s + 1 ≤ s := le_trans (le_firstTrial _) h
  exact Nat.findGreatest_is_greatest (P := fun k => firstTrial k ≤ s)
    (Nat.lt_succ_self _) hle h

lemma stage_eq (s k : ℕ) (h1 : firstTrial k ≤ s) (h2 : s < firstTrial (k + 1)) : stage s = k := by
  obtain ⟨a1, a2⟩ := stage_spec s
  have hm := firstTrial_strictMono.monotone
  rcases lt_trichotomy (stage s) k with h | h | h
  · have := hm (show stage s + 1 ≤ k from h); omega
  · exact h
  · have := hm (show k + 1 ≤ stage s from h); omega

lemma trialLen_le (s : ℕ) : 8 * trialLen s ≤ blockLen (stage s) := by
  unfold trialLen blockLen
  have h1 : s + 1 ≤ firstTrial (stage s + 1) := Nat.succ_le_of_lt (stage_spec s).2
  have h2 : 21 ^ (s + 1) ≤ 21 ^ firstTrial (stage s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h2
  omega

lemma trialStart_mono : Monotone trialStart := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show trialStart k ≤ trialStart k + (blockLen (stage k) + 2) * spacing (stage k)
  omega

lemma blk_floor (k : ℕ) (x : 𝕋) : -(floorC k) ≤ blk k x := by
  have := Erdos996.block_lower_floor (lam k) (sig k) (blockLen k) (depth k) (spacing k) (shift k)
    (lam_pos k) (by linarith [sig_ge k]) (one_le_blockLen k) (depth_spec k).1 x
  unfold blk floorC
  exact this

end Con
end Erdos995
