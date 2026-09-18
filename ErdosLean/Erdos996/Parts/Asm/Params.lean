import ErdosLean.Erdos996.Parts.Asm.Construction
import ErdosLean.Erdos996.Parts.BlockFloor

/-!
# Assembly sub-lemma 1 (Params): elementary facts about the stage parameters

Ho, arXiv:2604.18535, (3.1)–(3.2), (4.3)–(4.9),
Lemma 4.1 and the upper half of Lemma 5.1 (`scale_bound`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma lam_pos (A k : ℕ) : 0 < lam A k := by
  unfold lam; positivity

lemma lam_le_one (A k : ℕ) : lam A k ≤ 1 := by
  unfold lam; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma lam_le (A : ℕ) (hA : 1 ≤ A) (k : ℕ) : lam A k ≤ (2 : ℝ)⁻¹ ^ (k + 1) := by
  unfold lam aExp
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)

lemma geomSucc_summable : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1)) := by
  have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right (2⁻¹)
  exact this.congr (fun k => (pow_succ _ _).symm)

lemma geomSucc_tsum : ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma summable_lam (A : ℕ) (hA : 1 ≤ A) : Summable (lam A) := by
  exact Summable.of_nonneg_of_le (fun k => (lam_pos A k).le) (lam_le A hA) geomSucc_summable

lemma tsum_lam_le_one (A : ℕ) (hA : 1 ≤ A) : ∑' k, lam A k ≤ 1 := by
  calc ∑' k, lam A k ≤ ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) :=
        Summable.tsum_le_tsum (lam_le A hA) (summable_lam A hA) geomSucc_summable
    _ = 1 := geomSucc_tsum

lemma floorC_nonneg (A k : ℕ) : 0 ≤ floorC A k := by
  unfold floorC; exact div_nonneg (lam_pos A k).le (by norm_num)

lemma summable_floorC (A : ℕ) (hA : 1 ≤ A) : Summable (floorC A) := by
  exact (summable_lam A hA).div_const 100

lemma tsum_floorC_le (A : ℕ) (hA : 1 ≤ A) : ∑' k, floorC A k ≤ 1 / 100 := by
  show ∑' k, lam A k / 100 ≤ 1 / 100
  rw [tsum_div_const]
  have := tsum_lam_le_one A hA
  linarith

lemma one_le_blockLen (A k : ℕ) : 1 ≤ blockLen A k := by
  unfold blockLen
  have : 0 < 21 ^ firstTrial A (k + 1) := by positivity
  omega

lemma depth_nat (A k : ℕ) :
    640000 * blockLen A k * 2 ^ aExp A k ≤ 2 ^ depth A k ∧
      2 ^ depth A k < 2 * (640000 * blockLen A k * 2 ^ aExp A k) := by
  have hN1 : 1 < 640000 * blockLen A k * 2 ^ aExp A k := by
    have := one_le_blockLen A k
    have : 0 < 2 ^ aExp A k := by positivity
    nlinarith
  have hd : depth A k = Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k) := rfl
  rw [hd]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos := Nat.clog_pos (b := 2) (by norm_num) hN1
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
  have e : 2 ^ Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k) =
      2 * 2 ^ (Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k)).pred := by
    rw [← pow_succ']
    exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
  omega

lemma one_le_depth (A k : ℕ) : 1 ≤ depth A k := by
  obtain ⟨h1, _⟩ := depth_nat A k
  rcases Nat.eq_zero_or_pos (depth A k) with h | h
  · rw [h] at h1
    have := one_le_blockLen A k
    have : 0 < 2 ^ aExp A k := by positivity
    nlinarith
  · exact h

/-- The depth choice (Ho (3.2) / (4.5)) with `B = B₀ = 100`, in the exact form used by
`block_lower_floor` and `trial_signal`. -/
lemma depth_spec (A k : ℕ) :
    64 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k ≤ 2 ^ depth A k ∧
      (2 : ℝ) ^ depth A k < 128 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k := by
  obtain ⟨h1, h2⟩ := depth_nat A k
  have hlam : (lam A k)⁻¹ = (2 : ℝ) ^ aExp A k := by unfold lam; rw [inv_pow, inv_inv]
  have e1 : 64 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k =
      ((640000 * blockLen A k * 2 ^ aExp A k : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam]; push_cast; ring
  have e2 : 128 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k =
      ((2 * (640000 * blockLen A k * 2 ^ aExp A k) : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam]; push_cast; ring
  rw [e1, e2]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma firstTrial_strictMono (A : ℕ) : StrictMono (firstTrial A) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  show firstTrial A k < firstTrial A k + nTrials A k
  have : 0 < nTrials A k := by unfold nTrials; positivity
  omega

lemma le_firstTrial (A k : ℕ) : k ≤ firstTrial A k := by
  exact (firstTrial_strictMono A).id_le k

lemma stage_spec (A s : ℕ) :
    firstTrial A (stage A s) ≤ s ∧ s < firstTrial A (stage A s + 1) := by
  have h0 : firstTrial A (stage A s) ≤ s :=
    Nat.findGreatest_spec (P := fun k => firstTrial A k ≤ s) (Nat.zero_le s) (by simp [firstTrial])
  refine ⟨h0, ?_⟩
  by_contra h
  rw [not_lt] at h
  have hle : stage A s + 1 ≤ s := le_trans (le_firstTrial A _) h
  exact Nat.findGreatest_is_greatest (P := fun k => firstTrial A k ≤ s)
    (Nat.lt_succ_self _) hle h

lemma stage_eq (A s k : ℕ) (h1 : firstTrial A k ≤ s) (h2 : s < firstTrial A (k + 1)) :
    stage A s = k := by
  obtain ⟨a1, a2⟩ := stage_spec A s
  have hm := (firstTrial_strictMono A).monotone
  rcases lt_trichotomy (stage A s) k with h | h | h
  · have := hm (show stage A s + 1 ≤ k from h); omega
  · exact h
  · have := hm (show k + 1 ≤ stage A s from h); omega

lemma stage_mono (A : ℕ) : Monotone (stage A) := by
  intro s t hst
  by_contra h
  rw [not_le] at h
  obtain ⟨a1, _⟩ := stage_spec A s
  obtain ⟨_, b2⟩ := stage_spec A t
  have := (firstTrial_strictMono A).monotone (show stage A t + 1 ≤ stage A s from h)
  omega

/-- Every trial of stage `k` is at most `L_k / 8` long. -/
lemma trialLen_le (A s : ℕ) : 8 * trialLen s ≤ blockLen A (stage A s) := by
  unfold trialLen blockLen
  have h1 : s + 1 ≤ firstTrial A (stage A s + 1) := Nat.succ_le_of_lt (stage_spec A s).2
  have h2 : 21 ^ (s + 1) ≤ 21 ^ firstTrial A (stage A s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h2
  omega

lemma shift_mono (A : ℕ) : Monotone (shift A) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show shift A k ≤ shift A k + blockLen A k * spacing A k + depth A k
  omega

lemma trialStart_mono (A : ℕ) : Monotone (trialStart A) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show trialStart A k ≤ trialStart A k + (blockLen A (stage A k) + 2) * spacing A (stage A k)
  omega

/-- Deterministic floor of a block (Ho (3.4) with `C₃ = 1`, `B = 100`). -/
lemma blk_floor (A k : ℕ) (x : 𝕋) : -(floorC A k) ≤ blk A k x := by
  have := block_lower_floor (lam A k) 100 (blockLen A k) (depth A k) (spacing A k) (shift A k)
    (lam_pos A k) (by norm_num) (one_le_blockLen A k) (depth_spec A k).1 x
  unfold blk floorC
  exact this

lemma lt_two_pow_aux (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

lemma firstTrial_le_pow (A k : ℕ) : firstTrial A k ≤ 2 ^ (A * k + k + 24) := by
  induction k with
  | zero => simp [firstTrial]
  | succ k ih =>
    show firstTrial A k + nTrials A k ≤ _
    unfold nTrials aExp
    have h1 : 2 ^ (A * k + k + 24) ≤ 2 ^ (A * (k + 1) + k + 24) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ^ (A * (k + 1) + (k + 1) + 24) = 2 * 2 ^ (A * (k + 1) + k + 24) := by ring
    omega

lemma aExp_le_firstTrial (A k : ℕ) : aExp A k ≤ firstTrial A (k + 1) := by
  show aExp A k ≤ firstTrial A k + nTrials A k
  unfold nTrials
  have h1 := lt_two_pow_aux (aExp A k)
  have h2 : 2 ^ aExp A k ≤ 2 ^ (aExp A k + k + 24) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma depth_le (A k : ℕ) : depth A k ≤ 6 * firstTrial A (k + 1) + 23 := by
  obtain ⟨S, hS⟩ : ∃ S, firstTrial A (k + 1) = S := ⟨_, rfl⟩
  have hL : blockLen A k = 8 * 21 ^ S := by rw [← hS]; rfl
  have ha := aExp_le_firstTrial A k
  rw [hS] at ha ⊢
  apply Nat.clog_le_of_le_pow
  rw [hL]
  have h21 : 21 ^ S ≤ 2 ^ (5 * S) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
  have h2a : 2 ^ aExp A k ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) ha
  have e : 2 ^ (6 * S + 23) = 2 ^ 23 * (2 ^ (5 * S) * 2 ^ S) := by ring
  rw [e]
  have h3 : 21 ^ S * 2 ^ aExp A k ≤ 2 ^ (5 * S) * 2 ^ S := Nat.mul_le_mul h21 h2a
  have e2 : 640000 * (8 * 21 ^ S) * 2 ^ aExp A k = 5120000 * (21 ^ S * 2 ^ aExp A k) := by ring
  rw [e2]
  exact Nat.mul_le_mul (by norm_num) h3

lemma shift_le (A k : ℕ) : shift A k ≤ 2 ^ (6 * firstTrial A k + 10) := by
  induction k with
  | zero => simp [shift]
  | succ k ih =>
    show shift A k + blockLen A k * spacing A k + depth A k ≤ 2 ^ (6 * firstTrial A (k + 1) + 10)
    have hmono : firstTrial A k + 1 ≤ firstTrial A (k + 1) :=
      Nat.succ_le_of_lt (firstTrial_strictMono A (Nat.lt_succ_self k))
    have hd := depth_le A k
    obtain ⟨S, hS⟩ : ∃ S, firstTrial A (k + 1) = S := ⟨_, rfl⟩
    have hL : blockLen A k = 8 * 21 ^ S := by rw [← hS]; rfl
    rw [hS] at hd hmono ⊢
    have hL' : blockLen A k ≤ 2 ^ (5 * S + 3) := by
      rw [hL]
      have h21 : 21 ^ S ≤ 2 ^ (5 * S) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
      have : 2 ^ (5 * S + 3) = 8 * 2 ^ (5 * S) := by ring
      omega
    have hsp : spacing A k = depth A k + 2 := rfl
    have hlin : 12 * S + 48 ≤ 2 ^ (S + 6) := by
      have := lt_two_pow_aux S
      have : 2 ^ (S + 6) = 64 * 2 ^ S := by ring
      omega
    have hb1 := one_le_blockLen A k
    have h1 : blockLen A k * spacing A k + depth A k ≤ blockLen A k * (2 * depth A k + 2) := by
      rw [hsp]; nlinarith
    have h2 : blockLen A k * (2 * depth A k + 2) ≤ 2 ^ (5 * S + 3) * 2 ^ (S + 6) :=
      Nat.mul_le_mul hL' (by omega)
    have h3 : 2 ^ (6 * firstTrial A k + 10) ≤ 2 ^ (6 * S + 4) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (6 * S + 10) = 64 * 2 ^ (6 * S + 4) := by ring
    have e2 : 2 ^ (5 * S + 3) * 2 ^ (S + 6) = 32 * 2 ^ (6 * S + 4) := by ring
    omega

lemma twoLogQ_le (A k : ℕ) : 2 * logQ A k ≤ 2 ^ (2 ^ ((A + 1) * (k + 1) + 30)) := by
  have h1 := shift_le A (k + 1)
  have h2 := firstTrial_le_pow A (k + 1)
  have hq : logQ A k = shift A (k + 1) + 2 := rfl
  have hM : A * (k + 1) + (k + 1) + 24 = (A + 1) * (k + 1) + 24 := by ring
  rw [hM] at h2
  have hpM : 2 ^ ((A + 1) * (k + 1) + 30) = 64 * 2 ^ ((A + 1) * (k + 1) + 24) := by ring
  have hpos : 0 < 2 ^ ((A + 1) * (k + 1) + 24) := by positivity
  have h3 : 6 * firstTrial A (k + 1) + 12 ≤ 2 ^ ((A + 1) * (k + 1) + 30) := by omega
  have h4 : 2 ^ (6 * firstTrial A (k + 1) + 12) ≤ 2 ^ (2 ^ ((A + 1) * (k + 1) + 30)) :=
    Nat.pow_le_pow_right (by norm_num) h3
  have h5 : 2 ^ (6 * firstTrial A (k + 1) + 12) = 4 * 2 ^ (6 * firstTrial A (k + 1) + 10) := by
    ring
  have h6 : 4 ≤ 2 ^ (6 * firstTrial A (k + 1) + 10) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Endpoint scale control, upper half (Ho Lemma 5.1): `log log log (Q_k²) ≤ (A+1)(k+1) + 30`
where `Q_k = 2^{E_k}`. Proof: `S_{k+1} ≤ 2^{a_k+k+25}`, `d_k ≤ 6 S_{k+1} + 23`,
`E_k ≤ 2^{6 S_{k+1} + 11}`, then take three logarithms. -/
lemma scale_bound (A : ℕ) (hA : 1 ≤ A) (k : ℕ) :
    Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * logQ A k)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30 := by
  have hn := twoLogQ_le A k
  have hq2 : 2 ≤ logQ A k := by show 2 ≤ shift A (k + 1) + 2; omega
  obtain ⟨T, hT⟩ : ∃ T, (A + 1) * (k + 1) + 30 = T := ⟨_, rfl⟩
  rw [hT] at hn
  obtain ⟨E, hE0⟩ : ∃ E, 2 * logQ A k = E := ⟨_, rfl⟩
  rw [hE0] at hn
  have hE4 : 4 ≤ E := by omega
  rw [hE0]
  have hlt := Real.log_two_lt_d9
  have hgt := Real.log_two_gt_d9
  have hx1 : Real.log ((2 : ℝ) ^ E) = (E : ℝ) * Real.log 2 := Real.log_pow _ _
  have hE : (E : ℝ) ≤ (2 : ℝ) ^ (2 ^ T) := by
    have := (Nat.cast_le (α := ℝ)).2 hn
    rw [Nat.cast_pow, Nat.cast_ofNat] at this
    exact this
  have hEge : (4 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE4
  have hx1pos : 1 < Real.log ((2 : ℝ) ^ E) := by
    rw [hx1]
    have := mul_le_mul_of_nonneg_right hEge (by linarith : (0 : ℝ) ≤ Real.log 2)
    linarith
  have hx1le : Real.log ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ (2 ^ T) := by
    rw [hx1]
    have : (E : ℝ) * Real.log 2 ≤ (E : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hx2pos : 0 < Real.log (Real.log ((2 : ℝ) ^ E)) := Real.log_pos hx1pos
  have hx2le : Real.log (Real.log ((2 : ℝ) ^ E)) ≤ (2 : ℝ) ^ T := by
    have h1 : Real.log (Real.log ((2 : ℝ) ^ E)) ≤ Real.log ((2 : ℝ) ^ (2 ^ T)) :=
      Real.log_le_log (by linarith) hx1le
    have h2 : Real.log ((2 : ℝ) ^ (2 ^ T)) = ((2 ^ T : ℕ) : ℝ) * Real.log 2 := Real.log_pow _ _
    have h3 : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ T := by push_cast; rfl
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ T := by positivity
    have h5 : (2 : ℝ) ^ T * Real.log 2 ≤ (2 : ℝ) ^ T * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    rw [h2, h3] at h1
    linarith
  have h1 : Real.log (Real.log (Real.log ((2 : ℝ) ^ E))) ≤ Real.log ((2 : ℝ) ^ T) :=
    Real.log_le_log hx2pos hx2le
  have h2 : Real.log ((2 : ℝ) ^ T) = (T : ℝ) * Real.log 2 := Real.log_pow _ _
  have h3 : (T : ℝ) = ((A : ℝ) + 1) * (k + 1) + 30 := by rw [← hT]; push_cast; ring
  have h4 : (T : ℝ) * Real.log 2 ≤ (T : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [h2] at h1
  linarith

end Asm
end Erdos996
