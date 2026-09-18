import ErdosLean.Erdos996.Parts.Asm.Params

/-!
# Assembly sub-lemma 2 (Sequence): the exponent sequence

Blueprint §3. Ho §4 (4.10)–(4.13) and the lacunarity part of Prop. 4.3.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma trialOf_trial (s r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ trialLen s) :
    trialOf (21 ^ s + r - 2) = s := by
  unfold trialOf
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  unfold trialLen at hr2
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]; omega

/-- Every global index is the `r`-th exponent of some trial. -/
lemma exists_trial (j : ℕ) : ∃ s r, 1 ≤ r ∧ r ≤ trialLen s ∧ j = 21 ^ s + r - 2 := by
  have h1 := Nat.pow_log_le_self 21 (by omega : j + 1 ≠ 0)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 21) (j + 1)
  rw [Nat.pow_succ] at h2
  refine ⟨Nat.log 21 (j + 1), j + 2 - 21 ^ Nat.log 21 (j + 1), ?_, ?_, ?_⟩
  · omega
  · unfold trialLen; omega
  · omega

/-- The `r`-th exponent of trial `s` sits at global index `21^s + r - 2`. -/
lemma mExp_trial (A s r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ trialLen s) :
    mExp A (21 ^ s + r - 2) = trialStart A s + r * spacing A (stage A s) := by
  unfold mExp
  rw [trialOf_trial s r hr1 hr2]
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have : 21 ^ s + r - 2 + 2 - 21 ^ s = r := by omega
  rw [this]

lemma mExp_strictMono (A : ℕ) : StrictMono (mExp A) := by
  apply strictMono_nat_of_lt_succ
  intro j
  obtain ⟨s, r, h1, h2, rfl⟩ := exists_trial j
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  by_cases hr : r < trialLen s
  · have e : 21 ^ s + r - 2 + 1 = 21 ^ s + (r + 1) - 2 := by omega
    rw [e, mExp_trial A s (r + 1) (by omega) hr, mExp_trial A s r h1 h2, add_mul, one_mul]
    have : 0 < spacing A (stage A s) := by unfold spacing; omega
    omega
  · have hr' : r = trialLen s := by omega
    have e : 21 ^ s + r - 2 + 1 = 21 ^ (s + 1) + 1 - 2 := by
      rw [pow_succ]; unfold trialLen at hr'; omega
    have hlen : 1 ≤ trialLen (s + 1) := by
      unfold trialLen; have := Nat.one_le_pow (s + 1) 21 (by norm_num); omega
    rw [e, mExp_trial A (s + 1) 1 le_rfl hlen, mExp_trial A s r h1 h2, trialStart]
    have hL := trialLen_le A s
    have hm : r * spacing A (stage A s) ≤
        (blockLen A (stage A s) + 2) * spacing A (stage A s) :=
      Nat.mul_le_mul_right _ (by omega)
    have : 0 < spacing A (stage A (s + 1)) := by unfold spacing; omega
    omega

lemma isDyadicLacunary_nSeq (A : ℕ) : IsDyadicLacunary (nSeq A) := by
  refine ⟨Nat.one_le_pow _ _ (by norm_num), fun k => ?_⟩
  unfold nSeq
  have h := mExp_strictMono A (Nat.lt_succ_self k)
  calc 2 * 2 ^ mExp A k = 2 ^ (mExp A k + 1) := by ring
    _ ≤ 2 ^ mExp A (k + 1) := Nat.pow_le_pow_right (by norm_num) h

end Asm
end Erdos996
