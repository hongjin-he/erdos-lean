import ErdosLean.Erdos996.Parts.Asm.Construction

/-!
# Assembly sub-lemma 4 (HitWindow): spike events are digit-window events

Blueprint §4. Ho, proof of Lemma 2.1: `φ_d(2^v x)` depends only on the binary digits
`v+1, …, v+d` of `x` (digit `j` in the convention of `DeterminedByWindow` is
`fract(2^j x) < 1/2`, for `v ≤ j < v + d`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- `z ↦ z mod 1` lands in `[0, c)` iff the fractional part of `z` is below `c`. -/
lemma coe_mem_image_Ico_iff (z c : ℝ) (hc : c ≤ 1) :
    ((z : 𝕋) ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) c : Set 𝕋)) ↔ Int.fract z < c := by
  constructor
  · rintro ⟨w, hw, h⟩
    have h1 : ((w : ℝ) : 𝕋) = ((Int.fract z : ℝ) : 𝕋) := by
      rw [AddCircle.coe_fract]; exact h
    have hw' : w ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hw.1, by linarith [hw.2]⟩
    have hf' : Int.fract z ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg z, by simpa using Int.fract_lt_one z⟩
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hw' hf').1 h1
    rw [← this]; exact hw.2
  · intro h
    exact ⟨Int.fract z, ⟨Int.fract_nonneg z, h⟩, AddCircle.coe_fract z⟩

lemma fract_lt_two_inv_pow_succ (z : ℝ) (d : ℕ) :
    Int.fract z < (2 : ℝ)⁻¹ ^ (d + 1) ↔
      Int.fract z < 2⁻¹ ∧ Int.fract (2 * z) < (2 : ℝ)⁻¹ ^ d := by
  have hpow : (2 : ℝ)⁻¹ ^ (d + 1) = 2⁻¹ * (2 : ℝ)⁻¹ ^ d := by rw [pow_succ]; ring
  have hle : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  by_cases hf : Int.fract z < 2⁻¹
  · have h2 : Int.fract (2 * z) = 2 * Int.fract z := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [Int.fract_nonneg z], by linarith, 2 * ⌊z⌋, ?_⟩
      rw [Int.fract]; push_cast; ring
    rw [h2, hpow]
    constructor
    · intro h; exact ⟨hf, by linarith⟩
    · rintro ⟨-, h⟩; linarith
  · constructor
    · intro h; exfalso; apply hf; rw [hpow] at h; nlinarith
    · rintro ⟨h, -⟩; exact absurd h hf

/-- `fract z < 2^{-d}` iff the first `d` binary digits of `z` vanish. -/
lemma fract_lt_two_inv_pow_iff (d : ℕ) : ∀ z : ℝ,
    Int.fract z < (2 : ℝ)⁻¹ ^ d ↔ ∀ i < d, Int.fract ((2 : ℝ) ^ i * z) < 2⁻¹ := by
  induction d with
  | zero =>
    intro z
    simp only [pow_zero, Nat.not_lt_zero, false_imp_iff, implies_true, iff_true]
    exact Int.fract_lt_one z
  | succ d ih =>
    intro z
    rw [fract_lt_two_inv_pow_succ, ih (2 * z)]
    constructor
    · rintro ⟨h0, h⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := h i (by omega)
        rw [pow_succ, mul_assoc]; exact this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rw [pow_succ, mul_assoc] at this; exact this

lemma mem_hitSet_iff (d v : ℕ) (x : 𝕋) :
    x ∈ hitSet d v ↔ ∀ j, v ≤ j → j < v + d →
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ := by
  set y : ℝ := (AddCircle.equivIco 1 0 x : ℝ)
  have hx : ((y : ℝ) : 𝕋) = x := AddCircle.coe_equivIco
  have hsmul : (2 ^ v : ℕ) • x = (((2 : ℝ) ^ v * y : ℝ) : 𝕋) := by
    rw [← hx, ← AddCircle.coe_nsmul, nsmul_eq_mul]; push_cast; rfl
  simp only [hitSet, spikeSet, Set.mem_ofPred_eq]
  rw [hsmul, coe_mem_image_Ico_iff _ _ (pow_le_one₀ (by norm_num) (by norm_num)),
    fract_lt_two_inv_pow_iff]
  constructor
  · intro h j hj1 hj2
    have := h (j - v) (by omega)
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj1] at this
    exact this
  · intro h i hi
    rw [← mul_assoc, ← pow_add]
    exact h (i + v) (by omega) (by omega)

lemma determinedByWindow_hitSet (d v : ℕ) : DeterminedByWindow v (v + d) (hitSet d v) := by
  intro x y h
  rw [mem_hitSet_iff, mem_hitSet_iff]
  constructor
  · intro hx j hj1 hj2; exact (h j).1 (fun _ _ => hx j hj1 hj2)
  · intro hy j hj1 hj2; exact (h j).2 (hy j hj1 hj2) hj1 hj2

lemma DeterminedByWindow.compl' {a b : ℕ} {E : Set 𝕋} (h : DeterminedByWindow a b E) :
    DeterminedByWindow a b Eᶜ := by
  intro x y hxy
  exact not_congr (h x y hxy)

end Asm
end Erdos996
