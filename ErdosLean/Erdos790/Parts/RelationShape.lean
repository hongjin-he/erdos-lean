import ErdosLean.Erdos790.Defs

/-! Part: the shape of an additive relation `x = ∑ S` among positive integers
(`b₁` the largest summand, `z` the second largest). -/

namespace Erdos790

theorem relation_shape (S : Finset ℤ) (hpos : ∀ s ∈ S, 0 < s) (h2 : 2 ≤ S.card) (x : ℤ)
    (hsum : ∑ s ∈ S, s = x) :
    ∃ b₁ ∈ S, ∃ z ∈ S, 0 < z ∧ z < b₁ ∧ b₁ + z ≤ x ∧ z ≤ x - b₁ ∧
      x - b₁ ≤ (S.card : ℤ) * z ∧ x ≤ (S.card : ℤ) * b₁ := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  set b₁ := S.max' hS with hb₁def
  have hb₁ : b₁ ∈ S := S.max'_mem hS
  set T := S.erase b₁ with hTdef
  have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem hb₁
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  set z := T.max' hT with hzdef
  have hzT : z ∈ T := T.max'_mem hT
  have hzS : z ∈ S := Finset.mem_of_mem_erase hzT
  have hzne : z ≠ b₁ := Finset.ne_of_mem_erase hzT
  have hzle : z ≤ b₁ := S.le_max' z hzS
  have hzlt : z < b₁ := lt_of_le_of_ne hzle hzne
  have hzpos : 0 < z := hpos z hzS
  have hsplit : b₁ + ∑ s ∈ T, s = x := by
    rw [hTdef, Finset.add_sum_erase S (fun s => s) hb₁]; exact hsum
  have hTle : ∑ s ∈ T, s ≤ (T.card : ℤ) * z := by
    have := Finset.sum_le_card_nsmul T (fun s => s) z (fun s hs => T.le_max' s hs)
    simpa [nsmul_eq_mul] using this
  have hTge : z ≤ ∑ s ∈ T, s := by
    have := Finset.single_le_sum (f := fun s => s)
      (fun s hs => le_of_lt (hpos s (Finset.mem_of_mem_erase hs))) hzT
    simpa using this
  have hSle : ∑ s ∈ S, s ≤ (S.card : ℤ) * b₁ := by
    have := Finset.sum_le_card_nsmul S (fun s => s) b₁ (fun s hs => S.le_max' s hs)
    simpa [nsmul_eq_mul] using this
  have hcardT : (T.card : ℤ) ≤ S.card := by exact_mod_cast (by omega : T.card ≤ S.card)
  refine ⟨b₁, hb₁, z, hzS, hzpos, hzlt, by linarith, by linarith, ?_, by linarith⟩
  have : (T.card : ℤ) * z ≤ (S.card : ℤ) * z :=
    mul_le_mul_of_nonneg_right hcardT hzpos.le
  linarith

end Erdos790
