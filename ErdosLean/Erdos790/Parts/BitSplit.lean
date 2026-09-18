import ErdosLean.Erdos790.Defs

/-! Part: two indices `i < k < 2^L` are separated by the split point of a common block. -/

namespace Erdos790

/-- For `i < k < 2^L` there is a level `h < L` whose block contains both `i` and `k`
(same split point) with `i < splitPt h i ≤ k`. -/
theorem bit_split (L i k : ℕ) (hik : i < k) (hk : k < 2 ^ L) :
    ∃ h < L, splitPt h i = splitPt h k ∧ i < splitPt h i ∧ splitPt h k ≤ k := by
  have hex : ∃ m, i / 2 ^ m = k / 2 ^ m :=
    ⟨L, by rw [Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (hik.trans hk)]⟩
  classical
  obtain ⟨m, hmspec, hmL, hm0, hmin⟩ : ∃ m, i / 2 ^ m = k / 2 ^ m ∧ m ≤ L ∧ m ≠ 0 ∧
      ∀ j < m, i / 2 ^ j ≠ k / 2 ^ j := by
    refine ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex
      (by rw [Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (hik.trans hk)]), ?_,
      fun j hj => Nat.find_min hex hj⟩
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp at this
    omega
  obtain ⟨h, rfl⟩ : ∃ h, m = h + 1 := ⟨m - 1, by omega⟩
  have hne : i / 2 ^ h ≠ k / 2 ^ h := hmin h (by omega)
  have hpos : 0 < 2 ^ h := by positivity
  set q := i / 2 ^ (h + 1) with hq
  have hi2 : i / 2 ^ h / 2 = q := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hk2 : k / 2 ^ h / 2 = q := by rw [Nat.div_div_eq_div_mul, ← pow_succ, ← hmspec]
  have hle : i / 2 ^ h ≤ k / 2 ^ h := Nat.div_le_div_right hik.le
  have hia : i / 2 ^ h = 2 * q := by omega
  have hka : k / 2 ^ h = 2 * q + 1 := by omega
  have hsp : splitPt h i = (2 * q + 1) * 2 ^ h := by
    unfold splitPt; rw [← hq, pow_succ]; ring
  have hspk : splitPt h k = splitPt h i := by
    unfold splitPt; rw [← hmspec]
  refine ⟨h, by omega, hspk.symm, ?_, ?_⟩
  · rw [hsp]
    exact (Nat.div_lt_iff_lt_mul hpos).1 (by omega)
  · rw [hspk, hsp]
    exact (Nat.le_div_iff_mul_le hpos).1 (by omega)

end Erdos790
