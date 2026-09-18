import ErdosLean.Erdos790.Defs
import ErdosLean.Erdos790.Parts.BitSplit
import ErdosLean.Erdos790.Parts.RankElem

/-! Part: Korsky's Lemma 2 (distance lists) and the size bound `|D(a)| ≤ ⌈log₂ n⌉`. -/

namespace Erdos790

private theorem mem_Dset_of (A : Finset ℤ) (a : ℤ) {h : ℕ} (hL : h < Nat.clog 2 A.card)
    (hs : splitPt h (rank A a) < A.card) :
    |elem A (splitPt h (rank A a)) - a| ∈ Dset A a := by
  unfold Dset
  exact Finset.mem_image.2 ⟨h, Finset.mem_filter.2 ⟨Finset.mem_range.2 hL, hs⟩, rfl⟩

/-- Lemma 2: for `a < b` in `A`, some `δ ∈ D(a) ∪ D(b)` satisfies `(b - a)/2 ≤ δ ≤ b - a`. -/
theorem distance_lists (A : Finset ℤ) {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    ∃ δ, (δ ∈ Dset A a ∨ δ ∈ Dset A b) ∧ b - a ≤ 2 * δ ∧ δ ≤ b - a := by
  have hik := rank_lt_rank A ha hb hab
  have hkn := rank_lt_card A hb
  have hk : rank A b < 2 ^ Nat.clog 2 A.card :=
    lt_of_lt_of_le hkn (Nat.le_pow_clog (by norm_num) _)
  obtain ⟨h, hL, heq, his, hsk⟩ := bit_split _ _ _ hik hk
  have hsn : splitPt h (rank A b) < A.card := lt_of_le_of_lt hsk hkn
  have hsn' : splitPt h (rank A a) < A.card := heq ▸ hsn
  set e := elem A (splitPt h (rank A b)) with he
  have hae : a < e := by
    have := elem_lt_elem A (heq ▸ his) hsn
    rwa [elem_rank A ha] at this
  have heb : e ≤ b := by
    rcases lt_or_eq_of_le hsk with hlt | heq2
    · have := elem_lt_elem A hlt hkn
      rw [elem_rank A hb] at this; exact this.le
    · rw [he, heq2, elem_rank A hb]
  have hDa : |e - a| ∈ Dset A a := by
    have := mem_Dset_of A a hL hsn'
    rwa [heq] at this
  have hDb : |e - b| ∈ Dset A b := mem_Dset_of A b hL hsn
  rw [abs_of_pos (by linarith)] at hDa
  rw [abs_of_nonpos (by linarith)] at hDb
  by_cases hc : b - a ≤ 2 * (e - a)
  · exact ⟨e - a, Or.inl hDa, hc, by linarith⟩
  · exact ⟨-(e - b), Or.inr hDb, by linarith, by linarith⟩

theorem card_Dset_le (A : Finset ℤ) (a : ℤ) : (Dset A a).card ≤ Nat.clog 2 A.card := by
  unfold Dset
  refine Finset.card_image_le.trans ?_
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

end Erdos790
