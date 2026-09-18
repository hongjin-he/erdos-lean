import ErdosLean.Erdos790.Defs

/-! Part: the sorted enumeration `elem` and the rank function `rank` are inverse and monotone. -/

namespace Erdos790

lemma exists_orderEmb_eq (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) :
    ∃ i : Fin A.card, A.orderEmbOfFin rfl i = a := by
  have : a ∈ Set.range (A.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact ha
  exact this

lemma rank_orderEmb (A : Finset ℤ) (i : Fin A.card) :
    rank A (A.orderEmbOfFin rfl i) = i := by
  unfold rank
  have h : A.filter (· < A.orderEmbOfFin rfl i) =
      (Finset.Iio i).map (A.orderEmbOfFin rfl).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, rfl⟩ := exists_orderEmb_eq A hx
      exact ⟨j, (A.orderEmbOfFin rfl).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem A rfl j, (A.orderEmbOfFin rfl).lt_iff_lt.mpr hj⟩
  rw [h, Finset.card_map, Fin.card_Iio]

lemma elem_eq (A : Finset ℤ) (i : Fin A.card) : elem A i = A.orderEmbOfFin rfl i := by
  unfold elem; simp [i.2]

theorem rank_lt_card (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) : rank A a < A.card := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  rw [rank_orderEmb]; exact i.2

theorem elem_rank (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) : elem A (rank A a) = a := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  rw [rank_orderEmb, elem_eq]

theorem rank_lt_rank (A : Finset ℤ) {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    rank A a < rank A b := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  obtain ⟨j, rfl⟩ := exists_orderEmb_eq A hb
  rw [rank_orderEmb, rank_orderEmb]
  exact (A.orderEmbOfFin rfl).lt_iff_lt.mp hab

theorem elem_lt_elem (A : Finset ℤ) {s t : ℕ} (hst : s < t) (ht : t < A.card) :
    elem A s < elem A t := by
  have hs : s < A.card := hst.trans ht
  rw [elem_eq A ⟨s, hs⟩, elem_eq A ⟨t, ht⟩]
  exact (A.orderEmbOfFin rfl).lt_iff_lt.mpr hst

end Erdos790
