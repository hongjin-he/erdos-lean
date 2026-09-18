import ErdosLean.Erdos956Upper.Parts.SetDistFormula
import ErdosLean.Erdos956Upper.Parts.Orientation

/-!
# Erdős #956 upper bound — P5: splitting the unit pairs

Each unordered unit pair `{x, y}` has an orientation `(x, y)` with `y - x` on the upper arc or on the right side.
-/

namespace Erdos956Upper

open Erdos956 Metric

theorem unitPairs_card_le {C : Set E} {X : Finset E} (h : Admissible C X) :
    (unitPairs C X).card ≤
      (upperPairs (diffSet C) X).card + (sidePairs (diffSet C) X).card := by
  classical
  have hS := admissible_sepConfig h
  have hC : C.Nonempty := h.2.2.1
  have hsub : unitPairs C X ⊆
      (upperPairs (diffSet C) X ∪ sidePairs (diffSet C) X).image
        (fun q : E × E => s(q.1, q.2)) := by
    intro z hz
    simp only [unitPairs, Finset.mem_filter] at hz
    obtain ⟨hzX, x, y, rfl, hxy, hd⟩ := hz
    rw [Finset.mem_sym2_iff] at hzX
    have hx : x ∈ X := hzX x (Sym2.mem_mk_left x y)
    have hy : y ∈ X := hzX y (Sym2.mem_mk_right x y)
    rw [setDist_translate_eq_infDist hC] at hd
    have hneg : -(y - x) = x - y := by abel
    rw [Finset.mem_image]
    rcases unit_orientation hS hd with h1 | h1 | h1 | h1
    · refine ⟨(x, y), ?_, rfl⟩
      simp only [Finset.mem_union, sidePairs, upperPairs, Finset.mem_filter,
        Finset.mem_product]
      exact Or.inr ⟨⟨hx, hy⟩, hxy, h1⟩
    · rw [hneg] at h1
      refine ⟨(y, x), ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_union, sidePairs, upperPairs, Finset.mem_filter,
        Finset.mem_product]
      exact Or.inr ⟨⟨hy, hx⟩, Ne.symm hxy, h1⟩
    · refine ⟨(x, y), ?_, rfl⟩
      simp only [Finset.mem_union, sidePairs, upperPairs, Finset.mem_filter,
        Finset.mem_product]
      exact Or.inl ⟨⟨hx, hy⟩, hxy, h1⟩
    · rw [hneg] at h1
      refine ⟨(y, x), ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_union, sidePairs, upperPairs, Finset.mem_filter,
        Finset.mem_product]
      exact Or.inl ⟨⟨hy, hx⟩, Ne.symm hxy, h1⟩
  calc (unitPairs C X).card
      ≤ ((upperPairs (diffSet C) X ∪ sidePairs (diffSet C) X).image
          (fun q : E × E => s(q.1, q.2))).card := Finset.card_le_card hsub
    _ ≤ (upperPairs (diffSet C) X ∪ sidePairs (diffSet C) X).card := Finset.card_image_le
    _ ≤ _ := Finset.card_union_le _ _

end Erdos956Upper
