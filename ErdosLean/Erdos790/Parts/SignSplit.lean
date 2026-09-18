import ErdosLean.Erdos790.Defs

/-! Part: reduction to positive sets (one sign class has a quarter of the elements;
negation preserves sum-freeness). -/

namespace Erdos790

theorem sign_split (A : Finset ℤ) (hA : 2 ≤ A.card) :
    A.card ≤ 4 * (A.filter (fun x => 0 < x)).card ∨
      A.card ≤ 4 * (A.filter (fun x => x < 0)).card := by
  have hsub : A ⊆ insert 0 (A.filter (fun x => 0 < x) ∪ A.filter (fun x => x < 0)) := by
    intro x hx
    rcases lt_trichotomy x 0 with h | h | h
    · simp [hx, h]
    · simp [h]
    · simp [hx, h]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le (0 : ℤ)
    (A.filter (fun x => 0 < x) ∪ A.filter (fun x => x < 0))
  have h3 := Finset.card_union_le (A.filter (fun x => 0 < x)) (A.filter (fun x => x < 0))
  omega

theorem isSumFree_image_neg {B : Finset ℤ} (hB : IsSumFree B) :
    IsSumFree (B.image (fun x => -x)) := by
  intro x hx S hS hxS hcard hsum
  have hinj : Function.Injective (fun x : ℤ => -x) := neg_injective
  refine hB (-x) ?_ (S.image (fun x => -x)) ?_ ?_ ?_ ?_
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hS hz)
    simpa using hw
  · intro h
    obtain ⟨z, hz, hz'⟩ := Finset.mem_image.mp h
    have : z = x := by simpa using hz'
    exact hxS (this ▸ hz)
  · rwa [Finset.card_image_of_injective _ hinj]
  · rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_neg_distrib, hsum]

end Erdos790
