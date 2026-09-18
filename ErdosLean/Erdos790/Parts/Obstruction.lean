import ErdosLean.Erdos790.Defs
import ErdosLean.Erdos790.Parts.Dyadic
import ErdosLean.Erdos790.Parts.DistanceLists
import ErdosLean.Erdos790.Parts.RelationShape
import ErdosLean.Erdos790.Parts.Window

/-! Part: every additive relation inside a positive set `A` hits a forbidden index:
the dyadic index of its second largest summand lies in `F(a)` for `a` the sum or the largest
summand (Korsky, proof of Theorem 1, two cases). -/

namespace Erdos790

private theorem mem_Fset_of (A : Finset ℤ) {a z δ : ℤ} (hzA : z ∈ A) (hz : 0 < z)
    (hδ : δ ∈ Dplus A a) (h1 : δ ≤ 2 * (A.card : ℤ) * z) (h2 : z ≤ 2 * δ)
    (hne : dyIdx z ≠ dyIdx a) : dyIdx z ∈ Fset A a := by
  unfold Fset
  rw [Finset.mem_erase]
  exact ⟨hne, Finset.mem_biUnion.2 ⟨δ, hδ, mem_window_of A A.card hzA hz h1 h2⟩⟩

theorem obstruction (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) {x : ℤ} (hx : x ∈ A)
    {S : Finset ℤ} (hS : S ⊆ A) (hxS : x ∉ S) (h2 : 2 ≤ S.card) (hsum : ∑ s ∈ S, s = x) :
    ∃ z ∈ S, ∃ a, (a = x ∨ a ∈ S) ∧ dyIdx z ∈ Fset A a := by
  obtain ⟨b₁, hb₁, z, hzS, hz, hzb, hbz, hzd, hdz, hxb⟩ :=
    relation_shape S (fun s hs => hpos s (hS hs)) h2 x hsum
  have hcard : (S.card : ℤ) ≤ A.card := by exact_mod_cast Finset.card_le_card hS
  have hzA := hS hzS
  have hbA := hS hb₁
  have hb0 : 0 < b₁ := lt_trans hz hzb
  have hzx : 2 * z < x := by linarith
  have hdx : dyIdx z ≠ dyIdx x := (dyIdx_lt_of_two_mul_lt hz hzx).ne
  refine ⟨z, hzS, ?_⟩
  by_cases hcase : dyIdx b₁ = dyIdx z
  · have hb2 := lt_two_mul_of_dyIdx_eq hz hb0 hcase
    refine ⟨x, Or.inl rfl, mem_Fset_of A hzA hz (Finset.mem_insert_self _ _) ?_ (by linarith) hdx⟩
    have : (S.card : ℤ) * b₁ ≤ (A.card : ℤ) * (2 * z) :=
      mul_le_mul hcard hb2.le hb0.le (by positivity)
    linarith
  · have hbx : b₁ < x := by linarith
    obtain ⟨δ, hδ, hd1, hd2⟩ := distance_lists A hbA hx hbx
    have hNz : (S.card : ℤ) * z ≤ (A.card : ℤ) * z := mul_le_mul_of_nonneg_right hcard hz.le
    have hw1 : δ ≤ 2 * (A.card : ℤ) * z := by nlinarith
    have hw2 : z ≤ 2 * δ := by linarith
    rcases hδ with hδ | hδ
    · exact ⟨b₁, Or.inr hb₁, mem_Fset_of A hzA hz (Finset.mem_insert_of_mem hδ) hw1 hw2
        (Ne.symm hcase)⟩
    · exact ⟨x, Or.inl rfl, mem_Fset_of A hzA hz (Finset.mem_insert_of_mem hδ) hw1 hw2 hdx⟩

end Erdos790
