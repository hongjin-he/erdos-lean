import ErdosLean.Erdos956.Defs

/-!
# Erdős #956 — Part 4: `C = D/2` for a symmetric finite generating set

Generic facts about `C = (1/2) • conv S` for a finite set `S` closed under negation, plus the
specialisation to `gens k`.
-/

namespace Erdos956

open Pointwise

section generic

variable {S : Finset E}

lemma half_hull_isCompact : IsCompact ((1 / 2 : ℝ) • convexHull ℝ (S : Set E)) := by
  rw [← Set.image_smul]
  exact (S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image (continuous_const_smul _)

lemma half_hull_convex : Convex ℝ ((1 / 2 : ℝ) • convexHull ℝ (S : Set E)) :=
  (convex_convexHull ℝ _).smul _

lemma half_hull_nonempty (hne : S.Nonempty) :
    ((1 / 2 : ℝ) • convexHull ℝ (S : Set E)).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  exact ⟨(1 / 2 : ℝ) • z, Set.smul_mem_smul_set (subset_convexHull ℝ _ (by simpa using hz))⟩

/-- `C - C ⊆ D` when `S = -S`. -/
lemma sub_mem_hull_of_mem_half (hS : ∀ z ∈ S, -z ∈ S) {c c' : E}
    (hc : c ∈ (1 / 2 : ℝ) • convexHull ℝ (S : Set E))
    (hc' : c' ∈ (1 / 2 : ℝ) • convexHull ℝ (S : Set E)) :
    c - c' ∈ convexHull ℝ (S : Set E) := by
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨y, hy, rfl⟩ := hc'
  have hneg : -y ∈ convexHull ℝ (S : Set E) := by
    have h1 : -y ∈ convexHull ℝ (-(S : Set E)) := by
      rw [convexHull_neg]; simpa [Set.mem_neg] using hy
    refine convexHull_mono ?_ h1
    intro z hz
    have := hS (-z) (by simpa [Set.mem_neg] using hz)
    simpa using this
  have := convex_convexHull ℝ (S : Set E) hx hneg (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  convert this using 1
  simp [smul_neg, sub_eq_add_neg]

lemma half_mem_half_hull {z : E} (hz : z ∈ S) :
    (1 / 2 : ℝ) • z ∈ (1 / 2 : ℝ) • convexHull ℝ (S : Set E) :=
  Set.smul_mem_smul_set (subset_convexHull ℝ _ (by simpa using hz))

end generic

lemma neg_mem_gens {k : ℕ} {z : E} (hz : z ∈ gens k) : -z ∈ gens k := by
  unfold gens at *
  simp only [Finset.mem_union, Finset.mem_image] at *
  rcases hz with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact Or.inr ⟨i, hi, rfl⟩
  · exact Or.inl ⟨i, hi, (neg_neg _).symm⟩

lemma pp_mem_gens {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) : pp (η k) (i * a k) ∈ gens k := by
  unfold gens
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hik⟩, rfl⟩)

lemma gens_nonempty {k : ℕ} (hk : 1 ≤ k) : (gens k).Nonempty :=
  ⟨_, pp_mem_gens le_rfl hk⟩

lemma C_isCompact (k : ℕ) : IsCompact (C k) := half_hull_isCompact
lemma C_convex (k : ℕ) : Convex ℝ (C k) := half_hull_convex
lemma C_nonempty {k : ℕ} (hk : 1 ≤ k) : (C k).Nonempty := half_hull_nonempty (gens_nonempty hk)

lemma sub_mem_D {k : ℕ} {c c' : E} (hc : c ∈ C k) (hc' : c' ∈ C k) : c - c' ∈ D k :=
  sub_mem_hull_of_mem_half (fun _ hz => neg_mem_gens hz) hc hc'

end Erdos956
