import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: degree formula in the blow-up

A vertex in clump `(ℓ, j)` is adjacent exactly to the vertices of the other clumps in layers
`ℓ - 1, ℓ, ℓ + 1`, so its degree plus its own clump weight is `nbr ℓ`.

Proof plan: `neighborFinset v = (univ.filter fun c => c ≠ v.1 ∧ near).sigma fun _ => univ`;
`card_sigma`; split the clump sum by layer and use `card`-of-clumps-in-layer `= tot`.
-/

open SimpleGraph Finset

namespace Erdos612

/-- Total weight of a layer as a sum over its clumps. -/
lemma tot_eq_sum_wt (L : Layers) (ℓ : ℕ) :
    L.tot ℓ = ∑ j : Fin (L.cnt ℓ), L.wt ℓ j := by
  unfold Layers.tot Layers.wt Layers.cnt
  rw [← Fin.sum_univ_getElem]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.getD_eq_getElem]

lemma tot_eq_zero_of_ge (L : Layers) {ℓ : ℕ} (h : L.length ≤ ℓ) : L.tot ℓ = 0 := by
  unfold Layers.tot Layers.lay
  rw [List.getD_eq_default _ _ h]
  rfl

/-- Sum of the layer totals over layers `ℓ' < L.length` with `|ℓ' - ℓ| ≤ 1`. -/
lemma sum_near_tot (L : Layers) (ℓ : ℕ) :
    ∑ i ∈ (range L.length).filter (fun i => i ≤ ℓ + 1 ∧ ℓ ≤ i + 1), L.tot i = L.nbr ℓ := by
  have hsub : (range L.length).filter (fun i => i ≤ ℓ + 1 ∧ ℓ ≤ i + 1) ⊆ Icc (ℓ - 1) (ℓ + 1) := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    simp only [mem_Icc]; omega
  rw [Finset.sum_subset hsub]
  · unfold Layers.nbr
    rcases ℓ with _ | k
    · have : Icc (0 - 1) (0 + 1) = {0, 1} := by decide
      rw [this, sum_pair (by decide)]
      simp [Layers.lft]
    · have : Icc (k + 1 - 1) (k + 1 + 1) = {k, k + 1, k + 2} := by
        ext i; simp only [mem_Icc, mem_insert, mem_singleton]; omega
      rw [this, sum_insert (by simp), sum_pair (by omega)]
      have : (L.lft (k + 1)).sum = L.tot k := by
        simp [Layers.lft, Layers.tot, Layers.lay]
      rw [this]; ring
  · intro i hi hni
    apply tot_eq_zero_of_ge
    simp only [mem_Icc] at hi
    simp only [mem_filter, mem_range, not_and] at hni
    by_contra hlt
    exact absurd (hni (by omega)) (by omega)

theorem degree_add_wt (L : Layers) (v : Vtx L) :
    (blowup L).degree v + L.wt v.1.1 v.1.2 = L.nbr v.1.1 := by
  set S : Finset (Clump L) := univ.filter
    (fun c => c.1.val ≤ v.1.1.val + 1 ∧ v.1.1.val ≤ c.1.val + 1) with hS
  have hN : (blowup L).neighborFinset v = (S.erase v.1).sigma (fun _ => univ) := by
    ext u
    rw [mem_neighborFinset]
    simp only [blowup, Vtx.layer, mem_sigma, mem_erase, hS, mem_filter,
      mem_univ, true_and, and_true]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨Ne.symm h1, h3, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨Ne.symm h1, h3, h2⟩
  have hv : v.1 ∈ S := by simp [hS]
  rw [← card_neighborFinset_eq_degree, hN, card_sigma]
  simp only [card_univ, Fintype.card_fin]
  rw [sum_erase_add _ _ hv, hS, sum_filter, Fintype.sum_sigma]
  have : ∀ a : Fin L.length,
      (∑ b : Fin (L.cnt a), if (a.val ≤ v.1.1.val + 1 ∧ v.1.1.val ≤ a.val + 1)
        then L.wt a b else 0) =
      if (a.val ≤ v.1.1.val + 1 ∧ v.1.1.val ≤ a.val + 1) then L.tot a else 0 := by
    intro a
    split_ifs
    · exact (tot_eq_sum_wt L a).symm
    · simp
  simp only [this]
  rw [← sum_near_tot, sum_filter]
  exact Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ v.1.1.val + 1 ∧ v.1.1.val ≤ i + 1 then L.tot i else 0) L.length

end Erdos612
