import ErdosLean.Erdos612All.Defs

/-!
# Erdős 612 (all `r`), part: windows of `(List.range N).map G`

Generic bookkeeping: layers, left layers and three-layer windows of a layer sequence given by
an index function, and concatenation of two such sequences.
-/

namespace Erdos612All

open Erdos612

theorem lay_map_range (N : ℕ) (G : ℕ → List ℕ) (ℓ : ℕ) :
    Layers.lay ((List.range N).map G) ℓ = if ℓ < N then G ℓ else [] := by
  simp only [Layers.lay, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using (not_lt.mp h))]
    rfl

theorem lft_map_range (N : ℕ) (G : ℕ → List ℕ) (ℓ : ℕ) :
    Layers.lft ((List.range N).map G) ℓ =
      if ℓ = 0 then [] else if ℓ ≤ N then G (ℓ - 1) else [] := by
  rcases ℓ with _ | i
  · rfl
  · simp only [Layers.lft, List.getD_cons_succ, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    have := lay_map_range N G i
    simp only [Layers.lay] at this
    rw [this]
    split_ifs <;> first | rfl | omega

theorem allWin_map_range {Q : List ℕ → List ℕ → List ℕ → Prop} (N : ℕ) (G : ℕ → List ℕ) :
    AllWin Q ((List.range N).map G) ↔
      ∀ ℓ, ℓ < N → Q (if ℓ = 0 then [] else G (ℓ - 1)) (G ℓ)
        (if ℓ + 1 < N then G (ℓ + 1) else []) := by
  unfold AllWin
  simp only [List.length_map, List.length_range, lay_map_range, lft_map_range]
  refine forall_congr' fun ℓ => imp_congr_right fun h => ?_
  by_cases h0 : ℓ = 0
  · subst h0; simp [h]
  · simp [h0, h, h.le]

theorem someWin_map_range {Q : List ℕ → List ℕ → List ℕ → Prop} (N : ℕ) (G : ℕ → List ℕ) :
    SomeWin Q ((List.range N).map G) ↔
      ∃ ℓ, ℓ < N ∧ Q (if ℓ = 0 then [] else G (ℓ - 1)) (G ℓ)
        (if ℓ + 1 < N then G (ℓ + 1) else []) := by
  unfold SomeWin
  simp only [List.length_map, List.length_range, lay_map_range, lft_map_range]
  refine exists_congr fun ℓ => and_congr_right fun h => ?_
  by_cases h0 : ℓ = 0
  · subst h0; simp [h]
  · simp [h0, h, h.le]

theorem map_range_append (a b : ℕ) (F H : ℕ → List ℕ) :
    (List.range a).map F ++ (List.range b).map H =
      (List.range (a + b)).map (fun ℓ => if ℓ < a then F ℓ else H (ℓ - a)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_append, List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range]
    by_cases hi : i < a
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [hi]

end Erdos612All
