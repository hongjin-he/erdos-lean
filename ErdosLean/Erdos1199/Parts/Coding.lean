import ErdosLean.Erdos1199.Defs

/-!
# Erdős #1199 — Part 8: asymptotic binary coding

Paper: arXiv:2607.17333, Lemma 2.10, eq. (2.6) (`p h = π_H(p x)` at coordinate `0`).
-/

namespace Erdos1199

open Filter

/-- If `G` depends only on the coordinates in `F`, then `h n = G (Tⁿ x)` satisfies
`{n | h n} ∈ q ↔ G (q · x)` for every ultrafilter `q`. -/
theorem coding (G : Pt → Bool) (F : Finset Idx)
    (hF : ∀ u v : Pt, (∀ i ∈ F, u i = v i) → G u = G v) (x : Pt) (q : Ultrafilter ℕ) :
    {n : ℕ | G (act (pure n) x) = true} ∈ q ↔ G (act q x) = true := by
  classical
  set W : Set ℕ := {n | ∀ i ∈ F, act (pure n) x i = act q x i} with hWdef
  have hW : W ∈ q := by
    have : W = ⋂ i ∈ F, {n : ℕ | act (pure n) x i = act q x i} := by
      ext n; simp [hWdef]
    rw [this]
    show _ ∈ (q : Filter ℕ)
    rw [Filter.biInter_finset_mem F]
    intro i _
    by_cases hA : {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ q
    · refine Filter.mem_of_superset hA ?_
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      simp only [act, Ultrafilter.mem_pure, Set.mem_ofPred_eq, hn, hA, decide_true]
    · have hc := (Ultrafilter.compl_mem_iff_notMem).2 hA
      refine Filter.mem_of_superset hc ?_
      intro n hn
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hn ⊢
      simp only [act, Ultrafilter.mem_pure, Set.mem_ofPred_eq, hn, hA, decide_false, Bool.false_eq_true, decide_false]
  have hEq : ∀ n ∈ W, G (act (pure n) x) = G (act q x) := fun n hn => hF _ _ hn
  constructor
  · intro hS
    obtain ⟨n, hn1, hn2⟩ := (q.inter_mem hS hW |> Ultrafilter.nonempty_of_mem)
    rw [← hEq n hn2]; exact hn1
  · intro hG
    refine Filter.mem_of_superset hW ?_
    intro n hn
    simp only [Set.mem_ofPred_eq]
    rw [hEq n hn]; exact hG

end Erdos1199
