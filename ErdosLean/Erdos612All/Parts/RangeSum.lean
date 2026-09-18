import ErdosLean.Erdos612All.Defs

/-!
# Erdős 612 (all `r`), part: total weight of `(List.range N).map G`
-/

namespace Erdos612All

open Erdos612

theorem total_map_range (N : ℕ) (G : ℕ → List ℕ) :
    Layers.total ((List.range N).map G) = ∑ m ∈ Finset.range N, (G m).sum := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [Layers.total, List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp

/-- Group a sum over `range (3n)` into consecutive triples. -/
theorem sum_range_three (n : ℕ) (f : ℕ → ℕ) :
    ∑ m ∈ Finset.range (3 * n), f m = ∑ j ∈ Finset.range n, (f (3 * j) + f (3 * j + 1) + f (3 * j + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

end Erdos612All
