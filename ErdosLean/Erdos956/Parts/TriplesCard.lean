import ErdosLean.Erdos956.Defs

/-!
# Erdős #956 — Part 11: `|triples k| = M_k`

Fibre over `i`: `r ∈ [0, k-i]` (`k+1-i` values) and `s ∈ [i², k²]` (`k²+1-i²` values).

-/

namespace Erdos956

open Finset

lemma altTriplesCard_card_r (k i : ℕ) :
    ((range (k + 1)).filter fun r => r + i ≤ k).card = k + 1 - i := by
  have : (range (k + 1)).filter (fun r => r + i ≤ k) = range (k + 1 - i) := by
    ext r; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

lemma altTriplesCard_card_s (k i : ℕ) :
    ((range (k ^ 2 + 1)).filter fun s => i ^ 2 ≤ s).card = k ^ 2 + 1 - i ^ 2 := by
  have : (range (k ^ 2 + 1)).filter (fun s => i ^ 2 ≤ s) = Ico (i ^ 2) (k ^ 2 + 1) := by
    ext s; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

theorem card_triples (k : ℕ) : (triples k).card = Mk k := by
  unfold triples Mk
  rw [card_filter, sum_product]
  refine sum_congr rfl fun i _ => ?_
  rw [← card_filter]
  have : ((range (k + 1) ×ˢ range (k ^ 2 + 1)).filter
      fun x : ℕ × ℕ => x.1 + i ≤ k ∧ i ^ 2 ≤ x.2) =
      ((range (k + 1)).filter fun r => r + i ≤ k) ×ˢ
        ((range (k ^ 2 + 1)).filter fun s => i ^ 2 ≤ s) := by
    ext ⟨r, s⟩; simp only [mem_filter, mem_product]; tauto
  rw [this, card_product, altTriplesCard_card_r, altTriplesCard_card_s]


end Erdos956
