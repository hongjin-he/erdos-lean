import ErdosLean.Erdos956.Statement

/-!
# Erdős #956 — Part 15: `h` is an honest maximum

The achievable counts for size `n` are bounded by `|X.sym2| = n(n+1)/2`, so `le_csSup` applies.

-/

namespace Erdos956

theorem le_h {C : Set E} {X : Finset E} (hX : Admissible C X) :
    (unitPairs C X).card ≤ h X.card := by
  classical
  unfold h
  apply le_csSup
  · refine ⟨(X.card + 1).choose 2, ?_⟩
    rintro m ⟨C', X', hcard, -, rfl⟩
    rw [← hcard, ← Finset.card_sym2]
    unfold unitPairs
    exact Finset.card_filter_le _ _
  · exact ⟨C, X, rfl, hX, rfl⟩

end Erdos956
