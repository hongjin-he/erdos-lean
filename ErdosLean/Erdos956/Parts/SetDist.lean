import ErdosLean.Erdos956.Statement

/-!
# Erdős #956 — Part 8: set distance and disjointness of translates (note, (1)–(2))

`(c + x) - (c' + y) = -((y - x) - (c - c'))`, so both facts reduce to the difference vector
`y - x` versus `C - C`.
-/

namespace Erdos956

lemma altSetDist_translate_sub_norm (c c' x y : E) :
    ‖(c + x) - (c' + y)‖ = ‖(y - x) - (c - c')‖ := by
  rw [← norm_neg]
  congr 1
  abel

lemma translate_disjoint {C : Set E} {x y : E}
    (h : ∀ c ∈ C, ∀ c' ∈ C, c - c' ≠ y - x) : Disjoint (translate C x) (translate C y) := by
  rw [Set.disjoint_left]
  rintro z ⟨c, hc, rfl⟩ ⟨c', hc', hz⟩
  have hz' : c' + y = c + x := hz
  apply h c hc c' hc'
  rw [sub_eq_sub_iff_add_eq_add, add_comm y c']
  exact hz'.symm

lemma setDist_translate_eq_one {C : Set E} {x y : E}
    (hlow : ∀ c ∈ C, ∀ c' ∈ C, 1 ≤ ‖(y - x) - (c - c')‖)
    (hex : ∃ c ∈ C, ∃ c' ∈ C, ‖(y - x) - (c - c')‖ = 1) :
    setDist (translate C x) (translate C y) = 1 := by
  obtain ⟨c₀, hc₀, c₀', hc₀', h₀⟩ := hex
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ u ∈ translate C x, ∃ v ∈ translate C y, r = ‖u - v‖} :=
    ⟨c₀ + x, ⟨c₀, hc₀, rfl⟩, c₀' + y, ⟨c₀', hc₀', rfl⟩, by rw [altSetDist_translate_sub_norm, h₀]⟩
  unfold setDist
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ hmem
    rintro r ⟨u, -, v, -, rfl⟩
    exact norm_nonneg _
  · refine le_csInf ⟨1, hmem⟩ ?_
    rintro r ⟨u, ⟨c, hc, rfl⟩, v, ⟨c', hc', rfl⟩, rfl⟩
    rw [altSetDist_translate_sub_norm]
    exact hlow c hc c' hc'

end Erdos956
