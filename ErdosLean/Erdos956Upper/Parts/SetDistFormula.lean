import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P1: set distance of translates and the separated configuration

`δ(C+x, C+y) = infDist (y - x) (C - C)`; an admissible pair `(C, X)` gives `SepConfig (C - C) X`.
-/

namespace Erdos956Upper

open Erdos956 Metric
open scoped Pointwise

/-- `diffSet C` is the pointwise difference `C - C`. -/
lemma diffSet_eq_sub (C : Set E) : diffSet C = C - C := by
  ext v
  simp only [diffSet, Set.mem_sub]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- `δ(C + x, C + y) = dist(y - x, C - C)`. -/
theorem setDist_translate_eq_infDist {C : Set E} (hC : C.Nonempty) (x y : E) :
    setDist (translate C x) (translate C y) = infDist (y - x) (diffSet C) := by
  have hS : {r : ℝ | ∃ p ∈ translate C x, ∃ q ∈ translate C y, r = ‖p - q‖} =
      Set.range (fun v : diffSet C => dist (y - x) (v : E)) := by
    ext r
    simp only [Erdos956.translate, Set.mem_image, Set.mem_range, Subtype.exists]
    change (∃ p, _) ↔ _
    constructor
    · rintro ⟨p, ⟨a, ha, rfl⟩, q, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨a - b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
      rw [dist_eq_norm, ← norm_neg]
      congr 1
      rw [neg_sub]; abel
    · rintro ⟨v, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      refine ⟨a + x, ⟨a, ha, rfl⟩, b + y, ⟨b, hb, rfl⟩, ?_⟩
      rw [dist_eq_norm, ← norm_neg]
      congr 1
      rw [neg_sub]; abel
  rw [setDist, hS, infDist_eq_iInf]
  rfl

/-- An admissible `(C, X)` yields a separated configuration with `D = C - C`. -/
theorem admissible_sepConfig {C : Set E} {X : Finset E} (h : Admissible C X) :
    SepConfig (diffSet C) X := by
  obtain ⟨hcpt, hconv, ⟨c, hc⟩, hdisj⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : diffSet C = (fun p : E × E => p.1 - p.2) '' (C ×ˢ C) := by
      ext v
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [this]
    exact (hcpt.prod hcpt).image (continuous_fst.sub continuous_snd)
  · rw [diffSet_eq_sub]; exact hconv.sub hconv
  · exact ⟨c, hc, c, hc, (sub_self c).symm⟩
  · rintro v ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, neg_sub a b⟩
  · rintro p hp q hq hne ⟨a, ha, b, hb, hab⟩
    have hd := hdisj hp hq hne
    have h1 : a + p ∈ translate C p := ⟨a, ha, rfl⟩
    have h2 : a + p ∈ translate C q := ⟨b, hb, by
      have : q = a - b + p := by rw [← hab]; abel
      rw [this]; abel⟩
    exact Set.disjoint_left.mp hd h1 h2

end Erdos956Upper
