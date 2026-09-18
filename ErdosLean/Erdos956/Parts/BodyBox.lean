import ErdosLean.Erdos956.Parts.GenCoords

/-!
# Erdős #956 — Part 5: `D ⊆ [-W³/2, W³/2] × [-η, η]` (note, (4))

Every generator `±p(i a)` has `t = i a ∈ [0, W]`, so by Part 2 its coordinates are bounded;
the box is convex, so `convexHull_min` finishes.
-/

namespace Erdos956

lemma ia_le_W {k i : ℕ} (hk : 1 ≤ k) (hik : i ≤ k) : (i : ℝ) * a k ≤ W k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
  have hkpos : (0 : ℝ) < k := by linarith
  unfold a W α
  have e1 : (i : ℝ) * (1 / 10 / (k : ℝ) ^ 2) = (i / k) * (1 / 10 / k) := by
    field_simp
  rw [e1]
  have : (i : ℝ) / k ≤ 1 := by rw [div_le_one hkpos]; exact hik'
  have h0 : (0 : ℝ) ≤ 1 / 10 / k := by positivity
  nlinarith

private lemma box_convex (A B : ℝ) :
    Convex ℝ {z : E | |z 0| ≤ A ∧ |z 1| ≤ B} := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · calc |s * x 0 + t * y 0| ≤ |s * x 0| + |t * y 0| := abs_add_le _ _
      _ = s * |x 0| + t * |y 0| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * A + t * A := by gcongr
      _ = A := by rw [← add_mul, hst, one_mul]
  · calc |s * x 1 + t * y 1| ≤ |s * x 1| + |t * y 1| := abs_add_le _ _
      _ = s * |x 1| + t * |y 1| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * B + t * B := by gcongr
      _ = B := by rw [← add_mul, hst, one_mul]

lemma mem_D_bounds {k : ℕ} (hk : 1 ≤ k) {z : E} (hz : z ∈ D k) :
    |z 0| ≤ W k ^ 3 / 2 ∧ |z 1| ≤ η k := by
  have hW0 : 0 ≤ W k := by unfold W α; positivity
  have hηW : η k = W k ^ 4 := by unfold η W α; field_simp
  have key : ∀ i ∈ Finset.Icc 1 k,
      |pp (η k) (i * a k) 0| ≤ W k ^ 3 / 2 ∧ |pp (η k) (i * a k) 1| ≤ η k := by
    intro i hi
    have hik := (Finset.mem_Icc.mp hi).2
    have hle := ia_le_W hk hik
    have ht0 : 0 ≤ (i : ℝ) * a k := by unfold a α; positivity
    have h4 : ((i : ℝ) * a k) ^ 4 ≤ W k ^ 4 := pow_le_pow_left₀ ht0 hle 4
    have h3 : ((i : ℝ) * a k) ^ 3 ≤ W k ^ 3 := pow_le_pow_left₀ ht0 hle 3
    have he : ((i : ℝ) * a k) ^ 4 / 2 ≤ η k := by
      rw [hηW]; have := pow_nonneg ht0 4; linarith
    obtain ⟨h1, h2, h3', h4'⟩ := pp_coords ht0 he
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg h1]; linarith
    · rw [abs_of_nonneg h3']; exact h4'
  have hsub : (gens k : Set E) ⊆ {z : E | |z 0| ≤ W k ^ 3 / 2 ∧ |z 1| ≤ η k} := by
    intro g hg
    simp only [gens, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact key i hi
    · obtain ⟨h1, h2⟩ := key i hi
      simp only [Set.mem_ofPred_eq, PiLp.neg_apply, abs_neg]
      exact ⟨h1, h2⟩
  exact convexHull_min hsub (box_convex _ _) hz

end Erdos956
