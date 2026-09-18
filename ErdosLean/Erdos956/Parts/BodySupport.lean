import ErdosLean.Erdos956.Parts.GenCoords
import ErdosLean.Erdos956.Parts.SupportIneq

/-!
# Erdős #956 — Part 6: the line through `p(t)` with normal `ν(t)` supports `D` (note, Lemma 2)

For `t ∈ [0, W]` and every `z ∈ D`, `⟨z, (t,1)⟩ ≤ ⟨p(t), (t,1)⟩`.  Positive generators: Part 3;
negative generators: both `p(s)` and `p(t)` have non-negative coordinates (Part 2).
Then `convexHull_min` into the half-plane.
-/

namespace Erdos956

lemma altBodySupport_convex_halfplane (t c : ℝ) : Convex ℝ {z : E | z 0 * t + z 1 ≤ c} := by
  intro x hx y hy s u hs hu hsu
  simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  have h1 := mul_le_mul_of_nonneg_left hx hs
  have h2 := mul_le_mul_of_nonneg_left hy hu
  calc (s * x 0 + u * y 0) * t + (s * x 1 + u * y 1)
      = s * (x 0 * t + x 1) + u * (y 0 * t + y 1) := by ring
    _ ≤ s * c + u * c := add_le_add h1 h2
    _ = c := by rw [← add_mul, hsu, one_mul]

lemma altBodySupport_pp_nonneg {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (htW : t ≤ W k) :
    0 ≤ pp (η k) t 0 ∧ 0 ≤ pp (η k) t 1 := by
  have hηW : η k = W k ^ 4 := by unfold η W; ring
  have ht4 : t ^ 4 ≤ W k ^ 4 := pow_le_pow_left₀ ht0 htW 4
  have hW4 : 0 ≤ W k ^ 4 := by unfold W α; positivity
  have he : t ^ 4 / 2 ≤ η k := by rw [hηW]; linarith
  obtain ⟨h1, -, h3, -⟩ := pp_coords ht0 he
  exact ⟨h1, h3⟩

lemma altBodySupport_ia_le_W {k i : ℕ} (hk : 1 ≤ k) (hik : i ≤ k) : (i : ℝ) * a k ≤ W k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi : (i : ℝ) ≤ k := by exact_mod_cast hik
  unfold a W α
  rw [show (i : ℝ) * (1 / 10 / (k : ℝ) ^ 2) = (i / k) * (1 / 10 / k) by field_simp]
  have : (i : ℝ) / k ≤ 1 := (div_le_one hk0).2 hi
  have h2 : (0 : ℝ) ≤ 1 / 10 / k := by positivity
  nlinarith

lemma mem_D_support {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (htW : t ≤ W k)
    {z : E} (hz : z ∈ D k) :
    z 0 * t + z 1 ≤ pp (η k) t 0 * t + pp (η k) t 1 := by
  have hsub : (gens k : Set E) ⊆
      {z : E | z 0 * t + z 1 ≤ pp (η k) t 0 * t + pp (η k) t 1} := by
    intro g hg
    simp only [gens, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe, Finset.mem_Icc] at hg
    rcases hg with ⟨i, ⟨_, hi⟩, rfl⟩ | ⟨i, ⟨_, hi⟩, rfl⟩
    · have hs0 : (0 : ℝ) ≤ i * a k := by unfold a α; positivity
      exact support_gen hs0 ht0
    · have hs0 : (0 : ℝ) ≤ i * a k := by unfold a α; positivity
      obtain ⟨hs1, hs2⟩ := altBodySupport_pp_nonneg hk hs0 (altBodySupport_ia_le_W hk hi)
      obtain ⟨ht1, ht2⟩ := altBodySupport_pp_nonneg hk ht0 htW
      simp only [Set.mem_ofPred_eq, PiLp.neg_apply]
      nlinarith [mul_nonneg hs1 ht0, mul_nonneg ht1 ht0]
  exact convexHull_min hsub (altBodySupport_convex_halfplane _ _) hz

end Erdos956
