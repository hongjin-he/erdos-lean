import ErdosLean.Erdos956.Parts.UnitGap
import ErdosLean.Erdos956.Parts.HalfBody
import ErdosLean.Erdos956.Parts.SetDist
import ErdosLean.Erdos956.Parts.BodyBox

/-!
# Erdős #956 — Part 10: each counted pair is at set-distance exactly 1 (note, Lemma 4)

For `(i, r, s) ∈ triples k`, `upPt (r+i) (s-i²) - lowPt r s = γ(i a)` (because `b = a²/2`), and
with `c = p/2`, `c' = -p/2` (both in `C`) the distance `‖γ - p‖ = 1` is attained, while
Part 7 gives `≥ 1` for all `c - c' ∈ D`.
-/

namespace Erdos956

lemma upPt_sub_lowPt {k i r s : ℕ} (hk : 1 ≤ k) (his : i ^ 2 ≤ s) :
    upPt k (r + i) (s - i ^ 2) - lowPt k r s = γ (η k) (i * a k) := by
  have hb : b k = a k ^ 2 / 2 := by
    unfold a b; field_simp
  have hcast : ((s - i ^ 2 : ℕ) : ℝ) = (s : ℝ) - (i : ℝ) ^ 2 := by
    rw [Nat.cast_sub his]; push_cast; ring
  ext j
  fin_cases j
  · simp [upPt, lowPt, γ, pt]
    ring
  · simp [upPt, lowPt, γ, pt]
    rw [hcast, hb]; ring

theorem setDist_pairOf {k : ℕ} (hk : 1 ≤ k) {q : ℕ × ℕ × ℕ} (hq : q ∈ triples k) :
    setDist (translate (C k) (lowPt k q.2.1 q.2.2))
      (translate (C k) (upPt k (q.2.1 + q.1) (q.2.2 - q.1 ^ 2))) = 1 := by
  obtain ⟨i, r, s⟩ := q
  simp only [triples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hq
  obtain ⟨⟨⟨hi1, hik⟩, _, _⟩, _, his⟩ := hq
  have ht0 : (0 : ℝ) ≤ (i : ℝ) * a k := by
    unfold a α; positivity
  have htW := ia_le_W (i := i) hk hik
  apply setDist_translate_eq_one
  · intro c hc c' hc'
    simp only
    rw [upPt_sub_lowPt hk his]
    exact one_le_norm_γ_sub hk ht0 htW (sub_mem_D hc hc')
  · have hp := pp_mem_gens (k := k) hi1 hik
    refine ⟨(1 / 2 : ℝ) • pp (η k) (i * a k), half_mem_half_hull hp,
      (1 / 2 : ℝ) • -pp (η k) (i * a k), half_mem_half_hull (neg_mem_gens hp), ?_⟩
    simp only
    rw [upPt_sub_lowPt hk his]
    have : (1 / 2 : ℝ) • pp (η k) (i * a k) - (1 / 2 : ℝ) • -pp (η k) (i * a k)
        = pp (η k) (i * a k) := by
      rw [smul_neg, sub_neg_eq_add, ← add_smul]; norm_num
    rw [this, norm_γ_sub_pp]

end Erdos956
