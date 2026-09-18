import ErdosLean.Erdos956.Parts.SqrtBounds

/-!
# Erdős #956 — Part 2: coordinates of the generators `p(t)` (note, Lemma 1)

For `t ≥ 0` and `t⁴/2 ≤ e`: `0 ≤ p_x(t) ≤ t³/2` and `0 ≤ p_y(t) ≤ e`.

-/

namespace Erdos956

lemma pp_coords {e t : ℝ} (ht : 0 ≤ t) (he : t ^ 4 / 2 ≤ e) :
    0 ≤ pp e t 0 ∧ pp e t 0 ≤ t ^ 3 / 2 ∧ 0 ≤ pp e t 1 ∧ pp e t 1 ≤ e := by
  have hl := inv_rr_lower t
  have hu := inv_rr_upper t
  have h1 : 1 / rr t ≤ 1 := by
    rw [div_le_one (rr_pos t)]; exact one_le_rr t
  have hx : t - t / rr t = t * (1 - 1 / rr t) := by ring
  simp only [pp_zero, pp_one, hx]
  refine ⟨mul_nonneg ht (by linarith), ?_, by linarith, by linarith⟩
  have : t * (1 - 1 / rr t) ≤ t * (t ^ 2 / 2) := mul_le_mul_of_nonneg_left (by linarith) ht
  nlinarith

end Erdos956
