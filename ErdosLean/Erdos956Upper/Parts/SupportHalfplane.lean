import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P2: supporting half-plane at a unit vector

If `infDist v D = 1` and `d` is the nearest point of `D`, then `K` lies in the half-plane `⟪u - v, v - d⟫ ≤ 0` (projection onto a convex set: `norm_eq_iInf_iff_real_inner_le_zero`).
-/

namespace Erdos956Upper

open Erdos956 Metric



/-- Supporting half-plane of `K = {infDist · D ≤ 1}` at a boundary point `v`. -/
theorem exists_support {D : Set E} (hD : IsCompact D) (hDc : Convex ℝ D) (hne : D.Nonempty)
    {v : E} (hv : infDist v D = 1) :
    ∃ d ∈ D, ‖v - d‖ = 1 ∧ ∀ u ∈ Kset D, inner ℝ (u - v) (v - d) ≤ 0 := by
  obtain ⟨d, hdD, hdd⟩ := hD.exists_infDist_eq_dist hne v
  have hnorm : ‖v - d‖ = 1 := by rw [← dist_eq_norm, ← hdd, hv]
  have hproj : ∀ w ∈ D, inner ℝ (v - d) (w - d) ≤ 0 := by
    refine (norm_eq_iInf_iff_real_inner_le_zero hDc hdD).1 ?_
    rw [← dist_eq_norm, ← hdd, infDist_eq_iInf]
    simp only [dist_eq_norm]
  refine ⟨d, hdD, hnorm, fun u hu => ?_⟩
  obtain ⟨d', hd'D, hd'd⟩ := hD.exists_infDist_eq_dist hne u
  have hu1 : ‖u - d'‖ ≤ 1 := by
    have : infDist u D ≤ 1 := hu
    rw [hd'd, dist_eq_norm] at this; exact this
  have h1 := hproj d' hd'D
  have h2 : inner ℝ (u - d') (v - d) ≤ 1 := by
    calc inner ℝ (u - d') (v - d) ≤ ‖u - d'‖ * ‖v - d‖ := real_inner_le_norm _ _
      _ ≤ 1 := by rw [hnorm, mul_one]; exact hu1
  have h3 : inner ℝ (v - d) (v - d) = (1:ℝ) := by
    rw [real_inner_self_eq_norm_sq, hnorm]; norm_num
  have hsplit : u - v = (d' - d) + (u - d') - (v - d) := by abel
  have h4 : inner ℝ (d' - d) (v - d) ≤ 0 := by rw [real_inner_comm]; exact h1
  rw [hsplit, inner_sub_left, inner_add_left, h3]
  linarith

end Erdos956Upper
