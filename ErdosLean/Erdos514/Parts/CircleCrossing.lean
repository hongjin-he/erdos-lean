import Mathlib

/-! # Erdős #514 — Part: an unbounded preconnected set meets every large circle.
The image of `S` under the continuous map `‖·‖` is preconnected in `ℝ`,
hence an interval (`IsPreconnected.image`, `IsPreconnected.Icc_subset`); it contains `‖w‖`
and arbitrarily large values. -/

namespace Erdos514

theorem exists_mem_norm_eq {S : Set ℂ} (hS : IsPreconnected S) (hSb : ¬ Bornology.IsBounded S)
    {w : ℂ} (hw : w ∈ S) {r : ℝ} (hr : ‖w‖ ≤ r) : ∃ z ∈ S, ‖z‖ = r := by
  have hex : ∃ z ∈ S, r < ‖z‖ := by
    by_contra h
    push Not at h
    exact hSb ((Metric.isBounded_closedBall (x := (0:ℂ)) (r := r)).subset
      (fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using h z hz))
  obtain ⟨z, hzS, hz⟩ := hex
  have himg : IsPreconnected ((fun x : ℂ => ‖x‖) '' S) :=
    hS.image _ continuous_norm.continuousOn
  have hsub := himg.Icc_subset (Set.mem_image_of_mem _ hw) (Set.mem_image_of_mem _ hzS)
  obtain ⟨z', hz'S, hz'⟩ := hsub ⟨hr, hz.le⟩
  exact ⟨z', hz'S, hz'⟩

end Erdos514
