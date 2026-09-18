import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: high superlevel sets avoid a given disc
`g` is bounded on the compact `closedBall 0 R`; take `K ≥ max K₀ (sup of ‖g‖ there)`. -/

namespace Erdos514

theorem superlevel_subset_far {g : ℂ → ℂ} (hg : Continuous g) (R K₀ : ℝ) :
    ∃ K : ℝ, K₀ ≤ K ∧ superlevel g K ⊆ {z | R < ‖z‖} := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max K₀ C, le_max_left _ _, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq]
  by_contra h
  push Not at h
  have h1 : ‖g z‖ ≤ C := hC z (by simpa [Metric.mem_closedBall, dist_zero_right] using h)
  have h2 : max K₀ C < ‖g z‖ := hz
  linarith [le_max_right K₀ C]

end Erdos514
