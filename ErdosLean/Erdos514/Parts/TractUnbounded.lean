import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: every tract is unbounded
If `D = tract g K w` were bounded: `D` is open, its frontier is disjoint from the open set
`superlevel g K` (a frontier point in the superlevel set would lie in the same component),
so `‖g‖ ≤ K` on `frontier D`, and the maximum modulus principle on a bounded set
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) gives `‖g w‖ ≤ K`, contradiction.
(`D ≠ univ` because a bounded set is not `univ`; if `D = ∅` there is nothing to do.) -/

namespace Erdos514

theorem tract_not_bounded {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ} {w : ℂ}
    (hw : K < ‖g w‖) : ¬ Bornology.IsBounded (tract g K w) := by
  intro hb
  have hcont : Continuous g := hg.continuous
  set D := tract g K w with hD
  have hDo : IsOpen D := isOpen_tract hcont K w
  have hfr : ∀ z ∈ frontier D, ‖g z‖ ≤ K := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hzS : z ∈ superlevel g K := hlt
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_superlevel hcont K) z hzS
    have hzcl : z ∈ closure D := frontier_subset_closure hz
    obtain ⟨y, hyD, hzy⟩ := Metric.mem_closure_iff.mp hzcl r hr
    have hyB : y ∈ Metric.ball z r := Metric.mem_ball.mpr (by rw [dist_comm]; exact hzy)
    have hsub : Metric.ball z r ⊆ D := by
      have : Metric.ball z r ⊆ connectedComponentIn (superlevel g K) y :=
        (convex_ball z r).isPreconnected.subset_connectedComponentIn hyB hball
      rw [← connectedComponentIn_eq hyD] at this
      exact this
    have hzD : z ∈ D := hsub (Metric.mem_ball_self hr)
    exact (hDo.frontier_eq ▸ hz).2 hzD
  have hwD : w ∈ D := mem_tract_self hw
  have := Complex.norm_le_of_forall_mem_frontier_norm_le hb hg.diffContOnCl hfr
    (subset_closure hwD)
  linarith

end Erdos514
