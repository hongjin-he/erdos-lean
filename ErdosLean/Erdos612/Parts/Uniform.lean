import ErdosLean.Erdos612.Statement

/-!
# Erdős 612, part: the uniform reading implies the weak reading

The uniform constant works for every fixed `d`: a graph with `minDegree = d`, `2 ≤ d`,
`m ∣ d` satisfies the hypotheses of `DiamBoundUniform`.
-/

namespace Erdos612

theorem diamBound_of_uniform {s m : ℕ} {c : ℝ} (h : DiamBoundUniform s m c) :
    DiamBound s m c := by
  obtain ⟨C, hC⟩ := h
  intro d hd hm
  refine ⟨C, fun n G _ hconn hcf hmin => ?_⟩
  have := hC n G hconn hcf (hmin ▸ hd) (hmin ▸ hm)
  rwa [hmin] at this

end Erdos612
