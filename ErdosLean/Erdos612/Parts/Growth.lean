import Mathlib

/-!
# Erdős 612, part: a linear function with larger slope eventually wins

Proof plan: Archimedean property (`exists_nat_gt`) for `(b0 - a0) / (a - b)`.
-/

namespace Erdos612

theorem linear_escape (a b a0 b0 : ℝ) (hab : b < a) :
    ¬ ∀ p : ℕ, a * p + a0 ≤ b * p + b0 := by
  intro h
  obtain ⟨p, hp⟩ := exists_nat_gt ((b0 - a0) / (a - b))
  have h1 := h p
  have h2 : 0 < a - b := sub_pos.mpr hab
  rw [div_lt_iff₀ h2] at hp
  nlinarith

end Erdos612
