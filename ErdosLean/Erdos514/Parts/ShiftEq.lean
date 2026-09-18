import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: the Taylor-shift identity
`g z = g 0 + z * dslope g 0 z` (Mathlib `sub_smul_dslope`), valid for every function. -/

namespace Erdos514

theorem shift_eq_add_mul (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    shift f n z = shift f n 0 + z * shift f (n + 1) z := by
  have h := sub_smul_dslope (shift f n) 0 z
  simp only [sub_zero, smul_eq_mul] at h
  rw [shift_succ, h]; ring

end Erdos514
