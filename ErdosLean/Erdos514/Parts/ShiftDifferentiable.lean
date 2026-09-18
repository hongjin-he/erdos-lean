import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: Taylor shifts of entire functions are entire
Induction on `n` with `Complex.differentiableOn_dslope` (removable singularity). -/

namespace Erdos514

theorem shift_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (shift f n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [shift_succ, ← differentiableOn_univ,
      Complex.differentiableOn_dslope Filter.univ_mem]
    exact ih.differentiableOn

end Erdos514
