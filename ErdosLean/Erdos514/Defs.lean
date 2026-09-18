import ErdosLean.Erdos514.Statement

/-!
# Erdős #514 — shared definitions

* `shift f n`: the iterated Taylor shift, `shift f 0 = f`,
  `shift f (n+1) = dslope (shift f n) 0`; for `z ≠ 0`,
  `shift f n z = (f z - ∑_{k<n} aₖ zᵏ) / zⁿ` where `aₖ = shift f k 0` are the Taylor
  coefficients.  For entire `f` every `shift f n` is entire (removable singularity).
* `superlevel g K = {z | K < ‖g z‖}` and `tract g K z₀`, the connected component of the
  superlevel set through `z₀`.
-/

open Set

namespace Erdos514

/-- Iterated Taylor shift of `f` at `0`. -/
noncomputable def shift (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (shift f n) 0

@[simp] lemma shift_zero (f : ℂ → ℂ) : shift f 0 = f := rfl

@[simp] lemma shift_succ (f : ℂ → ℂ) (n : ℕ) : shift f (n + 1) = dslope (shift f n) 0 := rfl

/-- The superlevel set `{z | K < ‖g z‖}`. -/
def superlevel (g : ℂ → ℂ) (K : ℝ) : Set ℂ := {z | K < ‖g z‖}

/-- The tract of `g` at level `K` through `z₀`: the connected component of
`{z | K < ‖g z‖}` containing `z₀` (empty if `‖g z₀‖ ≤ K`). -/
def tract (g : ℂ → ℂ) (K : ℝ) (z₀ : ℂ) : Set ℂ := connectedComponentIn (superlevel g K) z₀

lemma mem_superlevel {g : ℂ → ℂ} {K : ℝ} {z : ℂ} : z ∈ superlevel g K ↔ K < ‖g z‖ := Iff.rfl

lemma isOpen_superlevel {g : ℂ → ℂ} (hg : Continuous g) (K : ℝ) : IsOpen (superlevel g K) :=
  isOpen_lt continuous_const (continuous_norm.comp hg)

lemma isOpen_tract {g : ℂ → ℂ} (hg : Continuous g) (K : ℝ) (z₀ : ℂ) :
    IsOpen (tract g K z₀) :=
  (isOpen_superlevel hg K).connectedComponentIn

lemma tract_subset_superlevel (g : ℂ → ℂ) (K : ℝ) (z₀ : ℂ) :
    tract g K z₀ ⊆ superlevel g K :=
  connectedComponentIn_subset _ _

lemma isPreconnected_tract (g : ℂ → ℂ) (K : ℝ) (z₀ : ℂ) : IsPreconnected (tract g K z₀) :=
  isPreconnected_connectedComponentIn

lemma mem_tract_self {g : ℂ → ℂ} {K : ℝ} {z₀ : ℂ} (h : K < ‖g z₀‖) : z₀ ∈ tract g K z₀ :=
  mem_connectedComponentIn h

end Erdos514
