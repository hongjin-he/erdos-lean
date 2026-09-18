import ErdosLean.Erdos996.Statement

/-! # Erdős 996: shared definitions (spike, digit windows, block). -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- The dyadic spike `φ_d = (1_{[0,2^{-d})} - 2^{-d}) / √(2^{-d}(1-2^{-d}))` on the circle. -/
noncomputable def spike (d : ℕ) (x : 𝕋) : ℝ :=
  ((Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) 1 x : ℝ) -
      (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))

/-- A set is *determined by the digit window* `[a, b)` if membership of `x` depends only on
binary digits `a+1, …, b` of `x`. -/
def DeterminedByWindow (a b : ℕ) (E : Set 𝕋) : Prop :=
  ∀ x y : 𝕋, (∀ j, a ≤ j → j < b →
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 y : ℝ)) < 2⁻¹) → (x ∈ E ↔ y ∈ E)

/-- The block `F(x) = √(λ/L) ∑_{q=1}^{L} φ_d(2^{U+qD} x)`. -/
noncomputable def block (lam : ℝ) (L d D U : ℕ) (x : 𝕋) : ℝ :=
  Real.sqrt (lam / L) * ∑ q ∈ Finset.Icc 1 L, spike d ((2 ^ (U + q * D) : ℕ) • x)

end Erdos996
