import ErdosLean.Erdos996.Statement

/-!
# Assembly sub-lemma 10 (ParsevalTail): the Fourier tail via Parseval

Blueprint §10. Generic: for `f ∈ L²(𝕋)`, `‖f - S_N f‖₂² = ∑_{|r| > N} |f̂(r)|²`
(`tsum_sq_fourierCoeff` applied to `f - S_N f`, whose coefficients are `f̂(r) 1_{|r|>N}`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma eLpNorm_sub_fourierPartial_sq (f : Lp ℂ 2 μ𝕋) (N : ℕ) :
    (eLpNorm (⇑f - fourierPartial f N) 2 μ𝕋).toReal ^ 2 =
      ∑' r : {r : ℤ // (N : ℤ) < |r|}, ‖fourierCoeff f r‖ ^ 2 := by
  classical
  set s : Finset ℤ := Icc (-(N : ℤ)) N with hs
  set g : Lp ℂ 2 μ𝕋 := f - ∑ i ∈ s, fourierCoeff f i • fourierLp (T := 1) 2 i with hg
  have hae : (⇑g : 𝕋 → ℂ) =ᵐ[μ𝕋] ⇑f - fourierPartial f N := by
    have h1 := Lp.coeFn_sub f (∑ i ∈ s, fourierCoeff f i • fourierLp (T := 1) 2 i)
    have h2 := Lp.coeFn_finsetSum s (fun i => fourierCoeff f i • fourierLp (T := 1) 2 i)
    have h3 : ∀ i : ℤ, (⇑(fourierCoeff f i • fourierLp (T := 1) 2 i) : 𝕋 → ℂ) =ᵐ[μ𝕋]
        fun x => fourierCoeff f i • fourier i x := by
      intro i
      filter_upwards [Lp.coeFn_smul (fourierCoeff f i) (fourierLp (T := 1) 2 i),
        coeFn_fourierLp (T := 1) 2 i] with x hx1 hx2
      rw [hx1, Pi.smul_apply, hx2]
    have h3' := ae_all_iff.2 h3
    filter_upwards [h1, h2, h3'] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, Pi.sub_apply, hx2, Finset.sum_apply]
    simp only [fourierPartial, hx3, hs]
  have hL : (eLpNorm (⇑f - fourierPartial f N) 2 μ𝕋).toReal = ‖g‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have hnorm : HasSum (fun i => ‖(fourierBasis (T := 1)).repr g i‖ ^ 2) (‖g‖ ^ 2) := by
    have H₁ : HasSum (fun i => ‖(fourierBasis (T := 1)).repr g i‖ ^ 2)
        (‖(fourierBasis (T := 1)).repr g‖ ^ 2) := by
      apply_mod_cast lp.hasSum_norm ?_ ((fourierBasis (T := 1)).repr g)
      simp
    simpa using H₁
  have he : ∀ j : ℤ, fourierLp (T := 1) 2 j = (fourierBasis (T := 1)) j := fun j => by
    rw [coe_fourierBasis]
  have hcoef : ∀ i, (fourierBasis (T := 1)).repr g i = if i ∈ s then 0 else fourierCoeff f i := by
    intro i
    rw [hg, map_sub, map_sum]
    simp only [he, map_smul, HilbertBasis.repr_self, lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, lp.single_apply, fourierBasis_repr,
      Pi.single_apply, smul_eq_mul]
    split_ifs with h <;> simp [h]
  have hterm : (fun i => ‖(fourierBasis (T := 1)).repr g i‖ ^ 2) =
      {r : ℤ | (N : ℤ) < |r|}.indicator (fun r => ‖fourierCoeff f r‖ ^ 2) := by
    funext i
    rw [hcoef i, Set.indicator_apply]
    by_cases h : i ∈ s
    · have : ¬ (N : ℤ) < |i| := by
        rw [hs, Finset.mem_Icc] at h; rw [not_lt, abs_le]; exact h
      simp [h, this]
    · have : (N : ℤ) < |i| := by
        rw [hs, Finset.mem_Icc] at h; rw [lt_abs]; omega
      simp [h, this]
  rw [hL, ← hnorm.tsum_eq, hterm]
  exact (tsum_subtype {r : ℤ | (N : ℤ) < |r|} _).symm

end Asm
end Erdos996
