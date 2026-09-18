import ErdosLean.Erdos996.Parts.SpikeGe
import ErdosLean.Erdos996.Parts.SpikeFourierSupport
import ErdosLean.Erdos996.Parts.SpikeTail
import ErdosLean.Erdos996.Parts.DigitIndependence
import ErdosLean.Erdos996.Parts.BlockFloor
import ErdosLean.Erdos996.Parts.TrialSignal
import ErdosLean.Erdos996.Parts.Asm.Construction
import ErdosLean.Erdos996.Parts.Asm.Params
import ErdosLean.Erdos996.Parts.Asm.Sequence
import ErdosLean.Erdos996.Parts.Asm.SpikeMeasure
import ErdosLean.Erdos996.Parts.Asm.HitWindow
import ErdosLean.Erdos996.Parts.Asm.StageProb
import ErdosLean.Erdos996.Parts.Asm.Atoms
import ErdosLean.Erdos996.Parts.Asm.PartialSumL2
import ErdosLean.Erdos996.Parts.Asm.GlobalL2
import ErdosLean.Erdos996.Parts.Asm.Master
import ErdosLean.Erdos996.Parts.Asm.ParsevalTail
import ErdosLean.Erdos996.Parts.Asm.TailSum
import ErdosLean.Erdos996.Parts.Asm.TailAsymp

/-!
# Erdős 996: global assembly (gaps G4, G5, G6)

The counterexample is the explicit construction of `Parts/Asm/Construction.lean` with the
parameter `A` supplied by `tail_asymp`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

open Asm in
/-- The pointwise counterexample: a mean-zero `g ∈ L²` (given pointwise, as an a.e. limit of
blocks), a dyadic lacunary `n`, the Fourier-tail bound for the `L²` class of `g`, and a set of
positive measure on which the averages are `≥ δ > 0` infinitely often. -/
theorem exists_pointwise_counterexample (C : ℝ) (hC : 0 < C) :
    ∃ (f : Lp ℂ 2 μ𝕋) (n : ℕ → ℕ) (δ : ℝ), 0 < δ ∧ IsDyadicLacunary n ∧
      FourierTailBound C f ∧ ∫ t, f t ∂μ𝕋 = 0 ∧
      0 < μ𝕋 {x | ∃ᶠ N in atTop, δ ≤ ‖(∑ k ∈ range N, f (n k • x)) / (N : ℂ)‖} := by
  obtain ⟨A₀, hA₀⟩ := tail_asymp C hC
  set A : ℕ := max A₀ 1 with hAdef
  have hA : 1 ≤ A := le_max_right _ _
  have hmem := memLp_gFun A hA
  set f : Lp ℂ 2 μ𝕋 := hmem.toLp _ with hfdef
  have hfg : (f : 𝕋 → ℂ) =ᵐ[μ𝕋] fun x => (gFun A x : ℂ) := hmem.coeFn_toLp
  refine ⟨f, nSeq A, 1, one_pos, isDyadicLacunary_nSeq A, ?_, ?_, ?_⟩
  · -- G5: the Fourier tail bound
    obtain ⟨C₁, hC₁, htail⟩ := tail_sum_le
    obtain ⟨K, hK, hev⟩ := hA₀ A (le_max_left _ _) (logQ A) (scale_bound A hA) C₁ hC₁.le
    have hcoef : fourierCoeff (⇑f) = fourierCoeff (fun x => (gFun A x : ℂ)) :=
      fourierCoeff_congr_ae hfg
    unfold FourierTailBound
    refine IsBigO.of_bound K ?_
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hsq := eLpNorm_sub_fourierPartial_sq f N
    rw [hcoef] at hsq
    calc (eLpNorm (⇑f - fourierPartial f N) 2 μ𝕋).toReal
        = Real.sqrt ((eLpNorm (⇑f - fourierPartial f N) 2 μ𝕋).toReal ^ 2) :=
          (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ Real.sqrt (C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ logQ A k / N)) := by
          rw [hsq]; exact Real.sqrt_le_sqrt (htail A hA N hN1)
      _ ≤ K * (1 / (Real.log (Real.log (Real.log N))) ^ C) := hN
      _ ≤ K * ‖1 / (Real.log (Real.log (Real.log N))) ^ C‖ :=
          mul_le_mul_of_nonneg_left (Real.le_norm_self _) hK
  · -- mean zero
    rw [integral_congr_ae hfg]
    exact integral_gFun A hA
  · -- G6: positive measure
    have hall : ∀ᵐ x ∂μ𝕋, ∀ j, gPos A (nSeq A j • x) ≠ ∞ ∧
        f (nSeq A j • x) = (gFun A (nSeq A j • x) : ℂ) :=
      ae_forall_nSeq A (P := fun y => gPos A y ≠ ∞ ∧ f y = (gFun A y : ℂ))
        (by filter_upwards [ae_gPos_ne_top A hA, hfg] with y h1 h2 using ⟨h1, h2⟩)
    set G : Set 𝕋 := {x | ∀ j, gPos A (nSeq A j • x) ≠ ∞ ∧
        f (nSeq A j • x) = (gFun A (nSeq A j • x) : ℂ)} with hGdef
    have hGc : μ𝕋 Gᶜ = 0 := mem_ae_iff.1 hall
    have hsub : (⋂ k, stageGood A k) ∩ G ⊆
        {x | ∃ᶠ N in atTop, (1 : ℝ) ≤ ‖(∑ k ∈ range N, f (nSeq A k • x)) / (N : ℂ)‖} := by
      rintro x ⟨hx, hxG⟩
      simp only [Set.mem_ofPred_eq]
      refine frequently_atTop.2 fun a => ?_
      have hxa : x ∈ stageGood A a := Set.mem_iInter.1 hx a
      simp only [stageGood] at hxa
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hxa
      obtain ⟨N, hsN, hN⟩ := master_trial A hA x s (fun j => (hxG j).1) hxs
      refine ⟨N, ?_, ?_⟩
      · have h1 := le_firstTrial A a
        have h2 := (Finset.mem_Ico.1 hs).1
        omega
      · have hsum : (∑ k ∈ range N, f (nSeq A k • x)) / (N : ℂ) =
            (((∑ j ∈ range N, gFun A (nSeq A j • x)) / N : ℝ) : ℂ) := by
          rw [Finset.sum_congr rfl fun j _ => (hxG j).2, Complex.ofReal_div,
            Complex.ofReal_sum, Complex.ofReal_natCast]
        rw [hsum, Complex.norm_real]
        exact hN.trans (Real.le_norm_self _)
    calc (0 : ℝ≥0∞) < μ𝕋 (⋂ k, stageGood A k) := measure_iInter_stageGood_pos A hA
      _ = μ𝕋 ((⋂ k, stageGood A k) ∩ G) := (measure_inter_conull hGc).symm
      _ ≤ _ := measure_mono hsub

end Erdos996
