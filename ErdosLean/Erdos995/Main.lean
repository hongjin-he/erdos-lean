import ErdosLean.Erdos995.Parts.UpperL2
import ErdosLean.Erdos995.Parts.UpperBorelCantelli
import ErdosLean.Erdos995.Parts.UpperDyadic
import ErdosLean.Erdos995.Parts.Params
import ErdosLean.Erdos995.Parts.Sequence
import ErdosLean.Erdos995.Parts.StageProb
import ErdosLean.Erdos995.Parts.BorelCantelli
import ErdosLean.Erdos995.Parts.Atoms
import ErdosLean.Erdos995.Parts.GlobalL2
import ErdosLean.Erdos995.Parts.MeanZero
import ErdosLean.Erdos995.Parts.Master
import ErdosLean.Erdos995.Parts.Growth
import ErdosLean.Erdos995.Parts.Consequences

/-!
# Erdős Problem 995: main theorem (assembly)

`erdos_995 : Erdos995Answer`, i.e. Erdős's upper bound `o(N (log N)^{1/2+ε})`, Ho's lower bound
`limsup ∑_{k<N} f(n_k x) / (N (log N)^{1/2-ε}) = +∞`, the critical exponent `1/2`, and the negative
answer to the `o(N √(log log N))` question. All analytic input is in `ErdosLean/Erdos995/Parts/`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- **Erdős's upper bound** (in fact for every sequence `n`, lacunary or not). -/
theorem erdosUpperBound : ErdosUpperBound := by
  intro f n _ ε hε
  have h : ∀ᵐ x ∂μ𝕋, ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, Upper.sumNorm f n (2 ^ (j + 1)) x ≤
      (1 / ((m : ℝ) + 1)) * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε)) :=
    ae_all_iff.2 fun m => Upper.ae_eventually_sumNorm_le f n hε (by positivity)
  filter_upwards [h] with x hx
  exact Upper.isLittleO_of_dyadic (fun N => lacSum f n x N) (fun M => Upper.sumNorm f n M x)
    (fun N => Upper.norm_lacSum_le_sumNorm f n x (Nat.lt_pow_succ_log_self (by norm_num) N).le)
    hε hx

/-- **Ho's lower bound**: the explicit construction of `Defs.lean` (namespace `Con`). -/
theorem hoLowerBound : HoLowerBound := by
  have hmem := Con.memLp_gFun
  set f : Lp ℂ 2 μ𝕋 := hmem.toLp _ with hfdef
  have hfg : (f : 𝕋 → ℂ) =ᵐ[μ𝕋] fun x => (Con.gFun x : ℂ) := hmem.coeFn_toLp
  refine ⟨f, Con.nSeq, Con.isDyadicLacunary_nSeq, ?_, ?_, ?_⟩
  · filter_upwards [hfg] with x hx
    rw [hx, Complex.ofReal_im]
  · rw [integral_congr_ae hfg]
    exact Con.integral_gFun
  · have hall : ∀ᵐ x ∂μ𝕋, ∀ j, Con.gPos (Con.nSeq j • x) ≠ ∞ ∧
        f (Con.nSeq j • x) = (Con.gFun (Con.nSeq j • x) : ℂ) :=
      Con.ae_forall_nSeq (P := fun y => Con.gPos y ≠ ∞ ∧ f y = (Con.gFun y : ℂ))
        (by filter_upwards [Con.ae_gPos_ne_top, hfg] with y h1 h2 using ⟨h1, h2⟩)
    filter_upwards [hall, Con.ae_eventually_stageGood] with x hx hgood
    intro ε hε C
    rw [frequently_atTop]
    intro N0
    obtain ⟨k, ⟨hxk, hgr⟩, hkN0⟩ :=
      ((hgood.and (Con.growth hε C)).and (eventually_ge_atTop N0)).exists
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hxk
    rw [Finset.mem_Ico] at hs
    have hstage : Con.stage s = k := Con.stage_eq s k hs.1 hs.2
    obtain ⟨N, hsN, hN21, hsig⟩ := Con.master_trial x s (fun j => (hx j).1) hxs
    refine ⟨N, ?_, ?_⟩
    · have := Con.le_firstTrial k
      omega
    · have hre : (lacSum f Con.nSeq x N).re = ∑ j ∈ range N, Con.gFun (Con.nSeq j • x) := by
        unfold lacSum
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(hx j).2, Complex.ofReal_re]
      rw [hre]
      have hNle : N ≤ 21 ^ Con.firstTrial (k + 1) :=
        hN21.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hstage] at hsig
      exact (hgr N hNle).trans hsig

/-- **Erdős Problem 995, full answer**: the growth is `N (log N)^{1/2+o(1)}`, and in particular
`∑_{k<N} f(n_k x) = o(N √(log log N))` fails in general. -/
theorem erdos_995 : Erdos995Answer :=
  ⟨erdosUpperBound, hoLowerBound, criticalExponent_of erdosUpperBound hoLowerBound,
    not_logLogQuestion_of hoLowerBound⟩

/-- The negative answer to the concrete question, stated on its own. -/
theorem erdos_995_logLog : ¬ LogLogQuestion := erdos_995.2.2.2

end Erdos995
