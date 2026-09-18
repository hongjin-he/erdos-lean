import ErdosLean.Erdos996.Defs

/-!
# Erdős 996, assembly: the explicit global construction

Everything here is a plain definition (no proofs). See the module docs for the
mathematics. The construction depends on one natural parameter `A` (the decay rate of the
stage costs, `λ_k = 2^{-A(k+1)}`), chosen in the assembly from the target exponent `C`.

Indexing conventions (all `ℕ`, starting at `0`):
* stages `k = 0, 1, 2, …`; stage `k` owns the trials `s ∈ [firstTrial A k, firstTrial A (k+1))`;
* trials `s = 0, 1, 2, …` are numbered globally; trial `s` has length `trialLen s = 20·21^s`
  and occupies the global indices `j ∈ [21^s - 1, 21^(s+1) - 1)`, the `r`-th exponent
  (`1 ≤ r ≤ trialLen s`) sitting at `j = 21^s + r - 2`;
* the selected exponents are `mExp A j = trialStart A s + r * spacing A (stage A s)` and
  `nSeq A j = 2 ^ mExp A j`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-! ### Stage parameters -/

/-- `a_k = A (k+1)`, so that `λ_k = 2^{-a_k}`. -/
def aExp (A k : ℕ) : ℕ := A * (k + 1)

/-- Stage cost `λ_k = 2^{-A(k+1)}` (squared `L²` norm of the `k`-th block). -/
noncomputable def lam (A k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ aExp A k

/-- Number of trials in stage `k`: `T_k = 2^{a_k + k + 24}`. -/
def nTrials (A k : ℕ) : ℕ := 2 ^ (aExp A k + k + 24)

/-- Index of the first trial of stage `k`: `S_0 = 0`, `S_{k+1} = S_k + T_k`. -/
def firstTrial (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => firstTrial A k + nTrials A k

/-- Number of layers of the `k`-th block: `L_k = 8 · 21^{S_{k+1}}` (≥ 8 × every trial length
of the stage). -/
def blockLen (A k : ℕ) : ℕ := 8 * 21 ^ firstTrial A (k + 1)

/-- Spike depth `d_k = ⌈log₂(64 B₀² L_k / λ_k)⌉` with `B₀ = 100`, i.e. the least `d` with
`640000 · L_k · 2^{a_k} ≤ 2^d`. -/
def depth (A k : ℕ) : ℕ := Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k)

/-- Layer spacing `D_k = d_k + 2`. -/
def spacing (A k : ℕ) : ℕ := depth A k + 2

/-- Base shift of the `k`-th block: `U_0 = 0`, `U_{k+1} = U_k + L_k D_k + d_k`
(so the dyadic valuation bands of different blocks are disjoint). -/
def shift (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => shift A k + blockLen A k * spacing A k + depth A k

/-- `log₂` of the Fourier threshold of the `k`-th block: `Q_k = 2^{E_k}`, `E_k = U_{k+1} + 2`. -/
def logQ (A k : ℕ) : ℕ := shift A (k + 1) + 2

/-! ### Trials and the exponent sequence -/

/-- The stage containing trial `s`: the largest `k ≤ s` with `S_k ≤ s`. -/
def stage (A s : ℕ) : ℕ := Nat.findGreatest (fun k => firstTrial A k ≤ s) s

/-- Length of trial `s`: `ℓ_s = 20 · 21^s` (so `P_s + 1 = 21^s` exponents precede it). -/
def trialLen (s : ℕ) : ℕ := 20 * 21 ^ s

/-- Start offset of trial `s`: `M_0 = 0`, `M_{s+1} = M_s + (L_k + 2) D_k` with `k = stage s`. -/
def trialStart (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => trialStart A s + (blockLen A (stage A s) + 2) * spacing A (stage A s)

/-- The trial containing global index `j`: `s = ⌊log₂₁ (j+1)⌋`. -/
def trialOf (j : ℕ) : ℕ := Nat.log 21 (j + 1)

/-- The `j`-th selected exponent: `m_j = M_s + r D_{stage s}` with `s = trialOf j`,
`r = j + 2 - 21^s ∈ [1, ℓ_s]`. -/
def mExp (A j : ℕ) : ℕ :=
  trialStart A (trialOf j) + (j + 2 - 21 ^ trialOf j) * spacing A (stage A (trialOf j))

/-- The lacunary sequence `n_j = 2^{m_j}`. -/
def nSeq (A j : ℕ) : ℕ := 2 ^ mExp A j

/-! ### The function -/

/-- The `k`-th block `F_k = √(λ_k/L_k) ∑_{q=1}^{L_k} φ_{d_k}(2^{U_k + q D_k} ·)`. -/
noncomputable def blk (A k : ℕ) (x : 𝕋) : ℝ :=
  block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k) x

/-- The `(k,q)` atom `φ_{d_k}(2^{U_k + q D_k} x)`; `blk A k = √(λ_k/L_k) ∑_q atom A k q`. -/
noncomputable def atom (A k q : ℕ) (x : 𝕋) : ℝ :=
  spike (depth A k) ((2 ^ (shift A k + q * spacing A k) : ℕ) • x)

/-- Deterministic floor constant `c_k = λ_k / B₀` (`B₀ = 100`): `F_k ≥ -c_k`. -/
noncomputable def floorC (A k : ℕ) : ℝ := lam A k / 100

/-- The nonnegative series `∑_k (F_k + c_k)` in `[0, ∞]`. -/
noncomputable def gPos (A : ℕ) (x : 𝕋) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (blk A k x + floorC A k)

/-- The counterexample, pointwise: `g = ∑_k (F_k + c_k) - ∑_k c_k` (where the first series is
finite, which is almost everywhere). -/
noncomputable def gFun (A : ℕ) (x : 𝕋) : ℝ :=
  (gPos A x).toReal - ∑' k, floorC A k

/-! ### Events -/

/-- The support of the positive part of the spike `φ_d`: the arc `[0, 2^{-d})`. -/
def spikeSet (d : ℕ) : Set 𝕋 := QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)

/-- `{x | 2^v x ∈ [0, 2^{-d})}`: the event that `φ_d(2^v x)` spikes. -/
def hitSet (d v : ℕ) : Set 𝕋 := {x | (2 ^ v : ℕ) • x ∈ spikeSet d}

/-- Good event of trial `s` (Ho, Def. 3.6): some central layer `h ∈ [ℓ_s + 1, L_k + 1]` spikes. -/
def goodSet (A s : ℕ) : Set 𝕋 :=
  ⋃ h ∈ Finset.Icc (trialLen s + 1) (blockLen A (stage A s) + 1),
    hitSet (depth A (stage A s)) (shift A (stage A s) + trialStart A s + h * spacing A (stage A s))

/-- Stage event `S_k`: some trial of stage `k` is good. -/
def stageGood (A k : ℕ) : Set 𝕋 :=
  ⋃ s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)), goodSet A s

end Asm
end Erdos996
