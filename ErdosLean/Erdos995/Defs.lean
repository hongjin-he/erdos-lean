import ErdosLean.Erdos995.Statement
import ErdosLean.Erdos996.Parts.Asm.Construction

/-!
# Erdős 995: shared definitions

Two groups of definitions.

1. `Upper`: the maximal function `sumNorm f n M x = ∑_{k<M} ‖f(n_k x)‖` used for Erdős's
   upper bound (Ho, arXiv:2604.18535, Remark 7.1).
2. `Con`: the explicit counterexample for the lower bound (Ho, §§3–4 and §7 with `p = 2`), a
   copy of the Erdős #996 construction `ErdosLean/Erdos996/Parts/Asm/Construction.lean` in which
   * the stage cost is `λ_k = 2^{-(k+1)}` (no parameter `A`: the Fourier tail is irrelevant);
   * the signal height is stage dependent, `B_k = 2^{b_k}` with `b_k = 8(k+1)² + 7 → ∞`
     (in #996 it was the constant `B₀ = 100`);
   * the number of trials is `T_k = 2^{a_k + 2 b_k + k + 24}`, so that
     `T_k λ_k / B_k² = 2^{k+24}` and stage failure is `≤ 2^{-(k+3)}` (summable);
   * the depth is `d_k = ⌈log₂(64 B_k² L_k / λ_k)⌉` and the floor constant is `c_k = λ_k / B_k`.
   The dyadic spike `Erdos996.spike`, the block `Erdos996.block` and the hit events
   `Erdos996.Asm.spikeSet` / `Erdos996.Asm.hitSet` are reused verbatim from #996.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-! ## Upper bound -/

namespace Upper

/-- The maximal majorant `G_M(x) = ∑_{k<M} ‖f(n_k x)‖`; `‖∑_{k<N} f(n_k x)‖ ≤ G_M(x)` for `N ≤ M`. -/
noncomputable def sumNorm (f : Lp ℂ 2 μ𝕋) (n : ℕ → ℕ) (M : ℕ) (x : 𝕋) : ℝ :=
  ∑ k ∈ range M, ‖f (n k • x)‖

end Upper

/-! ## The lower-bound construction -/

namespace Con

/-! ### Stage parameters -/

/-- `a_k = k + 1`, so that `λ_k = 2^{-a_k}`. -/
def aExp (k : ℕ) : ℕ := k + 1

/-- Stage cost `λ_k = 2^{-(k+1)}` (squared `L²` norm of the `k`-th block). -/
noncomputable def lam (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ aExp k

/-- `b_k = 8 (k+1)² + 7`, so that `B_k = 2^{b_k} ≥ 128`. -/
def bExp (k : ℕ) : ℕ := 8 * (k + 1) ^ 2 + 7

/-- Signal height `B_k = 2^{b_k}`. -/
noncomputable def sig (k : ℕ) : ℝ := (2 : ℝ) ^ bExp k

/-- Number of trials in stage `k`: `T_k = 2^{a_k + 2 b_k + k + 24}`. -/
def nTrials (k : ℕ) : ℕ := 2 ^ (aExp k + 2 * bExp k + k + 24)

/-- Index of the first trial of stage `k`: `S_0 = 0`, `S_{k+1} = S_k + T_k`. -/
def firstTrial : ℕ → ℕ
  | 0 => 0
  | k + 1 => firstTrial k + nTrials k

/-- Number of layers of the `k`-th block: `L_k = 8 · 21^{S_{k+1}}`. -/
def blockLen (k : ℕ) : ℕ := 8 * 21 ^ firstTrial (k + 1)

/-- Spike depth `d_k = ⌈log₂(64 B_k² L_k / λ_k)⌉`, i.e. the least `d` with
`64 · 4^{b_k} · L_k · 2^{a_k} ≤ 2^d`. -/
def depth (k : ℕ) : ℕ := Nat.clog 2 (64 * 4 ^ bExp k * blockLen k * 2 ^ aExp k)

/-- Layer spacing `D_k = d_k + 2`. -/
def spacing (k : ℕ) : ℕ := depth k + 2

/-- Base shift of the `k`-th block: `U_0 = 0`, `U_{k+1} = U_k + L_k D_k + d_k`. -/
def shift : ℕ → ℕ
  | 0 => 0
  | k + 1 => shift k + blockLen k * spacing k + depth k

/-! ### Trials and the exponent sequence (identical to #996) -/

/-- The stage containing trial `s`: the largest `k ≤ s` with `S_k ≤ s`. -/
def stage (s : ℕ) : ℕ := Nat.findGreatest (fun k => firstTrial k ≤ s) s

/-- Length of trial `s`: `ℓ_s = 20 · 21^s`. -/
def trialLen (s : ℕ) : ℕ := 20 * 21 ^ s

/-- Start offset of trial `s`: `M_0 = 0`, `M_{s+1} = M_s + (L_k + 2) D_k` with `k = stage s`. -/
def trialStart : ℕ → ℕ
  | 0 => 0
  | s + 1 => trialStart s + (blockLen (stage s) + 2) * spacing (stage s)

/-- The trial containing global index `j`: `s = ⌊log₂₁ (j+1)⌋`. -/
def trialOf (j : ℕ) : ℕ := Nat.log 21 (j + 1)

/-- The `j`-th selected exponent `m_j = M_s + r D_{stage s}`, `s = trialOf j`, `r = j + 2 - 21^s`. -/
def mExp (j : ℕ) : ℕ :=
  trialStart (trialOf j) + (j + 2 - 21 ^ trialOf j) * spacing (stage (trialOf j))

/-- The lacunary sequence `n_j = 2^{m_j}`. -/
def nSeq (j : ℕ) : ℕ := 2 ^ mExp j

/-! ### The function -/

/-- The `k`-th block `F_k = √(λ_k/L_k) ∑_{q=1}^{L_k} φ_{d_k}(2^{U_k + q D_k} ·)`. -/
noncomputable def blk (k : ℕ) (x : 𝕋) : ℝ :=
  Erdos996.block (lam k) (blockLen k) (depth k) (spacing k) (shift k) x

/-- The `(k,q)` atom `φ_{d_k}(2^{U_k + q D_k} x)`. -/
noncomputable def atom (k q : ℕ) (x : 𝕋) : ℝ :=
  Erdos996.spike (depth k) ((2 ^ (shift k + q * spacing k) : ℕ) • x)

/-- Deterministic floor constant `c_k = λ_k / B_k`: `F_k ≥ -c_k`. -/
noncomputable def floorC (k : ℕ) : ℝ := lam k / sig k

/-- The nonnegative series `∑_k (F_k + c_k)` in `[0, ∞]`. -/
noncomputable def gPos (x : 𝕋) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (blk k x + floorC k)

/-- The counterexample, pointwise: `g = ∑_k (F_k + c_k) - ∑_k c_k`. -/
noncomputable def gFun (x : 𝕋) : ℝ :=
  (gPos x).toReal - ∑' k, floorC k

/-! ### Events -/

/-- Good event of trial `s`: some central layer `h ∈ [ℓ_s + 1, L_k + 1]` spikes. -/
def goodSet (s : ℕ) : Set 𝕋 :=
  ⋃ h ∈ Finset.Icc (trialLen s + 1) (blockLen (stage s) + 1),
    Erdos996.Asm.hitSet (depth (stage s)) (shift (stage s) + trialStart s + h * spacing (stage s))

/-- Stage event `S_k`: some trial of stage `k` is good. -/
def stageGood (k : ℕ) : Set 𝕋 :=
  ⋃ s ∈ Finset.Ico (firstTrial k) (firstTrial (k + 1)), goodSet s

end Con

end Erdos995
