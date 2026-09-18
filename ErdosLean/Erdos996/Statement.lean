import Mathlib

/-!
# Erdős Problem 996 (JSP-000829): statement

Source: <https://www.erdosproblems.com/996>, catalogued as JSP-000829 in
<https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000829>.

> Let `n₁ < n₂ < ⋯` be a lacunary sequence of integers, and let `f ∈ L²([0,1])`.
> Let `fₙ` be the `n`th partial sum of the Fourier series of `f`. Is there an absolute
> constant `C > 0` such that, if `‖f - fₙ‖₂ ≪ 1 / (log log log n)^C`, then
> `lim_{N → ∞} (1/N) ∑_{k ≤ N} f({α n_k}) = ∫₀¹ f` for almost every `α`?

The answer is **no** (B. S. Ho, arXiv:2604.18535, Corollary 1.4).

`IsLacunary`, `fourierPartial` and the shape of `Erdos996Statement` follow
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/996.lean` at commit
`a9fb8e86c0`, and `FormalConjecturesForMathlib/NumberTheory/Lacunary.lean`),
Apache License 2.0, copied here so that this project does not depend on that repository.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

/-- A sequence is lacunary if there is some `c > 1` with `c * n k < n (k + 1)` for all
sufficiently large `k` (as in formal-conjectures). -/
def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

/-- The symmetric Fourier partial sum `S_k f = ∑_{|i| ≤ k} f̂(i) e_i`. -/
noncomputable def fourierPartial {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT))
    (k : ℕ) : AddCircle T → ℂ :=
  fun x => ∑ i ∈ Icc (-k : ℤ) k, fourierCoeff f i • fourier i x

/-- The Fourier-tail hypothesis `‖f - S_k f‖₂ = O((log log log k)^{-C})`. -/
def FourierTailBound (C : ℝ) (f : Lp ℂ 2 (haarAddCircle (T := 1))) : Prop :=
  (fun k : ℕ => (eLpNorm (⇑f - fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k : ℕ => 1 / (log (log (log k))) ^ C)

/-- The lacunary averages `(1/N) ∑_{k < N} f(n_k x)` converge to `∫ f` for almost every `x`. -/
def LacunaryAveragesConverge (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) : Prop :=
  ∀ᵐ x ∂(haarAddCircle (T := 1)),
    Tendsto (fun N : ℕ => (∑ k ∈ range N, f (n k • x)) / N) atTop
      (𝓝 (∫ t, f t ∂haarAddCircle))

/-- Erdős's question (#996), literally: is there an absolute `C > 0` such that the Fourier-tail
bound forces a.e. convergence of lacunary averages, for every `f ∈ L²` and every lacunary `n`? -/
def Erdos996Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n → FourierTailBound C f → LacunaryAveragesConverge f n

/-- A strong lacunarity condition satisfied by the counterexample (`n_{k+1} ≥ 2 n_k`, `n 0 ≥ 1`). -/
def IsDyadicLacunary (n : ℕ → ℕ) : Prop := 1 ≤ n 0 ∧ ∀ k, 2 * n k ≤ n (k + 1)

lemma IsDyadicLacunary.isLacunary {n : ℕ → ℕ} (hn : IsDyadicLacunary n) : IsLacunary n := by
  refine ⟨3 / 2, by norm_num, Eventually.of_forall fun k => ?_⟩
  have hpos : ∀ k, 1 ≤ n k := by
    intro k
    induction k with
    | zero => exact hn.1
    | succ k ih => have := hn.2 k; omega
  have h1 : (1 : ℝ) ≤ n k := by exact_mod_cast hpos k
  have h2 : (2 : ℝ) * n k ≤ n (k + 1) := by exact_mod_cast hn.2 k
  linarith

end Erdos996
