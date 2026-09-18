import Mathlib

/-!
# Erdős Problem 995 (JSP-000828): statement

Source: <https://www.erdosproblems.com/995>, catalogued as JSP-000828 in
<https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000828>.

> Let `n₁ < n₂ < ⋯` be a lacunary sequence of integers and `f ∈ L²([0,1])`. Estimate the
> growth of, for almost all `α`, `∑_{1 ≤ k ≤ N} f({α n_k})`. For example, is it true that,
> for almost all `α`, `∑_{1 ≤ k ≤ N} f({α n_k}) = o(N √(log log N))`?

## The answer formalised here

* **Upper bound** (stated by Erdős, *Problems and results on diophantine approximations*,
  Compositio Math. 16 (1964), 52–65, p. 58; elementary proof in Ho, arXiv:2604.18535,
  Remark 7.1): for every lacunary `(n_k)`, every `f ∈ L²` and every `ε > 0`,
  for almost every `α`, `∑_{k ≤ N} f(α n_k) = o(N (log N)^{1/2 + ε})`.
* **Lower bound** (B. S. Ho, arXiv:2604.18535 v2, Theorem 1.6 at `p = 2`): there are a real-valued
  mean-zero `f ∈ L²` and a lacunary `(n_k)` with `n_{k+1} ≥ 2 n_k` such that for almost every
  `α` and every `ε > 0`, `limsup_N (∑_{k ≤ N} f(α n_k)) / (N (log N)^{1/2 - ε}) = +∞`.
* Hence the worst-case almost-sure growth is `N (log N)^{1/2 + o(1)}`: the critical exponent of
  `log N` is exactly `1/2` (`Erdos995CriticalExponent`), and the answer to the "for example"
  question (`o(N √(log log N))`) is **no** (`¬ LogLogQuestion`).

Conventions. The circle `[0,1)` is `AddCircle (1 : ℝ)` with its Haar probability measure, and
`f({α n_k})` is `f (n_k • α)`, exactly as in `google-deepmind/formal-conjectures`
(`FormalConjectures/ErdosProblems/996.lean`, commit `a9fb8e86c0`, Apache License 2.0), from which
the definition of `IsLacunary` is copied (formal-conjectures has no statement of #995). Sums run
over `k < N` (0-indexed), which is the same as `1 ≤ k ≤ N` up to relabelling.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos995

/-- A sequence is lacunary if there is some `c > 1` with `c * n k < n (k + 1)` for all
sufficiently large `k` (as in formal-conjectures). -/
def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

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

/-- The partial sum `∑_{k < N} f(n_k x)`. -/
noncomputable def lacSum (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ)
    (x : AddCircle (1 : ℝ)) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, f (n k • x)

/-- Erdős's upper bound: `∑_{k<N} f(n_k x) = o(N (log N)^{1/2+ε})` a.e., for every lacunary `n`,
every `f ∈ L²` and every `ε > 0`. -/
def ErdosUpperBound : Prop :=
  ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n → ∀ ε : ℝ, 0 < ε →
    ∀ᵐ x ∂(haarAddCircle (T := 1)),
      (fun N : ℕ => lacSum f n x N) =o[atTop]
        (fun N : ℕ => (N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 + ε))

/-- Ho's lower bound: a real-valued mean-zero `f ∈ L²` and a lacunary `n` (`n_{k+1} ≥ 2 n_k`) such
that for a.e. `x` and every `ε > 0`,
`limsup_N (∑_{k<N} f(n_k x)) / (N (log N)^{1/2-ε}) = +∞`, i.e. for every `C` the partial sum
exceeds `C · N (log N)^{1/2-ε}` for infinitely many `N`. -/
def HoLowerBound : Prop :=
  ∃ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsDyadicLacunary n ∧ (∀ᵐ x ∂(haarAddCircle (T := 1)), (f x).im = 0) ∧
    ∫ x, f x ∂(haarAddCircle (T := 1)) = 0 ∧
    ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∃ᶠ N : ℕ in atTop,
      C * ((N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε)) ≤ (lacSum f n x N).re

/-- The concrete question of Erdős: is `∑_{k<N} f(n_k x) = o(N √(log log N))` a.e. for every
lacunary `n` and every `f ∈ L²`? -/
def LogLogQuestion : Prop :=
  ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n →
    ∀ᵐ x ∂(haarAddCircle (T := 1)),
      (fun N : ℕ => lacSum f n x N) =o[atTop]
        (fun N : ℕ => (N : ℝ) * Real.sqrt (Real.log (Real.log N)))

/-- "The universal a.e. growth bound `O(N (log N)^θ)` holds": for every lacunary `n` and `f ∈ L²`,
a.e. `∑_{k<N} f(n_k x) = O(N (log N)^θ)`. -/
def GrowthBoundHolds (θ : ℝ) : Prop :=
  ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n →
    ∀ᵐ x ∂(haarAddCircle (T := 1)),
      (fun N : ℕ => lacSum f n x N) =O[atTop] (fun N : ℕ => (N : ℝ) * Real.log N ^ θ)

/-- The critical exponent of `log N` is `1/2`: the growth bound `O(N (log N)^θ)` holds for every
`θ > 1/2` and fails for every `θ < 1/2` (so the worst-case growth is `N (log N)^{1/2+o(1)}`). -/
def Erdos995CriticalExponent : Prop :=
  (∀ θ : ℝ, 1 / 2 < θ → GrowthBoundHolds θ) ∧ (∀ θ : ℝ, θ < 1 / 2 → ¬ GrowthBoundHolds θ)

/-- **The full answer to Erdős Problem 995** as recorded in the literature:
Erdős's upper bound, Ho's lower bound, the resulting critical exponent `1/2`, and the negative
answer to the `o(N √(log log N))` question. -/
def Erdos995Answer : Prop :=
  ErdosUpperBound ∧ HoLowerBound ∧ Erdos995CriticalExponent ∧ ¬ LogLogQuestion

end Erdos995
