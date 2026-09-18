import Mathlib

/-!
# The Duffin–Schaeffer conjecture (JSP-000832, Erdős #999): statement

Sources:
* TheJustinSunPrize/awards, `problems/catalog-0801-0900.md#JSP-000832` ("Duffin-Schaeffer
  conjecture"): "Is divergence of the corresponding totient-weighted series equivalent to almost
  every real number having infinitely many reduced rational approximations at the prescribed
  denominator-dependent accuracy?"  Status: Solved, by
  D. Koukoulopoulos and J. Maynard, *On the Duffin–Schaeffer conjecture*,
  Ann. of Math. (2) 192 (2020), 251–307 (arXiv:1907.04593), Theorem 1.
* <https://www.erdosproblems.com/999>: "For any function `f : ℕ → ℕ` the property that, for almost
  all `α`, `|α - p/q| < f(q)/q` has infinitely many solutions with `(p,q) = 1`, is equivalent to
  `∑_{q ≥ 1} φ(q) f(q)/q = ∞`."

The catalogued theorem is for an arbitrary real accuracy function `ψ : ℕ → [0, ∞)`
(Koukoulopoulos–Maynard, Theorem 1, plus the easy converse (1.5) via Borel–Cantelli).
The integer-valued wording of erdosproblems.com is recorded separately (`Erdos999Statement`)
and follows from the real one.

`DuffinSchaefferStatement` covers every reading of the problem:
* strict inequality `|α - a/q| < ψ(q)/q` (erdosproblems.com) and non-strict `≤` (KM (1.7));
* "almost every real `α`" and "almost every `α ∈ [0,1]`" (KM Theorem 1);
* both implications, and additionally the Borel–Cantelli direction in its strong form
  "convergent series ⇒ almost every `α` has only finitely many solutions".

A solution is a pair `(a, q) ∈ ℤ × ℕ` with `q ≥ 1` and `gcd(a, q) = 1`
("infinitely many coprime solutions `a` and `q`").  This file was written from scratch for this
project; it does not copy any other formalization.
-/

open MeasureTheory

namespace DuffinSchaeffer

/-- The reduced solutions `(a, q)`, `q ≥ 1`, `gcd(a, q) = 1`, of `|α - a/q| < ψ(q)/q`. -/
def solutions (ψ : ℕ → ℝ) (α : ℝ) : Set (ℤ × ℕ) :=
  {s | 0 < s.2 ∧ Int.gcd s.1 s.2 = 1 ∧ |α - s.1 / s.2| < ψ s.2 / s.2}

/-- The reduced solutions `(a, q)`, `q ≥ 1`, `gcd(a, q) = 1`, of `|α - a/q| ≤ ψ(q)/q`
(the inequality (1.7) of Koukoulopoulos–Maynard). -/
def solutionsLe (ψ : ℕ → ℝ) (α : ℝ) : Set (ℤ × ℕ) :=
  {s | 0 < s.2 ∧ Int.gcd s.1 s.2 = 1 ∧ |α - s.1 / s.2| ≤ ψ s.2 / s.2}

/-- The Duffin–Schaeffer series `∑_{q ≥ 1} φ(q) ψ(q) / q` diverges.  (The `q = 0` term is `0`
in Lean; for `ψ ≥ 0` the terms are nonnegative, so "not summable" means "sums to `+∞`".) -/
def DSSeriesDiverges (ψ : ℕ → ℝ) : Prop :=
  ¬ Summable (fun q : ℕ => (Nat.totient q : ℝ) * ψ q / q)

/-- **The Duffin–Schaeffer theorem** (Koukoulopoulos–Maynard 2020 + Borel–Cantelli), for every
`ψ : ℕ → [0, ∞)`:
1. a.e. real `α` has infinitely many reduced solutions of `|α - a/q| < ψ(q)/q`
   iff `∑ φ(q)ψ(q)/q = ∞`;
2. the same with `≤`;
3. the same for a.e. `α ∈ [0,1]` (with `<`; the `≤` version on `[0,1]` follows from 2 and 4);
4. if `∑ φ(q)ψ(q)/q < ∞`, then a.e. `α` has only finitely many solutions even with `≤`. -/
def DuffinSchaefferStatement : Prop :=
  ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q) →
    ((∀ᵐ α : ℝ, (solutions ψ α).Infinite) ↔ DSSeriesDiverges ψ) ∧
    ((∀ᵐ α : ℝ, (solutionsLe ψ α).Infinite) ↔ DSSeriesDiverges ψ) ∧
    ((∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), (solutions ψ α).Infinite) ↔
      DSSeriesDiverges ψ) ∧
    (¬ DSSeriesDiverges ψ → ∀ᵐ α : ℝ, (solutionsLe ψ α).Finite)

/-- Erdős #999, literally as written on erdosproblems.com (`f : ℕ → ℕ`, strict inequality). -/
def Erdos999Statement : Prop :=
  ∀ f : ℕ → ℕ,
    (∀ᵐ α : ℝ, (solutions (fun q => (f q : ℝ)) α).Infinite) ↔
      DSSeriesDiverges (fun q => (f q : ℝ))

end DuffinSchaeffer
