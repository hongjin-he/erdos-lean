import Mathlib

/-!
# Erdős Problem 790 (JSP-000649): statement

Sources:
* <https://www.erdosproblems.com/790>: "Let `l(n)` be maximal such that if `A ⊂ ℤ` with
  `|A| = n` then there exists a sum-free `B ⊆ A` with `|B| ≥ l(n)` — that is, `B` is such that
  there are no solutions to `a₁ = a₂ + ⋯ + a_r` with `aᵢ ∈ B` all distinct.  Estimate `l(n)`.
  In particular, is it true that `l(n) n^{-1/2} → ∞`?  Is it true that `l(n) < n^{1-c}` for
  some `c > 0`?"
* TheJustinSunPrize/awards, `problems/catalog-*.md#JSP-000649`: "How large a subset of an
  arbitrary finite integer set can have no element equal to a sum of distinct other elements?"
* `google-deepmind/formal-conjectures` has no file for problem 790 (checked 2026-09-19), so the
  statement below is written from scratch.

Answer (Samuel Korsky, *Large Sum-Free Subsets of Sets of Integers*, preprint dated
13 September 2026, Theorem 1; posted as a proof claim on
<https://www.erdosproblems.com/forum/thread/790/proof-claims>; the paper credits GPT Astra with
the main idea): `l(n) ≫ n / (log n)²`.  Hence `l(n) n^{-1/2} → ∞` (yes), `l(n) ≥ n^{1-ε}`
eventually for every `ε > 0`, so `l(n) < n^{1-c}` fails for every `c > 0` (no), and
`l(n) = n^{1-o(1)}` (the Choi–Komlós–Szemerédi conjecture).  Together with the trivial
`l(n) ≤ n` this determines the exponent of `l(n)`.

Scope: the sharper upper bound `l(n) ≪ n / log n` of Choi, Komlós and Szemerédi (Trans. Amer.
Math. Soc. 212 (1975), 307–313) is not formalized here, and the logarithmic gap between
`n / (log n)²` and `n / log n` remains open.
-/

namespace Erdos790

open Filter

/-- `B` is sum-free in Erdős's strong sense: no element of `B` is the sum of two or more
distinct *other* elements of `B` (i.e. no `a₁ = a₂ + ⋯ + a_r`, `r ≥ 3`, `aᵢ ∈ B` distinct). -/
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ x ∈ B, ∀ S ⊆ B, x ∉ S → 2 ≤ S.card → ∑ s ∈ S, s ≠ x

/-- `l n`: the largest `k` such that every `n`-element set of integers contains a sum-free
subset with at least `k` elements (literal transcription of "`l(n)` maximal such that …"). -/
noncomputable def l (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ k ≤ B.card}

/-- The full answer to Erdős Problem 790:
1. `l(n) ≥ c n / (log n)²` for all `n ≥ 2` (Korsky's bound);
2. `l(n) ≤ n` (trivial upper bound; with 1 and 4 the growth exponent of `l` is exactly `1`);
3. `l(n) / √n → ∞` (first question: **yes**);
4. for every `ε > 0`, eventually `n^{1-ε} ≤ l(n)`, i.e. `l(n) = n^{1-o(1)}`;
5. there is no `c > 0` with `l(n) < n^{1-c}` (not even for infinitely many `n`)
   (second question: **no**). -/
def Erdos790Answer : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ l n) ∧
  (∀ n : ℕ, l n ≤ n) ∧
  Tendsto (fun n : ℕ => (l n : ℝ) / Real.sqrt n) atTop atTop ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ l n) ∧
  ¬ (∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c))

end Erdos790
