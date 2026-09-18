import Mathlib

/-!
# Erdős Problem 1199 (JSP-001004, Owings's question): statement

Sources:
* <https://www.erdosproblems.com/1199>:
  "Is it true that in any 2-colouring of ℕ there exists an infinite set `A` such that all
  elements of `A + A` are the same colour?"  (A conjecture of Owings, Amer. Math. Monthly
  Problem E2494, 1974; `A + A` includes the doubles `2a`.)
* TheJustinSunPrize/awards, `problems/catalog-1001-1022.md#JSP-001004`:
  "Does every two-coloring of the natural numbers contain an infinite set whose specified
  pairwise sums all have one color?"
* `google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/1199.lean` at commit
  `a14a7a739a` (theorem `Erdos1199.erdos_1199`, whose answer is still left open there).  The shape of
  `Erdos1199Statement` below is copied from that file (Apache License 2.0, Copyright 2026 The
  Formal Conjectures Authors), without depending on that repository.

The answer is **yes**: W. Huang, Z. Lian, S. Shao, R. Xiao, L. Xu, S. Zhang,
*An affirmative answer to Owings's sumset question*, arXiv:2607.17333 (v3), Theorem 1.1.

We record two versions:
* `Erdos1199Statement` — verbatim the formal-conjectures statement (colourings of `ℕ = {0,1,…}`,
  `A ⊆ ℕ`);
* `Erdos1199StatementPos` — the original formulation over the positive integers: the infinite
  set `A` consists of positive integers.  It trivially implies `Erdos1199Statement`
  (the colour of `0` is irrelevant because `A + A ⊆ {2,3,…}`).
-/

open Pointwise

namespace Erdos1199

/-- Erdős #1199 as stated in formal-conjectures (with `answer(True)`):
every 2-colouring of `ℕ` admits an infinite `A` with `A + A` monochromatic. -/
def Erdos1199Statement : Prop :=
  ∀ (color : ℕ → Fin 2), ∃ (A : Set ℕ),
    A.Infinite ∧ ∀ n ∈ (A + A), ∀ m ∈ (A + A), color n = color m

/-- Owings's original formulation over the positive integers: `A` is an infinite set of
positive integers and `A + A` (including all doubles `2a`) is monochromatic. -/
def Erdos1199StatementPos : Prop :=
  ∀ (color : ℕ → Fin 2), ∃ (A : Set ℕ),
    A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧ ∀ n ∈ (A + A), ∀ m ∈ (A + A), color n = color m

end Erdos1199
