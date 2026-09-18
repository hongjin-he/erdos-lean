import Mathlib

/-!
# Erdős Problem 265 (JSP-000229): statement

Sources:
* <https://www.erdosproblems.com/265> ([ErGr80, p.64], [Er88c, p.104]):
  "Let `1 ≤ a₁ < a₂ < ⋯` be an increasing sequence of integers. How fast can `aₙ → ∞` grow if
  `∑ 1/aₙ` and `∑ 1/(aₙ - 1)` are both rational?"
  Erdős believed that `aₙ^{1/n} → ∞` is possible, but `aₙ^{1/2ⁿ} → 1` is necessary.
* TheJustinSunPrize/awards, `problems/catalog-0201-0300.md#JSP-000229` (title currently the
  placeholder "ambiguous statement", cf. awards issue #835):
  "How fast can an increasing integer sequence grow if both its reciprocal sum and the
  reciprocal sum after subtracting one from every term are rational?"

The statement below records what is currently known about the "how fast" question, in the
form predicted by Erdős.  It is **not** a complete answer: the optimal doubly exponential
exponent remains open (see erdosproblems.com/265).  Writing `β*` for the supremum of all `β`
such that some admissible sequence has `aₙ^{1/βⁿ} → ∞`, the two halves below give
`51/50 ≤ β* ≤ 2`.

* **growth half** (V. Kovač and T. Tao, *On several irrationality problems for Ahmes series*,
  arXiv:2406.17593 v4, Theorem 2.8 / Corollary 2.9 with `d = 2`, proved in §7; published in
  Acta Math. Hungar. 175 (2025), 572–608, doi:10.1007/s10474-025-01528-0; shifted by one):
  there is such a sequence with `aₙ^{1/βⁿ} → ∞` for some `β > 1` (doubly exponential growth);
  in particular `aₙ^{1/n} → ∞` (Erdős's first belief).  Our formalisation follows the
  argument of §7 but with modified, explicit parameters (`N_k = 4^{m_k}`, `M_k = 2^{m_k}`,
  `f2 x = 1/(x(x-1))`, `β = 51/50`), so the constants differ from those in the paper;
* **barrier half** (Erdős's second belief): every such sequence satisfies `aₙ^{1/2ⁿ} → 1`; in
  particular `limsup aₙ^{1/2ⁿ} > 1` is impossible.  The mathematics of this half is due to
  Kenta Kitamura, who also gave the first Lean proof of it
  (github.com/KitaKen1/erdos-265-lean, 2026-09-07, Apache-2.0).  The proof here is an
  independent Lean formalisation of Kitamura's argument (tail envelope, square recurrence,
  second residual); no proof code was copied, but the shapes of `IsRationalPair` and
  `Erdos265LimsupNegative` are taken from that repository (see `NOTICE`).

Conventions.  Sequences are indexed from `0`.  Growth statements of the form
`aₙ^{1/βⁿ} → ∞`, `aₙ^{1/n} → ∞`, `aₙ^{1/2ⁿ} → 1` are invariant under an index shift, so this is
harmless.  We require `2 ≤ a 0` (so that every `aₙ - 1 ≥ 1` and `1/(aₙ - 1)` is a genuine
term; with `a 0 = 1` the second series is undefined), `StrictMono a` (the increasing condition,
cf. V. Kovač's comment on the forum page: without it the question is trivial), and explicit
summability (Lean's `tsum` of a non-summable series is `0`, which is rational).
-/

open Filter Topology

namespace Erdos265

/-- `a` is admissible for Erdős #265: strictly increasing integers `≥ 2`, and both
`∑ 1/aₙ` and `∑ 1/(aₙ - 1)` converge to rational numbers.  (Same shape as
`IsRationalPairSequence` in KitaKen1/erdos-265-lean, Apache-2.0.) -/
def IsRationalPair (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ 2 ≤ a 0 ∧
    Summable (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ)) ∧
    Summable (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1)) ∧
    (∃ q : ℚ, ∑' n : ℕ, (1 : ℝ) / (a n : ℝ) = (q : ℝ)) ∧
    (∃ q : ℚ, ∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) - 1) = (q : ℝ))

/-- **Erdős #265, known bounds** (not a complete answer: the optimal exponent is open).
1. (Kovač–Tao) some admissible sequence grows doubly exponentially: `aₙ^{1/βⁿ} → ∞`, `β > 1`;
2. (Erdős's first belief, a consequence of 1) some admissible sequence has `aₙ^{1/n} → ∞`;
3. (Erdős's second belief; Kitamura) every admissible sequence has `aₙ^{1/2ⁿ} → 1`. -/
def Erdos265Statement : Prop :=
  (∃ a : ℕ → ℕ, IsRationalPair a ∧ ∃ β : ℝ, 1 < β ∧
      Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / β ^ n)) atTop atTop) ∧
  (∃ a : ℕ → ℕ, IsRationalPair a ∧
      Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop atTop) ∧
  (∀ a : ℕ → ℕ, IsRationalPair a →
      Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 1))

/-- The "limsup" sub-question in Kitamura's robust form (shape taken from
`erdos265_negative_answer` in KitaKen1/erdos-265-lean, Apache-2.0): no admissible sequence has
`c^{2ⁿ} ≤ aₙ` infinitely often for a fixed `c > 1`.  (Implied by item 3 above.) -/
def Erdos265LimsupNegative : Prop :=
  ¬ ∃ a : ℕ → ℕ, IsRationalPair a ∧
      ∃ c : ℝ, 1 < c ∧ ∃ᶠ n in atTop, c ^ (2 ^ n) ≤ (a n : ℝ)

end Erdos265
