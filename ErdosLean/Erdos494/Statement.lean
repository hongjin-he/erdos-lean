import Mathlib

/-!
# Erdős Problem 494 (JSP-000399): statement

Sources:
* <https://www.erdosproblems.com/494>: for `A ⊂ ℂ` finite and `k ≥ 1`, let `A_k` be the
  multiset of all sums of `k` distinct elements of `A`.  Is `A` determined by `A_k` and `|A|`
  (for `k > 2`)?  The site notes the literal answer is *no* (`|A| = k`: Kruyt; `|A| = 2k`: Tao)
  and that "presumably some condition like `|A|` sufficiently large is intended"; the recorded
  positive answer is Gordon–Fraenkel–Straus [GFS62].
* TheJustinSunPrize/awards, `problems/catalog-0301-0400.md#JSP-000399`:
  "Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number
  of distinct elements?" — status *Solved*, references [SeSt58], [GFS62].
* `google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/494.lean`
  (commit `1e668fa332517af1c1e79d564cbe84de1cd111b8`).  The definitions `sumMultiset`,
  `Erdos494Unique` and the statements of `erdos_494.variants.gordon_fraenkel_straus`,
  `k_eq_card`, `card_eq_2k` are copied verbatim from that file (Apache License 2.0,
  Copyright 2025 The Formal Conjectures Authors), without depending on that repository.

[GFS62] B. Gordon, A. S. Fraenkel, E. G. Straus, *On the determination of sets by the sets of
sums of a certain order*, Pacific J. Math. 12 (1962), 187–196, §4 Theorem.

`Erdos494Full` records the complete answer: the literal question fails for `|A| = k` and
`|A| = 2k` (every `k > 2`), and it holds for every `k > 2` once `|A|` is large enough.
-/

open Filter

namespace Erdos494

/-- `A_k`: the multiset of all sums of `k` distinct elements of `A` (verbatim from
formal-conjectures). -/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

/-- Sets of size `card` are determined by their `k`-sum multiset (verbatim from
formal-conjectures). -/
def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

/-- Gordon–Fraenkel–Straus [GFS62]: `erdos_494.variants.gordon_fraenkel_straus` of
formal-conjectures. -/
def GFSStatement : Prop :=
  ∀ k > 2, ∀ᶠ card in atTop, Erdos494Unique k card

/-- The complete recorded answer to JSP-000399 / Erdős #494:
* Kruyt: uniqueness fails when `|A| = k` (`erdos_494.variants.k_eq_card`);
* Tao: uniqueness fails when `|A| = 2k` (`erdos_494.variants.card_eq_2k`);
* Gordon–Fraenkel–Straus: for every `k > 2` uniqueness holds for all sufficiently large `|A|`
  (`erdos_494.variants.gordon_fraenkel_straus`). -/
def Erdos494Full : Prop :=
  (∀ k > 2, ¬Erdos494Unique k k) ∧ (∀ k > 2, ¬Erdos494Unique k (2 * k)) ∧ GFSStatement

end Erdos494
