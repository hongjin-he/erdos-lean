import ErdosLean.Erdos612.Statement

/-!
# Erdős Problem 612 (JSP-000497), all `r`: statement

This file **reuses** the definitions of `ErdosLean/Erdos612/Statement.lean` verbatim
(`DiamBound`, `DiamBoundUniform`, `evenCoeff`, `oddCoeff`, `EvenConjAt`, `OddConjAt`); nothing is redefined.
See that file for the sources and for the (weakest) reading of `O(1)` that is formalised:
`EvenConjAt r` / `OddConjAt r` say that for **every** admissible minimum degree `d ≥ 2` there
is a constant `C = C(r, d)` with `diam G ≤ c · n / d + C` for all connected `K_s`-free graphs
`G` on `Fin n` with `minDegree G = d`.

Recall (Erdős–Pach–Pollack–Tuza, JCTB 47 (1989); erdosproblems.com/612; catalogue entry
`TheJustinSunPrize/awards`, `problems/catalog-0401-0500.md#JSP-000497`):
* part (i) at `r`: `K_{2r}`-free, `(r-1)(3r+2) ∣ d`, coefficient `2(r-1)(3r+2)/(2r²-1)`;
* part (ii) at `r`: `K_{2r+1}`-free, `3r-1 ∣ d`, coefficient `(3r-1)/r`.

`google-deepmind/formal-conjectures` has no `ErdosProblems/612.lean` (checked again
2026-09-19 with `gh api`, HTTP 404), so nothing is taken from that repository.

## What is proved (`Main.lean`)
* `(∀ r ≥ 2, ¬ EvenConjAt r)`: part (i) is false for **every** `r ≥ 2`
  (Czabarka–Singgih–Székely, JCTB 151 (2021), arXiv:2009.02611, §3);
* `(∀ r ≥ 4, ¬ OddConjAt r)`: part (ii) is false for **every** `r ≥ 4`
  (H. Chen–Y. Chen, arXiv:2609.03346, §2, Theorem 2.7);
* the same two statements for the uniform reading `DiamBoundUniform` (one constant for all
  `d`), which is stronger than `DiamBound`, so its failure follows.

Part (ii) for `r ∈ {2, 3}` is **not** part of this statement.  Those two cases (the bound
holds for `r = 2`, i.e. `K₅`-free graphs, and fails for `r = 3`, i.e. `K₇`-free graphs) were
formalised earlier by Kenta Kitamura in `KitaKen1/erdos-612-lean`; no credit is claimed for
them here and no code from that repository is used.  The range `r ≥ 4` is exactly the range
covered by the Chen–Chen construction.
-/

namespace Erdos612

/-- **Erdős #612, all `r` (answer recorded here).**
Part (i) fails for every `r ≥ 2` and part (ii) fails for every `r ≥ 4`, in the weak reading
(`EvenConjAt`/`OddConjAt`, constant may depend on `d`) and in the uniform reading. -/
def Erdos612AllAnswer : Prop :=
  (∀ r : ℕ, 2 ≤ r → ¬ EvenConjAt r) ∧
  (∀ r : ℕ, 4 ≤ r → ¬ OddConjAt r) ∧
  (∀ r : ℕ, 2 ≤ r → ¬ DiamBoundUniform (2 * r) ((r - 1) * (3 * r + 2)) (evenCoeff r)) ∧
  (∀ r : ℕ, 4 ≤ r → ¬ DiamBoundUniform (2 * r + 1) (3 * r - 1) (oddCoeff r))

end Erdos612
