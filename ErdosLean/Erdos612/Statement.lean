import Mathlib

/-!
# Erdős Problem 612 (JSP-000497): statement

Sources:
* <https://www.erdosproblems.com/612> (accessed 2026-09-18, still marked OPEN there):
  "Let `G` be a connected graph with `n` vertices, minimum degree `d`, and diameter `D`.
  Show if that `G` contains no `K_{2r}` and `(r-1)(3r+2) ∣ d` then
  `D ≤ 2(r-1)(3r+2)/(2r²-1) · n/d + O(1)`, and if `G` contains no `K_{2r+1}` and `3r-1 ∣ d`
  then `D ≤ (3r-1)/r · n/d + O(1)`."  ([EPPT89] P. Erdős, J. Pach, R. Pollack, Zs. Tuza,
  *Radius, diameter, and minimum degree*, J. Combin. Theory Ser. B 47 (1989) 73–79,
  doi:10.1016/0095-8956(89)90066-X.)
* TheJustinSunPrize/awards, `problems/catalog-0401-0500.md#JSP-000497`: "Can minimum degree
  bound the diameter of a graph excluding a clique of prescribed size?" (status Open).
* `google-deepmind/formal-conjectures` has no file `ErdosProblems/612.lean` (checked
  2026-09-18).  The statement below was written independently for this project from the text
  above; it follows the graphs-on-`Fin n` convention of Formal Conjectures and is similar in
  shape to the draft by Kenta Kitamura in formal-conjectures issue #828 (which also gives two
  readings of `O(1)`).  No code is copied from that draft, from `KitaKen1/erdos-612-lean`, or
  from any other Lean development.

The answer is **no** for both parts:
* part (i) fails for `r = 2`, `d = 24`: É. Czabarka, I. Singgih, L. A. Székely,
  *Counterexamples to a conjecture of Erdős, Pach, Pollack and Tuza*, J. Combin. Theory Ser. B
  151 (2021) 38–45, doi:10.1016/j.jctb.2021.06.001 [CSS21].  Theorem and figure numbers in this
  development refer to the preprint arXiv:2009.02611v1 (titled *On the maximum diameter of
  k-colorable graphs*; it contains the same construction): §3, Figure 1, Lemma 5 and
  Theorem 6, with `r = 2` (so `s = r - 1 = 1`);
* part (ii) fails for `r = 4`, `d = 8778`: Hangdi Chen, Yaojun Chen, *Counterexamples to two
  conjectures on the diameter of clique-free graphs*, arXiv:2609.03346v1 (2026) [CC26],
  §2, Theorem 2.7 (`δ ≥ 6(6r-5)(2r-1)(3r-1) = 8778` for `r = 4`).

Prior Lean work: `KitaKen1/erdos-612-lean` (Kenta Kitamura) proves in Lean that the odd case
with `r = 2` (`K₅`-free) holds and, since 2026-09-08, that the odd case with `r = 3`
(`K₇`-free) fails in the uniform reading of `O(1)`.  This development is independent of it;
its contribution is a single theorem covering both parts of the statement, in both readings of
`O(1)`, including a refutation of part (i).

## Reading of `O(1)`
The conjecture is asymptotic "as `n → ∞`" (EPPT89; CSS21 Conjecture 1; CC26 Conjecture 1.2),
for fixed `r` and `d`.  We formalise the **weakest** reading: for every admissible `r` and
every admissible minimum degree `d ≥ 2` there is a constant `C = C(r, d)` such that every
connected `K_s`-free graph with minimum degree exactly `d` satisfies `D ≤ c · n / d + C`
(`DiamBound`).  We also record the stronger, uniform reading in which `C` does not depend on
`d` (`DiamBoundUniform`), and refute both.  Graphs are on `Fin n` (the formal-conjectures
convention); `DiamBoundType` is the same statement over arbitrary finite vertex types.

Degenerate `r` are harmless: we quantify over `r ≥ 2` exactly as in CC26 Conjecture 1.2
("Let `r, δ ≥ 2`"), which only makes the conjecture weaker and its refutation stronger.

## Scope
Each part is formalised as a statement about all `r ≥ 2` (`PartI`, `PartII`), and the answer
refutes each of them by one explicit value of `r`.  The case-by-case status for individual `r`
(see the README) is not formalised here.
-/

open SimpleGraph

namespace Erdos612

/-- **Weak reading.**  For every minimum degree `d ≥ 2` divisible by `m` there is a constant
`C` (depending on `d`) such that every connected `K_s`-free graph on `Fin n` with minimum
degree `d` has diameter at most `c · n / d + C`. -/
def DiamBound (s m : ℕ) (c : ℝ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → m ∣ d → ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree s → G.minDegree = d →
      (G.diam : ℝ) ≤ c * (n : ℝ) / (d : ℝ) + C

/-- **Uniform reading.**  One constant `C` works for all graphs (all `n` and all `d`). -/
def DiamBoundUniform (s m : ℕ) (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree s → 2 ≤ G.minDegree → m ∣ G.minDegree →
      (G.diam : ℝ) ≤ c * (n : ℝ) / (G.minDegree : ℝ) + C

/-- `DiamBound` over arbitrary finite vertex types (equivalent; used internally). -/
def DiamBoundType (s m : ℕ) (c : ℝ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → m ∣ d → ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.Connected → G.CliqueFree s → G.minDegree = d →
      (G.diam : ℝ) ≤ c * (Fintype.card V : ℝ) / (d : ℝ) + C

/-- The EPPT coefficient for `K_{2r}`-free graphs: `2(r-1)(3r+2)/(2r²-1)`. -/
noncomputable def evenCoeff (r : ℕ) : ℝ :=
  2 * ((r : ℝ) - 1) * (3 * (r : ℝ) + 2) / (2 * (r : ℝ) ^ 2 - 1)

/-- The EPPT coefficient for `K_{2r+1}`-free graphs: `(3r-1)/r`. -/
noncomputable def oddCoeff (r : ℕ) : ℝ := (3 * (r : ℝ) - 1) / (r : ℝ)

/-- Part (i) at a fixed `r`: `K_{2r}`-free, `(r-1)(3r+2) ∣ d`. -/
def EvenConjAt (r : ℕ) : Prop := DiamBound (2 * r) ((r - 1) * (3 * r + 2)) (evenCoeff r)

/-- Part (ii) at a fixed `r`: `K_{2r+1}`-free, `3r-1 ∣ d`. -/
def OddConjAt (r : ℕ) : Prop := DiamBound (2 * r + 1) (3 * r - 1) (oddCoeff r)

/-- Erdős #612, part (i). -/
def PartI : Prop := ∀ r : ℕ, 2 ≤ r → EvenConjAt r

/-- Erdős #612, part (ii). -/
def PartII : Prop := ∀ r : ℕ, 2 ≤ r → OddConjAt r

/-- Part (i), uniform reading. -/
def PartIUniform : Prop :=
  ∀ r : ℕ, 2 ≤ r → DiamBoundUniform (2 * r) ((r - 1) * (3 * r + 2)) (evenCoeff r)

/-- Part (ii), uniform reading. -/
def PartIIUniform : Prop :=
  ∀ r : ℕ, 2 ≤ r → DiamBoundUniform (2 * r + 1) (3 * r - 1) (oddCoeff r)

/-- **Erdős #612** as a single conjecture (both parts). -/
def Erdos612Conjecture : Prop := PartI ∧ PartII

/-- The answer recorded by this development: **both parts are false** (in both readings).
`Main.lean` proves `erdos_612 : Erdos612Answer`. -/
def Erdos612Answer : Prop :=
  ¬ PartI ∧ ¬ PartII ∧ ¬ PartIUniform ∧ ¬ PartIIUniform ∧ ¬ EvenConjAt 2 ∧ ¬ OddConjAt 4

end Erdos612
