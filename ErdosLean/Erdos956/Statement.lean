import Mathlib

/-!
# Erdős Problem 956 (JSP-000796): statement

Source: <https://www.erdosproblems.com/956>, catalogued as JSP-000796 in
<https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000796>.

> If `C, D ⊆ ℝ²` then the distance between `C` and `D` is `δ(C,D) = inf_{c ∈ C, d ∈ D} ‖c - d‖`.
> Let `h(n)` be the maximal number of unit distances between disjoint convex translates. That is,
> the maximal `m` such that there is a compact convex set `C ⊂ ℝ²` and a set `X` of size `n` such
> that all `(C + x)_{x ∈ X}` are disjoint and there are `m` pairs `x₁, x₂ ∈ X` such that
> `δ(C + x₁, C + x₂) = 1`.
>
> Determine `h(n)` — in particular, prove that there exists a constant `c > 0` such that
> `h(n) > n^{1+c}` for all large `n`.

Known results.
* Upper bound `h(n) ≪ n^{4/3}`: P. Erdős and J. Pach, *Variations on the theme of repeated
  distances*, Combinatorica 10 (1990), 261–269 (doi:10.1007/BF02122780).
* Matching lower bound `h(n) ≫ n^{4/3}` (hence `h(n) = Θ(n^{4/3})`): announced by P. Valtr,
  *The unit-distance problem for convex sets*, Oberwolfach Reports 2 (2005), Report 17/2005
  (Discrete Geometry), doi:10.4171/OWR/2005/17; the parabolic-grid mechanism is in Valtr's
  manuscript *Strictly convex norms allowing many unit distances and related touching questions*
  (<https://kam.mff.cuni.cz/~valtr/n.pdf>).  A self-contained write-up adapting Valtr's
  mechanism to disjoint translates is the note *Unit distances between disjoint convex
  translates* (27 April 2026, generated with GPT-5.5 Pro and posted by P. Chojecki on the
  erdosproblems.com forum), <https://www.ulam.ai/research/erdos956.pdf>; below it is called
  "the note".  The construction formalized here follows the note.

This file formalizes the lower bound only.  The Erdős–Pach upper bound is stated
(`ErdosPachUpperBound`) but not proved here.  The statement file was written from scratch
(formal-conjectures has no file for #956).

Conventions.
* The plane is `E = EuclideanSpace ℝ (Fin 2)` with the Euclidean norm.
* `C + x` is the image of `C` under `c ↦ c + x`.
* "pairs" are unordered pairs of distinct points of `X` (elements of `Sym2 E`).
* The problem says "compact convex set"; we additionally require `C` nonempty (for `C = ∅` every
  `δ` is `sInf ∅ = 0 ≠ 1`, so this changes nothing).
* `h n` is the supremum (in `ℕ`) of the achievable counts; the set of counts is bounded by
  `|X.sym2|`, so this is a genuine maximum.  (If it were unbounded `sSup` would be the junk value
  `0`, and the lower bounds below would be false; so they certify the definition is meaningful.)
-/

open Filter

namespace Erdos956

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- `δ(A, B) = inf {‖a - b‖ : a ∈ A, b ∈ B}`. -/
noncomputable def setDist (A B : Set E) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, r = ‖x - y‖}

/-- The translate `C + x`. -/
def translate (C : Set E) (x : E) : Set E := (fun c => c + x) '' C

/-- `(C, X)` is admissible: `C` is a nonempty compact convex set and the translates `C + x`,
`x ∈ X`, are pairwise disjoint. -/
def Admissible (C : Set E) (X : Finset E) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ C.Nonempty ∧
    (X : Set E).Pairwise fun x y => Disjoint (translate C x) (translate C y)

/-- The unordered pairs `{x₁, x₂}` of distinct points of `X` with `δ(C + x₁, C + x₂) = 1`. -/
noncomputable def unitPairs (C : Set E) (X : Finset E) : Finset (Sym2 E) := by
  classical
  exact X.sym2.filter fun z =>
    ∃ x y, z = s(x, y) ∧ x ≠ y ∧ setDist (translate C x) (translate C y) = 1

/-- `h(n)`: the maximal number of unit distances between `n` disjoint translates of a compact
convex set. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (C : Set E) (X : Finset E),
    X.card = n ∧ Admissible C X ∧ (unitPairs C X).card = m}

/-- **Erdős #956, the question as posed**: there is `c > 0` with `h(n) > n^{1+c}` for all
large `n`. -/
def Erdos956Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < h n

/-- The sharp lower bound `h(n) ≫ n^{4/3}`. -/
def Erdos956LowerBound : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, c₀ * (n : ℝ) ^ ((4 : ℝ) / 3) ≤ h n

/-- Every exponent `c < 1/3` works (the range allowed by the Erdős–Pach upper bound). -/
def Erdos956AllExponents : Prop :=
  ∀ c : ℝ, c < 1 / 3 → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < h n

/-- The Erdős–Pach upper bound `h(n) ≪ n^{4/3}` (published, [ErPa90]).  It is *stated* here for
reference only; it is not proved in this project (its proof needs the crossing lemma). -/
def ErdosPachUpperBound : Prop :=
  ∃ K : ℝ, ∀ n : ℕ, (h n : ℝ) ≤ K * (n : ℝ) ^ ((4 : ℝ) / 3)

end Erdos956
