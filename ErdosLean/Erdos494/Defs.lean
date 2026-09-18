import ErdosLean.Erdos494.Statement

/-!
# Erdős 494: shared definitions for the proof

* `gfsPoly s n j = Σ_{i=1}^{s} (-1)^{i-1} i^{j-1} C(n, s-i)` — the Selfridge–Straus /
  Gordon–Fraenkel–Straus polynomial ([GFS62] §3, equation (1)).
* `psum A j = Σ_{a ∈ A} a^j` and `ksumPsum A s j = Σ_{σ ∈ A_s} σ^j`.
* `hasseEval r1 r2 c i1 i2 x y` — the `(i1,i2)`-th Hasse derivative of the bivariate integer
  polynomial `P(X,Y) = Σ_{k1 ≤ r1, k2 ≤ r2} c k1 k2 X^k1 Y^k2`, evaluated at `(x, y)`.
  Polynomials are handled as bare coefficient arrays so that Siegel's lemma, the Taylor bound
  and the lower bound at rational points are all explicit finite sums.
* `binRoot r a b = (b/a)^{1/r}` — the real `r`-th root used in Mahler's reduction.
-/

namespace Erdos494

/-- `f_s(n, j) = Σ_{i=1}^{s} (-1)^{i-1} i^{j-1} C(n, s-i)`. -/
def gfsPoly (s n j : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 s, (-1) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (s - i) : ℤ)

/-- The number-theoretic core of [GFS62] §4: for fixed `s > 2`, `f_s(n, j) ≠ 0` for all
`j ≥ 1` once `n` is large. -/
def GFSCore : Prop :=
  ∀ s > 2, ∀ᶠ n in Filter.atTop, ∀ j ≥ 1, gfsPoly s n j ≠ 0

/-- Power sum `Σ_{a ∈ A} a^j`. -/
def psum (A : Finset ℂ) (j : ℕ) : ℂ := ∑ a ∈ A, a ^ j

/-- Power sum of the multiset `A_s` of `s`-sums: `Σ_{σ ∈ A_s} σ^j`. -/
noncomputable def ksumPsum (A : Finset ℂ) (s j : ℕ) : ℂ :=
  ((sumMultiset A s).map (· ^ j)).sum

/-- `(i1,i2)`-th Hasse derivative of `P = Σ_{k1 ≤ r1, k2 ≤ r2} c k1 k2 X^k1 Y^k2` at `(x,y)`:
`Σ c k1 k2 · C(k1,i1) C(k2,i2) · x^(k1-i1) y^(k2-i2)`.  (Terms with `k1 < i1` or `k2 < i2`
vanish because the binomial coefficient is `0`.) -/
noncomputable def hasseEval (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (x y : ℝ) : ℝ :=
  ∑ k1 ∈ Finset.range (r1 + 1), ∑ k2 ∈ Finset.range (r2 + 1),
    (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * x ^ (k1 - i1) * y ^ (k2 - i2)

/-- `c` is a nonzero coefficient array inside the box `[0,r1] × [0,r2]`. -/
def BoxNonzero (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) : Prop :=
  ∃ k1 ≤ r1, ∃ k2 ≤ r2, c k1 k2 ≠ 0

/-- The positive real `r`-th root `(b/a)^{1/r}`. -/
noncomputable def binRoot (r a b : ℕ) : ℝ :=
  ((b : ℝ) / (a : ℝ)) ^ ((1 : ℝ) / (r : ℝ))

end Erdos494
