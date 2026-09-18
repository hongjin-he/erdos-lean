import ErdosLean.Erdos956.Statement

/-!
# Erdős #956 — shared definitions for the lower-bound construction

Lean-oriented encoding of the parabolic-grid construction (Valtr's mechanism, in the form of the
note <https://www.ulam.ai/research/erdos956.pdf>, §§2–4; see `Statement.lean` for references).

Parameters (with the fixed absolute constant `α = 1/10` and an integer `k ≥ 2`):

* `W = α/k`, `a = α/k²`, `b = α²/(2k⁴) = a²/2`, `η = α⁴/k⁴ = W⁴`;
* `r(t) = √(1+t²)`, `γ(t) = (t, 1 + η - t²/2)`, `ν(t) = (t, 1)/r(t)`, `p(t) = γ(t) - ν(t)`;
* the generators `±p(i a)`, `1 ≤ i ≤ k`, their convex hull `D`, and `C = D/2`;
* the grids `L = {(r a, s b)}`, `U = {(r a, 1 + η + s b)}`, `0 ≤ r ≤ k`, `0 ≤ s ≤ k²`.

Only the finitely many directions `t = i a` (`1 ≤ i ≤ k`) are used, so `D` is a polygon
(compactness is then free).
-/

namespace Erdos956

open Finset Pointwise

noncomputable section

/-- The point `(x, y)` of the Euclidean plane. -/
def pt (x y : ℝ) : E := !₂[x, y]

@[simp] lemma pt_zero (x y : ℝ) : pt x y 0 = x := rfl
@[simp] lemma pt_one (x y : ℝ) : pt x y 1 = y := rfl

/-- The fixed small absolute constant `α`. -/
def α : ℝ := 1 / 10

/-- `W = α / k`. -/
def W (k : ℕ) : ℝ := α / k
/-- Horizontal grid step `a = α / k²`. -/
def a (k : ℕ) : ℝ := α / (k : ℝ) ^ 2
/-- Vertical grid step `b = α² / (2 k⁴) = a² / 2`. -/
def b (k : ℕ) : ℝ := α ^ 2 / (2 * (k : ℝ) ^ 4)
/-- Vertical shift `η = α⁴ / k⁴ = W⁴`. -/
def η (k : ℕ) : ℝ := α ^ 4 / (k : ℝ) ^ 4

/-- `r(t) = √(1 + t²)`. -/
def rr (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2)

/-- The parabola `γ(t) = (t, 1 + η - t²/2)`. -/
def γ (e t : ℝ) : E := pt t (1 + e - t ^ 2 / 2)

/-- The upward unit normal `ν(t) = (t, 1)/√(1+t²)` of the parabola. -/
def ν (t : ℝ) : E := pt (t / rr t) (1 / rr t)

/-- `p(t) = γ(t) - ν(t)`, written in coordinates. -/
def pp (e t : ℝ) : E := pt (t - t / rr t) (1 + e - t ^ 2 / 2 - 1 / rr t)

@[simp] lemma γ_zero (e t : ℝ) : γ e t 0 = t := rfl
@[simp] lemma γ_one (e t : ℝ) : γ e t 1 = 1 + e - t ^ 2 / 2 := rfl
@[simp] lemma ν_zero (t : ℝ) : ν t 0 = t / rr t := rfl
@[simp] lemma ν_one (t : ℝ) : ν t 1 = 1 / rr t := rfl
@[simp] lemma pp_zero (e t : ℝ) : pp e t 0 = t - t / rr t := rfl
@[simp] lemma pp_one (e t : ℝ) : pp e t 1 = 1 + e - t ^ 2 / 2 - 1 / rr t := rfl

/-- The generators `{p(i a) : 1 ≤ i ≤ k} ∪ {-p(i a) : 1 ≤ i ≤ k}` of the body `D`. -/
def gens (k : ℕ) : Finset E :=
  (Icc 1 k).image (fun i : ℕ => pp (η k) (i * a k)) ∪
    (Icc 1 k).image (fun i : ℕ => -pp (η k) (i * a k))

/-- The centrally symmetric convex polygon `D = conv(gens)`. -/
def D (k : ℕ) : Set E := convexHull ℝ (gens k : Set E)

/-- The convex body `C = D / 2`, so that `C - C = D`. -/
def C (k : ℕ) : Set E := (1 / 2 : ℝ) • D k

/-- Lower grid point `(r a, s b)`. -/
def lowPt (k r s : ℕ) : E := pt (r * a k) (s * b k)
/-- Upper grid point `(r a, 1 + η + s b)`. -/
def upPt (k r s : ℕ) : E := pt (r * a k) (1 + η k + s * b k)

/-- The index box `{0,…,k} × {0,…,k²}`. -/
def idx (k : ℕ) : Finset (ℕ × ℕ) := range (k + 1) ×ˢ range (k ^ 2 + 1)

/-- The lower grid `L`. -/
def lowGrid (k : ℕ) : Finset E := (idx k).image fun q => lowPt k q.1 q.2
/-- The upper grid `U`. -/
def upGrid (k : ℕ) : Finset E := (idx k).image fun q => upPt k q.1 q.2

/-- The point set `X_k = L ∪ U`. -/
def X (k : ℕ) : Finset E := lowGrid k ∪ upGrid k

/-- `n_k = |X_k| = 2 (k+1) (k²+1)`. -/
def nk (k : ℕ) : ℕ := 2 * (k + 1) * (k ^ 2 + 1)

/-- The index set of the counted unit pairs: `(i, r, s)` with `1 ≤ i ≤ k`, `r ≤ k - i`,
`i² ≤ s ≤ k²`. -/
def triples (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc 1 k ×ˢ (range (k + 1) ×ˢ range (k ^ 2 + 1))).filter
    fun q => q.2.1 + q.1 ≤ k ∧ q.1 ^ 2 ≤ q.2.2

/-- `M_k = ∑_{i=1}^k (k+1-i)(k²+1-i²)`, the number of counted unit pairs. -/
def Mk (k : ℕ) : ℕ := ∑ i ∈ Icc 1 k, (k + 1 - i) * (k ^ 2 + 1 - i ^ 2)

/-- The unordered pair attached to a triple `(i, r, s)`: `{(r a, s b), ((r+i) a, 1+η+(s-i²) b)}`;
their difference is exactly `γ(i a)`. -/
def pairOf (k : ℕ) (q : ℕ × ℕ × ℕ) : Sym2 E :=
  s(lowPt k q.2.1 q.2.2, upPt k (q.2.1 + q.1) (q.2.2 - q.1 ^ 2))

end

end Erdos956
