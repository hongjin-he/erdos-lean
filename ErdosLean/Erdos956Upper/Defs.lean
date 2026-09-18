import ErdosLean.Erdos956.Statement

/-!
# Erdős #956, upper bound — shared definitions

Lean-oriented encoding of the Erdős–Pach upper bound `h(n) = O(n^{4/3})`.

Pipeline.
* `D = C - C` (`diffSet`), a compact convex centrally symmetric set containing `0`.
  For `x ≠ y` in an admissible `X`, `δ(C+x, C+y) = infDist (y - x) D` and `y - x ∉ D`
  (`SepConfig`).
* `K = {v | infDist v D ≤ 1}` (`Kset`), `w = max {v₀ : v ∈ K}` (`wid`), and the upper boundary
  function `g(t) = max {s : (t, s) ∈ K}` (`gUp`), concave on `(-w, w)`.
* every unit vector `v` (`infDist v D = 1`) satisfies `OnUpper v`, `OnUpper (-v)`, `OnSide v`
  or `OnSide (-v)`; side pairs are `O(n)`, upper pairs are counted by a crossing-lemma argument.
* the *upper drawing*: vertices `X`; for each centre `c ∈ X` the points of `X` on the curve
  `x ↦ c₁ + g(x - c₀)` (`curve`), joined consecutively by x-monotone arcs (`upperArc`).
* abstract x-monotone drawings: `Arc`, `Arc.Valid`, `Arc.Crosses`, `Arc.Avoids`, and the
  crossing-pair counts `crossAdj` / `crossDisj`.
-/

namespace Erdos956Upper

open Erdos956 Metric

noncomputable section

/-- The point `(x, y)` of the Euclidean plane. -/
def pt2 (x y : ℝ) : E := !₂[x, y]

@[simp] lemma pt2_zero (x y : ℝ) : pt2 x y 0 = x := rfl
@[simp] lemma pt2_one (x y : ℝ) : pt2 x y 1 = y := rfl

/-- The difference body `C - C`. -/
def diffSet (C : Set E) : Set E := {v | ∃ a ∈ C, ∃ b ∈ C, v = a - b}

/-- A *separated configuration*: `D` is a compact convex centrally symmetric set containing `0`,
and the differences of distinct points of `X` avoid `D`. -/
structure SepConfig (D : Set E) (X : Finset E) : Prop where
  compact : IsCompact D
  convex : Convex ℝ D
  zero_mem : (0 : E) ∈ D
  neg_mem : ∀ v ∈ D, -v ∈ D
  sep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → y - x ∉ D

/-- The unit ball `K = {v | infDist v D ≤ 1}` of the relevant distance. -/
def Kset (D : Set E) : Set E := {v | infDist v D ≤ 1}

/-- Half-width `w = sup {v₀ : v ∈ K}`. -/
def wid (D : Set E) : ℝ := sSup ((fun v : E => v 0) '' Kset D)

/-- Upper boundary function `g(t) = sup {s : (t, s) ∈ K}`. -/
def gUp (D : Set E) (t : ℝ) : ℝ := sSup {s : ℝ | pt2 t s ∈ Kset D}

/-- `v` lies on the open upper arc `{(t, g t) : |t| < w}` of `∂K`. -/
def OnUpper (D : Set E) (v : E) : Prop := |v 0| < wid D ∧ v 1 = gUp D (v 0)

/-- `v` lies on the right vertical side of `∂K`. -/
def OnSide (D : Set E) (v : E) : Prop := v 0 = wid D ∧ infDist v D = 1

/-- Ordered pairs `(x, y)` of distinct points of `X` with `y - x` on the upper arc. -/
def upperPairs (D : Set E) (X : Finset E) : Finset (E × E) := by
  classical
  exact (X ×ˢ X).filter fun q => q.1 ≠ q.2 ∧ OnUpper D (q.2 - q.1)

/-- Ordered pairs `(x, y)` of distinct points of `X` with `y - x` on the right side. -/
def sidePairs (D : Set E) (X : Finset E) : Finset (E × E) := by
  classical
  exact (X ×ˢ X).filter fun q => q.1 ≠ q.2 ∧ OnSide D (q.2 - q.1)

/-! ### Abstract x-monotone drawings -/

/-- An x-monotone arc: the graph of `f` over `[l, r]`. -/
structure Arc where
  l : ℝ
  r : ℝ
  f : ℝ → ℝ

namespace Arc

/-- Well-formedness: `l < r` and `f` continuous on `[l, r]`. -/
def Valid (a : Arc) : Prop := a.l < a.r ∧ ContinuousOn a.f (Set.Icc a.l a.r)

/-- Left endpoint `(l, f l)`. -/
def left (a : Arc) : E := pt2 a.l (a.f a.l)

/-- Right endpoint `(r, f r)`. -/
def right (a : Arc) : E := pt2 a.r (a.f a.r)

/-- Two arcs cross if they share a point interior to both. -/
def Crosses (a b : Arc) : Prop :=
  ∃ x, x ∈ Set.Ioo a.l a.r ∧ x ∈ Set.Ioo b.l b.r ∧ a.f x = b.f x

/-- The point `z` is not an interior point of the arc. -/
def Avoids (a : Arc) (z : E) : Prop := ¬ (z 0 ∈ Set.Ioo a.l a.r ∧ z 1 = a.f (z 0))

/-- The arcs share an endpoint. -/
def ShareEnd (a b : Arc) : Prop :=
  a.left = b.left ∨ a.left = b.right ∨ a.right = b.left ∨ a.right = b.right

end Arc

/-- Ordered crossing pairs of distinct edges. -/
def crossAll {ι : Type*} (A : Finset ι) (arc : ι → Arc) : Finset (ι × ι) := by
  classical
  exact (A ×ˢ A).filter fun q => q.1 ≠ q.2 ∧ (arc q.1).Crosses (arc q.2)

/-- Ordered crossing pairs of edges sharing an endpoint. -/
def crossAdj {ι : Type*} (A : Finset ι) (arc : ι → Arc) : Finset (ι × ι) := by
  classical
  exact (crossAll A arc).filter fun q => (arc q.1).ShareEnd (arc q.2)

/-- Ordered crossing pairs of edges with four distinct endpoints. -/
def crossDisj {ι : Type*} (A : Finset ι) (arc : ι → Arc) : Finset (ι × ι) := by
  classical
  exact (crossAll A arc).filter fun q => ¬ (arc q.1).ShareEnd (arc q.2)

/-! ### The upper drawing -/

/-- The translated upper arc with centre `c`: `x ↦ c₁ + g(x - c₀)`. -/
def curve (D : Set E) (c : E) (x : ℝ) : ℝ := c 1 + gUp D (x - c 0)

/-- `p, q` are consecutive points of `X` (from left to right) on the curve of centre `c`. -/
def Consec (D : Set E) (X : Finset E) (c p q : E) : Prop :=
  OnUpper D (p - c) ∧ OnUpper D (q - c) ∧ p 0 < q 0 ∧
    ∀ z ∈ X, OnUpper D (z - c) → ¬ (p 0 < z 0 ∧ z 0 < q 0)

/-- Edges of the upper drawing, indexed by `(c, p, q)`. -/
def upperEdges (D : Set E) (X : Finset E) : Finset (E × E × E) := by
  classical
  exact (X ×ˢ X ×ˢ X).filter fun e => Consec D X e.1 e.2.1 e.2.2

/-- The arc of the edge `(c, p, q)`: the curve of centre `c` over `[p₀, q₀]`. -/
def upperArc (D : Set E) (e : E × E × E) : Arc := ⟨e.2.1 0, e.2.2 0, curve D e.1⟩

end

end Erdos956Upper
