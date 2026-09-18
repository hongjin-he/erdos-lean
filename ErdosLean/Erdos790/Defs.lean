import ErdosLean.Erdos790.Statement

/-!
# Erdős 790: shared definitions for Korsky's construction

All objects are integer/natural-number valued; no probability is used.  The random choice of
dyadic intervals in the paper is replaced by an averaging argument over colourings
`χ : Fin (topIdx A + 1) → Fin m` (see `Parts/Averaging.lean`).
-/

namespace Erdos790

/-- The `s`-th smallest element of `A` (`0` if `s ≥ |A|`). -/
noncomputable def elem (A : Finset ℤ) (s : ℕ) : ℤ :=
  if h : s < A.card then A.orderEmbOfFin rfl ⟨s, h⟩ else 0

/-- The rank of `a` in `A`: the number of elements of `A` below `a`. -/
def rank (A : Finset ℤ) (a : ℤ) : ℕ := (A.filter (· < a)).card

/-- The split point of the level-`h` block of the dyadic tree on indices containing `i`:
the block is `[q 2^{h+1}, (q+1) 2^{h+1})` with `q = i / 2^{h+1}`, split at `q 2^{h+1} + 2^h`. -/
def splitPt (h i : ℕ) : ℕ := i / 2 ^ (h + 1) * 2 ^ (h + 1) + 2 ^ h

/-- Korsky's Lemma 2 distance list `D(a)` (repeated halving of the sorted set, via binary
expansion of ranks): distances from `a` to the split points of all blocks containing it. -/
noncomputable def Dset (A : Finset ℤ) (a : ℤ) : Finset ℤ :=
  ((Finset.range (Nat.clog 2 A.card)).filter (fun h => splitPt h (rank A a) < A.card)).image
    (fun h => |elem A (splitPt h (rank A a)) - a|)

/-- `D(a) ∪ {a}`. -/
noncomputable def Dplus (A : Finset ℤ) (a : ℤ) : Finset ℤ := insert a (Dset A a)

/-- Dyadic index: `a ∈ [2^j, 2^{j+1})` for `j = dyIdx a` (when `a > 0`). -/
def dyIdx (a : ℤ) : ℕ := Nat.log 2 a.toNat

/-- The largest dyadic index occurring in `A`. -/
def topIdx (A : Finset ℤ) : ℕ := A.sup dyIdx

/-- Dyadic indices `j ≤ M` whose interval `[2^j, 2^{j+1})` can meet `[δ/(2N), 2δ]`. -/
def window (N : ℕ) (δ : ℤ) (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter
    (fun j => δ ≤ 2 * (N : ℤ) * 2 ^ (j + 1) ∧ (2 : ℤ) ^ j ≤ 2 * δ)

/-- The forbidden index set `F(a)`. -/
noncomputable def Fset (A : Finset ℤ) (a : ℤ) : Finset ℕ :=
  ((Dplus A a).biUnion (fun δ => window A.card δ (topIdx A))).erase (dyIdx a)

/-- The bound `K(N) = (⌈log₂ N⌉ + 1)(⌈log₂ N⌉ + 5)` on `|F(a)|`. -/
def K (N : ℕ) : ℕ := (Nat.clog 2 N + 1) * (Nat.clog 2 N + 5)

/-- Dyadic indices viewed in the finite index type `Fin (topIdx A + 1)`. -/
def idx (A : Finset ℤ) (j : ℕ) : Fin (topIdx A + 1) := Fin.ofNat (topIdx A + 1) j

end Erdos790
