import Mathlib

/-!
# Erdős #1199 — shared definitions

Lean-oriented encoding of §3 of Huang–Lian–Shao–Xiao–Xu–Zhang, arXiv:2607.17333.

* `βℕ = Ultrafilter ℕ` with Mathlib's ultrafilter addition
  (`A ∈ p + q ↔ {m | {m' | m + m' ∈ A} ∈ q} ∈ p`, `Ultrafilter.eventually_add`).
* The paper's space `(2^ℤ)^{(s,r)}` is re-indexed by `Idx = ℕ × ℤ`: the coordinate `(k, R)`
  stands for the affine sampling `n ↦ c((k+1)·n + R)`; the shift is
  `(T x)(k, R) = x(k, R + (k+1))`.  A point is `Pt = Idx → Bool` (product topology,
  compact, zero-dimensional).
* `act p x` is `p-lim_n Tⁿ x`, written out coordinatewise (no topology needed).
* `cmpl` is the colour complementation `J`, `dil` is the paper's `Δ₂`
  (`(dil x)(k, R) = x(2k+1, R)`, i.e. stride `2(k+1)`), `dbl p` is `D p`.
-/

namespace Erdos1199

open Filter

/-- Mathlib only provides the additive semigroup structure on `Ultrafilter M` as a local
instance (in `Mathlib/Combinatorics/Hindman.lean`); we make it a global instance for `βℕ`. -/
noncomputable instance instAddSemigroupUltrafilterNat : AddSemigroup (Ultrafilter ℕ) :=
  Ultrafilter.addSemigroup

/-- A nonprincipal ultrafilter on `ℕ` (an element of `ℕ* = βℕ \ ℕ`). -/
def Nonprincipal (p : Ultrafilter ℕ) : Prop := (p : Filter ℕ) ≤ Filter.cofinite

/-- `D p`: the image of `p` under `n ↦ 2n`, so `A ∈ dbl p ↔ {n | 2n ∈ A} ∈ p`. -/
noncomputable def dbl (p : Ultrafilter ℕ) : Ultrafilter ℕ := p.map (fun n => 2 * n)

/-- Coordinates: `(k, R)` encodes the affine map `n ↦ (k+1) n + R`. -/
abbrev Idx : Type := ℕ × ℤ

/-- Points of the symbolic space `2^Idx`. -/
abbrev Pt : Type := Idx → Bool

/-- The stride `k + 1` of the coordinate `(k, R)`. -/
def stride (i : Idx) : ℤ := (i.1 : ℤ) + 1

open Classical in
/-- The `βℕ`-action `p · x = p-lim_n Tⁿ x`, where `(Tⁿ x)(k, R) = x(k, R + (k+1) n)`. -/
noncomputable def act (p : Ultrafilter ℕ) (x : Pt) : Pt :=
  fun i => decide ({n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ p)

/-- Colour complementation `J` (a fixed-point-free involution commuting with the action). -/
def cmpl (x : Pt) : Pt := fun i => !(x i)

/-- The dilation `Δ₂`: `(Δ₂ x)(k, R) = x(2k+1, R)` (stride `k+1 ↦ 2(k+1)`). -/
def dil (x : Pt) : Pt := fun i => x (2 * i.1 + 1, i.2)

/-- The encoded point `𝐜` of a colouring `c : ℤ → Bool`: `𝐜(k, R) = c(R)`, so that
`(Tⁿ 𝐜)(k, R) = c((k+1) n + R)`. -/
def encode (c : ℤ → Bool) : Pt := fun i => c i.2

/-- `c(z) = b(2z)` for `z ≥ 0` (and `b 0` for `z < 0`, an arbitrary choice). -/
def ext2 (b : ℕ → Bool) : ℤ → Bool := fun z => b (2 * z.toNat)

/-- `B + B` (including the doubles `2x`) is monochromatic for the colouring `col`. -/
def IsMonoSumset (col : ℕ → Bool) (B : Set ℕ) : Prop :=
  ∃ γ : Bool, ∀ x ∈ B, ∀ y ∈ B, col (x + y) = γ

/-- The Owings property for `b`: an infinite set of positive integers `B` with `B + B`
monochromatic. -/
def Owings (b : ℕ → Bool) : Prop :=
  ∃ B : Set ℕ, B.Infinite ∧ (∀ x ∈ B, 0 < x) ∧ IsMonoSumset b B

/-- `ω(x) = {p · x : p ∈ ℕ*}` (the omega-limit set, via Lemma 2.8 of the paper). -/
def Omega (x : Pt) : Set Pt := {y | ∃ p : Ultrafilter ℕ, Nonprincipal p ∧ act p x = y}

/-- `M` is a minimal subsystem of `ω(x)`, in the form used in the proof:
nonempty, closed, contained in `ω(x)`, invariant under the `βℕ`-action, and every point of `M`
reaches every other point of `M` under the action. -/
def IsMinimalSub (x : Pt) (M : Set Pt) : Prop :=
  M.Nonempty ∧ IsClosed M ∧ M ⊆ Omega x ∧
    (∀ p : Ultrafilter ℕ, ∀ y ∈ M, act p y ∈ M) ∧
    (∀ y ∈ M, ∀ z ∈ M, ∃ q : Ultrafilter ℕ, act q y = z)

end Erdos1199
