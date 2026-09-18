import ErdosLean.Erdos612.Defs
import ErdosLean.Erdos612All.Statement

/-!
# Erdős 612, all `r`: the two parametric layer families

We reuse `Erdos612.Layers`, `blowup`, `AllWin`, `SomeWin`, `PosQ`, `DegQ`, `TightQ`, `CliqQ`
and `fam` from `ErdosLean/Erdos612/Defs.lean`, and the engine `Erdos612.not_diamBound_of_fam` from
`ErdosLean/Erdos612/Main.lean`.  Here we only define the **parametric** layer sequences.

## Part (i): `r = s + 1`, `s ≥ 1` (Czabarka–Singgih–Székely 2021, §3, block `C_{s,δ}`)
Choose `δ = 2s·w` with `w = 2(s+1)(3s+5)`, so `2s ∣ δ` (the paper's case `d = 0`: all big
weights equal `δ/2s = w`) and `(r-1)(3r+2) = s(3s+5) ∣ δ`.  The block has `6s + 1` layers
`m = 0, …, 6s`:
* `m ≡ 0 (mod 3)`: one clump of weight `1`;
* `m = 3i + 1`: `2s - i` clumps of weight `w`;
* `m = 3i + 2`: `i + 1` clumps of weight `w`.
(This is exactly CSS's block — their layers `L_{6s-m}` for `m > 3s` are the mirror of the left
half, and the mirror of `3i+2` is `3(2s-1-i)+1` with `i+1 = 2s-(2s-1-i)` clumps.)
We take the plain juxtaposition `fam [] evPer [] p` **without** CSS's `±1` weight adjustment;
this costs one unit of weight per block, which is paid for by choosing `δ` larger than CSS's
threshold: the growth condition becomes `2s(3s+5)(2s+1) < δ` (here `δ = 2s(3s+5)(2s+2)`).

## Part (ii): `r = q + 4`, `q ≥ 0` (Chen–Chen 2026, §2, `J_{p,r}`)
`τ = 2r-1 = 2q+7`, `d = 3r-1 = 3q+11`, `δ = 6(6r-5)(2r-1)(3r-1)` (CC's threshold, divisible by
`τ`, `d` and `3`), `x = δ/τ`, `u = x/3 = d·2(6r-5)`.  One period has `6r-5 = 6q+19` layers
`m = 0, …, 6q+18`:
* `m < 6q+16`, `m = 3j`: one clump of weight `1` (CC: `L_{3i}`, `i = j+1`);
* `m < 6q+16`, `m = 3j+1`: `2q+6-j = τ-i` clumps of weight `x` (CC: `b_i = (τ-i)x`);
* `m < 6q+16`, `m = 3j+2`: `j+2 = i+1` clumps of weight `x` (CC: `c_i = (i+1)x`);
* `m = 6q+16` and `m = 6q+18`: three clumps of weight `u` (CC (E) with `a₁ = a₃ = x`);
* `m = 6q+17`: `2q+1` clumps of weight `3u` and `4` clumps of weight `4u`
  (`2r-3` clumps, total `(6q+19)u = δ - 2u`).
**Deviation from CC** (documented): CC's layer (F) has total `η = δ - λ - τ` split into
`⌈η/z⌉` balanced clumps; we use total `δ - 2u` with the explicit split above.  All degree,
clique and growth inequalities are re-verified (numerically for `q ≤ 14` during development,
and symbolically, for all `q`, in `Parts/Odd*.lean`).  Prefix `[[δ],[δ]]`, suffix `[[1],[δ],[δ]]`
(CC's end layers `L₁, L₂` / `L_{p(6r-5)+3..5}`, with `L₁` shrunk to one clump).
-/

namespace Erdos612All

open Erdos612

/-! ### Part (i) -/

/-- The big clump weight `w = δ/(2s) = 2(s+1)(3s+5)`. -/
def evW (s : ℕ) : ℕ := 2 * (s + 1) * (3 * s + 5)

/-- The minimum degree `δ = 2s·w = 4s(s+1)(3s+5)` used for `r = s + 1`. -/
def evDelta (s : ℕ) : ℕ := 2 * s * evW s

/-- Layer `m` (`0 ≤ m ≤ 6s`) of the CSS block. -/
def evBlock (s m : ℕ) : List ℕ :=
  if m % 3 = 0 then [1]
  else if m % 3 = 1 then List.replicate (2 * s - m / 3) (evW s)
  else List.replicate (m / 3 + 1) (evW s)

/-- The CSS block `C_{s,δ}` (`6s + 1` layers). -/
def evPer (s : ℕ) : Layers := (List.range (6 * s + 1)).map (evBlock s)

/-! ### Part (ii) -/

/-- `u = (3r-1)·2(6r-5)` for `r = q + 4` (weight of the clumps of the (E) layers). -/
def odU (q : ℕ) : ℕ := (3 * q + 11) * (2 * (6 * q + 19))

/-- `x = δ/τ = 3u`. -/
def odX (q : ℕ) : ℕ := 3 * odU q

/-- `δ = τ·x = 6(6r-5)(2r-1)(3r-1)` for `r = q + 4`. -/
def odDelta (q : ℕ) : ℕ := (2 * q + 7) * odX q

/-- The (E) layers: three clumps of weight `u`. -/
def odE (q : ℕ) : List ℕ := List.replicate 3 (odU q)

/-- The (F) layer: `2q+1` clumps of weight `3u` and four clumps of weight `4u`. -/
def odF (q : ℕ) : List ℕ := List.replicate (2 * q + 1) (3 * odU q) ++ List.replicate 4 (4 * odU q)

/-- Layer `m` (`0 ≤ m ≤ 6q+18`) of the CC period. -/
def odBlock (q m : ℕ) : List ℕ :=
  if m < 6 * q + 16 then
    (if m % 3 = 0 then [1]
     else if m % 3 = 1 then List.replicate (2 * q + 6 - m / 3) (odX q)
     else List.replicate (m / 3 + 2) (odX q))
  else if m = 6 * q + 16 then odE q
  else if m = 6 * q + 17 then odF q
  else odE q

/-- The CC period (`6r - 5 = 6q + 19` layers). -/
def odPer (q : ℕ) : Layers := (List.range (6 * q + 19)).map (odBlock q)

/-- Left end: two layers with one clump of weight `δ`. -/
def odPre (q : ℕ) : Layers := [[odDelta q], [odDelta q]]

/-- Right end: the junction `[1]`, then two layers with one clump of weight `δ`. -/
def odSuf (q : ℕ) : Layers := [[1], [odDelta q], [odDelta q]]

end Erdos612All
