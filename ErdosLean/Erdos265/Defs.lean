import ErdosLean.Erdos265.Statement

/-!
# Erdős #265 — shared definitions

**Barrier half** (`aₙ^{1/2ⁿ} → 1`; the argument is K. Kitamura's, formalised
independently).  Tails `T n = ∑_{k≥n} 1/a_k`, `V n = ∑_{k≥n} 1/(a_k-1)`,
`Dt n = V n - T n = ∑_{k≥n} 1/(a_k(a_k-1))`, the prefix products `P n = ∏_{k<n} a_k`,
`Ps n = ∏_{k<n} (a_k - 1)`, the tail envelope `Henv n = P n / √(Dt n)` (it satisfies
`Henv (n+1) ≤ K·Henv n ²`), and the second residual `Eres n = T n/(1 - T n) - V n`
(positive by strict superadditivity of `x ↦ x/(1-x)`; `1/(a-1) = (1/a)/(1 - 1/a)`).

**Growth half** (Kovač–Tao, arXiv:2406.17593 v4, Theorem 2.8 / Corollary 2.9, §7,
`d = 2`, shifted; parameters modified).  With `f1 x = 1/x`, `f2 x = 1/(x(x-1))` we have
`1/(x-1) = f1 x + f2 x`.  Block `k` places two terms near `N_k` and `2N_k`, where
`N_k = 4^{m_k}`, `M_k = 2^{m_k} = √N_k`, `m_0 = 40`, `m_{k+1} = m_k + ⌊m_k/10⌋ + 1`.
-/

open Filter Topology

namespace Erdos265

/-! ## Barrier half -/

/-- Tail `∑_{k ≥ n} f k` (indexed as `∑' k, f (k + n)`). -/
noncomputable def tail (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k : ℕ, f (k + n)

/-- `1 / a_n`. -/
noncomputable def recip (a : ℕ → ℕ) (n : ℕ) : ℝ := 1 / (a n : ℝ)

/-- `1 / (a_n - 1)`. -/
noncomputable def recipS (a : ℕ → ℕ) (n : ℕ) : ℝ := 1 / ((a n : ℝ) - 1)

/-- `1 / (a_n (a_n - 1)) = 1/(a_n - 1) - 1/a_n`. -/
noncomputable def recipD (a : ℕ → ℕ) (n : ℕ) : ℝ := 1 / ((a n : ℝ) * ((a n : ℝ) - 1))

/-- `T n = ∑_{k≥n} 1/a_k`. -/
noncomputable def T (a : ℕ → ℕ) (n : ℕ) : ℝ := tail (recip a) n

/-- `V n = ∑_{k≥n} 1/(a_k - 1)`. -/
noncomputable def V (a : ℕ → ℕ) (n : ℕ) : ℝ := tail (recipS a) n

/-- `Dt n = ∑_{k≥n} 1/(a_k(a_k - 1))`. -/
noncomputable def Dt (a : ℕ → ℕ) (n : ℕ) : ℝ := tail (recipD a) n

/-- Prefix product `P n = ∏_{k<n} a_k`. -/
def P (a : ℕ → ℕ) (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, a k

/-- Shifted prefix product `Ps n = ∏_{k<n} (a_k - 1)`. -/
def Ps (a : ℕ → ℕ) (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, (a k - 1)

/-- The tail envelope `Henv n = P n / √(Dt n)`. -/
noncomputable def Henv (a : ℕ → ℕ) (n : ℕ) : ℝ := (P a n : ℝ) / Real.sqrt (Dt a n)

/-- The second residual `Eres n = T n / (1 - T n) - V n`. -/
noncomputable def Eres (a : ℕ → ℕ) (n : ℕ) : ℝ := T a n / (1 - T a n) - V a n

/-- Binary logarithmic ratio `log (H n) / 2ⁿ`. -/
noncomputable def logRatio (H : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (H n) / (2 : ℝ) ^ n

/-- The slowly varying regulariser `F n = ⌈log a_n⌉ + 2` in the tail estimate
`T n ≤ F n / a_n` (valid once `a_m ≥ e^m`). -/
noncomputable def regF (a : ℕ → ℕ) (n : ℕ) : ℝ := (Nat.ceil (Real.log (a n : ℝ)) : ℝ) + 2

/-! ## Growth half -/

/-- `f1 x = 1/x`. -/
noncomputable def f1 (x : ℝ) : ℝ := 1 / x

/-- `f2 x = 1/(x(x-1))`. -/
noncomputable def f2 (x : ℝ) : ℝ := 1 / (x * (x - 1))

/-- Exponent sequence: `m 0 = 40`, `m (k+1) = m k + m k / 10 + 1`. -/
def mSeq : ℕ → ℕ
  | 0 => 40
  | k + 1 => mSeq k + mSeq k / 10 + 1

/-- Block scale `N_k = 4^{m_k}`. -/
def NN (k : ℕ) : ℕ := 4 ^ mSeq k

/-- Block half-width `M_k = 2^{m_k}` (so `M_k² = N_k`). -/
def MM (k : ℕ) : ℕ := 2 ^ mSeq k

/-- Box radius in the first coordinate: `M_k / (16 N_k²)`. -/
noncomputable def rad1 (k : ℕ) : ℝ := (MM k : ℝ) / (16 * (NN k : ℝ) ^ 2)

/-- Box radius in the second coordinate: `M_k / (16 N_k³)`. -/
noncomputable def rad2 (k : ℕ) : ℝ := (MM k : ℝ) / (16 * (NN k : ℝ) ^ 3)

/-- Contribution of block `k` with offsets `c = (n₁, n₂)`: the two terms are
`N_k + n₁` and `2N_k + n₂`; coordinates are the `f1`- and `f2`-sums. -/
noncomputable def blockVal (k : ℕ) (c : ℤ × ℤ) : ℝ × ℝ :=
  (f1 ((NN k : ℝ) + c.1) + f1 (2 * (NN k : ℝ) + c.2),
   f2 ((NN k : ℝ) + c.1) + f2 (2 * (NN k : ℝ) + c.2))

/-- Admissible offsets for block `k`: `|n₁|, |n₂| ≤ M_k`. -/
def Adm (k : ℕ) (c : ℤ × ℤ) : Prop := |c.1| ≤ (MM k : ℤ) ∧ |c.2| ≤ (MM k : ℤ)

/-- The centre `s_k` of block `k` (zero offsets). -/
noncomputable def center (k : ℕ) : ℝ × ℝ := blockVal k (0, 0)

/-- The integer sequence encoded by offsets `c`: `a (2k) = N_k + n₁(k)`,
`a (2k+1) = 2 N_k + n₂(k)`. -/
def seqOf (c : ℕ → ℤ × ℤ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then ((NN (n / 2) : ℤ) + (c (n / 2)).1).toNat
  else (2 * (NN (n / 2) : ℤ) + (c (n / 2)).2).toNat

end Erdos265
