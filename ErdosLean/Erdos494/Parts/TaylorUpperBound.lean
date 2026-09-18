import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part D8: Taylor upper bound near `(θ, θ)`.

Exact Taylor expansion of the polynomial `D^{(i1,i2)} P` at `(θ,θ)`:
`D^{(i)}P(x,y) = Σ_{j} C(i1+j1,i1) C(i2+j2,i2) D^{(i+j)}P(θ,θ) (x-θ)^{j1} (y-θ)^{j2}`.
Terms with `(i+j)` of weight `< t` vanish by hypothesis, the others have `j1/r1 + j2/r2 ≥ t - Θ0`
and are bounded by `4^{r1+r2} (r1+1)(r2+1) H (|θ|+1)^{r1+r2} Λ^{t - Θ0}`
(using `|x-θ|^{j1} |y-θ|^{j2} ≤ Λ^{j1/r1 + j2/r2}` and `Λ ≤ 1`). -/

namespace Erdos494

open Finset

/-- Univariate Taylor expansion of `C(k,i) (θ+u)^(k-i)` around `θ`. -/
lemma taylor_uni (i k N : ℕ) (hk : k ≤ i + N) (θ u : ℝ) :
    (k.choose i : ℝ) * (θ + u) ^ (k - i) =
      ∑ j ∈ range (N + 1),
        ((i + j).choose i : ℝ) * (k.choose (i + j) : ℝ) * θ ^ (k - (i + j)) * u ^ j := by
  by_cases h : k < i
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [Nat.choose_eq_zero_of_lt (by omega : k < i + j)]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = i + m := ⟨k - i, by omega⟩
    have hm : m ≤ N := by omega
    rw [Nat.add_sub_cancel_left, add_comm θ u, add_pow, Finset.mul_sum]
    have hsub : range (m + 1) ⊆ range (N + 1) := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    rw [← Finset.sum_subset hsub (f := fun j =>
      ((i + j).choose i : ℝ) * ((i + m).choose (i + j) : ℝ) * θ ^ (i + m - (i + j)) * u ^ j) ?_]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      have hc : (i + m).choose (i + j) * (i + j).choose i
          = (i + m).choose i * m.choose j := by
        rw [Nat.choose_mul (by omega)]
        congr 2 <;> omega
      have hc' : ((i + m).choose (i + j) : ℝ) * ((i + j).choose i : ℝ)
          = ((i + m).choose i : ℝ) * (m.choose j : ℝ) := by exact_mod_cast hc
      rw [Nat.add_sub_add_left]
      linear_combination (-(u ^ j * θ ^ (m - j))) * hc'
    · intro j _ hj'
      simp only [Finset.mem_range] at hj'
      rw [Nat.choose_eq_zero_of_lt (by omega : i + m < i + j)]
      simp

/-- Hasse derivatives of order beyond the degree vanish. -/
lemma hasseEval_eq_zero_left (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (m1 m2 : ℕ) (h : r1 < m1) (x y : ℝ) :
    hasseEval r1 r2 c m1 m2 x y = 0 := by
  unfold hasseEval
  apply Finset.sum_eq_zero
  intro k1 hk1
  apply Finset.sum_eq_zero
  intro k2 _
  simp only [Finset.mem_range] at hk1
  rw [Nat.choose_eq_zero_of_lt (by omega : k1 < m1)]
  simp

lemma hasseEval_eq_zero_right (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (m1 m2 : ℕ) (h : r2 < m2) (x y : ℝ) :
    hasseEval r1 r2 c m1 m2 x y = 0 := by
  unfold hasseEval
  apply Finset.sum_eq_zero
  intro k1 _
  apply Finset.sum_eq_zero
  intro k2 hk2
  simp only [Finset.mem_range] at hk2
  rw [Nat.choose_eq_zero_of_lt (by omega : k2 < m2)]
  simp

/-- Bivariate Taylor expansion. -/
lemma hasseEval_taylor (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (θ u v : ℝ) :
    hasseEval r1 r2 c i1 i2 (θ + u) (θ + v) =
      ∑ j1 ∈ range (r1 - i1 + 1), ∑ j2 ∈ range (r2 - i2 + 1),
        ((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          hasseEval r1 r2 c (i1 + j1) (i2 + j2) θ θ * u ^ j1 * v ^ j2 := by
  have key : ∀ k1 ∈ range (r1 + 1), ∀ k2 ∈ range (r2 + 1),
      (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * (θ + u) ^ (k1 - i1)
        * (θ + v) ^ (k2 - i2) =
      ∑ j1 ∈ range (r1 - i1 + 1), ∑ j2 ∈ range (r2 - i2 + 1),
        ((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          ((c k1 k2 : ℝ) * (k1.choose (i1 + j1) : ℝ) * (k2.choose (i2 + j2) : ℝ) *
            θ ^ (k1 - (i1 + j1)) * θ ^ (k2 - (i2 + j2))) * u ^ j1 * v ^ j2 := by
    intro k1 hk1 k2 hk2
    simp only [Finset.mem_range] at hk1 hk2
    have e1 := taylor_uni i1 k1 (r1 - i1) (by omega) θ u
    have e2 := taylor_uni i2 k2 (r2 - i2) (by omega) θ v
    calc (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * (θ + u) ^ (k1 - i1)
          * (θ + v) ^ (k2 - i2)
        = (c k1 k2 : ℝ) * ((k1.choose i1 : ℝ) * (θ + u) ^ (k1 - i1)) *
            ((k2.choose i2 : ℝ) * (θ + v) ^ (k2 - i2)) := by ring
      _ = _ := by
        rw [e1, e2, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j1 _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j2 _
        ring
  unfold hasseEval
  rw [Finset.sum_congr rfl (fun k1 hk1 => Finset.sum_congr rfl (fun k2 hk2 => key k1 hk1 k2 hk2))]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, k1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, k1, 2, j1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j1]; rw [Finset.sum_comm]

/-- Crude bound for all Hasse derivatives at `(θ, θ)`. -/
lemma hasseEval_abs_le (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (H : ℝ)
    (hH : ∀ k1 k2, |(c k1 k2 : ℝ)| ≤ H) (m1 m2 : ℕ) (θ : ℝ) :
    |hasseEval r1 r2 c m1 m2 θ θ| ≤
      ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) *
        ((|θ| + 1) ^ r1 * (|θ| + 1) ^ r2 * 2 ^ r1 * 2 ^ r2 * H) := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0 0)
  unfold hasseEval
  calc _ ≤ ∑ k1 ∈ range (r1 + 1), ∑ k2 ∈ range (r2 + 1),
        |(c k1 k2 : ℝ) * (k1.choose m1 : ℝ) * (k2.choose m2 : ℝ) * θ ^ (k1 - m1) *
          θ ^ (k2 - m2)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k1 ∈ range (r1 + 1), ∑ k2 ∈ range (r2 + 1),
        ((|θ| + 1) ^ r1 * (|θ| + 1) ^ r2 * 2 ^ r1 * 2 ^ r2 * H) := by
      apply Finset.sum_le_sum
      intro k1 hk1
      apply Finset.sum_le_sum
      intro k2 hk2
      simp only [Finset.mem_range] at hk1 hk2
      have ht1 : |θ| ^ (k1 - m1) ≤ (|θ| + 1) ^ r1 :=
        (pow_le_pow_left₀ (abs_nonneg θ) (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg θ]) (by omega))
      have ht2 : |θ| ^ (k2 - m2) ≤ (|θ| + 1) ^ r2 :=
        (pow_le_pow_left₀ (abs_nonneg θ) (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg θ]) (by omega))
      have hc1 : (k1.choose m1 : ℝ) ≤ 2 ^ r1 := by
        have : k1.choose m1 ≤ 2 ^ r1 :=
          (Nat.choose_le_two_pow k1 m1).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact_mod_cast this
      have hc2 : (k2.choose m2 : ℝ) ≤ 2 ^ r2 := by
        have : k2.choose m2 ≤ 2 ^ r2 :=
          (Nat.choose_le_two_pow k2 m2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact_mod_cast this
      calc _ = |θ| ^ (k1 - m1) * |θ| ^ (k2 - m2) * (k1.choose m1 : ℝ) * (k2.choose m2 : ℝ) *
            |(c k1 k2 : ℝ)| := by
            simp only [abs_mul, abs_pow, Nat.abs_cast]; ring
        _ ≤ _ := by gcongr; exact hH k1 k2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

theorem taylor_upper_bound (r1 r2 : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2) (c : ℕ → ℕ → ℤ) (H : ℝ)
    (hH : ∀ k1 k2, |(c k1 k2 : ℝ)| ≤ H) (θ t Θ0 Λ : ℝ)
    (hvan : ∀ i1 i2 : ℕ, (i1 : ℝ) / r1 + (i2 : ℝ) / r2 < t → hasseEval r1 r2 c i1 i2 θ θ = 0)
    (i1 i2 : ℕ) (hi : (i1 : ℝ) / r1 + (i2 : ℝ) / r2 ≤ Θ0) (hΘ : Θ0 ≤ t)
    (hΛ0 : 0 < Λ) (hΛ1 : Λ ≤ 1) (x y : ℝ)
    (hx : |x - θ| ≤ Λ ^ ((1 : ℝ) / r1)) (hy : |y - θ| ≤ Λ ^ ((1 : ℝ) / r2)) :
    |hasseEval r1 r2 c i1 i2 x y| ≤
      ((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * 8 ^ (r1 + r2) * H * (|θ| + 1) ^ (r1 + r2) *
        Λ ^ (t - Θ0) := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0 0)
  obtain ⟨Bh, hBh0, hBhe, hBh⟩ : ∃ Bh : ℝ, 0 ≤ Bh ∧
      Bh = ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) *
        ((|θ| + 1) ^ r1 * (|θ| + 1) ^ r2 * 2 ^ r1 * 2 ^ r2 * H) ∧
      ∀ m1 m2 : ℕ, |hasseEval r1 r2 c m1 m2 θ θ| ≤ Bh :=
    ⟨_, by positivity, rfl, fun m1 m2 => hasseEval_abs_le r1 r2 c H hH m1 m2 θ⟩
  have hL0 : 0 ≤ Λ ^ (t - Θ0) := Real.rpow_nonneg hΛ0.le _
  have hr1' : (0 : ℝ) < r1 := by exact_mod_cast hr1
  have hr2' : (0 : ℝ) < r2 := by exact_mod_cast hr2
  have hxe : x = θ + (x - θ) := by ring
  have hye : y = θ + (y - θ) := by ring
  rw [hxe, hye, hasseEval_taylor]
  set u := x - θ
  set v := y - θ
  set M : ℝ := 2 ^ r1 * 2 ^ r2 * Bh * Λ ^ (t - Θ0) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm : ∀ j1 j2 : ℕ,
      |((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          hasseEval r1 r2 c (i1 + j1) (i2 + j2) θ θ * u ^ j1 * v ^ j2| ≤ M := by
    intro j1 j2
    by_cases hw : (((i1 + j1 : ℕ) : ℝ) / r1 + ((i2 + j2 : ℕ) : ℝ) / r2 < t)
    · rw [hvan _ _ hw]; simpa using hM0
    by_cases h1 : r1 < i1 + j1
    · rw [hasseEval_eq_zero_left _ _ _ _ _ h1]; simpa using hM0
    by_cases h2 : r2 < i2 + j2
    · rw [hasseEval_eq_zero_right _ _ _ _ _ h2]; simpa using hM0
    have hc1 : ((i1 + j1).choose i1 : ℝ) ≤ 2 ^ r1 := by
      have : (i1 + j1).choose i1 ≤ 2 ^ r1 :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have hc2 : ((i2 + j2).choose i2 : ℝ) ≤ 2 ^ r2 := by
      have : (i2 + j2).choose i2 ≤ 2 ^ r2 :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have hexp : t - Θ0 ≤ (j1 : ℝ) / r1 + (j2 : ℝ) / r2 := by
      push_cast [add_div] at hw
      linarith
    have hpow : ∀ (r j : ℕ) (w : ℝ), |w| ≤ Λ ^ ((1 : ℝ) / r) →
        |w| ^ j ≤ Λ ^ ((j : ℝ) / r) := by
      intro r j w hw
      calc |w| ^ j ≤ (Λ ^ ((1 : ℝ) / r)) ^ j := pow_le_pow_left₀ (abs_nonneg w) hw j
        _ = Λ ^ ((j : ℝ) / r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]
          congr 1
          ring
    have huv : |u| ^ j1 * |v| ^ j2 ≤ Λ ^ (t - Θ0) := by
      calc |u| ^ j1 * |v| ^ j2 ≤ Λ ^ ((j1 : ℝ) / r1) * Λ ^ ((j2 : ℝ) / r2) :=
            mul_le_mul (hpow r1 j1 u hx) (hpow r2 j2 v hy) (by positivity)
              (Real.rpow_nonneg hΛ0.le _)
        _ = Λ ^ ((j1 : ℝ) / r1 + (j2 : ℝ) / r2) := (Real.rpow_add hΛ0 _ _).symm
        _ ≤ Λ ^ (t - Θ0) := Real.rpow_le_rpow_of_exponent_ge hΛ0 hΛ1 hexp
    calc _ = ((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          |hasseEval r1 r2 c (i1 + j1) (i2 + j2) θ θ| * (|u| ^ j1 * |v| ^ j2) := by
          simp only [abs_mul, abs_pow, Nat.abs_cast]; ring
      _ ≤ M := by
        rw [hM]
        gcongr
        exact hBh _ _
  calc _ ≤ ∑ j1 ∈ range (r1 - i1 + 1), ∑ j2 ∈ range (r2 - i2 + 1), M :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j1 _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j2 _ => hterm j1 j2))
    _ = ((r1 - i1 + 1 : ℕ) : ℝ) * ((r2 - i2 + 1 : ℕ) : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) * M := by
      have e1 : ((r1 - i1 + 1 : ℕ) : ℝ) ≤ (r1 : ℝ) + 1 := by
        have : r1 - i1 + 1 ≤ r1 + 1 := by omega
        exact_mod_cast this
      have e2 : ((r2 - i2 + 1 : ℕ) : ℝ) ≤ (r2 : ℝ) + 1 := by
        have : r2 - i2 + 1 ≤ r2 + 1 := by omega
        exact_mod_cast this
      gcongr
    _ = ((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ r1 * 2 ^ r1 * (2 ^ r2 * 2 ^ r2)) *
          H * (|θ| + 1) ^ (r1 + r2) * Λ ^ (t - Θ0) := by
      rw [hM, hBhe, pow_add]; ring
    _ ≤ _ := by
      have h8 : (2 : ℝ) ^ r1 * 2 ^ r1 * (2 ^ r2 * 2 ^ r2) ≤ 8 ^ (r1 + r2) := by
        rw [← mul_pow, ← mul_pow, pow_add]
        gcongr <;> norm_num
      gcongr

end Erdos494
