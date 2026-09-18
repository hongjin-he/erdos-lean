import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part B3: the GFS lemma (two dominant terms).

Let `T_i = i^{j-1} C(n, s-i)` (`1 ≤ i ≤ s`, `n > s`), so `f = Σ (-1)^{i-1} T_i`.  The ratios
`ρ_i = T_{i+1}/T_i` satisfy `ρ_{i+1} ≤ λ^{j-1} ρ_i` with `λ = s(s-2)/(s-1)^2 < 1`
(log-concavity).  If `T_m` is the largest term then all `T_i` with `|i-m| ≥ 2` are
`≤ λ^{j-1} T_m`, and `T_{m-1} T_{m+1} ≤ λ^{j-1} T_m^2`, so `f = 0` forces one neighbour
`T_{m'}` (`m' = m ± 1`) with `|T_m - T_{m'}| ≤ (s+1) λ^{(j-1)/2} T_m`.  With `i = min(m, m')`,
dividing by `C(n, s-i-1)` gives
`|i^{j-1}(n-s+i+1) - (s-i)(i+1)^{j-1}| ≤ 4 s (s+1) λ^{(j-1)/2} (i+1)^{j-1}`, and replacing
`n-s+i+1` by `n` costs `≤ s i^{j-1}`.  For `j ≥ J0` both errors are `≤ ½ Y^{1-δ}` with
`Y = (s-i)(i+1)^{j-1}` and `δ = ½ min(log(1/λ)/(2 log s), log(s/(s-1))/log s)`.
The second conclusion `n ≤ 2Y` is immediate from the first.

In the formal proof we use `θ = 1 - 1/(2(s-1)^2)` (so `λ ≤ θ²`), `q = 1 + 1/(4s²)` and
`δ = log_s q`, so that `s^δ = q`, `qθ < 1` and `q (s-1)/s < 1`. -/

namespace Erdos494

namespace TwoTermApprox

open Finset

/-- Log-concavity of binomial coefficients. -/
lemma choose_lc (n r : ℕ) : n.choose (r + 2) * n.choose r ≤ n.choose (r + 1) ^ 2 := by
  rcases Nat.lt_or_ge r n with h | h
  · obtain ⟨t, rfl⟩ : ∃ t, n = r + t + 1 := ⟨n - r - 1, by omega⟩
    have h1 := Nat.choose_succ_right_eq (r + t + 1) r
    have h2 := Nat.choose_succ_right_eq (r + t + 1) (r + 1)
    have e1 : r + t + 1 - r = t + 1 := by omega
    have e2 : r + t + 1 - (r + 1) = t := by omega
    rw [e1] at h1
    rw [e2] at h2
    set a := (r + t + 1).choose r
    set b := (r + t + 1).choose (r + 1)
    set c := (r + t + 1).choose (r + 1 + 1)
    have hpos : 0 < (r + 2) * (t + 1) := by positivity
    have key : c * a * ((r + 2) * (t + 1)) ≤ b ^ 2 * ((r + 2) * (t + 1)) := by
      calc c * a * ((r + 2) * (t + 1)) = (c * (r + 1 + 1)) * (a * (t + 1)) := by ring
        _ = (b * t) * (b * (r + 1)) := by rw [h2, h1]
        _ = b ^ 2 * (t * (r + 1)) := by ring
        _ ≤ b ^ 2 * ((r + 2) * (t + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
    exact Nat.le_of_mul_le_mul_right key hpos
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < r + 2)]
    simp

/-- Far terms are small (upward direction), for an abstract log-concave sequence. -/
lemma far_up (T : ℕ → ℝ) (s m : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hnn : ∀ i, 0 ≤ T i) (hlc : ∀ k, T k * T (k + 2) ≤ μ * T (k + 1) ^ 2)
    (hpos : ∀ i, 0 < T i ↔ (1 ≤ i ∧ i ≤ s)) (hm1 : 1 ≤ m) (hmax : ∀ i, T i ≤ T m) :
    ∀ d, T (m + d + 2) ≤ μ * T m := by
  have aux : ∀ d, T (m + d + 1) ≤ T (m + d) → T (m + d + 2) ≤ μ * T (m + d + 1) := by
    intro d hd
    rcases (hnn (m + d)).lt_or_eq with h | h
    · have h1 := hlc (m + d)
      have h2 : μ * T (m + d + 1) ^ 2 ≤ μ * T (m + d + 1) * T (m + d) := by
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hd (mul_nonneg hμ0 (hnn _))
      have h3 : T (m + d) * T (m + d + 2) ≤ T (m + d) * (μ * T (m + d + 1)) := by
        have : m + d + 1 + 1 = m + d + 2 := rfl
        nlinarith
      exact le_of_mul_le_mul_left h3 h
    · have hs : ¬ (m + d ≤ s) := by
        intro hc
        have := (hpos (m + d)).2 ⟨by omega, hc⟩
        linarith
      have h4 : ¬ (0 < T (m + d + 2)) := by
        rw [hpos]; omega
      push Not at h4
      linarith [mul_nonneg hμ0 (hnn (m + d + 1))]
  have mono : ∀ d, T (m + d + 1) ≤ T (m + d) := by
    intro d
    induction d with
    | zero => simpa using hmax (m + 1)
    | succ d ih =>
      have h5 := aux d ih
      have e1 : m + (d + 1) + 1 = m + d + 2 := by ring
      have e2 : m + (d + 1) = m + d + 1 := by ring
      rw [e1, e2]
      nlinarith [hnn (m + d + 1)]
  intro d
  calc T (m + d + 2) ≤ μ * T (m + d + 1) := aux d (mono d)
    _ ≤ μ * T m := mul_le_mul_of_nonneg_left (hmax _) hμ0

/-- Far terms are small in both directions. -/
lemma far (T : ℕ → ℝ) (s m : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hnn : ∀ i, 0 ≤ T i) (hlc : ∀ k, T k * T (k + 2) ≤ μ * T (k + 1) ^ 2)
    (hpos : ∀ i, 0 < T i ↔ (1 ≤ i ∧ i ≤ s)) (hm1 : 1 ≤ m) (hms : m ≤ s)
    (hmax : ∀ i, T i ≤ T m) :
    ∀ i, (i + 2 ≤ m ∨ m + 2 ≤ i) → T i ≤ μ * T m := by
  intro i hi
  rcases hi with hi | hi
  · -- reflect
    set U : ℕ → ℝ := fun i => T (s + 1 - i) with hU
    have hT0 : T 0 = 0 := by
      have h := hpos 0
      have : ¬ (0 < T 0) := by rw [h]; omega
      linarith [hnn 0]
    have hUnn : ∀ i, 0 ≤ U i := fun i => hnn _
    have hUpos : ∀ i, 0 < U i ↔ (1 ≤ i ∧ i ≤ s) := by
      intro i; simp only [hU]; rw [hpos]; omega
    have hUlc : ∀ k, U k * U (k + 2) ≤ μ * U (k + 1) ^ 2 := by
      intro k
      simp only [hU]
      by_cases hk : k + 2 ≤ s + 1
      · have := hlc (s + 1 - (k + 2))
        have e1 : s + 1 - (k + 2) + 2 = s + 1 - k := by omega
        have e2 : s + 1 - (k + 2) + 1 = s + 1 - (k + 1) := by omega
        rw [e1, e2] at this
        linarith
      · have : s + 1 - (k + 2) = 0 := by omega
        rw [this, hT0, mul_zero]
        exact mul_nonneg hμ0 (sq_nonneg _)
    have hUmax : ∀ i, U i ≤ U (s + 1 - m) := by
      intro i; simp only [hU]
      have : s + 1 - (s + 1 - m) = m := by omega
      rw [this]; exact hmax _
    have := far_up U s (s + 1 - m) μ hμ0 hμ1 hUnn hUlc hUpos (by omega) hUmax (m - i - 2)
    simp only [hU] at this
    have e1 : s + 1 - (s + 1 - m + (m - i - 2) + 2) = i := by omega
    have e2 : s + 1 - (s + 1 - m) = m := by omega
    rw [e1, e2] at this
    exact this
  · have := far_up T s m μ hμ0 hμ1 hnn hlc hpos hm1 hmax (i - m - 2)
    have e : m + (i - m - 2) + 2 = i := by omega
    rw [e] at this
    exact this

/-- The combinatorial core: if the alternating sum vanishes, two consecutive terms are close. -/
lemma core (T : ℕ → ℝ) (s : ℕ) (θk : ℝ) (hθ0 : 0 ≤ θk) (he : ((s : ℝ) + 1) * θk ≤ 1 / 2)
    (hnn : ∀ i, 0 ≤ T i) (hlc : ∀ k, T k * T (k + 2) ≤ θk ^ 2 * T (k + 1) ^ 2)
    (hpos : ∀ i, 0 < T i ↔ (1 ≤ i ∧ i ≤ s)) (hs : 1 ≤ s)
    (hsum : ∑ i ∈ Icc 1 s, (-1 : ℝ) ^ (i - 1) * T i = 0) :
    ∃ i ∈ Icc 1 (s - 1), |T i - T (i + 1)| ≤ 2 * (((s : ℝ) + 1) * θk) * T (i + 1) := by
  have hSne : (Icc 1 s).Nonempty := ⟨1, by simp; omega⟩
  obtain ⟨m, hmS, hmmax⟩ := Finset.exists_max_image (Icc 1 s) T hSne
  have hmS' := Finset.mem_Icc.1 hmS
  have hM : 0 < T m := (hpos m).2 hmS'
  have hmax : ∀ i, T i ≤ T m := by
    intro i
    by_cases hi : i ∈ Icc 1 s
    · exact hmmax i hi
    · have : ¬ (0 < T i) := by rw [hpos]; simpa using hi
      linarith [hnn i]
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hθ1 : θk ≤ 1 := by nlinarith
  set μ := θk ^ 2 with hμ
  have hμ0 : 0 ≤ μ := sq_nonneg _
  have hμ1 : μ ≤ 1 := by rw [hμ]; nlinarith
  have hμθ : μ ≤ θk := by rw [hμ]; nlinarith
  have hfar := far T s m μ hμ0 hμ1 hnn hlc hpos hmS'.1 hmS'.2 hmax
  -- the dominant term is bounded by the rest
  have hsplit := Finset.add_sum_erase (Icc 1 s) (fun i => (-1 : ℝ) ^ (i - 1) * T i) hmS
  rw [hsum] at hsplit
  have hrest : |∑ i ∈ (Icc 1 s).erase m, (-1 : ℝ) ^ (i - 1) * T i| = T m := by
    have : ∑ i ∈ (Icc 1 s).erase m, (-1 : ℝ) ^ (i - 1) * T i = -((-1 : ℝ) ^ (m - 1) * T m) := by
      linarith
    rw [this, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hM]
  have hle1 : T m ≤ ∑ i ∈ (Icc 1 s).erase m, T i := by
    rw [← hrest]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (hnn i)]
  set A := T (m - 1) with hA
  set B := T (m + 1) with hB
  have hle2 : ∑ i ∈ (Icc 1 s).erase m, T i ≤ ∑ i ∈ (Icc 1 s).erase m,
      ((if i = m - 1 then A else 0) + (if i = m + 1 then B else 0) + μ * T m) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_erase.1 hi
    have hi'' := Finset.mem_Icc.1 hi'.2
    have hμM : 0 ≤ μ * T m := mul_nonneg hμ0 hM.le
    split_ifs with h1 h2 h2
    · omega
    · rw [h1]; linarith
    · rw [h2]; linarith
    · have := hfar i (by omega)
      linarith
  have hA0 : 0 ≤ A := hnn _
  have hB0 : 0 ≤ B := hnn _
  have hle3 : ∑ i ∈ (Icc 1 s).erase m,
      ((if i = m - 1 then A else 0) + (if i = m + 1 then B else 0) + μ * T m) ≤
      A + B + s * (μ * T m) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      Finset.sum_const, nsmul_eq_mul]
    have hc : (((Icc 1 s).erase m).card : ℝ) ≤ s := by
      have := Finset.card_erase_le (s := Icc 1 s) (a := m)
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    have h1 : (if m - 1 ∈ (Icc 1 s).erase m then A else 0) ≤ A := by split_ifs <;> linarith
    have h2 : (if m + 1 ∈ (Icc 1 s).erase m then B else 0) ≤ B := by split_ifs <;> linarith
    have h3 : (((Icc 1 s).erase m).card : ℝ) * (μ * T m) ≤ s * (μ * T m) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hμ0 hM.le)
    linarith
  have hkey : T m ≤ A + B + s * (μ * T m) := by linarith
  have hAB : A * B ≤ μ * T m ^ 2 := by
    have := hlc (m - 1)
    have e1 : m - 1 + 2 = m + 1 := by omega
    have e2 : m - 1 + 1 = m := by omega
    rw [e1, e2] at this
    exact this
  have hAM : A ≤ T m := hmax _
  have hBM : B ≤ T m := hmax _
  have hsμ : (s : ℝ) * (μ * T m) ≤ s * (θk * T m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hμθ hM.le) hs0
  have he0 : 0 ≤ ((s : ℝ) + 1) * θk := by positivity
  rcases le_or_gt A B with hle | hlt
  · -- A is the small one
    have hAsmall : A ≤ θk * T m := by
      by_contra hc
      push Not at hc
      have h0 : 0 ≤ θk * T m := mul_nonneg hθ0 hM.le
      have : (θk * T m) * (θk * T m) < A * A := mul_self_lt_mul_self h0 hc
      nlinarith
    have hBbig : T m - B ≤ ((s : ℝ) + 1) * θk * T m := by nlinarith
    have hB2 : T m ≤ 2 * B := by nlinarith
    have hBpos : 0 < B := by linarith
    have hm1s : 1 ≤ m + 1 ∧ m + 1 ≤ s := (hpos (m + 1)).1 hBpos
    refine ⟨m, Finset.mem_Icc.2 ⟨hmS'.1, by omega⟩, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    calc T m - B ≤ ((s : ℝ) + 1) * θk * T m := hBbig
      _ ≤ ((s : ℝ) + 1) * θk * (2 * B) := mul_le_mul_of_nonneg_left hB2 he0
      _ = 2 * (((s : ℝ) + 1) * θk) * B := by ring
  · -- B is the small one
    have hBsmall : B ≤ θk * T m := by
      by_contra hc
      push Not at hc
      have h0 : 0 ≤ θk * T m := mul_nonneg hθ0 hM.le
      have : (θk * T m) * (θk * T m) < B * B := mul_self_lt_mul_self h0 hc
      nlinarith
    have hAbig : T m - A ≤ ((s : ℝ) + 1) * θk * T m := by nlinarith
    have hApos : 0 < A := by nlinarith
    have hm1s : 1 ≤ m - 1 ∧ m - 1 ≤ s := (hpos (m - 1)).1 hApos
    refine ⟨m - 1, Finset.mem_Icc.2 ⟨hm1s.1, by omega⟩, ?_⟩
    have e : m - 1 + 1 = m := by omega
    rw [e, abs_of_nonpos (by linarith)]
    calc -(A - T m) = T m - A := by ring
      _ ≤ ((s : ℝ) + 1) * θk * T m := hAbig
      _ ≤ 2 * (((s : ℝ) + 1) * θk) * T m := by nlinarith

/-- Numerical constants: `θ = 1 - 1/(2(S-1)^2)`, `q = 1 + ε/2`, `α = q(1-ε)` with
`ε = 1/(2S^2)`. -/
lemma constants (S : ℝ) (hS3 : 3 ≤ S) :
    ∃ θ q α : ℝ, 0 ≤ θ ∧ 1 < q ∧ q < S ∧ 0 < α ∧ α < 1 ∧ θ * q ≤ α ∧
      (∀ i : ℝ, 1 ≤ i → i + 1 ≤ S → i * q ≤ α * (i + 1)) ∧
      (∀ k : ℝ, 1 ≤ k → k + 2 ≤ S → k * (k + 2) ≤ θ ^ 2 * (k + 1) ^ 2) := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * S ^ 2) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (2 * (S - 1) ^ 2) := ⟨_, rfl⟩
  have hS0 : 0 < S := by linarith
  have hS1 : 0 < S - 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεS : ε * (2 * S ^ 2) = 1 := by rw [hε]; field_simp
  have hS2 : 9 ≤ S ^ 2 := by nlinarith
  have hε1 : ε ≤ 1 / 18 := by nlinarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have hxS : x * (2 * (S - 1) ^ 2) = 1 := by rw [hx]; field_simp
  have hS12 : 4 ≤ (S - 1) ^ 2 := by nlinarith
  have hx1 : x ≤ 1 / 8 := by nlinarith
  have hεx : ε ≤ x := by
    have h1 : (S - 1) ^ 2 ≤ S ^ 2 := by nlinarith
    have h2 : x * (2 * (S - 1) ^ 2) ≤ x * (2 * S ^ 2) := by nlinarith
    have h3 : ε * (2 * S ^ 2) ≤ x * (2 * S ^ 2) := by linarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  refine ⟨1 - x, 1 + ε / 2, (1 + ε / 2) * (1 - ε), by linarith, by linarith, by linarith,
    by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
  · intro i hi1 hiS
    have h1 : i + 1 ≤ 2 * S ^ 2 := by nlinarith
    have h2 : ε * (i + 1) ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε / 2)
      (by linarith : (0 : ℝ) ≤ 1 - ε * (i + 1))]
  · intro k hk1 hk2
    have ht : (k + 1) ^ 2 ≤ (S - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h1 : 2 * x * (k + 1) ^ 2 ≤ 1 := by nlinarith
    have hθ2 : 1 - 2 * x ≤ (1 - x) ^ 2 := by nlinarith [sq_nonneg x]
    have h2 : (1 - 2 * x) * (k + 1) ^ 2 ≤ (1 - x) ^ 2 * (k + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hθ2 (sq_nonneg _)
    nlinarith

/-- The terms `T_i = i^κ C(n, s-i)` for `1 ≤ i ≤ s`, extended by zero. -/
noncomputable def Tf (s n κ : ℕ) (i : ℕ) : ℝ :=
  if 1 ≤ i ∧ i ≤ s then (i : ℝ) ^ κ * (n.choose (s - i) : ℝ) else 0

lemma Tf_in (s n κ i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ s) :
    Tf s n κ i = (i : ℝ) ^ κ * (n.choose (s - i) : ℝ) := by
  unfold Tf; rw [if_pos ⟨h1, h2⟩]

lemma Tf_out (s n κ i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ s)) : Tf s n κ i = 0 := by
  unfold Tf; rw [if_neg h]

lemma choose_pos_real (s n r : ℕ) (hn : s < n) (hr : r ≤ s) : (0 : ℝ) < (n.choose r : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega)

lemma Tf_nonneg (s n κ : ℕ) : ∀ i, 0 ≤ Tf s n κ i := by
  intro i
  by_cases h : 1 ≤ i ∧ i ≤ s
  · rw [Tf_in s n κ i h.1 h.2]; positivity
  · rw [Tf_out s n κ i h]

lemma Tf_pos (s n κ : ℕ) (hn : s < n) : ∀ i, 0 < Tf s n κ i ↔ (1 ≤ i ∧ i ≤ s) := by
  intro i
  constructor
  · intro h
    by_contra hc
    rw [Tf_out s n κ i hc] at h
    exact lt_irrefl _ h
  · intro h
    rw [Tf_in s n κ i h.1 h.2]
    have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast h.1
    have := choose_pos_real s n (s - i) hn (Nat.sub_le _ _)
    positivity

lemma Tf_lc (s n κ : ℕ) (θ : ℝ)
    (hθ : ∀ k : ℝ, 1 ≤ k → k + 2 ≤ (s : ℝ) → k * (k + 2) ≤ θ ^ 2 * (k + 1) ^ 2) :
    ∀ k, Tf s n κ k * Tf s n κ (k + 2) ≤ (θ ^ κ) ^ 2 * Tf s n κ (k + 1) ^ 2 := by
  intro k
  by_cases hk : 1 ≤ k ∧ k + 2 ≤ s
  · rw [Tf_in s n κ k hk.1 (by omega), Tf_in s n κ (k + 2) (by omega) hk.2,
      Tf_in s n κ (k + 1) (by omega) (by omega)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk2 : (k : ℝ) + 2 ≤ (s : ℝ) := by exact_mod_cast hk.2
    have hpow := hθ k hk1 hk2
    have hpowk : ((k : ℝ) * ((k : ℝ) + 2)) ^ κ ≤ (θ ^ 2 * ((k : ℝ) + 1) ^ 2) ^ κ :=
      pow_le_pow_left₀ (by positivity) hpow κ
    have hb := choose_lc n (s - k - 2)
    have e1 : s - k - 2 + 2 = s - k := by omega
    have e2 : s - k - 2 + 1 = s - (k + 1) := by omega
    have e3 : s - k - 2 = s - (k + 2) := by omega
    rw [e1, e2, e3] at hb
    have hbR : (n.choose (s - k) : ℝ) * (n.choose (s - (k + 2)) : ℝ) ≤
        (n.choose (s - (k + 1)) : ℝ) ^ 2 := by exact_mod_cast hb
    have hc0 : (0 : ℝ) ≤ (n.choose (s - k) : ℝ) * (n.choose (s - (k + 2)) : ℝ) := by positivity
    have hk2' : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    have hk1' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hk2', hk1']
    calc (k : ℝ) ^ κ * (n.choose (s - k) : ℝ) * (((k : ℝ) + 2) ^ κ * (n.choose (s - (k + 2)) : ℝ))
        = ((k : ℝ) * ((k : ℝ) + 2)) ^ κ *
            ((n.choose (s - k) : ℝ) * (n.choose (s - (k + 2)) : ℝ)) := by rw [mul_pow]; ring
      _ ≤ (θ ^ 2 * ((k : ℝ) + 1) ^ 2) ^ κ * ((n.choose (s - (k + 1)) : ℝ) ^ 2) :=
          mul_le_mul hpowk hbR hc0 (by positivity)
      _ = (θ ^ κ) ^ 2 * (((k : ℝ) + 1) ^ κ * (n.choose (s - (k + 1)) : ℝ)) ^ 2 := by
          have p1 : (θ ^ 2) ^ κ = (θ ^ κ) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
          have p2 : (((k : ℝ) + 1) ^ 2) ^ κ = (((k : ℝ) + 1) ^ κ) ^ 2 := by
            rw [← pow_mul, ← pow_mul, mul_comm]
          rw [mul_pow, p1, p2]; ring
  · have h0 : Tf s n κ k * Tf s n κ (k + 2) = 0 := by
      by_cases h1 : 1 ≤ k
      · rw [Tf_out s n κ (k + 2) (by omega), mul_zero]
      · rw [Tf_out s n κ k (by omega), zero_mul]
    rw [h0]; positivity

lemma Tf_sum (s n j : ℕ) (hf : gfsPoly s n j = 0) :
    ∑ i ∈ Icc 1 s, (-1 : ℝ) ^ (i - 1) * Tf s n (j - 1) i = 0 := by
  have hf' : ((gfsPoly s n j : ℤ) : ℝ) = 0 := by rw [hf]; simp
  unfold gfsPoly at hf'
  push_cast at hf'
  rw [← hf']
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Icc.1 hi
  rw [Tf_in s n (j - 1) i hi'.1 hi'.2]
  ring

/-- Converting closeness of `T_i, T_{i+1}` into the near-equation. -/
lemma conversion (s n κ i : ℕ) (hn : s < n) (hi1 : 1 ≤ i) (his : i + 1 ≤ s) (e : ℝ)
    (hclose : |Tf s n κ i - Tf s n κ (i + 1)| ≤ 2 * e * Tf s n κ (i + 1)) :
    |(n : ℝ) * (i : ℝ) ^ κ - ((s : ℝ) - i) * ((i : ℝ) + 1) ^ κ| ≤
      2 * e * (((s : ℝ) - i) * ((i : ℝ) + 1) ^ κ) + (s : ℝ) * (i : ℝ) ^ κ := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((s : ℝ) - i) * ((i : ℝ) + 1) ^ κ := ⟨_, rfl⟩
  rw [← hYdef]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (n.choose (s - (i + 1)) : ℝ) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact choose_pos_real s n _ hn (by omega)
  have hIs : (i : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast his
  have hpas : (n.choose (s - i) : ℝ) * ((s : ℝ) - i) = c * ((n : ℝ) - s + i + 1) := by
    have h := Nat.choose_succ_right_eq n (s - (i + 1))
    have e1 : s - (i + 1) + 1 = s - i := by omega
    rw [e1] at h
    have h' : ((n.choose (s - i) * (s - i) : ℕ) : ℝ) =
        ((n.choose (s - (i + 1)) * (n - (s - (i + 1))) : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub (by omega : i ≤ s), Nat.cast_sub (by omega : s - (i + 1) ≤ n),
      Nat.cast_sub (by omega : i + 1 ≤ s)] at h'
    rw [hc]; linarith
  have hTi : Tf s n κ i = (i : ℝ) ^ κ * (n.choose (s - i) : ℝ) := Tf_in s n κ i hi1 (by omega)
  have hTi1 : Tf s n κ (i + 1) = ((i : ℝ) + 1) ^ κ * c := by
    rw [Tf_in s n κ (i + 1) (by omega) (by omega), hc]; push_cast; ring
  have hdiff : ((s : ℝ) - i) * (Tf s n κ i - Tf s n κ (i + 1)) =
      c * ((i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y) := by
    rw [hTi, hTi1, hYdef]
    have : ((s : ℝ) - i) * ((i : ℝ) ^ κ * (n.choose (s - i) : ℝ)) =
        (i : ℝ) ^ κ * ((n.choose (s - i) : ℝ) * ((s : ℝ) - i)) := by ring
    rw [mul_sub, this, hpas]; ring
  have hTY : ((s : ℝ) - i) * Tf s n κ (i + 1) = c * Y := by rw [hTi1, hYdef]; ring
  have hsi : (0 : ℝ) < (s : ℝ) - i := by linarith
  have herr1 : |(i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y| ≤ 2 * e * Y := by
    have h1 : c * |(i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y| =
        ((s : ℝ) - i) * |Tf s n κ i - Tf s n κ (i + 1)| := by
      rw [← abs_of_pos hcpos, ← abs_mul, ← hdiff, abs_mul, abs_of_pos hsi]
    have h2 : ((s : ℝ) - i) * |Tf s n κ i - Tf s n κ (i + 1)| ≤
        ((s : ℝ) - i) * (2 * e * Tf s n κ (i + 1)) :=
      mul_le_mul_of_nonneg_left hclose hsi.le
    have h3 : ((s : ℝ) - i) * (2 * e * Tf s n κ (i + 1)) = c * (2 * e * Y) := by
      linear_combination (2 * e) * hTY
    have h4 : c * |(i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y| ≤ c * (2 * e * Y) := by linarith
    exact le_of_mul_le_mul_left h4 hcpos
  have hIκ0 : (0 : ℝ) ≤ (i : ℝ) ^ κ := by positivity
  have hsplit : (n : ℝ) * (i : ℝ) ^ κ - Y = ((i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y) +
      (i : ℝ) ^ κ * ((s : ℝ) - i - 1) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hI0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have h5 : |(i : ℝ) ^ κ * ((s : ℝ) - i - 1)| ≤ (s : ℝ) * (i : ℝ) ^ κ := by
    rw [abs_of_nonneg (mul_nonneg hIκ0 (by linarith))]
    nlinarith
  linarith

/-- The final real-variable estimate. -/
lemma final_step (S q α θ I N : ℝ) (κ : ℕ) (hS1 : 1 < S) (hq1 : 1 < q) (hθ0 : 0 ≤ θ)
    (hα0 : 0 < α) (hθq : θ * q ≤ α) (hακ : 4 * (S + 1) * q * α ^ κ ≤ 1) (hI1 : 1 ≤ I)
    (hIS : I + 1 ≤ S) (hiq : I * q ≤ α * (I + 1))
    (herr : |N - (S - I) * (I + 1) ^ κ| ≤
      2 * ((S + 1) * θ ^ κ) * ((S - I) * (I + 1) ^ κ) + S * I ^ κ) :
    |N - (S - I) * (I + 1) ^ κ| ≤ ((S - I) * (I + 1) ^ κ) ^ (1 - Real.logb S q) := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = (S - I) * (I + 1) ^ κ := ⟨_, rfl⟩
  rw [← hYdef] at herr ⊢
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.logb S q := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.logb_pos hS1 hq1
  have hSδ : S ^ δ = q := by rw [hδ]; exact Real.rpow_logb (by linarith) (by linarith) (by linarith)
  have hsi : (1 : ℝ) ≤ S - I := by linarith
  have hi1κ : (1 : ℝ) ≤ (I + 1) ^ κ := one_le_pow₀ (by linarith)
  have hYge : (I + 1) ^ κ ≤ Y := by rw [hYdef]; nlinarith
  have hYpos : 0 < Y := by linarith
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Y ^ δ := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hYpos δ
  have hYS : Y ≤ S ^ (κ + 1) := by
    rw [hYdef, pow_succ]
    have h1 : (I + 1) ^ κ ≤ S ^ κ := pow_le_pow_left₀ (by linarith) hIS κ
    have h2 : S - I ≤ S := by linarith
    have h3 : 0 ≤ (I + 1) ^ κ := by positivity
    have h4 : 0 ≤ S ^ κ := by positivity
    nlinarith
  have hPq : P ≤ q ^ (κ + 1) := by
    calc P = Y ^ δ := hP
      _ ≤ (S ^ (κ + 1)) ^ δ := Real.rpow_le_rpow hYpos.le hYS hδ0.le
      _ = (S ^ δ) ^ (κ + 1) := by
          rw [← Real.rpow_natCast_mul (by linarith), ← Real.rpow_mul_natCast (by linarith),
            mul_comm]
      _ = q ^ (κ + 1) := by rw [hSδ]
  have hR : Y ^ (1 - δ) = Y / P := by
    rw [Real.rpow_sub hYpos, Real.rpow_one, hP]
  have hθκ0 : 0 ≤ θ ^ κ := pow_nonneg hθ0 κ
  have hθκα : θ ^ κ * q ^ κ ≤ α ^ κ := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hθ0 (by linarith)) hθq κ
  have hqκ0 : 0 ≤ q ^ κ := by positivity
  -- condition 1
  have hc1 : 2 * ((S + 1) * θ ^ κ) * Y * (2 * P) ≤ Y := by
    have h1 : 4 * ((S + 1) * θ ^ κ) * P ≤ 1 := by
      calc 4 * ((S + 1) * θ ^ κ) * P ≤ 4 * ((S + 1) * θ ^ κ) * q ^ (κ + 1) :=
            mul_le_mul_of_nonneg_left hPq (by positivity)
        _ = 4 * (S + 1) * q * (θ ^ κ * q ^ κ) := by rw [pow_succ]; ring
        _ ≤ 4 * (S + 1) * q * α ^ κ :=
            mul_le_mul_of_nonneg_left hθκα (by positivity)
        _ ≤ 1 := hακ
    have := mul_le_mul_of_nonneg_left h1 hYpos.le
    nlinarith
  -- condition 2
  have hc2 : S * I ^ κ * (2 * P) ≤ Y := by
    have hiqκ : (I * q) ^ κ ≤ (α * (I + 1)) ^ κ :=
      pow_le_pow_left₀ (by positivity) hiq κ
    rw [mul_pow, mul_pow] at hiqκ
    have h2 : 2 * S * q * α ^ κ ≤ 1 := by
      have : 0 ≤ q * α ^ κ := by positivity
      nlinarith
    calc S * I ^ κ * (2 * P) ≤ S * I ^ κ * (2 * q ^ (κ + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = 2 * S * q * (I ^ κ * q ^ κ) := by rw [pow_succ]; ring
      _ ≤ 2 * S * q * (α ^ κ * (I + 1) ^ κ) :=
          mul_le_mul_of_nonneg_left hiqκ (by positivity)
      _ = (2 * S * q * α ^ κ) * (I + 1) ^ κ := by ring
      _ ≤ 1 * (I + 1) ^ κ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ Y := by linarith
  rw [hR, le_div_iff₀ hPpos]
  have := mul_le_mul_of_nonneg_right herr hPpos.le
  nlinarith

end TwoTermApprox

open TwoTermApprox in
theorem two_term_approx (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ J0 : ℕ, ∀ n j : ℕ, s < n → J0 ≤ j → gfsPoly s n j = 0 →
      ∃ i ∈ Finset.Icc 1 (s - 1),
        |((n * i ^ (j - 1) : ℕ) : ℝ) - (((s - i) * (i + 1) ^ (j - 1) : ℕ) : ℝ)| ≤
          (((s - i) * (i + 1) ^ (j - 1) : ℕ) : ℝ) ^ (1 - δ) ∧
        n ≤ 2 * ((s - i) * (i + 1) ^ (j - 1)) := by
  have hS3 : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hS1 : (1 : ℝ) < (s : ℝ) := by linarith
  obtain ⟨θ, q, α, hθ0, hq1, hqS, hα0, hα1, hθq, hiq, hlcθ⟩ := constants (s : ℝ) hS3
  have hC : 0 < 1 / (4 * ((s : ℝ) + 1) * q) := by positivity
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hC hα1
  have hKall : ∀ κ, K ≤ κ → 4 * ((s : ℝ) + 1) * q * α ^ κ ≤ 1 := by
    intro κ hκ
    have h1 : α ^ κ ≤ α ^ K := pow_le_pow_of_le_one hα0.le hα1.le hκ
    have h2 : 0 < 4 * ((s : ℝ) + 1) * q := by positivity
    have h3 : α ^ κ < 1 / (4 * ((s : ℝ) + 1) * q) := lt_of_le_of_lt h1 hK
    rw [lt_div_iff₀ h2] at h3
    linarith
  refine ⟨Real.logb (s : ℝ) q, Real.logb_pos hS1 hq1, ?_, K + 1, ?_⟩
  · rw [← Real.logb_self_eq_one hS1]
    exact Real.logb_lt_logb hS1 (by linarith) hqS
  intro n j hn hj hf
  have hακ := hKall (j - 1) (by omega)
  -- `(s+1) θ^κ ≤ 1/2`
  have hθκ0 : 0 ≤ θ ^ (j - 1) := pow_nonneg hθ0 _
  have he : ((s : ℝ) + 1) * θ ^ (j - 1) ≤ 1 / 2 := by
    have h1 : θ ^ (j - 1) ≤ α ^ (j - 1) := by
      have hθα : θ ≤ α := le_trans (by nlinarith) hθq
      exact pow_le_pow_left₀ hθ0 hθα _
    have h2 : 0 ≤ α ^ (j - 1) := pow_nonneg hα0.le _
    have h3 : 4 * ((s : ℝ) + 1) * α ^ (j - 1) ≤ 4 * ((s : ℝ) + 1) * q * α ^ (j - 1) := by
      have : 0 ≤ 4 * ((s : ℝ) + 1) * α ^ (j - 1) := by positivity
      nlinarith
    have h4 : ((s : ℝ) + 1) * θ ^ (j - 1) ≤ ((s : ℝ) + 1) * α ^ (j - 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  obtain ⟨i, hi, hclose⟩ := core (Tf s n (j - 1)) s (θ ^ (j - 1)) hθκ0 he
    (Tf_nonneg s n (j - 1)) (Tf_lc s n (j - 1) θ hlcθ) (Tf_pos s n (j - 1) hn) (by omega)
    (Tf_sum s n j hf)
  have hi' := Finset.mem_Icc.1 hi
  refine ⟨i, hi, ?_⟩
  have herr := conversion s n (j - 1) i hn hi'.1 (by omega) _ hclose
  have hI1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi'.1
  have hIs : (i : ℝ) + 1 ≤ (s : ℝ) := by
    have : i + 1 ≤ s := by omega
    exact_mod_cast this
  have hmain := final_step (s : ℝ) q α θ (i : ℝ) ((n : ℝ) * (i : ℝ) ^ (j - 1)) (j - 1) hS1 hq1
    hθ0 hα0 hθq hακ hI1 hIs (hiq (i : ℝ) hI1 hIs) herr
  have hYcast : (((s - i) * (i + 1) ^ (j - 1) : ℕ) : ℝ) =
      ((s : ℝ) - i) * ((i : ℝ) + 1) ^ (j - 1) := by
    push_cast [Nat.cast_sub (by omega : i ≤ s)]; ring
  have hXcast : ((n * i ^ (j - 1) : ℕ) : ℝ) = (n : ℝ) * (i : ℝ) ^ (j - 1) := by
    push_cast; ring
  rw [hYcast, hXcast]
  refine ⟨hmain, ?_⟩
  -- `n ≤ 2Y`
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((s : ℝ) - i) * ((i : ℝ) + 1) ^ (j - 1) := ⟨_, rfl⟩
  rw [← hYdef] at hmain hYcast
  have hδ1 : Real.logb (s : ℝ) q < 1 := by
    rw [← Real.logb_self_eq_one hS1]
    exact Real.logb_lt_logb hS1 (by linarith) hqS
  have hi1κ : (1 : ℝ) ≤ ((i : ℝ) + 1) ^ (j - 1) := one_le_pow₀ (by linarith)
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    have : (1 : ℝ) ≤ (s : ℝ) - i := by linarith
    nlinarith
  have hRY : Y ^ (1 - Real.logb (s : ℝ) q) ≤ Y := by
    calc Y ^ (1 - Real.logb (s : ℝ) q) ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [Real.logb_pos hS1 hq1])
      _ = Y := Real.rpow_one Y
  have h1 : (n : ℝ) * (i : ℝ) ^ (j - 1) ≤ 2 * Y := by
    have := (abs_le.1 hmain).2
    linarith
  have hiκ1 : (1 : ℝ) ≤ (i : ℝ) ^ (j - 1) := one_le_pow₀ hI1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h2 : (n : ℝ) ≤ 2 * Y := by nlinarith
  rw [← hYcast] at h2
  exact_mod_cast h2

end Erdos494
