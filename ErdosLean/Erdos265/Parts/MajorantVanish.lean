import ErdosLean.Erdos265.Parts.ExpGrowth
import ErdosLean.Erdos265.Parts.TailRegular

/-!
# Erdős #265 — Part U10: in the positive-limit branch the majorant tends to `0`

Let `L n = log P n`.  From `Dt n ≥ 1/a_n²` we get `Henv n ≤ P (n+1)`; from
Part U9, `Dt n ≤ (2/a_n) T n ≤ 2 F_n/a_n²`, so `Henv n ≥ P (n+1)/√(2F_n)`.  With
`log F_n = O(n)` this gives `L (n+1) = ℓ 2ⁿ + o(2ⁿ)`.  Then
`log (P_n² F_n F_{n+1}/(a_n a_{n+1})) = 3 L n - L (n+2) + log F_n + log F_{n+1}
 = -(ℓ/2) 2ⁿ + o(2ⁿ) → -∞`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

lemma mv_one_le_P (ha : IsRationalPair a) (n : ℕ) : 1 ≤ P a n := by
  unfold P
  rw [Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro k _
  have := two_le_of ha k
  omega

lemma mv_P_succ (n : ℕ) : (P a (n + 1) : ℝ) = (P a n : ℝ) * (a n : ℝ) := by
  unfold P
  rw [Finset.prod_range_succ]
  push_cast
  ring

/-- `Dt n ≤ (2/a_n) T n`. -/
lemma mv_Dt_le_two_T (ha : IsRationalPair a) (n : ℕ) :
    Dt a n ≤ 2 / (a n : ℝ) * T a n := by
  have hs : Summable (fun k => recip a (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_recip ha)
  have hsD : Summable (fun k => recipD a (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_recipD ha)
  have hX : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have hpt : ∀ k, recipD a (k + n) ≤ 2 / (a n : ℝ) * recip a (k + n) := by
    intro k
    have hk : (a n : ℝ) ≤ a (k + n) := by exact_mod_cast ha.1.monotone (by omega)
    unfold recipD recip
    rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith
  unfold Dt T tail
  rw [← tsum_mul_left]
  exact hsD.tsum_le_tsum hpt (hs.mul_left _)

lemma mv_logH (ha : IsRationalPair a) (n : ℕ) :
    Real.log (Henv a n) = Real.log (P a n : ℝ) - Real.log (Dt a n) / 2 := by
  have hD := Dt_pos ha n
  have hP : (1 : ℝ) ≤ (P a n : ℝ) := by exact_mod_cast mv_one_le_P ha n
  unfold Henv
  rw [Real.log_div (by positivity) (Real.sqrt_pos.mpr hD).ne', Real.log_sqrt hD.le]

lemma mv_logD_lower (ha : IsRationalPair a) (n : ℕ) :
    -2 * Real.log (a n : ℝ) ≤ Real.log (Dt a n) := by
  have hX : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have h := Real.log_le_log (by positivity) (inv_sq_le_Dt ha n)
  rw [one_div, Real.log_inv, Real.log_pow] at h
  push_cast at h
  linarith

lemma mv_logD_upper (ha : IsRationalPair a) {n : ℕ} (hT : T a n ≤ regF a n / (a n : ℝ)) :
    Real.log (Dt a n) ≤ Real.log 2 + Real.log (regF a n) - 2 * Real.log (a n : ℝ) := by
  have hX : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have hF : (2 : ℝ) ≤ regF a n := by
    unfold regF
    have := Nat.cast_nonneg (α := ℝ) ⌈Real.log (a n : ℝ)⌉₊
    linarith
  have hD := Dt_pos ha n
  have h1 : Dt a n ≤ 2 * regF a n / (a n : ℝ) ^ 2 := by
    calc Dt a n ≤ 2 / (a n : ℝ) * T a n := mv_Dt_le_two_T ha n
      _ ≤ 2 / (a n : ℝ) * (regF a n / (a n : ℝ)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = 2 * regF a n / (a n : ℝ) ^ 2 := by ring
  have h2 := Real.log_le_log hD h1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow] at h2
  push_cast at h2
  linarith

theorem majorant_vanish (ha : IsRationalPair a) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlim : Tendsto (logRatio (Henv a)) atTop (𝓝 ℓ)) :
    Tendsto (fun n ↦ (P a n : ℝ) ^ 2 * (regF a n / (a n : ℝ)) *
      (regF a (n + 1) / (a (n + 1) : ℝ))) atTop (𝓝 0) := by
  have hX : ∀ n, (2 : ℝ) ≤ (a n : ℝ) := fun n => by exact_mod_cast two_le_of ha n
  have hP1 : ∀ n, (1 : ℝ) ≤ (P a n : ℝ) := fun n => by exact_mod_cast mv_one_le_P ha n
  have hF2 : ∀ n, (2 : ℝ) ≤ regF a n := fun n => by
    unfold regF
    have := Nat.cast_nonneg (α := ℝ) ⌈Real.log (a n : ℝ)⌉₊
    linarith
  have hLs : ∀ n, Real.log (P a (n + 1) : ℝ) =
      Real.log (P a n : ℝ) + Real.log (a n : ℝ) := by
    intro n
    rw [mv_P_succ, Real.log_mul (by linarith [hP1 n]) (by linarith [hX n])]
  have h2pos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  -- r n = n / 2^n → 0
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    simpa using this
  -- growth bound on log F
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n : ℕ in atTop, Real.log (regF a n) ≤ B * n := by
    have hev : ∀ᶠ n : ℕ in atTop, logRatio (Henv a) n ≤ ℓ + 1 :=
      hlim.eventually (ge_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    set C : ℝ := 2 * ℓ + 5 with hC
    have hC1 : (1 : ℝ) ≤ C := by linarith
    have hlC : 0 ≤ Real.log C := Real.log_nonneg hC1
    refine ⟨Real.log C + Real.log 2, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n + 1 := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_of_max_le_right hn)
    have h1 := hN (n + 1) hnN
    unfold logRatio at h1
    rw [div_le_iff₀ (h2pos _)] at h1
    have h2 := log_a_le_log_Henv_succ ha n
    have hceil : regF a n ≤ Real.log (a n : ℝ) + 3 := by
      unfold regF
      have := Nat.ceil_lt_add_one (log_a_nonneg ha n)
      linarith
    have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hFC : regF a n ≤ C * (2 : ℝ) ^ n := by
      rw [pow_succ] at h1
      rw [hC]
      nlinarith
    have := Real.log_le_log (by linarith [hF2 n]) hFC
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow] at this
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hlF0 : ∀ n, 0 ≤ Real.log (regF a n) := fun n =>
    Real.log_nonneg (by linarith [hF2 n])
  -- v n = L(n+1)/2^(n+1) → ℓ/2
  have hv : Tendsto (fun n : ℕ => Real.log (P a (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1))
      atTop (𝓝 (ℓ / 2)) := by
    have hlo : Tendsto (fun n => logRatio (Henv a) n / 2) atTop (𝓝 (ℓ / 2)) :=
      hlim.div_const 2
    have hhi : Tendsto (fun n : ℕ => logRatio (Henv a) n / 2 +
        (Real.log 2 + B) / 4 * ((n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 (ℓ / 2)) := by
      have := hlo.add (hr.const_mul ((Real.log 2 + B) / 4))
      simpa using this
    have htr := tail_regular ha (exp_growth ha hℓ hlim)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards with n
      have hH := mv_logH ha n
      have hD := mv_logD_lower ha n
      unfold logRatio
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), pow_succ, hLs n]
      nlinarith [h2pos n]
    · filter_upwards [htr, hB, eventually_ge_atTop 1] with n hn hBn hn1
      have hH := mv_logH ha n
      have hD := mv_logD_upper ha hn
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      unfold logRatio
      have hq : 0 < (2 : ℝ) ^ n := h2pos n
      rw [pow_succ, hLs n]
      rw [div_le_iff₀ (by positivity)]
      have e1 : (Real.log (Henv a n) / 2 ^ n / 2 +
          (Real.log 2 + B) / 4 * (↑n / 2 ^ n)) * (2 ^ n * 2) =
          Real.log (Henv a n) + (Real.log 2 + B) / 2 * n := by
        field_simp; ring
      rw [e1]
      nlinarith
  have hu : Tendsto (fun n : ℕ => Real.log (P a n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 (ℓ / 2)) :=
    (tendsto_add_atTop_iff_nat 1).mp hv
  have hu2 : Tendsto (fun n : ℕ => Real.log (P a (n + 2) : ℝ) / (2 : ℝ) ^ (n + 2))
      atTop (𝓝 (ℓ / 2)) := (tendsto_add_atTop_iff_nat 2).mpr hu
  have hw : Tendsto (fun n : ℕ => Real.log (regF a n) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have hhi : Tendsto (fun n : ℕ => B * ((n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using hr.const_mul B
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards with n
      exact div_nonneg (hlF0 n) (h2pos n).le
    · filter_upwards [hB] with n hn
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hn (h2pos n).le
  have hw1 : Tendsto (fun n : ℕ => Real.log (regF a (n + 1)) / (2 : ℝ) ^ (n + 1))
      atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hw
  -- the log of the majorant over 2^n
  set Q : ℕ → ℝ := fun n ↦ (P a n : ℝ) ^ 2 * (regF a n / (a n : ℝ)) *
      (regF a (n + 1) / (a (n + 1) : ℝ)) with hQ
  have hQpos : ∀ n, 0 < Q n := by
    intro n
    have := hX n; have := hX (n + 1); have := hF2 n; have := hF2 (n + 1); have := hP1 n
    simp only [hQ]
    positivity
  have hlogQ : ∀ n, Real.log (Q n) / (2 : ℝ) ^ n =
      3 * (Real.log (P a n : ℝ) / (2 : ℝ) ^ n)
      - 4 * (Real.log (P a (n + 2) : ℝ) / (2 : ℝ) ^ (n + 2))
      + Real.log (regF a n) / (2 : ℝ) ^ n
      + 2 * (Real.log (regF a (n + 1)) / (2 : ℝ) ^ (n + 1)) := by
    intro n
    have := hX n; have := hX (n + 1); have := hF2 n; have := hF2 (n + 1); have := hP1 n
    have e : Real.log (Q n) = 2 * Real.log (P a n : ℝ) + (Real.log (regF a n) -
        Real.log (a n : ℝ)) + (Real.log (regF a (n + 1)) - Real.log (a (n + 1) : ℝ)) := by
      simp only [hQ]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]
      push_cast; ring
    have e2 : Real.log (P a (n + 2) : ℝ) = Real.log (P a n : ℝ) + Real.log (a n : ℝ) +
        Real.log (a (n + 1) : ℝ) := by
      rw [hLs (n + 1), hLs n]
    rw [e, e2]
    have hq := h2pos n
    field_simp
    ring
  have hlim2 : Tendsto (fun n => Real.log (Q n) / (2 : ℝ) ^ n) atTop (𝓝 (-(ℓ / 2))) := by
    have := (((hu.const_mul 3).sub (hu2.const_mul 4)).add hw).add (hw1.const_mul 2)
    have e : 3 * (ℓ / 2) - 4 * (ℓ / 2) + 0 + 2 * 0 = -(ℓ / 2) := by ring
    rw [e] at this
    exact this.congr (fun n => (hlogQ n).symm)
  have hbot : Tendsto (fun n => Real.log (Q n)) atTop atBot := by
    have h := hlim2.neg_mul_atTop (by linarith)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    refine h.congr (fun n => ?_)
    have hq := h2pos n
    field_simp
  have := Real.tendsto_exp_atBot.comp hbot
  exact this.congr (fun n => Real.exp_log (hQpos n))

end Erdos265
