import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 3: capping `ψ`

We replace `ψ` by `capψ ψ = min(ψ, q/(2φ(q)))`: then
`w = min(w, 1/2)` (still divergent), the radius `≤ 1/(2φ(q)) → 0` (needed by Gallagher), and
`A_q` only shrinks.  Also: windows `[N, Y]` with `∑ w ∈ [1, 2]` (KM §5).
-/

open MeasureTheory Filter Topology

namespace DuffinSchaeffer

theorem capψ_nonneg (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) : 0 ≤ capψ ψ q := by
  unfold capψ
  exact le_min (hψ q) (by positivity)

theorem capψ_le (ψ : ℕ → ℝ) (q : ℕ) : capψ ψ q ≤ ψ q := min_le_left _ _

theorem weight_capψ_le_half (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) :
    weight (capψ ψ) q ≤ 1 / 2 := by
  unfold weight
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hq']
  calc (Nat.totient q : ℝ) * capψ ψ q ≤ (Nat.totient q : ℝ) * ((q : ℝ) / (2 * Nat.totient q)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hφ.le
    _ = 1 / 2 * q := by field_simp

theorem weight_capψ_eq (ψ : ℕ → ℝ) (q : ℕ) (h : weight (capψ ψ) q < 1 / 2) :
    weight (capψ ψ) q = weight ψ q := by
  unfold weight at *
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold capψ at *
  rcases min_choice (ψ q) ((q : ℝ) / (2 * Nat.totient q)) with h1 | h1
  · rw [h1]
  · exfalso
    rw [h1] at h
    have : (Nat.totient q : ℝ) * ((q : ℝ) / (2 * Nat.totient q)) / q = 1 / 2 := by
      field_simp
    linarith

theorem weight_nonneg (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) : 0 ≤ weight ψ q := by
  unfold weight
  have := hψ q
  positivity

theorem not_summable_weight_capψ (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q)
    (h : ¬ Summable (weight ψ)) : ¬ Summable (weight (capψ ψ)) := by
  intro hs
  apply h
  have ht := hs.tendsto_cofinite_zero
  have hev : ∀ᶠ q in cofinite, weight (capψ ψ) q < 1 / 2 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  refine hs.of_norm_bounded_eventually ?_
  filter_upwards [hev] with q hq
  rw [weight_capψ_eq ψ q hq, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg ψ hψ q)]

/-- If `φ(p^k) ≤ K` for all prime powers dividing `n`, then `n ∣ (2K)!`. -/
theorem le_factorial_of_totient_le {n K : ℕ} (hn : 0 < n) (hK : Nat.totient n ≤ K) :
    n ≤ Nat.factorial (2 * K) := by
  have hdvd : n ∣ Nat.factorial (2 * K) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hpp : p.Prime := hp
    apply Nat.dvd_factorial (pow_pos hpp.pos k)
    have h1 : Nat.totient (p ^ k) ≤ Nat.totient n :=
      Nat.le_of_dvd (Nat.totient_pos.2 hn) (Nat.totient_dvd_of_dvd hpk)
    rw [Nat.totient_prime_pow hpp hk] at h1
    have h2 : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    have h3 : p ≤ 2 * (p - 1) := by have := hpp.two_le; omega
    calc p ^ k = p ^ (k - 1) * p := h2
      _ ≤ p ^ (k - 1) * (2 * (p - 1)) := Nat.mul_le_mul_left _ h3
      _ = 2 * (p ^ (k - 1) * (p - 1)) := by ring
      _ ≤ 2 * K := by omega
  exact Nat.le_of_dvd (Nat.factorial_pos _) hdvd

theorem tendsto_totient_atTop : Tendsto (fun n : ℕ => Nat.totient n) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  rw [eventually_atTop]
  refine ⟨Nat.factorial (2 * K) + 1, fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  have := le_factorial_of_totient_le (n := n) (K := K) (by omega) hlt.le
  omega

/-- The radius `capψ ψ q / q ≤ 1/(2φ(q))` tends to `0`. -/
theorem tendsto_capψ_div (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) :
    Tendsto (fun n : ℕ => capψ ψ n / n) atTop (𝓝 0) := by
  have hφ : Tendsto (fun n : ℕ => ((Nat.totient n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_totient_atTop
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((Nat.totient n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hφ).const_mul (1 / 2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with n
    exact div_nonneg (capψ_nonneg ψ hψ n) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hφ0 : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.2 hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    calc capψ ψ n ≤ (n : ℝ) / (2 * Nat.totient n) := min_le_right _ _
      _ = 1 / 2 * (Nat.totient n : ℝ)⁻¹ * n := by field_simp

/-- A window `[N, Y]` with `1 ≤ ∑_{N ≤ q ≤ Y} w(q) ≤ 2`, for a divergent series with terms `≤ 1/2`. -/
theorem exists_window (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hle : ∀ q, weight ψ q ≤ 1 / 2)
    (h : ¬ Summable (weight ψ)) (N : ℕ) :
    ∃ Y : ℕ, 1 ≤ ∑ q ∈ Finset.Icc N Y, weight ψ q ∧ ∑ q ∈ Finset.Icc N Y, weight ψ q ≤ 2 := by
  have hw := weight_nonneg ψ hψ
  set S : ℕ → ℝ := fun M => ∑ q ∈ Finset.Ico N M, weight ψ q with hS
  have hex : ∃ M, 1 ≤ S M := by
    by_contra hne
    push Not at hne
    apply h
    refine summable_of_sum_range_le (c := ∑ q ∈ Finset.range N, weight ψ q + 1) hw ?_
    intro n
    rcases le_total N n with hNn | hnN
    · rw [← Finset.sum_range_add_sum_Ico _ hNn]
      have := hne n
      simp only [hS] at this
      linarith
    · have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hnN)
        (fun i _ _ => hw i)
      linarith
  classical
  let M := Nat.find hex
  have hM : 1 ≤ S M := Nat.find_spec hex
  have hNM : N < M := by
    by_contra hc
    push Not at hc
    have : S M = 0 := by
      simp only [hS]
      rw [Finset.Ico_eq_empty_of_le hc, Finset.sum_empty]
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y, M = Y + 1 := ⟨M - 1, by omega⟩
  have hprev : ¬ 1 ≤ S Y := Nat.find_min hex (by omega)
  have hIcc : Finset.Icc N Y = Finset.Ico N (Y + 1) := (Finset.Ico_add_one_right_eq_Icc N Y).symm
  refine ⟨Y, ?_, ?_⟩
  · rw [hIcc]; rw [hY] at hM; exact hM
  · rw [hIcc, Finset.sum_Ico_succ_top (by omega)]
    have := hle Y
    simp only [hS] at hprev
    linarith

end DuffinSchaeffer
