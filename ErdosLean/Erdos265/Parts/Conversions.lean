import ErdosLean.Erdos265.Defs

/-!
# Erdős #265 — Part L7: conversions between growth formulations

* `aₙ^{1/βⁿ} → ∞` (`β > 1`) implies `aₙ^{1/n} → ∞`
  (`aₙ^{1/n} = (aₙ^{1/βⁿ})^{βⁿ/n}` and `βⁿ/n → ∞`);
* `aₙ ≥ 1` and `log aₙ / 2ⁿ → 0` imply `aₙ^{1/2ⁿ} = exp (log aₙ / 2ⁿ) → 1`;
* item 3 of `Erdos265Statement` implies Kitamura's form `Erdos265LimsupNegative`
  (`c^{2ⁿ} ≤ aₙ` gives `aₙ^{1/2ⁿ} ≥ c > 1` infinitely often).
-/

open Filter Topology

namespace Erdos265

theorem rpow_inv_n_of_beta {a : ℕ → ℕ} {β : ℝ} (hβ : 1 < β)
    (h : Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / β ^ n)) atTop atTop) :
    Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop atTop := by
  have hβ0 : 0 < β := by linarith
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℕ) / β ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 hβ
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ β ^ n := by
    filter_upwards [hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with n hn
    rw [pow_one, div_lt_one (pow_pos hβ0 n)] at hn
    exact hn.le
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [hev, h.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hn hx hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hbpos : 0 < β ^ n := pow_pos hβ0 n
  have hsplit : (1 : ℝ) / n = (1 / β ^ n) * (β ^ n / n) := by
    field_simp
  rw [hsplit, Real.rpow_mul (Nat.cast_nonneg _)]
  calc (a n : ℝ) ^ ((1 : ℝ) / β ^ n)
      = ((a n : ℝ) ^ ((1 : ℝ) / β ^ n)) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ ((a n : ℝ) ^ ((1 : ℝ) / β ^ n)) ^ (β ^ n / n) := by
        apply Real.rpow_le_rpow_of_exponent_le hx
        rw [le_div_iff₀ hnpos]; linarith

theorem rpow_two_pow_tendsto_one {a : ℕ → ℕ} (h1 : ∀ n, 1 ≤ (a n : ℝ))
    (h : Tendsto (fun n : ℕ ↦ Real.log (a n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 1) := by
  have heq : (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)) =
      fun n ↦ Real.exp (Real.log (a n : ℝ) / (2 : ℝ) ^ n) := by
    funext n
    rw [Real.rpow_def_of_pos (by linarith [h1 n])]
    congr 1; ring
  rw [heq, ← Real.exp_zero]
  exact (Real.continuous_exp.tendsto 0).comp h

theorem limsup_negative_of
    (h : ∀ a : ℕ → ℕ, IsRationalPair a →
      Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 1)) :
    Erdos265LimsupNegative := by
  rintro ⟨a, ha, c, hc, hfreq⟩
  have hlim := h a ha
  have hev : ∀ᶠ n : ℕ in atTop, (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n) < c :=
    hlim.eventually (gt_mem_nhds hc)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
  have hc0 : 0 ≤ c := by linarith
  have hkey : (c ^ (2 ^ n : ℕ)) ^ ((1 : ℝ) / (2 : ℝ) ^ n) = c := by
    have : (1 : ℝ) / (2 : ℝ) ^ n = (((2 ^ n : ℕ) : ℝ))⁻¹ := by push_cast; ring
    rw [this, Real.pow_rpow_inv_natCast hc0 (by positivity)]
  have : c ≤ (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n) := by
    calc c = (c ^ (2 ^ n : ℕ)) ^ ((1 : ℝ) / (2 : ℝ) ^ n) := hkey.symm
      _ ≤ (a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n) :=
        Real.rpow_le_rpow (by positivity) hn1 (by positivity)
  linarith

end Erdos265
