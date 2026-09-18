import ErdosLean.Erdos790.Defs

/-! Part: `n/(log n)²` beats `√n` and every `n^{1-ε}`. -/

namespace Erdos790

open Filter

lemma asymptotics_key (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ c * x / Real.log x ^ 2 := by
  have h := (isLittleO_log_rpow_atTop (half_pos hε)).bound (Real.sqrt_pos.2 hc)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hxpos : 0 < x := by linarith
  rw [Real.norm_of_nonneg hl.le, Real.norm_of_nonneg (by positivity)] at hx
  have hsq : Real.log x ^ 2 ≤ c * x ^ ε := by
    calc Real.log x ^ 2 ≤ (Real.sqrt c * x ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ hl.le hx 2
      _ = c * x ^ ε := by
        rw [mul_pow, Real.sq_sqrt hc.le, ← Real.rpow_natCast (x ^ (ε / 2)),
          ← Real.rpow_mul hxpos.le]
        norm_num
  rw [le_div_iff₀ (by positivity)]
  calc x ^ (1 - ε) * Real.log x ^ 2 ≤ x ^ (1 - ε) * (c * x ^ ε) := by gcongr
    _ = c * x := by rw [mul_left_comm, ← Real.rpow_add hxpos]; simp

theorem asymptotics (f : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ f n) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.sqrt n) atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ f n := by
  have h2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ f n := by
    intro ε hε
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (asymptotics_key c hc ε hε),
      eventually_ge_atTop 2] with n hn h2n
    exact hn.trans (hf n h2n)
  refine ⟨?_, h2⟩
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)
  filter_upwards [h2 (1 / 4) (by norm_num), eventually_ge_atTop 1] with n hn h1n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1n
  simp only [Function.comp]
  rw [le_div_iff₀ (Real.sqrt_pos.2 hnpos), Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
  norm_num at hn ⊢
  exact hn

end Erdos790
