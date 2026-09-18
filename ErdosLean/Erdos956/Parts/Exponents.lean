import Mathlib

/-!
# Erdős #956 — Part 17: `c₀ n^{4/3} ≤ g(n)` eventually ⟹ `n^{1+c} < g(n)` eventually, `c < 1/3`

`n^{1+c} = n^{4/3} · n^{c - 1/3}` and `n^{c-1/3} → 0`.
-/

namespace Erdos956

open Filter

theorem exponents_of_lower (g : ℕ → ℕ)
    (hg : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, c₀ * (n : ℝ) ^ ((4 : ℝ) / 3) ≤ g n) :
    ∀ c : ℝ, c < 1 / 3 → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < g n := by
  intro c hc
  obtain ⟨c₀, hc₀, h⟩ := hg
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 3 - c))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h, ht.eventually (gt_mem_nhds hc₀), eventually_ge_atTop 1] with n hn hlt h1
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hsplit : (n : ℝ) ^ (1 + c) = (n : ℝ) ^ ((4 : ℝ) / 3) * (n : ℝ) ^ (-(1 / 3 - c)) := by
    rw [← Real.rpow_add hpos]; congr 1; ring
  rw [hsplit]
  calc (n : ℝ) ^ ((4 : ℝ) / 3) * (n : ℝ) ^ (-(1 / 3 - c))
      < (n : ℝ) ^ ((4 : ℝ) / 3) * c₀ := mul_lt_mul_of_pos_left hlt (by positivity)
    _ = c₀ * (n : ℝ) ^ ((4 : ℝ) / 3) := mul_comm _ _
    _ ≤ g n := hn

end Erdos956
