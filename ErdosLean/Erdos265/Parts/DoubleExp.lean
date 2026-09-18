import ErdosLean.Erdos265.Parts.Params

/-!
# Erdős #265 — Part L6: doubly exponential growth of the constructed sequence

For `n = 2k + j`: `aₙ ≥ N_k - M_k ≥ N_k/2 = 4^{m_k}/2`, and
`m_k ≥ 40 (21/20)^k ≥ 40 (21/20)^{(n-1)/2}`.  Since `√(21/20) > 51/50`,
`log aₙ / (51/50)ⁿ → ∞`, i.e. `aₙ^{1/(51/50)ⁿ} → ∞`.

(We use the slightly weaker, cleaner bound `aₙ ≥ M_k = 2^{m_k}`.)
-/

open Filter Topology

namespace Erdos265

theorem seqOf_ge_MM {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) (n : ℕ) :
    MM (n / 2) ≤ seqOf c n := by
  have h4 := MM_ge (n / 2)
  have hsq := MM_sq (n / 2)
  obtain ⟨h1, h2⟩ := hc (n / 2)
  have hsqZ : ((NN (n / 2) : ℕ) : ℤ) = (MM (n / 2) : ℤ) ^ 2 := by exact_mod_cast hsq.symm
  have h4Z : (4 : ℤ) ≤ (MM (n / 2) : ℤ) := by exact_mod_cast h4
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have e1 : (MM (n / 2) : ℤ) ≤ (NN (n / 2) : ℤ) + (c (n / 2)).1 := by nlinarith
  have e2 : (MM (n / 2) : ℤ) ≤ 2 * (NN (n / 2) : ℤ) + (c (n / 2)).2 := by nlinarith
  unfold seqOf
  split_ifs <;> omega

theorem seqOf_double_exp {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) :
    Tendsto (fun n : ℕ ↦ (seqOf c n : ℝ) ^ ((1 : ℝ) / (51 / 50 : ℝ) ^ n)) atTop atTop := by
  have key : ∀ n : ℕ, (2 : ℝ) ^ ((40 / (51 / 50 : ℝ)) * ((21 / 20 : ℝ) / (51 / 50) ^ 2) ^ (n / 2))
      ≤ (seqOf c n : ℝ) ^ ((1 : ℝ) / (51 / 50 : ℝ) ^ n) := by
    intro n
    have hA : (2 : ℝ) ^ (mSeq (n / 2)) ≤ (seqOf c n : ℝ) := by
      have := seqOf_ge_MM hc n
      unfold MM at this
      exact_mod_cast this
    have hm := mSeq_growth (n / 2)
    have hpos : 0 < (51 / 50 : ℝ) ^ n := by positivity
    have hn : (51 / 50 : ℝ) ^ n ≤ (51 / 50 : ℝ) ^ (2 * (n / 2) + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hE : (40 / (51 / 50 : ℝ)) * ((21 / 20 : ℝ) / (51 / 50) ^ 2) ^ (n / 2)
        ≤ (mSeq (n / 2) : ℝ) / (51 / 50 : ℝ) ^ n := by
      rw [le_div_iff₀ hpos]
      calc (40 / (51 / 50 : ℝ)) * ((21 / 20 : ℝ) / (51 / 50) ^ 2) ^ (n / 2) * (51 / 50 : ℝ) ^ n
          ≤ (40 / (51 / 50 : ℝ)) * ((21 / 20 : ℝ) / (51 / 50) ^ 2) ^ (n / 2)
              * (51 / 50 : ℝ) ^ (2 * (n / 2) + 1) :=
            mul_le_mul_of_nonneg_left hn (by positivity)
        _ = 40 * (21 / 20 : ℝ) ^ (n / 2) := by
            rw [div_pow, pow_succ (51 / 50 : ℝ) (2 * (n / 2)), pow_mul]
            field_simp
        _ ≤ (mSeq (n / 2) : ℝ) := hm
    generalize hR : (51 / 50 : ℝ) ^ n = R at hE hpos ⊢
    generalize hK : (40 / (51 / 50 : ℝ)) * ((21 / 20 : ℝ) / (51 / 50) ^ 2) ^ (n / 2) = K at hE ⊢
    calc (2 : ℝ) ^ K ≤ (2 : ℝ) ^ ((mSeq (n / 2) : ℝ) / R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
      _ = ((2 : ℝ) ^ (mSeq (n / 2))) ^ ((1 : ℝ) / R) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div]
      _ ≤ (seqOf c n : ℝ) ^ ((1 : ℝ) / R) :=
          Real.rpow_le_rpow (by positivity) hA (by positivity)
  refine tendsto_atTop_mono key ?_
  have h1 : Tendsto (fun n : ℕ ↦ ((21 / 20 : ℝ) / (51 / 50) ^ 2) ^ (n / 2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp (Nat.tendsto_div_const_atTop two_ne_zero)
  have h2 := h1.const_mul_atTop (show (0 : ℝ) < 40 / (51 / 50) by norm_num)
  exact (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp h2

end Erdos265
