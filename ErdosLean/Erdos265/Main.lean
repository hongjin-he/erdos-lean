import ErdosLean.Erdos265.Parts.SquareRec
import ErdosLean.Erdos265.Parts.QuadLimit
import ErdosLean.Erdos265.Parts.LogBound
import ErdosLean.Erdos265.Parts.ResidualLower
import ErdosLean.Erdos265.Parts.ResidualUpper
import ErdosLean.Erdos265.Parts.ExpGrowth
import ErdosLean.Erdos265.Parts.TailRegular
import ErdosLean.Erdos265.Parts.MajorantVanish
import ErdosLean.Erdos265.Parts.BlockApprox
import ErdosLean.Erdos265.Parts.NestedBoxes
import ErdosLean.Erdos265.Parts.SeqAssembly
import ErdosLean.Erdos265.Parts.DoubleExp
import ErdosLean.Erdos265.Parts.Conversions

/-!
# Erdős Problem 265 (JSP-000229): main theorem

Assembly of the parts:
* `growth_half` — Kovač–Tao construction (arXiv:2406.17593 v4, Theorem 2.8 / Corollary 2.9,
  §7, `d = 2`), with modified parameters `N_k = 4^{m_k}` and `β = 51/50`;
* `barrier_half` — every admissible sequence has `log aₙ / 2ⁿ → 0`: an independent Lean
  formalisation of Kitamura's argument (tail envelope and second residual); the mathematics
  of this half is due to K. Kitamura;
* `erdos_265 : Erdos265Statement`, i.e. `51/50 ≤ β* ≤ 2` for the optimal exponent `β*`,
  which remains open.
-/

open Filter Topology

namespace Erdos265

/-- **Barrier half** (Kitamura's argument).  Every admissible sequence has `log aₙ / 2ⁿ → 0`. -/
theorem barrier_half {a : ℕ → ℕ} (ha : IsRationalPair a) :
    Tendsto (fun n : ℕ ↦ Real.log (a n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  obtain ⟨K, hK, hrec⟩ := Henv_sq_rec ha
  obtain ⟨ℓ, hℓ0, hlim⟩ := quad_limit (one_le_Henv ha) hK (Eventually.of_forall hrec)
  -- the positive-limit branch is impossible
  have hℓ : ℓ = 0 := by
    by_contra hne
    have hpos : 0 < ℓ := lt_of_le_of_ne hℓ0 (Ne.symm hne)
    obtain ⟨K', hK', hlow⟩ := residual_lower ha
    have hup := residual_upper ha
    have htr := tail_regular ha (exp_growth ha hpos hlim)
    have htr' : ∀ᶠ n in atTop, T a (n + 1) ≤ regF a (n + 1) / (a (n + 1) : ℝ) :=
      (tendsto_add_atTop_nat 1).eventually htr
    have hmaj := majorant_vanish ha hpos hlim
    have h0 : Tendsto (fun n ↦ 8 * K' * ((P a n : ℝ) ^ 2 * (regF a n / (a n : ℝ)) *
        (regF a (n + 1) / (a (n + 1) : ℝ)))) atTop (𝓝 0) := by
      simpa using hmaj.const_mul (8 * K')
    have hsmall := h0.eventually (gt_mem_nhds zero_lt_one)
    obtain ⟨n, hn1, hn2, hn3, hn4, hn5⟩ :=
      (hlow.and (hup.and (htr.and (htr'.and hsmall)))).exists
    have hT0 := T_nonneg ha n
    have hT1 := T_nonneg ha (n + 1)
    have hp : 0 ≤ (P a n : ℝ) ^ 2 := by positivity
    have hu0 : 0 ≤ regF a n / (a n : ℝ) := hT0.trans hn3
    have hprod : T a n * T a (n + 1) ≤
        (regF a n / (a n : ℝ)) * (regF a (n + 1) / (a (n + 1) : ℝ)) :=
      mul_le_mul hn3 hn4 hT1 hu0
    have hKp : 0 ≤ K' * (P a n : ℝ) ^ 2 := mul_nonneg hK'.le hp
    have hchain : K' * (P a n : ℝ) ^ 2 * Eres a n ≤
        8 * K' * ((P a n : ℝ) ^ 2 * (regF a n / (a n : ℝ)) *
          (regF a (n + 1) / (a (n + 1) : ℝ))) := by
      calc K' * (P a n : ℝ) ^ 2 * Eres a n
          ≤ K' * (P a n : ℝ) ^ 2 * (8 * T a n * T a (n + 1)) :=
            mul_le_mul_of_nonneg_left hn2 hKp
        _ ≤ K' * (P a n : ℝ) ^ 2 * (8 * ((regF a n / (a n : ℝ)) *
              (regF a (n + 1) / (a (n + 1) : ℝ)))) := by
            rw [mul_assoc 8]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hprod (by norm_num)) hKp
        _ = 8 * K' * ((P a n : ℝ) ^ 2 * (regF a n / (a n : ℝ)) *
              (regF a (n + 1) / (a (n + 1) : ℝ))) := by ring
    linarith
  subst hℓ
  -- squeeze `0 ≤ log aₙ / 2ⁿ ≤ 2 · logRatio Henv (n+1)`
  have hup : Tendsto (fun n : ℕ ↦ 2 * logRatio (Henv a) (n + 1)) atTop (𝓝 0) := by
    simpa using (hlim.comp (tendsto_add_atTop_nat 1)).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n ↦ div_nonneg (log_a_nonneg ha n) (by positivity)) (fun n ↦ ?_)
  have h2 : (2 : ℝ) * logRatio (Henv a) (n + 1) =
      Real.log (Henv a (n + 1)) / (2 : ℝ) ^ n := by
    unfold logRatio
    rw [pow_succ]
    field_simp
  show Real.log (a n : ℝ) / (2 : ℝ) ^ n ≤ 2 * logRatio (Henv a) (n + 1)
  rw [h2]
  exact div_le_div_of_nonneg_right (log_a_le_log_Henv_succ ha n) (by positivity)

/-- **Growth half** (Kovač–Tao).  An admissible sequence with `aₙ^{1/(51/50)ⁿ} → ∞`. -/
theorem growth_half : ∃ a : ℕ → ℕ, IsRationalPair a ∧
    Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (51 / 50 : ℝ) ^ n)) atTop atTop := by
  obtain ⟨hs1, hs2⟩ := center_summable
  have hr1 := rad1_pos 0
  have hr2 := rad2_pos 0
  obtain ⟨q1, hq1l, hq1r⟩ := exists_rat_btwn
    (show ∑' k, (center k).1 - rad1 0 < ∑' k, (center k).1 + rad1 0 by linarith)
  obtain ⟨q2, hq2l, hq2r⟩ := exists_rat_btwn
    (show ∑' k, (center k).2 - rad2 0 < ∑' k, (center k).2 + rad2 0 by linarith)
  have hx1 : |((q1 : ℝ), (q2 : ℝ)).1 - ∑' k, (center k).1| ≤ rad1 0 :=
    abs_le.2 ⟨by simp only; linarith, by simp only; linarith⟩
  have hx2 : |((q1 : ℝ), (q2 : ℝ)).2 - ∑' k, (center k).2| ≤ rad2 0 :=
    abs_le.2 ⟨by simp only; linarith, by simp only; linarith⟩
  obtain ⟨c, hadm, h1, h2⟩ := nested_boxes blockVal Adm center rad1 rad2 hs1 hs2
    rad1_tendsto rad2_tendsto (fun _ _ hi ↦ blockVal_nonneg hi)
    (fun k δ h1 h2 ↦ by
      obtain ⟨c, hc, e1, e2⟩ := block_approx k δ h1 h2
      exact ⟨c, hc, e1.trans (step_rad1 k), e2.trans (step_rad2 k)⟩)
    ((q1 : ℝ), (q2 : ℝ)) hx1 hx2
  exact ⟨seqOf c, isRationalPair_of_blocks hadm h1 h2, seqOf_double_exp hadm⟩

/-- **Erdős #265, known bounds** (both halves; the optimal exponent remains open). -/
theorem erdos_265 : Erdos265Statement := by
  obtain ⟨a, ha, hg⟩ := growth_half
  refine ⟨⟨a, ha, 51 / 50, by norm_num, hg⟩,
    ⟨a, ha, rpow_inv_n_of_beta (by norm_num) hg⟩, fun b hb ↦ ?_⟩
  refine rpow_two_pow_tendsto_one (fun n ↦ ?_) (barrier_half hb)
  have : 1 ≤ b n := le_trans (by norm_num) (two_le_of hb n)
  exact_mod_cast this

/-- Kitamura's form of the `limsup` sub-question (negative answer), as a corollary. -/
theorem erdos_265_limsup : Erdos265LimsupNegative :=
  limsup_negative_of erdos_265.2.2

end Erdos265
