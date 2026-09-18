import ErdosLean.Erdos996.Parts.Asm.Construction
import ErdosLean.Erdos996.Parts.Asm.Params

/-!
# Assembly sub-lemma 12 (TailAsymp): the tail sum beats `(log log log N)^{-C}`

Blueprint §11. Replaces Ho Prop. 5.2 for #996 (fixed `C`, no endpoint): split the stages into
`2^{E_k} ≤ √N` (contribution `≤ ∑ λ_k / √N ≤ N^{-1/2}`) and `N < 2^{2E_k}` (then
`log log log N ≤ B_k := (A+1)(k+1)+30`, so `λ_k ≤ λ_k B_k^{2C} / (log log log N)^{2C}`, and
`∑ λ_k B_k^{2C} < ∞` since `λ_k` decays geometrically); finally
`N^{-1/2} ≤ (log log log N)^{-2C}` for large `N`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma alt_log_gt_three (N : ℕ) (hN : 32 ≤ N) : 3 < Real.log (N : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h : Real.log ((2 : ℝ) ^ 5) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ^ 5 ≤ N by norm_num; omega))
  rw [Real.log_pow] at h
  push_cast at h
  linarith

lemma alt_one_lt_loglog (N : ℕ) (hN : 32 ≤ N) : 1 < Real.log (Real.log (N : ℝ)) := by
  have h3 := alt_log_gt_three N hN
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

lemma alt_lll_pos (N : ℕ) (hN : 32 ≤ N) : 0 < Real.log (Real.log (Real.log (N : ℝ))) :=
  Real.log_pos (alt_one_lt_loglog N hN)

lemma alt_lll_le_log (N : ℕ) (hN : 32 ≤ N) :
    Real.log (Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) := by
  have h1 := alt_one_lt_loglog N hN
  have h3 := alt_log_gt_three N hN
  calc _ ≤ Real.log (Real.log (N : ℝ)) := Real.log_le_self (by linarith)
    _ ≤ Real.log (N : ℝ) := Real.log_le_self (by linarith)

lemma alt_lll_lt (N e : ℕ) (hN : 32 ≤ N) (h : (N : ℝ) < (2 : ℝ) ^ (2 * e)) :
    Real.log (Real.log (Real.log (N : ℝ))) <
      Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * e)))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 := alt_one_lt_loglog N hN
  have h3 := alt_log_gt_three N hN
  have g1 : Real.log (N : ℝ) < Real.log ((2 : ℝ) ^ (2 * e)) := Real.log_lt_log hNpos h
  have g2 : Real.log (Real.log (N : ℝ)) < Real.log (Real.log ((2 : ℝ) ^ (2 * e))) :=
    Real.log_lt_log (by linarith) g1
  exact Real.log_lt_log (by linarith) g2

/-- Per-term bound. -/
lemma alt_term_bound (A : ℕ) (C : ℝ) (hC : 0 < C) (e k : ℕ)
    (hE : Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * e)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30)
    (N : ℕ) (hN : 32 ≤ N) :
    lam A k * min 1 ((2 : ℝ) ^ e / N) ≤
      lam A k / Real.sqrt N + lam A k * ((((A : ℝ) + 1) * (k + 1) + 30) ^ C) ^ 2 /
        (Real.log (Real.log (Real.log (N : ℝ))) ^ C) ^ 2 := by
  have hl := lam_pos A k
  set B : ℝ := ((A : ℝ) + 1) * (k + 1) + 30 with hB
  set L := Real.log (Real.log (Real.log (N : ℝ))) with hL
  have hLpos : 0 < L := alt_lll_pos N hN
  have hu : 0 < L ^ C := Real.rpow_pos_of_pos hLpos C
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hBpos : 0 < B := by rw [hB]; positivity
  have t1 : 0 ≤ lam A k / Real.sqrt N := by positivity
  have t2 : 0 ≤ lam A k * (B ^ C) ^ 2 / (L ^ C) ^ 2 := by positivity
  have hmin0 : 0 ≤ min 1 ((2 : ℝ) ^ e / N) := le_min zero_le_one (by positivity)
  by_cases h : (2 : ℝ) ^ (2 * e) ≤ N
  · have h1 : Real.sqrt (((2 : ℝ) ^ e) ^ 2) ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (by rw [← pow_mul, mul_comm]; exact h)
    rw [Real.sqrt_sq (by positivity)] at h1
    have e1 : Real.sqrt N / N = 1 / Real.sqrt N := by
      rw [eq_div_iff hs.ne', div_mul_eq_mul_div, div_eq_one_iff_eq hNpos.ne']
      exact Real.mul_self_sqrt hNpos.le
    have h2 : min 1 ((2 : ℝ) ^ e / N) ≤ 1 / Real.sqrt N := by
      rw [← e1]
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_right h1 hNpos.le)
    calc lam A k * min 1 ((2 : ℝ) ^ e / N) ≤ lam A k * (1 / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h2 hl.le
      _ = lam A k / Real.sqrt N := by rw [mul_one_div]
      _ ≤ _ := le_add_of_nonneg_right t2
  · push Not at h
    have hlt := alt_lll_lt N e hN h
    have hLB : L ≤ B := (le_of_lt hlt).trans hE
    have hLC : L ^ C ≤ B ^ C := Real.rpow_le_rpow hLpos.le hLB hC.le
    have hsq : (L ^ C) ^ 2 ≤ (B ^ C) ^ 2 := pow_le_pow_left₀ hu.le hLC 2
    have hone : 1 ≤ (B ^ C) ^ 2 / (L ^ C) ^ 2 := (one_le_div (by positivity)).2 hsq
    calc lam A k * min 1 ((2 : ℝ) ^ e / N) ≤ lam A k * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hl.le
      _ ≤ lam A k * ((B ^ C) ^ 2 / (L ^ C) ^ 2) := mul_le_mul_of_nonneg_left hone hl.le
      _ = lam A k * (B ^ C) ^ 2 / (L ^ C) ^ 2 := by rw [mul_div_assoc]
      _ ≤ _ := le_add_of_nonneg_left t1

/-- Summability of the weighted stage costs `λ_k B_k^{2C}`. -/
lemma alt_summable_weight (A : ℕ) (hA : 1 ≤ A) (C : ℝ) (_hC : 0 < C) :
    Summable (fun k : ℕ => lam A k * ((((A : ℝ) + 1) * (k + 1) + 30) ^ C) ^ 2) := by
  set n := ⌈C⌉₊
  set c : ℝ := ((A : ℝ) + 31) ^ (2 * n)
  have hg : Summable (fun m : ℕ => (m : ℝ) ^ (2 * n) * ((2 : ℝ)⁻¹) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (2 * n)
      (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
  have hg1 : Summable (fun k : ℕ => c * (((k : ℝ) + 1) ^ (2 * n) * ((2 : ℝ)⁻¹) ^ (k + 1))) := by
    have := (summable_nat_add_iff 1).2 hg
    refine (this.mul_left c).congr fun k => ?_
    push_cast; ring
  refine Summable.of_nonneg_of_le (fun k => by have := lam_pos A k; positivity) (fun k => ?_) hg1
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  set B : ℝ := ((A : ℝ) + 1) * (k + 1) + 30 with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hBle : B ≤ ((A : ℝ) + 31) * ((k : ℝ) + 1) := by rw [hB]; nlinarith
  have h1 : B ^ C ≤ B ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil C)
  rw [Real.rpow_natCast] at h1
  have h2 : B ^ n ≤ (((A : ℝ) + 31) * ((k : ℝ) + 1)) ^ n :=
    pow_le_pow_left₀ (by linarith) hBle n
  have h3 : (B ^ C) ^ 2 ≤ ((((A : ℝ) + 31) * ((k : ℝ) + 1)) ^ n) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) C) (h1.trans h2) 2
  have e3 : ((((A : ℝ) + 31) * ((k : ℝ) + 1)) ^ n) ^ 2 = c * ((k : ℝ) + 1) ^ (2 * n) := by
    rw [← pow_mul, mul_pow, mul_comm n 2]
  have hlam := lam_le A hA k
  calc lam A k * (B ^ C) ^ 2 ≤ (2 : ℝ)⁻¹ ^ (k + 1) * (c * ((k : ℝ) + 1) ^ (2 * n)) := by
        rw [← e3]
        exact mul_le_mul hlam h3 (by positivity) (by positivity)
    _ = _ := by ring

/-- Eventually `(log log log N)^{2C} ≤ √N`. -/
lemma alt_eventually_small (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, 32 ≤ N ∧
      (Real.log (Real.log (Real.log (N : ℝ))) ^ C) ^ 2 ≤ Real.sqrt N := by
  have ho := (isLittleO_log_rpow_rpow_atTop C (show (0 : ℝ) < 1 / 4 by norm_num)).bound one_pos
  have ho' := tendsto_natCast_atTop_atTop.eventually ho
  filter_upwards [ho', eventually_ge_atTop 32] with N hN h32
  refine ⟨h32, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos := alt_lll_pos N h32
  have hlog := alt_log_gt_three N h32
  have hle := alt_lll_le_log N h32
  simp only [one_mul, Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) C),
    abs_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  have h1 : Real.log (Real.log (Real.log (N : ℝ))) ^ C ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    (Real.rpow_le_rpow hLpos.le hle hC.le).trans hN
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hLpos.le C) h1 2
  refine h2.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
  norm_num

lemma tail_asymp (C : ℝ) (hC : 0 < C) : ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → ∀ E : ℕ → ℕ,
    (∀ k, Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * E k)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30) →
    ∀ C₁ : ℝ, 0 ≤ C₁ → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      Real.sqrt (C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N)) ≤
        K * (1 / (Real.log (Real.log (Real.log N))) ^ C) := by
  refine ⟨1, fun A hA E hE C₁ hC₁ => ?_⟩
  set w : ℕ → ℝ := fun k => lam A k * ((((A : ℝ) + 1) * (k + 1) + 30) ^ C) ^ 2 with hw
  have hws : Summable w := alt_summable_weight A hA C hC
  set W := ∑' k, w k
  have hW0 : 0 ≤ W := tsum_nonneg fun k => by
    have := lam_pos A k; simp only [hw]; positivity
  refine ⟨Real.sqrt (C₁ * (1 + W)), Real.sqrt_nonneg _, ?_⟩
  filter_upwards [alt_eventually_small C hC] with N ⟨hN, hsmall⟩
  set L := Real.log (Real.log (Real.log (N : ℝ))) with hL
  have hLpos : 0 < L := alt_lll_pos N hN
  have hu : 0 < L ^ C := Real.rpow_pos_of_pos hLpos C
  have hu2 : 0 < (L ^ C) ^ 2 := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hlamS := summable_lam A hA
  have hfS : Summable (fun k => lam A k * min 1 ((2 : ℝ) ^ E k / N)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hlamS
    · have := lam_pos A k
      have : 0 ≤ min 1 ((2 : ℝ) ^ E k / N) := le_min zero_le_one (by positivity)
      positivity
    · exact mul_le_of_le_one_right (lam_pos A k).le (min_le_left _ _)
  have hS : ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N) ≤ (1 + W) / (L ^ C) ^ 2 := by
    have hsum := (hlamS.div_const (Real.sqrt N)).add (hws.div_const ((L ^ C) ^ 2))
    calc ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N)
        ≤ ∑' k, (lam A k / Real.sqrt N + w k / (L ^ C) ^ 2) :=
          Summable.tsum_mono hfS hsum fun k => alt_term_bound A C hC (E k) k (hE k) N hN
      _ = (∑' k, lam A k) / Real.sqrt N + W / (L ^ C) ^ 2 := by
          rw [Summable.tsum_add (hlamS.div_const _) (hws.div_const _), tsum_div_const,
            tsum_div_const]
      _ ≤ 1 / Real.sqrt N + W / (L ^ C) ^ 2 := by
          gcongr
          exact tsum_lam_le_one A hA
      _ ≤ 1 / (L ^ C) ^ 2 + W / (L ^ C) ^ 2 := by
          gcongr
      _ = (1 + W) / (L ^ C) ^ 2 := by ring
  calc Real.sqrt (C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N))
      ≤ Real.sqrt (C₁ * ((1 + W) / (L ^ C) ^ 2)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hS hC₁)
    _ = Real.sqrt (C₁ * (1 + W)) * (1 / L ^ C) := by
        rw [← mul_div_assoc, Real.sqrt_div' _ hu2.le, Real.sqrt_sq hu.le, mul_one_div]

end Asm
end Erdos996
