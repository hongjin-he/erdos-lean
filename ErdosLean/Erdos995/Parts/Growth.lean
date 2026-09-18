import ErdosLean.Erdos995.Parts.Params

/-!
# Erdős 995, part L9 (Growth): `B_k` beats `(log N)^{1/2-ε}` at the end of stage `k`

Ho §7, (7.3)–(7.5). For `N ≤ 21^{S_{k+1}}`:
`log N ≤ S_{k+1} log 21 ≤ 4 S_{k+1}` and `S_{k+1} = ∑_{i ≤ k} T_i ≤ 2^{2 b_k + 3k + 25}`, so
`log N ≤ 2^{E_k}`, `E_k = 2 b_k + 3k + 27`. Hence `(log N)^{1/2-ε} ≤ 2^{E_k (1/2-ε)}` (or `≤ 1`), and
`b_k - E_k(1/2 - ε) = ε E_k - (3k+27)/2 ≥ 16 ε (k+1)² - 2k - 14 → ∞`, which eventually exceeds
`log₂ C`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

lemma bExp_le_succ (k : ℕ) : bExp k ≤ bExp (k + 1) := by
  unfold bExp; have : (k + 1) ^ 2 ≤ (k + 1 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

lemma firstTrial_succ_le (k : ℕ) : firstTrial (k + 1) ≤ 2 ^ (2 * bExp k + 3 * k + 25) := by
  induction k with
  | zero =>
    rw [show firstTrial (0 + 1) = 0 + nTrials 0 from rfl, zero_add]
    unfold nTrials aExp
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  | succ k ih =>
    have e : firstTrial (k + 1 + 1) = firstTrial (k + 1) + nTrials (k + 1) := rfl
    rw [e]
    have hb := bExp_le_succ k
    have h1 : 2 ^ (2 * bExp k + 3 * k + 25) ≤ 2 ^ (2 * bExp (k + 1) + 3 * k + 27) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : nTrials (k + 1) ≤ 2 ^ (2 * bExp (k + 1) + 3 * k + 27) := by
      unfold nTrials aExp
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (2 * bExp (k + 1) + 3 * (k + 1) + 25) =
        2 * 2 ^ (2 * bExp (k + 1) + 3 * k + 27) := by
      rw [← pow_succ', show 2 * bExp (k + 1) + 3 * (k + 1) + 25 = 2 * bExp (k + 1) + 3 * k + 27 + 1 by ring]
    rw [h3]; omega

lemma log_le_aux (S B N : ℕ) (hS : S ≤ 2 ^ B) (hN : N ≤ 21 ^ S) :
    Real.log N ≤ 4 * (2 : ℝ) ^ B := by
  have hl21 : Real.log 21 ≤ 4 := by
    have h1 : Real.log 21 ≤ Real.log (2 ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1; linarith
  have hS' : (S : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast hS
  have hl0 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
  have hF0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ 2 ^ B := by positivity
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN' : (N : ℝ) ≤ (21 : ℝ) ^ S := by exact_mod_cast hN
  have h1 : Real.log N ≤ Real.log ((21 : ℝ) ^ S) := Real.log_le_log hNr hN'
  rw [Real.log_pow] at h1
  nlinarith

lemma log_le_of_le (k N : ℕ) (hN : N ≤ 21 ^ firstTrial (k + 1)) :
    Real.log N ≤ (2 : ℝ) ^ (2 * bExp k + 3 * k + 27) := by
  have h := log_le_aux _ _ N (firstTrial_succ_le k) hN
  have e : (2 : ℝ) ^ (2 * bExp k + 3 * k + 27) = 4 * (2 : ℝ) ^ (2 * bExp k + 3 * k + 25) := by
    rw [show 2 * bExp k + 3 * k + 27 = (2 * bExp k + 3 * k + 25) + 2 by ring, pow_add]; norm_num; ring
  rw [e]; exact h

lemma natCast_le_sig (k : ℕ) : (k : ℝ) ≤ sig k := by
  unfold sig
  have h1 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : (2 : ℝ) ^ k ≤ 2 ^ bExp k :=
    pow_le_pow_right₀ (by norm_num) (by unfold bExp; nlinarith)
  linarith

lemma growth {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, N ≤ 21 ^ firstTrial (k + 1) →
      C * ((N : ℝ) * Real.log N ^ ((1 : ℝ) / 2 - ε)) ≤ sig k * N := by
  set p : ℝ := 1 / 2 - ε with hp_def
  set K : ℝ := max 1 (Real.log 2 ^ p) with hK
  filter_upwards [eventually_ge_atTop ⌈1 / ε⌉₊, eventually_ge_atTop ⌈C⌉₊,
    eventually_ge_atTop ⌈C * K⌉₊] with k hk1 hk2 hk3
  intro N hN
  have hlogE : Real.log N ≤ (2 : ℝ) ^ (2 * bExp k + 3 * k + 27) := log_le_of_le k N hN
  clear hN
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · rw [h0]; simp only [Nat.cast_zero, zero_mul, mul_zero, le_refl]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  suffices h : C * Real.log N ^ p ≤ sig k by
    have := mul_le_mul_of_nonneg_left h hNr.le
    calc C * ((N : ℝ) * Real.log N ^ p) = N * (C * Real.log N ^ p) := by ring
      _ ≤ N * sig k := this
      _ = sig k * N := by ring
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hNpos)
  have hx0 : 0 ≤ Real.log N ^ p := Real.rpow_nonneg hlog0 _
  have hks := natCast_le_sig k
  rcases le_or_gt C 0 with hC | hC
  · have := sig_pos k; nlinarith
  rcases le_or_gt p 0 with hp | hp
  · have hxK : Real.log N ^ p ≤ K := by
      rcases Nat.lt_or_ge N 2 with h2 | h2
      · have : N = 1 := by omega
        subst this; simp only [Nat.cast_one, Real.log_one]
        exact le_trans (Real.zero_rpow_le_one p) (le_max_left _ _)
      · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        exact le_trans (Real.rpow_le_rpow_of_nonpos hl2 this hp) (le_max_right _ _)
    have hk3' : C * K ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk3)
    calc C * Real.log N ^ p ≤ C * K := by gcongr
      _ ≤ k := hk3'
      _ ≤ sig k := hks
  · set E : ℕ := 2 * bExp k + 3 * k + 27 with hE
    have h1 : Real.log N ^ p ≤ ((2 : ℝ) ^ E) ^ p := Real.rpow_le_rpow hlog0 hlogE hp.le
    rw [← Real.rpow_natCast_mul (by norm_num)] at h1
    have hk1' : 1 / ε ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk1)
    have hεk : 1 ≤ ε * k := by
      rw [div_le_iff₀ hε] at hk1'; linarith
    have hCk : C ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk2)
    have hk2pow : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self).le
    have hexp : (E : ℝ) * p + k ≤ (bExp k : ℝ) := by
      rw [hE, hp_def]; unfold bExp; push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hεk (by linarith : (0 : ℝ) ≤ k + 1),
        mul_nonneg hε.le hk0]
    have hsig : sig k = (2 : ℝ) ^ ((bExp k : ℕ) : ℝ) := by unfold sig; rw [Real.rpow_natCast]
    have h3 : (2 : ℝ) ^ ((E : ℝ) * p) * (2 : ℝ) ^ (k : ℝ) ≤ sig k := by
      rw [← Real.rpow_add (by norm_num), hsig]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hpos : 0 ≤ (2 : ℝ) ^ ((E : ℝ) * p) := Real.rpow_nonneg (by norm_num) _
    calc C * Real.log N ^ p ≤ C * (2 : ℝ) ^ ((E : ℝ) * p) := by gcongr
      _ ≤ (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ ((E : ℝ) * p) := by
          gcongr; linarith
      _ ≤ sig k := by linarith

end Con
end Erdos995
