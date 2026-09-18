import ErdosLean.Erdos494.Defs
import ErdosLean.Erdos494.Parts.PowerSumsDetermine
import ErdosLean.Erdos494.Parts.KSumPowerSum
import ErdosLean.Erdos494.Parts.Kruyt
import ErdosLean.Erdos494.Parts.TaoNeg
import ErdosLean.Erdos494.Parts.Divisibility
import ErdosLean.Erdos494.Parts.BoundedJ
import ErdosLean.Erdos494.Parts.TwoTermApprox
import ErdosLean.Erdos494.Parts.ExactCase
import ErdosLean.Erdos494.Parts.SmoothGap

/-!
# Erdős Problem 494 (JSP-000399): main theorem

Assembly of [GFS62]:
* algebraic layer (Selfridge–Straus): if `f_s(n,j) ≠ 0` for all `j ≥ 1` then `A_s` and `|A| = n`
  determine all power sums of `A`, hence `A`;
* number-theoretic core `GFSCore`: bounded `j` is trivial; otherwise `f = 0` forces a two-term
  near-equality between `P`-smooth numbers (`two_term_approx` + `gfs_dvd`), which the
  Ridout-type gap theorem `smooth_gap` turns into an exact equality, excluded by `exact_case`.
-/

open Filter

namespace Erdos494

/-- Every prime factor of `(s-1)! * s^(j-1)` is `≤ s`. -/
private lemma smooth_of_dvd_factorial_mul_pow {s j m : ℕ}
    (h : m ∣ (s - 1).factorial * s ^ (j - 1)) (hs : 1 ≤ s) :
    m ∈ Nat.smoothNumbers (s + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpm
  have hpd := dvd_trans hpm h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.Prime.dvd_factorial hp).1 h1
    omega
  · have := Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow h1)
    omega

private lemma smooth_pow_of_le {s i e : ℕ} (hi0 : 0 < i) (his : i ≤ s) :
    i ^ e ∈ Nat.smoothNumbers (s + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpm
  have := Nat.le_of_dvd hi0 (hp.dvd_of_dvd_pow hpm)
  omega

/-- The number-theoretic core of [GFS62] §4. -/
theorem gfs_core : GFSCore := by
  intro s hs
  have hs3 : 3 ≤ s := hs
  obtain ⟨δ, hδ0, -, J0, hTT⟩ := two_term_approx s hs3
  obtain ⟨N1, hBJ⟩ := bounded_j s (by omega) J0
  obtain ⟨N2, hEx⟩ := exact_case s hs3
  obtain ⟨X0, hSG⟩ := smooth_gap (s + 1) δ hδ0
  rw [Filter.eventually_atTop]
  refine ⟨N1 + N2 + 2 * X0 + s + 1, fun n hn j hj hf => ?_⟩
  by_cases hjJ : j < J0
  · exact hBJ n j (by omega) hjJ hf
  replace hjJ := not_lt.1 hjJ
  obtain ⟨i, hi, happrox, hn2⟩ := hTT n j (by omega) hjJ hf
  have hi' := Finset.mem_Icc.1 hi
  have hdvd := gfs_dvd s n j (by omega) (by omega) hf
  have hnsm : n ∈ Nat.smoothNumbers (s + 1) :=
    smooth_of_dvd_factorial_mul_pow hdvd (by omega)
  have hx : n * i ^ (j - 1) ∈ Nat.smoothNumbers (s + 1) :=
    Nat.mul_mem_smoothNumbers hnsm (smooth_pow_of_le (by omega) (by omega))
  have hsi : s - i ∈ Nat.smoothNumbers (s + 1) := by
    simpa using smooth_pow_of_le (s := s) (i := s - i) (e := 1) (by omega) (by omega)
  have hy : (s - i) * (i + 1) ^ (j - 1) ∈ Nat.smoothNumbers (s + 1) :=
    Nat.mul_mem_smoothNumbers hsi (smooth_pow_of_le (by omega) (by omega))
  have hy0 : X0 < (s - i) * (i + 1) ^ (j - 1) := by omega
  have heq := hSG _ _ hx hy hy0 happrox
  exact hEx n j i (by omega) hj hi heq hf

/-- Selfridge–Straus: nonvanishing of `f_s(n, ·)` gives uniqueness for `|A| = n`. -/
theorem unique_of_gfsPoly_ne_zero (s n : ℕ) (hcore : ∀ j, 1 ≤ j → gfsPoly s n j ≠ 0) :
    Erdos494Unique s n := by
  intro A B hA hB hAB
  have hall : ∀ j, 1 ≤ j → psum A j = psum B j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hlow : ∀ l, 1 ≤ l → l < j → psum A l = psum B l := fun l hl hlj => ih l hlj hl
      have key := ksum_power_sum A B n s j hA hB hj hlow
      have hk : ksumPsum A s j = ksumPsum B s j := by simp [ksumPsum, hAB]
      rw [hk, sub_self] at key
      have hne : (gfsPoly s n j : ℂ) ≠ 0 := by exact_mod_cast hcore j hj
      exact sub_eq_zero.1 ((mul_eq_zero.1 key.symm).resolve_left hne)
  exact power_sums_determine A B n hA hB fun j hj _ => hall j hj

/-- Gordon–Fraenkel–Straus [GFS62]: `erdos_494.variants.gordon_fraenkel_straus`. -/
theorem gordon_fraenkel_straus : GFSStatement := by
  intro k hk
  filter_upwards [gfs_core k hk] with n hn
  exact unique_of_gfsPoly_ne_zero k n hn

/-- The complete answer to Erdős #494 / JSP-000399. -/
theorem erdos_494 : Erdos494Full :=
  ⟨kruyt_counterexample, tao_counterexample, gordon_fraenkel_straus⟩

end Erdos494
