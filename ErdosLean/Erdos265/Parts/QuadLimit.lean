import ErdosLean.Erdos265.Defs

/-!
# Erdős #265 — Part U4: quadratic recurrences have a binary-logarithmic limit

Pure real analysis.  If `H n ≥ 1` and eventually `H (n+1) ≤ K H n²`
(`K > 0`), then `(log H n + log K') / 2ⁿ` (`K' = max K 1`) is eventually antitone and bounded
below by `0`, so `log H n / 2ⁿ` converges to some `ℓ ≥ 0`.
-/

open Filter Topology

namespace Erdos265

theorem quad_limit {H : ℕ → ℝ} (h1 : ∀ n, 1 ≤ H n) {K : ℝ} (hK : 0 < K)
    (hrec : ∀ᶠ n in atTop, H (n + 1) ≤ K * H n ^ 2) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ Tendsto (logRatio H) atTop (𝓝 ℓ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hrec
  set C : ℝ := Real.log (max K 1) with hCdef
  have hC : 0 ≤ C := Real.log_nonneg (le_max_right _ _)
  have hlogK : Real.log K ≤ C := Real.log_le_log hK (le_max_left _ _)
  have hHpos : ∀ n, 0 < H n := fun n => lt_of_lt_of_le one_pos (h1 n)
  have hL0 : ∀ n, 0 ≤ Real.log (H n) := fun n => Real.log_nonneg (h1 n)
  set b : ℕ → ℝ := fun n => (Real.log (H n) + C) / (2 : ℝ) ^ n with hbdef
  have hstep : ∀ n, N ≤ n → Real.log (H (n + 1)) ≤ C + 2 * Real.log (H n) := by
    intro n hn
    have h := hN n hn
    have hpos2 : 0 < K * H n ^ 2 := by have := hHpos n; positivity
    calc Real.log (H (n + 1)) ≤ Real.log (K * H n ^ 2) := Real.log_le_log (hHpos _) h
      _ = Real.log K + 2 * Real.log (H n) := by
          rw [Real.log_mul hK.ne' (by have := hHpos n; positivity), Real.log_pow]
          push_cast; ring
      _ ≤ C + 2 * Real.log (H n) := by linarith
  set g : ℕ → ℝ := fun k => b (k + N) with hgdef
  have hanti : Antitone g := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    simp only [hgdef, hbdef]
    have hs := hstep (k + N) (by omega)
    rw [show k + 1 + N = (k + N) + 1 by omega, pow_succ]
    have hp : (0 : ℝ) < 2 ^ (k + N) := by positivity
    rw [div_le_div_iff₀ (by positivity) hp]
    have : (Real.log (H (k + N + 1)) + C) ≤ 2 * (Real.log (H (k + N)) + C) := by linarith
    nlinarith
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    simp only [hgdef, hbdef]
    have := hL0 (k + N)
    positivity
  have hbdd : BddBelow (Set.range g) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hg0 k⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  refine ⟨⨅ i, g i, le_ciInf hg0, ?_⟩
  have hb : Tendsto b atTop (𝓝 (⨅ i, g i)) := (tendsto_add_atTop_iff_nat N).1 hlim
  have hc : Tendsto (fun n : ℕ => C / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have := hb.sub hc
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  simp only [hbdef, logRatio]
  ring

end Erdos265
