import ErdosLean.Erdos265.Defs

/-!
# Erdős #265 — Part U1: tails and rational denominators

Basic tail algebra and the integrality of the scaled tails:
if `∑ 1/a_k = p/b` then `b · P n · T n ∈ ℤ` (clear the denominators of the finite prefix
`∑_{k<n} 1/a_k`, whose denominator divides `P n = ∏_{k<n} a_k`), and likewise
`d · Ps n · V n ∈ ℤ`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

theorem two_le_of (ha : IsRationalPair a) (n : ℕ) : 2 ≤ a n :=
  le_trans ha.2.1 (ha.1.monotone (Nat.zero_le n))

theorem tail_eq_add_tail_succ {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    tail f n = f n + tail f (n + 1) := by
  have hs : Summable (fun k => f (k + n)) := (summable_nat_add_iff n).mpr hf
  unfold tail
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  omega

theorem tail_tendsto_zero (f : ℕ → ℝ) : Tendsto (tail f) atTop (𝓝 0) :=
  tendsto_sum_nat_add f

theorem summable_recip (ha : IsRationalPair a) : Summable (recip a) := ha.2.2.1

theorem summable_recipS (ha : IsRationalPair a) : Summable (recipS a) := ha.2.2.2.1

theorem recip_pos (ha : IsRationalPair a) (n : ℕ) : 0 < recip a n := by
  have := two_le_of ha n
  unfold recip
  have : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast this
  positivity

theorem T_pos (ha : IsRationalPair a) (n : ℕ) : 0 < T a n := by
  have hs : Summable (fun k => recip a (k + n)) := (summable_nat_add_iff n).mpr (summable_recip ha)
  exact hs.tsum_pos (fun i => (recip_pos ha _).le) 0 (recip_pos ha _)

theorem T_nonneg (ha : IsRationalPair a) (n : ℕ) : 0 ≤ T a n := (T_pos ha n).le

/-- Generic integrality: if `∑ 1/c_k = q ∈ ℚ` with all `c_k ≥ 1`, then
`q.den · ∏_{k<n} c_k · ∑_{k≥n} 1/c_k ∈ ℤ`. -/
theorem int_scale_aux (c : ℕ → ℕ) (hc : ∀ k, 1 ≤ c k)
    (hs : Summable (fun k => (1 : ℝ) / (c k : ℝ))) (q : ℚ)
    (hq : ∑' k, (1 : ℝ) / (c k : ℝ) = (q : ℝ)) (n : ℕ) :
    ∃ z : ℤ, ((q.den * ∏ k ∈ Finset.range n, c k : ℕ) : ℝ) *
      tail (fun k => (1 : ℝ) / (c k : ℝ)) n = z := by
  refine ⟨(∏ k ∈ Finset.range n, (c k : ℤ)) * q.num -
      (q.den : ℤ) * ∑ k ∈ Finset.range n, ∏ j ∈ (Finset.range n).erase k, (c j : ℤ), ?_⟩
  have htail : tail (fun k => (1 : ℝ) / (c k : ℝ)) n =
      (q : ℝ) - ∑ k ∈ Finset.range n, (1 : ℝ) / (c k : ℝ) := by
    rw [← hq, ← hs.sum_add_tsum_nat_add n]
    unfold tail
    ring
  have hkey : ∀ k ∈ Finset.range n,
      (∏ j ∈ Finset.range n, (c j : ℝ)) * ((1 : ℝ) / (c k : ℝ)) =
        ∏ j ∈ (Finset.range n).erase k, (c j : ℝ) := by
    intro k hk
    rw [← Finset.mul_prod_erase _ _ hk]
    have : (c k : ℝ) ≠ 0 := by
      have := hc k
      have : (1 : ℝ) ≤ (c k : ℝ) := by exact_mod_cast this
      linarith
    field_simp
  have hqn : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    have h := Rat.den_mul_eq_num q
    have : ((q.den * q : ℚ) : ℝ) = ((q.num : ℚ) : ℝ) := by rw [h]
    push_cast at this
    exact this
  rw [htail]
  push_cast
  rw [mul_sub, Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.range n,
      (q.den : ℝ) * (∏ k ∈ Finset.range n, (c k : ℝ)) * ((1 : ℝ) / (c i : ℝ)) =
      (q.den : ℝ) * ∑ i ∈ Finset.range n, ∏ j ∈ (Finset.range n).erase i, (c j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc, hkey i hi]
  rw [hsum]
  rw [← hqn]
  ring

/-- Integrality of the scaled tails. -/
theorem int_scale (ha : IsRationalPair a) :
    ∃ b d : ℕ, 0 < b ∧ 0 < d ∧
      (∀ n, ∃ z : ℤ, ((b * P a n : ℕ) : ℝ) * T a n = z) ∧
      (∀ n, ∃ z : ℤ, ((d * Ps a n : ℕ) : ℝ) * V a n = z) := by
  have h2 := two_le_of ha
  obtain ⟨_, _, hs1, hs2, ⟨q, hq⟩, ⟨r, hr⟩⟩ := ha
  have hcast : ∀ k, (((a k - 1 : ℕ) : ℕ) : ℝ) = (a k : ℝ) - 1 := by
    intro k
    have := h2 k
    rw [Nat.cast_sub (by omega)]
    simp
  refine ⟨q.den, r.den, q.den_pos, r.den_pos, fun n => ?_, fun n => ?_⟩
  · exact int_scale_aux a (fun k => by have := h2 k; omega) hs1 q hq n
  · have hs2' : Summable (fun k => (1 : ℝ) / ((a k - 1 : ℕ) : ℝ)) := by
      simpa only [hcast] using hs2
    have hr' : ∑' k, (1 : ℝ) / ((a k - 1 : ℕ) : ℝ) = (r : ℝ) := by
      simpa only [hcast] using hr
    obtain ⟨z, hz⟩ := int_scale_aux (fun k => a k - 1) (fun k => by have := h2 k; omega)
      hs2' r hr' n
    refine ⟨z, ?_⟩
    rw [← hz]
    unfold V Ps tail recipS
    simp only [hcast]
