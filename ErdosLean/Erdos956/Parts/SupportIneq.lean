import ErdosLean.Erdos956.Parts.SqrtBounds

/-!
# Erdős #956 — Part 3: the support inequality (note, Lemma 2, inequality (6))

For `s, t ≥ 0`, `⟨p(s), (t,1)⟩ ≤ ⟨p(t), (t,1)⟩` (the positive factor `1/r(t)` of `ν(t)` is
dropped).  Equivalently `r_t - (1+st)/r_s ≤ (t-s)²/2`, which follows from
`r_s r_t - 1 - st = (s-t)²/(r_s r_t + 1 + st)` and `r_s (r_s r_t + 1 + st) ≥ 2`.

-/

namespace Erdos956

lemma support_gen {e s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    pp e s 0 * t + pp e s 1 ≤ pp e t 0 * t + pp e t 1 := by
  simp only [pp_zero, pp_one]
  have hx2 := rr_sq s
  have hy2 := rr_sq t
  have hx1 := one_le_rr s
  have hy1 := one_le_rr t
  set x := rr s with hx
  set y := rr t with hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  have hxy : 1 ≤ x * y := by nlinarith
  set Q := x * y + 1 + s * t with hQ
  have hQ0 : 0 < Q := by linarith
  have hkey : (x * y - 1 - s * t) * Q = (s - t) ^ 2 := by
    have : (x * y) ^ 2 = (1 + s ^ 2) * (1 + t ^ 2) := by rw [mul_pow, hx2, hy2]
    rw [hQ]; nlinarith [this]
  have hD : 0 ≤ x * y - 1 - s * t := by
    by_contra h
    rw [not_le] at h
    nlinarith [sq_nonneg (s - t), mul_neg_of_neg_of_pos h hQ0]
  have hxQ : 2 ≤ x * Q := by rw [hQ]; nlinarith
  -- r_s r_t - 1 - s t ≤ r_s (t - s)² / 2
  have hmain : 2 * (x * y - 1 - s * t) ≤ x * (s - t) ^ 2 := by
    rw [← hkey]; nlinarith [mul_le_mul_of_nonneg_left hxQ hD]
  have hyt : t ^ 2 / y + 1 / y = y := by
    field_simp; linarith [hy2]
  have h1 : s / x * t + 1 / x = (1 + s * t) / x := by field_simp; ring
  have h2 : t / y * t + 1 / y = y := by
    have : t / y * t + 1 / y = t ^ 2 / y + 1 / y := by ring
    rw [this, hyt]
  have he : (1 + s * t) / x = y - (x * y - 1 - s * t) / x := by field_simp; ring
  have hd : (x * y - 1 - s * t) / x ≤ (t - s) ^ 2 / 2 := by
    rw [div_le_iff₀ hx0]; nlinarith [hmain]
  have hfin : y - (1 + s * t) / x ≤ (t - s) ^ 2 / 2 := by rw [he]; linarith
  nlinarith [h1, h2, hfin]

end Erdos956
