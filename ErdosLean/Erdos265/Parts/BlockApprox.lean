import ErdosLean.Erdos265.Parts.Linearize
import ErdosLean.Erdos265.Parts.Params

/-!
# Erdős #265 — Part L2: one block approximates a whole box (cf. KT v4 Lemma 7.2, `d = 2`)

Let `N = N_k`, `M = M_k` (`M² = N`).  For `n = (n₁, n₂)` the linear part of
`s_k - blockVal k n` is `p(n) = ((n₁ + n₂/4)/N², 2(n₁ + n₂/8)/N³)`.  Given a displacement
`δ` with `|δ₁| ≤ M/(16N²)`, `|δ₂| ≤ M/(16N³)`, put `u = -N² δ₁`, `v = -N³ δ₂/2` and
`n₂ = round (8(u - v))`, `n₁ = round (2v - u)`; then `|n₁|, |n₂| ≤ 3M/4 + 1/2 ≤ M`, the rounding
error of `p(n) + δ` is `≤ (5/8)/N²` resp. `≤ (9/8)/N³`, and by Part L1 the non-linear error is
`≤ (2+2)M²/N³ ≤ 4/N²` resp. `≤ 16 M²/N⁴ ≤ 16/N³`… altogether `≤ 16/N²`, `≤ 16/N³`.
-/

open Filter Topology

namespace Erdos265

lemma block_coord1 {N : ℝ} (hN64 : 64 ≤ N) {a b : ℤ} {x y δ1 : ℝ} (hd : δ1 = -x / N ^ 2)
    (hab : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 ≤ N) (haN : |(a : ℝ)| ≤ N / 8) (hbN : |(b : ℝ)| ≤ N / 8)
    (he1 : |(a : ℝ) - (y - x)| ≤ 1 / 2) (he2 : |(b : ℝ) - (8 * x - 4 * y)| ≤ 1 / 2) :
    |f1 N + f1 (2 * N) + δ1 - (f1 (N + a) + f1 (2 * N + b))| ≤ 16 / N ^ 2 := by
  have hNpos : 0 < N := by linarith
  have he1' := abs_le.mp he1
  have he2' := abs_le.mp he2
  have L1 := lin_f1 hN64 haN
  have L2 := lin_f1_two hN64 hbN
  have key : f1 N + f1 (2 * N) + δ1 - (f1 (N + a) + f1 (2 * N + b)) =
      (f1 N - f1 (N + a) - a / N ^ 2) + (f1 (2 * N) - f1 (2 * N + b) - b / (4 * N ^ 2)) +
      (((a : ℝ) - (y - x)) + ((b : ℝ) - (8 * x - 4 * y)) / 4) / N ^ 2 := by
    rw [hd]
    field_simp
    ring
  rw [key]
  have hr : |(((a : ℝ) - (y - x)) + ((b : ℝ) - (8 * x - 4 * y)) / 4) / N ^ 2|
      ≤ (5 / 8) / N ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < N ^ 2)]
    gcongr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum : 2 * (a : ℝ) ^ 2 / N ^ 3 + 2 * (b : ℝ) ^ 2 / N ^ 3 + (5 / 8) / N ^ 2
      ≤ 16 / N ^ 2 := by
    have e1 : 2 * (a : ℝ) ^ 2 / N ^ 3 + 2 * (b : ℝ) ^ 2 / N ^ 3 + (5 / 8) / N ^ 2
        = (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 + 5 / 8 * N) / N ^ 3 := by
      field_simp
    have e2 : (16 : ℝ) / N ^ 2 = 16 * N / N ^ 3 := by field_simp
    rw [e1, e2]
    gcongr
    linarith
  calc _ ≤ |f1 N - f1 (N + a) - a / N ^ 2| + |f1 (2 * N) - f1 (2 * N + b) - b / (4 * N ^ 2)|
        + |(((a : ℝ) - (y - x)) + ((b : ℝ) - (8 * x - 4 * y)) / 4) / N ^ 2| :=
        abs_add_three _ _ _
    _ ≤ _ := by linarith

lemma block_coord2 {N : ℝ} (hN64 : 64 ≤ N) {a b : ℤ} {x y δ2 : ℝ} (hd : δ2 = -y / N ^ 3)
    (hab : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 ≤ N) (haN : |(a : ℝ)| ≤ N / 8) (hbN : |(b : ℝ)| ≤ N / 8)
    (he1 : |(a : ℝ) - (y - x)| ≤ 1 / 2) (he2 : |(b : ℝ) - (8 * x - 4 * y)| ≤ 1 / 2) :
    |f2 N + f2 (2 * N) + δ2 - (f2 (N + a) + f2 (2 * N + b))| ≤ 16 / N ^ 3 := by
  have hNpos : 0 < N := by linarith
  have he1' := abs_le.mp he1
  have he2' := abs_le.mp he2
  have L1 := lin_f2 hN64 haN
  have L2 := lin_f2_two hN64 hbN
  have key : f2 N + f2 (2 * N) + δ2 - (f2 (N + a) + f2 (2 * N + b)) =
      (f2 N - f2 (N + a) - 2 * a / N ^ 3) + (f2 (2 * N) - f2 (2 * N + b) - b / (4 * N ^ 3)) +
      (2 * ((a : ℝ) - (y - x)) + ((b : ℝ) - (8 * x - 4 * y)) / 4) / N ^ 3 := by
    rw [hd]
    field_simp
    ring
  rw [key]
  have hr : |(2 * ((a : ℝ) - (y - x)) + ((b : ℝ) - (8 * x - 4 * y)) / 4) / N ^ 3|
      ≤ (9 / 8) / N ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < N ^ 3)]
    gcongr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum : 8 * (a : ℝ) ^ 2 / N ^ 4 + 8 * (b : ℝ) ^ 2 / N ^ 4 + (9 / 8) / N ^ 3
      ≤ 16 / N ^ 3 := by
    have e1 : 8 * (a : ℝ) ^ 2 / N ^ 4 + 8 * (b : ℝ) ^ 2 / N ^ 4 + (9 / 8) / N ^ 3
        = (8 * (a : ℝ) ^ 2 + 8 * (b : ℝ) ^ 2 + 9 / 8 * N) / N ^ 4 := by
      field_simp
    have e2 : (16 : ℝ) / N ^ 3 = 16 * N / N ^ 4 := by field_simp
    rw [e1, e2]
    gcongr
    linarith
  calc _ ≤ |f2 N - f2 (N + a) - 2 * a / N ^ 3|
        + |f2 (2 * N) - f2 (2 * N + b) - b / (4 * N ^ 3)|
        + |(2 * ((a : ℝ) - (y - x)) + ((b : ℝ) - (8 * x - 4 * y)) / 4) / N ^ 3| :=
        abs_add_three _ _ _
    _ ≤ _ := by linarith

theorem block_approx (k : ℕ) (δ : ℝ × ℝ) (h1 : |δ.1| ≤ rad1 k) (h2 : |δ.2| ≤ rad2 k) :
    ∃ c : ℤ × ℤ, Adm k c ∧
      |(center k).1 + δ.1 - (blockVal k c).1| ≤ 16 / (NN k : ℝ) ^ 2 ∧
      |(center k).2 + δ.2 - (blockVal k c).2| ≤ 16 / (NN k : ℝ) ^ 3 := by
  obtain ⟨δ1, δ2⟩ := δ
  simp only at h1 h2 ⊢
  set N : ℝ := (NN k : ℝ) with hNdef
  set M : ℝ := (MM k : ℝ) with hMdef
  have hMN : M ^ 2 = N := by
    simp only [hNdef, hMdef]; exact_mod_cast MM_sq k
  have hN64 : (64 : ℝ) ≤ N := by simp only [hNdef]; exact_mod_cast NN_ge k
  have hM0 : 0 ≤ M := by positivity
  have hM8 : 8 ≤ M := by nlinarith
  have hNpos : 0 < N := by linarith
  have hr1 : rad1 k = M / (16 * N ^ 2) := rfl
  have hr2 : rad2 k = M / (16 * N ^ 3) := rfl
  set x : ℝ := -(N ^ 2 * δ1) with hx
  set y : ℝ := -(N ^ 3 * δ2) with hy
  have hxb : |x| ≤ M / 16 := by
    rw [hx, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < N ^ 2)]
    rw [hr1] at h1
    calc N ^ 2 * |δ1| ≤ N ^ 2 * (M / (16 * N ^ 2)) := by gcongr
      _ = M / 16 := by field_simp
  have hyb : |y| ≤ M / 16 := by
    rw [hy, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < N ^ 3)]
    rw [hr2] at h2
    calc N ^ 3 * |δ2| ≤ N ^ 3 * (M / (16 * N ^ 3)) := by gcongr
      _ = M / 16 := by field_simp
  set a : ℤ := round (y - x) with ha
  set b : ℤ := round (8 * x - 4 * y) with hb
  have he1 : |(a : ℝ) - (y - x)| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round _
  have he2 : |(b : ℝ) - (8 * x - 4 * y)| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round _
  have hx' := abs_le.mp hxb
  have hy' := abs_le.mp hyb
  have he1' := abs_le.mp he1
  have he2' := abs_le.mp he2
  have haM : |(a : ℝ)| ≤ M / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hbM : |(b : ℝ)| ≤ 7 * M / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha2 : (a : ℝ) ^ 2 ≤ (M / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) haM 2
  have hb2 : (b : ℝ) ^ 2 ≤ (7 * M / 8) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hbM 2
  have hab : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 ≤ N := by nlinarith
  have haN : |(a : ℝ)| ≤ N / 8 := by nlinarith
  have hbN : |(b : ℝ)| ≤ N / 8 := by nlinarith
  refine ⟨(a, b), ⟨?_, ?_⟩, ?_, ?_⟩
  · have : (|a| : ℝ) ≤ ((MM k : ℤ) : ℝ) := by
      push_cast; rw [← hMdef]; linarith
    exact_mod_cast this
  · have : (|b| : ℝ) ≤ ((MM k : ℤ) : ℝ) := by
      push_cast; rw [← hMdef]; linarith
    exact_mod_cast this
  · have hd : δ1 = -x / N ^ 2 := by rw [hx]; field_simp
    have := block_coord1 hN64 hd hab haN hbN he1 he2
    simpa [center, blockVal, ← hNdef] using this
  · have hd : δ2 = -y / N ^ 3 := by rw [hy]; field_simp
    have := block_coord2 hN64 hd hab haN hbN he1 he2
    simpa [center, blockVal, ← hNdef] using this

end Erdos265
