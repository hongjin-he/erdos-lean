import ErdosLean.Erdos996.Defs

/-! # Erdős 996: deterministic lower floor of a block (G3). -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Crude spike floor: `φ_d ≥ -t/√(t(1-t))` with `t = 2^{-d}` (valid for all `d`). -/
lemma spike_ge_floor_aux (d : ℕ) (x : 𝕋) :
    -((2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) ≤ spike d x := by
  unfold spike
  rw [← neg_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : 𝕋 → ℝ) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  linarith

/-- The spike floor constant `g` satisfies `g² ≤ 2 · 2^{-d}`. -/
lemma spike_floor_exists (d : ℕ) :
    ∃ g : ℝ, 0 ≤ g ∧ g ^ 2 ≤ 2 * (2 : ℝ)⁻¹ ^ d ∧ ∀ y : 𝕋, -g ≤ spike d y := by
  have ht0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have ht1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨(2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)),
    div_nonneg ht0.le (Real.sqrt_nonneg _), ?_, fun y => spike_ge_floor_aux d y⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · simp
  · have ht2 : (2 : ℝ)⁻¹ ^ d ≤ 1 / 2 := by
      have := pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) hd1
      simpa using this
    have hs : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ^ 2
        = (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) := Real.sq_sqrt (by nlinarith)
    rw [div_pow, hs, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (sq_nonneg ((2 : ℝ)⁻¹ ^ d)) (sub_nonneg.2 ht2)]

/-- Deterministic lower floor `F ≥ -C₃ λ / B` under the depth choice `64 B² L / λ ≤ 2^d`. -/
lemma block_lower_floor (lam B : ℝ) (L d D U : ℕ) (hlam : 0 < lam) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hd : 64 * B ^ 2 * L / lam ≤ 2 ^ d) (x : 𝕋) :
    -(lam / B) ≤ block lam L d D U x := by
  obtain ⟨g, hg0, hg2, hspk⟩ := spike_floor_exists d
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hB0 : 0 < B := by linarith
  have ht0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hsum : -((L : ℝ) * g) ≤
      ∑ q ∈ Finset.Icc 1 L, spike d ((2 ^ (U + q * D) : ℕ) • x) := by
    have h := Finset.sum_le_sum (s := Finset.Icc 1 L)
      (fun q _ => hspk ((2 ^ (U + q * D) : ℕ) • x))
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h
    linarith
  have htd : (2 : ℝ)⁻¹ ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have h1 : 64 * B ^ 2 * L ≤ 2 ^ d * lam := (div_le_iff₀ hlam).1 hd
  have h2 := mul_le_mul_of_nonneg_right h1 ht0.le
  have e : 2 ^ d * lam * (2 : ℝ)⁻¹ ^ d = lam := by linear_combination lam * htd
  have hkey : (L : ℝ) * g ^ 2 * B ^ 2 ≤ lam := by
    have := mul_le_mul_of_nonneg_left hg2 (by positivity : (0 : ℝ) ≤ L * B ^ 2)
    nlinarith
  have hsq : Real.sqrt (lam / L) ^ 2 = lam / L := Real.sq_sqrt (div_nonneg hlam.le hLpos.le)
  have hAB : Real.sqrt (lam / L) * (L * g) * B ≤ lam := by
    apply (pow_le_pow_iff_left₀ (by positivity) hlam.le two_ne_zero).1
    rw [mul_pow, mul_pow, hsq]
    have e2 : lam / L * ((L : ℝ) ^ 2 * g ^ 2) * B ^ 2 = lam * (L * g ^ 2 * B ^ 2) := by
      field_simp
    rw [mul_pow, e2]
    have := mul_le_mul_of_nonneg_left hkey hlam.le
    nlinarith
  have h3 : Real.sqrt (lam / L) * (L * g) ≤ lam / B := (le_div_iff₀ hB0).2 hAB
  have h4 := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg (lam / L))
  unfold block
  linarith

end Erdos996
