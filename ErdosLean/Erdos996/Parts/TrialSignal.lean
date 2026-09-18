import ErdosLean.Erdos996.Defs

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- Pointwise lower bound for the spike. -/
lemma spike_ge_neg (d : ℕ) (y : 𝕋) :
    -((2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ≤ spike d y := by
  unfold spike
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : 𝕋 → ℝ) y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
  linarith

/-- Value of the spike on its support interval. -/
lemma spike_eq_of_mem (d : ℕ) (y : 𝕋)
    (hy : y ∈ QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) :
    spike d y = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
  unfold spike
  rw [Set.indicator_of_mem hy]
  simp

/-- Local amplification: on the good event the trial sum is at least `2 B ℓ`
(the probability bound `≥ c₀ λ / B²` is a consequence of G2). -/
lemma trial_signal (lam B : ℝ) (L ℓ d D U M : ℕ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hB : 100 ≤ B) (hL : 1 ≤ L) (hℓ : 8 * ℓ ≤ L) (hD : d + 2 ≤ D)
    (hd : 64 * B ^ 2 * L / lam ≤ 2 ^ d) (hd' : (2 : ℝ) ^ d < 128 * B ^ 2 * L / lam) (x : 𝕋)
    (hgood : ∃ h ∈ Finset.Icc (ℓ + 1) (L + 1),
      (2 ^ (U + M + h * D) : ℕ) • x ∈ QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) :
    2 * B * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ, block lam L d D U ((2 ^ (M + r * D) : ℕ) • x) := by
  obtain ⟨h, hh, hx⟩ := hgood
  rw [Finset.mem_Icc] at hh
  have hppos : 0 < (2 : ℝ)⁻¹ ^ d := by positivity
  have hp2 : (2 : ℝ)⁻¹ ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hkey : 64 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d ≤ lam := by
    have h0 := (div_le_iff₀ hlam).1 hd
    have h1 := mul_le_mul_of_nonneg_right h0 hppos.le
    calc 64 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d ≤ 2 ^ d * lam * (2 : ℝ)⁻¹ ^ d := h1
      _ = lam := by linear_combination lam * hp2
  have hB2 : (10000 : ℝ) ≤ B ^ 2 := by nlinarith
  have hLp0 : 0 ≤ (L : ℝ) * (2 : ℝ)⁻¹ ^ d := by positivity
  have hLp : (L : ℝ) * (2 : ℝ)⁻¹ ^ d ≤ 1 / 640000 := by
    nlinarith [mul_le_mul_of_nonneg_right hB2 hLp0]
  have hpL : (2 : ℝ)⁻¹ ^ d ≤ (L : ℝ) * (2 : ℝ)⁻¹ ^ d := by nlinarith
  have hp1 : 0 < 1 - (2 : ℝ)⁻¹ ^ d := by linarith
  have hs : 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) :=
    Real.sqrt_pos.2 (mul_pos hppos hp1)
  have hs2 : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ^ 2
      = (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) := Real.sq_sqrt (mul_pos hppos hp1).le
  have ha : 0 ≤ Real.sqrt (lam / L) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (lam / L) ^ 2 * L = lam := by
    rw [Real.sq_sqrt (div_nonneg hlam.le hLpos.le)]; field_simp
  -- the amplification inequality for one block
  have hmain : 2 * B ≤ Real.sqrt (lam / L) *
      ((1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) := by
    rw [← mul_div_assoc, le_div_iff₀ hs]
    by_contra hcon
    push_neg at hcon
    have h0 : 0 ≤ Real.sqrt (lam / L) * (1 - L * (2 : ℝ)⁻¹ ^ d) :=
      mul_nonneg ha (by linarith)
    have h1 := mul_self_lt_mul_self h0 hcon
    have h2 : Real.sqrt (lam / L) ^ 2 * (1 - L * (2 : ℝ)⁻¹ ^ d) ^ 2
        < 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      rw [← hs2]; nlinarith [h1]
    have h3 : lam * (1 - L * (2 : ℝ)⁻¹ ^ d) ^ 2
        < 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) * L := by
      rw [← ha2]; nlinarith [mul_lt_mul_of_pos_right h2 hLpos]
    have h4 : 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) * L
        ≤ 4 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d := by
      have : 0 ≤ B ^ 2 * L * (2 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ d := by positivity
      nlinarith
    have h5 : lam * (L * (2 : ℝ)⁻¹ ^ d) ≤ lam * (1 / 640000) :=
      mul_le_mul_of_nonneg_left hLp hlam.le
    have h6 : 0 ≤ lam * (L * (2 : ℝ)⁻¹ ^ d) ^ 2 := by positivity
    nlinarith
  have hterm : ∀ r ∈ Finset.Icc 1 ℓ,
      2 * B ≤ block lam L d D U ((2 ^ (M + r * D) : ℕ) • x) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    obtain ⟨q, rfl⟩ : ∃ q, h = q + r := ⟨h - r, by omega⟩
    have hq0 : q ∈ Finset.Icc 1 L := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hbig : spike d ((2 ^ (U + q * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
        = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      apply spike_eq_of_mem
      rw [smul_smul, ← pow_add]
      have he : U + q * D + (M + r * D) = U + M + (q + r) * D := by ring
      rw [he]; exact hx
    have hnn : ∀ q' ∈ Finset.Icc 1 L,
        0 ≤ spike d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
          + (2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      intro q' _
      have := spike_ge_neg d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
      rw [neg_div] at this
      linarith
    have hsingle := Finset.single_le_sum hnn hq0
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hbig,
      Nat.add_sub_cancel] at hsingle
    have hsum : (1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
        ≤ ∑ q' ∈ Finset.Icc 1 L,
          spike d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x)) := by
      have hid : (1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
          = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
            + (2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
            - (L : ℝ) * ((2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) := by
        field_simp; ring
      rw [hid]; linarith
    unfold block
    exact hmain.trans (mul_le_mul_of_nonneg_left hsum ha)
  calc 2 * B * (ℓ : ℝ) = ∑ r ∈ Finset.Icc 1 ℓ, 2 * B := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring
    _ ≤ _ := Finset.sum_le_sum hterm

end Erdos996
