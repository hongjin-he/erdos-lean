import ErdosLean.Erdos790.Defs

/-! Part: membership in, and size of, the dyadic window of a distance `δ`. -/

namespace Erdos790

/-- If `z ∈ A` is positive and `δ ≤ 2 N z`, `z ≤ 2δ`, then `dyIdx z` lies in the window. -/
theorem mem_window_of (A : Finset ℤ) (N : ℕ) {z δ : ℤ} (hzA : z ∈ A) (hz : 0 < z)
    (h1 : δ ≤ 2 * (N : ℤ) * z) (h2 : z ≤ 2 * δ) : dyIdx z ∈ window N δ (topIdx A) := by
  unfold window
  rw [Finset.mem_filter, Finset.mem_range]
  have hle : dyIdx z ≤ topIdx A := Finset.le_sup (f := dyIdx) hzA
  have hzn : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz.le
  have hne : z.toNat ≠ 0 := by omega
  have hlo : 2 ^ dyIdx z ≤ z.toNat := Nat.pow_log_le_self 2 hne
  have hhi : z.toNat < 2 ^ (dyIdx z + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlo' : (2 : ℤ) ^ dyIdx z ≤ z := by rw [← hzn]; exact_mod_cast hlo
  have hhi' : z < (2 : ℤ) ^ (dyIdx z + 1) := by rw [← hzn]; exact_mod_cast hhi
  refine ⟨by omega, ?_, by linarith⟩
  have : 2 * (N : ℤ) * z ≤ 2 * (N : ℤ) * 2 ^ (dyIdx z + 1) :=
    mul_le_mul_of_nonneg_left hhi'.le (by positivity)
  linarith

/-- A window contains at most `⌈log₂ N⌉ + 5` indices. -/
theorem card_window_le (N : ℕ) (hN : 1 ≤ N) (δ : ℤ) (M : ℕ) :
    (window N δ M).card ≤ Nat.clog 2 N + 5 := by
  rcases (window N δ M).eq_empty_or_nonempty with h | h
  · simp [h]
  set a := (window N δ M).min' h
  have ha := Finset.min'_mem _ h
  have haw : δ ≤ 2 * (N : ℤ) * 2 ^ (a + 1) := by
    have := ha; unfold window at this; rw [Finset.mem_filter] at this; exact this.2.1
  have hNc : (N : ℤ) ≤ 2 ^ Nat.clog 2 N := by exact_mod_cast Nat.le_pow_clog (by norm_num) N
  have hsub : window N δ M ⊆ Finset.Icc a (a + Nat.clog 2 N + 3) := by
    intro j hj
    have hmin : a ≤ j := Finset.min'_le _ _ hj
    have hj' := hj
    unfold window at hj'; rw [Finset.mem_filter] at hj'
    have h2 : (2 : ℤ) ^ j ≤ 2 * δ := hj'.2.2
    have key : (2 : ℤ) ^ j ≤ 2 ^ (a + Nat.clog 2 N + 3) := by
      have e : (2 : ℤ) ^ (a + Nat.clog 2 N + 3) = 4 * 2 ^ Nat.clog 2 N * 2 ^ (a + 1) := by
        ring
      have hp : (0 : ℤ) ≤ 2 ^ (a + 1) := by positivity
      have : 2 * (2 * (N : ℤ) * 2 ^ (a + 1)) ≤ 4 * 2 ^ Nat.clog 2 N * 2 ^ (a + 1) := by
        nlinarith
      linarith
    have : j ≤ a + Nat.clog 2 N + 3 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 key
    exact Finset.mem_Icc.2 ⟨hmin, this⟩
  calc (window N δ M).card ≤ (Finset.Icc a (a + Nat.clog 2 N + 3)).card := Finset.card_le_card hsub
    _ = Nat.clog 2 N + 4 := by simp; omega
    _ ≤ _ := by omega

end Erdos790
