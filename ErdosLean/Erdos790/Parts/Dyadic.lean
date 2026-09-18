import ErdosLean.Erdos790.Defs

/-! Part: basic facts about dyadic indices of positive integers. -/

namespace Erdos790

private lemma toNat_cast {z : ℤ} (hz : 0 < z) : ((z.toNat : ℕ) : ℤ) = z :=
  Int.toNat_of_nonneg hz.le

theorem two_pow_dyIdx_le {z : ℤ} (hz : 0 < z) : (2 : ℤ) ^ dyIdx z ≤ z := by
  have hn : z.toNat ≠ 0 := by omega
  have := Nat.pow_log_le_self 2 hn
  unfold dyIdx
  calc (2 : ℤ) ^ Nat.log 2 z.toNat = ((2 ^ Nat.log 2 z.toNat : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ ((z.toNat : ℕ) : ℤ) := by exact_mod_cast this
    _ = z := toNat_cast hz

theorem lt_two_pow_dyIdx_succ {z : ℤ} (hz : 0 < z) : z < (2 : ℤ) ^ (dyIdx z + 1) := by
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z.toNat
  unfold dyIdx
  calc z = ((z.toNat : ℕ) : ℤ) := (toNat_cast hz).symm
    _ < ((2 ^ (Nat.log 2 z.toNat).succ : ℕ) : ℤ) := by exact_mod_cast this
    _ = (2 : ℤ) ^ (Nat.log 2 z.toNat + 1) := by push_cast; rfl

theorem dyIdx_lt_of_two_mul_lt {z x : ℤ} (hz : 0 < z) (hzx : 2 * z < x) :
    dyIdx z < dyIdx x := by
  have h1 := two_pow_dyIdx_le hz
  have h2 : (2 : ℤ) ^ (dyIdx z + 1) ≤ x := by
    rw [pow_succ]; linarith
  have hx : 0 < x := by linarith
  have h3 : 2 ^ (dyIdx z + 1) ≤ x.toNat := by
    have : ((2 ^ (dyIdx z + 1) : ℕ) : ℤ) ≤ ((x.toNat : ℕ) : ℤ) := by
      rw [toNat_cast hx]; push_cast; exact h2
    exact_mod_cast this
  have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h3
  unfold dyIdx at *
  omega

theorem lt_two_mul_of_dyIdx_eq {z b : ℤ} (hz : 0 < z) (hb : 0 < b) (h : dyIdx b = dyIdx z) :
    b < 2 * z := by
  have h1 := lt_two_pow_dyIdx_succ hb
  have h2 := two_pow_dyIdx_le hz
  rw [h, pow_succ] at h1
  linarith

theorem dyIdx_le_topIdx {A : Finset ℤ} {z : ℤ} (hz : z ∈ A) : dyIdx z ≤ topIdx A :=
  Finset.le_sup (f := dyIdx) hz

end Erdos790
