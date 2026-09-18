import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part B4: the exact case `n i^{j-1} = (s-i)(i+1)^{j-1}` ([GFS62] end of §4).

`gcd(i, i+1) = 1` forces `i^{j-1} ∣ s - i`; for `i ≥ 2` this bounds `j`, hence `n`.  For `i = 1`
we get `n = (s-1) 2^{j-1}`; then `T_1 - T_2 = -(s-2)/(s-1) · C(n, s-2)` while
`T_3 = 3^{j-1} C(n, s-3)` is larger by a factor `≍ (3/2)^{j}`, and `T_4, …, T_s` are smaller than
`T_3` by a factor `≍ (2/3)^{j}`; so `f ≠ 0` for large `j` (needs `s ≥ 3`: for `s = 2` this is
the genuine infinite family `n = 2^{j-1}`). -/

namespace Erdos494

/-- `C(n,k) (n-s)^t ≤ s^t C(n,k+t)` whenever `k + t ≤ s`. -/
lemma exactCase_choose_mul_pow_le (n s : ℕ) :
    ∀ t k, k + t ≤ s → n.choose k * (n - s) ^ t ≤ s ^ t * n.choose (k + t) := by
  intro t
  induction t with
  | zero => intro k _; simp
  | succ t ih =>
    intro k hk
    have h1 := Nat.choose_succ_right_eq n k
    have h2 : n - s ≤ n - k := by omega
    have h3 := ih (k + 1) (by omega)
    calc n.choose k * (n - s) ^ (t + 1) = n.choose k * (n - s) * (n - s) ^ t := by ring
      _ ≤ n.choose k * (n - k) * (n - s) ^ t := by gcongr
      _ = n.choose (k + 1) * (k + 1) * (n - s) ^ t := by rw [h1]
      _ ≤ n.choose (k + 1) * s * (n - s) ^ t := by gcongr; omega
      _ = s * (n.choose (k + 1) * (n - s) ^ t) := by ring
      _ ≤ s * (s ^ t * n.choose (k + 1 + t)) := by gcongr
      _ = s ^ (t + 1) * n.choose (k + (t + 1)) := by
          rw [show k + 1 + t = k + (t + 1) by omega]; ring

lemma exactCase_le_two_pow (i : ℕ) (hi : 4 ≤ i) : i ≤ 2 ^ (i - 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = t + 4 := ⟨i - 4, by omega⟩
  have h : t < 2 ^ t := Nat.lt_two_pow_self
  rw [show t + 4 - 2 = t + 2 by omega, pow_add]
  norm_num
  omega

/-- For `4 ≤ i ≤ s` and `2^m ≤ n - s`: `i^m C(n, s-i) ≤ 2^m s^s C(n, s-3)`. -/
lemma exactCase_term_le (s n m i : ℕ) (hi4 : 4 ≤ i) (his : i ≤ s) (hn : 2 ^ m ≤ n - s) :
    i ^ m * n.choose (s - i) ≤ 2 ^ m * s ^ s * n.choose (s - 3) := by
  have key := exactCase_choose_mul_pow_le n s (i - 3) (s - i) (by omega)
  rw [show s - i + (i - 3) = s - 3 by omega] at key
  have hpow : i ^ m ≤ 2 ^ m * (2 ^ m) ^ (i - 3) := by
    calc i ^ m ≤ (2 ^ (i - 2)) ^ m := Nat.pow_le_pow_left (exactCase_le_two_pow i hi4) m
      _ = 2 ^ m * (2 ^ m) ^ (i - 3) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1
          rw [show i - 2 = (i - 3) + 1 by omega]; ring
  have hst : s ^ (i - 3) ≤ s ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  calc i ^ m * n.choose (s - i) ≤ 2 ^ m * (2 ^ m) ^ (i - 3) * n.choose (s - i) := by gcongr
    _ = 2 ^ m * (n.choose (s - i) * (2 ^ m) ^ (i - 3)) := by ring
    _ ≤ 2 ^ m * (n.choose (s - i) * (n - s) ^ (i - 3)) := by gcongr
    _ ≤ 2 ^ m * (s ^ (i - 3) * n.choose (s - 3)) := by gcongr
    _ ≤ 2 ^ m * (s ^ s * n.choose (s - 3)) := by gcongr
    _ = 2 ^ m * s ^ s * n.choose (s - 3) := by ring

/-- `2^m (m+2) ≤ 2 · 3^m`. -/
lemma exactCase_bernoulli (m : ℕ) : 2 ^ m * (m + 2) ≤ 2 * 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (2 ^ m), Nat.zero_le m]

/-- The case `i = 1`, with `s = r + 3`: `n = (r+2) 2^m` and `f > 0` for `m` large. -/
lemma exactCase_one' (r m n : ℕ) (hm : 2 ≤ m) (hn : n = (r + 2) * 2 ^ m)
    (hK : 2 ^ m * (1 + (r + 3) ^ (r + 3 + 1)) < 3 ^ m) :
    0 < gfsPoly (r + 3) n (m + 1) := by
  have h2m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hns : 2 ^ m ≤ n - (r + 3) := by
    have : (r + 2) * 2 ^ m = (r + 1) * 2 ^ m + 2 ^ m := by ring
    have h4 : (r + 1) * 4 ≤ (r + 1) * 2 ^ m := Nat.mul_le_mul_left _ h2m
    omega
  have hnr : r + 2 ≤ n := by
    have : (r + 2) * 1 ≤ (r + 2) * 2 ^ m := Nat.mul_le_mul_left _ (by omega)
    omega
  have hf : gfsPoly (r + 3) n (m + 1) = ∑ i ∈ Finset.Icc 1 (r + 3),
      (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ) := by
    simp [gfsPoly]
  have hsplit : ∑ i ∈ Finset.Icc 1 (r + 3),
      (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ) =
      ((n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ) + 3 ^ m * (n.choose r : ℤ)) +
      ∑ i ∈ Finset.Ico 4 (r + 4), (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ) := by
    have e : Finset.Icc 1 (r + 3) = Finset.Ico 1 (r + 4) := by
      ext x; simp [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, ← Finset.sum_Ico_consecutive _ (show 1 ≤ 4 by norm_num) (show 4 ≤ r + 4 by omega)]
    congr 1
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.sum_Ico_succ_top (by norm_num),
      Finset.sum_Ico_succ_top (by norm_num)]
    simp only [Finset.Ico_self, Finset.sum_empty]
    rw [show r + 3 - 1 = r + 2 by omega, show r + 3 - 2 = r + 1 by omega,
      show r + 3 - 3 = r by omega]
    norm_num
    ring
  have hcpos : 0 < n.choose r := Nat.choose_pos (by omega)
  -- remainder bound
  have hR : |∑ i ∈ Finset.Ico 4 (r + 4), (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ)|
      ≤ (r : ℤ) * (2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * (n.choose r : ℤ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.Ico 4 (r + 4),
        |(-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ)|
          ≤ ((2 ^ m * (r + 3) ^ (r + 3) * n.choose r : ℕ) : ℤ) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have := exactCase_term_le (r + 3) n m i hi.1 (by omega) hns
      rw [show r + 3 - 3 = r by omega] at this
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      exact_mod_cast this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show r + 4 - 4 = r by omega]
    push_cast
    exact le_refl _
  have hA := Nat.choose_succ_right_eq n (r + 1)
  have hB := Nat.choose_succ_right_eq n r
  have hAz : (n.choose (r + 2) : ℤ) * (r + 2) = (n.choose (r + 1) : ℤ) * ((n : ℤ) - (r + 1)) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hA
    push_cast [Nat.cast_sub (show r + 1 ≤ n by omega)] at this
    rw [show r + 1 + 1 = r + 2 by omega] at this
    linarith
  have hBz : (n.choose (r + 1) : ℤ) * (r + 1) = (n.choose r : ℤ) * ((n : ℤ) - r) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hB
    push_cast [Nat.cast_sub (show r ≤ n by omega)] at this
    linarith
  have hnz : (n : ℤ) = (r + 2) * 2 ^ m := by
    rw [hn]; push_cast; ring
  have hkey : ((r : ℤ) + 2) * ((n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ)
      + 2 ^ m * (n.choose r : ℤ)) = (n.choose r : ℤ) * r := by
    linear_combination hAz - hBz + ((n.choose (r + 1) : ℤ) - (n.choose r : ℤ)) * hnz
  have hfirst : (0 : ℤ) ≤ (n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ)
      + 2 ^ m * (n.choose r : ℤ) := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 : ((r : ℤ) + 2) * ((n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ)
      + 2 ^ m * (n.choose r : ℤ)) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    have h2 : (0 : ℤ) ≤ (n.choose r : ℤ) * r := by positivity
    linarith
  rw [hf, hsplit]
  have hR' := neg_abs_le (∑ i ∈ Finset.Ico 4 (r + 4),
    (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ))
  have hKz : (2 : ℤ) ^ m * (1 + ((r : ℤ) + 3) ^ (r + 3 + 1)) + 1 ≤ 3 ^ m := by
    exact_mod_cast hK
  have hcz : (1 : ℤ) ≤ n.choose r := by exact_mod_cast hcpos
  have hss : (r : ℤ) * (2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * n.choose r)
      ≤ 2 ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) * n.choose r := by
    have h0 : (0 : ℤ) ≤ 2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * n.choose r := by positivity
    have : (2 : ℤ) ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) * n.choose r
        = ((r : ℤ) + 3) * (2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * n.choose r) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) h0
  set X : ℤ := (2 : ℤ) ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) with hX
  set C : ℤ := (n.choose r : ℤ) with hC
  have hD : (0 : ℤ) ≤ (3 ^ m - (2 ^ m + X + 1)) * (C - 1) :=
    mul_nonneg (by nlinarith) (by linarith)
  have hX' : 2 ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) * C = X * C := by rw [hX]
  nlinarith

lemma exactCase_one (s m : ℕ) (hs : 3 ≤ s) (hm : 2 ≤ m)
    (hK : 2 ^ m * (1 + s ^ (s + 1)) < 3 ^ m) :
    0 < gfsPoly s ((s - 1) * 2 ^ m) (m + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 3 := ⟨s - 3, by omega⟩
  exact exactCase_one' r m _ hm (by rw [show r + 3 - 1 = r + 2 by omega]) hK

theorem exact_case (s : ℕ) (hs : 3 ≤ s) :
    ∃ N : ℕ, ∀ n j i : ℕ, N ≤ n → 1 ≤ j → i ∈ Finset.Icc 1 (s - 1) →
      n * i ^ (j - 1) = (s - i) * (i + 1) ^ (j - 1) → gfsPoly s n j ≠ 0 := by
  set K := 1 + s ^ (s + 1) with hKdef
  set M := 2 * K + 2 with hM
  refine ⟨s ^ (s + 1) + (s - 1) * 2 ^ M + 1, ?_⟩
  intro n j i hN hj hi heq
  rw [Finset.mem_Icc] at hi
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at heq
  rcases Nat.lt_or_ge i 2 with hi1 | hi2
  · -- i = 1
    have hi1' : i = 1 := by omega
    subst hi1'
    simp only [one_pow, mul_one] at heq
    norm_num at heq
    subst heq
    have hmM : M ≤ m := by
      by_contra hlt
      rw [not_le] at hlt
      have : 2 ^ m ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hlt.le
      have : (s - 1) * 2 ^ m ≤ (s - 1) * 2 ^ M := Nat.mul_le_mul_left _ this
      omega
    have hb := exactCase_bernoulli m
    have hK : 2 ^ m * (1 + s ^ (s + 1)) < 3 ^ m := by
      rw [← hKdef]
      have : 2 ^ m * (2 * K) < 2 ^ m * (m + 2) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
      nlinarith
    exact (exactCase_one s m hs (by omega) hK).ne'
  · -- i ≥ 2: impossible for large n
    exfalso
    have hcop : Nat.Coprime (i ^ m) ((i + 1) ^ m) :=
      Nat.Coprime.pow m m (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _))
    have hdvd : i ^ m ∣ (s - i) * (i + 1) ^ m := ⟨n, by rw [← heq]; ring⟩
    have hd := hcop.dvd_of_dvd_mul_right hdvd
    have hle : i ^ m ≤ s - i := Nat.le_of_dvd (by omega) hd
    have h2i : 2 ^ m ≤ i ^ m := Nat.pow_le_pow_left hi2 m
    have hms : m < s := by
      have : m < 2 ^ m := Nat.lt_two_pow_self
      omega
    have hip : 1 ≤ i ^ m := Nat.one_le_pow _ _ (by omega)
    have h1 : n ≤ n * i ^ m := Nat.le_mul_of_pos_right n hip
    have h2 : (s - i) * (i + 1) ^ m ≤ s * s ^ s := by
      apply Nat.mul_le_mul (by omega)
      calc (i + 1) ^ m ≤ s ^ m := Nat.pow_le_pow_left (by omega) m
        _ ≤ s ^ s := Nat.pow_le_pow_right (by omega) hms.le
    have h3 : s * s ^ s = s ^ (s + 1) := by ring
    omega

end Erdos494
