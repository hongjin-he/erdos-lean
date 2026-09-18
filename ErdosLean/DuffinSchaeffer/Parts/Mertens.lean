import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 5: Mertens-type upper bounds

Only *upper* bounds for `∑ 1/p` over ranges of primes are needed
(KM §5, Lemma 7.3, Lemma 8.4, and the sieve), plus both directions of Mertens' first theorem
`∑_{p ≤ x} log p / p = log x + O(1)` (Legendre + `log n! = n log n + O(n)` + Chebyshev
`θ(x) ≤ x log 4`, which is `Chebyshev.theta_le_log4_mul_x`).
-/

open Real Finset

namespace DuffinSchaeffer

namespace MertensAux

lemma Iic_eq_range' (n : ℕ) : Iic n = range (n + 1) := by
  ext m; simp

lemma sum_primes_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ (Iic (n + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (Iic n).filter Nat.Prime, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [Iic_eq_range', Iic_eq_range', sum_filter, sum_filter, sum_range_succ]

lemma sum_primes_Ioc_succ (f : ℕ → ℝ) {M n : ℕ} (h : M ≤ n) :
    ∑ p ∈ (Ioc M (n + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (Ioc M n).filter Nat.Prime, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [sum_filter, sum_filter, sum_Ioc_succ_top h]

lemma theta_le (n : ℕ) : ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h1 : (Iic n).filter Nat.Prime = Nat.primesLE n := by
    rw [Nat.primesLE_eq_filter_range, Iic_eq_range']
  rw [h1, ← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)

lemma log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ p ∈ (Iic n).filter Nat.Prime,
      ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact mem_filter.2 ⟨mem_Iic.2 ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
  · intro p _; simp

lemma div_le_factorization (n p : ℕ) (hp : p.Prime) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p n))]
  rcases Nat.lt_or_ge n p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p n + 1) := by
      have := Nat.log_pos hp.one_lt h
      simp only [mem_Ico, le_refl, true_and]
      omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

lemma factorization_le_div (n p : ℕ) (hp : p.Prime) :
    ((n.factorial.factorization p : ℕ) : ℝ) ≤ n / ((p : ℝ) - 1) := by
  have h := Nat.sub_one_mul_factorization_factorial hp (n := n)
  have h' : (p - 1) * n.factorial.factorization p ≤ n := by rw [h]; exact Nat.sub_le _ _
  have hc : (((p - 1) * n.factorial.factorization p : ℕ) : ℝ) ≤ n := by exact_mod_cast h'
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hc
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma log_succ_sub_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
  rw [Real.log_div (by positivity) hn'.ne'] at this
  have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  linarith

lemma sum_log_div_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 2 n, Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤
      1 + Real.log 2 - (Real.log ((n : ℝ) + 1) + 1) / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num; linarith
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e0 : ((n : ℝ) + 1 - 1) = n := by ring
    rw [e0]
    set a := Real.log ((n : ℝ) + 1)
    set b := Real.log ((n : ℝ) + 1 + 1)
    have hk : b - a ≤ 1 / ((n : ℝ) + 1) := by
      have := log_succ_sub_log_le (n + 1) (by omega)
      push_cast at this
      exact this
    have hk2 : (n : ℝ) * (b - a) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hk hn'.le
      have h2 : (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      linarith
    have e : (a + 1) / n - (b + 1) / ((n : ℝ) + 1) - a / (((n : ℝ) + 1) * n) =
        (1 - n * (b - a)) / (((n : ℝ) + 1) * n) := by
      field_simp; ring
    have hnn : 0 ≤ (1 - n * (b - a)) / (((n : ℝ) + 1) * n) :=
      div_nonneg (by linarith) (by positivity)
    linarith

lemma sum_inv_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 2 n, 1 / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e0 : ((n : ℝ) + 1 - 1) = n := by ring
    rw [e0]
    have e : 1 - 1 / (n : ℝ) + 1 / (((n : ℝ) + 1) * n) = 1 - 1 / ((n : ℝ) + 1) := by
      field_simp; ring
    linarith

lemma log_four_lt_two : Real.log 4 < 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

end MertensAux

open MertensAux

/-- Mertens' first theorem, upper bound. -/
theorem sum_log_prime_div_le (x : ℝ) (hx : 1 ≤ x) :
    ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + 2 := by
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have key : (n : ℝ) * ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p ≤
      Real.log (n.factorial : ℝ) + ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p := by
    rw [log_factorial_eq, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h1 : (n : ℝ) < p * (((n / p : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ n hpp.pos
    have h2 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      exact_mod_cast div_le_factorization n p hpp
    have h3 : (n : ℝ) / p ≤ ((n.factorial.factorization p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]; nlinarith
    calc (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
      _ ≤ (((n.factorial.factorization p : ℕ) : ℝ) + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right h3 hlog
      _ = _ := by ring
  have hfac : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    exact_mod_cast Nat.factorial_le_pow n
  have hθ := theta_le n
  have hlogn : Real.log n ≤ Real.log x := Real.log_le_log hnpos hnx
  have h4 := log_four_lt_two
  by_contra hcon
  replace hcon := not_le.mp hcon
  have : (n : ℝ) * (Real.log n + 2) < n * ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p :=
    mul_lt_mul_of_pos_left (by linarith) hnpos
  nlinarith

/-- Mertens' first theorem, lower bound. -/
theorem sum_log_prime_div_ge (x : ℝ) (hx : 1 ≤ x) :
    Real.log x - 3 ≤ ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p := by
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set S := ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p with hS
  set B := ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) with hB
  have key : Real.log (n.factorial : ℝ) ≤ n * (S + B) := by
    rw [log_factorial_eq, hS, hB, ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hv := factorization_le_div n p hpp
    have e : (n : ℝ) * (Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) =
        (n / ((p : ℝ) - 1)) * Real.log p := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hv hlog
  have hBle : B ≤ 2 - 1 / n := by
    have hsub : (Iic n).filter Nat.Prime ⊆ Icc 2 n := by
      intro p hp
      simp only [mem_filter, mem_Iic] at hp
      simp only [mem_Icc]
      exact ⟨hp.2.two_le, hp.1⟩
    have h1 : B ≤ ∑ m ∈ Icc 2 n, Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro m hm _
      simp only [mem_Icc] at hm
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
      apply div_nonneg (Real.log_nonneg (by linarith))
      apply mul_nonneg <;> linarith
    have h2 := sum_log_div_Icc n hn1
    have h3 : 1 / (n : ℝ) ≤ (Real.log ((n : ℝ) + 1) + 1) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      linarith
    have h4 := Real.log_two_lt_d9
    linarith
  have hlow : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hnpos.le n
    have hpos : (0 : ℝ) < (n : ℝ) ^ n / (n.factorial : ℝ) := by
      have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      positivity
    have := Real.log_le_log hpos h
    rw [Real.log_exp, Real.log_div (by positivity) (by exact_mod_cast (Nat.factorial_ne_zero n)),
      Real.log_pow] at this
    linarith
  have hSn : Real.log n - 3 + 1 / n ≤ S := by
    have h5 : (n : ℝ) * Real.log n - 3 * n + 1 ≤ n * S := by
      have : (n : ℝ) * (S + B) ≤ n * (S + (2 - 1 / n)) :=
        mul_le_mul_of_nonneg_left (by linarith) hnpos.le
      have e : (n : ℝ) * (S + (2 - 1 / n)) = n * S + 2 * n - 1 := by field_simp; ring
      linarith
    have e : Real.log n - 3 + 1 / n = ((n : ℝ) * Real.log n - 3 * n + 1) / n := by
      field_simp
    rw [e, div_le_iff₀ hnpos]
    linarith
  have hlx : Real.log x ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) hxn.le
  have := log_succ_sub_log_le n hn1
  linarith

/-- Mertens' second theorem in the form of an upper bound on a range:
`∑_{y < p ≤ x} 1/p ≤ log(log x / log y) + 100 / log y` for `2 ≤ y ≤ x`. -/
theorem sum_inv_prime_Ioc_le (y x : ℝ) (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log x / Real.log y) + 100 / Real.log y := by
  set M := ⌊y⌋₊ with hM
  set N := ⌊x⌋₊ with hN
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hy)
  have hMN : M ≤ N := Nat.floor_le_floor hyx
  have hAup : ∀ n : ℕ, 1 ≤ n →
      ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p ≤ Real.log n + 2 := fun n hn => by
    have := sum_log_prime_div_le (n : ℝ) (by exact_mod_cast hn)
    simpa using this
  have hAlo : ∀ n : ℕ, 1 ≤ n →
      Real.log n - 3 ≤ ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p := fun n hn => by
    have := sum_log_prime_div_ge (n : ℝ) (by exact_mod_cast hn)
    simpa using this
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  set AM := ∑ p ∈ (Iic M).filter Nat.Prime, Real.log p / p with hAM
  have inv : ∀ n : ℕ, M ≤ n →
      ∑ p ∈ (Ioc M n).filter Nat.Prime, (1 : ℝ) / p -
          (∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p - AM) / Real.log n ≤
        Real.log (Real.log n) - Real.log (Real.log M) +
          (5 - Real.log M) * (1 / Real.log M - 1 / Real.log n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp [hAM]
    | succ n hn ih =>
      set S := ∑ p ∈ (Ioc M n).filter Nat.Prime, (1 : ℝ) / p with hS
      set A := ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p with hA
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hn1 : (1 : ℝ) < (n : ℝ) + 1 := by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        linarith
      have hlogn1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos hn1
      have hS' := sum_primes_Ioc_succ (fun p : ℕ => (1 : ℝ) / p) hn
      have hA' := sum_primes_succ (fun p : ℕ => Real.log p / p) n
      rw [hS', hA']
      push_cast
      have hrel : S + (if (n + 1).Prime then 1 / ((n : ℝ) + 1) else 0) -
          (A + (if (n + 1).Prime then Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) else 0) - AM) /
            Real.log ((n : ℝ) + 1) = S - (A - AM) / Real.log ((n : ℝ) + 1) := by
        split_ifs
        · field_simp; ring
        · ring
      rw [hrel]
      have hD : A - AM ≤ Real.log n + 5 - Real.log M := by
        have h1 := hAup n (by omega)
        have h2 := hAlo M (by omega)
        linarith
      set d := 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) with hd
      have hd0 : 0 ≤ d := by
        rw [hd, sub_nonneg]
        apply one_div_le_one_div_of_le hlogn
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
      have hll : Real.log n * d ≤
          Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
        have h := Real.one_sub_inv_le_log_of_pos
          (x := Real.log ((n : ℝ) + 1) / Real.log n) (by positivity)
        rw [Real.log_div hlogn1.ne' hlogn.ne', inv_div] at h
        have e : Real.log n * d = 1 - Real.log n / Real.log ((n : ℝ) + 1) := by
          rw [hd]; field_simp
        linarith
      have hDd : (A - AM) * d ≤ (Real.log n + 5 - Real.log M) * d :=
        mul_le_mul_of_nonneg_right hD hd0
      have e1 : S - (A - AM) / Real.log ((n : ℝ) + 1) =
          (S - (A - AM) / Real.log n) + (A - AM) * d := by
        rw [hd]; ring
      have e2 : (Real.log n + 5 - Real.log M) * d = Real.log n * d +
          ((5 - Real.log M) * (1 / Real.log M - 1 / Real.log ((n : ℝ) + 1)) -
            (5 - Real.log M) * (1 / Real.log M - 1 / Real.log n)) := by
        rw [hd]; ring
      rw [e1]
      linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hmain := inv N hMN
  have hD : ∑ p ∈ (Iic N).filter Nat.Prime, Real.log p / p - AM ≤
      Real.log N + 5 - Real.log M := by
    have h1 := hAup N (by omega)
    have h2 := hAlo M (by omega)
    linarith
  have hD' : (∑ p ∈ (Iic N).filter Nat.Prime, Real.log p / p - AM) / Real.log N ≤
      1 + (5 - Real.log M) * (1 / Real.log N) := by
    have := div_le_div_of_nonneg_right hD hlogN.le
    have e : (Real.log N + 5 - Real.log M) / Real.log N =
        1 + (5 - Real.log M) * (1 / Real.log N) := by
      field_simp; ring
    linarith
  have eM : Real.log M * (1 / Real.log M) = 1 := by field_simp
  have hSN : ∑ p ∈ (Ioc M N).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log N) - Real.log (Real.log M) + 5 / Real.log M := by
    have e5 : 5 / Real.log M = 5 * (1 / Real.log M) := by ring
    rw [e5]
    nlinarith
  -- conversion to `x, y`
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hMy : (M : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyM : y < M + 1 := Nat.lt_floor_add_one y
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2r : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log (Real.log N) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogN (Real.log_le_log hNpos hNx)
  rw [Real.log_div hlogx.ne' hlogy.ne']
  have hmL : Real.log M ≤ Real.log y := Real.log_le_log hMpos hMy
  have hLm : Real.log y - Real.log M ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (x := y / M) (by positivity)
    rw [Real.log_div (by linarith) hMpos.ne'] at h
    have h2 : y / M - 1 ≤ 1 / 2 := by
      rw [div_sub_one hMpos.ne', div_le_iff₀ hMpos]; linarith
    linarith
  have hll : Real.log (Real.log y) - Real.log (Real.log M) ≤
      (Real.log y - Real.log M) / Real.log M := by
    have h := Real.log_le_sub_one_of_pos (x := Real.log y / Real.log M) (by positivity)
    rw [Real.log_div hlogy.ne' hlogM.ne', div_sub_one hlogM.ne'] at h
    exact h
  have h3 : (Real.log y - Real.log M) / Real.log M ≤ (1 / 2) / Real.log M :=
    div_le_div_of_nonneg_right hLm hlogM.le
  have h4 : (11 / 2) / Real.log M ≤ 100 / Real.log y := by
    rw [div_le_div_iff₀ hlogM hlogy]
    have hl2 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2r
    have := Real.log_two_gt_d9
    nlinarith
  have e : (1 / 2) / Real.log M + 5 / Real.log M = (11 / 2) / Real.log M := by ring
  linarith

/-- `∏_{y < p ≤ x} (1 + 1/p) ≤ e^{100/log y} · log x / log y`. -/
theorem prod_one_add_inv_prime_le (y x : ℝ) (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 + (1 : ℝ) / p) ≤
      Real.exp (100 / Real.log y) * (Real.log x / Real.log y) := by
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  calc ∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 + (1 : ℝ) / p)
      ≤ ∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, Real.exp ((1 : ℝ) / p) := by
        apply prod_le_prod₀
        · intro p _; positivity
        · intro p _
          have := Real.add_one_le_exp ((1 : ℝ) / p)
          linarith
    _ = Real.exp (∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp (Real.log (Real.log x / Real.log y) + 100 / Real.log y) :=
        Real.exp_le_exp.mpr (sum_inv_prime_Ioc_le y x hy hyx)
    _ = Real.exp (100 / Real.log y) * (Real.log x / Real.log y) := by
        rw [Real.exp_add, Real.exp_log (by positivity), mul_comm]

/-- Mertens' third theorem, upper bound: `∏_{p ≤ x} (1 - 1/p)⁻¹ ≪ log x`. -/
theorem prod_inv_one_sub_inv_prime_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ ≤ C * Real.log x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.exp (3 / 2 + 100 / Real.log 2) / Real.log 2, by positivity, fun x hx => ?_⟩
  set n := ⌊x⌋₊ with hn
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hprod : ∏ p ∈ (Iic n).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp (∑ p ∈ (Iic n).filter Nat.Prime,
        ((1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
    rw [Real.exp_sum]
    apply prod_le_prod₀
    · intro p hp
      have hpp := (mem_filter.1 hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have : 0 < 1 - (1 : ℝ) / p := by
        rw [sub_pos, div_lt_one (by linarith)]; exact hp1
      positivity
    · intro p hp
      have hpp := (mem_filter.1 hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have e : (1 - (1 : ℝ) / p)⁻¹ = ((1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1))) + 1 := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        have : (p : ℝ) ≠ 0 := by linarith
        field_simp; ring
      rw [e]
      exact Real.add_one_le_exp _
  rw [sum_add_distrib] at hprod
  have hsub : (Iic n).filter Nat.Prime ⊆ Icc 2 n := by
    intro p hp
    simp only [mem_filter, mem_Iic] at hp
    simp only [mem_Icc]
    exact ⟨hp.2.two_le, hp.1⟩
  have hB : ∑ p ∈ (Iic n).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    have h1 : ∑ p ∈ (Iic n).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        ∑ m ∈ Icc 2 n, 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro m hm _
      simp only [mem_Icc] at hm
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
      apply div_nonneg zero_le_one
      apply mul_nonneg <;> linarith
    have h2 := sum_inv_Icc n (by omega)
    have h3 : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hsplit : (Iic n).filter Nat.Prime ⊆ insert 2 ((Ioc 2 n).filter Nat.Prime) := by
    intro p hp
    simp only [mem_filter, mem_Iic] at hp
    simp only [mem_insert, mem_filter, mem_Ioc]
    rcases eq_or_ne p 2 with h | h
    · left; exact h
    · right; exact ⟨⟨lt_of_le_of_ne hp.2.two_le (Ne.symm h), hp.1⟩, hp.2⟩
  have hA : ∑ p ∈ (Iic n).filter Nat.Prime, (1 : ℝ) / p ≤
      1 / 2 + ∑ p ∈ (Ioc 2 n).filter Nat.Prime, (1 : ℝ) / p := by
    have h1 := sum_le_sum_of_subset_of_nonneg hsplit
      (f := fun p : ℕ => (1 : ℝ) / p) (fun p _ _ => by positivity)
    rw [sum_insert (by simp)] at h1
    norm_num at h1 ⊢
    linarith
  have hM2 := sum_inv_prime_Ioc_le 2 x le_rfl hx
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hfl] at hM2
  have hexp : Real.exp (∑ p ∈ (Iic n).filter Nat.Prime, (1 : ℝ) / p +
      ∑ p ∈ (Iic n).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      Real.exp (3 / 2 + 100 / Real.log 2 + Real.log (Real.log x / Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hR : Real.exp (3 / 2 + 100 / Real.log 2 + Real.log (Real.log x / Real.log 2)) =
      Real.exp (3 / 2 + 100 / Real.log 2) * (Real.log x / Real.log 2) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
  have e : Real.exp (3 / 2 + 100 / Real.log 2) * (Real.log x / Real.log 2) =
      Real.exp (3 / 2 + 100 / Real.log 2) / Real.log 2 * Real.log x := by ring
  linarith

end DuffinSchaeffer
