import ErdosLean.DuffinSchaeffer.Parts.Mertens

/-!
# Duffin–Schaeffer — Part 7: an upper-bound sieve for integers coprime to `m`

`∑_{1 ≤ h ≤ H, (h,m)=1} gcd(h,g)/φ(gcd(h,g)) ≪ H ∏_{p | m, p ≤ H} (1 - 1/p)`.

Instead of Selberg's Λ² sieve we use the elementary "Chebyshev–Hall–Tenenbaum" argument:
with `F(n) = 1_{(n,m)=1} n/φ(n)` (which dominates the weight since `gcd(h,g) ∣ h`),
* `F(n) log n = ∑_{d ∣ n} Λ(d) F(n) ≤ 2 ∑_{d ∣ n} Λ(d) F(n/d)` (sub-multiplicativity of `n/φ(n)`
  and `d/φ(d) ≤ 2` for prime powers), so by Chebyshev `ψ(x) ≪ x`,
  `∑_{n ≤ N} F(n) log n ≪ N ∑_{n ≤ N} F(n)/n`;
* `log(N/n) ≤ N/n`, hence `(∑_{n≤N} F(n)) log N ≪ N ∑_{n ≤ N, (n,m)=1} 1/φ(n)`;
* the Euler product bounds `∑_{n ≤ N, (n,m)=1} 1/φ(n) ≤ e⁴ ∏_{p ≤ N, p ∤ m} (1 - 1/p)⁻¹`,
  and Mertens' third theorem (upper bound, Part 5) turns this into `≪ log N ∏_{p ∣ m, p ≤ N}(1-1/p)`.
-/

open Finset

namespace DuffinSchaeffer

namespace CoprimeSieveAux

lemma totient_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv] at h
  simpa [one_div] using h

lemma prime_factor_bounds {p : ℕ} (hp : p.Prime) :
    0 < 1 - (1 : ℝ) / p ∧ 1 - (1 : ℝ) / p ≤ 1 ∧ 1 / 2 ≤ 1 - (1 : ℝ) / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (1 : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h4 : 0 ≤ (1 : ℝ) / p := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩

lemma one_le_factor {p : ℕ} (hp : p.Prime) : 1 ≤ (1 - (1 : ℝ) / p)⁻¹ := by
  obtain ⟨h1, h2, -⟩ := prime_factor_bounds hp
  exact (one_le_inv₀ h1).mpr h2

/-- `R n = n / φ(n)`. -/
noncomputable def R (n : ℕ) : ℝ := (n : ℝ) / Nat.totient n

lemma R_nonneg (n : ℕ) : 0 ≤ R n := by unfold R; positivity

lemma R_eq {n : ℕ} (hn : n ≠ 0) : R n = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
  rw [R, totient_real, prod_inv_distrib]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [div_mul_eq_div_div, div_self this, one_div]

lemma R_mono {d n : ℕ} (hd : d ∣ n) (hn : n ≠ 0) : R d ≤ R n := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  rw [R_eq hd0, R_eq hn]
  have hsub : d.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hd hn
  rw [← prod_sdiff hsub]
  have h1 : (1 : ℝ) ≤ ∏ p ∈ n.primeFactors \ d.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
    calc (1 : ℝ) = ∏ p ∈ n.primeFactors \ d.primeFactors, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun p hp => one_le_factor (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1))
  have h2 : 0 ≤ ∏ p ∈ d.primeFactors, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_nonneg (fun p hp => by linarith [one_le_factor (Nat.prime_of_mem_primeFactors hp)])
  nlinarith

lemma R_primePow {d : ℕ} (hd : IsPrimePow d) : R d ≤ 2 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  rw [R_eq (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk.ne' hp, prod_singleton]
  obtain ⟨h1, -, h3⟩ := prime_factor_bounds hp
  rw [inv_le_comm₀ h1 (by norm_num)]
  have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  linarith

lemma R_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : R (a * b) ≤ R a * R b := by
  unfold R
  have hta : (0 : ℝ) < Nat.totient a := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)
  have htb : (0 : ℝ) < Nat.totient b := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have hsup : (Nat.totient a : ℝ) * Nat.totient b ≤ Nat.totient (a * b) := by
    exact_mod_cast Nat.totient_super_multiplicative a b
  rw [div_mul_div_comm, Nat.cast_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsup

/-- `F m n = 1_{(n,m)=1} · n/φ(n)`. -/
noncomputable def F (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime m then R n else 0, by simp [R]⟩

lemma F_apply (m n : ℕ) : F m n = if n.Coprime m then R n else 0 := rfl

lemma F_nonneg (m n : ℕ) : 0 ≤ F m n := by
  rw [F_apply]; split_ifs
  · exact R_nonneg n
  · exact le_refl 0

lemma F_mul_log_le (m n : ℕ) :
    F m n * Real.log n ≤ 2 * (ArithmeticFunction.vonMangoldt * F m) n := by
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum, ArithmeticFunction.mul_apply]
  have hd := Nat.sum_divisorsAntidiagonal
    (fun a b => ArithmeticFunction.vonMangoldt a * F m b) (n := n)
  rw [hd, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hid : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hi).2
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt i := ArithmeticFunction.vonMangoldt_nonneg
  by_cases h0 : ArithmeticFunction.vonMangoldt i = 0
  · rw [h0]; simp
  have hpp : IsPrimePow i := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
  have hk0 : n / i ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hi) (Nat.pos_of_ne_zero hi0)).ne'
  have key : F m n ≤ 2 * F m (n / i) := by
    rw [F_apply, F_apply]
    by_cases h1 : n.Coprime m
    · have h2 : (n / i).Coprime m := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hid) h1
      rw [if_pos h1, if_pos h2]
      calc R n = R (i * (n / i)) := by rw [Nat.mul_div_cancel' hid]
        _ ≤ R i * R (n / i) := R_mul_le hi0 hk0
        _ ≤ 2 * R (n / i) := mul_le_mul_of_nonneg_right (R_primePow hpp) (R_nonneg _)
    · rw [if_neg h1]
      split_ifs
      · linarith [R_nonneg (n / i)]
      · norm_num
  calc F m n * ArithmeticFunction.vonMangoldt i
      = ArithmeticFunction.vonMangoldt i * F m n := mul_comm _ _
    _ ≤ ArithmeticFunction.vonMangoldt i * (2 * F m (n / i)) := mul_le_mul_of_nonneg_left key hΛ
    _ = 2 * (ArithmeticFunction.vonMangoldt i * F m (n / i)) := by ring

lemma sum_F_log_le (m N : ℕ) :
    ∑ n ∈ Ioc 0 N, F m n * Real.log n ≤
      2 * (Real.log 4 + 4) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
  calc ∑ n ∈ Ioc 0 N, F m n * Real.log n
      ≤ ∑ n ∈ Ioc 0 N, 2 * (ArithmeticFunction.vonMangoldt * F m) n :=
        sum_le_sum fun n _ => F_mul_log_le m n
    _ = 2 * ∑ n ∈ Ioc 0 N, (F m * ArithmeticFunction.vonMangoldt) n := by
        rw [← mul_sum, mul_comm ArithmeticFunction.vonMangoldt (F m)]
    _ = 2 * ∑ k ∈ Ioc 0 N, F m k * ∑ j ∈ Ioc 0 (N / k), ArithmeticFunction.vonMangoldt j := by
        rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    _ ≤ 2 * ∑ k ∈ Ioc 0 N, F m k * ((Real.log 4 + 4) * ((N : ℝ) / k)) := by
        gcongr with k hk
        · exact F_nonneg m k
        · have h1 : ∑ j ∈ Ioc 0 (N / k), ArithmeticFunction.vonMangoldt j =
              Chebyshev.psi ((N / k : ℕ) : ℝ) := by
            simp [Chebyshev.psi]
          rw [h1]
          calc Chebyshev.psi ((N / k : ℕ) : ℝ) ≤ (Real.log 4 + 4) * ((N / k : ℕ) : ℝ) :=
                Chebyshev.psi_le_const_mul_self (by positivity)
            _ ≤ (Real.log 4 + 4) * ((N : ℝ) / k) := by
                gcongr
                exact Nat.cast_div_le
    _ = 2 * (Real.log 4 + 4) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun k _ => by ring

lemma sum_F_logN_le (m N : ℕ) :
    (∑ n ∈ Ioc 0 N, F m n) * Real.log N ≤
      (2 * (Real.log 4 + 4) + 1) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
  have h : ∀ n ∈ Ioc 0 N, F m n * Real.log N ≤ F m n * Real.log n + N * (F m n / n) := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn.1 hn.2)
    have hlog : Real.log N ≤ Real.log n + N / n := by
      have e : Real.log N = Real.log n + Real.log ((N : ℝ) / n) := by
        rw [Real.log_div hN0.ne' hn0.ne']; ring
      have h2 : Real.log ((N : ℝ) / n) ≤ N / n :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      linarith
    have := F_nonneg m n
    calc F m n * Real.log N ≤ F m n * (Real.log n + N / n) := mul_le_mul_of_nonneg_left hlog this
      _ = _ := by ring
  have hA := sum_F_log_le m N
  have e2 : (2 * (Real.log 4 + 4) + 1) * N * ∑ n ∈ Ioc 0 N, F m n / n =
      2 * (Real.log 4 + 4) * N * (∑ n ∈ Ioc 0 N, F m n / n) +
        N * ∑ n ∈ Ioc 0 N, F m n / n := by ring
  calc (∑ n ∈ Ioc 0 N, F m n) * Real.log N = ∑ n ∈ Ioc 0 N, F m n * Real.log N := sum_mul _ _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (F m n * Real.log n + N * (F m n / n)) := sum_le_sum h
    _ = ∑ n ∈ Ioc 0 N, F m n * Real.log n + N * ∑ n ∈ Ioc 0 N, F m n / n := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ _ := by rw [e2]; linarith

/-- `f n = 1/φ(n)`. -/
noncomputable def f (n : ℕ) : ℝ := 1 / (Nat.totient n : ℝ)

lemma f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; positivity

lemma f_one : f 1 = 1 := by simp [f]

lemma f_mul {a b : ℕ} (h : Nat.Coprime a b) : f (a * b) = f a * f b := by
  simp [f, Nat.totient_mul h, mul_comm]

lemma f_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ (k + 1)) = (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ k := by
  rw [f, Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le,
    Nat.cast_one, one_div_pow, div_mul_div_comm, one_mul, mul_comm]

lemma hasSum_f_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun k => f (p ^ k)) (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / ((p : ℝ) - 1))
  have hg' : HasSum (fun k => f (p ^ (k + 1))) (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹) := by
    have : (fun k => f (p ^ (k + 1))) = fun k => (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ k := by
      funext k; exact f_pow_succ hp k
    rw [this]; exact hg
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [sum_range_one, pow_zero, f_one, add_sub_cancel_right]
  exact hg'

lemma euler_factor_le {p : ℕ} (hp : p.Prime) :
    1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1 ≤
      (1 - 1 / (p : ℝ))⁻¹ * (1 + 2 * ((p : ℝ) ^ 2)⁻¹) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set q : ℝ := (p : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have e1 : (1 - 1 / q)⁻¹ = q / (q - 1) := by rw [one_sub_div hq0, inv_div]
  rw [e1]
  have key : q / (q - 1) * (1 + 2 * (q ^ 2)⁻¹) - (1 / (q - 1) * (q / (q - 1)) + 1) =
      (q - 2) / (q * (q - 1) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (q - 2) / (q * (q - 1) ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

lemma prod_euler_le (N : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p ≤ N) :
    ∏ p ∈ s, (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) ≤
      Real.exp 4 * ∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹ := by
  have hnn : 0 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_nonneg fun p hp => by linarith [one_le_factor (hs p hp).1]
  calc ∏ p ∈ s, (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1)
      ≤ ∏ p ∈ s, ((1 - 1 / (p : ℝ))⁻¹ * (1 + 2 * ((p : ℝ) ^ 2)⁻¹)) := by
        refine prod_le_prod₀ (fun p hp => ?_) (fun p hp => euler_factor_le (hs p hp).1)
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).1.two_le
        have : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
        have := one_le_factor (hs p hp).1
        positivity
    _ = (∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ s, (1 + 2 * ((p : ℝ) ^ 2)⁻¹) := prod_mul_distrib
    _ ≤ (∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹) * Real.exp 4 := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        calc ∏ p ∈ s, (1 + 2 * ((p : ℝ) ^ 2)⁻¹) ≤ ∏ p ∈ s, Real.exp (2 * ((p : ℝ) ^ 2)⁻¹) :=
              prod_le_prod₀ (fun p _ => by positivity)
                (fun p _ => by linarith [Real.add_one_le_exp (2 * ((p : ℝ) ^ 2)⁻¹)])
          _ = Real.exp (∑ p ∈ s, 2 * ((p : ℝ) ^ 2)⁻¹) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              rw [← mul_sum]
              have hsub : s ⊆ Ioo 0 (N + 1) := fun p hp => by
                have := hs p hp
                simp only [mem_Ioo]
                exact ⟨this.1.pos, by omega⟩
              have h1 := sum_le_sum_of_subset_of_nonneg hsub
                (f := fun i : ℕ => ((i : ℝ) ^ 2)⁻¹) (fun i _ _ => by positivity)
              have h2 := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
              norm_num at h2
              linarith
    _ = _ := mul_comm _ _

lemma sum_F_div_le (m N : ℕ) :
    ∑ n ∈ Ioc 0 N, F m n / n ≤
      ∏ p ∈ ((Iic N).filter Nat.Prime).filter (fun p => ¬ p ∣ m),
        (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  classical
  set s := ((Iic N).filter Nat.Prime).filter (fun p => ¬ p ∣ m) with hs
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simpa [Real.norm_eq_abs] using (hasSum_f_pow hp).summable.abs
  obtain ⟨-, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := f) f_one (fun h => f_mul h) hsum s
  have hsP : ∀ p ∈ s, p.Prime := fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2
  have hfilt : s.filter Nat.Prime = s := filter_true_of_mem hsP
  have hle : ∑ n ∈ Ioc 0 N, F m n / n = ∑ n ∈ (Ioc 0 N).filter (fun n => n.Coprime m), f n := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := (mem_Ioc.mp hn).1
      exact_mod_cast this.ne'
    rw [F_apply]
    split_ifs
    · unfold R f
      have ht : (Nat.totient n : ℝ) ≠ 0 := by
        have : 0 < n := (mem_Ioc.mp hn).1
        exact_mod_cast (Nat.totient_pos.mpr this).ne'
      field_simp
    · simp
  rw [hle]
  have hmem : ∀ n ∈ (Ioc 0 N).filter (fun n => n.Coprime m), n ∈ Nat.factoredNumbers s := by
    intro n hn
    obtain ⟨hnI, hcop⟩ := mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hnI
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
    refine ⟨hn1.ne', fun p hp => ?_⟩
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    simp only [hs, mem_filter, mem_Iic]
    refine ⟨⟨(Nat.le_of_dvd hn1 hpn).trans hn2, hpp⟩, fun hpm => ?_⟩
    have := Nat.dvd_gcd hpn hpm
    rw [hcop.gcd_eq_one] at this
    exact hpp.not_dvd_one this
  rw [← sum_subtype_of_mem f hmem]
  calc ∑ x ∈ ((Ioc 0 N).filter (fun n => n.Coprime m)).subtype (· ∈ Nat.factoredNumbers s), f x
      ≤ ∑' x : Nat.factoredNumbers s, f x :=
        hhas.summable.sum_le_tsum _ (fun x _ => f_nonneg x)
    _ = ∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, f (p ^ k) := hhas.tsum_eq
    _ = _ := by
        rw [hfilt]
        exact prod_congr rfl fun p hp => (hasSum_f_pow (hsP p hp)).tsum_eq

end CoprimeSieveAux

open CoprimeSieveAux in
theorem sieve_weighted_coprime : ∃ C : ℝ, 0 < C ∧ ∀ (m g : ℕ) (H : ℝ), 0 < m → 0 < g → 1 ≤ H →
    ∑ h ∈ (Icc 1 ⌊H⌋₊).filter (fun h => Nat.Coprime h m),
        ((Nat.gcd h g : ℝ) / Nat.totient (Nat.gcd h g)) ≤
      C * H * ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) := by
  obtain ⟨CM, hCM, hMert⟩ := prod_inv_one_sub_inv_prime_le
  set K : ℝ := 2 * (Real.log 4 + 4) + 1 with hK
  have hK0 : 0 < K := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); rw [hK]; linarith
  refine ⟨max 1 (K * Real.exp 4 * CM), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro m g H hm _hg hH
  have hH0 : (0 : ℝ) ≤ H := by linarith
  set N := ⌊H⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hH)
  have hNH : (N : ℝ) ≤ H := Nat.floor_le hH0
  set Q := ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) with hQ
  have hQpos : 0 < Q := prod_pos fun p hp =>
    (prime_factor_bounds (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).1
  -- Step 0: the weight is at most `h/φ(h)`.
  have hLA : ∑ h ∈ (Icc 1 N).filter (fun h => Nat.Coprime h m),
        ((Nat.gcd h g : ℝ) / Nat.totient (Nat.gcd h g)) ≤ ∑ n ∈ Ioc 0 N, F m n := by
    have hIcc : Icc 1 N = Ioc 0 N := by ext; simp; omega
    rw [← hIcc, sum_filter]
    refine sum_le_sum fun h hh => ?_
    rw [F_apply]
    split_ifs
    · exact R_mono (Nat.gcd_dvd_left h g) (by simp at hh; omega)
    · exact le_refl 0
  refine hLA.trans ?_
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · -- `N = 1`
    have hN1' : N = 1 := by omega
    have hA : ∑ n ∈ Ioc 0 N, F m n ≤ 1 := by
      rw [hN1']
      simp [F_apply, R]
    have hH2 : H < 2 := by
      have : ⌊H⌋₊ < 2 := hN2
      exact (Nat.floor_lt hH0).mp (by simpa using this)
    have hQ1 : Q = 1 := by
      rw [hQ]
      refine prod_eq_one fun p hp => ?_
      exfalso
      obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp1).two_le
      linarith
    rw [hQ1, mul_one]
    calc ∑ n ∈ Ioc 0 N, F m n ≤ 1 := hA
      _ = 1 * 1 := by norm_num
      _ ≤ max 1 (K * Real.exp 4 * CM) * H := by gcongr; exact le_max_left _ _
  · -- `N ≥ 2`
    have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    set T := (Iic N).filter Nat.Prime with hT
    have hs'eq : m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H) = T.filter (fun p => p ∣ m) := by
      ext p
      simp only [hT, mem_filter, Nat.mem_primeFactors, mem_Iic]
      constructor
      · rintro ⟨⟨hp, hpm, -⟩, hpH⟩
        exact ⟨⟨Nat.le_floor hpH, hp⟩, hpm⟩
      · rintro ⟨⟨hpN, hp⟩, hpm⟩
        exact ⟨⟨hp, hpm, hm.ne'⟩, (Nat.le_floor_iff hH0).mp hpN⟩
    have hMN := hMert (N : ℝ) hN2'
    rw [Nat.floor_natCast] at hMN
    have hsplit := prod_filter_mul_prod_filter_not T (fun p => p ∣ m)
      (f := fun p : ℕ => (1 - (1 : ℝ) / p)⁻¹)
    have hQinv : ∏ p ∈ T.filter (fun p => p ∣ m), (1 - (1 : ℝ) / p)⁻¹ = Q⁻¹ := by
      rw [hQ, hs'eq, prod_inv_distrib]
    rw [hQinv] at hsplit
    set Ps := ∏ p ∈ T.filter (fun p => ¬ p ∣ m), (1 - (1 : ℝ) / p)⁻¹ with hPs
    have hPs : Ps ≤ CM * Real.log N * Q := by
      have e : Ps = (Q⁻¹ * Ps) * Q := by field_simp
      rw [e, hsplit]
      exact mul_le_mul_of_nonneg_right hMN hQpos.le
    have hB := sum_F_div_le m N
    have hE := prod_euler_le N (T.filter (fun p => ¬ p ∣ m)) (fun p hp => by
      simp only [hT, mem_filter, mem_Iic] at hp
      exact ⟨hp.1.2, hp.1.1⟩)
    have hB' : ∑ n ∈ Ioc 0 N, F m n / n ≤ Real.exp 4 * (CM * Real.log N * Q) :=
      hB.trans (hE.trans (mul_le_mul_of_nonneg_left hPs (Real.exp_pos 4).le))
    have hAlog := sum_F_logN_le m N
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hA : (∑ n ∈ Ioc 0 N, F m n) * Real.log N ≤
        ((K * Real.exp 4 * CM) * N * Q) * Real.log N := by
      calc (∑ n ∈ Ioc 0 N, F m n) * Real.log N
          ≤ K * N * ∑ n ∈ Ioc 0 N, F m n / n := hAlog
        _ ≤ K * N * (Real.exp 4 * (CM * Real.log N * Q)) :=
            mul_le_mul_of_nonneg_left hB' (by positivity)
        _ = ((K * Real.exp 4 * CM) * N * Q) * Real.log N := by ring
    have hA' := le_of_mul_le_mul_right hA hlogN
    calc ∑ n ∈ Ioc 0 N, F m n ≤ (K * Real.exp 4 * CM) * N * Q := hA'
      _ ≤ max 1 (K * Real.exp 4 * CM) * H * Q := by
          refine mul_le_mul_of_nonneg_right ?_ hQpos.le
          exact mul_le_mul (le_max_right _ _) hNH hN0 (by positivity)

end DuffinSchaeffer
