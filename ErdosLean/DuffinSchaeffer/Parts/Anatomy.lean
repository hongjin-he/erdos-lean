import ErdosLean.DuffinSchaeffer.Parts.Mertens

/-!
# Duffin–Schaeffer — Part 10: few integers with many large prime factors (KM Lemma 7.3)

`#{n ≤ x : ∑_{p | n, p ≥ t} 1/p ≥ c} ≪ x exp(-t^{e^{c-1}})`,
`c ∈ [1, 10]`.  KM cite Lemma 7.2 (Hall–Tenenbaum); an elementary replacement suffices:
with `T = t^{e^{c-1}}`, `1_{…} ≤ e^{-T} ∏_{p | n, p ≥ T} e^{2T/p}`, expand
`∏_{p|n,p≥T} e^{2T/p} = ∑_{d | n, d sqfree, p|d ⇒ p ≥ T} ∏_{p|d}(e^{2T/p} - 1)`, swap sums and use
`∑_{p ≥ T} (e^{2T/p}-1)/p ≪ T ∑_{p≥T} 1/p² ≪ 1`.
-/

open Finset

namespace DuffinSchaeffer

/-- Rankin-type expansion: `∑_{n ≤ N} ∏_{p | n, p ≥ T} (1 + g p) ≤ N ∏_{p ≤ N, p ≥ T} (1 + g p / p)`. -/
lemma sum_prod_one_add_le (N : ℕ) (T : ℝ) (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) :
    ∑ n ∈ Icc 1 N, ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p) ≤
      (N : ℝ) * ∏ p ∈ (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)),
        (1 + g p / p) := by
  classical
  set P := (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)) with hPdef
  have hsub : ∀ n ∈ Icc 1 N, n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)) ⊆ P := by
    intro n hn p hp
    simp only [mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpn, hn0⟩, hT⟩ := hp
    simp only [hPdef, mem_filter, mem_Icc] at hn ⊢
    exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpn).trans hn.2⟩, hpp, hT⟩
  have step1 : ∀ n ∈ Icc 1 N,
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p)
        = ∑ A ∈ P.powerset, if A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ))
            then ∏ p ∈ A, g p else 0 := by
    intro n hn
    rw [prod_one_add, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext A
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨h.trans (hsub n hn), h⟩, fun h => h.2⟩
  rw [sum_congr rfl step1, sum_comm]
  have hIcc : Icc 1 N = Ioc 0 N := by ext; simp; omega
  have step2 : ∀ A ∈ P.powerset,
      ∑ n ∈ Icc 1 N, (if A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ))
          then ∏ p ∈ A, g p else 0) ≤ (N : ℝ) * ∏ p ∈ A, (g p / p) := by
    intro A hA
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hApr : ∀ p ∈ A, p.Prime := fun p hp => ((mem_filter.1 (mem_powerset.1 hA hp)).2).1
    have hcard : ((Icc 1 N).filter
        (fun n => A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)))).card
          ≤ N / ∏ p ∈ A, p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, ← hIcc]
      apply card_le_card
      intro n hn
      simp only [mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      apply Finset.prod_primes_dvd
      · intro p hp; exact Nat.prime_iff.1 (hApr p hp)
      · intro p hp
        have := hn.2 hp
        simp only [mem_filter, Nat.mem_primeFactors] at this
        exact this.1.2.1
    have hG : 0 ≤ ∏ p ∈ A, g p := prod_nonneg (fun p _ => hg p)
    calc (((Icc 1 N).filter
          (fun n => A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)))).card : ℝ)
            * ∏ p ∈ A, g p
          ≤ ((N / ∏ p ∈ A, p : ℕ) : ℝ) * ∏ p ∈ A, g p := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hG
      _ ≤ ((N : ℝ) / ∏ p ∈ A, (p : ℝ)) * ∏ p ∈ A, g p := by
          gcongr; rw [← Nat.cast_prod]; exact Nat.cast_div_le
      _ = (N : ℝ) * ∏ p ∈ A, (g p / p) := by
          rw [prod_div_distrib]; try ring
  calc _ ≤ ∑ A ∈ P.powerset, (N : ℝ) * ∏ p ∈ A, (g p / p) := sum_le_sum step2
    _ = _ := by rw [← mul_sum, prod_one_add]

/-- `e^u - 1 ≤ 8u` for `0 ≤ u ≤ 2`. -/
lemma exp_sub_one_le_eight_mul (u : ℝ) (h0 : 0 ≤ u) (h2 : u ≤ 2) :
    Real.exp u - 1 ≤ 8 * u := by
  have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hle : Real.exp u - 1 ≤ u * Real.exp u := by nlinarith [Real.exp_pos u]
  have he2 : Real.exp u ≤ 8 := by
    have : Real.exp u ≤ Real.exp 2 := Real.exp_le_exp.2 h2
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  nlinarith

theorem card_many_large_prime_factors_le : ∃ C : ℝ, 0 < C ∧ ∀ x t c : ℝ, 1 ≤ x → 1 ≤ t →
    1 ≤ c → c ≤ 10 →
    (((Icc 1 ⌊x⌋₊).filter (fun n : ℕ =>
        c ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p)).card : ℝ) ≤
      C * x * Real.exp (-(t ^ Real.exp (c - 1))) := by
  refine ⟨Real.exp (Real.exp (300 * Real.exp 9)), Real.exp_pos _, ?_⟩
  intro x t c hx ht hc1 hc10
  set E := Real.exp (c - 1) with hE
  set T := t ^ E with hT
  set S := (Icc 1 ⌊x⌋₊).filter (fun n : ℕ =>
        c ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p) with hS
  set K := Real.exp (300 * Real.exp 9) with hK
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by linarith)
  have hE9 : E ≤ Real.exp 9 := Real.exp_le_exp.2 (by linarith)
  have hx0 : 0 ≤ x := by linarith
  have ht0 : 0 < t := by linarith
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hTexp : T = Real.exp (Real.log t * E) := Real.rpow_def_of_pos ht0 E
  have hTpos : 0 < T := by rw [hTexp]; exact Real.exp_pos _
  have hcardx : (S.card : ℝ) ≤ x := by
    have : S.card ≤ ⌊x⌋₊ := (card_filter_le _ _).trans (by simp)
    calc (S.card : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast this
      _ ≤ x := Nat.floor_le hx0
  have hK64 : 64 ≤ K := by
    have h1 : 1 ≤ Real.exp 9 := Real.one_le_exp (by norm_num)
    have := Real.add_one_le_exp (300 * Real.exp 9)
    linarith
  by_cases hts : Real.log t ≤ 300
  · -- small `t`: the trivial bound suffices
    have hTle : T ≤ K := by
      rw [hTexp, hK]
      apply Real.exp_le_exp.2
      nlinarith
    have h1 : 1 ≤ Real.exp K * Real.exp (-T) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc (S.card : ℝ) ≤ x := hcardx
      _ ≤ (Real.exp K * Real.exp (-T)) * x := le_mul_of_one_le_left hx0 h1
      _ = Real.exp K * x * Real.exp (-T) := by ring
  · rw [not_le] at hts
    -- large `t`
    have htT : t ≤ T := by
      have := Real.rpow_le_rpow_of_exponent_le ht hE1
      simpa [hT] using this
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ht2 : 2 ≤ t / 2 := by
      have : Real.exp 300 < t := by
        rw [← Real.exp_log ht0]; exact Real.exp_lt_exp.2 hts
      have : (4 : ℝ) ≤ Real.exp 300 := by
        have := Real.add_one_le_exp (300 : ℝ); linarith
      linarith
    -- Mertens on `(t/2, T]`
    set B := (Ioc ⌊t / 2⌋₊ ⌊T⌋₊).filter Nat.Prime with hB
    have hBle : ∑ p ∈ B, (1 : ℝ) / p ≤ c - 1 / 2 := by
      have hM := sum_inv_prime_Ioc_le (t / 2) T ht2 (by linarith)
      have hlogt2 : Real.log (t / 2) = Real.log t - Real.log 2 :=
        Real.log_div (by linarith) (by norm_num)
      have hlogT : Real.log T = E * Real.log t := by
        rw [hT]; exact Real.log_rpow ht0 E
      have hden : 299 ≤ Real.log t - Real.log 2 := by linarith
      have hdpos : 0 < Real.log t - Real.log 2 := by linarith
      have hr : Real.log (Real.log T / Real.log (t / 2))
          = (c - 1) + Real.log (Real.log t / (Real.log t - Real.log 2)) := by
        rw [hlogT, hlogt2, mul_div_assoc, Real.log_mul (by positivity)
          (div_pos (by linarith) hdpos).ne', hE, Real.log_exp]
      have hr2 : Real.log (Real.log t / (Real.log t - Real.log 2))
          ≤ Real.log 2 / (Real.log t - Real.log 2) := by
        have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0:ℝ) < Real.log t) hdpos)
        have heq : Real.log t / (Real.log t - Real.log 2) - 1
            = Real.log 2 / (Real.log t - Real.log 2) := by
          field_simp; ring
        linarith
      rw [hr, hlogt2] at hM
      have h100 : 100 / (Real.log t - Real.log 2) ≤ 100 / 299 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      have hl2 : Real.log 2 / (Real.log t - Real.log 2) ≤ 1 / 299 := by
        rw [div_le_div_iff₀ hdpos (by norm_num)]; nlinarith
      linarith
    -- Rankin weights
    set g : ℕ → ℝ := fun p => Real.exp (2 * T / p) - 1 with hgdef
    have hg : ∀ p, 0 ≤ g p := by
      intro p; simp only [hgdef, sub_nonneg]
      exact Real.one_le_exp (by positivity)
    set F : ℕ → ℝ := fun n =>
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p) with hFdef
    have hF0 : ∀ n, 0 ≤ F n := fun n => prod_nonneg (fun p _ => by linarith [hg p])
    have hrank : ∀ n ∈ S, 1 ≤ Real.exp (-T) * F n := by
      intro n hn
      simp only [hS, mem_filter] at hn
      obtain ⟨-, hsum⟩ := hn
      set Q := n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) with hQ
      have hsplit := sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) < T)
        (fun p : ℕ => (1 : ℝ) / p)
      have hA : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p
          ≤ ∑ p ∈ B, (1 : ℝ) / p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [hQ, mem_filter, Nat.mem_primeFactors] at hp
          obtain ⟨⟨⟨hpp, -, -⟩, htp⟩, hpT⟩ := hp
          simp only [hB, mem_filter, mem_Ioc]
          refine ⟨⟨?_, Nat.le_floor hpT.le⟩, hpp⟩
          have : (⌊t / 2⌋₊ : ℝ) < p :=
            lt_of_le_of_lt (Nat.floor_le (by linarith)) (by linarith)
          exact_mod_cast this
        · intro p _ _; positivity
      have hC : ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) < T), (1 : ℝ) / p
          ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 : ℝ) / p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [hQ, mem_filter, not_lt] at hp ⊢
          exact ⟨hp.1.1, hp.2⟩
        · intro p _ _; positivity
      have hhalf : 1 / 2 ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)),
          (1 : ℝ) / p := by linarith
      have hFe : F n = Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)),
          2 * T / p) := by
        rw [hFdef, Real.exp_sum]
        apply prod_congr rfl; intro p _; simp only [hgdef]; ring
      rw [hFe, ← Real.exp_add]
      apply Real.one_le_exp
      have : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), 2 * T / (p : ℝ)
          = 2 * T * ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 : ℝ) / p := by
        rw [mul_sum]; apply sum_congr rfl; intro p _; ring
      rw [this]; nlinarith
    -- the sum over all `n ≤ x`
    set N := ⌊x⌋₊ with hN
    set P := (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)) with hP
    have hPsum : ∑ p ∈ P, g p / p ≤ 64 := by
      have hterm : ∑ p ∈ P, g p / p ≤ ∑ p ∈ P, 16 * T * ((p : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro p hp
        simp only [hP, mem_filter] at hp
        have hpT : T ≤ (p : ℝ) := hp.2.2
        have hp0 : 0 < (p : ℝ) := by linarith
        have hu2 : 2 * T / p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
        have := exp_sub_one_le_eight_mul (2 * T / p) (by positivity) hu2
        simp only [hgdef]
        rw [div_le_iff₀ hp0]
        calc Real.exp (2 * T / p) - 1 ≤ 8 * (2 * T / p) := this
          _ = 16 * T * ((p : ℝ) ^ 2)⁻¹ * p := by field_simp; ring
      have hsq : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ 4 / T := by
        set k := ⌊T / 2⌋₊ with hk
        have hk1 : T / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
        calc ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Ioo k (N + 1), ((i : ℝ) ^ 2)⁻¹ := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp
                simp only [hP, mem_filter, mem_Icc] at hp
                simp only [mem_Ioo]
                refine ⟨?_, by omega⟩
                have : (k : ℝ) < p :=
                  lt_of_le_of_lt (Nat.floor_le (by positivity)) (by linarith [hp.2.2])
                exact_mod_cast this
              · intro i _ _; positivity
          _ ≤ 2 / ((k : ℝ) + 1) := sum_Ioo_inv_sq_le k (N + 1)
          _ ≤ 2 / (T / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hk1.le
          _ = 4 / T := by field_simp; ring
      calc ∑ p ∈ P, g p / p ≤ ∑ p ∈ P, 16 * T * ((p : ℝ) ^ 2)⁻¹ := hterm
        _ = 16 * T * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
        _ ≤ 16 * T * (4 / T) := by gcongr
        _ = 64 := by field_simp; ring
    have hPprod : ∏ p ∈ P, (1 + g p / p) ≤ Real.exp 64 := by
      calc ∏ p ∈ P, (1 + g p / p) ≤ ∏ p ∈ P, Real.exp (g p / p) := by
            apply Finset.prod_le_prod₀
            · intro p _; have := hg p; positivity
            · intro p _; have := Real.add_one_le_exp (g p / p); linarith
        _ = Real.exp (∑ p ∈ P, g p / p) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp 64 := Real.exp_le_exp.2 hPsum
    have hall : ∑ n ∈ Icc 1 N, F n ≤ x * Real.exp 64 := by
      calc ∑ n ∈ Icc 1 N, F n ≤ (N : ℝ) * ∏ p ∈ P, (1 + g p / p) :=
            sum_prod_one_add_le N T g hg
        _ ≤ x * Real.exp 64 := by
            gcongr
            · exact prod_nonneg (fun p _ => by have := hg p; positivity)
            · exact Nat.floor_le hx0
    have hSsub : S ⊆ Icc 1 N := filter_subset _ _
    calc (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, Real.exp (-T) * F n := sum_le_sum hrank
      _ ≤ ∑ n ∈ Icc 1 N, Real.exp (-T) * F n :=
          sum_le_sum_of_subset_of_nonneg hSsub (fun n _ _ => by
            have := hF0 n; positivity)
      _ = Real.exp (-T) * ∑ n ∈ Icc 1 N, F n := by rw [mul_sum]
      _ ≤ Real.exp (-T) * (x * Real.exp 64) := by gcongr
      _ ≤ Real.exp (-T) * (x * Real.exp K) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hK64) hx0) (Real.exp_pos _).le
      _ = Real.exp K * x * Real.exp (-T) := by ring

end DuffinSchaeffer
