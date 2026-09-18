import ErdosLean.DuffinSchaeffer.Parts.EdgeBound
import ErdosLean.DuffinSchaeffer.Parts.Mertens

/-!
# Duffin–Schaeffer — Part 19: the pair sum (KM (5.7), end of §5)

`∑_{q ≠ r ∈ [X,Y]} w(q) w(r) P(q,r) ≪ 1` whenever `∑_{[X,Y]} w ≤ 2`.
Split by `P(q,r) < e^{100}`; otherwise pick `j` maximal with `L_{exp exp j}(q,r) ≥ 10`,
bound `P(q,r) ≪ e^j` (Mertens) and use Prop. 5.4 with `t = exp exp j`; `∑_j e^j / exp exp j < ∞`.
No hypothesis `ψ ≤ 1/2` is needed.

(We split at `P(q,r) < e^{200}` instead of `e^{100}`, which makes the
constants in the Mertens step comfortable.)
-/

open Finset

namespace DuffinSchaeffer

/-- `t_j = exp(exp j)`. -/
noncomputable def alt_tt (j : ℕ) : ℝ := Real.exp (Real.exp j)

theorem alt_tt_ge_two (j : ℕ) : 2 ≤ alt_tt j := by
  unfold alt_tt
  have h1 : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (Nat.cast_nonneg j)
  have h2 : Real.exp 1 ≤ Real.exp (Real.exp j) := Real.exp_le_exp.2 h1
  have h3 := Real.exp_one_gt_d9
  linarith

theorem alt_log_tt (j : ℕ) : Real.log (alt_tt j) = Real.exp j := by
  unfold alt_tt; exact Real.log_exp _

/-- Split a sum of `1/p` at a threshold `T`. -/
theorem alt_sum_split (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (T : ℝ) :
    ∑ p ∈ S.filter P, (1 : ℝ) / p ≤
      ∑ p ∈ (S.filter P).filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p +
        ∑ p ∈ S.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 : ℝ) / p := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter P) (fun p : ℕ => (p : ℝ) < T)]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, not_lt] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  · intro p _ _
    positivity

/-- Primes `p | m` with `s < p < T`, `2 ≤ s ≤ T`, via Mertens. -/
theorem alt_sum_mid_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (s T : ℝ) (hs : 2 ≤ s)
    (hsT : s ≤ T) :
    ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter (fun p : ℕ => (p : ℝ) < T),
        (1 : ℝ) / p ≤ Real.log (Real.log T / Real.log s) + 100 / Real.log s := by
  refine le_trans ?_ (sum_inv_prime_Ioc_le s T hs hsT)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨⟨hpS, hsp⟩, hpT⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨(Nat.floor_lt (by linarith)).2 hsp, Nat.le_floor hpT.le⟩, hS p hpS⟩
  · intro p _ _
    positivity

/-- Primes `p | m` with `p < T`, `2 ≤ T`, via Mertens. -/
theorem alt_sum_low_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (T : ℝ) (hT : 2 ≤ T) :
    ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p ≤
      1 / 2 + (Real.log (Real.log T / Real.log 2) + 100 / Real.log 2) := by
  have hmert := sum_inv_prime_Ioc_le 2 T le_rfl hT
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hfl] at hmert
  have hsub : S.filter (fun p : ℕ => (p : ℝ) < T) ⊆
      {2} ∪ (Ioc 2 ⌊T⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpS, hpT⟩ := Finset.mem_filter.1 hp
    have hp2 := (hS p hpS).two_le
    rcases Nat.eq_or_lt_of_le hp2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_singleton.2 h.symm)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h, ?_⟩, hS p hpS⟩)
      exact Nat.le_floor hpT.le
  have hdisj : Disjoint ({2} : Finset ℕ) ((Ioc 2 ⌊T⌋₊).filter Nat.Prime) := by
    rw [Finset.disjoint_singleton_left]
    simp
  calc ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p
      ≤ ∑ p ∈ {2} ∪ (Ioc 2 ⌊T⌋₊).filter Nat.Prime, (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = 1 / 2 + ∑ p ∈ (Ioc 2 ⌊T⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
        rw [Finset.sum_union hdisj, Finset.sum_singleton]
        norm_num
    _ ≤ 1 / 2 + (Real.log (Real.log T / Real.log 2) + 100 / Real.log 2) := by
        gcongr

/-- The pointwise bound on `P(q,r)`. -/
theorem alt_Pfac_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q r J : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hJ : q * r ≤ J) :
    Pfac ψ q r ≤ Real.exp 200 + ∑ j ∈ range J,
      (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
        then Real.exp 158 * Real.exp j else 0) := by
  classical
  set g := Nat.gcd q r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set m := coprimePart q r with hmdef
  set S := m.primeFactors with hSdef
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hm0 : 0 < m := by
    rw [hmdef, coprimePart]
    apply Nat.mul_pos
    · exact Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hg
    · exact Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hg
  have hmJ : m ≤ J := by
    refine le_trans ?_ hJ
    rw [hmdef, coprimePart]
    exact Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  set s : ℝ := Mqr ψ q r / g with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef, Mqr]
    have := hψ q
    exact div_nonneg (le_trans (by positivity) (le_max_left _ _)) hgR.le
  set σ : ℝ := ∑ p ∈ S.filter (fun p : ℕ => s < (p : ℝ)), (1 : ℝ) / p with hσdef
  have hsumnn : 0 ≤ ∑ j ∈ range J,
      (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
        then Real.exp 158 * Real.exp j else 0) := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  have hP : Pfac ψ q r ≤ Real.exp σ := by
    have h := Real.prod_one_add_le_exp_sum (S.filter (fun p : ℕ => s < (p : ℝ)))
      (f := fun p : ℕ => 1 / (p : ℝ)) (fun p => by positivity)
    exact h
  by_cases hσ : σ < 200
  · have : Real.exp σ ≤ Real.exp 200 := Real.exp_le_exp.2 hσ.le
    linarith
  push Not at hσ
  -- the index `j`
  set good : ℕ → Prop := fun j => 10 ≤ Lsum (alt_tt j) q r with hgood
  have hLsum_def : ∀ t : ℝ, Lsum t q r = ∑ p ∈ S.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p :=
    fun t => rfl
  have hgood0 : good 0 := by
    show 10 ≤ Lsum (alt_tt 0) q r
    have hsplit := alt_sum_split S (fun p : ℕ => s < (p : ℝ)) (alt_tt 0)
    have hlow : ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) < alt_tt 0), (1 : ℝ) / p ≤ 1 / 2 := by
      have hsub : (S.filter (fun p : ℕ => s < (p : ℝ))).filter
          (fun p : ℕ => (p : ℝ) < alt_tt 0) ⊆ {2} := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨⟨hpS, _⟩, hpt⟩ := hp
        have h2 := (hSprime p hpS).two_le
        have ht0 : alt_tt 0 < 3 := by
          unfold alt_tt
          simp only [Nat.cast_zero, Real.exp_zero]
          have := Real.exp_one_lt_d9
          linarith
        have hp3 : (p : ℝ) < 3 := lt_trans hpt ht0
        have : p < 3 := by exact_mod_cast hp3
        exact Finset.mem_singleton.2 (by omega)
      calc _ ≤ ∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ = 1 / 2 := by simp
    rw [hLsum_def]
    linarith
  have hgoodJ : ¬ good J := by
    show ¬ 10 ≤ Lsum (alt_tt J) q r
    rw [hLsum_def]
    have hempty : S.filter (fun p : ℕ => alt_tt J ≤ (p : ℝ)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro p hp hle
      have hpm : p ≤ m := Nat.le_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
      have h1 : (J : ℝ) + 1 ≤ Real.exp J := by
        have := Real.add_one_le_exp (J : ℝ); linarith
      have h2 : Real.exp J + 1 ≤ Real.exp (Real.exp J) := by
        have := Real.add_one_le_exp (Real.exp J); linarith
      have h3 : (p : ℝ) ≤ J := by exact_mod_cast hpm.trans hmJ
      unfold alt_tt at hle
      linarith
    rw [hempty, Finset.sum_empty]
    norm_num
  set j := Nat.findGreatest good J with hjdef
  have hjgood : good j := Nat.findGreatest_spec (Nat.zero_le J) hgood0
  have hjJ : j < J := by
    rcases Nat.lt_or_ge j J with h | h
    · exact h
    · have : j = J := le_antisymm (Nat.findGreatest_le J) h
      rw [this] at hjgood
      exact absurd hjgood hgoodJ
  have hjnext : ¬ good (j + 1) :=
    Nat.findGreatest_is_greatest (Nat.lt_succ_self j) hjJ
  have hLnext : Lsum (alt_tt (j + 1)) q r < 10 := lt_of_not_ge hjnext
  have hsplitj := alt_sum_split S (fun p : ℕ => s < (p : ℝ)) (alt_tt (j + 1))
  rw [← hσdef, ← hLsum_def] at hsplitj
  have hlogt : ∀ i : ℕ, Real.log (alt_tt i) = Real.exp i := alt_log_tt
  have hexpj : Real.exp ((j : ℝ) + 1) = Real.exp 1 * Real.exp j := by
    rw [Real.exp_add, mul_comm]
  -- (a) `s ≤ t_j`
  have hsj : s ≤ alt_tt j := by
    by_contra hcon
    push Not at hcon
    have hs2 : 2 ≤ s := le_trans (alt_tt_ge_two j) hcon.le
    have hmid : ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)), (1 : ℝ) / p ≤ 101 := by
      by_cases hsT : s ≤ alt_tt (j + 1)
      · refine (alt_sum_mid_le S hSprime s (alt_tt (j + 1)) hs2 hsT).trans ?_
        have hlogs : Real.exp j < Real.log s := by
          rw [← hlogt j]
          exact Real.log_lt_log (by linarith [alt_tt_ge_two j]) hcon
        have hej : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (Nat.cast_nonneg j)
        have h1 : Real.log (Real.log (alt_tt (j + 1)) / Real.log s) ≤ 1 := by
          rw [hlogt, Nat.cast_succ, hexpj]
          have hpos : 0 < Real.exp 1 * Real.exp j / Real.log s := div_pos (by positivity) (by linarith)
          have hle : Real.exp 1 * Real.exp j / Real.log s ≤ Real.exp 1 := by
            rw [div_le_iff₀ (by linarith)]
            have := Real.exp_pos 1
            nlinarith
          calc Real.log (Real.exp 1 * Real.exp j / Real.log s) ≤ Real.log (Real.exp 1) :=
                Real.log_le_log hpos hle
            _ = 1 := Real.log_exp 1
        have h2 : 100 / Real.log s ≤ 100 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        linarith
      · push Not at hsT
        have hempty : (S.filter (fun p : ℕ => s < (p : ℝ))).filter
            (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)) = ∅ := by
          apply Finset.filter_eq_empty_iff.2
          intro p hp hpt
          have := (Finset.mem_filter.1 hp).2
          linarith
        rw [hempty, Finset.sum_empty]
        norm_num
    linarith
  -- (b) `σ ≤ 158 + j`
  have hσj : σ ≤ 158 + j := by
    have hlow := alt_sum_low_le S hSprime (alt_tt (j + 1)) (alt_tt_ge_two (j + 1))
    have hsubset : ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)), (1 : ℝ) / p ≤
        ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)), (1 : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1.1, hp.2⟩
      · intro p _ _
        positivity
    have hl2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hlog2pos : 0 < Real.log 2 := by linarith
    have hmert : Real.log (Real.log (alt_tt (j + 1)) / Real.log 2) + 100 / Real.log 2 ≤
        j + 1 + 146 := by
      rw [hlogt, Real.log_div (Real.exp_pos _).ne' hlog2pos.ne', Real.log_exp]
      have h1 : -Real.log (Real.log 2) ≤ 1 := by
        have := Real.one_sub_inv_le_log_of_pos hlog2pos
        have hinv : (Real.log 2)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hlog2pos (by norm_num)]
          linarith
        linarith
      have h2 : 100 / Real.log 2 ≤ 145 := by
        rw [div_le_iff₀ hlog2pos]
        linarith
      push_cast
      linarith
    linarith
  -- assemble
  have hmem : j ∈ range J := Finset.mem_range.2 hjJ
  have hcond : Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r := by
    refine ⟨?_, hjgood⟩
    rw [← hgdef]
    have := (div_le_iff₀ hgR).1 hsj
    linarith
  have hterm := Finset.single_le_sum (f := fun j => (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧
      10 ≤ Lsum (alt_tt j) q r) then Real.exp 158 * Real.exp j else 0))
    (fun i _ => by split_ifs <;> positivity) hmem
  simp only [hcond, and_self, if_true] at hterm
  have hPj : Pfac ψ q r ≤ Real.exp 158 * Real.exp j := by
    refine hP.trans ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 hσj
  have := Real.exp_pos 200
  linarith

/-- `∑_{j < J} e^j / exp(e^j) ≤ 2`. -/
theorem alt_sum_exp_div_le (J : ℕ) :
    ∑ j ∈ range J, Real.exp j / alt_tt j ≤ 2 := by
  refine le_trans ?_ (sum_geometric_two_le J)
  apply Finset.sum_le_sum
  intro j _
  unfold alt_tt
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : 2 * (j : ℝ) ≤ Real.exp j := by
    have := Real.quadratic_le_exp_of_nonneg hj
    nlinarith [sq_nonneg ((j : ℝ) - 1)]
  have h2 : Real.exp j / Real.exp (Real.exp j) ≤ Real.exp (-(j : ℝ)) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  refine h2.trans ?_
  have h3 : Real.exp (-(j : ℝ)) = (Real.exp (-1)) ^ j := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h3]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.exp_one_gt_d9
  norm_num
  linarith

theorem pair_sum_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℕ → ℝ), (∀ q, 0 ≤ ψ q) → ∀ X Y : ℕ, 1 ≤ X →
    ∑ q ∈ Icc X Y, weight ψ q ≤ 2 →
      ∑ q ∈ Icc X Y, ∑ r ∈ Icc X Y,
        (if q = r then 0 else weight ψ q * weight ψ r * Pfac ψ q r) ≤ C := by
  classical
  obtain ⟨C54, hC54, h54⟩ := prop54
  refine ⟨4 * Real.exp 200 + Real.exp 158 * C54 * 2, by positivity, ?_⟩
  intro ψ hψ X Y hX hsum
  set I := Icc X Y with hIdef
  set J := Y * Y with hJdef
  have hw : ∀ q, 0 ≤ weight ψ q := fun q => by
    unfold weight; have := hψ q; positivity
  set c : ℕ → ℝ := fun j => Real.exp 158 * Real.exp j with hcdef
  have hc : ∀ j, 0 ≤ c j := fun j => by positivity
  set B : ℕ → ℕ → ℕ → ℝ := fun j q r =>
    if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
      then weight ψ q * weight ψ r else 0 with hBdef
  have hpt : ∀ q ∈ I, ∀ r ∈ I,
      (if q = r then 0 else weight ψ q * weight ψ r * Pfac ψ q r) ≤
        weight ψ q * weight ψ r * Real.exp 200 + ∑ j ∈ range J, c j * B j q r := by
    intro q hq r hr
    obtain ⟨hXq, hqY⟩ := Finset.mem_Icc.1 hq
    obtain ⟨hXr, hrY⟩ := Finset.mem_Icc.1 hr
    have hww := mul_nonneg (hw q) (hw r)
    have hBnn : ∀ j, 0 ≤ c j * B j q r := fun j => by
      apply mul_nonneg (hc j)
      rw [hBdef]; dsimp only; split_ifs
      · exact hww
      · exact le_rfl
    split_ifs with hqr
    · have := Finset.sum_nonneg (fun j (_ : j ∈ range J) => hBnn j)
      have : 0 ≤ weight ψ q * weight ψ r * Real.exp 200 := by positivity
      linarith
    · have hP := alt_Pfac_le ψ hψ q r J (by omega) (by omega) (Nat.mul_le_mul hqY hrY)
      calc weight ψ q * weight ψ r * Pfac ψ q r
          ≤ weight ψ q * weight ψ r * (Real.exp 200 + ∑ j ∈ range J,
              (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
                then Real.exp 158 * Real.exp j else 0)) := mul_le_mul_of_nonneg_left hP hww
        _ = weight ψ q * weight ψ r * Real.exp 200 + ∑ j ∈ range J, c j * B j q r := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [hBdef, hcdef]
          dsimp only
          split_ifs <;> ring
  have hEt : ∀ j, ∑ q ∈ I, ∑ r ∈ I, B j q r =
      ∑ e ∈ Et ψ X Y (alt_tt j), weight ψ e.1 * weight ψ e.2 := by
    intro j
    rw [Et, Finset.sum_filter, Finset.sum_product]
  have hsq : (∑ q ∈ I, weight ψ q) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ ∑ q ∈ I, weight ψ q := Finset.sum_nonneg fun q _ => hw q
    nlinarith
  calc ∑ q ∈ I, ∑ r ∈ I, (if q = r then 0 else weight ψ q * weight ψ r * Pfac ψ q r)
      ≤ ∑ q ∈ I, ∑ r ∈ I, (weight ψ q * weight ψ r * Real.exp 200 +
          ∑ j ∈ range J, c j * B j q r) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => hpt q hq r hr
    _ = Real.exp 200 * (∑ q ∈ I, weight ψ q) ^ 2 +
          ∑ j ∈ range J, c j * ∑ q ∈ I, ∑ r ∈ I, B j q r := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _
          ring
        · calc ∑ q ∈ I, ∑ r ∈ I, ∑ j ∈ range J, c j * B j q r
              = ∑ q ∈ I, ∑ j ∈ range J, ∑ r ∈ I, c j * B j q r := by
                apply Finset.sum_congr rfl; intro q _; exact Finset.sum_comm
            _ = ∑ j ∈ range J, ∑ q ∈ I, ∑ r ∈ I, c j * B j q r := Finset.sum_comm
            _ = ∑ j ∈ range J, c j * ∑ q ∈ I, ∑ r ∈ I, B j q r := by
                apply Finset.sum_congr rfl; intro j _
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _
                rw [Finset.mul_sum]
    _ ≤ Real.exp 200 * 4 + ∑ j ∈ range J, c j * (C54 / alt_tt j) := by
        gcongr with j hj
        rw [hEt j]
        exact h54 ψ hψ X Y hX hsum (alt_tt j) (by linarith [alt_tt_ge_two j])
    _ = Real.exp 200 * 4 + Real.exp 158 * C54 * ∑ j ∈ range J, Real.exp j / alt_tt j := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [hcdef]; dsimp only
        ring
    _ ≤ Real.exp 200 * 4 + Real.exp 158 * C54 * 2 := by
        gcongr
        exact alt_sum_exp_div_le J
    _ = 4 * Real.exp 200 + Real.exp 158 * C54 * 2 := by ring

end DuffinSchaeffer
