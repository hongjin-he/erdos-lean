import ErdosLean.DuffinSchaeffer.Parts.UnitPairCount
import ErdosLean.DuffinSchaeffer.Parts.CoprimeSieve

/-!
# Duffin–Schaeffer — Part 9: the overlap estimate (KM Lemma 5.3, Pollington–Vaughan)

For `q ≠ r`:
`λ(A_q ∩ A_r) ≪ w(q) w(r) ∏_{p | qr/gcd², p > M(q,r)/gcd(q,r)} (1 + 1/p)`.
No restriction `ψ ≤ 1/2` is needed (KM assume it only because they cite PV).
Proof: union bound over arcs, `λ(I_a ∩ J_b) ≤ 2 min(ψ(q)/q, ψ(r)/r)`, nonzero only if
`h = a r' - b q'` has `0 < |h| < (rψ(q) + qψ(r))/g ≤ 2M/g`; count with `card_unit_pairs_le`
and sum over `h` with `sieve_weighted_coprime`; primes `p ≤ (M/g)` cancel against `m/φ(m)`.
-/

open MeasureTheory Finset

namespace DuffinSchaeffer

/-- Two balls in `ℝ/ℤ` intersect in measure at most `2 min(δ, ε)`. -/
theorem ovl_ball_inter_le (x y : UnitAddCircle) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume.real (Metric.ball x δ ∩ Metric.ball y ε) ≤ 2 * min δ ε := by
  have key : ∀ (z : UnitAddCircle) (η : ℝ), 0 ≤ η → volume.real (Metric.ball z η) ≤ 2 * η := by
    intro z η hη
    calc volume.real (Metric.ball z η) ≤ volume.real (Metric.closedBall z η) :=
          measureReal_mono Metric.ball_subset_closedBall
      _ = min 1 (2 * η) := by
          rw [measureReal_def, AddCircle.volume_closedBall,
            ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]
      _ ≤ 2 * η := min_le_right _ _
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  exact le_min ((measureReal_mono Set.inter_subset_left).trans (key x δ hδ))
    ((measureReal_mono Set.inter_subset_right).trans (key y ε hε))

/-- `A_q ∩ A_r` is covered by the intersections of arcs around `a/q`, `b/r` whose centres are
at distance `< ψ(q)/q + ψ(r)/r`. -/
theorem ovl_cover (ψ : ℕ → ℝ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    Aq ψ q ∩ Aq ψ r ⊆ ⋃ ab ∈ ((range q ×ˢ range r).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        dist (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) <
          ψ q / q + ψ r / r)),
      Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (ψ q / q) ∩
        Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) (ψ r / r) := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨b1, hb1, hxb1⟩ := mem_approx_add_orderOf_iff.1 hx1
  obtain ⟨b2, hb2, hxb2⟩ := mem_approx_add_orderOf_iff.1 hx2
  obtain ⟨a, ha, hag, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hq).1 hb1
  obtain ⟨b, hb, hbg, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hr).1 hb2
  simp only [mul_one] at hxb1 hxb2
  refine Set.mem_biUnion (x := (a, b)) ?_ ⟨hxb1, hxb2⟩
  refine mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 ha, mem_range.2 hb⟩, hag, hbg, ?_⟩
  rw [Metric.mem_ball] at hxb1 hxb2
  calc dist _ _ ≤ dist (((a : ℝ) / q : ℝ) : UnitAddCircle) x +
        dist x (((b : ℝ) / r : ℝ) : UnitAddCircle) := dist_triangle _ _ _
    _ < _ := add_lt_add (by rw [dist_comm]; exact hxb1) hxb2

/-- `a/q - b/r = (a r' - b q') / lcm(q,r)`. -/
theorem ovl_arith (q r a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (a : ℝ) / q - b / r =
      (((a : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (b : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) : ℤ) : ℝ) /
        (Nat.lcm q r : ℝ) := by
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have h1 : ((Nat.gcd q r : ℕ) : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) = q := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have h2 : ((Nat.gcd q r : ℕ) : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) = r := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have h3 : ((Nat.gcd q r : ℕ) : ℝ) * (Nat.lcm q r : ℝ) = q * r := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  have hgR : ((Nat.gcd q r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hL : (Nat.lcm q r : ℝ) = q * r / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h3
  have hq' : ((q / Nat.gcd q r : ℕ) : ℝ) = q / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h1
  have hr' : ((r / Nat.gcd q r : ℕ) : ℝ) = r / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h2
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    Int.cast_natCast, Int.cast_natCast, hq', hr', hL]
  field_simp

/-- Telescoping: `∏_{n=2}^{N} (1 - 1/n²) = (N+1)/(2N)`. -/
theorem ovl_prod_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∏ n ∈ Icc 2 N, (1 - 1 / (n : ℝ) ^ 2) = ((N : ℝ) + 1) / (2 * (N : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by norm_num)]; norm_num
  | succ N hN ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have : (0:ℝ) < N := by exact_mod_cast hN
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- `∏_{p ∈ S} (1 - 1/p²) ≥ 1/2` for any finite set of integers `≥ 2`. -/
theorem ovl_prod_ge_half (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (1:ℝ) / 2 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := by
  set N := max (S.sup id) 1 with hN
  have hsub : S ⊆ Icc 2 N := fun p hp =>
    mem_Icc.2 ⟨hS p hp, le_max_of_le_left (le_sup (f := id) hp)⟩
  have hf0 : ∀ n ∈ Icc 2 N, 0 ≤ 1 - 1 / (n : ℝ) ^ 2 := by
    intro n hn
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hf1 : ∀ n ∈ Icc 2 N, 1 - 1 / (n : ℝ) ^ 2 ≤ 1 := by
    intro n _
    exact sub_le_self _ (by positivity)
  have h := ovl_prod_Icc N (le_max_right _ _)
  rw [← prod_sdiff hsub] at h
  have hA : ∏ n ∈ Icc 2 N \ S, (1 - 1 / (n : ℝ) ^ 2) ≤ 1 :=
    prod_le_one₀ (fun n hn => hf0 n (sdiff_subset hn)) (fun n hn => hf1 n (sdiff_subset hn))
  have hB : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := prod_nonneg fun p hp => hf0 p (hsub hp)
  have hNpos : (1:ℝ) ≤ N := by exact_mod_cast le_max_right (S.sup id) 1
  have hC : (1:ℝ) / 2 ≤ ((N : ℝ) + 1) / (2 * (N : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  calc (1:ℝ) / 2 ≤ ((N : ℝ) + 1) / (2 * (N : ℝ)) := hC
    _ = (∏ n ∈ Icc 2 N \ S, (1 - 1 / (n : ℝ) ^ 2)) * ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := h.symm
    _ ≤ 1 * ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hA hB
    _ = _ := one_mul _

/-- `(m/φ(m)) ∏_{p | m, p ≤ H} (1 - 1/p) ≤ 2 ∏_{p | m, p > X} (1 + 1/p)` whenever `X ≤ H`. -/
theorem ovl_euler (m : ℕ) (hm : 0 < m) (X H : ℝ) (hXH : X ≤ H) :
    (m : ℝ) / Nat.totient m *
        ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) ≤
      2 * ∏ p ∈ m.primeFactors.filter (fun p : ℕ => X < (p : ℝ)), (1 + 1 / (p : ℝ)) := by
  have htot : (Nat.totient m : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - (1 : ℝ) / p) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors m)
    push_cast at this
    simpa [one_div] using this
  have hpos : ∀ p ∈ m.primeFactors, 0 < 1 - (1 : ℝ) / p := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  set S := m.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ H) with hSdef
  set A := ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) with hAdef
  set B := ∏ p ∈ S, (1 - (1 : ℝ) / p) with hBdef
  have hAB : ∏ p ∈ m.primeFactors, (1 - (1 : ℝ) / p) = A * B :=
    (prod_filter_mul_prod_filter_not _ _ _).symm
  have hA : 0 < A := prod_pos fun p hp => hpos p (mem_filter.1 hp).1
  have hB : 0 < B := prod_pos fun p hp => hpos p (mem_filter.1 hp).1
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hlhs : (m : ℝ) / Nat.totient m * A = 1 / B := by
    rw [htot, hAB]
    field_simp
  rw [hlhs, div_le_iff₀ hB]
  set T := m.primeFactors.filter (fun p : ℕ => X < (p : ℝ)) with hTdef
  have hST : S ⊆ T := by
    intro p hp
    rw [hSdef, mem_filter] at hp
    rw [hTdef, mem_filter]
    exact ⟨hp.1, lt_of_le_of_lt hXH (not_le.1 hp.2)⟩
  have hone : ∀ p ∈ T, (1:ℝ) ≤ 1 + 1 / (p : ℝ) := fun p _ => le_add_of_nonneg_right (by positivity)
  have hTS : (1:ℝ) ≤ ∏ p ∈ T \ S, (1 + 1 / (p : ℝ)) := by
    calc (1:ℝ) = ∏ _p ∈ T \ S, (1:ℝ) := prod_const_one.symm
      _ ≤ ∏ p ∈ T \ S, (1 + 1 / (p : ℝ)) :=
        prod_le_prod₀ (fun _ _ => zero_le_one) (fun p hp => hone p (sdiff_subset hp))
  have hSnn : 0 ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := prod_nonneg fun p _ => by positivity
  have hQ : ∏ p ∈ S, (1 + 1 / (p : ℝ)) ≤ ∏ p ∈ T, (1 + 1 / (p : ℝ)) := by
    rw [← prod_sdiff hST]
    calc ∏ p ∈ S, (1 + 1 / (p : ℝ)) = 1 * ∏ p ∈ S, (1 + 1 / (p : ℝ)) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hTS hSnn
  have hSB : (∏ p ∈ S, (1 + 1 / (p : ℝ))) * B = ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [hBdef, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    ring
  have hhalf := ovl_prod_ge_half S (fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).two_le)
  calc (1:ℝ) ≤ 2 * ((∏ p ∈ S, (1 + 1 / (p : ℝ))) * B) := by rw [hSB]; linarith
    _ ≤ 2 * ((∏ p ∈ T, (1 + 1 / (p : ℝ))) * B) := by
        have := mul_le_mul_of_nonneg_right hQ hB.le
        linarith
    _ = 2 * (∏ p ∈ T, (1 + 1 / (p : ℝ))) * B := by ring

theorem measure_inter_Aq_le : ∃ C : ℝ, 0 < C ∧ ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q) →
    ∀ q r : ℕ, 0 < q → 0 < r → q ≠ r →
      volume.real (Aq ψ q ∩ Aq ψ r) ≤ C * weight ψ q * weight ψ r * Pfac ψ q r := by
  obtain ⟨Cs, hCs, hsieve⟩ := sieve_weighted_coprime
  refine ⟨16 * Cs, by positivity, ?_⟩
  intro ψ hψ q r hq hr hqr
  -- basic arithmetic
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have hq' : 0 < q / Nat.gcd q r :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hg
  have hr' : 0 < r / Nat.gcd q r :=
    Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hg
  have hm : 0 < coprimePart q r := Nat.mul_pos hq' hr'
  have hm1 : coprimePart q r ≠ 1 := by
    intro h
    unfold coprimePart at h
    rw [mul_eq_one] at h
    have e1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
    have e2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
    rw [h.1, mul_one] at e1
    rw [h.2, mul_one] at e2
    exact hqr (e1.symm.trans e2)
  have hgR : (0:ℝ) < Nat.gcd q r := by exact_mod_cast hg
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hLpos : (0:ℝ) < Nat.lcm q r := by exact_mod_cast Nat.lcm_pos hq hr
  have hLR : (Nat.lcm q r : ℝ) = q * r / Nat.gcd q r := by
    have h3 : ((Nat.gcd q r : ℕ) : ℝ) * (Nat.lcm q r : ℝ) = q * r := by
      exact_mod_cast Nat.gcd_mul_lcm q r
    rw [eq_div_iff hgR.ne', mul_comm]; exact h3
  have hφm : (0:ℝ) < Nat.totient (coprimePart q r) := by exact_mod_cast Nat.totient_pos.2 hm
  have hδq0 : 0 ≤ ψ q / q := div_nonneg (hψ q) hqR.le
  have hδr0 : 0 ≤ ψ r / r := div_nonneg (hψ r) hrR.le
  -- the main quantities
  set δq : ℝ := ψ q / q with hδq
  set δr : ℝ := ψ r / r with hδr
  set H : ℝ := (δq + δr) * (Nat.lcm q r : ℝ) with hH
  set N : ℕ := ⌊H⌋₊ with hN
  set K : ℝ := (Nat.gcd q r : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient r : ℝ) / r) *
    ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hH0 : 0 ≤ H := mul_nonneg (add_nonneg hδq0 hδr0) hLpos.le
  set P := (range q ×ˢ range r).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        dist (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) <
          δq + δr) with hP
  -- Step 1: union bound
  have step1 : volume.real (Aq ψ q ∩ Aq ψ r) ≤ (P.card : ℝ) * (2 * min δq δr) := by
    calc volume.real (Aq ψ q ∩ Aq ψ r)
        ≤ volume.real (⋃ ab ∈ P, Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) δq ∩
            Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) δr) :=
          measureReal_mono (ovl_cover ψ q r hq hr) (measure_ne_top _ _)
      _ ≤ ∑ ab ∈ P, volume.real (Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) δq ∩
            Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) δr) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ab ∈ P, 2 * min δq δr := sum_le_sum fun ab _ => ovl_ball_inter_le _ _ hδq0 hδr0
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  -- Step 2: counting via `h = a r' - b q' (mod lcm)`
  set F : ℕ × Bool → Finset (ℕ × ℕ) := fun ns =>
    ((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (ab.2 : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) ≡
          (if ns.2 then (ns.1 : ℤ) else -(ns.1 : ℤ)) [ZMOD (Nat.lcm q r : ℤ)]) with hF
  have hsub : P ⊆ (range (N + 1) ×ˢ (univ : Finset Bool)).biUnion F := by
    rintro ⟨a, b⟩ hab
    rw [hP, mem_filter] at hab
    obtain ⟨hab0, hc1, hc2, hd⟩ := hab
    simp only at hc1 hc2 hd
    set x : ℤ := (a : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (b : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ)
      with hx
    have ht : (a : ℝ) / q - b / r = (x : ℝ) / (Nat.lcm q r : ℝ) := ovl_arith q r a b hq hr
    have hnorm : dist (((a : ℝ) / q : ℝ) : UnitAddCircle) (((b : ℝ) / r : ℝ) : UnitAddCircle) =
        |((a : ℝ) / q - b / r) - round ((a : ℝ) / q - b / r)| := by
      rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
    set k := round ((a : ℝ) / q - b / r) with hk
    set z : ℤ := x - k * (Nat.lcm q r : ℤ) with hz
    have hzR : (z : ℝ) = ((a : ℝ) / q - b / r - k) * Nat.lcm q r := by
      rw [hz]
      push_cast
      rw [ht]
      field_simp
    have habs : |(z : ℝ)| < H := by
      rw [hzR, abs_mul, abs_of_pos hLpos]
      rw [hnorm] at hd
      exact mul_lt_mul_of_pos_right hd hLpos
    have hnN : z.natAbs ≤ N := by
      apply Nat.le_floor
      have : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [this]
      exact habs.le
    have hmod : x ≡ z [ZMOD (Nat.lcm q r : ℤ)] :=
      Int.modEq_iff_dvd.2 ⟨-k, by rw [hz]; ring⟩
    rw [mem_biUnion]
    by_cases h0 : 0 ≤ z
    · refine ⟨(z.natAbs, true), mem_product.2 ⟨mem_range.2 (by omega), mem_univ _⟩, ?_⟩
      rw [hF, mem_filter]
      refine ⟨hab0, hc1, hc2, ?_⟩
      have : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg h0
      simp only [ite_true, this]
      exact hmod
    · refine ⟨(z.natAbs, false), mem_product.2 ⟨mem_range.2 (by omega), mem_univ _⟩, ?_⟩
      rw [hF, mem_filter]
      refine ⟨hab0, hc1, hc2, ?_⟩
      have : -((z.natAbs : ℕ) : ℤ) = z := by
        rw [Int.natCast_natAbs, abs_of_neg (not_le.1 h0), neg_neg]
      simp only [Bool.false_eq_true, ite_false, this]
      exact hmod
  set Bf : ℕ → ℝ := fun n => (if Nat.gcd n (coprimePart q r) = 1 then 1 else 0) *
      (K * ((Nat.gcd n (Nat.gcd q r) : ℝ) / Nat.totient (Nat.gcd n (Nat.gcd q r)))) with hBf
  have hBn : ∀ (n : ℕ) (s : Bool), ((F (n, s)).card : ℝ) ≤ Bf n := by
    intro n s
    have := card_unit_pairs_le q r hq hr (if s then (n : ℤ) else -(n : ℤ))
    have e1 : Int.gcd (if s then (n : ℤ) else -(n : ℤ)) ((coprimePart q r : ℕ) : ℤ) =
        Nat.gcd n (coprimePart q r) := by cases s <;> simp
    have e2 : Int.gcd (if s then (n : ℤ) else -(n : ℤ)) ((Nat.gcd q r : ℕ) : ℤ) =
        Nat.gcd n (Nat.gcd q r) := by cases s <;> simp
    rw [e1, e2] at this
    exact this
  have step2 : (P.card : ℝ) ≤ ∑ n ∈ range (N + 1), 2 * Bf n := by
    calc (P.card : ℝ) ≤ (((range (N + 1) ×ˢ (univ : Finset Bool)).biUnion F).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ ns ∈ range (N + 1) ×ˢ (univ : Finset Bool), ((F ns).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ n ∈ range (N + 1), ∑ s ∈ (univ : Finset Bool), ((F (n, s)).card : ℝ) :=
          sum_product _ _ _
      _ ≤ ∑ n ∈ range (N + 1), ∑ _s ∈ (univ : Finset Bool), Bf n :=
          sum_le_sum fun n _ => sum_le_sum fun s _ => hBn n s
      _ = ∑ n ∈ range (N + 1), 2 * Bf n := by
          refine sum_congr rfl fun n _ => ?_
          rw [sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
          norm_num
  -- Step 3: reduce to the sieve sum over `1 ≤ n ≤ N`
  set S := ∑ h ∈ (Icc 1 ⌊H⌋₊).filter (fun h => Nat.Coprime h (coprimePart q r)),
    ((Nat.gcd h (Nat.gcd q r) : ℝ) / Nat.totient (Nat.gcd h (Nat.gcd q r))) with hS
  have step3 : ∑ n ∈ range (N + 1), 2 * Bf n = 2 * K * S := by
    have hfilt : (range (N + 1)).filter (fun n => Nat.Coprime n (coprimePart q r)) =
        (Icc 1 ⌊H⌋₊).filter (fun n => Nat.Coprime n (coprimePart q r)) := by
      ext n
      simp only [mem_filter, mem_range, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, by omega⟩, h2⟩
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact absurd (Nat.coprime_zero_left _ |>.1 h2) hm1
        · exact hpos
      · rintro ⟨⟨_, h1'⟩, h2⟩
        exact ⟨by omega, h2⟩
    rw [hS, ← hfilt, sum_filter, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    simp only [hBf, Nat.Coprime]
    split_ifs <;> ring
  -- Step 4: the sieve
  have hPi0 : 0 ≤ ∏ p ∈ (coprimePart q r).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H),
      (1 - (1 : ℝ) / p) := prod_nonneg fun p hp => by
    have : (1:ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  have step4 : S ≤ Cs * H * ∏ p ∈ (coprimePart q r).primeFactors.filter
      (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) := by
    by_cases h1 : 1 ≤ H
    · exact hsieve _ _ H hm hg h1
    · have hN0 : ⌊H⌋₊ = 0 := Nat.floor_eq_zero.2 (not_le.1 h1)
      rw [hS, hN0, Finset.Icc_eq_empty (by norm_num), filter_empty, sum_empty]
      exact mul_nonneg (mul_nonneg hCs.le hH0) hPi0
  -- Step 5: algebra
  have hmin : min δq δr * H ≤ 2 * δq * δr * Nat.lcm q r := by
    have : min δq δr * (δq + δr) ≤ 2 * δq * δr := by
      rcases le_total δq δr with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    rw [hH, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right this hLpos.le
  have hid : K * δq * δr * Nat.lcm q r =
      weight ψ q * weight ψ r * ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) := by
    rw [hK, hδq, hδr, hLR]
    unfold weight
    field_simp
  have hX : Mqr ψ q r / Nat.gcd q r ≤ H := by
    have hH' : H = (r * ψ q + q * ψ r) / Nat.gcd q r := by
      rw [hH, hδq, hδr, hLR]
      field_simp
    rw [hH']
    apply div_le_div_of_nonneg_right _ hgR.le
    unfold Mqr
    exact max_le (le_add_of_nonneg_right (mul_nonneg hqR.le (hψ r)))
      (le_add_of_nonneg_left (mul_nonneg hrR.le (hψ q)))
  have hE := ovl_euler (coprimePart q r) hm (Mqr ψ q r / Nat.gcd q r) H hX
  have hW0 : 0 ≤ weight ψ q * weight ψ r := by
    unfold weight
    have := hψ q
    have := hψ r
    positivity
  have hmin0 : 0 ≤ min δq δr := le_min hδq0 hδr0
  set Pi1 := ∏ p ∈ (coprimePart q r).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H),
      (1 - (1 : ℝ) / p) with hPi1
  calc volume.real (Aq ψ q ∩ Aq ψ r) ≤ (P.card : ℝ) * (2 * min δq δr) := step1
    _ ≤ (2 * K * S) * (2 * min δq δr) := by
        rw [← step3]; exact mul_le_mul_of_nonneg_right step2 (by positivity)
    _ ≤ (2 * K * (Cs * H * Pi1)) * (2 * min δq δr) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left step4 (by positivity)
    _ = 4 * Cs * K * Pi1 * (min δq δr * H) := by ring
    _ ≤ 4 * Cs * K * Pi1 * (2 * δq * δr * Nat.lcm q r) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = 8 * Cs * Pi1 * (K * δq * δr * Nat.lcm q r) := by ring
    _ = 8 * Cs * (weight ψ q * weight ψ r) *
          ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r) * Pi1) := by rw [hid]; ring
    _ ≤ 8 * Cs * (weight ψ q * weight ψ r) * (2 * Pfac ψ q r) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 16 * Cs * weight ψ q * weight ψ r * Pfac ψ q r := by ring

end DuffinSchaeffer
