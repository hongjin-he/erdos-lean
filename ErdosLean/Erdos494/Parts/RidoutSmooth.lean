import ErdosLean.Erdos494.Defs
import ErdosLean.Erdos494.Parts.DysonBinomial

/-! # Erdős 494, part D2: the Ridout special case needed by [GFS62], via Mahler's trick.

Claim: for coprime `P`-smooth `x, y`, `|x - y| ≥ max(x,y)^{1-δ}` once `max(x,y)` is large.
(GFS quote Ridout's `p`-adic Thue–Siegel–Roth theorem; we only need an *archimedean*
approximation theorem with exponent `o(r)` for `r`-th roots of rationals.)

Proof from `dyson_binomial`: fix `r` with `r δ ≥ 10 √r + 2`.  Write `x = a u^r`, `y = b v^r`
with `a, b` `r`-th-power-free `P`-smooth (finitely many choices: `a ∣ ∏_{p<P} p^{r-1}`).
If infinitely many bad pairs exist, pigeonhole fixes `(a,b)`; then
`|(u/v)^r - b/a| ≤ |x-y|/(a v^r) ≤ C v^{-rδ}` and, as `|α^r - β^r| ≥ |α - β| β^{r-1}`,
`|u/v - (b/a)^{1/r}| ≤ C' v^{-rδ} < v^{-(10√r)}` for `v` large; `u/v ≠ (b/a)^{1/r}` since
`x ≠ y` (coprime, `max > 1`).  Distinct pairs give distinct `(u,v)`, contradicting
`dyson_binomial`. -/

namespace Erdos494

/-- Mahler decomposition: a `P`-smooth `x` is `a * u ^ r` with `a` bounded in terms of `P, r`. -/
lemma ridout_decomp (P r : ℕ) (hr : 0 < r) (x : ℕ) (hx : x ∈ Nat.smoothNumbers P) :
    ∃ a u : ℕ, 0 < a ∧ a ≤ ((P + 1) ^ r) ^ P ∧ 0 < u ∧ x = a * u ^ r := by
  have hx0 : x ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hx
  have hsub : x.primeFactors ⊆ Finset.range P :=
    ((Nat.mem_smoothNumbers_iff_primeFactors_subset.1 hx).2).trans (Finset.filter_subset _ _)
  refine ⟨∏ p ∈ x.primeFactors, p ^ (x.factorization p % r),
    ∏ p ∈ x.primeFactors, p ^ (x.factorization p / r), ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · calc ∏ p ∈ x.primeFactors, p ^ (x.factorization p % r)
          ≤ ∏ _p ∈ x.primeFactors, (P + 1) ^ r := by
            apply Finset.prod_le_prod' fun p hp => ?_
            have hpP : p < P := Finset.mem_range.1 (hsub hp)
            have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
            calc p ^ (x.factorization p % r) ≤ p ^ r :=
                  Nat.pow_le_pow_right hp1 (Nat.mod_lt _ hr).le
              _ ≤ (P + 1) ^ r := Nat.pow_le_pow_left (by omega) _
        _ = ((P + 1) ^ r) ^ x.primeFactors.card := Finset.prod_const _
        _ ≤ ((P + 1) ^ r) ^ P := by
            apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (by positivity))
            simpa using Finset.card_le_card hsub
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hx0]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, ← pow_add, mul_comm (x.factorization p / r) r, Nat.mod_add_div]

/-- `|α - β| β^(n-1) ≤ |α^n - β^n|` for `α, β ≥ 0`, `n ≥ 1`. -/
lemma ridout_pow_sub_pow (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) (hn : 1 ≤ n) :
    |α - β| * β ^ (n - 1) ≤ |α ^ n - β ^ n| := by
  rw [← geom_sum₂_mul, abs_mul, mul_comm]
  gcongr
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
  have := Finset.single_le_sum (f := fun i => α ^ i * β ^ (n - 1 - i))
    (fun i _ => by positivity) h0
  simpa using this

/-- The core estimate, with `y` the larger number. -/
lemma ridout_core (P : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ x y : ℕ, x ∈ Nat.smoothNumbers P → y ∈ Nat.smoothNumbers P →
      Nat.Coprime x y → x ≤ y → B < y →
      ((y : ℕ) : ℝ) ^ (1 - δ) ≤ |(x : ℝ) - y| := by
  -- parameters
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 10 / δ < k := exists_nat_gt _
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hkN : 0 < k := by exact_mod_cast hk0
  set r : ℕ := k ^ 2 with hr_def
  have hr : 0 < r := by positivity
  set κ : ℝ := 10 * k with hκ_def
  set ε : ℝ := 10 / k with hε_def
  have hεδ : ε < δ := by
    rw [hε_def, div_lt_iff₀ hk0]; rw [div_lt_iff₀ hδ] at hk; linarith
  have hε0 : 0 < ε := by positivity
  have hκ : 10 * Real.sqrt r ≤ κ := by
    rw [hr_def]; push_cast; rw [Real.sqrt_sq hk0.le]
  set A0 : ℕ := ((P + 1) ^ r) ^ P with hA0
  have hA0pos : 0 < A0 := by positivity
  have hA0R : (1 : ℝ) ≤ A0 := by exact_mod_cast hA0pos
  -- the finite exceptional set, uniformly over `a, b ≤ A0`
  set S : Set (ℤ × ℕ) := ⋃ a ∈ Finset.Icc 1 A0, ⋃ b ∈ Finset.Icc 1 A0,
    {pq : ℤ × ℕ | 0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ binRoot r a b ∧
        |binRoot r a b - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)} with hS
  have hSfin : S.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun a ha => ?_
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun b hb => ?_
    have ha' := (Finset.mem_Icc.1 ha).1
    have hb' := (Finset.mem_Icc.1 hb).1
    exact dyson_binomial r a b hr ha' hb' κ hκ
  set N : ℕ := hSfin.toFinset.sup (fun pq => pq.2) with hN
  set T : ℝ := ((A0 : ℝ) ^ 2) ^ (1 / (δ - ε)) with hT
  refine ⟨⌈T⌉₊ + A0 * N ^ r + 1, by omega, ?_⟩
  intro x y hx hy hxy hxy' hB
  by_contra hbad
  push Not at hbad
  obtain ⟨a, u, ha0, haA, hu0, rfl⟩ := ridout_decomp P r hr x hx
  obtain ⟨b, v, hb0, hbA, hv0, rfl⟩ := ridout_decomp P r hr y hy
  -- x ≠ y
  have hne : a * u ^ r ≠ b * v ^ r := by
    intro h
    rw [h, Nat.coprime_self] at hxy
    omega
  set β : ℝ := binRoot r a b with hβ
  have hβ0 : 0 ≤ β := Real.rpow_nonneg (by positivity) _
  have hβr : β ^ r = (b : ℝ) / a := by
    rw [hβ, binRoot, one_div]
    exact Real.rpow_inv_natCast_pow (by positivity) hr.ne'
  have huv_ne : (u : ℝ) / v ≠ β := by
    intro h
    apply hne
    have h2 : ((u : ℝ) / v) ^ r = (b : ℝ) / a := by rw [h, hβr]
    have hv : (v : ℝ) ≠ 0 := by positivity
    have ha : (a : ℝ) ≠ 0 := by positivity
    rw [div_pow, div_eq_div_iff (by positivity) ha] at h2
    exact_mod_cast (by linarith : (a : ℝ) * u ^ r = b * v ^ r)
  -- (u, v) is not exceptional
  have hnotS : ((u : ℤ), v) ∉ S := by
    intro hmem
    have hle : v ≤ N := by
      rw [hN]
      exact Finset.le_sup (f := fun pq : ℤ × ℕ => pq.2) (hSfin.mem_toFinset.2 hmem)
    have : b * v ^ r ≤ A0 * N ^ r := Nat.mul_le_mul hbA (Nat.pow_le_pow_left hle _)
    omega
  have hlow : (v : ℝ) ^ (-κ) ≤ |β - (u : ℝ) / v| := by
    by_contra hlt
    push Not at hlt
    apply hnotS
    rw [hS]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨a, ⟨ha0, haA⟩, b, ⟨hb0, hbA⟩, hv0, ?_, ?_⟩
    · push_cast; exact huv_ne
    · push_cast; exact hlt
  -- analytic chain
  set w : ℝ := (v : ℝ) ^ r with hw
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv0
  have hw0 : 0 < w := by positivity
  have hwκ : (v : ℝ) ^ (-κ) = w ^ (-ε) := by
    rw [hw, ← Real.rpow_natCast_mul (by positivity)]
    congr 1
    rw [hr_def, hκ_def, hε_def]; push_cast; field_simp
  set M : ℝ := ((b * v ^ r : ℕ) : ℝ) with hM
  have hMw : M = b * w := by rw [hM, hw]; push_cast; ring
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  set D : ℝ := |((a * u ^ r : ℕ) : ℝ) - ((b * v ^ r : ℕ) : ℝ)| with hD
  -- β^(r-1) ≥ 1/A0
  have hβr1 : 1 / (A0 : ℝ) ≤ β ^ (r - 1) := by
    rcases le_or_gt 1 β with h | h
    · calc 1 / (A0 : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hA0R
        _ ≤ β ^ (r - 1) := one_le_pow₀ h
    · calc 1 / (A0 : ℝ) ≤ (b : ℝ) / a := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have : (1 : ℝ) ≤ b := by exact_mod_cast hb0
            have : (a : ℝ) ≤ A0 := by exact_mod_cast haA
            nlinarith
        _ = β ^ r := hβr.symm
        _ ≤ β ^ (r - 1) := pow_le_pow_of_le_one hβ0 h.le (by omega)
  -- |α^r - β^r| = D / (a w)
  have hdiff : |((u : ℝ) / v) ^ r - β ^ r| = D / (a * w) := by
    rw [hβr, hD, div_pow, hw]
    have hv : (v : ℝ) ≠ 0 := by positivity
    have ha : (a : ℝ) ≠ 0 := by positivity
    rw [div_sub_div _ _ (pow_ne_zero _ hv) ha, abs_div, abs_of_pos (show (0:ℝ) < v ^ r * a by positivity)]
    congr 1
    · push_cast; congr 1; ring
    · ring
  have hstep : w ^ (-ε) ≤ A0 * D / w := by
    rw [← hwκ]
    refine hlow.trans ?_
    have key := ridout_pow_sub_pow ((u : ℝ) / v) β (by positivity) hβ0 r hr
    rw [hdiff, abs_sub_comm] at key
    have hpos : 0 < β ^ (r - 1) := lt_of_lt_of_le (by positivity) hβr1
    rw [← le_div_iff₀ hpos] at key
    refine key.trans ?_
    rw [div_le_iff₀ hpos]
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hD0 : 0 ≤ D := abs_nonneg _
    calc D / (a * w) ≤ D / w := by
          apply div_le_div_of_nonneg_left hD0 hw0; nlinarith
      _ = (A0 * D / w) * (1 / A0) := by field_simp
      _ ≤ A0 * D / w * β ^ (r - 1) := by gcongr
  -- w^(1-ε) ≤ A0 D
  have h1 : w ^ (1 - ε) ≤ A0 * D := by
    rw [sub_eq_add_neg, Real.rpow_add hw0, Real.rpow_one]
    rw [le_div_iff₀ hw0] at hstep
    linarith
  have hbadD : D < M ^ (1 - δ) := hbad
  have hMA : M ≤ A0 * w := by
    rw [hMw]; gcongr
  have h1ε : 0 ≤ 1 - ε := by linarith
  have h2 : M ^ (1 - ε) ≤ A0 * w ^ (1 - ε) := by
    calc M ^ (1 - ε) ≤ ((A0 : ℝ) * w) ^ (1 - ε) :=
          Real.rpow_le_rpow (by linarith) hMA h1ε
      _ = (A0 : ℝ) ^ (1 - ε) * w ^ (1 - ε) := Real.mul_rpow (by positivity) hw0.le
      _ ≤ (A0 : ℝ) ^ (1 : ℝ) * w ^ (1 - ε) := by
          gcongr
          · linarith
      _ = A0 * w ^ (1 - ε) := by rw [Real.rpow_one]
  have hM0 : 0 < M := by linarith
  have h3 : M ^ (δ - ε) * M ^ (1 - δ) < (A0 : ℝ) ^ 2 * M ^ (1 - δ) := by
    rw [← Real.rpow_add hM0, show δ - ε + (1 - δ) = 1 - ε by ring]
    calc M ^ (1 - ε) ≤ A0 * w ^ (1 - ε) := h2
      _ ≤ A0 * (A0 * D) := by gcongr
      _ < A0 * (A0 * M ^ (1 - δ)) := by gcongr
      _ = (A0 : ℝ) ^ 2 * M ^ (1 - δ) := by ring
  have h4 : M ^ (δ - ε) < (A0 : ℝ) ^ 2 :=
    lt_of_mul_lt_mul_right h3 (Real.rpow_nonneg hM0.le _)
  have hMT : T < M := by
    have : (⌈T⌉₊ : ℝ) < M := by
      rw [hM]; exact_mod_cast (show ⌈T⌉₊ < b * v ^ r by omega)
    exact lt_of_le_of_lt (Nat.le_ceil T) this
  have hδε : 0 < δ - ε := by linarith
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  have h5 : T ^ (δ - ε) < M ^ (δ - ε) := Real.rpow_lt_rpow hT0 hMT hδε
  rw [hT, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hδε.ne', Real.rpow_one] at h5
  linarith

end Erdos494

namespace Erdos494

theorem ridout_smooth (P : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, ∀ x y : ℕ, x ∈ Nat.smoothNumbers P → y ∈ Nat.smoothNumbers P →
      Nat.Coprime x y → B < max x y →
      ((max x y : ℕ) : ℝ) ^ (1 - δ) ≤ |(x : ℝ) - y| := by
  rcases lt_or_ge δ 1 with hδ1 | hδ1
  · obtain ⟨B, hB1, hB⟩ := ridout_core P δ hδ hδ1
    refine ⟨B, fun x y hx hy hxy hBm => ?_⟩
    rcases le_total x y with h | h
    · rw [max_eq_right h] at hBm ⊢
      exact hB x y hx hy hxy h hBm
    · rw [max_eq_left h] at hBm ⊢
      rw [abs_sub_comm]
      exact hB y x hy hx hxy.symm h hBm
  · refine ⟨1, fun x y hx hy hxy hBm => ?_⟩
    have hne : x ≠ y := by
      rintro rfl
      rw [Nat.coprime_self] at hxy
      subst hxy
      simp at hBm
    have hx0 := Nat.ne_zero_of_mem_smoothNumbers hx
    have hy0 := Nat.ne_zero_of_mem_smoothNumbers hy
    have hm1 : (1 : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ max x y)
    calc ((max x y : ℕ) : ℝ) ^ (1 - δ) ≤ ((max x y : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ = 1 := Real.rpow_zero _
      _ ≤ |(x : ℝ) - y| := by
          rcases lt_or_gt_of_ne hne with h | h
          · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            linarith
          · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
            rw [abs_of_nonneg (by linarith)]
            linarith

end Erdos494
