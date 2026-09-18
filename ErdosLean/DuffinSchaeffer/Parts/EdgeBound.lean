import ErdosLean.DuffinSchaeffer.Parts.GoodSubgraph
import ErdosLean.DuffinSchaeffer.Parts.Anatomy

/-!
# Duffin–Schaeffer — Part 18: the edge bound (KM Prop. 6.3 via §7, and Prop. 5.4)

-/

open Finset

namespace DuffinSchaeffer

/-! ### Auxiliary lemmas (racing prover) -/

theorem alt63_prod_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    (∏ p ∈ P, p ^ f p).factorization q = if q ∈ P then f q else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hP p hp).ne_zero),
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (g := fun p => if p = q then f p else 0)]
  · exact Finset.sum_ite_eq' P q f
  · intro p hp
    rw [Nat.factorization_pow, (hP p hp).factorization, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp

theorem alt63_prod_dvd (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : (∏ p ∈ P, p ^ f p) ∣ v := by
  classical
  have h0 : (∏ p ∈ P, p ^ f p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
  rw [← Nat.factorization_le_iff_dvd h0 hv, Finsupp.le_def]
  intro q
  rw [alt63_prod_fact P f hP q]
  split_ifs with hq
  · exact ((hP q hq).pow_dvd_iff_le_factorization hv).1 (hd q hq)
  · exact Nat.zero_le _

theorem alt63_prod_pos (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < ∏ p ∈ P, p ^ f p :=
  Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)

/-- Counting multiples of `a` up to `M`. -/
theorem alt63_card_dvd_le (S : Finset ℕ) (a M : ℕ) (ha : 0 < a)
    (hS : ∀ v ∈ S, 0 < v ∧ a ∣ v ∧ v ≤ M) : (S.card : ℝ) ≤ (M : ℝ) / a := by
  have hinj : Set.InjOn (fun v => v / a) S := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨-, hax, -⟩ := hS x hx
    obtain ⟨-, hay, -⟩ := hS y hy
    rw [← Nat.div_mul_cancel hax, ← Nat.div_mul_cancel hay, hxy]
  have hsub : S.image (fun v => v / a) ⊆ Icc 1 (M / a) := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨hv0, hav, hvM⟩ := hS v hv
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd hv0 hav) ha, Nat.div_le_div_right hvM⟩
  have h1 : S.card ≤ M / a := by
    rw [← Finset.card_image_of_injOn hinj]
    calc (S.image (fun v => v / a)).card ≤ (Icc 1 (M / a)).card := Finset.card_le_card hsub
      _ = M / a := by simp
  calc (S.card : ℝ) ≤ ((M / a : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (M : ℝ) / a := Nat.cast_div_le

/-- `1 - x ≥ e^{-2x}` for `0 ≤ x ≤ 1/2`. -/
theorem alt63_exp_le_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h1 : 0 < 1 - x := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    rw [← div_one (1 : ℝ), one_div_one, ← one_div]
    rw [show (1 : ℝ) - 1 / (1 - x) = -x / (1 - x) by field_simp; ring]
    rw [le_div_iff₀ h1]
    nlinarith
  calc Real.exp (-2 * x) ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.2 (le_trans h3 h2)
    _ = 1 - x := Real.exp_log h1

/-- Uniform lower bound for `∏_{p ∈ S} (1 - p^{-31/30})^{10}`. -/
theorem alt63_zeta_bound : ∃ z0 : ℝ, 0 < z0 ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    z0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((31 : ℝ) / 30)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  set T := ∑' n : ℕ, 1 / (n : ℝ) ^ ((31 : ℝ) / 30)
  refine ⟨Real.exp (-20 * T), Real.exp_pos _, ?_⟩
  intro S hS
  have hx : ∀ p ∈ S, 0 ≤ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ∧ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 / 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    constructor
    · positivity
    · have : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) :=
        Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
  have hST : ∑ p ∈ S, 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ T :=
    hsum.sum_le_tsum S (fun n _ => by positivity)
  calc Real.exp (-20 * T) ≤ Real.exp (-20 * ∑ p ∈ S, 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = ∏ p ∈ S, (Real.exp (-2 * (1 / (p : ℝ) ^ ((31 : ℝ) / 30)))) ^ 10 := by
        rw [Finset.mul_sum, Real.exp_sum]
        apply Finset.prod_congr rfl
        intro p _
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 := by
        apply Finset.prod_le_prod₀
        · intro p _; positivity
        · intro p hp
          obtain ⟨h0, h1⟩ := hx p hp
          exact pow_le_pow_left₀ (Real.exp_pos _).le (alt63_exp_le_one_sub _ h0 h1) 10

/-- `φ(v)/v = ∏_{p | v} (1 - 1/p)` in `ℝ`. -/
theorem alt63_totient_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

/-- Weight bound `w(v) ≤ ψ(v) ∏_{p ∈ P, f(p)=g(p)≥1} (1 - 1/p)` when those primes divide `v`. -/
theorem alt63_weight_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (P : Finset ℕ) (f g : ℕ → ℕ)
    (v : ℕ) (hv : 0 < v) (hdv : ∀ p ∈ P, f p = g p ∧ 1 ≤ f p → p.Prime ∧ p ∣ v) :
    weight ψ v ≤ ψ v * ∏ p ∈ P, (1 - (if f p = g p ∧ 1 ≤ f p then 1 / (p : ℝ) else 0)) := by
  classical
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hw : weight ψ v = ψ v * ∏ p ∈ v.primeFactors, (1 - (p : ℝ)⁻¹) := by
    unfold weight
    rw [alt63_totient_real v]
    field_simp
  have hP : ∏ p ∈ P, (1 - (if f p = g p ∧ 1 ≤ f p then 1 / (p : ℝ) else 0)) =
      ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p _
    split_ifs <;> simp
  have hsub : P.filter (fun p => f p = g p ∧ 1 ≤ f p) ⊆ v.primeFactors := by
    intro p hp
    obtain ⟨hpP, hc⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpp, hpv⟩ := hdv p hpP hc
    exact Nat.mem_primeFactors.2 ⟨hpp, hpv, hv.ne'⟩
  have hle : ∏ p ∈ v.primeFactors, (1 - (p : ℝ)⁻¹) ≤
      ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) := by
    rw [← Finset.prod_sdiff hsub]
    have h1 : ∏ p ∈ v.primeFactors \ P.filter (fun p => f p = g p ∧ 1 ≤ f p),
        (1 - (p : ℝ)⁻¹) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1
        have : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
        linarith
      · intro p _
        have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
        linarith
    have h2 : 0 ≤ ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hp
      have hpp := hdv p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2
      have : (1 : ℝ) ≤ p := by exact_mod_cast hpp.1.one_lt.le
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      linarith
    calc (∏ p ∈ v.primeFactors \ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹)
        ≤ 1 * ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := one_mul _
  rw [hw, hP]
  exact mul_le_mul_of_nonneg_left hle (hψ v)

namespace GCDGraph

theorem alt63_gcd_eq (H : GCDGraph) (hR : H.R = ∅) (e : ℕ × ℕ) (he : e ∈ H.E) :
    Nat.gcd e.1 e.2 = ∏ p ∈ H.P, p ^ min (H.f p) (H.g p) := by
  classical
  obtain ⟨hv, hw⟩ := Finset.mem_product.1 (H.E_sub he)
  have hv0 := H.V_pos _ hv
  have hg0 : Nat.gcd e.1 e.2 ≠ 0 := (Nat.gcd_pos_of_pos_left _ hv0).ne'
  have hp0 : (∏ p ∈ H.P, p ^ min (H.f p) (H.g p)) ≠ 0 :=
    (alt63_prod_pos H.P _ H.P_prime).ne'
  apply Nat.eq_of_factorization_eq hg0 hp0
  intro q
  rw [alt63_prod_fact H.P _ H.P_prime q]
  split_ifs with hq
  · exact H.gcd_E q hq e he
  · rw [Nat.factorization_eq_zero_iff]
    by_contra hc
    push Not at hc
    obtain ⟨hqp, hqd, -⟩ := hc
    have : q ∈ H.R := by
      unfold R
      refine Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨e, he, ?_⟩, hq⟩
      exact Nat.mem_primeFactors.2 ⟨hqp, hqd, hg0⟩
    rw [hR] at this
    exact absurd this (Finset.notMem_empty q)

theorem alt63_X_mul (H : GCDGraph) :
    (∏ p ∈ H.P, p ^ H.fgDist p) * (∏ p ∈ H.P, p ^ min (H.f p) (H.g p)) ^ 2 =
      H.aProd * H.bProd := by
  unfold aProd bProd
  rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  unfold fgDist
  omega

theorem alt63_quality_eq (H : GCDGraph) :
    H.quality = H.density ^ 10 * wsum H.μ H.V * wsum H.μ H.W *
      ((∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p) /
        ((∏ p ∈ H.P, (1 - (if H.f p = H.g p ∧ 1 ≤ H.f p then 1 / (p : ℝ) else 0)) ^ 2) *
          ∏ p ∈ H.P, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  unfold quality qualityFactor
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]

end GCDGraph

/-! ### Deduction of Proposition 6.3 from Proposition 7.1 (KM §7) -/

theorem alt63_Lsum_split (t : ℝ) (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    Lsum t x y ≤ ∑ p ∈ x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p +
      ∑ p ∈ y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p := by
  classical
  unfold Lsum
  have hsub : (coprimePart x y).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ⊆
      x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ∪
        y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpd, -⟩, htp⟩ := hp
    unfold coprimePart at hpd
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
        ⟨hpp, h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)), hx.ne'⟩, htp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
        ⟨hpp, h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)), hy.ne'⟩, htp⟩)
  calc _ ≤ ∑ p ∈ (x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ∪
          y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ))), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := alt84_sum_union_le _ _ _ (fun _ => by positivity)

/-- Counting "bad" multiples of `a` up to `M`. -/
theorem alt63_count (S : Finset ℕ) (a M : ℕ) (ha : 0 < a) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x)
    (hS : ∀ v ∈ S, 0 < v ∧ a ∣ v ∧ v ≤ M ∧ bad (v / a)) :
    (S.card : ℝ) ≤ D * ((M : ℝ) / a) := by
  rcases S.eq_empty_or_nonempty with h | ⟨v0, hv0⟩
  · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hMa : 1 ≤ (M : ℝ) / a := by
    obtain ⟨h0, hd, hM, -⟩ := hS v0 hv0
    rw [le_div_iff₀ haR, one_mul]
    exact_mod_cast (Nat.le_of_dvd h0 hd).trans hM
  have hinj : Set.InjOn (fun v => v / a) S := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨-, hax, -⟩ := hS x hx
    obtain ⟨-, hay, -⟩ := hS y hy
    rw [← Nat.div_mul_cancel hax, ← Nat.div_mul_cancel hay, hxy]
  have hsub : S.image (fun v => v / a) ⊆ (Icc 1 ⌊(M : ℝ) / a⌋₊).filter bad := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨hv0, hav, hvM, hb⟩ := hS v hv
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hv0 hav) ha, ?_⟩, hb⟩
    rw [Nat.floor_div_eq_div]
    exact Nat.div_le_div_right hvM
  calc (S.card : ℝ) = ((S.image (fun v => v / a)).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (((Icc 1 ⌊(M : ℝ) / a⌋₊).filter bad).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ D * ((M : ℝ) / a) := hcount _ hMa

theorem alt63_esum_eq (G : GCDGraph) :
    esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.W) := by
  unfold GCDGraph.density
  rcases eq_or_ne (wsum G.μ G.V * wsum G.μ G.W) 0 with h | h
  · rw [h, mul_zero]
    have := GCDGraph.alt_esum_le G.μ_nonneg G.E_sub
    rw [h] at this
    exact le_antisymm this (GCDGraph.alt_esum_nonneg G.μ_nonneg _)
  · rw [div_mul_cancel₀ _ h]

/-- One fibre `{(v, w) ∈ E}` over a fixed `w`, restricted to bad `v / a`. -/
theorem alt63_fiber (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x)
    (w : ℕ) (F : Finset (ℕ × ℕ)) (hF : ∀ e ∈ F, e ∈ H.E ∧ e.2 = w ∧ bad (e.1 / H.aProd)) :
    (F.card : ℝ) * ψ w ≤ D * t * m / H.aProd := by
  classical
  have ha : 0 < H.aProd := alt63_prod_pos H.P H.f H.P_prime
  have haR : (0 : ℝ) < H.aProd := by exact_mod_cast ha
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · rw [hFe, Finset.card_empty, Nat.cast_zero, zero_mul]; positivity
  set S := F.image Prod.fst with hSdef
  have hSne : S.Nonempty := hFne.image _
  have hvmS : S.max' hSne ∈ S := S.max'_mem hSne
  obtain ⟨e0, he0F, he0v⟩ := Finset.mem_image.1 hvmS
  obtain ⟨he0E, he0w, -⟩ := hF e0 he0F
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have h1 := (hF x hx).2.1
    have h2 := (hF y hy).2.1
    exact Prod.ext hxy (h1.trans h2.symm)
  have hcard : F.card = S.card := (Finset.card_image_of_injOn hinj).symm
  have hcS : (S.card : ℝ) ≤ D * (((S.max' hSne : ℕ) : ℝ) / H.aProd) := by
    apply alt63_count S H.aProd (S.max' hSne) ha bad D hD hcount
    intro v hv
    obtain ⟨e, heF, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨heE, -, hb⟩ := hF e heF
    have hv := (Finset.mem_product.1 (H.E_sub heE)).1
    exact ⟨H.V_pos _ hv, alt63_prod_dvd H.P H.f H.P_prime _ (H.V_pos _ hv).ne'
      (fun p hp => H.dvd_V p hp _ hv), S.le_max' _ (Finset.mem_image_of_mem _ heF), hb⟩
  have hψw : ((S.max' hSne : ℕ) : ℝ) * ψ w ≤ t * m := by
    have h := hM e0 he0E
    unfold Mqr at h
    rw [← he0v, ← he0w]
    exact le_trans (le_max_right _ _) h
  calc (F.card : ℝ) * ψ w = S.card * ψ w := by rw [hcard]
    _ ≤ D * (((S.max' hSne : ℕ) : ℝ) / H.aProd) * ψ w := mul_le_mul_of_nonneg_right hcS (hψ w)
    _ = D / H.aProd * (((S.max' hSne : ℕ) : ℝ) * ψ w) := by ring
    _ ≤ D / H.aProd * (t * m) := mul_le_mul_of_nonneg_left hψw (by positivity)
    _ = D * t * m / H.aProd := by ring

theorem alt63_sum_fst (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x) :
    ∑ e ∈ H.E.filter (fun e => bad (e.1 / H.aProd)), ψ e.2 ≤
      H.W.card * (D * t * m / H.aProd) := by
  classical
  have hmaps : ∀ e ∈ H.E.filter (fun e => bad (e.1 / H.aProd)), e.2 ∈ H.W := fun e he =>
    (Finset.mem_product.1 (H.E_sub (Finset.mem_filter.1 he).1)).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ w ∈ H.W, D * t * m / H.aProd := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.sum_congr rfl (g := fun _ => ψ w)
          (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const, nsmul_eq_mul]
        apply alt63_fiber H ψ hψ t ht m hM bad D hD hcount w
        intro e he
        simp only [Finset.mem_filter] at he
        exact ⟨he.1.1, he.2, he.1.2⟩
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem alt63_sum_snd (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad] :
    ∑ e ∈ H.E.filter (fun e => bad (e.2 / H.bProd)), ψ e.2 ≤
      (H.W.filter (fun w => bad (w / H.bProd))).card * (t * m / H.aProd) := by
  classical
  have hmaps : ∀ e ∈ H.E.filter (fun e => bad (e.2 / H.bProd)),
      e.2 ∈ H.W.filter (fun w => bad (w / H.bProd)) := fun e he =>
    Finset.mem_filter.2 ⟨(Finset.mem_product.1 (H.E_sub (Finset.mem_filter.1 he).1)).2,
      (Finset.mem_filter.1 he).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ w ∈ H.W.filter (fun w => bad (w / H.bProd)), t * m / H.aProd := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.sum_congr rfl (g := fun _ => ψ w)
          (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const, nsmul_eq_mul]
        have h := alt63_fiber H ψ hψ t ht m hM (fun _ => True) 1 zero_le_one
          (fun x hx => by
            rw [Finset.filter_true_of_mem (fun _ _ => trivial), Nat.card_Icc, one_mul]
            simp only [add_tsub_cancel_right]
            exact Nat.floor_le (by linarith))
          w (((H.E.filter (fun e => bad (e.2 / H.bProd))).filter (fun e => e.2 = w)))
          (fun e he => by
            simp only [Finset.mem_filter] at he
            exact ⟨he.1.1, he.2, trivial⟩)
        rwa [one_mul] at h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


/-- (7.2)–(7.5): the quality of a high-degree graph with measure `w` is controlled by
`∑_{E''} ψ(v) ψ(w)`, where `E'' = {(v,w) ∈ E : (v, w₀) ∈ E}`. -/
theorem alt63_quality_le (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hμ : H.μ = weight ψ)
    (z0 : ℝ) (hz0 : 0 < z0) (hz : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      z0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)
    (hδ : 0 < H.density) (hHD : H.HighDegree) (w0 : ℕ) (hw0 : w0 ∈ H.W) :
    H.quality ≤ 100 / 81 / z0 * (∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p) *
      ∑ e ∈ ((H.nbhdW w0) ×ˢ H.W).filter (· ∈ H.E), ψ e.1 * ψ e.2 := by
  classical
  have hq0 := H.alt63_quality_eq
  obtain ⟨hHD1, hHD2⟩ := hHD
  rw [Finset.prod_pow (s := H.P) (n := 2)] at hq0
  set δ := H.density with hδdef
  set SV := wsum H.μ H.V with hSV
  set SW := wsum H.μ H.W with hSW
  set X := ∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p with hX
  set Pi1 := ∏ p ∈ H.P, (1 - (if H.f p = H.g p ∧ 1 ≤ H.f p then 1 / (p : ℝ) else 0)) with hPi1
  set Z := ∏ p ∈ H.P, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 with hZ
  set E2 := ((H.nbhdW w0) ×ˢ H.W).filter (· ∈ H.E) with hE2
  set Sψ := ∑ e ∈ E2, ψ e.1 * ψ e.2 with hSψ
  have hSV0 : 0 < SV := H.wsum_V_pos_of_density_pos hδ
  have hSW0 : 0 < SW := H.wsum_W_pos_of_density_pos hδ
  have hδ1 : δ ≤ 1 := H.density_le_one
  have hX0 : 0 ≤ X := Finset.prod_nonneg (fun p _ => by positivity)
  have hZz : z0 ≤ Z := hz H.P H.P_prime
  have hZ0 : 0 < Z := lt_of_lt_of_le hz0 hZz
  have hPi10 : 0 < Pi1 := by
    apply Finset.prod_pos
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (H.P_prime p hp).two_le
    split_ifs
    · have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
      linarith
    · norm_num
  have hSig0 : 0 ≤ Sψ := Finset.sum_nonneg (fun e _ => mul_nonneg (hψ _) (hψ _))
  have hδ0 : 0 ≤ δ := H.density_nonneg
  have hwl : ∀ v, 0 < v → (∀ p ∈ H.P, H.f p = H.g p ∧ 1 ≤ H.f p → p.Prime ∧ p ∣ v) →
      weight ψ v ≤ ψ v * Pi1 := fun v hv hdv => alt63_weight_le ψ hψ H.P H.f H.g v hv hdv
  clear_value δ SV SW X Pi1 Z E2 Sψ
  -- Claim 1: `μ(E'') ≥ (9δ/10)^2 μ(V) μ(W)`.
  have h1 : (9 * δ / 10 * SV) * (9 * δ / 10 * SW) ≤ esum H.μ E2 := by
    have heq : esum H.μ E2 = ∑ v ∈ H.nbhdW w0, H.μ v * wsum H.μ (H.nbhdV v) := by
      unfold esum wsum GCDGraph.nbhdV
      rw [hE2, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    rw [heq]
    calc (9 * δ / 10 * SV) * (9 * δ / 10 * SW) ≤ wsum H.μ (H.nbhdW w0) * (9 * δ / 10 * SW) :=
          mul_le_mul_of_nonneg_right (hHD2 w0 hw0) (by positivity)
      _ = ∑ v ∈ H.nbhdW w0, H.μ v * (9 * δ / 10 * SW) := by unfold wsum; rw [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
          (hHD1 v (Finset.mem_filter.1 hv).1) (H.μ_nonneg v))
  -- Claim 2: `μ(E'') ≤ Pi1^2 ∑_{E''} ψ ψ`.
  have hwnn : ∀ q, 0 ≤ weight ψ q := fun q =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ _)) (Nat.cast_nonneg _)
  have h2 : esum H.μ E2 ≤ Pi1 ^ 2 * Sψ := by
    unfold esum
    rw [hμ, hSψ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [hE2] at he
    have heE : e ∈ H.E := (Finset.mem_filter.1 he).2
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (H.E_sub heE)
    have hv' : weight ψ e.1 ≤ ψ e.1 * Pi1 :=
      hwl e.1 (H.V_pos _ hv) (fun p hp hc =>
        ⟨H.P_prime p hp, (dvd_pow_self p (by omega : H.f p ≠ 0)).trans (H.dvd_V p hp _ hv)⟩)
    have hw' : weight ψ e.2 ≤ ψ e.2 * Pi1 :=
      hwl e.2 (H.W_pos _ hw) (fun p hp hc =>
        ⟨H.P_prime p hp, (dvd_pow_self p (by omega : H.g p ≠ 0)).trans (H.dvd_W p hp _ hw)⟩)
    calc weight ψ e.1 * weight ψ e.2 ≤ (ψ e.1 * Pi1) * (ψ e.2 * Pi1) :=
          mul_le_mul hv' hw' (hwnn _) (mul_nonneg (hψ _) hPi10.le)
      _ = Pi1 ^ 2 * (ψ e.1 * ψ e.2) := by ring
  -- Claim 3: combine.
  have hA : δ ^ 10 * SV * SW ≤ 100 / 81 * (Pi1 ^ 2 * Sψ) := by
    have hδ10 : δ ^ 10 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ0 hδ1 (by norm_num)
    calc δ ^ 10 * SV * SW ≤ δ ^ 2 * SV * SW := by
          have := mul_le_mul_of_nonneg_right hδ10 (mul_pos hSV0 hSW0).le
          linarith [this]
      _ = 100 / 81 * ((9 * δ / 10 * SV) * (9 * δ / 10 * SW)) := by ring
      _ ≤ 100 / 81 * (Pi1 ^ 2 * Sψ) := by
          apply mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
  rw [hq0]
  have hXZ : 0 ≤ X / (Pi1 ^ 2 * Z) := div_nonneg hX0 (mul_pos (pow_pos hPi10 2) hZ0).le
  calc δ ^ 10 * SV * SW * (X / (Pi1 ^ 2 * Z)) ≤ 100 / 81 * (Pi1 ^ 2 * Sψ) * (X / (Pi1 ^ 2 * Z)) :=
        mul_le_mul_of_nonneg_right hA hXZ
    _ = 100 / 81 * X * Sψ / Z := by field_simp
    _ ≤ 100 / 81 * X * Sψ / z0 := div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) hX0) hSig0) hz0 hZz
    _ = 100 / 81 / z0 * X * Sψ := by ring

/-- The core bound (7.6) plus the case analysis of KM §7, in a uniform form: if every edge has
`B₁(v/a)` or `B₂(w/b)` and the `Bᵢ` have counting densities `Dᵢ`, then `q(G') ≪ (D₁ + D₂) t²`. -/
theorem alt63_qH_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t) (z0 : ℝ)
    (hz0 : 0 < z0) (hz : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      z0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)
    (H : GCDGraph) (hμ : H.μ = weight ψ) (hδ : 0 < H.density) (hR : H.R = ∅)
    (hHD : H.HighDegree) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2)
    (B1 B2 : ℕ → Prop) [DecidablePred B1] [DecidablePred B2] (D1 D2 : ℝ) (hD1 : 0 ≤ D1)
    (hD2 : 0 ≤ D2)
    (hc1 : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter B1).card : ℝ) ≤ D1 * x)
    (hc2 : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter B2).card : ℝ) ≤ D2 * x)
    (hB : ∀ e ∈ H.E, B1 (e.1 / H.aProd) ∨ B2 (e.2 / H.bProd)) :
    H.quality ≤ 100 / 81 / z0 * (D1 + D2) * t ^ 2 := by
  classical
  set m := ∏ p ∈ H.P, p ^ min (H.f p) (H.g p) with hm
  have hM' : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m := fun e he => by
    have := hM e he
    rwa [H.alt63_gcd_eq hR e he] at this
  have hWne : H.W.Nonempty := by
    rcases H.W.eq_empty_or_nonempty with h | h
    · have := H.wsum_W_pos_of_density_pos hδ
      rw [h] at this
      simp [wsum] at this
    · exact h
  have hw0 : H.W.max' hWne ∈ H.W := H.W.max'_mem hWne
  set w0 := H.W.max' hWne with hw0def
  have hw0pos : 0 < w0 := H.W_pos _ hw0
  have hw0R : (0 : ℝ) < w0 := by exact_mod_cast hw0pos
  have ha : 0 < H.aProd := alt63_prod_pos H.P H.f H.P_prime
  have hb : 0 < H.bProd := alt63_prod_pos H.P H.g H.P_prime
  have haR : (0 : ℝ) < H.aProd := by exact_mod_cast ha
  have hbR : (0 : ℝ) < H.bProd := by exact_mod_cast hb
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hq := alt63_quality_le H ψ hψ hμ z0 hz0 hz hδ hHD w0 hw0
  set E2 := ((H.nbhdW w0) ×ˢ H.W).filter (· ∈ H.E) with hE2
  set X := ∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p with hX
  have hX0 : 0 ≤ X := Finset.prod_nonneg (fun p _ => by positivity)
  -- ψ(v) ≤ t m / w₀ on E''
  have hSig1 : ∑ e ∈ E2, ψ e.1 * ψ e.2 ≤ (t * m / w0) * ∑ e ∈ H.E, ψ e.2 := by
    calc ∑ e ∈ E2, ψ e.1 * ψ e.2 ≤ ∑ e ∈ E2, (t * m / w0) * ψ e.2 := by
          apply Finset.sum_le_sum
          intro e he
          apply mul_le_mul_of_nonneg_right _ (hψ _)
          obtain ⟨he1, -⟩ := Finset.mem_filter.1 he
          obtain ⟨hv, -⟩ := Finset.mem_product.1 he1
          have hvw0 : (e.1, w0) ∈ H.E := (Finset.mem_filter.1 hv).2
          have h := hM' _ hvw0
          unfold Mqr at h
          rw [le_div_iff₀ hw0R, mul_comm]
          exact le_trans (le_max_left _ _) h
      _ = (t * m / w0) * ∑ e ∈ E2, ψ e.2 := by rw [Finset.mul_sum]
      _ ≤ (t * m / w0) * ∑ e ∈ H.E, ψ e.2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun e he => (Finset.mem_filter.1 he).2)
            (fun e _ _ => hψ _)
  have hEeq : H.E.filter (fun e => B1 (e.1 / H.aProd)) ∪
      H.E.filter (fun e => B2 (e.2 / H.bProd)) = H.E := by
    rw [← Finset.filter_or]
    exact Finset.filter_true_of_mem hB
  have hSig2 : ∑ e ∈ H.E, ψ e.2 ≤ ∑ e ∈ H.E.filter (fun e => B1 (e.1 / H.aProd)), ψ e.2 +
      ∑ e ∈ H.E.filter (fun e => B2 (e.2 / H.bProd)), ψ e.2 := by
    calc ∑ e ∈ H.E, ψ e.2 = ∑ e ∈ (H.E.filter (fun e => B1 (e.1 / H.aProd)) ∪
          H.E.filter (fun e => B2 (e.2 / H.bProd))), ψ e.2 := by rw [hEeq]
      _ ≤ _ := alt84_sum_union_le _ _ (fun e : ℕ × ℕ => ψ e.2) (fun _ => hψ _)
  have hS1 := alt63_sum_fst H ψ hψ t ht m hM' B1 D1 hD1 hc1
  have hS2 := alt63_sum_snd H ψ hψ t ht m hM' B2
  have hbdvd : ∀ w ∈ H.W, H.bProd ∣ w := fun w hw =>
    alt63_prod_dvd H.P H.g H.P_prime w (H.W_pos w hw).ne' (fun p hp => H.dvd_W p hp w hw)
  have hWc : (H.W.card : ℝ) ≤ (w0 : ℝ) / H.bProd :=
    alt63_card_dvd_le H.W H.bProd w0 hb
      (fun w hw => ⟨H.W_pos w hw, hbdvd w hw, H.W.le_max' w hw⟩)
  have hW2 : ((H.W.filter (fun w => B2 (w / H.bProd))).card : ℝ) ≤
      D2 * ((w0 : ℝ) / H.bProd) := by
    apply alt63_count _ H.bProd w0 hb B2 D2 hD2 hc2
    intro w hw
    obtain ⟨hw, hb2⟩ := Finset.mem_filter.1 hw
    exact ⟨H.W_pos w hw, hbdvd w hw, H.W.le_max' w hw, hb2⟩
  have hXm : X * (m : ℝ) ^ 2 = (H.aProd : ℝ) * H.bProd := by
    have h := congrArg (Nat.cast : ℕ → ℝ) H.alt63_X_mul
    push_cast at h
    rw [hX, hm]
    push_cast
    exact h
  clear_value X E2
  have hK : 0 ≤ 100 / 81 / z0 * X := mul_nonneg (by positivity) hX0
  have htm : 0 ≤ t * m / w0 := div_nonneg (mul_nonneg ht hmR) hw0R.le
  have htma : 0 ≤ t * m / H.aProd := div_nonneg (mul_nonneg ht hmR) haR.le
  have hD1a : 0 ≤ D1 * t * m / H.aProd := div_nonneg (mul_nonneg (mul_nonneg hD1 ht) hmR) haR.le
  calc H.quality ≤ 100 / 81 / z0 * X * ∑ e ∈ E2, ψ e.1 * ψ e.2 := hq
    _ ≤ 100 / 81 / z0 * X * ((t * m / w0) * (H.W.card * (D1 * t * m / H.aProd) +
          (H.W.filter (fun w => B2 (w / H.bProd))).card * (t * m / H.aProd))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact hSig1.trans (mul_le_mul_of_nonneg_left (hSig2.trans (add_le_add hS1 hS2)) htm)
    _ ≤ 100 / 81 / z0 * X * ((t * m / w0) * (((w0 : ℝ) / H.bProd) * (D1 * t * m / H.aProd) +
          (D2 * ((w0 : ℝ) / H.bProd)) * (t * m / H.aProd))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply mul_le_mul_of_nonneg_left _ htm
        exact add_le_add (mul_le_mul_of_nonneg_right hWc hD1a)
          (mul_le_mul_of_nonneg_right hW2 htma)
    _ = 100 / 81 / z0 * (D1 + D2) * t ^ 2 * (X * (m : ℝ) ^ 2 / (H.aProd * H.bProd)) := by
        field_simp
    _ = 100 / 81 / z0 * (D1 + D2) * t ^ 2 := by
        rw [hXm, div_self (mul_pos haR hbR).ne', mul_one]


/-- Proposition 6.3. -/
theorem prop63 : ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℕ → ℝ), (∀ q, 0 ≤ ψ q) → ∀ t : ℝ, 1 ≤ t →
    ∀ G : GCDGraph, G.μ = weight ψ → G.P = ∅ → G.V = G.W → wsum G.μ G.V ≤ 2 →
      (∀ e ∈ G.E, Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2 ∧ 10 ≤ Lsum t e.1 e.2) →
      esum G.μ G.E ≤ C / t := by
  classical
  obtain ⟨c, hc, h71⟩ := GCDGraph.prop71
  obtain ⟨z0, hz0, hz⟩ := alt63_zeta_bound
  obtain ⟨CA, hCA, hA⟩ := card_many_large_prime_factors_le
  have hT0 : 0 < T0 := by unfold T0; positivity
  have hf12 : (0 : ℝ) < (Nat.factorial 12 : ℝ) := by exact_mod_cast Nat.factorial_pos 12
  refine ⟨4 * T0 + 4 + 100 / 81 / z0 / c + 2 * (100 / 81 / z0) * CA * (Nat.factorial 12 : ℝ) / c,
    by positivity, ?_⟩
  intro ψ hψ t ht G hμ hP hVW hS hE
  set K := 100 / 81 / z0 with hKdef
  have hK : 0 < K := by positivity
  have ht0 : 0 < t := by linarith
  have hS0 : 0 ≤ wsum G.μ G.V := GCDGraph.alt_wsum_nonneg G.μ_nonneg _
  have hesum : esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.V) := by
    rw [alt63_esum_eq, hVW]
  have hqG : G.quality = G.density ^ 9 * esum G.μ G.E := by
    unfold GCDGraph.quality
    rw [hP, Finset.prod_empty, hesum, hVW]
    ring
  have hδ0 : 0 ≤ G.density := G.density_nonneg
  have hδ1 : G.density ≤ 1 := G.density_le_one
  have hE0 : 0 ≤ esum G.μ G.E := GCDGraph.alt_esum_nonneg G.μ_nonneg _
  have hSS0 : 0 ≤ wsum G.μ G.V * wsum G.μ G.V := mul_nonneg hS0 hS0
  have hSS : wsum G.μ G.V * wsum G.μ G.V ≤ 4 := by nlinarith
  have hE4 : esum G.μ G.E ≤ 4 := by
    rw [hesum]
    calc G.density * (wsum G.μ G.V * wsum G.μ G.V) ≤ 1 * 4 :=
          mul_le_mul hδ1 hSS hSS0 zero_le_one
      _ = 4 := one_mul 4
  have hB1 : 0 ≤ K / c := by positivity
  have hB2 : 0 ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) / c := by positivity
  rw [le_div_iff₀ ht0]
  -- trivial cases
  by_cases htT : t ≤ T0
  · have : esum G.μ G.E * t ≤ 4 * T0 :=
      mul_le_mul hE4 htT ht0.le (by norm_num)
    linarith
  push Not at htT
  by_cases hδt : G.density * t < 1
  · have : esum G.μ G.E * t ≤ 4 := by
      rw [hesum]
      calc G.density * (wsum G.μ G.V * wsum G.μ G.V) * t =
            (G.density * t) * (wsum G.μ G.V * wsum G.μ G.V) := by ring
        _ ≤ 1 * 4 := mul_le_mul hδt.le hSS hSS0 zero_le_one
        _ = 4 := one_mul 4
    linarith
  push Not at hδt
  have hδpos : 0 < G.density := by
    rcases hδ0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hδt; linarith
  have h10 : 10 * G.density ^ (-(1 : ℝ) / 50) ≤ t := by
    have hs0 : 0 < G.density ^ (-(1 : ℝ) / 50) := Real.rpow_pos_of_pos hδpos _
    have hs50 : (G.density ^ (-(1 : ℝ) / 50)) ^ (50 : ℕ) = G.density⁻¹ := by
      rw [← Real.rpow_mul_natCast hδpos.le,
        show (-(1 : ℝ) / 50 * ((50 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    have hs50t : (G.density ^ (-(1 : ℝ) / 50)) ^ (50 : ℕ) ≤ t := by
      rw [hs50]
      calc G.density⁻¹ ≤ G.density⁻¹ * (G.density * t) :=
            le_mul_of_one_le_right (inv_nonneg.2 hδ0) hδt
        _ = t := by field_simp
    by_contra hcon
    push Not at hcon
    have h1 : t / 10 < G.density ^ (-(1 : ℝ) / 50) := by linarith
    have h2 : (t / 10) ^ (50 : ℕ) < (G.density ^ (-(1 : ℝ) / 50)) ^ (50 : ℕ) :=
      pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    have h3 : t ≤ (t / 10) ^ (50 : ℕ) := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have ht49 : (10 : ℝ) ^ 50 ≤ t ^ (49 : ℕ) := by
        have h1' : (10 : ℝ) ^ 50 ≤ T0 := by
          unfold T0; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
        have h2' : t ≤ t ^ (49 : ℕ) := le_self_pow₀ ht (by norm_num)
        linarith
      calc t * 10 ^ 50 ≤ t * t ^ 49 := mul_le_mul_of_nonneg_left ht49 ht0.le
        _ = t ^ 50 := by ring
    linarith
  have hL : ∀ e ∈ G.E, 10 ≤ Lsum t e.1 e.2 := fun e he => (hE e he).2
  obtain ⟨G', hs, hδ', hR', hHD', hcase⟩ := h71 G t hP hδpos hL h10 htT
  have hμ' : G'.μ = weight ψ := hs.1.trans hμ
  have hM' : ∀ e ∈ G'.E, Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2 := fun e he =>
    (hE e (hs.2.2.2.1 he)).1
  have hu9 : 1 ≤ (G.density * t) ^ 9 := one_le_pow₀ hδt
  rcases hcase with h | h
  · -- Case (d)-(i)
    have hq' := alt63_qH_le ψ hψ t ht0.le z0 hz0 hz G' hμ' hδ' hR' hHD' hM'
      (fun _ => False) (fun _ => True) 0 1 le_rfl zero_le_one
      (fun x _ => by simp)
      (fun x hx => by
        rw [Finset.filter_true_of_mem (fun _ _ => trivial), Nat.card_Icc, one_mul]
        simp only [add_tsub_cancel_right]
        exact Nat.floor_le (by linarith))
      (fun e _ => Or.inr trivial)
    have hu : 1 ≤ (G.density * t) ^ 10 := one_le_pow₀ hδt
    have hcE : 0 ≤ c * esum G.μ G.E * t ^ 40 :=
      mul_nonneg (mul_nonneg hc.le hE0) (by positivity)
    have hA1 : c * esum G.μ G.E * t ^ 40 * (G.density * t) ^ 10 ≤ K * t ^ 2 := by
      have h' := h.trans hq'
      rw [hqG] at h'
      calc c * esum G.μ G.E * t ^ 40 * (G.density * t) ^ 10 =
            c * G.density * t ^ 50 * (G.density ^ 9 * esum G.μ G.E) := by ring
        _ ≤ K * (0 + 1) * t ^ 2 := h'
        _ = K * t ^ 2 := by ring
    have hA2 : c * esum G.μ G.E * t ^ 40 ≤ K * t ^ 2 :=
      le_trans (le_mul_of_one_le_right hcE hu) hA1
    have hA3 : c * esum G.μ G.E * t ^ 38 ≤ K := by
      have h' : (c * esum G.μ G.E * t ^ 38) * t ^ 2 ≤ K * t ^ 2 := by
        calc (c * esum G.μ G.E * t ^ 38) * t ^ 2 = c * esum G.μ G.E * t ^ 40 := by ring
          _ ≤ _ := hA2
      exact le_of_mul_le_mul_right h' (by positivity)
    have hA4 : c * (esum G.μ G.E * t) ≤ K := by
      have h' : t ≤ t ^ 38 := le_self_pow₀ ht (by norm_num)
      calc c * (esum G.μ G.E * t) ≤ c * (esum G.μ G.E * t ^ 38) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h' hE0) hc.le
        _ = c * esum G.μ G.E * t ^ 38 := by ring
        _ ≤ K := hA3
    have : esum G.μ G.E * t ≤ K / c := by
      rw [le_div_iff₀ hc]; linarith
    have : (0 : ℝ) ≤ 4 * T0 := by positivity
    linarith
  · -- Case (d)-(ii)
    set bad : ℕ → Prop := fun n : ℕ =>
      (2 : ℝ) ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p with hbad
    set D := CA * Real.exp (-(t ^ Real.exp (2 - 1))) with hD
    have hD0 : 0 ≤ D := by positivity
    have hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x := by
      intro x hx
      have h' := hA x t 2 hx ht (by norm_num) (by norm_num)
      calc (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ CA * x * Real.exp (-(t ^ Real.exp (2 - 1))) := by
            convert h' using 3
        _ = D * x := by rw [hD]; ring
    have hB : ∀ e ∈ G'.E, bad (e.1 / G'.aProd) ∨ bad (e.2 / G'.bProd) := by
      intro e he
      have hL4 := h.2 e he
      obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G'.E_sub he)
      have hx : 0 < e.1 / G'.aProd :=
        Nat.div_pos (Nat.le_of_dvd (G'.V_pos _ hv) (alt63_prod_dvd G'.P G'.f G'.P_prime _
          (G'.V_pos _ hv).ne' (fun p hp => G'.dvd_V p hp _ hv)))
          (alt63_prod_pos G'.P G'.f G'.P_prime)
      have hy : 0 < e.2 / G'.bProd :=
        Nat.div_pos (Nat.le_of_dvd (G'.W_pos _ hw) (alt63_prod_dvd G'.P G'.g G'.P_prime _
          (G'.W_pos _ hw).ne' (fun p hp => G'.dvd_W p hp _ hw)))
          (alt63_prod_pos G'.P G'.g G'.P_prime)
      have hsplit := alt63_Lsum_split t _ _ hx hy
      by_contra hcon
      simp only [hbad, not_or, not_le] at hcon
      linarith [hcon.1, hcon.2]
    have hq' := alt63_qH_le ψ hψ t ht0.le z0 hz0 hz G' hμ' hδ' hR' hHD' hM'
      bad bad D D hD0 hD0 hcount hcount hB
    have hEq : esum G.μ G.E ≤ t ^ 9 * G.quality := by
      rw [hqG]
      calc esum G.μ G.E = 1 * esum G.μ G.E := (one_mul _).symm
        _ ≤ (G.density * t) ^ 9 * esum G.μ G.E := mul_le_mul_of_nonneg_right hu9 hE0
        _ = t ^ 9 * (G.density ^ 9 * esum G.μ G.E) := by ring
    have hexp : Real.exp (-(t ^ Real.exp (2 - 1))) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.2
      have : t ≤ t ^ Real.exp (2 - 1) :=
        Real.self_le_rpow_of_one_le ht (Real.one_le_exp (by norm_num))
      linarith
    have hfac : t ^ 12 * Real.exp (-t) ≤ (Nat.factorial 12 : ℝ) := by
      have h' := Real.pow_div_factorial_le_exp _ ht0.le 12
      rw [div_le_iff₀ hf12] at h'
      calc t ^ 12 * Real.exp (-t) ≤ Real.exp t * (Nat.factorial 12 : ℝ) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
        _ = (Nat.factorial 12 : ℝ) * (Real.exp t * Real.exp (-t)) := by ring
        _ = (Nat.factorial 12 : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hmain : c * (esum G.μ G.E * t) ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) := by
      calc c * (esum G.μ G.E * t) ≤ c * (t ^ 9 * G.quality * t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEq ht0.le) hc.le
        _ = t ^ 10 * (c * G.quality) := by ring
        _ ≤ t ^ 10 * (K * (D + D) * t ^ 2) :=
            mul_le_mul_of_nonneg_left (h.1.trans hq') (by positivity)
        _ = 2 * K * CA * (t ^ 12 * Real.exp (-(t ^ Real.exp (2 - 1)))) := by rw [hD]; ring
        _ ≤ 2 * K * CA * (t ^ 12 * Real.exp (-t)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
    have : esum G.μ G.E * t ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) / c := by
      rw [le_div_iff₀ hc]; linarith
    have : (0 : ℝ) ≤ 4 * T0 := by positivity
    linarith

/-- Proposition 5.4 (second moment bound on `E_t`). -/
theorem prop54 : ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℕ → ℝ), (∀ q, 0 ≤ ψ q) → ∀ X Y : ℕ, 1 ≤ X →
    ∑ q ∈ Icc X Y, weight ψ q ≤ 2 → ∀ t : ℝ, 1 ≤ t →
      ∑ e ∈ Et ψ X Y t, weight ψ e.1 * weight ψ e.2 ≤ C / t := by
  obtain ⟨C, hC, h63⟩ := prop63
  refine ⟨C, hC, ?_⟩
  intro ψ hψ X Y hX hsum t ht
  let G : GCDGraph :=
    { μ := weight ψ
      V := Icc X Y
      W := Icc X Y
      E := Et ψ X Y t
      P := ∅
      f := fun _ => 0
      g := fun _ => 0
      μ_nonneg := fun q => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ _)) (Nat.cast_nonneg _)
      V_pos := fun v hv => by have := (Finset.mem_Icc.1 hv).1; omega
      W_pos := fun v hv => by have := (Finset.mem_Icc.1 hv).1; omega
      E_sub := Finset.filter_subset _ _
      P_prime := fun p hp => absurd hp (Finset.notMem_empty p)
      dvd_V := fun p hp => absurd hp (Finset.notMem_empty p)
      dvd_W := fun p hp => absurd hp (Finset.notMem_empty p)
      gcd_E := fun p hp => absurd hp (Finset.notMem_empty p)
      exact_V := fun p hp => absurd hp (Finset.notMem_empty p)
      exact_W := fun p hp => absurd hp (Finset.notMem_empty p) }
  exact h63 ψ hψ t ht G rfl rfl rfl hsum (fun e he => (Finset.mem_filter.1 he).2)

end DuffinSchaeffer
