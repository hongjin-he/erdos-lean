import ErdosLean.DuffinSchaeffer.Parts.SmallPrimes
import ErdosLean.DuffinSchaeffer.Parts.SharpPrimes
import ErdosLean.DuffinSchaeffer.Parts.RemoveR

/-!
# Duffin–Schaeffer — Part 17: existence of a good GCD subgraph (KM Prop. 7.1, proof in §8)

Stages 1, 2, 3a/3b, 4b of KM §8: Prop 8.3, then iterate Prop 8.1
(strong induction on `#R(G)`), then either iterate Props 8.1/8.2 (case (a)) or Lemma 8.4 and then
iterate Props 8.1/8.2 (case (b)); finish with Lemma 8.5 (`exists_highDegree_subgraph`).
-/

open Finset

namespace DuffinSchaeffer

/-! ### Auxiliary lemmas (racing prover) -/

theorem alt71_extract {δ q δ' q' X : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hq' : 0 ≤ q')
    (h : X ≤ min 1 (δ' / δ) * (q' / q)) : X * q ≤ q' ∧ X * (δ * q) ≤ δ' * q' := by
  have hr : 0 ≤ q' / q := div_nonneg hq' hq.le
  have h1 : X ≤ q' / q := by
    refine le_trans h ?_
    have := min_le_left 1 (δ' / δ)
    calc min 1 (δ' / δ) * (q' / q) ≤ 1 * (q' / q) := mul_le_mul_of_nonneg_right this hr
      _ = q' / q := one_mul _
  have h2 : X ≤ δ' / δ * (q' / q) :=
    le_trans h (mul_le_mul_of_nonneg_right (min_le_right _ _) hr)
  constructor
  · rwa [le_div_iff₀ hq] at h1
  · rw [div_mul_div_comm, le_div_iff₀ (mul_pos hδ hq)] at h2
    exact h2

theorem alt71_prod_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
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

theorem alt71_prod_dvd (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : (∏ p ∈ P, p ^ f p) ∣ v := by
  classical
  have h0 : (∏ p ∈ P, p ^ f p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
  rw [← Nat.factorization_le_iff_dvd h0 hv, Finsupp.le_def]
  intro q
  rw [alt71_prod_fact P f hP q]
  split_ifs with hq
  · exact ((hP q hq).pow_dvd_iff_le_factorization hv).1 (hd q hq)
  · exact Nat.zero_le _

theorem alt71_div_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) (q : ℕ) :
    (v / ∏ p ∈ P, p ^ f p).factorization q = v.factorization q - (if q ∈ P then f q else 0) := by
  rw [Nat.factorization_div (alt71_prod_dvd P f hP v hv hd), Finsupp.tsub_apply,
    alt71_prod_fact P f hP q]

theorem alt71_div_pos (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : 0 < v)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : 0 < v / ∏ p ∈ P, p ^ f p := by
  have h0 : 0 < (∏ p ∈ P, p ^ f p) :=
    Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)
  exact Nat.div_pos (Nat.le_of_dvd hv (alt71_prod_dvd P f hP v hv.ne' hd)) h0

theorem alt71_not_dvd (v w p : ℕ) (hv : 0 < v) (hw : 0 < w) (hp : p.Prime)
    (h : v.factorization p = w.factorization p) : ¬ p ∣ coprimePart v w := by
  intro hdvd
  have hv0 : v ≠ 0 := hv.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hg : (Nat.gcd v w).factorization p = v.factorization p := by
    rw [Nat.factorization_gcd hv0 hw0, Finsupp.inf_apply, h, inf_idem]
  have h1 : (v / Nat.gcd v w).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left v w), Finsupp.tsub_apply, hg, Nat.sub_self]
  have h2 : (w / Nat.gcd v w).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_right v w), Finsupp.tsub_apply, hg, h, Nat.sub_self]
  have hvg0 : v / Nat.gcd v w ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  have hwg0 : w / Nat.gcd v w ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'
  unfold coprimePart at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hd | hd
  · rcases (Nat.factorization_eq_zero_iff _ _).1 h1 with h' | h' | h'
    · exact h' hp
    · exact h' hd
    · exact hvg0 h'
  · rcases (Nat.factorization_eq_zero_iff _ _).1 h2 with h' | h' | h'
    · exact h' hp
    · exact h' hd
    · exact hwg0 h'

theorem alt71_dvd_cp (v w p : ℕ) (hv : 0 < v) (hw : 0 < w)
    (h : v.factorization p ≠ w.factorization p) : p ∣ coprimePart v w := by
  have hv0 : v ≠ 0 := hv.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hg : (Nat.gcd v w).factorization p = min (v.factorization p) (w.factorization p) := by
    rw [Nat.factorization_gcd hv0 hw0, Finsupp.inf_apply]
  unfold coprimePart
  rcases lt_or_gt_of_ne h with hlt | hlt
  · apply dvd_mul_of_dvd_right
    apply Nat.dvd_of_factorization_pos
    rw [Nat.factorization_div (Nat.gcd_dvd_right v w), Finsupp.tsub_apply, hg]
    omega
  · apply dvd_mul_of_dvd_left
    apply Nat.dvd_of_factorization_pos
    rw [Nat.factorization_div (Nat.gcd_dvd_left v w), Finsupp.tsub_apply, hg]
    omega

theorem alt71_coprimePart_ne_zero (v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    coprimePart v w ≠ 0 := by
  unfold coprimePart
  apply Nat.mul_ne_zero
  · exact (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  · exact (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'

/-- If `2^N < t^50` and `t > 10^2000` then `N ≤ t`. -/
theorem alt71_N_le (t : ℝ) (ht : T0 < t) (N : ℕ) (h : (2 : ℝ) ^ N < t ^ (50 : ℕ)) :
    (N : ℝ) ≤ t := by
  have hT : (30000 : ℝ) ≤ T0 := by
    unfold T0
    calc (30000 : ℝ) ≤ 10 ^ 5 := by norm_num
      _ ≤ 10 ^ 2000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have ht0 : 0 < t := by linarith
  by_contra hN
  push Not at hN
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hl2 := Real.log_two_gt_d9
  have hs : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht0.le]; ring
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hs1 := Real.log_le_sub_one_of_pos hsq0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hN2 : t * Real.log 2 < (N : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hN (Real.log_pos (by norm_num))
  push_cast at hl
  -- t log 2 < 50 log t ≤ 100 (√t - 1) < 100 √t
  have key : Real.sqrt t * Real.sqrt t * 0.69 < 100 * Real.sqrt t := by nlinarith
  have hsqt : Real.sqrt t < 145 := by nlinarith
  nlinarith

namespace GCDGraph

theorem alt71_newUnequal_le {H2 H1 H : GCDGraph} (h21 : H2.IsSubgraph H1) :
    newUnequal H2 H ≤ newUnequal H2 H1 + newUnequal H1 H := by
  classical
  unfold newUnequal
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hp ⊢
  obtain ⟨⟨hp2, hpH⟩, hne⟩ := hp
  by_cases hp1 : p ∈ H1.P
  · right
    obtain ⟨hf, hg⟩ := h21.2.2.2.2.2 p hp1
    refine ⟨⟨hp1, hpH⟩, ?_⟩
    rwa [← hf, ← hg]
  · left
    exact ⟨⟨hp2, hp1⟩, hne⟩

theorem alt71_newUnequal_self (H : GCDGraph) : newUnequal H H = 0 := by
  unfold newUnequal
  simp

theorem alt71_sharp_of_flat (H : GCDGraph) (hflat : H.Rflat = ∅) (p : ℕ) (hp : p ∈ H.R) :
    p ∈ H.Rsharp := by
  classical
  have := (Finset.filter_eq_empty_iff.1 hflat) hp
  unfold Rsharp
  exact Finset.mem_filter.2 ⟨hp, by simpa using this⟩

/-- Iterating Props 8.1/8.2 until `R = ∅` (Stages 3a / 4b). -/
theorem alt71_iterate : ∀ n : ℕ, ∀ H : GCDGraph, H.R.card = n → 0 < H.density →
    (∀ p ∈ H.R, T0 < (p : ℝ)) →
    ∃ H' : GCDGraph, H'.IsSubgraph H ∧ 0 < H'.density ∧ H'.R = ∅ ∧
      H.quality ≤ H'.quality ∧ H'.P ⊆ H.P ∪ H.R := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hδ hR
  by_cases h0 : H.R = ∅
  · exact ⟨H, IsSubgraph.refl H, hδ, h0, le_rfl, Finset.subset_union_left⟩
  have hne : H.R.Nonempty := Finset.nonempty_iff_ne_empty.2 h0
  obtain ⟨H1, hs1, hδ1, -, hPR1, hR1, hq1⟩ : ∃ H1 : GCDGraph, H1.IsSubgraph H ∧
      0 < H1.density ∧ H.P ⊂ H1.P ∧ H1.P ⊆ H.P ∪ H.R ∧ H1.R ⊂ H.R ∧
      H.quality ≤ H1.quality := by
    by_cases hf : H.Rflat.Nonempty
    · obtain ⟨H1, a, b, c, d, e, f⟩ := prop81 H hδ hR hf
      refine ⟨H1, a, b, c, d, e, ?_⟩
      have hq0 := (H.quality_pos_iff).2 hδ
      have hq1 := H1.quality_nonneg
      have := (alt71_extract hδ hq0 hq1 f).1
      have h2 : (1 : ℝ) ≤ 2 ^ newUnequal H1 H := one_le_pow₀ (by norm_num)
      nlinarith
    · have hflat : H.Rflat = ∅ := Finset.not_nonempty_iff_eq_empty.1 hf
      have hsharp : H.Rsharp.Nonempty := by
        obtain ⟨p, hp⟩ := hne
        exact ⟨p, alt71_sharp_of_flat H hflat p hp⟩
      obtain ⟨H1, a, b, c, d, e, f⟩ := prop82 H hδ hR hflat hsharp
      exact ⟨H1, a, b, c, d, e, f⟩
  have hR1' : ∀ p ∈ H1.R, T0 < (p : ℝ) := fun p hp => hR p (hR1.subset hp)
  obtain ⟨H2, hs2, hδ2, hR2, hq2, hP2⟩ :=
    ih H1.R.card (hn ▸ Finset.card_lt_card hR1) H1 rfl hδ1 hR1'
  refine ⟨H2, hs2.trans hs1, hδ2, hR2, hq1.trans hq2, ?_⟩
  intro p hp
  rcases Finset.mem_union.1 (hP2 hp) with h | h
  · exact hPR1 h
  · exact Finset.mem_union_right _ (hR1.subset h)

/-- Stage 2: iterating Prop 8.1 until `R♭ = ∅`. -/
theorem alt71_stage2 : ∀ n : ℕ, ∀ H : GCDGraph, H.R.card = n → 0 < H.density →
    (∀ p ∈ H.R, T0 < (p : ℝ)) →
    ∃ H' : GCDGraph, H'.IsSubgraph H ∧ 0 < H'.density ∧ H'.Rflat = ∅ ∧
      (2 : ℝ) ^ (newUnequal H' H) * H.quality ≤ H'.quality ∧
      (2 : ℝ) ^ (newUnequal H' H) * (H.density * H.quality) ≤ H'.density * H'.quality := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hδ hR
  have hq0 := (H.quality_pos_iff).2 hδ
  by_cases hf : H.Rflat.Nonempty
  · obtain ⟨H1, hs1, hδ1, -, -, hR1, h81⟩ := prop81 H hδ hR hf
    have hq1 := H1.quality_nonneg
    obtain ⟨e1, e2⟩ := alt71_extract hδ hq0 hq1 h81
    have hR1' : ∀ p ∈ H1.R, T0 < (p : ℝ) := fun p hp => hR p (hR1.subset hp)
    obtain ⟨H2, hs2, hδ2, hflat2, f1, f2⟩ :=
      ih H1.R.card (hn ▸ Finset.card_lt_card hR1) H1 rfl hδ1 hR1'
    refine ⟨H2, hs2.trans hs1, hδ2, hflat2, ?_, ?_⟩
    · have hle := alt71_newUnequal_le (H := H) hs2
      have hp : (2 : ℝ) ^ (newUnequal H2 H) ≤ 2 ^ (newUnequal H2 H1 + newUnequal H1 H) :=
        pow_le_pow_right₀ (by norm_num) hle
      rw [pow_add] at hp
      have hA : (0 : ℝ) ≤ 2 ^ newUnequal H2 H1 := by positivity
      calc (2 : ℝ) ^ (newUnequal H2 H) * H.quality
          ≤ 2 ^ newUnequal H2 H1 * 2 ^ newUnequal H1 H * H.quality :=
            mul_le_mul_of_nonneg_right hp hq0.le
        _ = 2 ^ newUnequal H2 H1 * (2 ^ newUnequal H1 H * H.quality) := by ring
        _ ≤ 2 ^ newUnequal H2 H1 * H1.quality := mul_le_mul_of_nonneg_left e1 hA
        _ ≤ H2.quality := f1
    · have hle := alt71_newUnequal_le (H := H) hs2
      have hp : (2 : ℝ) ^ (newUnequal H2 H) ≤ 2 ^ (newUnequal H2 H1 + newUnequal H1 H) :=
        pow_le_pow_right₀ (by norm_num) hle
      rw [pow_add] at hp
      have hA : (0 : ℝ) ≤ 2 ^ newUnequal H2 H1 := by positivity
      have hdq : 0 ≤ H.density * H.quality := (mul_pos hδ hq0).le
      calc (2 : ℝ) ^ (newUnequal H2 H) * (H.density * H.quality)
          ≤ 2 ^ newUnequal H2 H1 * 2 ^ newUnequal H1 H * (H.density * H.quality) :=
            mul_le_mul_of_nonneg_right hp hdq
        _ = 2 ^ newUnequal H2 H1 * (2 ^ newUnequal H1 H * (H.density * H.quality)) := by ring
        _ ≤ 2 ^ newUnequal H2 H1 * (H1.density * H1.quality) :=
            mul_le_mul_of_nonneg_left e2 hA
        _ ≤ H2.density * H2.quality := f2
  · have hflat : H.Rflat = ∅ := Finset.not_nonempty_iff_eq_empty.1 hf
    refine ⟨H, IsSubgraph.refl H, hδ, hflat, ?_, ?_⟩ <;>
      simp [alt71_newUnequal_self]

/-- The final anatomical estimate of Stage 4b. -/
theorem alt71_final (F G2 : GCDGraph) (hs : F.IsSubgraph G2) (hPF : F.P ⊆ G2.P ∪ G2.R)
    (t : ℝ) (ht : 0 < t)
    (hcount : (((G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ))).card : ℕ) : ℝ) ≤ t)
    (e : ℕ × ℕ) (he : e ∈ F.E)
    (h5 : 5 ≤ ∑ p ∈ (coprimePart e.1 e.2).primeFactors.filter
        (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ G2.R), (1 : ℝ) / p) :
    4 ≤ Lsum t (e.1 / F.aProd) (e.2 / F.bProd) := by
  classical
  obtain ⟨hv, hw⟩ := Finset.mem_product.1 (F.E_sub he)
  have hv0 := F.V_pos _ hv
  have hw0 := F.W_pos _ hw
  have hdV : ∀ p ∈ F.P, p ^ F.f p ∣ e.1 := fun p hp => F.dvd_V p hp _ hv
  have hdW : ∀ p ∈ F.P, p ^ F.g p ∣ e.2 := fun p hp => F.dvd_W p hp _ hw
  have hva := alt71_div_pos F.P F.f F.P_prime e.1 hv0 hdV
  have hwb := alt71_div_pos F.P F.g F.P_prime e.2 hw0 hdW
  set B := (coprimePart e.1 e.2).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ G2.R)
  set Pd := G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ))
  have hsplit := Finset.sum_filter_add_sum_filter_not B (fun p => p ∈ Pd) (fun p : ℕ => (1 : ℝ) / p)
  have h1 : ∑ p ∈ B.filter (fun p => p ∈ Pd), (1 : ℝ) / p ≤ 1 := by
    calc ∑ p ∈ B.filter (fun p => p ∈ Pd), (1 : ℝ) / p ≤ ∑ p ∈ Pd, (1 : ℝ) / p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; exact (Finset.mem_filter.1 hp).2
          · intro p _ _; positivity
      _ ≤ ∑ p ∈ Pd, (1 : ℝ) / t := by
          apply Finset.sum_le_sum
          intro p hp
          have := (Finset.mem_filter.1 hp).2.2
          exact one_div_le_one_div_of_le ht this
      _ = (Pd.card : ℝ) / t := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by rw [div_le_one ht]; exact hcount
  have h2 : ∑ p ∈ B.filter (fun p => p ∉ Pd), (1 : ℝ) / p ≤ Lsum t (e.1 / F.aProd) (e.2 / F.bProd) := by
    unfold Lsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpB, hpPd⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpA, htp, hpR⟩ := Finset.mem_filter.1 hpB
      have hpp := Nat.prime_of_mem_primeFactors hpA
      have hpd := Nat.dvd_of_mem_primeFactors hpA
      have hne : e.1.factorization p ≠ e.2.factorization p := fun h =>
        alt71_not_dvd e.1 e.2 p hv0 hw0 hpp h hpd
      have hfa := alt71_div_fact F.P F.f F.P_prime e.1 hv0.ne' hdV p
      have hfb := alt71_div_fact F.P F.g F.P_prime e.2 hw0.ne' hdW p
      have hne' : (e.1 / F.aProd).factorization p ≠ (e.2 / F.bProd).factorization p := by
        unfold aProd bProd
        rw [hfa, hfb]
        by_cases hpF : p ∈ F.P
        · have hp2 : p ∈ G2.P := by
            rcases Finset.mem_union.1 (hPF hpF) with h | h
            · exact h
            · exact absurd h hpR
          have hfg2 : G2.f p = G2.g p := by
            by_contra h
            exact hpPd (Finset.mem_filter.2 ⟨hp2, h, htp⟩)
          obtain ⟨hff, hgg⟩ := hs.2.2.2.2.2 p hp2
          have hfg : F.f p = F.g p := by rw [hff, hgg, hfg2]
          have hgcd := F.gcd_E p hpF e he
          rw [Nat.factorization_gcd hv0.ne' hw0.ne', Finsupp.inf_apply] at hgcd
          simp only [hpF, ite_true]
          rw [← hfg]
          rw [← hfg] at hgcd
          have hmin : min (F.f p) (F.f p) = F.f p := min_self _
          rw [hmin] at hgcd
          change min (e.1.factorization p) (e.2.factorization p) = F.f p at hgcd
          omega
        · simp only [hpF, ite_false, Nat.sub_zero]
          exact hne
      refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hpp, ?_, ?_⟩, htp⟩
      · exact alt71_dvd_cp _ _ p hva hwb hne'
      · exact alt71_coprimePart_ne_zero _ _ hva hwb
    · intro p _ _; positivity
  linarith

/-- Proposition 7.1. -/
theorem prop71 : ∃ c : ℝ, 0 < c ∧ ∀ (G : GCDGraph) (t : ℝ), G.P = ∅ → 0 < G.density →
    (∀ e ∈ G.E, 10 ≤ Lsum t e.1 e.2) → 10 * G.density ^ (-(1 : ℝ) / 50) ≤ t → T0 < t →
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.R = ∅ ∧ G'.HighDegree ∧
      (c * G.density * t ^ (50 : ℕ) * G.quality ≤ G'.quality ∨
        (c * G.quality ≤ G'.quality ∧
          ∀ e ∈ G'.E, 4 ≤ Lsum t (e.1 / G'.aProd) (e.2 / G'.bProd))) := by
  obtain ⟨K, hK, hKdef⟩ : ∃ K : ℝ, 0 < K ∧ 1 / (10 : ℝ) ^ ((10 : ℕ) ^ 3000) = 1 / K :=
    ⟨_, pow_pos (by norm_num) _, rfl⟩
  refine ⟨1 / (2 * 10 ^ 50 * K), by positivity, ?_⟩
  intro G t hP hδ hL _ hT
  have hq := (G.quality_pos_iff).2 hδ
  have hT1 : (1 : ℝ) ≤ T0 := by unfold T0; exact one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  -- Stage 1
  obtain ⟨G1, hs1, hδ1, hP1, hR1, h83⟩ := prop83 G hP hδ
  rw [hKdef] at h83
  clear hKdef
  obtain ⟨e1, e1'⟩ := alt71_extract hδ hq G1.quality_nonneg h83
  have hq1 : 0 < G1.quality := (G1.quality_pos_iff).2 hδ1
  -- Stage 2
  obtain ⟨G2, hs2, hδ2, hflat2, hq2, hdq2⟩ := alt71_stage2 _ G1 rfl hδ1 hR1
  set N := newUnequal G2 G1 with hNdef
  have hs2' : G2.IsSubgraph G := hs2.trans hs1
  have hRG2 : ∀ p ∈ G2.R, T0 < (p : ℝ) := fun p hp => hR1 p (R_mono hs2 hp)
  have hq2pos : 0 < G2.quality := (G2.quality_pos_iff).2 hδ2
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have F1 : G.quality ≤ K * G1.quality := by
    have := mul_le_mul_of_nonneg_left e1 hK.le
    rwa [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] at this
  have F1' : G.density * G.quality ≤ K * (G1.density * G1.quality) := by
    have := mul_le_mul_of_nonneg_left e1' hK.le
    rwa [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] at this
  have hq12 : G1.quality ≤ G2.quality := le_trans (le_mul_of_one_le_left hq1.le h2N) hq2
  have hGq2 : G.quality ≤ K * G2.quality :=
    le_trans F1 (mul_le_mul_of_nonneg_left hq12 hK.le)
  set A := (t / 10) ^ (50 : ℕ) with hA
  have hApos : 0 < A := by positivity
  by_cases hcase : A * G.density * G.quality ≤ K * G2.quality
  · -- Case (a)
    obtain ⟨G3, hs3, hδ3, hR3, hq3, -⟩ := alt71_iterate _ G2 rfl hδ2 hRG2
    obtain ⟨G4, hs4, -, -, -, hδ4, -, hq4, hHD⟩ := exists_highDegree_subgraph G3 hδ3
    refine ⟨G4, hs4.trans (hs3.trans hs2'), hδ4, ?_, hHD, Or.inl ?_⟩
    · exact Finset.subset_empty.1 (hR3 ▸ R_mono hs4)
    · have h1 : 1 / (2 * 10 ^ 50 * K) * G.density * t ^ (50 : ℕ) * G.quality =
          A * G.density * G.quality / K / 2 := by
        rw [hA, div_pow]; field_simp
      rw [h1]
      have h2 : A * G.density * G.quality / K ≤ G2.quality := by
        rw [div_le_iff₀ hK]; linarith
      have h3 : 0 ≤ A * G.density * G.quality / K :=
        div_nonneg (mul_pos (mul_pos hApos hδ) hq).le hK.le
      linarith
  · -- Case (b)
    push Not at hcase
    have hdq12 : G1.density * G1.quality ≤ G2.density * G2.quality :=
      le_trans (le_mul_of_one_le_left (mul_pos hδ1 hq1).le h2N) hdq2
    have hδq : 0 < G.density * G.quality := mul_pos hδ hq
    -- δ₂ ≥ (10/t)^50
    have hδ2t : (10 / t) ^ (50 : ℕ) ≤ G2.density := by
      have h1 : G.density * G.quality ≤ K * (G2.density * G2.quality) :=
        le_trans F1' (mul_le_mul_of_nonneg_left hdq12 hK.le)
      have h2 : K * (G2.density * G2.quality) < G2.density * (A * G.density * G.quality) := by
        have := mul_lt_mul_of_pos_left hcase hδ2
        have e : K * (G2.density * G2.quality) = G2.density * (K * G2.quality) := by ring
        rw [e]; exact this
      have h3 : 1 < G2.density * A := by
        have h' : 1 * (G.density * G.quality) < (G2.density * A) * (G.density * G.quality) := by
          have e : G2.density * (A * G.density * G.quality) =
              (G2.density * A) * (G.density * G.quality) := by ring
          rw [one_mul, ← e]; exact lt_of_le_of_lt h1 h2
        exact lt_of_mul_lt_mul_right h' hδq.le
      have h4 : (10 / t) ^ (50 : ℕ) * A = 1 := by
        rw [hA, ← mul_pow]; field_simp
      have h5 : (10 / t) ^ (50 : ℕ) = 1 / A := eq_one_div_of_mul_eq_one_left h4
      rw [h5, div_le_iff₀ hApos]
      linarith
    -- 2^N < t^50
    have hN : (2 : ℝ) ^ N < t ^ (50 : ℕ) := by
      have h2N0 : (0 : ℝ) ≤ 2 ^ N := by positivity
      have h1 : 2 ^ N * G.quality ≤ K * G2.quality := by
        calc 2 ^ N * G.quality ≤ 2 ^ N * (K * G1.quality) := mul_le_mul_of_nonneg_left F1 h2N0
          _ = K * (2 ^ N * G1.quality) := by ring
          _ ≤ K * G2.quality := mul_le_mul_of_nonneg_left hq2 hK.le
      have hδ1' : G.density ≤ 1 := G.density_le_one
      have hAt : A ≤ t ^ (50 : ℕ) := by
        rw [hA, div_pow]
        exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
      have h2 : 2 ^ N * G.quality < A * G.quality := by
        have : A * G.density * G.quality ≤ A * G.quality := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ1' hApos.le) hq.le
          rwa [mul_one] at this
        linarith
      have h3 : (2 : ℝ) ^ N < A := lt_of_mul_lt_mul_right h2 hq.le
      linarith
    have hNt : (N : ℝ) ≤ t := alt71_N_le t hT N hN
    -- Stage 3b
    obtain ⟨G3, hs3, hV3, hW3, hP3, hf3, hg3, hq3pos, hq3, hL3⟩ :=
      lemma84 G2 t hT.le hδ2 hflat2 hδ2t (fun e he => hL e (hs2'.2.2.2.1 he))
    have hδ3 : 0 < G3.density := (G3.quality_pos_iff).1 hq3pos
    have hRG3 : ∀ p ∈ G3.R, T0 < (p : ℝ) := fun p hp => hRG2 p (R_mono hs3 hp)
    -- Stage 4b
    obtain ⟨G4, hs4, hδ4, hR4, hq4, hP4⟩ := alt71_iterate _ G3 rfl hδ3 hRG3
    obtain ⟨G5, hs5, hP5, hf5, hg5, hδ5, -, hq5, hHD⟩ := exists_highDegree_subgraph G4 hδ4
    refine ⟨G5, hs5.trans (hs4.trans (hs3.trans hs2')), hδ5, ?_, hHD, Or.inr ⟨?_, ?_⟩⟩
    · exact Finset.subset_empty.1 (hR4 ▸ R_mono hs5)
    · have h1 : 1 / (2 * 10 ^ 50 * K) * G.quality ≤ G2.quality / 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        have h10 : (1 : ℝ) ≤ 10 ^ 50 := one_le_pow₀ (by norm_num)
        have h' : K * G2.quality ≤ K * G2.quality * 10 ^ 50 :=
          le_mul_of_one_le_right (mul_nonneg hK.le hq2pos.le) h10
        calc G.quality ≤ K * G2.quality := hGq2
          _ ≤ K * G2.quality * 10 ^ 50 := h'
          _ = G2.quality / 2 * (2 * 10 ^ 50 * K) := by ring
      linarith
    · intro e he
      have he4 : e ∈ G4.E := hs5.2.2.2.1 he
      have he3 : e ∈ G3.E := hs4.2.2.2.1 he4
      have h5 := hL3 e he3
      have ha : G5.aProd = G4.aProd := by unfold aProd; rw [hP5, hf5]
      have hb : G5.bProd = G4.bProd := by unfold bProd; rw [hP5, hg5]
      rw [ha, hb]
      have hs42 : G4.IsSubgraph G2 := hs4.trans hs3
      have hPF : G4.P ⊆ G2.P ∪ G2.R := by
        intro p hp
        rcases Finset.mem_union.1 (hP4 hp) with h | h
        · rw [hP3] at h; exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (R_mono hs3 h)
      apply alt71_final G4 G2 hs42 hPF t ht0 _ e he4 h5
      have hsub : G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ)) ⊆
          (G2.P \ G1.P).filter (fun p => G2.f p ≠ G2.g p) := by
        intro p hp
        obtain ⟨hp2, hne, htp⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hp2, ?_⟩, hne⟩
        intro hp1
        have := hP1 p hp1
        linarith
      have hc := Finset.card_le_card hsub
      have hc' : (((G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ))).card : ℕ) : ℝ) ≤ N := by
        exact_mod_cast hc
      linarith

end GCDGraph

end DuffinSchaeffer
