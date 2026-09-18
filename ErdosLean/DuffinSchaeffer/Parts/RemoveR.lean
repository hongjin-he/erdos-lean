import ErdosLean.DuffinSchaeffer.Parts.GraphBasics
import ErdosLean.DuffinSchaeffer.Parts.Mertens

/-!
# Duffin–Schaeffer — Part 16: removing the effect of `R(G)` from `L_t` (KM Lemma 8.4)

We assume `t ≥ 10^2000` instead of KM's `t ≥ 300` so that the
Rosser–Schoenfeld input `∑_{t ≤ p ≤ t^50} 1/p ≤ 4` follows from `sum_inv_prime_Ioc_le`
(`log 50 + 100/log t < 4`).  Prop. 7.1 only uses `t > 10^2000`.
-/

open Finset

namespace DuffinSchaeffer

/-! ### Auxiliary lemmas (racing prover) -/

theorem alt84_sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg (fun _ _ => hf _)
  linarith

theorem alt84_esum_le (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n) (S : Finset (ℕ × ℕ)) (A B : Finset ℕ)
    (h : S ⊆ A ×ˢ B) : esum μ S ≤ wsum μ A * wsum μ B := by
  unfold esum wsum
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => mul_nonneg (hμ _) (hμ _))

theorem alt84_inv_sq (A : Finset ℕ) (N : ℝ) (hN : 1 ≤ N) (hA : ∀ a ∈ A, N ≤ a) :
    ∑ a ∈ A, ((a : ℝ) ^ 2)⁻¹ ≤ 2 / N := by
  set m := ⌈N⌉₊ with hm
  have hNm : N ≤ m := Nat.le_ceil N
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := le_trans hN hNm
    exact_mod_cast this
  have hsub : A ⊆ Ioo (m - 1) (A.sup id + 1) := by
    intro a ha
    rw [Finset.mem_Ioo]
    constructor
    · have : m ≤ a := Nat.ceil_le.2 (hA a ha)
      omega
    · have := Finset.le_sup (f := id) ha
      simp only [id] at this
      omega
  calc ∑ a ∈ A, ((a : ℝ) ^ 2)⁻¹ ≤ ∑ a ∈ Ioo (m - 1) (A.sup id + 1), ((a : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / (((m - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ = 2 / (m : ℝ) := by rw [Nat.cast_sub hm1]; ring_nf
    _ ≤ 2 / N := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hNm

theorem alt84_T0_log : Real.log T0 = 2000 * Real.log 10 := by
  unfold T0; rw [Real.log_pow]; push_cast; ring

theorem alt84_log10 : 2 < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

theorem alt84_log51 : Real.log 51 ≤ 4 - 1 / 39 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp (4 - 1 / 39) = Real.exp 1 ^ 4 * Real.exp (-(1 / 39)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [h1]
  have h2 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have h3 : -(1 / 39 : ℝ) + 1 ≤ Real.exp (-(1 / 39)) := Real.add_one_le_exp _
  have h4 : 0 ≤ Real.exp 1 ^ 4 := by positivity
  nlinarith

/-- `∑_{t ≤ p < t^50} 1/p ≤ 4` in the form produced by `sum_inv_prime_Ioc_le`. -/
theorem alt84_mertens (t : ℝ) (ht : T0 ≤ t) :
    Real.log (Real.log (t ^ (50 : ℕ)) / Real.log (t - 1)) + 100 / Real.log (t - 1) ≤ 4 := by
  have hT : (4 : ℝ) ≤ T0 := by
    unfold T0; exact le_trans (by norm_num) (le_self_pow₀ (by norm_num : (1:ℝ) ≤ 10) (by norm_num))
  have ht4 : 4 ≤ t := le_trans hT ht
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl10 := alt84_log10
  have hlogt : 2000 * Real.log 10 ≤ Real.log t := by
    rw [← alt84_T0_log]; exact Real.log_le_log (by unfold T0; positivity) ht
  have hlt1 : Real.log t ≤ Real.log 2 + Real.log (t - 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hL : 3999 ≤ Real.log (t - 1) := by linarith
  have hLpos : 0 < Real.log (t - 1) := by linarith
  have hratio : Real.log (t ^ (50 : ℕ)) / Real.log (t - 1) ≤ 51 := by
    rw [div_le_iff₀ hLpos, Real.log_pow]
    push_cast
    linarith
  have hratio0 : 0 < Real.log (t ^ (50 : ℕ)) / Real.log (t - 1) := by
    apply div_pos _ hLpos
    rw [Real.log_pow]; push_cast; linarith
  have h1 : Real.log (Real.log (t ^ (50 : ℕ)) / Real.log (t - 1)) ≤ Real.log 51 :=
    Real.log_le_log hratio0 hratio
  have h2 : 100 / Real.log (t - 1) ≤ 100 / 3999 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h3 := alt84_log51
  have h4 : (100 : ℝ) / 3999 ≤ 1 / 39 := by norm_num
  linarith

theorem alt84_not_dvd (v w p : ℕ) (hv : 0 < v) (hw : 0 < w) (hp : p.Prime)
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

theorem alt84_coprimePart_ne_zero (v w : ℕ) (hv : 0 < v) (hw : 0 < w) : coprimePart v w ≠ 0 := by
  unfold coprimePart
  apply Nat.mul_ne_zero
  · exact (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  · exact (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'

namespace GCDGraph

/-- For a sharp prime `p`, the edges with `p ∣ vw/gcd(v,w)^2` have measure `≤ 2·10^40/p·μ(V)μ(W)`. -/
theorem alt84_sharp_bound (G : GCDGraph) (p : ℕ) (hp : p.Prime) (hs : G.IsSharp p) :
    esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2)) ≤
      2 * (K40 / p) * (wsum G.μ G.V * wsum G.μ G.W) := by
  classical
  obtain ⟨k, hVk, hWk⟩ := hs
  have hsub : G.E.filter (fun e => p ∣ coprimePart e.1 e.2) ⊆
      G.E.filter (fun e => e.1.factorization p ≠ k) ∪
        G.E.filter (fun e => e.2.factorization p ≠ k) := by
    intro e he
    obtain ⟨he, hd⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    by_contra hc
    simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_not] at hc
    have h1 := hc.1 he
    have h2 := hc.2 he
    exact alt84_not_dvd e.1 e.2 p (G.V_pos _ hv) (G.W_pos _ hw) hp (h1.trans h2.symm) hd
  have hnn : ∀ e : ℕ × ℕ, 0 ≤ G.μ e.1 * G.μ e.2 := fun e => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
  have hA : esum G.μ (G.E.filter (fun e => e.1.factorization p ≠ k)) ≤
      wsum G.μ (G.V.filter (fun v => v.factorization p ≠ k)) * wsum G.μ G.W := by
    apply alt84_esum_le G.μ G.μ_nonneg
    intro e he
    obtain ⟨he, hk⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hv, hk⟩, hw⟩
  have hB : esum G.μ (G.E.filter (fun e => e.2.factorization p ≠ k)) ≤
      wsum G.μ G.V * wsum G.μ (G.W.filter (fun w => w.factorization p ≠ k)) := by
    apply alt84_esum_le G.μ G.μ_nonneg
    intro e he
    obtain ⟨he, hk⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact Finset.mem_product.2 ⟨hv, Finset.mem_filter.2 ⟨hw, hk⟩⟩
  have hV' : wsum G.μ (G.V.filter (fun v => v.factorization p ≠ k)) ≤ K40 / p * wsum G.μ G.V := by
    have := Finset.sum_filter_add_sum_filter_not G.V (fun v => v.factorization p = k) G.μ
    unfold wsum vslice at *
    linarith
  have hW' : wsum G.μ (G.W.filter (fun w => w.factorization p ≠ k)) ≤ K40 / p * wsum G.μ G.W := by
    have := Finset.sum_filter_add_sum_filter_not G.W (fun w => w.factorization p = k) G.μ
    unfold wsum vslice at *
    linarith
  have hV0 : 0 ≤ wsum G.μ G.V := Finset.sum_nonneg (fun _ _ => G.μ_nonneg _)
  have hW0 : 0 ≤ wsum G.μ G.W := Finset.sum_nonneg (fun _ _ => G.μ_nonneg _)
  calc esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2))
      ≤ esum G.μ (G.E.filter (fun e => e.1.factorization p ≠ k) ∪
          G.E.filter (fun e => e.2.factorization p ≠ k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hnn e)
    _ ≤ esum G.μ (G.E.filter (fun e => e.1.factorization p ≠ k)) +
          esum G.μ (G.E.filter (fun e => e.2.factorization p ≠ k)) :=
        alt84_sum_union_le _ _ _ hnn
    _ ≤ K40 / p * wsum G.μ G.V * wsum G.μ G.W + wsum G.μ G.V * (K40 / p * wsum G.μ G.W) := by
        apply add_le_add
        · exact le_trans hA (mul_le_mul_of_nonneg_right hV' hW0)
        · exact le_trans hB (mul_le_mul_of_nonneg_left hW' hV0)
    _ = 2 * (K40 / p) * (wsum G.μ G.V * wsum G.μ G.W) := by ring

/-- Lemma 8.4. -/
theorem lemma84 (G : GCDGraph) (t : ℝ) (ht : T0 ≤ t) (hδ : 0 < G.density)
    (hflat : G.Rflat = ∅) (hδt : (10 / t) ^ (50 : ℕ) ≤ G.density)
    (hE : ∀ e ∈ G.E, 10 ≤ Lsum t e.1 e.2) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.V = G.V ∧ G'.W = G.W ∧ G'.P = G.P ∧ G'.f = G.f ∧
      G'.g = G.g ∧ 0 < G'.quality ∧ G.quality / 2 ≤ G'.quality ∧
      ∀ e ∈ G'.E, 5 ≤ ∑ p ∈ (coprimePart e.1 e.2).primeFactors.filter
        (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ G.R), (1 : ℝ) / p := by
  classical
  have hE0 : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hV0 := G.wsum_V_pos_of_density_pos hδ
  have hW0 := G.wsum_W_pos_of_density_pos hδ
  have hq0 : 0 < G.quality := (G.quality_pos_iff).2 hδ
  have hT1 : (4 : ℝ) ≤ T0 := by
    unfold T0; exact le_trans (by norm_num) (le_self_pow₀ (by norm_num : (1:ℝ) ≤ 10) (by norm_num))
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set N : ℝ := t ^ (50 : ℕ) with hN
  have htN : t ≤ N := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ (50 : ℕ) := pow_le_pow_right₀ ht1 (by norm_num)
  have hN1 : 1 ≤ N := le_trans ht1 htN
  have hN0 : 0 < N := by linarith
  have hsharp : ∀ p ∈ G.R, G.IsSharp p := by
    intro p hp
    have := (Finset.filter_eq_empty_iff.1 hflat) hp
    simpa using this
  have hcp0 : ∀ e ∈ G.E, coprimePart e.1 e.2 ≠ 0 := by
    intro e he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact alt84_coprimePart_ne_zero _ _ (G.V_pos _ hv) (G.W_pos _ hw)
  -- the "large R-part" of `L_t`
  set S : ℕ × ℕ → ℝ := fun e => ∑ p ∈ (coprimePart e.1 e.2).primeFactors.filter
    (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)), (1 : ℝ) / p with hSdef
  have hS0 : ∀ e, 0 ≤ S e := fun e => Finset.sum_nonneg (fun _ _ => by positivity)
  set R' : Finset ℕ := G.R.filter (fun p : ℕ => N ≤ (p : ℝ)) with hR'
  have hSe : ∀ e ∈ G.E, S e = ∑ p ∈ R', if p ∣ coprimePart e.1 e.2 then (1 : ℝ) / p else 0 := by
    intro e he
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, hR']
    constructor
    · rintro ⟨⟨_, hdvd, _⟩, hR, hNp⟩; exact ⟨⟨hR, hNp⟩, hdvd⟩
    · rintro ⟨⟨hR, hNp⟩, hdvd⟩; exact ⟨⟨G.prime_of_mem_R hR, hdvd, hcp0 e he⟩, hR, hNp⟩
  have hkey : ∑ e ∈ G.E, G.μ e.1 * G.μ e.2 * S e ≤ esum G.μ G.E / 100 := by
    have h1 : ∑ e ∈ G.E, G.μ e.1 * G.μ e.2 * S e =
        ∑ p ∈ R', (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2)) := by
      rw [Finset.sum_congr rfl (fun e he => by rw [hSe e he, Finset.mul_sum]), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      unfold esum
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    have h2 : ∀ p ∈ R', (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2)) ≤
        2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ((p : ℝ) ^ 2)⁻¹ := by
      intro p hp
      have hpR := (Finset.mem_filter.1 hp).1
      have hb := G.alt84_sharp_bound p (G.prime_of_mem_R hpR) (hsharp p hpR)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (G.prime_of_mem_R hpR).pos
      calc (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2))
          ≤ (1 : ℝ) / p * (2 * (K40 / p) * (wsum G.μ G.V * wsum G.μ G.W)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ((p : ℝ) ^ 2)⁻¹ := by
            field_simp
    have h3 : ∑ p ∈ R', ((p : ℝ) ^ 2)⁻¹ ≤ 2 / N :=
      alt84_inv_sq R' N hN1 (fun a ha => (Finset.mem_filter.1 ha).2)
    have hK : (0 : ℝ) < K40 := by unfold K40; positivity
    have hVW : 0 < wsum G.μ G.V * wsum G.μ G.W := mul_pos hV0 hW0
    have hEeq : esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.W) := by
      unfold density; field_simp
    have hδN : (10 : ℝ) ^ 50 / N ≤ G.density := by
      rw [hN, ← div_pow]; exact hδt
    rw [h1]
    calc ∑ p ∈ R', (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2))
        ≤ ∑ p ∈ R', 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum h2
      _ = 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ∑ p ∈ R', ((p : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * (2 / N) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (10 : ℝ) ^ 50 / N * (wsum G.μ G.V * wsum G.μ G.W) / 100 := by
          have hXN : 0 ≤ (wsum G.μ G.V * wsum G.μ G.W) / N := by positivity
          have e1 : 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * (2 / N) =
              4 * 10 ^ 40 * ((wsum G.μ G.V * wsum G.μ G.W) / N) := by unfold K40; ring
          have e2 : (10 : ℝ) ^ 50 / N * (wsum G.μ G.V * wsum G.μ G.W) / 100 =
              10 ^ 48 * ((wsum G.μ G.V * wsum G.μ G.W) / N) := by ring
          rw [e1, e2]
          nlinarith
      _ ≤ esum G.μ G.E / 100 := by
          rw [hEeq]
          have := mul_le_mul_of_nonneg_right hδN hVW.le
          linarith
  set E' := G.E.filter (fun e => S e ≤ 1) with hE'
  have hbad : esum G.μ (G.E.filter (fun e => ¬ S e ≤ 1)) ≤ esum G.μ G.E / 100 := by
    calc esum G.μ (G.E.filter (fun e => ¬ S e ≤ 1))
        ≤ ∑ e ∈ G.E.filter (fun e => ¬ S e ≤ 1), G.μ e.1 * G.μ e.2 * S e := by
          unfold esum
          apply Finset.sum_le_sum
          intro e he
          have h1 : 1 ≤ S e := le_of_lt (not_le.1 (Finset.mem_filter.1 he).2)
          have h0 : 0 ≤ G.μ e.1 * G.μ e.2 := mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
          nlinarith
      _ ≤ ∑ e ∈ G.E, G.μ e.1 * G.μ e.2 * S e :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun e _ _ => mul_nonneg (mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)) (hS0 e))
      _ ≤ esum G.μ G.E / 100 := hkey
  have hsplit : esum G.μ E' + esum G.μ (G.E.filter (fun e => ¬ S e ≤ 1)) = esum G.μ G.E :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hE'ge : 99 / 100 * esum G.μ G.E ≤ esum G.μ E' := by linarith
  have hE'pos : 0 < esum G.μ E' := by linarith
  let G' := G.induce G.V G.W E' (subset_refl _) (subset_refl _) (Finset.filter_subset _ _)
    ((Finset.filter_subset _ _).trans G.E_sub)
  have hq : G'.quality = G.quality * (esum G.μ E' / esum G.μ G.E) ^ 10 := by
    have hd : G'.density = esum G.μ E' / (wsum G.μ G.V * wsum G.μ G.W) := rfl
    have hqf : ∏ p ∈ G'.P, G'.qualityFactor p = ∏ p ∈ G.P, G.qualityFactor p := rfl
    have hVV : wsum G'.μ G'.V = wsum G.μ G.V := rfl
    have hWW : wsum G'.μ G'.W = wsum G.μ G.W := rfl
    unfold quality
    rw [hd, hqf, hVV, hWW]
    unfold density
    rw [div_pow, div_pow, div_pow]
    field_simp
  have hx : 99 / 100 ≤ esum G.μ E' / esum G.μ G.E := by rw [le_div_iff₀ hE0]; linarith
  refine ⟨G', ⟨rfl, subset_refl _, subset_refl _, Finset.filter_subset _ _, subset_refl _,
    fun p _ => ⟨rfl, rfl⟩⟩, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hq]; positivity
  · rw [hq]
    have h1 : (99 / 100 : ℝ) ^ 10 ≤ (esum G.μ E' / esum G.μ G.E) ^ 10 :=
      pow_le_pow_left₀ (by norm_num) hx 10
    have h2 : (1 / 2 : ℝ) ≤ (99 / 100) ^ 10 := by norm_num
    nlinarith
  · intro e he
    have he' : e ∈ E' := he
    obtain ⟨heE, hS1⟩ := Finset.mem_filter.1 he'
    have hL := hE e heE
    unfold Lsum at hL
    set A := (coprimePart e.1 e.2).primeFactors with hA
    have hsplit2 := Finset.sum_filter_add_sum_filter_not (A.filter (fun p : ℕ => t ≤ (p : ℝ)))
      (fun p => p ∉ G.R) (fun p : ℕ => (1 : ℝ) / p)
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hsub : A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ ¬ p ∉ G.R) ⊆
        A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N) ∪
          A.filter (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)) := by
      intro p hp
      obtain ⟨hpA, htp, hpR⟩ := Finset.mem_filter.1 hp
      rw [not_not] at hpR
      rcases lt_or_ge (p : ℝ) N with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hpA, htp, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hpA, hpR, h⟩)
    have hnn : ∀ p : ℕ, (0 : ℝ) ≤ 1 / p := fun p => by positivity
    have hX : ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N), (1 : ℝ) / p ≤ 4 := by
      have hsub2 : A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N) ⊆
          (Ioc ⌊t - 1⌋₊ ⌊N⌋₊).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpA, htp, hpN⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩, Nat.prime_of_mem_primeFactors hpA⟩
        · rw [Nat.floor_lt (by linarith)]; linarith
        · exact Nat.le_floor hpN.le
      calc ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N), (1 : ℝ) / p
          ≤ ∑ p ∈ (Ioc ⌊t - 1⌋₊ ⌊N⌋₊).filter Nat.Prime, (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => hnn p)
        _ ≤ Real.log (Real.log N / Real.log (t - 1)) + 100 / Real.log (t - 1) :=
            sum_inv_prime_Ioc_le (t - 1) N (by linarith) (by linarith)
        _ ≤ 4 := alt84_mertens t ht
    have hY : ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ ¬ p ∉ G.R), (1 : ℝ) / p ≤ 4 + 1 := by
      calc ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ ¬ p ∉ G.R), (1 : ℝ) / p
          ≤ ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N) ∪
              A.filter (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
        _ ≤ ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N), (1 : ℝ) / p +
              ∑ p ∈ A.filter (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)), (1 : ℝ) / p :=
            alt84_sum_union_le _ _ _ hnn
        _ ≤ 4 + 1 := add_le_add hX hS1
    linarith

end GCDGraph

end DuffinSchaeffer
