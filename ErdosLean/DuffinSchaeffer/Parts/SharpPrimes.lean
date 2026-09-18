import ErdosLean.DuffinSchaeffer.Parts.Unbalanced
import ErdosLean.DuffinSchaeffer.Parts.GenericPrimes

/-!
# Duffin–Schaeffer — Part 15: iteration when `R♭(G) = ∅` (KM §14: Lemma 14.1, Prop. 8.2)

The most delicate step: the factor `(1 - 1_{f=g≥1}/p)^{-2}` in the
quality pays for passing to `V_{p^k} ∪ V_{p^{k+1}}` when `p^k` divides almost all vertices.

We follow KM's proof of Lemma 14.1, but compare the three candidate graphs
`G⁺`, `G_{p^k,p^{k-1}}`, `G_{p^{k-1},p^k}` directly with the (sparsified) graph `G₁`, and replace
KM's exponential estimates by the weighted AM–GM inequality `y^{9/10} z^{1/10} ≤ (9y + z)/10`.
-/

open Finset

namespace DuffinSchaeffer

namespace GCDGraph

/-! ### Basic bookkeeping -/

theorem alt_sh_wsum_nonneg (G : GCDGraph) (S : Finset ℕ) : 0 ≤ wsum G.μ S :=
  sum_nonneg fun i _ => G.μ_nonneg i

theorem alt_sh_esum_nonneg (G : GCDGraph) (S : Finset (ℕ × ℕ)) : 0 ≤ esum G.μ S :=
  sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)

theorem alt_sh_pos (G : GCDGraph) (hδ : 0 < G.density) :
    0 < esum G.μ G.E ∧ 0 < wsum G.μ G.V ∧ 0 < wsum G.μ G.W := by
  have hV0 : 0 ≤ wsum G.μ G.V := sum_nonneg fun i _ => G.μ_nonneg i
  have hW0 : 0 ≤ wsum G.μ G.W := sum_nonneg fun i _ => G.μ_nonneg i
  unfold density at hδ
  have hVW : wsum G.μ G.V * wsum G.μ G.W ≠ 0 := by
    intro h; rw [h, div_zero] at hδ; exact lt_irrefl _ hδ
  have hVW' : 0 < wsum G.μ G.V * wsum G.μ G.W :=
    lt_of_le_of_ne (mul_nonneg hV0 hW0) (Ne.symm hVW)
  refine ⟨(div_pos_iff_of_pos_right hVW').1 hδ,
    lt_of_le_of_ne hV0 (fun h => hVW (by rw [← h, zero_mul])),
    lt_of_le_of_ne hW0 (fun h => hVW (by rw [← h, mul_zero]))⟩

theorem alt_sh_esum_le_prod (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (h : E' ⊆ V' ×ˢ W') : esum G.μ E' ≤ wsum G.μ V' * wsum G.μ W' := by
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg h (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))

theorem alt_sh_esum_union_le (G : GCDGraph) (s t : Finset (ℕ × ℕ)) :
    esum G.μ (s ∪ t) ≤ esum G.μ s + esum G.μ t := by
  unfold esum
  rw [← sum_union_inter]
  have : 0 ≤ ∑ e ∈ s ∩ t, G.μ e.1 * G.μ e.2 :=
    sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
  linarith

theorem alt_sh_disj_le (G : GCDGraph) (S : Finset ℕ) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ v, P v → ¬ Q v) :
    wsum G.μ (S.filter P) + wsum G.μ (S.filter Q) ≤ wsum G.μ S := by
  unfold wsum
  rw [← sum_union (disjoint_filter.2 (fun v _ h1 h2 => h v h1 h2))]
  exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun i _ _ => G.μ_nonneg i)

/-! ### The graph `G⁺` of KM §14 -/

/-- `G⁺ = (μ, V_{p^k} ∪ V_{p^{k+1}}, W_{p^k} ∪ W_{p^{k+1}}, E⁺, P ∪ {p}, f⁺, g⁺)` with
`f⁺(p) = g⁺(p) = k`, where `E⁺` consists of the edges of type `(k,k)`, `(k,k+1)`, `(k+1,k)`. -/
def alt_sh_plus (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) : GCDGraph where
  μ := G.μ
  V := G.V.filter (fun v => v.factorization p = k ∨ v.factorization p = k + 1)
  W := G.W.filter (fun w => w.factorization p = k ∨ w.factorization p = k + 1)
  E := G.E.filter (fun e => (e.1.factorization p = k ∧ e.2.factorization p = k) ∨
    (e.1.factorization p = k ∧ e.2.factorization p = k + 1) ∨
    (e.1.factorization p = k + 1 ∧ e.2.factorization p = k))
  P := insert p G.P
  f := Function.update G.f p k
  g := Function.update G.g p k
  μ_nonneg := G.μ_nonneg
  V_pos := fun v hv => G.V_pos v (Finset.mem_filter.1 hv).1
  W_pos := fun w hw => G.W_pos w (Finset.mem_filter.1 hw).1
  E_sub := by
    intro e he
    obtain ⟨he, h⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hv, ?_⟩, Finset.mem_filter.2 ⟨hw, ?_⟩⟩
    · omega
    · omega
  P_prime := by
    intro q hq
    rcases Finset.mem_insert.1 hq with hqp | hq
    · rw [hqp]; exact hp
    · exact G.P_prime q hq
  dvd_V := by
    intro q hq v hv
    obtain ⟨hv, hvk⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self]
      exact (pow_dvd_pow p (by omega : k ≤ v.factorization p)).trans (Nat.ordProj_dvd v p)
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_V q hq' v hv
  dvd_W := by
    intro q hq w hw
    obtain ⟨hw, hwk⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self]
      exact (pow_dvd_pow p (by omega : k ≤ w.factorization p)).trans (Nat.ordProj_dvd w p)
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_W q hq' w hw
  gcd_E := by
    intro q hq e he0
    obtain ⟨he, h⟩ := Finset.mem_filter.1 he0
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
      have hv0 : e.1 ≠ 0 := (G.V_pos _ hv).ne'
      have hw0 : e.2 ≠ 0 := (G.W_pos _ hw).ne'
      rw [hqp, Function.update_self, Function.update_self, Nat.factorization_gcd hv0 hw0,
        Finsupp.inf_apply]
      show min (e.1.factorization p) (e.2.factorization p) = min k k
      omega
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact G.gcd_E q hq' e he
  exact_V := by
    intro q hq hfg v hv
    obtain ⟨hv, _⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self, Function.update_self] at hfg
      exact absurd rfl hfg
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_V q hq' hfg v hv
  exact_W := by
    intro q hq hfg w hw
    obtain ⟨hw, _⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self, Function.update_self] at hfg
      exact absurd rfl hfg
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_W q hq' hfg w hw

theorem alt_sh_plus_isSubgraph (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (alt_sh_plus G p k hp hpP).IsSubgraph G := by
  refine ⟨rfl, filter_subset _ _, filter_subset _ _, filter_subset _ _, subset_insert _ _, ?_⟩
  intro q hq
  have hne : q ≠ p := fun h => hpP (h ▸ hq)
  exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩

theorem alt_sh_plus_R (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (alt_sh_plus G p k hp hpP).R ⊆ G.R.erase p := by
  intro q hq
  obtain ⟨h1, h2⟩ := mem_sdiff.1 hq
  obtain ⟨e, he, hqe⟩ := mem_biUnion.1 h1
  have hq1 : q ∉ G.P := fun h => h2 (mem_insert_of_mem h)
  have hqp : q ≠ p := fun h => h2 (by rw [h]; exact mem_insert_self p G.P)
  exact mem_erase.2 ⟨hqp, mem_sdiff.2 ⟨mem_biUnion.2 ⟨e, (mem_filter.1 he).1, hqe⟩, hq1⟩⟩

theorem alt_sh_plus_quality (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hE : 0 < esum G.μ G.E) (hV : 0 < wsum G.μ G.V) (hW : 0 < wsum G.μ G.W)
    (hV' : 0 < wsum G.μ (alt_sh_plus G p k hp hpP).V)
    (hW' : 0 < wsum G.μ (alt_sh_plus G p k hp hpP).W) :
    (alt_sh_plus G p k hp hpP).quality = G.quality *
      (esum G.μ (alt_sh_plus G p k hp hpP).E / esum G.μ G.E) ^ 10 *
      (wsum G.μ G.V / wsum G.μ (alt_sh_plus G p k hp hpP).V) ^ 9 *
      (wsum G.μ G.W / wsum G.μ (alt_sh_plus G p k hp hpP).W) ^ 9 *
      (1 / ((1 - (if 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
        (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  set G' := alt_sh_plus G p k hp hpP with hG'
  have hq' : G'.quality = esum G.μ G'.E ^ 10 / (wsum G.μ G'.V ^ 9 * wsum G.μ G'.W ^ 9) *
      ∏ q ∈ G'.P, G'.qualityFactor q := quality_eq G'
  have hq := quality_eq G
  have hprod : ∏ q ∈ G'.P, G'.qualityFactor q =
      (1 / ((1 - (if 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
        (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) * ∏ q ∈ G.P, G.qualityFactor q := by
    show ∏ q ∈ insert p G.P, G'.qualityFactor q = _
    rw [prod_insert hpP]
    congr 1
    · show (p : ℝ) ^ ((Function.update G.f p k p - Function.update G.g p k p) +
          (Function.update G.g p k p - Function.update G.f p k p)) /
        ((1 - (if Function.update G.f p k p = Function.update G.g p k p ∧
          1 ≤ Function.update G.f p k p then 1 / (p : ℝ) else 0)) ^ 2 *
          (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) = _
      simp only [Function.update_self, Nat.sub_self, add_zero, pow_zero, true_and]
    · apply prod_congr rfl
      intro q hq
      have hne : q ≠ p := fun h => hpP (h ▸ hq)
      show (q : ℝ) ^ ((Function.update G.f p k q - Function.update G.g p k q) +
          (Function.update G.g p k q - Function.update G.f p k q)) /
        ((1 - (if Function.update G.f p k q = Function.update G.g p k q ∧
          1 ≤ Function.update G.f p k q then 1 / (q : ℝ) else 0)) ^ 2 *
          (1 - 1 / (q : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) = G.qualityFactor q
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      rfl
  rw [hq', hprod, hq]
  field_simp

/-! ### Real-variable lemmas -/

/-- Weighted AM–GM: `x^{10} < y^9 z ⇒ x < (9y + z)/10`. -/
theorem alt_sh_amgm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 10 < y ^ 9 * z) :
    x < (9 * y + z) / 10 := by
  by_contra hge
  push_neg at hge
  have hw := Real.geom_mean_le_arith_mean2_weighted (w₁ := 9 / 10) (w₂ := 1 / 10) (p₁ := y)
    (p₂ := z) (by norm_num) (by norm_num) hy hz (by norm_num)
  have h1 : (y ^ ((9 : ℝ) / 10) * z ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = y ^ 9 * z := by
    rw [mul_pow, ← Real.rpow_natCast (y ^ ((9 : ℝ) / 10)), ← Real.rpow_mul hy,
      ← Real.rpow_natCast (z ^ ((1 : ℝ) / 10)), ← Real.rpow_mul hz]
    norm_num
  have h2 : (y ^ ((9 : ℝ) / 10) * z ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) ≤ ((9 * y + z) / 10) ^ 10 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h3 : ((9 * y + z) / 10) ^ 10 ≤ x ^ 10 := pow_le_pow_left₀ (by positivity) hge 10
  linarith

/-- From `x^{10} (V/V')^9 (W/W')^9 F < 1` to `x^{10} < (1-a)^9 (1-b)^9 / F`. -/
theorem alt_sh_bound1 (x V V' W W' a b F : ℝ) (hV : 0 < V) (hW : 0 < W) (hV' : 0 < V')
    (hW' : 0 < W') (hVa : V' ≤ (1 - a) * V) (hWb : W' ≤ (1 - b) * W) (hF : 0 < F)
    (h : x ^ 10 * (V / V') ^ 9 * (W / W') ^ 9 * F < 1) :
    x ^ 10 < (1 - a) ^ 9 * (1 - b) ^ 9 / F := by
  have hu : V' / V ≤ 1 - a := by rw [div_le_iff₀ hV]; linarith
  have hv : W' / W ≤ 1 - b := by rw [div_le_iff₀ hW]; linarith
  have e : x ^ 10 * (V / V') ^ 9 * (W / W') ^ 9 * F =
      x ^ 10 * F / ((V' / V) ^ 9 * (W' / W) ^ 9) := by
    field_simp
  rw [e, div_lt_one (by positivity)] at h
  have h2 : x ^ 10 < (V' / V) ^ 9 * (W' / W) ^ 9 / F := by
    rw [lt_div_iff₀ hF]; linarith
  refine lt_of_lt_of_le h2 ?_
  apply div_le_div_of_nonneg_right _ hF.le
  apply mul_le_mul (pow_le_pow_left₀ (by positivity) hu 9)
    (pow_le_pow_left₀ (by positivity) hv 9) (by positivity)
  exact le_trans (by positivity) (pow_le_pow_left₀ (by positivity) hu 9)

theorem alt_sh_final (xp xa xb a b c θ e η : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haη : a ≤ η)
    (hbη : b ≤ η) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hθ0 : 0 ≤ θ)
    (hxp : xp < (9 * ((1 - a) * (1 - b) * (1 - c)) + (1 - θ) ^ 2 * (1 - c)) / 10)
    (hxa : xa ≤ (1 - c) * (9 * b + θ) / 10) (hxb : xb ≤ (1 - c) * (9 * a + θ) / 10)
    (hcov : 1 ≤ xp + xa + xb + c / 2 + e) (hsmall : η ^ 2 + θ ^ 2 + e ≤ c / 2) : False := by
  have key : (9 * ((1 - a) * (1 - b) * (1 - c)) + (1 - θ) ^ 2 * (1 - c)) / 10 +
      (1 - c) * (9 * b + θ) / 10 + (1 - c) * (9 * a + θ) / 10 =
      (1 - c) + (1 - c) * (9 * (a * b) + θ ^ 2) / 10 := by ring
  have hab : a * b ≤ η ^ 2 := by
    rw [sq]; exact mul_le_mul haη hbη hb0 (le_trans ha0 haη)
  have hnn : 0 ≤ 9 * (a * b) + θ ^ 2 := by positivity
  have h2 : (1 - c) * (9 * (a * b) + θ ^ 2) ≤ 9 * (a * b) + θ ^ 2 := by
    have : 0 ≤ c * (9 * (a * b) + θ ^ 2) := mul_nonneg hc0 hnn
    linarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  nlinarith

/-- The numerical heart of Lemma 14.1: for `P ≥ 10^{2000}`,
`(10^{40}/P)^2 + P^{-2} + (10^{40}/P)^{9/5} ≤ P^{-31/30}/2`. -/
theorem alt_sh_numeric (P : ℝ) (hP : T0 ≤ P) :
    (K40 / P) ^ 2 + (1 / P) ^ 2 + (K40 / P) ^ ((9 : ℝ) / 5) ≤ 1 / P ^ ((31 : ℝ) / 30) / 2 := by
  unfold T0 at hP
  unfold K40
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have h30 : (P ^ ((1 : ℝ) / 30)) ^ (30 : ℕ) = P := by
    rw [← Real.rpow_natCast (P ^ ((1 : ℝ) / 30)) 30, ← Real.rpow_mul hP0.le]; norm_num
  have h31 : (P ^ ((1 : ℝ) / 30)) ^ (31 : ℕ) = P ^ ((31 : ℝ) / 30) := by
    rw [← Real.rpow_natCast (P ^ ((1 : ℝ) / 30)) 31, ← Real.rpow_mul hP0.le]; norm_num
  have hs0 : 0 < P ^ ((1 : ℝ) / 30) := Real.rpow_pos_of_pos hP0 _
  generalize P ^ ((1 : ℝ) / 30) = s at h30 h31 hs0
  have hs : (10 : ℝ) ^ (10 : ℕ) ≤ s := by
    have : ((10 : ℝ) ^ (10 : ℕ)) ^ (30 : ℕ) ≤ s ^ (30 : ℕ) := by
      rw [h30, ← pow_mul]
      exact le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hP
    exact le_of_pow_le_pow_left₀ (by norm_num) hs0.le this
  have hs1 : 1 ≤ s := le_trans (one_le_pow₀ (by norm_num)) hs
  have hbig : ∀ n : ℕ, 9 ≤ n → (10 : ℝ) ^ (90 : ℕ) ≤ s ^ n := by
    intro n hn
    calc (10 : ℝ) ^ (90 : ℕ) = ((10 : ℝ) ^ (10 : ℕ)) ^ (9 : ℕ) := by rw [← pow_mul]
      _ ≤ s ^ (9 : ℕ) := pow_le_pow_left₀ (by positivity) hs 9
      _ ≤ s ^ n := pow_le_pow_right₀ hs1 hn
  have e1 : (10 : ℝ) ^ (40 : ℕ) / P = (10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ) := by
    rw [← h30]; ring
  have hq0 : 0 ≤ (10 : ℝ) ^ (8 : ℕ) / s ^ (6 : ℕ) := by positivity
  have e2 : ((10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ)) ^ ((9 : ℝ) / 5) =
      (10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast ((10 : ℝ) ^ (8 : ℕ) / s ^ (6 : ℕ)) 5, ← Real.rpow_mul hq0]
    norm_num
  rw [e1, e2, ← h31, ← h30]
  have t1 : ((10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ)) ^ 2 ≤ 1 / (6 * s ^ (31 : ℕ)) := by
    rw [show ((10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ)) ^ 2 = (10 : ℝ) ^ (80 : ℕ) / s ^ (60 : ℕ) by
      ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h29 := hbig 29 (by norm_num)
    calc (10 : ℝ) ^ (80 : ℕ) * (6 * s ^ (31 : ℕ)) = (6 * 10 ^ (80 : ℕ)) * s ^ (31 : ℕ) := by ring
      _ ≤ s ^ (29 : ℕ) * s ^ (31 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * s ^ (60 : ℕ) := by ring
  have t2 : (1 / s ^ (30 : ℕ)) ^ 2 ≤ 1 / (6 * s ^ (31 : ℕ)) := by
    rw [show (1 / s ^ (30 : ℕ)) ^ 2 = 1 / s ^ (60 : ℕ) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h29 := hbig 29 (by norm_num)
    calc 1 * (6 * s ^ (31 : ℕ)) = 6 * s ^ (31 : ℕ) := by ring
      _ ≤ s ^ (29 : ℕ) * s ^ (31 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * s ^ (60 : ℕ) := by ring
  have t3 : (10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (9 : ℕ) ≤ 1 / (6 * s ^ (31 : ℕ)) := by
    rw [show ((10 : ℝ) ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (9 : ℕ) = (10 : ℝ) ^ (72 : ℕ) / s ^ (54 : ℕ) by
      ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h23 := hbig 23 (by norm_num)
    calc (10 : ℝ) ^ (72 : ℕ) * (6 * s ^ (31 : ℕ)) = (6 * 10 ^ (72 : ℕ)) * s ^ (31 : ℕ) := by ring
      _ ≤ s ^ (23 : ℕ) * s ^ (31 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * s ^ (54 : ℕ) := by ring
  have t4 : 1 / (6 * s ^ (31 : ℕ)) * 3 = 1 / s ^ (31 : ℕ) / 2 := by
    field_simp; ring
  linarith

/-! ### Pieces of the proof of Lemma 14.1 -/

/-- Coverage of the edge set of the sparsified graph `G₁` (normalized form). -/
theorem alt_sh_cover (G G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hμ1 : G1.μ = G.μ) (hE1 : 0 < esum G1.μ G1.E) (η : ℝ)
    (hVk : (1 - η) * wsum G1.μ G1.V ≤ wsum G1.μ (vslice G1.V p k))
    (hWk : (1 - η) * wsum G1.μ G1.W ≤ wsum G1.μ (vslice G1.W p k))
    (hsp : ∀ A ⊆ G1.V, ∀ B ⊆ G1.W, wsum G.μ A ≤ η * wsum G.μ G1.V →
      wsum G.μ B ≤ η * wsum G.μ G1.W →
      esum G.μ (G1.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G1.E)
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30))
    (hbad1 : esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧
      1 + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤
        esum G1.μ G1.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)))
    (hbad2 : esum G1.μ (G1.E.filter (fun e => e.2.factorization p = k ∧
      1 + 1 ≤ (e.1.factorization p - k) + (k - e.1.factorization p))) ≤
        esum G1.μ G1.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) :
    1 ≤ esum G1.μ (alt_sh_plus G1 p k hp hpP1).E / esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)) /
        esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)) /
        esum G1.μ G1.E + c / 2 + η ^ ((9 : ℝ) / 5) := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Gp := alt_sh_plus G1 p k hp hpP1 with hGp
  set Ea := G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)
    with hEa
  set Eb := G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)
    with hEb
  set B1 := G1.E.filter (fun e => e.1.factorization p = k ∧
    1 + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k)) with hB1
  set B2 := G1.E.filter (fun e => e.2.factorization p = k ∧
    1 + 1 ≤ (e.1.factorization p - k) + (k - e.1.factorization p)) with hB2
  set B3 := G1.E.filter (fun e => ¬ e.1.factorization p = k ∧ ¬ e.2.factorization p = k)
    with hB3
  have hsub : G1.E ⊆ B1 ∪ B2 ∪ B3 ∪ Gp.E ∪ Ea ∪ Eb := by
    intro e he
    have hd : (e.1.factorization p = k ∧ e.2.factorization p = k) ∨
        (e.1.factorization p = k ∧ e.2.factorization p = k + 1) ∨
        (e.1.factorization p = k + 1 ∧ e.2.factorization p = k) ∨
        (e.1.factorization p = k ∧ e.2.factorization p + 1 = k) ∨
        (e.1.factorization p + 1 = k ∧ e.2.factorization p = k) ∨
        (e.1.factorization p = k ∧
          1 + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k)) ∨
        (e.2.factorization p = k ∧
          1 + 1 ≤ (e.1.factorization p - k) + (k - e.1.factorization p)) ∨
        (¬ e.1.factorization p = k ∧ ¬ e.2.factorization p = k) := by omega
    rw [mem_union, mem_union, mem_union, mem_union, mem_union]
    rcases hd with h | h | h | h | h | h | h | h
    · left; left; right; exact mem_filter.2 ⟨he, Or.inl h⟩
    · left; left; right; exact mem_filter.2 ⟨he, Or.inr (Or.inl h)⟩
    · left; left; right; exact mem_filter.2 ⟨he, Or.inr (Or.inr h)⟩
    · left; right; exact mem_filter.2 ⟨he, h⟩
    · right; exact mem_filter.2 ⟨he, h⟩
    · left; left; left; left; left; exact mem_filter.2 ⟨he, h⟩
    · left; left; left; left; right; exact mem_filter.2 ⟨he, h⟩
    · left; left; left; right; exact mem_filter.2 ⟨he, h⟩
  have hcov : E1 ≤ esum G1.μ B1 + esum G1.μ B2 + esum G1.μ B3 + esum G1.μ Gp.E +
      esum G1.μ Ea + esum G1.μ Eb := by
    have h0 : E1 ≤ esum G1.μ (B1 ∪ B2 ∪ B3 ∪ Gp.E ∪ Ea ∪ Eb) := by
      unfold esum
      exact sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => mul_nonneg (G1.μ_nonneg _) (G1.μ_nonneg _))
    have u1 := alt_sh_esum_union_le G1 (B1 ∪ B2 ∪ B3 ∪ Gp.E ∪ Ea) Eb
    have u2 := alt_sh_esum_union_le G1 (B1 ∪ B2 ∪ B3 ∪ Gp.E) Ea
    have u3 := alt_sh_esum_union_le G1 (B1 ∪ B2 ∪ B3) Gp.E
    have u4 := alt_sh_esum_union_le G1 (B1 ∪ B2) B3
    have u5 := alt_sh_esum_union_le G1 B1 B2
    linarith
  -- the sparse bound for `B3`
  have hVksplit : wsum G1.μ (vslice G1.V p k) +
      wsum G1.μ (G1.V.filter (fun v => ¬ v.factorization p = k)) = V1 := by
    unfold wsum vslice; exact sum_filter_add_sum_filter_not _ _ _
  have hWksplit : wsum G1.μ (vslice G1.W p k) +
      wsum G1.μ (G1.W.filter (fun w => ¬ w.factorization p = k)) = W1 := by
    unfold wsum vslice; exact sum_filter_add_sum_filter_not _ _ _
  have hB3le : esum G1.μ B3 ≤ η ^ ((9 : ℝ) / 5) * E1 := by
    have h := hsp (G1.V.filter (fun v => ¬ v.factorization p = k)) (filter_subset _ _)
      (G1.W.filter (fun w => ¬ w.factorization p = k)) (filter_subset _ _)
      (by rw [← hμ1]; linarith) (by rw [← hμ1]; linarith)
    rw [← hμ1] at h
    have hset : G1.E.filter (fun e => e.1 ∈ G1.V.filter (fun v => ¬ v.factorization p = k) ∧
        e.2 ∈ G1.W.filter (fun w => ¬ w.factorization p = k)) = B3 := by
      apply filter_congr
      intro e he
      obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
      simp only [mem_filter]
      exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hv, h.1⟩, ⟨hw, h.2⟩⟩⟩
    rw [hset] at h
    exact h
  have e1 : esum G1.μ B1 ≤ E1 * c / 4 := by
    refine le_trans hbad1 (le_of_eq ?_); rw [hc]; field_simp
  have e2 : esum G1.μ B2 ≤ E1 * c / 4 := by
    refine le_trans hbad2 (le_of_eq ?_); rw [hc]; field_simp
  have : E1 * 1 ≤ E1 * (esum G1.μ Gp.E / E1 + esum G1.μ Ea / E1 + esum G1.μ Eb / E1 + c / 2 +
      η ^ ((9 : ℝ) / 5)) := by
    have ex : E1 * (esum G1.μ Gp.E / E1 + esum G1.μ Ea / E1 + esum G1.μ Eb / E1 + c / 2 +
        η ^ ((9 : ℝ) / 5)) =
        esum G1.μ Gp.E + esum G1.μ Ea + esum G1.μ Eb + E1 * c / 2 +
          η ^ ((9 : ℝ) / 5) * E1 := by
      field_simp
    rw [ex]; linarith
  exact le_of_mul_le_mul_left this hE1

/-- The bound for the `G⁺` candidate. -/
theorem alt_sh_xp (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hq1 : 0 < G1.quality) (hE1 : 0 < esum G1.μ G1.E) (hV1 : 0 < wsum G1.μ G1.V)
    (hW1 : 0 < wsum G1.μ G1.W) (hVkpos : 0 < wsum G1.μ (vslice G1.V p k))
    (hWkpos : 0 < wsum G1.μ (vslice G1.W p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc0 : 0 < c) (hc2 : c ≤ 1 / 2)
    (θ : ℝ) (hθ : θ = if 1 ≤ k then 1 / (p : ℝ) else 0) (hθ2 : θ ≤ 1 / 2)
    (hGp_good : (alt_sh_plus G1 p k hp hpP1).quality < G1.quality) :
    esum G1.μ (alt_sh_plus G1 p k hp hpP1).E / esum G1.μ G1.E <
      (9 * ((1 - wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) /
          wsum G1.μ G1.V) *
        (1 - wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) / wsum G1.μ G1.W) *
          (1 - c)) + (1 - θ) ^ 2 * (1 - c)) / 10 := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Gp := alt_sh_plus G1 p k hp hpP1 with hGp
  set Vm := G1.V.filter (fun v => v.factorization p + 1 = k) with hVm
  set Wm := G1.W.filter (fun w => w.factorization p + 1 = k) with hWm
  set a := wsum G1.μ Vm / V1 with ha
  set b := wsum G1.μ Wm / W1 with hb
  set xp := esum G1.μ Gp.E / E1 with hxp
  have hVmk := alt_sh_disj_le G1 G1.V (fun v => v.factorization p + 1 = k)
    (fun v => v.factorization p = k) (fun v h1 h2 => by omega)
  have hWmk := alt_sh_disj_le G1 G1.W (fun w => w.factorization p + 1 = k)
    (fun w => w.factorization p = k) (fun w h1 h2 => by omega)
  have hVpk : wsum G1.μ (vslice G1.V p k) ≤ wsum G1.μ Gp.V :=
    sum_le_sum_of_subset_of_nonneg
      (fun v hv => mem_filter.2 ⟨(mem_filter.1 hv).1, Or.inl (mem_filter.1 hv).2⟩)
      (fun i _ _ => G1.μ_nonneg i)
  have hWpk : wsum G1.μ (vslice G1.W p k) ≤ wsum G1.μ Gp.W :=
    sum_le_sum_of_subset_of_nonneg
      (fun v hv => mem_filter.2 ⟨(mem_filter.1 hv).1, Or.inl (mem_filter.1 hv).2⟩)
      (fun i _ _ => G1.μ_nonneg i)
  have hVp : 0 < wsum G1.μ Gp.V := lt_of_lt_of_le hVkpos hVpk
  have hWp : 0 < wsum G1.μ Gp.W := lt_of_lt_of_le hWkpos hWpk
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hV1]
    have := alt_sh_wsum_nonneg G1 (vslice G1.V p k)
    have h' : wsum G1.μ Vm + wsum G1.μ (vslice G1.V p k) ≤ V1 := hVmk
    linarith
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one hW1]
    have := alt_sh_wsum_nonneg G1 (vslice G1.W p k)
    have h' : wsum G1.μ Wm + wsum G1.μ (vslice G1.W p k) ≤ W1 := hWmk
    linarith
  have hVpa : wsum G1.μ Gp.V ≤ (1 - a) * V1 := by
    have h := alt_sh_disj_le G1 G1.V
      (fun v => v.factorization p = k ∨ v.factorization p = k + 1)
      (fun v => v.factorization p + 1 = k) (fun v h1 h2 => by omega)
    have e : (1 - a) * V1 = V1 - wsum G1.μ Vm := by rw [ha]; field_simp
    rw [e]
    have : wsum G1.μ Gp.V + wsum G1.μ Vm ≤ V1 := h
    linarith
  have hWpb : wsum G1.μ Gp.W ≤ (1 - b) * W1 := by
    have h := alt_sh_disj_le G1 G1.W
      (fun v => v.factorization p = k ∨ v.factorization p = k + 1)
      (fun v => v.factorization p + 1 = k) (fun v h1 h2 => by omega)
    have e : (1 - b) * W1 = W1 - wsum G1.μ Wm := by rw [hb]; field_simp
    rw [e]
    have : wsum G1.μ Gp.W + wsum G1.μ Wm ≤ W1 := h
    linarith
  have hqp := alt_sh_plus_quality G1 p k hp hpP1 hE1 hV1 hW1 hVp hWp
  set Fp : ℝ := 1 / ((1 - θ) ^ 2 * (1 - c) ^ 10) with hFp
  have hFp0 : 0 < Fp := by
    rw [hFp]; apply div_pos one_pos; apply mul_pos
    · apply pow_pos; linarith
    · apply pow_pos; linarith
  have hXp : xp ^ 10 * (V1 / wsum G1.μ Gp.V) ^ 9 * (W1 / wsum G1.μ Gp.W) ^ 9 * Fp < 1 := by
    have h := hGp_good
    have hqp' : Gp.quality = G1.quality *
        (xp ^ 10 * (V1 / wsum G1.μ Gp.V) ^ 9 * (W1 / wsum G1.μ Gp.W) ^ 9 * Fp) := by
      rw [hqp, hxp, hFp, hθ, hc]; ring
    rw [hqp'] at h
    exact (mul_lt_iff_lt_one_right hq1).1 h
  have hxp0 : 0 ≤ xp := div_nonneg (alt_sh_esum_nonneg G1 _) hE1.le
  have hxp10 := alt_sh_bound1 xp V1 (wsum G1.μ Gp.V) W1 (wsum G1.μ Gp.W) a b Fp hV1 hW1 hVp hWp
    hVpa hWpb hFp0 hXp
  apply alt_sh_amgm xp _ _ hxp0
  · have : 0 ≤ 1 - a := by linarith
    have : 0 ≤ 1 - b := by linarith
    have : 0 ≤ 1 - c := by linarith
    positivity
  · have : 0 ≤ 1 - c := by linarith
    positivity
  · refine lt_of_lt_of_le hxp10 (le_of_eq ?_)
    rw [hFp]
    have h1 : (1 - θ) ≠ 0 := by linarith
    have h2 : (1 - c) ≠ 0 := by linarith
    field_simp

/-- The bound for the `G_{p^k, p^{k-1}}` candidate. -/
theorem alt_sh_xa (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hp0 : (0 : ℝ) < p) (hq1 : 0 < G1.quality) (hE1 : 0 < esum G1.μ G1.E)
    (hV1 : 0 < wsum G1.μ G1.V) (hW1 : 0 < wsum G1.μ G1.W)
    (hVkpos : 0 < wsum G1.μ (vslice G1.V p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc2 : c ≤ 1 / 2)
    (θ : ℝ) (hθ : θ = if 1 ≤ k then 1 / (p : ℝ) else 0) (hθ0 : 0 ≤ θ)
    (hA : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p k (k - 1) hp hpP1).quality)) :
    esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)) /
        esum G1.μ G1.E ≤
      (1 - c) * (9 * (wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) /
        wsum G1.μ G1.W) + θ) / 10 := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Wm := G1.W.filter (fun w => w.factorization p + 1 = k) with hWm
  set Ea := G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)
    with hEa
  set b := wsum G1.μ Wm / W1 with hb
  set xa := esum G1.μ Ea / E1 with hxa
  have hb0 : 0 ≤ b := div_nonneg (alt_sh_wsum_nonneg G1 _) hW1.le
  have hxa0 : 0 ≤ xa := div_nonneg (alt_sh_esum_nonneg G1 _) hE1.le
  have hEa_le : esum G1.μ Ea ≤ wsum G1.μ (vslice G1.V p k) * wsum G1.μ Wm := by
    apply alt_sh_esum_le_prod
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  by_cases hk : 1 ≤ k ∧ 0 < wsum G1.μ Wm
  · have hqa : (G1.restrictPrime p k (k - 1) hp hpP1).quality < G1.quality := by
      by_contra h; push_neg at h; exact hA ⟨hk.1, hk.2, h⟩
    have hWeq : vslice G1.W p (k - 1) = Wm := by
      apply filter_congr; intro w _; omega
    have hWk1 : 0 < wsum G1.μ (vslice G1.W p (k - 1)) := by rw [hWeq]; exact hk.2
    have hqr := quality_restrictPrime G1 p k (k - 1) hp hpP1 hE1 hVkpos hWk1
    have hEeq : esum G1.μ (G1.restrictPrime p k (k - 1) hp hpP1).E = esum G1.μ Ea := by
      show esum G1.μ (G1.E.filter
        (fun e => e.1.factorization p = k ∧ e.2.factorization p = k - 1)) = _
      congr 1
      apply filter_congr; intro e _; omega
    have hd1 : (k - (k - 1)) + ((k - 1) - k) = 1 := by omega
    have hne : ¬ (k = k - 1 ∧ 1 ≤ k) := by omega
    rw [hEeq, hWeq, hd1, if_neg hne] at hqr
    have hX : xa ^ 10 * (V1 / wsum G1.μ (vslice G1.V p k)) ^ 9 * (W1 / wsum G1.μ Wm) ^ 9 *
        ((p : ℝ) / (1 - c) ^ 10) < 1 := by
      have hqr' : (G1.restrictPrime p k (k - 1) hp hpP1).quality = G1.quality *
          (xa ^ 10 * (V1 / wsum G1.μ (vslice G1.V p k)) ^ 9 * (W1 / wsum G1.μ Wm) ^ 9 *
            ((p : ℝ) / (1 - c) ^ 10)) := by
        rw [hqr, hxa, hc]; ring
      rw [hqr'] at hqa
      exact (mul_lt_iff_lt_one_right hq1).1 hqa
    have hWmb : wsum G1.μ Wm ≤ (1 - (1 - b)) * W1 := by
      rw [hb, sub_sub_cancel, div_mul_cancel₀ _ hW1.ne']
    have hVsub : wsum G1.μ (vslice G1.V p k) ≤ (1 - 0) * V1 := by
      rw [sub_zero, one_mul]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G1.μ_nonneg i)
    have hpc10 : 0 < (p : ℝ) / (1 - c) ^ 10 := by
      have : 0 < 1 - c := by linarith
      positivity
    have hx10 := alt_sh_bound1 xa V1 (wsum G1.μ (vslice G1.V p k)) W1 (wsum G1.μ Wm) 0 (1 - b)
      ((p : ℝ) / (1 - c) ^ 10) hV1 hW1 hVkpos hk.2 hVsub hWmb hpc10 hX
    have hlt := alt_sh_amgm xa (b * (1 - c)) ((1 - c) / p) hxa0
      (mul_nonneg hb0 (by linarith)) (div_nonneg (by linarith) hp0.le)
      (by
        refine lt_of_lt_of_le hx10 (le_of_eq ?_)
        have h2 : (1 - c) ≠ 0 := by linarith
        field_simp
        ring)
    have : θ = 1 / p := by rw [hθ, if_pos hk.1]
    rw [this]
    have e : (9 * (b * (1 - c)) + (1 - c) / p) / 10 = (1 - c) * (9 * b + 1 / p) / 10 := by ring
    linarith
  · have hWm0 : wsum G1.μ Wm = 0 := by
      by_contra h
      obtain ⟨w, hw, _⟩ := exists_ne_zero_of_sum_ne_zero h
      have hk1 : 1 ≤ k := by have := (mem_filter.1 hw).2; omega
      exact hk ⟨hk1, lt_of_le_of_ne (alt_sh_wsum_nonneg G1 _) (Ne.symm h)⟩
    have : esum G1.μ Ea ≤ 0 := by rw [hWm0, mul_zero] at hEa_le; exact hEa_le
    have hxa' : xa ≤ 0 := by rw [hxa]; exact div_nonpos_of_nonpos_of_nonneg this hE1.le
    have : 0 ≤ (1 - c) * (9 * b + θ) / 10 := by
      have : 0 ≤ 1 - c := by linarith
      positivity
    linarith

/-- The bound for the `G_{p^{k-1}, p^k}` candidate. -/
theorem alt_sh_xb (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hp0 : (0 : ℝ) < p) (hq1 : 0 < G1.quality) (hE1 : 0 < esum G1.μ G1.E)
    (hV1 : 0 < wsum G1.μ G1.V) (hW1 : 0 < wsum G1.μ G1.W)
    (hWkpos : 0 < wsum G1.μ (vslice G1.W p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc2 : c ≤ 1 / 2)
    (θ : ℝ) (hθ : θ = if 1 ≤ k then 1 / (p : ℝ) else 0) (hθ0 : 0 ≤ θ)
    (hB : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p (k - 1) k hp hpP1).quality)) :
    esum G1.μ (G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)) /
        esum G1.μ G1.E ≤
      (1 - c) * (9 * (wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) /
        wsum G1.μ G1.V) + θ) / 10 := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Vm := G1.V.filter (fun v => v.factorization p + 1 = k) with hVm
  set Eb := G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)
    with hEb
  set a := wsum G1.μ Vm / V1 with ha
  set xb := esum G1.μ Eb / E1 with hxb
  have ha0 : 0 ≤ a := div_nonneg (alt_sh_wsum_nonneg G1 _) hV1.le
  have hxb0 : 0 ≤ xb := div_nonneg (alt_sh_esum_nonneg G1 _) hE1.le
  have hEb_le : esum G1.μ Eb ≤ wsum G1.μ Vm * wsum G1.μ (vslice G1.W p k) := by
    apply alt_sh_esum_le_prod
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  by_cases hk : 1 ≤ k ∧ 0 < wsum G1.μ Vm
  · have hqb : (G1.restrictPrime p (k - 1) k hp hpP1).quality < G1.quality := by
      by_contra h; push_neg at h; exact hB ⟨hk.1, hk.2, h⟩
    have hVeq : vslice G1.V p (k - 1) = Vm := by
      apply filter_congr; intro w _; omega
    have hVk1 : 0 < wsum G1.μ (vslice G1.V p (k - 1)) := by rw [hVeq]; exact hk.2
    have hqr := quality_restrictPrime G1 p (k - 1) k hp hpP1 hE1 hVk1 hWkpos
    have hEeq : esum G1.μ (G1.restrictPrime p (k - 1) k hp hpP1).E = esum G1.μ Eb := by
      show esum G1.μ (G1.E.filter
        (fun e => e.1.factorization p = k - 1 ∧ e.2.factorization p = k)) = _
      congr 1
      apply filter_congr; intro e _; omega
    have hd1 : ((k - 1) - k) + (k - (k - 1)) = 1 := by omega
    have hne : ¬ (k - 1 = k ∧ 1 ≤ k - 1) := by omega
    rw [hEeq, hVeq, hd1, if_neg hne] at hqr
    have hX : xb ^ 10 * (W1 / wsum G1.μ (vslice G1.W p k)) ^ 9 * (V1 / wsum G1.μ Vm) ^ 9 *
        ((p : ℝ) / (1 - c) ^ 10) < 1 := by
      have hqr' : (G1.restrictPrime p (k - 1) k hp hpP1).quality = G1.quality *
          (xb ^ 10 * (W1 / wsum G1.μ (vslice G1.W p k)) ^ 9 * (V1 / wsum G1.μ Vm) ^ 9 *
            ((p : ℝ) / (1 - c) ^ 10)) := by
        rw [hqr, hxb, hc]; ring
      rw [hqr'] at hqb
      exact (mul_lt_iff_lt_one_right hq1).1 hqb
    have hVma : wsum G1.μ Vm ≤ (1 - (1 - a)) * V1 := by
      rw [ha, sub_sub_cancel, div_mul_cancel₀ _ hV1.ne']
    have hWsub : wsum G1.μ (vslice G1.W p k) ≤ (1 - 0) * W1 := by
      rw [sub_zero, one_mul]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G1.μ_nonneg i)
    have hpc10 : 0 < (p : ℝ) / (1 - c) ^ 10 := by
      have : 0 < 1 - c := by linarith
      positivity
    have hx10 := alt_sh_bound1 xb W1 (wsum G1.μ (vslice G1.W p k)) V1 (wsum G1.μ Vm) 0 (1 - a)
      ((p : ℝ) / (1 - c) ^ 10) hW1 hV1 hWkpos hk.2 hWsub hVma hpc10 hX
    have hlt := alt_sh_amgm xb (a * (1 - c)) ((1 - c) / p) hxb0
      (mul_nonneg ha0 (by linarith)) (div_nonneg (by linarith) hp0.le)
      (by
        refine lt_of_lt_of_le hx10 (le_of_eq ?_)
        have h2 : (1 - c) ≠ 0 := by linarith
        field_simp
        ring)
    have : θ = 1 / p := by rw [hθ, if_pos hk.1]
    rw [this]
    have e : (9 * (a * (1 - c)) + (1 - c) / p) / 10 = (1 - c) * (9 * a + 1 / p) / 10 := by ring
    linarith
  · have hVm0 : wsum G1.μ Vm = 0 := by
      by_contra h
      obtain ⟨w, hw, _⟩ := exists_ne_zero_of_sum_ne_zero h
      have hk1 : 1 ≤ k := by have := (mem_filter.1 hw).2; omega
      exact hk ⟨hk1, lt_of_le_of_ne (alt_sh_wsum_nonneg G1 _) (Ne.symm h)⟩
    have : esum G1.μ Eb ≤ 0 := by rw [hVm0, zero_mul] at hEb_le; exact hEb_le
    have hxb' : xb ≤ 0 := by rw [hxb]; exact div_nonpos_of_nonpos_of_nonneg this hE1.le
    have : 0 ≤ (1 - c) * (9 * a + θ) / 10 := by
      have : 0 ≤ 1 - c := by linarith
      positivity
    linarith

/-- The contradiction when none of the three candidates increases the quality. -/
theorem alt_sh_contra (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hpT : T0 ≤ (p : ℝ)) (hp0 : (0 : ℝ) < p) (hp2 : (2 : ℝ) ≤ p) (hq1 : 0 < G1.quality)
    (hE1 : 0 < esum G1.μ G1.E) (hV1 : 0 < wsum G1.μ G1.V) (hW1 : 0 < wsum G1.μ G1.W)
    (η : ℝ) (hη : η = K40 / p) (hη1 : η < 1)
    (hVk : (1 - η) * wsum G1.μ G1.V ≤ wsum G1.μ (vslice G1.V p k))
    (hWk : (1 - η) * wsum G1.μ G1.W ≤ wsum G1.μ (vslice G1.W p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc0 : 0 < c) (hc2 : c ≤ 1 / 2)
    (hcov' : 1 ≤ esum G1.μ (alt_sh_plus G1 p k hp hpP1).E / esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)) /
        esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)) /
        esum G1.μ G1.E + c / 2 + η ^ ((9 : ℝ) / 5))
    (hGp_good : (alt_sh_plus G1 p k hp hpP1).quality < G1.quality)
    (hA : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p k (k - 1) hp hpP1).quality))
    (hB : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p (k - 1) k hp hpP1).quality)) : False := by
  have hVkpos : 0 < wsum G1.μ (vslice G1.V p k) :=
    lt_of_lt_of_le (mul_pos (by linarith) hV1) hVk
  have hWkpos : 0 < wsum G1.μ (vslice G1.W p k) :=
    lt_of_lt_of_le (mul_pos (by linarith) hW1) hWk
  -- the parameter `θ = 1_{k ≥ 1}/p`
  set θ : ℝ := if 1 ≤ k then 1 / (p : ℝ) else 0 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; split_ifs <;> positivity
  have hθ1 : θ ≤ 1 / p := by rw [hθ]; split_ifs <;> [exact le_rfl; positivity]
  have hθ2 : θ ≤ 1 / 2 := le_trans hθ1 (by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith)
  have hxpb := alt_sh_xp G1 p k hp hpP1 hq1 hE1 hV1 hW1 hVkpos hWkpos c hc hc0 hc2 θ hθ hθ2
    hGp_good
  have hxab := alt_sh_xa G1 p k hp hpP1 hp0 hq1 hE1 hV1 hW1 hVkpos c hc hc2 θ hθ hθ0 hA
  have hxbb := alt_sh_xb G1 p k hp hpP1 hp0 hq1 hE1 hV1 hW1 hWkpos c hc hc2 θ hθ hθ0 hB
  -- the measures `a`, `b` of `V_{p^{k-1}}`, `W_{p^{k-1}}`
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Vm := G1.V.filter (fun v => v.factorization p + 1 = k) with hVm
  set Wm := G1.W.filter (fun w => w.factorization p + 1 = k) with hWm
  set a := wsum G1.μ Vm / V1 with ha
  set b := wsum G1.μ Wm / W1 with hb
  have ha0 : 0 ≤ a := div_nonneg (alt_sh_wsum_nonneg G1 _) hV1.le
  have hb0 : 0 ≤ b := div_nonneg (alt_sh_wsum_nonneg G1 _) hW1.le
  have hVmk := alt_sh_disj_le G1 G1.V (fun v => v.factorization p + 1 = k)
    (fun v => v.factorization p = k) (fun v h1 h2 => by omega)
  have hWmk := alt_sh_disj_le G1 G1.W (fun w => w.factorization p + 1 = k)
    (fun w => w.factorization p = k) (fun w h1 h2 => by omega)
  have haη : a ≤ η := by
    rw [ha, div_le_iff₀ hV1]
    have h' : wsum G1.μ Vm + wsum G1.μ (vslice G1.V p k) ≤ V1 := hVmk
    nlinarith
  have hbη : b ≤ η := by
    rw [hb, div_le_iff₀ hW1]
    have h' : wsum G1.μ Wm + wsum G1.μ (vslice G1.W p k) ≤ W1 := hWmk
    nlinarith
  -- numerics
  have hnum := alt_sh_numeric p hpT
  have hsmall : η ^ 2 + θ ^ 2 + η ^ ((9 : ℝ) / 5) ≤ c / 2 := by
    have : θ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ hθ0 hθ1 2
    rw [hη, hc]
    linarith
  exact alt_sh_final _ _ _ a b c θ (η ^ ((9 : ℝ) / 5)) η ha0 hb0 haη hbη hc0.le (by linarith)
    hθ0 hxpb hxab hxbb hcov' hsmall

/-! ### Lemma 14.1 -/

/-- Lemma 14.1 (quality increment even when a prime power divides almost everything). -/
theorem lemma141 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpT : T0 ≤ (p : ℝ)) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = insert p G.P ∧ G'.R ⊆ G.R.erase p ∧
      0 < G'.quality ∧ G.quality ≤ G'.quality := by
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hK40 : (0 : ℝ) < K40 := by unfold K40; positivity
  have hK : K40 < p := by
    have : K40 < T0 := by simp only [K40, T0]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith
  have hpT' : T0 < (p : ℝ) := by
    rcases lt_or_eq_of_le hpT with h | h
    · exact h
    · exfalso
      have hpe : p = 10 ^ 2000 := by
        have : (p : ℝ) = ((10 ^ 2000 : ℕ) : ℝ) := by
          rw [← h]; unfold T0; push_cast; ring
        exact_mod_cast this
      have h2 : 2 ∣ p := by
        rw [hpe]; exact dvd_pow (by norm_num : (2 : ℕ) ∣ 10) (by norm_num)
      have h2p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
      have h10 : 10 ≤ 10 ^ 2000 := Nat.le_self_pow (by norm_num) 10
      rw [← h2p] at hpe
      generalize (10 : ℕ) ^ 2000 = X at hpe h10
      omega
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  -- the constant `c = p^{-31/30}`
  set c : ℝ := 1 / (p : ℝ) ^ ((31 : ℝ) / 30) with hc
  have hpc : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc2 : c ≤ 1 / 2 := by
    rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- sparsify (Lemma 11.6 with `η = 10^40/p`)
  set η : ℝ := K40 / p with hη
  have hη0 : 0 < η := div_pos hK40 hp0
  have hη1 : η < 1 := (div_lt_one hp0).2 hK
  obtain ⟨G1, hG1, hP1, hf1, hg1, hδ1, hqq1, hsp⟩ :=
    exists_sparse_small_sets_subgraph G hδ η hη0 hη1
  have hμ1 : G1.μ = G.μ := hG1.1
  have hq1 : 0 < G1.quality := (quality_pos_iff G1).2 hδ1
  have hpP1 : p ∉ G1.P := hP1 ▸ hpP
  have finish : ∀ G' : GCDGraph, G'.IsSubgraph G1 → G'.P = insert p G1.P →
      G'.R ⊆ G1.R.erase p → G1.quality ≤ G'.quality →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = insert p G.P ∧ G'.R ⊆ G.R.erase p ∧
        0 < G'.quality ∧ G.quality ≤ G'.quality := by
    intro G' h1 h2 h3 h4
    exact ⟨G', h1.trans hG1, by rw [h2, hP1], h3.trans (erase_subset_erase p (R_mono hG1)),
      lt_of_lt_of_le hq (hqq1.trans h4), hqq1.trans h4⟩
  have finishR : ∀ k l, G1.quality ≤ (G1.restrictPrime p k l hp hpP1).quality →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = insert p G.P ∧ G'.R ⊆ G.R.erase p ∧
        0 < G'.quality ∧ G.quality ≤ G'.quality :=
    fun k l h => finish _ (restrictPrime_isSubgraph G1 p k l hp hpP1) rfl
      (R_restrictPrime_subset G1 p k l hp hpP1) h
  -- Lemma 12.2
  rcases lemma122 G1 hδ1 p hp hpP1 hK with ⟨k, l, _, hr⟩ | ⟨k, hVk, hWk⟩
  · apply finishR k l
    have h1 : (1 : ℝ) ≤ 2 ^ (if k ≠ l then 1 else 0) := one_le_pow₀ (by norm_num)
    have h2 : min 1 ((G1.restrictPrime p k l hp hpP1).density / G1.density) *
        ((G1.restrictPrime p k l hp hpP1).quality / G1.quality) ≤
        (G1.restrictPrime p k l hp hpP1).quality / G1.quality :=
      mul_le_of_le_one_left (div_nonneg (quality_nonneg _) hq1.le) (min_le_left _ _)
    exact (one_le_div hq1).1 (by linarith)
  -- Lemmas 11.3 and 11.4 with `r = 1`
  have hpr1 : T0 < (p : ℝ) ^ (1 : ℕ) := by rw [pow_one]; exact hpT'
  rcases lemma113 G1 hδ1 p hp hpP1 1 k le_rfl hpr1 hWk with ⟨l, _, h2q, _⟩ | hbad1
  · exact finishR k l (by linarith)
  rcases lemma114 G1 hδ1 p hp hpP1 1 k le_rfl hpr1 hVk with ⟨l, _, h2q, _⟩ | hbad2
  · exact finishR l k (by linarith)
  obtain ⟨hE1, hV1, hW1⟩ := alt_sh_pos G1 hδ1
  have hcov' := alt_sh_cover G G1 p k hp hpP1 hμ1 hE1 η hVk hWk hsp c hc hbad1 hbad2
  -- candidate 1: `G⁺`
  by_cases hGp_good : G1.quality ≤ (alt_sh_plus G1 p k hp hpP1).quality
  · exact finish _ (alt_sh_plus_isSubgraph G1 p k hp hpP1) rfl (alt_sh_plus_R G1 p k hp hpP1)
      hGp_good
  -- candidate 2: `G_{p^k, p^{k-1}}`
  by_cases hA_good : 1 ≤ k ∧ 0 < wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p k (k - 1) hp hpP1).quality
  · exact finishR k (k - 1) hA_good.2.2
  -- candidate 3: `G_{p^{k-1}, p^k}`
  by_cases hB_good : 1 ≤ k ∧ 0 < wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p (k - 1) k hp hpP1).quality
  · exact finishR (k - 1) k hB_good.2.2
  exact alt_sh_contra G1 p k hp hpP1 hpT hp0 hp2 hq1 hE1 hV1 hW1 η hη hη1 hVk hWk c hc hc0 hc2
    hcov' (lt_of_not_ge hGp_good) hA_good hB_good |>.elim

/-- Proposition 8.2 (iteration when `R♭(G) = ∅`, `R♯(G) ≠ ∅`). -/
theorem prop82 (G : GCDGraph) (hδ : 0 < G.density) (hR : ∀ p ∈ G.R, T0 < (p : ℝ))
    (hflat : G.Rflat = ∅) (hsharp : G.Rsharp.Nonempty) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G.P ⊂ G'.P ∧ G'.P ⊆ G.P ∪ G.R ∧
      G'.R ⊂ G.R ∧ G.quality ≤ G'.quality := by
  classical
  obtain ⟨p, hp⟩ := hsharp
  have hpR : p ∈ G.R := (mem_filter.1 hp).1
  have hpp : p.Prime := G.prime_of_mem_R hpR
  have hpP : p ∉ G.P := G.not_mem_P_of_mem_R hpR
  obtain ⟨G', hG', hP', hR', hq'pos, hqq'⟩ := lemma141 G hδ p hpp hpP (hR p hpR).le
  refine ⟨G', hG', (quality_pos_iff G').1 hq'pos, ?_, ?_, ?_, hqq'⟩
  · rw [hP']; exact ssubset_insert hpP
  · rw [hP']
    intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · exact mem_union_right _ hpR
    · exact mem_union_left _ hq
  · exact lt_of_le_of_lt hR' (erase_ssubset hpR)

end GCDGraph

end DuffinSchaeffer
