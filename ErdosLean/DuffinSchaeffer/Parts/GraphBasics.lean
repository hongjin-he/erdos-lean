import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 11: basic facts on GCD graphs

KM Lemma 6.7, Lemma 11.1 (quality of `G_{p^k,p^ℓ}`),
Lemma 11.2 (pigeonhole over partitions), Lemma 10.1 + Lemma 8.5 (high-degree subgraph),
Lemma 11.5 + Lemma 11.6 (few edges between small sets).  The iterations in 8.5 and 11.6 are
strong inductions on `G.V.card + G.W.card`.
-/

open Finset

namespace DuffinSchaeffer

namespace GCDGraph

/-! ### Auxiliary lemmas -/

theorem alt_wsum_nonneg {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (S : Finset ℕ) : 0 ≤ wsum μ S :=
  Finset.sum_nonneg (fun i _ => hμ i)

theorem alt_esum_nonneg {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (E : Finset (ℕ × ℕ)) :
    0 ≤ esum μ E :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hμ _) (hμ _))

theorem alt_wsum_mono {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) {S T : Finset ℕ} (h : S ⊆ T) :
    wsum μ S ≤ wsum μ T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hμ i)

theorem alt_esum_le {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) {E : Finset (ℕ × ℕ)} {V W : Finset ℕ}
    (h : E ⊆ V ×ˢ W) : esum μ E ≤ wsum μ V * wsum μ W := by
  have h1 : esum μ E ≤ esum μ (V ×ˢ W) :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => mul_nonneg (hμ _) (hμ _))
  refine h1.trans (le_of_eq ?_)
  unfold esum wsum
  rw [Finset.sum_product, Finset.sum_mul_sum]

theorem alt_c_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2 : (1 : ℝ) < (p : ℝ) ^ ((31 : ℝ) / 30) := Real.one_lt_rpow h1 (by norm_num)
  have h3 : 1 / (p : ℝ) ^ ((31 : ℝ) / 30) < 1 := by
    rw [div_lt_one (by linarith)]; exact h2
  linarith

theorem alt_c_le_one (p : ℕ) : 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 := by
  have : 0 ≤ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
  linarith

theorem alt_qf_pos (G : GCDGraph) {p : ℕ} (hp : p.Prime) : 0 < G.qualityFactor p := by
  unfold qualityFactor
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hc := alt_c_pos hp
  have hd : 0 < 1 - (if G.f p = G.g p ∧ 1 ≤ G.f p then 1 / (p : ℝ) else 0) := by
    split_ifs
    · have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact h1
      linarith
    · norm_num
  positivity

theorem alt_prodqf_pos (G : GCDGraph) : 0 < ∏ p ∈ G.P, G.qualityFactor p :=
  Finset.prod_pos (fun p hp => G.alt_qf_pos (G.P_prime p hp))

/-! ### Lemma 6.7 -/

theorem IsSubgraph.refl (G : GCDGraph) : G.IsSubgraph G := by
  exact ⟨rfl, subset_rfl, subset_rfl, subset_rfl, subset_rfl, fun p _ => ⟨rfl, rfl⟩⟩

theorem IsSubgraph.trans {G₁ G₂ G₃ : GCDGraph} (h₁ : G₁.IsSubgraph G₂) (h₂ : G₂.IsSubgraph G₃) :
    G₁.IsSubgraph G₃ := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h₁
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h₂
  exact ⟨a1.trans a2, b1.trans b2, c1.trans c2, d1.trans d2, e2.trans e1, fun p hp =>
    ⟨(f1 p (e2 hp)).1.trans (f2 p hp).1, (f1 p (e2 hp)).2.trans (f2 p hp).2⟩⟩

/-- Lemma 6.7(b). -/
theorem R_mono {G' G : GCDGraph} (h : G'.IsSubgraph G) : G'.R ⊆ G.R := by
  intro p hp
  simp only [R, mem_sdiff, mem_biUnion] at hp ⊢
  obtain ⟨⟨e, he, hpe⟩, hnP⟩ := hp
  exact ⟨⟨e, h.2.2.2.1 he, hpe⟩, fun h' => hnP (h.2.2.2.2.1 h')⟩

theorem density_nonneg (G : GCDGraph) : 0 ≤ G.density :=
  div_nonneg (alt_esum_nonneg G.μ_nonneg _)
    (mul_nonneg (alt_wsum_nonneg G.μ_nonneg _) (alt_wsum_nonneg G.μ_nonneg _))

theorem density_le_one (G : GCDGraph) : G.density ≤ 1 :=
  div_le_one_of_le₀ (alt_esum_le G.μ_nonneg G.E_sub)
    (mul_nonneg (alt_wsum_nonneg G.μ_nonneg _) (alt_wsum_nonneg G.μ_nonneg _))

/-- Lemma 6.7(c)(d). -/
theorem density_pos_iff (G : GCDGraph) : 0 < G.density ↔ G.Nontrivial := by
  constructor
  · intro h
    rcases (alt_esum_nonneg G.μ_nonneg G.E).lt_or_eq with h' | h'
    · exact h'
    · simp [density, ← h'] at h
  · intro h
    exact div_pos h (lt_of_lt_of_le h (alt_esum_le G.μ_nonneg G.E_sub))

theorem wsum_V_pos_of_density_pos (G : GCDGraph) (h : 0 < G.density) : 0 < wsum G.μ G.V := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 h
  have hle := alt_esum_le G.μ_nonneg G.E_sub
  rcases (alt_wsum_nonneg G.μ_nonneg G.V).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at hle; simp at hle; linarith

theorem wsum_W_pos_of_density_pos (G : GCDGraph) (h : 0 < G.density) : 0 < wsum G.μ G.W := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 h
  have hle := alt_esum_le G.μ_nonneg G.E_sub
  rcases (alt_wsum_nonneg G.μ_nonneg G.W).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at hle; simp at hle; linarith

/-- Lemma 6.7(d): `q(G) > 0 ↔ δ(G) > 0`. -/
theorem quality_pos_iff (G : GCDGraph) : 0 < G.quality ↔ 0 < G.density := by
  constructor
  · intro h
    rcases G.density_nonneg.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      unfold quality at h
      rw [← h'] at h
      simp at h
  · intro h
    unfold quality
    have := G.wsum_V_pos_of_density_pos h
    have := G.wsum_W_pos_of_density_pos h
    have := G.alt_prodqf_pos
    positivity

theorem quality_nonneg (G : GCDGraph) : 0 ≤ G.quality := by
  unfold quality
  have := G.density_nonneg
  have := alt_wsum_nonneg G.μ_nonneg G.V
  have := alt_wsum_nonneg G.μ_nonneg G.W
  have := G.alt_prodqf_pos
  positivity

/-- Expression of the quality through `μ(E)`: `q(G) = μ(E)^{10} / (μ(V)^9 μ(W)^9) ∏ …`. -/
theorem quality_eq (G : GCDGraph) :
    G.quality = esum G.μ G.E ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
      ∏ p ∈ G.P, G.qualityFactor p := by
  unfold quality density
  rcases eq_or_ne (wsum G.μ G.V) 0 with hS | hS
  · simp [hS]
  rcases eq_or_ne (wsum G.μ G.W) 0 with hT | hT
  · simp [hT]
  rw [div_pow]
  field_simp

/-! ### Special subgraphs `G_{p^k,p^ℓ}` -/

theorem restrictPrime_isSubgraph (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (G.restrictPrime p k l hp hpP).IsSubgraph G := by
  refine ⟨rfl, filter_subset _ _, filter_subset _ _, filter_subset _ _, subset_insert _ _,
    fun q hq => ?_⟩
  have hne : q ≠ p := fun h => hpP (h ▸ hq)
  exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩

theorem R_restrictPrime_subset (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (G.restrictPrime p k l hp hpP).R ⊆ G.R.erase p := by
  intro q hq
  refine mem_erase.2 ⟨?_, R_mono (G.restrictPrime_isSubgraph p k l hp hpP) hq⟩
  intro h
  rw [h] at hq
  exact (G.restrictPrime p k l hp hpP).not_mem_P_of_mem_R hq (mem_insert_self _ _)

/-- Lemma 11.1. -/
theorem quality_restrictPrime (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hE : 0 < esum G.μ G.E) (hV : 0 < wsum G.μ (vslice G.V p k))
    (hW : 0 < wsum G.μ (vslice G.W p l)) :
    (G.restrictPrime p k l hp hpP).quality =
      G.quality * (esum G.μ (G.restrictPrime p k l hp hpP).E / esum G.μ G.E) ^ 10 *
        (wsum G.μ G.V / wsum G.μ (vslice G.V p k)) ^ 9 *
        (wsum G.μ G.W / wsum G.μ (vslice G.W p l)) ^ 9 *
        ((p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  have hprod : ∏ q ∈ (G.restrictPrime p k l hp hpP).P,
      (G.restrictPrime p k l hp hpP).qualityFactor q =
      ((p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) * ∏ q ∈ G.P, G.qualityFactor q := by
    show ∏ q ∈ insert p G.P, _ = _
    rw [prod_insert hpP]
    congr 1
    · simp only [qualityFactor, fgDist, restrictPrime, Function.update_self]
    · apply prod_congr rfl
      intro q hq
      have hne : q ≠ p := fun h => hpP (h ▸ hq)
      simp only [qualityFactor, fgDist, restrictPrime, Function.update_of_ne hne]
  have hS' := hV
  have hT' := hW
  have hS : 0 < wsum G.μ G.V := lt_of_lt_of_le hV (alt_wsum_mono G.μ_nonneg (filter_subset _ _))
  have hT : 0 < wsum G.μ G.W := lt_of_lt_of_le hW (alt_wsum_mono G.μ_nonneg (filter_subset _ _))
  rw [quality_eq, quality_eq G, hprod]
  change esum G.μ (G.restrictPrime p k l hp hpP).E ^ 10 /
    (wsum G.μ (vslice G.V p k) ^ 9 * wsum G.μ (vslice G.W p l) ^ 9) * _ = _
  field_simp

/-- Adding a prime `p ∉ P` that divides no `gcd(v,w)`, `(v,w) ∈ E`, with `f(p) = g(p) = 0`
(used when `p ∉ R(G)`; the quality gets multiplied by `(1 - p^{-31/30})^{-10} ≥ 1`). -/
theorem exists_addPrime_zero (G : GCDGraph) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpR : p ∉ G.R) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.V = G.V ∧ G'.W = G.W ∧ G'.E = G.E ∧
      G'.P = insert p G.P ∧ G'.f p = 0 ∧ G'.g p = 0 ∧ G'.R ⊆ G.R.erase p ∧
      G.quality ≤ G'.quality ∧ G'.density = G.density := by
  let G' : GCDGraph :=
  { μ := G.μ
    V := G.V
    W := G.W
    E := G.E
    P := insert p G.P
    f := Function.update G.f p 0
    g := Function.update G.g p 0
    μ_nonneg := G.μ_nonneg
    V_pos := G.V_pos
    W_pos := G.W_pos
    E_sub := G.E_sub
    P_prime := by
      intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact hp
      · exact G.P_prime q hq
    dvd_V := by
      intro q hq v hv
      rcases mem_insert.1 hq with rfl | hq'
      · simp
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne]
        exact G.dvd_V q hq' v hv
    dvd_W := by
      intro q hq w hw
      rcases mem_insert.1 hq with rfl | hq'
      · simp
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne]
        exact G.dvd_W q hq' w hw
    gcd_E := by
      intro q hq e he
      rcases mem_insert.1 hq with rfl | hq'
      · simp only [Function.update_self, min_self]
        apply Finsupp.notMem_support_iff.1
        rw [Nat.support_factorization]
        intro hmem
        exact hpR (mem_sdiff.2 ⟨mem_biUnion.2 ⟨e, he, hmem⟩, hpP⟩)
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact G.gcd_E q hq' e he
    exact_V := by
      intro q hq hfg v hv
      rcases mem_insert.1 hq with rfl | hq'
      · simp at hfg
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
        rw [Function.update_of_ne hne]
        exact G.exact_V q hq' hfg v hv
    exact_W := by
      intro q hq hfg w hw
      rcases mem_insert.1 hq with rfl | hq'
      · simp at hfg
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
        rw [Function.update_of_ne hne]
        exact G.exact_W q hq' hfg w hw }
  have hsub : G'.IsSubgraph G := by
    refine ⟨rfl, subset_rfl, subset_rfl, subset_rfl, subset_insert _ _, fun q hq => ?_⟩
    have hne : q ≠ p := fun h => hpP (h ▸ hq)
    exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩
  have hqf : G'.qualityFactor p = 1 / (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 := by
    simp [G', qualityFactor, fgDist]
  have hq : G'.quality = G.quality * G'.qualityFactor p := by
    unfold quality
    rw [show G'.P = insert p G.P from rfl, prod_insert hpP]
    have : ∏ q ∈ G.P, G'.qualityFactor q = ∏ q ∈ G.P, G.qualityFactor q := by
      apply prod_congr rfl
      intro q hq
      have hne : q ≠ p := fun h => hpP (h ▸ hq)
      simp only [G', qualityFactor, fgDist, Function.update_of_ne hne]
    rw [this]
    change G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * _ = _
    ring
  have hge : 1 ≤ G'.qualityFactor p := by
    rw [hqf, one_le_div (by have := alt_c_pos hp; positivity)]
    exact pow_le_one₀ (alt_c_pos hp).le (alt_c_le_one p)
  refine ⟨G', hsub, rfl, rfl, rfl, rfl, by simp [G'], by simp [G'], ?_, ?_, rfl⟩
  · intro q hq
    refine mem_erase.2 ⟨?_, R_mono hsub hq⟩
    intro h
    rw [h] at hq
    exact G'.not_mem_P_of_mem_R hq (mem_insert_self _ _)
  · rw [hq]
    exact le_mul_of_one_le_right G.quality_nonneg hge

/-! ### Lemma 11.2 -/

theorem alt_induce_quality (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (hV : V' ⊆ G.V) (hW : W' ⊆ G.W) (hE : E' ⊆ G.E) (hE' : E' ⊆ V' ×ˢ W') :
    (G.induce V' W' E' hV hW hE hE').quality =
      esum G.μ E' ^ 10 / (wsum G.μ V' ^ 9 * wsum G.μ W' ^ 9) * ∏ p ∈ G.P, G.qualityFactor p :=
  quality_eq _

theorem alt_induce_isSubgraph (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (hV : V' ⊆ G.V) (hW : W' ⊆ G.W) (hE : E' ⊆ G.E) (hE' : E' ⊆ V' ×ˢ W') :
    (G.induce V' W' E' hV hW hE hE').IsSubgraph G :=
  ⟨rfl, hV, hW, hE, subset_rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- Lemma 11.2: given partitions of `V` and `W` indexed by `I` and `J` (via labelling maps),
some block pair keeps a `1/(|I||J|)` share of the density and a `1/(|I||J|)^{10}` share of the
quality. -/
theorem exists_block_subgraph (G : GCDGraph) (hδ : 0 < G.density) (I J : Finset ℕ)
    (iV jW : ℕ → ℕ) (hI : ∀ v ∈ G.V, iV v ∈ I) (hJ : ∀ w ∈ G.W, jW w ∈ J) :
    ∃ i ∈ I, ∃ j ∈ J, ∃ G' : GCDGraph, G'.IsSubgraph G ∧
      G'.V = G.V.filter (fun v => iV v = i) ∧ G'.W = G.W.filter (fun w => jW w = j) ∧
      G'.E = G.E.filter (fun e => iV e.1 = i ∧ jW e.2 = j) ∧
      G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧ 0 < G'.density ∧
      G.density / ((I.card : ℝ) * J.card) ≤ G'.density ∧
      G.quality / ((I.card : ℝ) * J.card) ^ 10 ≤ G'.quality := by
  classical
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 hδ
  have hS := wsum_V_pos_of_density_pos G hδ
  have hT := wsum_W_pos_of_density_pos G hδ
  have hprod := G.alt_prodqf_pos
  have hVne : G.V.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [wsum, h] at hS
  have hWne : G.W.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [wsum, h] at hT
  obtain ⟨v0, hv0⟩ := hVne
  obtain ⟨w0, hw0⟩ := hWne
  have hIne : I.Nonempty := ⟨iV v0, hI v0 hv0⟩
  have hJne : J.Nonempty := ⟨jW w0, hJ w0 hw0⟩
  set c : ℝ := (I.card : ℝ) * J.card with hc_def
  have hc : 0 < c := by
    have h1 : (0 : ℝ) < I.card := by exact_mod_cast card_pos.2 hIne
    have h2 : (0 : ℝ) < J.card := by exact_mod_cast card_pos.2 hJne
    positivity
  let F : ℕ × ℕ → ℝ := fun ij => esum G.μ (G.E.filter (fun e => iV e.1 = ij.1 ∧ jW e.2 = ij.2))
  have hsum : ∑ ij ∈ I ×ˢ J, F ij = esum G.μ G.E := by
    have hmap : ∀ e ∈ G.E, (fun e : ℕ × ℕ => (iV e.1, jW e.2)) e ∈ I ×ˢ J := by
      intro e he'
      have := mem_product.1 (G.E_sub he')
      exact mem_product.2 ⟨hI _ this.1, hJ _ this.2⟩
    have := Finset.sum_fiberwise_of_maps_to hmap (fun e => G.μ e.1 * G.μ e.2)
    unfold esum at this ⊢
    rw [← this]
    apply sum_congr rfl
    intro ij _
    unfold F esum
    apply sum_congr _ (fun _ _ => rfl)
    apply filter_congr
    intro e _
    simp [Prod.ext_iff]
  obtain ⟨ij, hij, hle⟩ := Finset.exists_le_of_sum_le (hIne.product hJne)
    (show ∑ _ij ∈ I ×ˢ J, esum G.μ G.E / c ≤ ∑ ij ∈ I ×ˢ J, F ij by
      rw [hsum, sum_const, card_product, nsmul_eq_mul]
      push_cast
      rw [← hc_def]
      field_simp
      rfl)
  obtain ⟨hi, hj⟩ := mem_product.1 hij
  set E' := G.E.filter (fun e => iV e.1 = ij.1 ∧ jW e.2 = ij.2) with hE'_def
  set V' := G.V.filter (fun v => iV v = ij.1) with hV'_def
  set W' := G.W.filter (fun w => jW w = ij.2) with hW'_def
  have hE'sub : E' ⊆ V' ×ˢ W' := by
    intro e he'
    obtain ⟨he1, h1, h2⟩ := mem_filter.1 he'
    have := mem_product.1 (G.E_sub he1)
    exact mem_product.2 ⟨mem_filter.2 ⟨this.1, h1⟩, mem_filter.2 ⟨this.2, h2⟩⟩
  have hEij : esum G.μ G.E / c ≤ esum G.μ E' := hle
  have hEpos : 0 < esum G.μ E' := lt_of_lt_of_le (div_pos he hc) hEij
  have hEle : esum G.μ E' ≤ wsum G.μ V' * wsum G.μ W' := alt_esum_le G.μ_nonneg hE'sub
  have hVle : wsum G.μ V' ≤ wsum G.μ G.V := alt_wsum_mono G.μ_nonneg (filter_subset _ _)
  have hWle : wsum G.μ W' ≤ wsum G.μ G.W := alt_wsum_mono G.μ_nonneg (filter_subset _ _)
  have hV0 := alt_wsum_nonneg G.μ_nonneg V'
  have hW0 := alt_wsum_nonneg G.μ_nonneg W'
  have hVW : 0 < wsum G.μ V' * wsum G.μ W' := lt_of_lt_of_le hEpos hEle
  have hVp : 0 < wsum G.μ V' := by
    rcases hV0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hVW; simp at hVW
  have hWp : 0 < wsum G.μ W' := by
    rcases hW0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hVW; simp at hVW
  refine ⟨ij.1, hi, ij.2, hj, G.induce V' W' E' (filter_subset _ _) (filter_subset _ _)
    (filter_subset _ _) hE'sub, alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, rfl, rfl,
    rfl, (density_pos_iff _).2 hEpos, ?_, ?_⟩
  · show esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W) / c ≤
      esum G.μ E' / (wsum G.μ V' * wsum G.μ W')
    calc esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W) / c
        = (esum G.μ G.E / c) / (wsum G.μ G.V * wsum G.μ G.W) := by ring
      _ ≤ esum G.μ E' / (wsum G.μ G.V * wsum G.μ G.W) :=
          div_le_div_of_nonneg_right hEij (by positivity)
      _ ≤ esum G.μ E' / (wsum G.μ V' * wsum G.μ W') :=
          div_le_div_of_nonneg_left hEpos.le hVW (mul_le_mul hVle hWle hW0 hS.le)
  · rw [alt_induce_quality, quality_eq]
    calc (esum G.μ G.E ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p) / c ^ 10
        = (esum G.μ G.E / c) ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p := by rw [div_pow]; ring
      _ ≤ esum G.μ E' ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p := by
          gcongr
      _ ≤ esum G.μ E' ^ 10 / (wsum G.μ V' ^ 9 * wsum G.μ W' ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p := by
          gcongr

/-! ### Lemmas 10.1 and 8.5 -/

theorem alt_real_remove (X Y e a n : ℝ) (hY : 0 < Y) (ha : 0 ≤ a) (haX : a ≤ X) (he : 0 < e)
    (heXY : e ≤ X * Y) (hlt : n < 9 * (e / (X * Y)) / 10 * Y) (he' : e - a * n ≤ (X - a) * Y) :
    e / (X * Y) ≤ (e - a * n) / ((X - a) * Y) ∧
    (e / (X * Y)) ^ 10 * X * Y ≤ ((e - a * n) / ((X - a) * Y)) ^ 10 * (X - a) * Y := by
  have hXY : 0 < X * Y := lt_of_lt_of_le he heXY
  set δ := e / (X * Y) with hδdef
  have hδ : 0 ≤ δ := div_nonneg he.le hXY.le
  have hX : 0 < X := (pos_iff_pos_of_mul_pos hXY).2 hY
  have heq : e = δ * X * Y := by rw [hδdef]; field_simp
  have h1 : a * n ≤ a * (9 * δ / 10 * Y) := mul_le_mul_of_nonneg_left hlt.le ha
  have h2 : a * (9 * δ / 10 * Y) ≤ X * (9 * δ / 10 * Y) :=
    mul_le_mul_of_nonneg_right haX (by positivity)
  have hpos' : 0 < e - a * n := by nlinarith
  have hXa : 0 < X - a := by
    by_contra h
    push Not at h
    have : (X - a) * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hY.le
    linarith
  set x := a / (10 * (X - a)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hkey : δ * (1 + x) ≤ (e - a * n) / ((X - a) * Y) := by
    rw [le_div_iff₀ (by positivity)]
    have : δ * (1 + x) * ((X - a) * Y) = δ * X * Y - 9 * δ / 10 * Y * a := by
      rw [hx]; field_simp; ring
    rw [this]; nlinarith
  have hδle : δ ≤ δ * (1 + x) := by nlinarith
  refine ⟨hδle.trans hkey, ?_⟩
  have hb : 1 + ((10 : ℕ) : ℝ) * x ≤ (1 + x) ^ 10 := one_add_mul_le_pow (by linarith) 10
  have h3 : (δ * (1 + x)) ^ 10 ≤ ((e - a * n) / ((X - a) * Y)) ^ 10 :=
    pow_le_pow_left₀ (by positivity) hkey 10
  have h4 : (1 + ((10 : ℕ) : ℝ) * x) * (X - a) = X := by
    rw [hx]; push_cast; field_simp; ring
  calc δ ^ 10 * X * Y = δ ^ 10 * ((1 + ((10 : ℕ) : ℝ) * x) * (X - a)) * Y := by rw [h4]
    _ ≤ δ ^ 10 * ((1 + x) ^ 10 * (X - a)) * Y := by gcongr
    _ = (δ * (1 + x)) ^ 10 * (X - a) * Y := by ring
    _ ≤ _ := by gcongr

theorem alt_esum_split_fst (G : GCDGraph) (v : ℕ) :
    esum G.μ G.E = esum G.μ (G.E.filter (fun e => e.1 ≠ v)) + G.μ v * wsum G.μ (G.nbhdV v) := by
  unfold esum
  rw [← sum_filter_add_sum_filter_not G.E (fun e => e.1 ≠ v)]
  congr 1
  unfold wsum nbhdV
  rw [mul_sum]
  refine Finset.sum_nbij' (fun e => e.2) (fun w => (v, w)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_filter, not_not] at he ⊢
    obtain ⟨he, rfl⟩ := he
    exact ⟨(mem_product.1 (G.E_sub he)).2, he⟩
  · intro w hw
    simp only [mem_filter, not_not] at hw ⊢
    exact ⟨hw.2, trivial⟩
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    rfl
  · intro w _
    rfl
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    rfl

theorem alt_esum_split_snd (G : GCDGraph) (w : ℕ) :
    esum G.μ G.E = esum G.μ (G.E.filter (fun e => e.2 ≠ w)) + G.μ w * wsum G.μ (G.nbhdW w) := by
  unfold esum
  rw [← sum_filter_add_sum_filter_not G.E (fun e => e.2 ≠ w)]
  congr 1
  unfold wsum nbhdW
  rw [mul_sum]
  refine Finset.sum_nbij' (fun e => e.1) (fun v => (v, w)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_filter, not_not] at he ⊢
    obtain ⟨he, rfl⟩ := he
    exact ⟨(mem_product.1 (G.E_sub he)).1, he⟩
  · intro v hv
    simp only [mem_filter, not_not] at hv ⊢
    exact ⟨hv.2, trivial⟩
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    rfl
  · intro v _
    rfl
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    ring

theorem alt_step10 (G : GCDGraph) (hδ : 0 < G.density) (hH : ¬ G.HighDegree) :
    ∃ G1 : GCDGraph, G1.IsSubgraph G ∧ G1.P = G.P ∧ G1.f = G.f ∧ G1.g = G.g ∧
      G1.V.card + G1.W.card < G.V.card + G.W.card ∧ G.density ≤ G1.density ∧
      G.quality ≤ G1.quality := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 hδ
  have heST := alt_esum_le G.μ_nonneg G.E_sub
  have hS := wsum_V_pos_of_density_pos G hδ
  have hT := wsum_W_pos_of_density_pos G hδ
  have hprod := G.alt_prodqf_pos
  rw [HighDegree, not_and_or] at hH
  rcases hH with hH | hH
  · push Not at hH
    obtain ⟨v, hv, hlt⟩ := hH
    have hE' : G.E.filter (fun e => e.1 ≠ v) ⊆ (G.V.erase v) ×ˢ G.W := by
      intro e he
      rw [mem_filter] at he
      have := mem_product.1 (G.E_sub he.1)
      exact mem_product.2 ⟨mem_erase.2 ⟨he.2, this.1⟩, this.2⟩
    have hsplit := G.alt_esum_split_fst v
    have hVe : wsum G.μ (G.V.erase v) = wsum G.μ G.V - G.μ v := by
      unfold wsum; rw [sum_erase_eq_sub hv]
    have hle' := alt_esum_le G.μ_nonneg hE'
    have hEf : esum G.μ (G.E.filter (fun e => e.1 ≠ v)) =
        esum G.μ G.E - G.μ v * wsum G.μ (G.nbhdV v) := by linarith
    obtain ⟨h1, h2⟩ := alt_real_remove (wsum G.μ G.V) (wsum G.μ G.W) (esum G.μ G.E) (G.μ v)
      (wsum G.μ (G.nbhdV v)) hT (G.μ_nonneg v)
      (single_le_sum (fun i _ => G.μ_nonneg i) hv) he heST hlt
      (by rw [← hEf, ← hVe]; exact hle')
    refine ⟨G.induce (G.V.erase v) G.W _ (erase_subset _ _) subset_rfl (filter_subset _ _) hE',
      alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show (G.V.erase v).card + G.W.card < _
      rw [card_erase_of_mem hv]
      have := card_pos.2 ⟨v, hv⟩
      omega
    · show G.density ≤ esum G.μ (G.E.filter (fun e => e.1 ≠ v)) /
        (wsum G.μ (G.V.erase v) * wsum G.μ G.W)
      rw [hEf, hVe]; exact h1
    · show G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p ≤
        (esum G.μ (G.E.filter (fun e => e.1 ≠ v)) / (wsum G.μ (G.V.erase v) * wsum G.μ G.W)) ^ 10 *
          wsum G.μ (G.V.erase v) * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p
      rw [hEf, hVe]
      exact mul_le_mul_of_nonneg_right h2 hprod.le
  · push Not at hH
    obtain ⟨w, hw, hlt⟩ := hH
    have hE' : G.E.filter (fun e => e.2 ≠ w) ⊆ G.V ×ˢ (G.W.erase w) := by
      intro e he
      rw [mem_filter] at he
      have := mem_product.1 (G.E_sub he.1)
      exact mem_product.2 ⟨this.1, mem_erase.2 ⟨he.2, this.2⟩⟩
    have hsplit := G.alt_esum_split_snd w
    have hWe : wsum G.μ (G.W.erase w) = wsum G.μ G.W - G.μ w := by
      unfold wsum; rw [sum_erase_eq_sub hw]
    have hle' := alt_esum_le G.μ_nonneg hE'
    have hEf : esum G.μ (G.E.filter (fun e => e.2 ≠ w)) =
        esum G.μ G.E - G.μ w * wsum G.μ (G.nbhdW w) := by linarith
    have hden : G.density = esum G.μ G.E / (wsum G.μ G.W * wsum G.μ G.V) := by
      rw [density, mul_comm]
    rw [hden] at hlt
    obtain ⟨h1, h2⟩ := alt_real_remove (wsum G.μ G.W) (wsum G.μ G.V) (esum G.μ G.E) (G.μ w)
      (wsum G.μ (G.nbhdW w)) hS (G.μ_nonneg w)
      (single_le_sum (fun i _ => G.μ_nonneg i) hw) he (by rw [mul_comm]; exact heST) hlt
      (by rw [← hEf, ← hWe, mul_comm]; exact hle')
    refine ⟨G.induce G.V (G.W.erase w) _ subset_rfl (erase_subset _ _) (filter_subset _ _) hE',
      alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show G.V.card + (G.W.erase w).card < _
      rw [card_erase_of_mem hw]
      have := card_pos.2 ⟨w, hw⟩
      omega
    · show G.density ≤ esum G.μ (G.E.filter (fun e => e.2 ≠ w)) /
        (wsum G.μ G.V * wsum G.μ (G.W.erase w))
      rw [hEf, hWe, hden, mul_comm (wsum G.μ G.V)]; exact h1
    · show G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p ≤
        (esum G.μ (G.E.filter (fun e => e.2 ≠ w)) / (wsum G.μ G.V * wsum G.μ (G.W.erase w))) ^ 10 *
          wsum G.μ G.V * wsum G.μ (G.W.erase w) * ∏ p ∈ G.P, G.qualityFactor p
      rw [hEf, hWe, hden, mul_comm (wsum G.μ G.V) (wsum G.μ G.W - G.μ w)]
      have h2' : (esum G.μ G.E / (wsum G.μ G.W * wsum G.μ G.V)) ^ 10 * wsum G.μ G.V *
          wsum G.μ G.W ≤ ((esum G.μ G.E - G.μ w * wsum G.μ (G.nbhdW w)) /
            ((wsum G.μ G.W - G.μ w) * wsum G.μ G.V)) ^ 10 * wsum G.μ G.V *
              (wsum G.μ G.W - G.μ w) := by
        linarith
      exact mul_le_mul_of_nonneg_right h2' hprod.le

/-- Lemma 8.5 (by iterating Lemma 10.1). -/
theorem exists_highDegree_subgraph (G : GCDGraph) (hδ : 0 < G.density) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
      0 < G'.density ∧ G.density ≤ G'.density ∧ G.quality ≤ G'.quality ∧ G'.HighDegree := by
  suffices H : ∀ n, ∀ G : GCDGraph, G.V.card + G.W.card = n → 0 < G.density →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
        0 < G'.density ∧ G.density ≤ G'.density ∧ G.quality ≤ G'.quality ∧ G'.HighDegree from
    H _ G rfl hδ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hδ
  by_cases hH : G.HighDegree
  · exact ⟨G, IsSubgraph.refl G, rfl, rfl, rfl, hδ, le_rfl, le_rfl, hH⟩
  obtain ⟨G1, hsub, hP, hf, hg, hlt, hδ1, hq1⟩ := alt_step10 G hδ hH
  obtain ⟨G', h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih _ (hn ▸ hlt) G1 rfl (hδ.trans_le hδ1)
  exact ⟨G', h1.trans hsub, h2.trans hP, h3.trans hf, h4.trans hg, h5, hδ1.trans h6,
    hq1.trans h7, h8⟩

/-! ### Lemmas 11.5 and 11.6 -/

theorem alt_real_sparse (S T e e1 A B η : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hAS : A ≤ η * S) (hBT : B ≤ η * T) (he : 0 ≤ e) (hη : 0 < η)
    (he1 : η ^ ((9 : ℝ) / 5) * e < e1) :
    e ^ 10 / (S ^ 9 * T ^ 9) ≤ e1 ^ 10 / (A ^ 9 * B ^ 9) := by
  have hr : (η ^ ((9 : ℝ) / 5)) ^ 10 = η ^ 18 := by
    rw [← Real.rpow_natCast (η ^ ((9 : ℝ) / 5)) 10, ← Real.rpow_mul hη.le,
      show (9 : ℝ) / 5 * ((10 : ℕ) : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hηr : 0 < η ^ ((9 : ℝ) / 5) := Real.rpow_pos_of_pos hη _
  rcases eq_or_ne (S ^ 9 * T ^ 9) 0 with h0 | h0
  · rw [h0, div_zero]; positivity
  have hST : 0 ≤ S ^ 9 * T ^ 9 := by
    have h1 : 0 ≤ A ^ 9 := by positivity
    have h2 : A ^ 9 ≤ (η * S) ^ 9 := pow_le_pow_left₀ hA.le hAS 9
    have h3 : 0 ≤ B ^ 9 := by positivity
    have h4 : B ^ 9 ≤ (η * T) ^ 9 := pow_le_pow_left₀ hB.le hBT 9
    have h5 : 0 ≤ (η * S) ^ 9 * (η * T) ^ 9 := by
      have := mul_le_mul h2 h4 h3 (h1.trans h2)
      have : 0 ≤ A ^ 9 * B ^ 9 := by positivity
      linarith
    have : (η * S) ^ 9 * (η * T) ^ 9 = η ^ 18 * (S ^ 9 * T ^ 9) := by ring
    rw [this] at h5
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0:ℝ) < η ^ 18)
  have hSTp : 0 < S ^ 9 * T ^ 9 := lt_of_le_of_ne hST (Ne.symm h0)
  rw [div_le_div_iff₀ hSTp (by positivity)]
  have h2 : A ^ 9 ≤ (η * S) ^ 9 := pow_le_pow_left₀ hA.le hAS 9
  have h4 : B ^ 9 ≤ (η * T) ^ 9 := pow_le_pow_left₀ hB.le hBT 9
  calc e ^ 10 * (A ^ 9 * B ^ 9) ≤ e ^ 10 * ((η * S) ^ 9 * (η * T) ^ 9) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h2 h4 (by positivity) ((by positivity : (0:ℝ) ≤ A ^ 9).trans h2)
    _ = (η ^ ((9 : ℝ) / 5) * e) ^ 10 * (S ^ 9 * T ^ 9) := by
        rw [show (η ^ ((9 : ℝ) / 5) * e) ^ 10 = η ^ 18 * e ^ 10 by rw [mul_pow, hr]]; ring
    _ ≤ e1 ^ 10 * (S ^ 9 * T ^ 9) := by
        apply mul_le_mul_of_nonneg_right _ hSTp.le
        exact pow_le_pow_left₀ (by positivity) he1.le 10

theorem alt_step115 (G : GCDGraph) (hδ : 0 < G.density) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hA : ¬ ∀ A ⊆ G.V, ∀ B ⊆ G.W, wsum G.μ A ≤ η * wsum G.μ G.V → wsum G.μ B ≤ η * wsum G.μ G.W →
        esum G.μ (G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G.E) :
    ∃ G1 : GCDGraph, G1.IsSubgraph G ∧ G1.P = G.P ∧ G1.f = G.f ∧ G1.g = G.g ∧
      G1.V.card + G1.W.card < G.V.card + G.W.card ∧ 0 < G1.density ∧
      G.quality ≤ G1.quality := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 hδ
  have hS := wsum_V_pos_of_density_pos G hδ
  have hT := wsum_W_pos_of_density_pos G hδ
  have hprod := G.alt_prodqf_pos
  push Not at hA
  obtain ⟨A, hAV, B, hBW, hAS, hBT, hlt⟩ := hA
  set E1 := G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B) with hE1
  have hE1sub : E1 ⊆ A ×ˢ B := by
    intro e he'
    obtain ⟨_, h1, h2⟩ := mem_filter.1 he'
    exact mem_product.2 ⟨h1, h2⟩
  have hηr : 0 < η ^ ((9 : ℝ) / 5) := Real.rpow_pos_of_pos hη0 _
  have he1 : 0 < esum G.μ E1 := lt_of_le_of_lt (by positivity) hlt
  have hle := alt_esum_le G.μ_nonneg hE1sub
  have hA0 := alt_wsum_nonneg G.μ_nonneg A
  have hB0 := alt_wsum_nonneg G.μ_nonneg B
  have hAB : 0 < wsum G.μ A * wsum G.μ B := lt_of_lt_of_le he1 hle
  have hAp : 0 < wsum G.μ A := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hAB; simp at hAB
  have hBp : 0 < wsum G.μ B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hAB; simp at hAB
  have hAne : A ≠ G.V := by
    rintro rfl
    nlinarith
  have hBne : B ≠ G.W := by
    rintro rfl
    nlinarith
  have hAc : A.card < G.V.card := card_lt_card (hAV.ssubset_of_ne hAne)
  have hBc : B.card < G.W.card := card_lt_card (hBW.ssubset_of_ne hBne)
  refine ⟨G.induce A B E1 hAV hBW (filter_subset _ _) hE1sub,
    alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, by show A.card + B.card < _; omega,
    (density_pos_iff _).2 he1, ?_⟩
  rw [alt_induce_quality, quality_eq]
  exact mul_le_mul_of_nonneg_right (alt_real_sparse _ _ _ _ _ _ η hAp hBp hAS hBT he.le hη0 hlt)
    hprod.le

/-- Lemma 11.6 (by iterating Lemma 11.5). -/
theorem exists_sparse_small_sets_subgraph (G : GCDGraph) (hδ : 0 < G.density) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
      0 < G'.density ∧ G.quality ≤ G'.quality ∧
      ∀ A ⊆ G'.V, ∀ B ⊆ G'.W, wsum G.μ A ≤ η * wsum G.μ G'.V → wsum G.μ B ≤ η * wsum G.μ G'.W →
        esum G.μ (G'.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G'.E := by
  suffices H : ∀ n, ∀ G : GCDGraph, G.V.card + G.W.card = n → 0 < G.density →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
        0 < G'.density ∧ G.quality ≤ G'.quality ∧
        ∀ A ⊆ G'.V, ∀ B ⊆ G'.W, wsum G.μ A ≤ η * wsum G.μ G'.V →
          wsum G.μ B ≤ η * wsum G.μ G'.W →
          esum G.μ (G'.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤
            η ^ ((9 : ℝ) / 5) * esum G.μ G'.E from
    H _ G rfl hδ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hδ
  by_cases hA : ∀ A ⊆ G.V, ∀ B ⊆ G.W, wsum G.μ A ≤ η * wsum G.μ G.V →
      wsum G.μ B ≤ η * wsum G.μ G.W →
      esum G.μ (G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G.E
  · exact ⟨G, IsSubgraph.refl G, rfl, rfl, rfl, hδ, le_rfl, hA⟩
  obtain ⟨G1, hsub, hP, hf, hg, hlt, hδ1, hq1⟩ := alt_step115 G hδ η hη0 hη1 hA
  obtain ⟨G', h1, h2, h3, h4, h5, h7, h8⟩ := ih _ (hn ▸ hlt) G1 rfl hδ1
  have hμ : G1.μ = G.μ := hsub.1
  rw [hμ] at h8
  exact ⟨G', h1.trans hsub, h2.trans hP, h3.trans hf, h4.trans hg, h5, hq1.trans h7, h8⟩

end GCDGraph

end DuffinSchaeffer
