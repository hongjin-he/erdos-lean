import ErdosLean.DuffinSchaeffer.Parts.GraphBasics

/-!
# Duffin–Schaeffer — Part 13: iteration for generic primes (KM §12: Lemmas 12.1, 12.2, Prop. 8.1)


Lemma 12.1 is proved with the weight `(20/21)^{|k-ℓ|}` in place of KM's
`2^{-|k-ℓ|/20}` (any geometric weight with ratio `≥ 2^{-1/11}` works).
-/

open Finset

namespace DuffinSchaeffer

namespace GCDGraph

/-! ### Auxiliary real-variable lemmas (Lemma 12.1) -/

/-- The lower bound of (our version of) KM Lemma 12.1. -/
noncomputable def alt_gp_B (α β : ℕ → ℝ) (k l : ℕ) : ℝ :=
  if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else
    (α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l))) *
      (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000

theorem alt_gp_geom_eq (m : ℕ) :
    ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) = 20 * (1 - (20 / 21 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring

theorem alt_gp_geom_le (m : ℕ) : ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) ≤ 20 := by
  rw [alt_gp_geom_eq]
  have : (0 : ℝ) ≤ (20 / 21 : ℝ) ^ m := by positivity
  linarith

theorem alt_gp_offdiag (n k : ℕ) :
    ∑ l ∈ range n, (if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k))) ≤ 40 := by
  have hpt : ∀ l ∈ range n, (if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k))) ≤
      (if l < k then (20 / 21 : ℝ) ^ (k - l) else 0) +
        (if k < l then (20 / 21 : ℝ) ^ (l - k) else 0) := by
    intro l _
    rcases lt_trichotomy l k with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), add_zero]
      have : l - k = 0 := by omega
      rw [this, add_zero]
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add]
      have : k - l = 0 := by omega
      rw [this, zero_add]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have h1 : ∑ l ∈ (range n).filter (fun l => l < k), (20 / 21 : ℝ) ^ (k - l) ≤ 20 := by
    have hsub : (range n).filter (fun l => l < k) ⊆ range k := by
      intro l hl; simp only [mem_filter, mem_range] at hl ⊢; exact hl.2
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
    rw [← sum_range_reflect]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_gp_geom_le k)
    intro j hj
    simp only [mem_range] at hj
    congr 1
    omega
  have h2 : ∑ l ∈ (range n).filter (fun l => k < l), (20 / 21 : ℝ) ^ (l - k) ≤ 20 := by
    have hset : (range n).filter (fun l => k < l) = Ico (k + 1) n := by
      ext l; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hset, sum_Ico_eq_sum_range]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_gp_geom_le (n - (k + 1)))
    intro j _
    congr 1
    omega
  linarith

theorem alt_gp_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ ((1 : ℝ) / 2) ≤ (a + b) / 2 := by
  rw [Real.mul_rpow ha hb]
  have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 2) (w₂ := 1 / 2) (p₁ := a) (p₂ := b)
    (by norm_num) (by norm_num) ha hb (by norm_num)
  linarith

theorem alt_gp_sum_bound (n : ℕ) (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : ∑ k ∈ range n, α k = 1) (hβ : ∑ k ∈ range n, β k = 1) :
    ∑ k ∈ range n, ∑ l ∈ range n, alt_gp_B α β k l ≤ 1 := by
  have hα1 : ∀ k ∈ range n, α k ≤ 1 := fun k hk => by
    rw [← hα]; exact single_le_sum (fun i _ => hα0 i) hk
  have hβ1 : ∀ k ∈ range n, β k ≤ 1 := fun k hk => by
    rw [← hβ]; exact single_le_sum (fun i _ => hβ0 i) hk
  have hn : (range n).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; rw [h, sum_empty] at hα; norm_num at hα
  set A : ℕ → ℝ := fun k => α k * (1 - β k) + β k * (1 - α k) with hA
  set e : ℕ → ℕ → ℝ := fun k l =>
    if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k)) with he
  have hA0 : ∀ k ∈ range n, 0 ≤ A k := fun k hk => by
    have := hα1 k hk; have := hβ1 k hk; have := hα0 k; have := hβ0 k
    simp only [hA]; nlinarith
  have he0 : ∀ k l, 0 ≤ e k l := fun k l => by simp only [he]; split_ifs <;> positivity
  have hesymm : ∀ k l, e k l = e l k := fun k l => by
    simp only [he]
    by_cases h : k = l
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), add_comm]
  have hB : ∀ k l, alt_gp_B α β k l =
      (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0) +
        (A k * e k l / 1000 + A l * e k l / 1000) := fun k l => by
    simp only [alt_gp_B, hA, he]
    split_ifs <;> ring
  simp_rw [hB, sum_add_distrib]
  rw [sum_comm (f := fun k l => A l * e k l / 1000)]
  -- diagonal part
  have hdiag : ∀ k ∈ range n, ∑ l ∈ range n, (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0)
      = (α k * β k) ^ ((9 : ℝ) / 10) := fun k hk => by rw [sum_ite_eq, if_pos hk]
  rw [sum_congr rfl hdiag]
  -- off-diagonal parts
  have hoff1 : ∀ k ∈ range n, ∑ l ∈ range n, A k * e k l / 1000 ≤ A k * 40 / 1000 := by
    intro k hk
    rw [← sum_div, ← mul_sum]
    gcongr
    · exact hA0 k hk
    · exact alt_gp_offdiag n k
  have hoff2 : ∀ l ∈ range n, ∑ k ∈ range n, A l * e k l / 1000 ≤ A l * 40 / 1000 := by
    intro l hl
    simp_rw [hesymm _ l]
    exact hoff1 l hl
  have hS2 := add_le_add (sum_le_sum hoff1) (sum_le_sum hoff2)
  -- sum of A
  set D := ∑ k ∈ range n, α k * β k with hD
  have hsumA : ∑ k ∈ range n, A k * 40 / 1000 = (2 - 2 * D) * 40 / 1000 := by
    rw [← sum_div, ← sum_mul]
    congr 2
    simp only [hA, hD, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, hα, hβ]
    rw [show ∑ i ∈ range n, β i * α i = ∑ i ∈ range n, α i * β i from
      sum_congr rfl fun i _ => mul_comm _ _]
    ring
  -- the maximum γ
  obtain ⟨k0, hk0, hmax⟩ := exists_max_image (range n) (fun k => α k * β k) hn
  set γ := α k0 * β k0 with hγ
  have hγ0 : 0 ≤ γ := mul_nonneg (hα0 k0) (hβ0 k0)
  have hγ1 : γ ≤ 1 := by
    have := hα1 k0 hk0; have := hβ1 k0 hk0
    calc γ = α k0 * β k0 := rfl
      _ ≤ 1 * 1 := mul_le_mul (hα1 k0 hk0) (hβ1 k0 hk0) (hβ0 k0) zero_le_one
      _ = 1 := by norm_num
  have hDγ : γ ≤ D := single_le_sum (f := fun k => α k * β k)
    (fun i _ => mul_nonneg (hα0 i) (hβ0 i)) hk0
  have hS1 : ∑ k ∈ range n, (α k * β k) ^ ((9 : ℝ) / 10) ≤ γ ^ ((2 : ℝ) / 5) := by
    have hpt : ∀ k ∈ range n, (α k * β k) ^ ((9 : ℝ) / 10) ≤
        γ ^ ((2 : ℝ) / 5) * ((α k + β k) / 2) := by
      intro k hk
      have hx0 : 0 ≤ α k * β k := mul_nonneg (hα0 k) (hβ0 k)
      rw [show (9 : ℝ) / 10 = 2 / 5 + 1 / 2 by norm_num, Real.rpow_add' hx0 (by norm_num)]
      exact mul_le_mul (Real.rpow_le_rpow hx0 (hmax k hk) (by norm_num))
        (alt_gp_sqrt_le _ _ (hα0 k) (hβ0 k)) (by positivity) (by positivity)
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [← mul_sum, ← sum_div, sum_add_distrib, hα, hβ]
    norm_num
  have hbern : γ ^ ((2 : ℝ) / 5) ≤ 1 + 2 / 5 * (γ - 1) := by
    have := _root_.rpow_one_add_le_one_add_mul_self (s := γ - 1) (by linarith)
      (p := (2 : ℝ) / 5) (by norm_num) (by norm_num)
    simpa using this
  linarith

/-! ### Graph-side lemmas -/

theorem alt_gp_pos (G : GCDGraph) (hδ : 0 < G.density) :
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

theorem alt_gp_wsum_nonneg (G : GCDGraph) (S : Finset ℕ) : 0 ≤ wsum G.μ S :=
  sum_nonneg fun i _ => G.μ_nonneg i

theorem alt_gp_esum_nonneg (G : GCDGraph) (S : Finset (ℕ × ℕ)) : 0 ≤ esum G.μ S :=
  sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)

theorem alt_gp_vslice_le (G : GCDGraph) (S : Finset ℕ) (p k : ℕ) :
    wsum G.μ (vslice S p k) ≤ wsum G.μ S :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G.μ_nonneg i)

theorem alt_gp_two_slices (G : GCDGraph) (S : Finset ℕ) (p k l : ℕ) (hkl : k ≠ l) :
    wsum G.μ (vslice S p k) + wsum G.μ (vslice S p l) ≤ wsum G.μ S := by
  unfold wsum vslice
  rw [← sum_union (disjoint_filter.2 (fun v _ h1 h2 => hkl (h1.symm.trans h2)))]
  exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun i _ _ => G.μ_nonneg i)

theorem alt_gp_wsum_partition (G : GCDGraph) (S : Finset ℕ) (p N : ℕ)
    (hN : ∀ v ∈ S, v.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), wsum G.μ (vslice S p k) = wsum G.μ S := by
  unfold wsum vslice
  exact sum_fiberwise_of_maps_to (fun v hv => mem_range.2 (Nat.lt_succ_of_le (hN v hv))) G.μ

theorem alt_gp_esum_partition (G : GCDGraph) (p N : ℕ)
    (hN : ∀ e ∈ G.E, e.1.factorization p ≤ N ∧ e.2.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1),
      esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) =
      esum G.μ G.E := by
  rw [← sum_product' (f := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)))]
  have h := sum_fiberwise_of_maps_to (s := G.E) (t := range (N + 1) ×ˢ range (N + 1))
    (g := fun e : ℕ × ℕ => (e.1.factorization p, e.2.factorization p))
    (fun e he => mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le (hN e he).1),
      mem_range.2 (Nat.lt_succ_of_le (hN e he).2)⟩) (fun e => G.μ e.1 * G.μ e.2)
  unfold esum
  rw [← h]
  refine sum_congr rfl fun x _ => sum_congr ?_ fun _ _ => rfl
  ext e
  simp [Prod.ext_iff]

theorem alt_gp_esum_slice_le (G : GCDGraph) (p k l : ℕ) :
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) ≤
      wsum G.μ (vslice G.V p k) * wsum G.μ (vslice G.W p l) := by
  have hsub : G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l) ⊆
      vslice G.V p k ×ˢ vslice G.W p l := by
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))

theorem alt_gp_B_nonneg (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα1 : ∀ k, α k ≤ 1) (hβ1 : ∀ k, β k ≤ 1) (k l : ℕ) : 0 ≤ alt_gp_B α β k l := by
  unfold alt_gp_B
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg (hα0 k) (hβ0 k)) _
  · have := hα0 k; have := hβ0 k; have := hα1 k; have := hβ1 k
    have := hα0 l; have := hβ0 l; have := hα1 l; have := hβ1 l
    have h1 : 0 ≤ α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l)) := by
      nlinarith
    positivity

/-- KM Lemma 12.1 (with our weights). -/
theorem alt_gp_lemma121 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) :
    ∃ k l : ℕ, 0 < wsum G.μ (vslice G.V p k) ∧ 0 < wsum G.μ (vslice G.W p l) ∧
      alt_gp_B (fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V)
          (fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W) k l * esum G.μ G.E ≤
        esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) := by
  obtain ⟨hE, hV, hW⟩ := alt_gp_pos G hδ
  set N := (G.V ∪ G.W).sup (fun v => v.factorization p) with hNdef
  have hNV : ∀ v ∈ G.V, v.factorization p ≤ N := fun v hv =>
    le_sup (f := fun v => v.factorization p) (mem_union_left _ hv)
  have hNW : ∀ v ∈ G.W, v.factorization p ≤ N := fun v hv =>
    le_sup (f := fun v => v.factorization p) (mem_union_right _ hv)
  have hNE : ∀ e ∈ G.E, e.1.factorization p ≤ N ∧ e.2.factorization p ≤ N := fun e he => by
    obtain ⟨hv, hw⟩ := mem_product.1 (G.E_sub he)
    exact ⟨hNV _ hv, hNW _ hw⟩
  set α : ℕ → ℝ := fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V with hα
  set β : ℕ → ℝ := fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W with hβ
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (alt_gp_wsum_nonneg G _) hV.le
  have hβ0 : ∀ k, 0 ≤ β k := fun k => div_nonneg (alt_gp_wsum_nonneg G _) hW.le
  have hα1 : ∀ k, α k ≤ 1 := fun k => (div_le_one hV).2 (alt_gp_vslice_le G _ _ _)
  have hβ1 : ∀ k, β k ≤ 1 := fun k => (div_le_one hW).2 (alt_gp_vslice_le G _ _ _)
  have hαs : ∑ k ∈ range (N + 1), α k = 1 := by
    simp only [hα]; rw [← sum_div, alt_gp_wsum_partition G _ p N hNV, div_self hV.ne']
  have hβs : ∑ k ∈ range (N + 1), β k = 1 := by
    simp only [hβ]; rw [← sum_div, alt_gp_wsum_partition G _ p N hNW, div_self hW.ne']
  have hsum := alt_gp_sum_bound (N + 1) α β hα0 hβ0 hαs hβs
  by_contra hcon
  push_neg at hcon
  set Ekl : ℕ → ℕ → ℝ := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) with hEkl
  have hle : ∀ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 ≤ alt_gp_B α β x.1 x.2 * esum G.μ G.E := by
    intro x _
    by_cases h : 0 < wsum G.μ (vslice G.V p x.1) ∧ 0 < wsum G.μ (vslice G.W p x.2)
    · exact (hcon x.1 x.2 h.1 h.2).le
    · have h0 : wsum G.μ (vslice G.V p x.1) * wsum G.μ (vslice G.W p x.2) = 0 := by
        rcases not_and_or.1 h with h | h
        · rw [le_antisymm (not_lt.1 h) (alt_gp_wsum_nonneg G _), zero_mul]
        · rw [le_antisymm (not_lt.1 h) (alt_gp_wsum_nonneg G _), mul_zero]
      calc Ekl x.1 x.2 ≤ _ := alt_gp_esum_slice_le G p x.1 x.2
        _ = 0 := h0
        _ ≤ _ := mul_nonneg (alt_gp_B_nonneg α β hα0 hβ0 hα1 hβ1 _ _) hE.le
  have hpart : ∑ x ∈ range (N + 1) ×ˢ range (N + 1), Ekl x.1 x.2 = esum G.μ G.E := by
    rw [sum_product' (f := Ekl)]; exact alt_gp_esum_partition G p N hNE
  have hex : ∃ x ∈ range (N + 1) ×ˢ range (N + 1), (0 : ℝ) < Ekl x.1 x.2 := by
    apply exists_lt_of_sum_lt
    rw [hpart, sum_const_zero]; exact hE
  obtain ⟨x, hx, hxpos⟩ := hex
  have hlt : ∃ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 < alt_gp_B α β x.1 x.2 * esum G.μ G.E := by
    refine ⟨x, hx, hcon x.1 x.2 ?_ ?_⟩
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_gp_wsum_nonneg G _)
      have := alt_gp_esum_slice_le G p x.1 x.2
      rw [h0', zero_mul] at this
      exact absurd hxpos (not_lt.2 this)
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_gp_wsum_nonneg G _)
      have := alt_gp_esum_slice_le G p x.1 x.2
      rw [h0', mul_zero] at this
      exact absurd hxpos (not_lt.2 this)
  have := sum_lt_sum hle hlt
  rw [hpart, ← sum_mul, sum_product' (f := fun k l => alt_gp_B α β k l)] at this
  have h2 := mul_le_mul_of_nonneg_right hsum hE.le
  linarith

/-! ### Real-variable core of Lemma 12.2 -/

theorem alt_gp_F_ge (p : ℕ) (hp : p.Prime) (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    (p : ℝ) ^ j ≤ (p : ℝ) ^ j / ((1 - c) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpr : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq0 : 0 < 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
  have hq1 : 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  apply le_div_self (by positivity)
  · apply mul_pos
    · apply pow_pos; linarith
    · apply pow_pos; linarith
  · calc (1 - c) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 ≤ 1 * 1 := by
          apply mul_le_mul _ _ (by apply pow_nonneg; linarith) zero_le_one
          · apply pow_le_one₀ <;> linarith
          · apply pow_le_one₀ <;> linarith
      _ = 1 := by norm_num

/-- The key lower bound: `min(1, δ'/δ) q'/q ≥ (S²/y) P / (2·10^33)`. -/
theorem alt_gp_key (a b x S F P : ℝ) (j : ℕ) (ha : 0 < a) (hb : 0 < b) (hSy : a * b ≤ S)
    (hx : S * (20 / 21 : ℝ) ^ j / 1000 ≤ x) (hj : 1 ≤ j) (hP : 2 ≤ P) (hF : P ^ j ≤ F) :
    S ^ 2 / (a * b) * P / (2 * 10 ^ 33) ≤
      min 1 (x / (a * b)) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) := by
  set y := a * b with hy
  have hy0 : 0 < y := mul_pos ha hb
  have hS0 : 0 < S := lt_of_lt_of_le hy0 hSy
  set t : ℝ := (20 / 21 : ℝ) ^ j / 1000 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have : (20 / 21 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [ht]; linarith
  have hxS : S * t ≤ x := by rw [ht, ← mul_div_assoc]; exact hx
  have hx0 : 0 < x := lt_of_lt_of_le (mul_pos hS0 ht0) hxS
  have hmin : t ≤ min 1 (x / y) := by
    apply le_min ht1
    rw [le_div_iff₀ hy0]
    calc t * y ≤ t * S := mul_le_mul_of_nonneg_left hSy ht0.le
      _ = S * t := mul_comm _ _
      _ ≤ x := hxS
  have hab : (1 / a) ^ 9 * (1 / b) ^ 9 = 1 / y ^ 9 := by
    rw [hy, mul_pow, one_div_pow, one_div_pow, one_div_mul_one_div]
  have hF0 : 0 < F := lt_of_lt_of_le (by positivity) hF
  have h10 : (S * t) ^ 10 ≤ x ^ 10 := pow_le_pow_left₀ (by positivity) hxS 10
  have hS8 : y ^ 8 ≤ S ^ 8 := pow_le_pow_left₀ hy0.le hSy 8
  -- t^11 P^j ≥ P / (2·10^33)
  have htP : P / (2 * 10 ^ 33) ≤ t ^ 11 * P ^ j := by
    have hr : (1 : ℝ) / 2 ≤ (20 / 21 : ℝ) ^ 11 := by norm_num
    have hbase : 1 ≤ (20 / 21 : ℝ) ^ 11 * P := by nlinarith
    have hpow : (20 / 21 : ℝ) ^ 11 * P ≤ ((20 / 21 : ℝ) ^ 11 * P) ^ j := by
      conv_lhs => rw [← pow_one ((20 / 21 : ℝ) ^ 11 * P)]
      exact pow_le_pow_right₀ hbase hj
    have : t ^ 11 * P ^ j = ((20 / 21 : ℝ) ^ 11 * P) ^ j / 10 ^ 33 := by
      rw [ht, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 11]; ring
    rw [this, le_div_iff₀ (by norm_num)]
    have : P / (2 * 10 ^ 33) * 10 ^ 33 = (1 / 2) * P := by ring
    rw [this]
    nlinarith
  -- main chain
  have hmain : t * (x ^ 10 * (1 / y ^ 9) * F) ≥ t ^ 11 * P ^ j * (S ^ 2 / y) := by
    have h1 : x ^ 10 * (1 / y ^ 9) * F ≥ (S * t) ^ 10 * (1 / y ^ 9) * P ^ j := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right h10 (by positivity)) hF (by positivity)
        (by positivity)
    have h2 : (S * t) ^ 10 * (1 / y ^ 9) * P ^ j ≥ t ^ 10 * P ^ j * (S ^ 2 / y) := by
      have : S ^ 2 / y ≤ S ^ 10 * (1 / y ^ 9) := by
        rw [div_le_iff₀ hy0]
        have e : S ^ 10 * (1 / y ^ 9) * y = S ^ 2 * (S ^ 8 / y ^ 8) := by
          field_simp
        rw [e]
        have : 1 ≤ S ^ 8 / y ^ 8 := by rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith [sq_nonneg S]
      calc t ^ 10 * P ^ j * (S ^ 2 / y) ≤ t ^ 10 * P ^ j * (S ^ 10 * (1 / y ^ 9)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (S * t) ^ 10 * (1 / y ^ 9) * P ^ j := by ring
    calc t ^ 11 * P ^ j * (S ^ 2 / y) = t * (t ^ 10 * P ^ j * (S ^ 2 / y)) := by ring
      _ ≤ t * ((S * t) ^ 10 * (1 / y ^ 9) * P ^ j) := mul_le_mul_of_nonneg_left h2 ht0.le
      _ ≤ t * (x ^ 10 * (1 / y ^ 9) * F) := mul_le_mul_of_nonneg_left h1 ht0.le
  have hval : min 1 (x / y) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) =
      min 1 (x / y) * (x ^ 10 * (1 / y ^ 9) * F) := by
    rw [mul_assoc (x ^ 10), hab]
  rw [hval]
  have hnn : 0 ≤ x ^ 10 * (1 / y ^ 9) * F := by positivity
  calc S ^ 2 / y * P / (2 * 10 ^ 33) = P / (2 * 10 ^ 33) * (S ^ 2 / y) := by ring
    _ ≤ t ^ 11 * P ^ j * (S ^ 2 / y) :=
        mul_le_mul_of_nonneg_right htP (by positivity)
    _ ≤ t * (x ^ 10 * (1 / y ^ 9) * F) := hmain
    _ ≤ min 1 (x / y) * (x ^ 10 * (1 / y ^ 9) * F) := mul_le_mul_of_nonneg_right hmin hnn

/-- Case `k = ℓ` of Lemma 12.2: no quality loss. -/
theorem alt_gp_diag (a b x F : ℝ) (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hx : (a * b) ^ ((9 : ℝ) / 10) ≤ x) (hF : 1 ≤ F) :
    1 ≤ min 1 (x / (a * b)) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) := by
  set y := a * b with hy
  have hy0 : 0 < y := mul_pos ha hb
  have hy1 : y ≤ 1 := by
    calc y = a * b := rfl
      _ ≤ 1 * 1 := mul_le_mul ha1 hb1 hb.le zero_le_one
      _ = 1 := by norm_num
  have hyx : y ≤ x := by
    refine le_trans ?_ hx
    conv_lhs => rw [← Real.rpow_one y]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by norm_num)
  have hmin : min 1 (x / y) = 1 := by
    rw [min_eq_left]; rw [le_div_iff₀ hy0]; linarith
  have hab : (1 / a) ^ 9 * (1 / b) ^ 9 = 1 / y ^ 9 := by
    rw [hy, mul_pow, one_div_pow, one_div_pow, one_div_mul_one_div]
  rw [hmin, one_mul, mul_assoc (x ^ 10), hab]
  have hx10 : y ^ 9 ≤ x ^ 10 := by
    have h1 : ((y ^ ((9 : ℝ) / 10)) ^ (10 : ℕ)) = y ^ 9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    rw [← h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hy0.le _) hx 10
  have : 1 ≤ x ^ 10 * (1 / y ^ 9) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
  nlinarith

/-- From a small `S²/y` to the sharp alternative. -/
theorem alt_gp_sharp_real (ak bk al bl η : ℝ) (hak0 : 0 ≤ ak) (hbk0 : 0 ≤ bk) (hal0 : 0 ≤ al)
    (hbl0 : 0 ≤ bl) (hak1 : ak ≤ 1) (hbk1 : bk ≤ 1) (hal1 : al ≤ 1) (hbl1 : bl ≤ 1)
    (hy : 0 < ak * bl)
    (hQ : (ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al))) ^ 2 / (ak * bl) ≤ 1 / 5)
    (hS : ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) ≤ η)
    (hη : 2 * η ≤ 1 / 2) :
    (1 - ak ≤ 2 * η ∧ 1 - bk ≤ 2 * η) ∨ (1 - al ≤ 2 * η ∧ 1 - bl ≤ 2 * η) := by
  set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hSdef
  have t1 : 0 ≤ ak * (1 - bk) := mul_nonneg hak0 (by linarith)
  have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
  have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
  have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hbl0 (by linarith)
  by_cases hbk : 1 / 2 ≤ bk
  · left
    have h1 : 1 - ak ≤ 2 * η := by nlinarith
    refine ⟨h1, ?_⟩
    have : 1 / 2 ≤ ak := by linarith
    nlinarith
  by_cases hal : 1 / 2 ≤ al
  · right
    have h1 : 1 - bl ≤ 2 * η := by nlinarith
    refine ⟨?_, h1⟩
    have : 1 / 2 ≤ bl := by linarith
    nlinarith
  exfalso
  push_neg at hbk hal
  have hS1 : (ak + bl) / 2 ≤ S := by nlinarith
  have hS2 : ak * bl ≤ S ^ 2 := by nlinarith [sq_nonneg (ak - bl)]
  rw [div_le_iff₀ hy] at hQ
  nlinarith

/-! ### Lemma 12.2 -/

/-- Lemma 12.2 (with Lemma 12.1 inside its proof).  For a prime `p ∉ P`, `p > 10^40`, either some
`G_{p^k,p^ℓ}` has `min(1, δ'/δ) q'/q ≥ 2^{1_{k ≠ ℓ}}`, or `p` is sharp. -/
theorem lemma122 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpK : K40 < p) :
    (∃ k l : ℕ, 0 < (G.restrictPrime p k l hp hpP).density ∧
        (2 : ℝ) ^ (if k ≠ l then 1 else 0) ≤
          min 1 ((G.restrictPrime p k l hp hpP).density / G.density) *
            ((G.restrictPrime p k l hp hpP).quality / G.quality)) ∨
      G.IsSharp p := by
  obtain ⟨hE, hV, hW⟩ := alt_gp_pos G hδ
  obtain ⟨k, l, hVk, hWl, hB⟩ := alt_gp_lemma121 G hδ p
  set G' := G.restrictPrime p k l hp hpP with hG'
  set E' := esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    with hE'
  set Vk := wsum G.μ (vslice G.V p k) with hVkdef
  set Wl := wsum G.μ (vslice G.W p l) with hWldef
  set V := wsum G.μ G.V with hVdef
  set W := wsum G.μ G.W with hWdef
  set E := esum G.μ G.E with hEdef
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hq' := quality_restrictPrime G p k l hp hpP hE hVk hWl
  set F := (p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) with hFdef
  have hF : (p : ℝ) ^ ((k - l) + (l - k)) ≤ F := by
    apply alt_gp_F_ge p hp
    · split_ifs <;> positivity
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      split_ifs
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      · norm_num
  have hq'' : G'.quality = G.quality * (E' / E) ^ 10 * (V / Vk) ^ 9 * (W / Wl) ^ 9 * F := hq'
  have hdens : G'.density / G.density = (E' / E) / ((Vk / V) * (Wl / W)) := by
    show (E' / (Vk * Wl)) / (E / (V * W)) = _
    field_simp
  have hqual : G'.quality / G.quality =
      (E' / E) ^ 10 * (1 / (Vk / V)) ^ 9 * (1 / (Wl / W)) ^ 9 * F := by
    rw [hq'', one_div_div, one_div_div, mul_assoc, mul_assoc, mul_assoc,
      mul_div_cancel_left₀ _ hq.ne']
    ring
  have hE'E : E' ≤ E := by
    unfold E' E esum
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))
  have hα0 : 0 < Vk / V := div_pos hVk hV
  have hβ0 : 0 < Wl / W := div_pos hWl hW
  have hα1 : Vk / V ≤ 1 := (div_le_one hV).2 (alt_gp_vslice_le G _ _ _)
  have hβ1 : Wl / W ≤ 1 := (div_le_one hW).2 (alt_gp_vslice_le G _ _ _)
  by_cases hkl : k = l
  · -- Case 1
    subst hkl
    left
    refine ⟨k, k, ?_, ?_⟩
    · have hx : (Vk / V * (Wl / W)) ^ ((9 : ℝ) / 10) ≤ E' / E := by
        rw [le_div_iff₀ hE]; simpa [alt_gp_B] using hB
      have : 0 < E' := by
        have := mul_pos (Real.rpow_pos_of_pos (mul_pos hα0 hβ0) ((9 : ℝ) / 10)) hE
        have h2 := (le_div_iff₀ hE).1 hx
        linarith
      show 0 < E' / (Vk * Wl)
      positivity
    · rw [if_neg (by simp), pow_zero, hdens, hqual]
      apply alt_gp_diag _ _ _ _ hα0 hβ0 hα1 hβ1
      · rw [le_div_iff₀ hE]; simpa [alt_gp_B] using hB
      · simpa using hF
  · -- Case 2
    set ak := Vk / V
    set bl := Wl / W
    set bk := wsum G.μ (vslice G.W p k) / W with hbk
    set al := wsum G.μ (vslice G.V p l) / V with hal
    have hbk0 : 0 ≤ bk := div_nonneg (alt_gp_wsum_nonneg G _) hW.le
    have hal0 : 0 ≤ al := div_nonneg (alt_gp_wsum_nonneg G _) hV.le
    have hbk1 : bk ≤ 1 := (div_le_one hW).2 (alt_gp_vslice_le G _ _ _)
    have hal1 : al ≤ 1 := (div_le_one hV).2 (alt_gp_vslice_le G _ _ _)
    have hbsum : bk + bl ≤ 1 := by
      rw [hbk, ← add_div, div_le_one hW]; exact alt_gp_two_slices G _ p k l hkl
    set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hS
    have hSy : ak * bl ≤ S := by
      have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
      have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
      have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hβ0.le (by linarith)
      have : ak * bl ≤ ak * (1 - bk) := mul_le_mul_of_nonneg_left (by linarith) hα0.le
      linarith
    have hj : 1 ≤ (k - l) + (l - k) := by omega
    have hx : S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 ≤ E' / E := by
      rw [le_div_iff₀ hE]; simpa [alt_gp_B, hkl] using hB
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hkey := alt_gp_key ak bl (E' / E) S F p ((k - l) + (l - k)) hα0 hβ0 hSy hx hj hP hF
    have hE'pos : 0 < E' := by
      have h1 : 0 < S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 := by
        have := lt_of_lt_of_le (mul_pos hα0 hβ0) hSy; positivity
      have := lt_of_lt_of_le h1 hx
      exact (div_pos_iff_of_pos_right hE).1 this
    have hdpos : 0 < G'.density := by
      show 0 < E' / (Vk * Wl)
      positivity
    by_cases hbig : (2 : ℝ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality)
    · left
      refine ⟨k, l, hdpos, ?_⟩
      rw [if_pos hkl, pow_one]; exact hbig
    · right
      push_neg at hbig
      rw [hdens, hqual] at hbig
      have hy0 : 0 < ak * bl := mul_pos hα0 hβ0
      have hpK' : (10 : ℝ) ^ 40 < p := by simpa [K40] using hpK
      have hQ : S ^ 2 / (ak * bl) < 4 * 10 ^ 33 / p := by
        have h1 := lt_of_le_of_lt hkey hbig
        have h2 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 * 10 ^ 33)).1 h1
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have hSQ : S ≤ S ^ 2 / (ak * bl) := by
        rw [le_div_iff₀ hy0]
        have : 0 < S := lt_of_lt_of_le hy0 hSy
        calc S * (ak * bl) ≤ S * S := mul_le_mul_of_nonneg_left hSy this.le
          _ = S ^ 2 := (sq S).symm
      have hsmall : 4 * 10 ^ 33 / (p : ℝ) ≤ 1 / 10 ^ 6 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hres := alt_gp_sharp_real ak bk al bl (4 * 10 ^ 33 / p) hα0.le hbk0 hal0 hβ0.le
        hα1 hbk1 hal1 hβ1 hy0 (by linarith) (by linarith) (by linarith)
      have hKp : 2 * (4 * 10 ^ 33 / (p : ℝ)) ≤ K40 / p := by
        rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
        simp only [K40]; norm_num
      rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨k, ?_, ?_⟩
        · have : 1 - K40 / p ≤ ak := by linarith
          calc (1 - K40 / p) * V ≤ ak * V := mul_le_mul_of_nonneg_right this hV.le
            _ = Vk := div_mul_cancel₀ _ hV.ne'
        · have : 1 - K40 / p ≤ bk := by linarith
          calc (1 - K40 / p) * W ≤ bk * W := mul_le_mul_of_nonneg_right this hW.le
            _ = wsum G.μ (vslice G.W p k) := div_mul_cancel₀ _ hW.ne'
      · refine ⟨l, ?_, ?_⟩
        · have : 1 - K40 / p ≤ al := by linarith
          calc (1 - K40 / p) * V ≤ al * V := mul_le_mul_of_nonneg_right this hV.le
            _ = wsum G.μ (vslice G.V p l) := div_mul_cancel₀ _ hV.ne'
        · have : 1 - K40 / p ≤ bl := by linarith
          calc (1 - K40 / p) * W ≤ bl * W := mul_le_mul_of_nonneg_right this hW.le
            _ = Wl := div_mul_cancel₀ _ hW.ne'

/-- Proposition 8.1 (iteration when `R♭(G) ≠ ∅`). -/
theorem prop81 (G : GCDGraph) (hδ : 0 < G.density) (hR : ∀ p ∈ G.R, T0 < (p : ℝ))
    (hflat : G.Rflat.Nonempty) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G.P ⊂ G'.P ∧ G'.P ⊆ G.P ∪ G.R ∧
      G'.R ⊂ G.R ∧
      (2 : ℝ) ^ (newUnequal G' G) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
  classical
  obtain ⟨p, hp⟩ := hflat
  have hpR : p ∈ G.R := (mem_filter.1 hp).1
  have hns : ¬ G.IsSharp p := by
    have := (mem_filter.1 hp).2
    convert this
  have hpp : p.Prime := G.prime_of_mem_R hpR
  have hpP : p ∉ G.P := G.not_mem_P_of_mem_R hpR
  have hpK : K40 < p := by
    have h1 := hR p hpR
    have h2 : K40 < T0 := by
      simp only [K40, T0]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith
  rcases lemma122 G hδ p hpp hpP hpK with ⟨k, l, hd, hq⟩ | hsh
  · refine ⟨G.restrictPrime p k l hpp hpP, restrictPrime_isSubgraph G p k l hpp hpP, hd, ?_, ?_,
      ?_, ?_⟩
    · exact ssubset_insert hpP
    · intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact mem_union_right _ hpR
      · exact mem_union_left _ hq
    · refine lt_of_le_of_lt (R_restrictPrime_subset G p k l hpp hpP) ?_
      exact erase_ssubset hpR
    · have hN : newUnequal (G.restrictPrime p k l hpp hpP) G = if k ≠ l then 1 else 0 := by
        unfold newUnequal
        have hset : (insert p G.P \ G.P) = {p} := by
          ext q; simp only [mem_sdiff, mem_insert, mem_singleton]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact h1
            · exact absurd h1 h2
          · rintro rfl; exact ⟨Or.inl rfl, hpP⟩
        show ((insert p G.P \ G.P).filter
          (fun q => Function.update G.f p k q ≠ Function.update G.g p l q)).card = _
        rw [hset, filter_singleton, Function.update_self, Function.update_self]
        split_ifs <;> simp
      rw [hN]; exact hq
  · exact absurd hsh hns

end GCDGraph

end DuffinSchaeffer
