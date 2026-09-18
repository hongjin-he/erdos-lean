import ErdosLean.DuffinSchaeffer.Parts.Unbalanced
import ErdosLean.DuffinSchaeffer.Parts.GenericPrimes

/-!
# Duffin–Schaeffer — Part 14: bounded quality loss for small primes
(KM §13: Lemmas 13.1, 13.2, Prop. 8.3)


(Alt version.)  The auxiliary lemmas `alt_sp_*` re-prove (our version of) KM Lemma 12.1 locally,
with the weight `(20/21)^{|k-ℓ|}` in place of `2^{-|k-ℓ|/20}`.  In Lemma 13.2 we use `r = 7000`
(so `2^r > 10^{2000}` is elementary) instead of KM's `r ≤ 6644`.
-/

open Finset

namespace DuffinSchaeffer

namespace GCDGraph

/-! ### Auxiliary real-variable lemmas (Lemma 12.1) -/

/-- The lower bound of (our version of) KM Lemma 12.1. -/
noncomputable def alt_sp_B (α β : ℕ → ℝ) (k l : ℕ) : ℝ :=
  if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else
    (α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l))) *
      (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000

theorem alt_sp_geom_eq (m : ℕ) :
    ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) = 20 * (1 - (20 / 21 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring

theorem alt_sp_geom_le (m : ℕ) : ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) ≤ 20 := by
  rw [alt_sp_geom_eq]
  have : (0 : ℝ) ≤ (20 / 21 : ℝ) ^ m := by positivity
  linarith

theorem alt_sp_offdiag (n k : ℕ) :
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
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_sp_geom_le k)
    intro j hj
    simp only [mem_range] at hj
    congr 1
    omega
  have h2 : ∑ l ∈ (range n).filter (fun l => k < l), (20 / 21 : ℝ) ^ (l - k) ≤ 20 := by
    have hset : (range n).filter (fun l => k < l) = Ico (k + 1) n := by
      ext l; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hset, sum_Ico_eq_sum_range]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_sp_geom_le (n - (k + 1)))
    intro j _
    congr 1
    omega
  linarith

theorem alt_sp_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ ((1 : ℝ) / 2) ≤ (a + b) / 2 := by
  rw [Real.mul_rpow ha hb]
  have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 2) (w₂ := 1 / 2) (p₁ := a) (p₂ := b)
    (by norm_num) (by norm_num) ha hb (by norm_num)
  linarith

theorem alt_sp_sum_bound (n : ℕ) (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : ∑ k ∈ range n, α k = 1) (hβ : ∑ k ∈ range n, β k = 1) :
    ∑ k ∈ range n, ∑ l ∈ range n, alt_sp_B α β k l ≤ 1 := by
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
  have hB : ∀ k l, alt_sp_B α β k l =
      (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0) +
        (A k * e k l / 1000 + A l * e k l / 1000) := fun k l => by
    simp only [alt_sp_B, hA, he]
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
    · exact alt_sp_offdiag n k
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
        (alt_sp_sqrt_le _ _ (hα0 k) (hβ0 k)) (by positivity) (by positivity)
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [← mul_sum, ← sum_div, sum_add_distrib, hα, hβ]
    norm_num
  have hbern : γ ^ ((2 : ℝ) / 5) ≤ 1 + 2 / 5 * (γ - 1) := by
    have := _root_.rpow_one_add_le_one_add_mul_self (s := γ - 1) (by linarith)
      (p := (2 : ℝ) / 5) (by norm_num) (by norm_num)
    simpa using this
  linarith

/-! ### Graph-side lemmas -/

theorem alt_sp_pos (G : GCDGraph) (hδ : 0 < G.density) :
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

theorem alt_sp_wsum_nonneg (G : GCDGraph) (S : Finset ℕ) : 0 ≤ wsum G.μ S :=
  sum_nonneg fun i _ => G.μ_nonneg i

theorem alt_sp_esum_nonneg (G : GCDGraph) (S : Finset (ℕ × ℕ)) : 0 ≤ esum G.μ S :=
  sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)

theorem alt_sp_vslice_le (G : GCDGraph) (S : Finset ℕ) (p k : ℕ) :
    wsum G.μ (vslice S p k) ≤ wsum G.μ S :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G.μ_nonneg i)

theorem alt_sp_two_slices (G : GCDGraph) (S : Finset ℕ) (p k l : ℕ) (hkl : k ≠ l) :
    wsum G.μ (vslice S p k) + wsum G.μ (vslice S p l) ≤ wsum G.μ S := by
  unfold wsum vslice
  rw [← sum_union (disjoint_filter.2 (fun v _ h1 h2 => hkl (h1.symm.trans h2)))]
  exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun i _ _ => G.μ_nonneg i)

theorem alt_sp_wsum_partition (G : GCDGraph) (S : Finset ℕ) (p N : ℕ)
    (hN : ∀ v ∈ S, v.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), wsum G.μ (vslice S p k) = wsum G.μ S := by
  unfold wsum vslice
  exact sum_fiberwise_of_maps_to (fun v hv => mem_range.2 (Nat.lt_succ_of_le (hN v hv))) G.μ

theorem alt_sp_esum_partition (G : GCDGraph) (p N : ℕ)
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

theorem alt_sp_esum_slice_le (G : GCDGraph) (p k l : ℕ) :
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

theorem alt_sp_B_nonneg (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα1 : ∀ k, α k ≤ 1) (hβ1 : ∀ k, β k ≤ 1) (k l : ℕ) : 0 ≤ alt_sp_B α β k l := by
  unfold alt_sp_B
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg (hα0 k) (hβ0 k)) _
  · have := hα0 k; have := hβ0 k; have := hα1 k; have := hβ1 k
    have := hα0 l; have := hβ0 l; have := hα1 l; have := hβ1 l
    have h1 : 0 ≤ α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l)) := by
      nlinarith
    positivity

/-- KM Lemma 12.1 (with our weights). -/
theorem alt_sp_lemma121 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) :
    ∃ k l : ℕ, 0 < wsum G.μ (vslice G.V p k) ∧ 0 < wsum G.μ (vslice G.W p l) ∧
      alt_sp_B (fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V)
          (fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W) k l * esum G.μ G.E ≤
        esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) := by
  obtain ⟨hE, hV, hW⟩ := alt_sp_pos G hδ
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
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (alt_sp_wsum_nonneg G _) hV.le
  have hβ0 : ∀ k, 0 ≤ β k := fun k => div_nonneg (alt_sp_wsum_nonneg G _) hW.le
  have hα1 : ∀ k, α k ≤ 1 := fun k => (div_le_one hV).2 (alt_sp_vslice_le G _ _ _)
  have hβ1 : ∀ k, β k ≤ 1 := fun k => (div_le_one hW).2 (alt_sp_vslice_le G _ _ _)
  have hαs : ∑ k ∈ range (N + 1), α k = 1 := by
    simp only [hα]; rw [← sum_div, alt_sp_wsum_partition G _ p N hNV, div_self hV.ne']
  have hβs : ∑ k ∈ range (N + 1), β k = 1 := by
    simp only [hβ]; rw [← sum_div, alt_sp_wsum_partition G _ p N hNW, div_self hW.ne']
  have hsum := alt_sp_sum_bound (N + 1) α β hα0 hβ0 hαs hβs
  by_contra hcon
  push_neg at hcon
  set Ekl : ℕ → ℕ → ℝ := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) with hEkl
  have hle : ∀ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 ≤ alt_sp_B α β x.1 x.2 * esum G.μ G.E := by
    intro x _
    by_cases h : 0 < wsum G.μ (vslice G.V p x.1) ∧ 0 < wsum G.μ (vslice G.W p x.2)
    · exact (hcon x.1 x.2 h.1 h.2).le
    · have h0 : wsum G.μ (vslice G.V p x.1) * wsum G.μ (vslice G.W p x.2) = 0 := by
        rcases not_and_or.1 h with h | h
        · rw [le_antisymm (not_lt.1 h) (alt_sp_wsum_nonneg G _), zero_mul]
        · rw [le_antisymm (not_lt.1 h) (alt_sp_wsum_nonneg G _), mul_zero]
      calc Ekl x.1 x.2 ≤ _ := alt_sp_esum_slice_le G p x.1 x.2
        _ = 0 := h0
        _ ≤ _ := mul_nonneg (alt_sp_B_nonneg α β hα0 hβ0 hα1 hβ1 _ _) hE.le
  have hpart : ∑ x ∈ range (N + 1) ×ˢ range (N + 1), Ekl x.1 x.2 = esum G.μ G.E := by
    rw [sum_product' (f := Ekl)]; exact alt_sp_esum_partition G p N hNE
  have hex : ∃ x ∈ range (N + 1) ×ˢ range (N + 1), (0 : ℝ) < Ekl x.1 x.2 := by
    apply exists_lt_of_sum_lt
    rw [hpart, sum_const_zero]; exact hE
  obtain ⟨x, hx, hxpos⟩ := hex
  have hlt : ∃ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 < alt_sp_B α β x.1 x.2 * esum G.μ G.E := by
    refine ⟨x, hx, hcon x.1 x.2 ?_ ?_⟩
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_sp_wsum_nonneg G _)
      have := alt_sp_esum_slice_le G p x.1 x.2
      rw [h0', zero_mul] at this
      exact absurd hxpos (not_lt.2 this)
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_sp_wsum_nonneg G _)
      have := alt_sp_esum_slice_le G p x.1 x.2
      rw [h0', mul_zero] at this
      exact absurd hxpos (not_lt.2 this)
  have := sum_lt_sum hle hlt
  rw [hpart, ← sum_mul, sum_product' (f := fun k l => alt_sp_B α β k l)] at this
  have h2 := mul_le_mul_of_nonneg_right hsum hE.le
  linarith

/-! ### Real-variable core of Lemma 12.2 -/

theorem alt_sp_F_ge (p : ℕ) (hp : p.Prime) (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
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
theorem alt_sp_key (a b x S F P : ℝ) (j : ℕ) (ha : 0 < a) (hb : 0 < b) (hSy : a * b ≤ S)
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
theorem alt_sp_diag (a b x F : ℝ) (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
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
theorem alt_sp_sharp_real (ak bk al bl η : ℝ) (hak0 : 0 ≤ ak) (hbk0 : 0 ≤ bk) (hal0 : 0 ≤ al)
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


/-! ### Ratio bookkeeping -/

theorem alt_sp_density_nonneg (G : GCDGraph) : 0 ≤ G.density :=
  div_nonneg (alt_sp_esum_nonneg G _) (mul_nonneg (alt_sp_wsum_nonneg G _) (alt_sp_wsum_nonneg G _))

theorem alt_sp_ratio_ge (d d' q q' c : ℝ) (h1 : c ≤ q' / q) (h2 : c ≤ d' / d * (q' / q)) :
    c ≤ min 1 (d' / d) * (q' / q) := by
  rcases le_total 1 (d' / d) with h | h
  · rw [min_eq_left h, one_mul]; exact h1
  · rw [min_eq_right h]; exact h2

theorem alt_sp_ratio_mono (d d1 d' q q1 q' : ℝ) (hd : 0 < d) (hq : 0 < q) (hdd1 : d ≤ d1)
    (hqq1 : q ≤ q1) (hd' : 0 ≤ d') (hq' : 0 ≤ q') :
    min 1 (d' / d1) * (q' / q1) ≤ min 1 (d' / d) * (q' / q) := by
  have h1 : d' / d1 ≤ d' / d := div_le_div_of_nonneg_left hd' hd hdd1
  have h2 : q' / q1 ≤ q' / q := div_le_div_of_nonneg_left hq' hq hqq1
  exact mul_le_mul (min_le_min_left _ h1) h2 (div_nonneg hq' (hq.trans_le hqq1).le)
    (le_min zero_le_one (div_nonneg hd' hd.le))

theorem alt_sp_ratio_chain (d0 d1 d2 q0 q1 q2 : ℝ) (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 ≤ d2)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hq2 : 0 ≤ q2) :
    (min 1 (d2 / d1) * (q2 / q1)) * (min 1 (d1 / d0) * (q1 / q0)) ≤
      min 1 (d2 / d0) * (q2 / q0) := by
  have ha : 0 ≤ d2 / d1 := div_nonneg hd2 hd1.le
  have hb : 0 ≤ d1 / d0 := div_nonneg hd1.le hd0.le
  have hmin : min 1 (d2 / d1) * min 1 (d1 / d0) ≤ min 1 (d2 / d0) := by
    have e : d2 / d0 = (d2 / d1) * (d1 / d0) := by field_simp
    rw [e]
    apply le_min
    · calc min 1 (d2 / d1) * min 1 (d1 / d0) ≤ 1 * 1 :=
            mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min zero_le_one hb) zero_le_one
        _ = 1 := one_mul 1
    · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min zero_le_one hb) ha
  have e2 : q2 / q0 = (q2 / q1) * (q1 / q0) := by field_simp
  rw [e2]
  calc (min 1 (d2 / d1) * (q2 / q1)) * (min 1 (d1 / d0) * (q1 / q0)) =
      (min 1 (d2 / d1) * min 1 (d1 / d0)) * ((q2 / q1) * (q1 / q0)) := by ring
    _ ≤ min 1 (d2 / d0) * ((q2 / q1) * (q1 / q0)) :=
        mul_le_mul_of_nonneg_right hmin (by positivity)

theorem alt_sp_esum_le_prod (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (h : E' ⊆ V' ×ˢ W') : esum G.μ E' ≤ wsum G.μ V' * wsum G.μ W' := by
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg h (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))

/-- `μ(E ∩ (S × W)) = ∑_{v ∈ S} μ(v) μ(Γ(v))`. -/
theorem alt_sp_esum_nbhd (G : GCDGraph) (S : Finset ℕ) (hS : S ⊆ G.V) :
    esum G.μ (G.E.filter (fun e => e.1 ∈ S)) = ∑ v ∈ S, G.μ v * wsum G.μ (G.nbhdV v) := by
  unfold esum wsum nbhdV
  have h1 : ∀ v ∈ S, G.μ v * ∑ w ∈ G.W.filter (fun w => (v, w) ∈ G.E), G.μ w =
      ∑ w ∈ G.W, if (v, w) ∈ G.E then G.μ v * G.μ w else 0 := by
    intro v _
    rw [mul_sum, sum_filter]
  rw [sum_congr rfl h1, ← sum_product' (f := fun v w => if (v, w) ∈ G.E then G.μ v * G.μ w else 0)]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨he, hs⟩
    exact ⟨⟨hs, (mem_product.1 (G.E_sub he)).2⟩, he⟩
  · rintro ⟨⟨hs, _⟩, he⟩
    exact ⟨he, hs⟩

/-! ### Lemma 13.1 -/

/-- Lemma 13.1. -/
theorem lemma131 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (∃ k l : ℕ, 0 < (G.restrictPrime p k l hp hpP).density ∧
        1 / (10 : ℝ) ^ (40 : ℕ) ≤
          min 1 ((G.restrictPrime p k l hp hpP).density / G.density) *
            ((G.restrictPrime p k l hp hpP).quality / G.quality)) ∨
      ∃ k : ℕ, 9 / 10 * wsum G.μ G.V ≤ wsum G.μ (vslice G.V p k) ∧
        9 / 10 * wsum G.μ G.W ≤ wsum G.μ (vslice G.W p k) := by
  obtain ⟨hE, hV, hW⟩ := alt_sp_pos G hδ
  obtain ⟨k, l, hVk, hWl, hB⟩ := alt_sp_lemma121 G hδ p
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hq' := quality_restrictPrime G p k l hp hpP hE hVk hWl
  set G' := G.restrictPrime p k l hp hpP with hG'
  set E' := esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    with hE'
  set Vk := wsum G.μ (vslice G.V p k) with hVkdef
  set Wl := wsum G.μ (vslice G.W p l) with hWldef
  set V := wsum G.μ G.V with hVdef
  set W := wsum G.μ G.W with hWdef
  set E := esum G.μ G.E with hEdef
  set F := (p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) with hFdef
  have hF : (p : ℝ) ^ ((k - l) + (l - k)) ≤ F := by
    apply alt_sp_F_ge p hp
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
  have hα0 : 0 < Vk / V := div_pos hVk hV
  have hβ0 : 0 < Wl / W := div_pos hWl hW
  have hα1 : Vk / V ≤ 1 := (div_le_one hV).2 (alt_sp_vslice_le G _ _ _)
  have hβ1 : Wl / W ≤ 1 := (div_le_one hW).2 (alt_sp_vslice_le G _ _ _)
  by_cases hkl : k = l
  · -- Case 1
    subst hkl
    left
    refine ⟨k, k, ?_, ?_⟩
    · have hx : (Vk / V * (Wl / W)) ^ ((9 : ℝ) / 10) ≤ E' / E := by
        rw [le_div_iff₀ hE]; simpa [alt_sp_B] using hB
      have : 0 < E' := by
        have := mul_pos (Real.rpow_pos_of_pos (mul_pos hα0 hβ0) ((9 : ℝ) / 10)) hE
        have h2 := (le_div_iff₀ hE).1 hx
        linarith
      show 0 < E' / (Vk * Wl)
      positivity
    · rw [hdens, hqual]
      refine le_trans (by norm_num) (alt_sp_diag _ _ _ _ hα0 hβ0 hα1 hβ1 ?_ ?_)
      · rw [le_div_iff₀ hE]; simpa [alt_sp_B] using hB
      · simpa using hF
  · -- Case 2
    set ak := Vk / V
    set bl := Wl / W
    set bk := wsum G.μ (vslice G.W p k) / W with hbk
    set al := wsum G.μ (vslice G.V p l) / V with hal
    have hbk0 : 0 ≤ bk := div_nonneg (alt_sp_wsum_nonneg G _) hW.le
    have hal0 : 0 ≤ al := div_nonneg (alt_sp_wsum_nonneg G _) hV.le
    have hbk1 : bk ≤ 1 := (div_le_one hW).2 (alt_sp_vslice_le G _ _ _)
    have hal1 : al ≤ 1 := (div_le_one hV).2 (alt_sp_vslice_le G _ _ _)
    have hbsum : bk + bl ≤ 1 := by
      rw [hbk, ← add_div, div_le_one hW]; exact alt_sp_two_slices G _ p k l hkl
    set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hS
    have hSy : ak * bl ≤ S := by
      have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
      have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
      have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hβ0.le (by linarith)
      have : ak * bl ≤ ak * (1 - bk) := mul_le_mul_of_nonneg_left (by linarith) hα0.le
      linarith
    have hj : 1 ≤ (k - l) + (l - k) := by omega
    have hx : S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 ≤ E' / E := by
      rw [le_div_iff₀ hE]; simpa [alt_sp_B, hkl] using hB
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hkey := alt_sp_key ak bl (E' / E) S F p ((k - l) + (l - k)) hα0 hβ0 hSy hx hj hP hF
    have hE'pos : 0 < E' := by
      have h1 : 0 < S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 := by
        have := lt_of_lt_of_le (mul_pos hα0 hβ0) hSy; positivity
      have := lt_of_lt_of_le h1 hx
      exact (div_pos_iff_of_pos_right hE).1 this
    have hdpos : 0 < G'.density := by
      show 0 < E' / (Vk * Wl)
      positivity
    by_cases hbig : 1 / (10 : ℝ) ^ (40 : ℕ) ≤
        min 1 (G'.density / G.density) * (G'.quality / G.quality)
    · left
      exact ⟨k, l, hdpos, hbig⟩
    · right
      push_neg at hbig
      rw [hdens, hqual] at hbig
      have hy0 : 0 < ak * bl := mul_pos hα0 hβ0
      have hQ : S ^ 2 / (ak * bl) ≤ 1 / 10 ^ 7 := by
        have h1 := lt_of_le_of_lt hkey hbig
        have h2 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 * 10 ^ 33)).1 h1
        have h3 : S ^ 2 / (ak * bl) * 2 ≤ S ^ 2 / (ak * bl) * p :=
          mul_le_mul_of_nonneg_left hP (by positivity)
        norm_num at h2 ⊢
        linarith
      have hSQ : S ≤ S ^ 2 / (ak * bl) := by
        rw [le_div_iff₀ hy0]
        have : 0 < S := lt_of_lt_of_le hy0 hSy
        calc S * (ak * bl) ≤ S * S := mul_le_mul_of_nonneg_left hSy this.le
          _ = S ^ 2 := (sq S).symm
      have hres := alt_sp_sharp_real ak bk al bl (1 / 10 ^ 7) hα0.le hbk0 hal0 hβ0.le
        hα1 hbk1 hal1 hβ1 hy0 (by linarith) (by linarith) (by norm_num)
      rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨k, ?_, ?_⟩
        · have : 9 / 10 ≤ ak := by linarith
          calc 9 / 10 * V ≤ ak * V := mul_le_mul_of_nonneg_right this hV.le
            _ = Vk := div_mul_cancel₀ _ hV.ne'
        · have : 9 / 10 ≤ bk := by linarith
          calc 9 / 10 * W ≤ bk * W := mul_le_mul_of_nonneg_right this hW.le
            _ = wsum G.μ (vslice G.W p k) := div_mul_cancel₀ _ hW.ne'
      · refine ⟨l, ?_, ?_⟩
        · have : 9 / 10 ≤ al := by linarith
          calc 9 / 10 * V ≤ al * V := mul_le_mul_of_nonneg_right this hV.le
            _ = wsum G.μ (vslice G.V p l) := div_mul_cancel₀ _ hV.ne'
        · have : 9 / 10 ≤ bl := by linarith
          calc 9 / 10 * W ≤ bl * W := mul_le_mul_of_nonneg_right this hW.le
            _ = Wl := div_mul_cancel₀ _ hW.ne'

/-! ### Lemma 13.2 -/

theorem alt_sp_T0_lt (p : ℕ) (hp : p.Prime) : T0 < (p : ℝ) ^ (7000 : ℕ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold T0
  calc (10 : ℝ) ^ (2000 : ℕ) < 10 ^ (3 * 700) := pow_lt_pow_right₀ (by norm_num) (by norm_num)
    _ = (10 ^ 3) ^ 700 := pow_mul 10 3 700
    _ ≤ (2 ^ 10) ^ 700 := pow_le_pow_left₀ (by norm_num) (by norm_num) 700
    _ = 2 ^ (10 * 700) := (pow_mul 2 10 700).symm
    _ ≤ (p : ℝ) ^ (10 * 700) := pow_le_pow_left₀ (by norm_num) hp2 _

/-- Lemma 13.2 (adding a small prime to `P`). -/
theorem lemma132 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpT : (p : ℝ) ≤ T0) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.P = insert p G.P ∧
      G'.R ⊆ G.R.erase p ∧
      1 / (10 : ℝ) ^ (50 : ℕ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
  obtain ⟨G1, hG1, hP1, hf1, hg1, hδ1, hδδ1, hqq1, hHD⟩ := exists_highDegree_subgraph G hδ
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hq1 : 0 < G1.quality := (quality_pos_iff G1).2 hδ1
  have hpP1 : p ∉ G1.P := hP1 ▸ hpP
  have hμ1 : G1.μ = G.μ := hG1.1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  -- any `G1_{p^k,p^ℓ}` with a good ratio relative to `G1` finishes the proof
  have finish : ∀ k l, 0 < (G1.restrictPrime p k l hp hpP1).density →
      1 / (10 : ℝ) ^ (50 : ℕ) ≤
        min 1 ((G1.restrictPrime p k l hp hpP1).density / G1.density) *
          ((G1.restrictPrime p k l hp hpP1).quality / G1.quality) →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.P = insert p G.P ∧
        G'.R ⊆ G.R.erase p ∧
        1 / (10 : ℝ) ^ (50 : ℕ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
    intro k l hd hr
    refine ⟨G1.restrictPrime p k l hp hpP1, (restrictPrime_isSubgraph G1 p k l hp hpP1).trans hG1,
      hd, ?_, ?_, ?_⟩
    · show insert p G1.P = _
      rw [hP1]
    · exact (R_restrictPrime_subset G1 p k l hp hpP1).trans (erase_subset_erase p (R_mono hG1))
    · exact hr.trans (alt_sp_ratio_mono _ _ _ _ _ _ hδ hq hδδ1 hqq1 (alt_sp_density_nonneg _)
        ((quality_nonneg _)))
  rcases lemma131 G1 hδ1 p hp hpP1 with ⟨k, l, hd, hr⟩ | ⟨k, hVk9, hWk9⟩
  · refine finish k l hd (le_trans ?_ hr)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hE1, hV1, hW1⟩ := alt_sp_pos G1 hδ1
  -- (13.2): the sharp-type bound, unless we are already done
  have hsharp : (∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.P = insert p G.P ∧
        G'.R ⊆ G.R.erase p ∧
        1 / (10 : ℝ) ^ (50 : ℕ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality)) ∨
      (1 - K40 / p) * wsum G1.μ G1.W ≤ wsum G1.μ (vslice G1.W p k) := by
    by_cases hbig : (10 : ℝ) ^ (41 : ℕ) < p
    · have hK : K40 < p := by
        have : K40 < (10 : ℝ) ^ (41 : ℕ) := by
          simp only [K40]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
        linarith
      rcases lemma122 G1 hδ1 p hp hpP1 hK with ⟨k', l', hd, hr⟩ | ⟨k', hV', hW'⟩
      · left
        refine finish k' l' hd (le_trans ?_ hr)
        have : (1 : ℝ) ≤ 2 ^ (if k' ≠ l' then 1 else 0) := one_le_pow₀ (by norm_num)
        have h2 : 1 / (10 : ℝ) ^ (50 : ℕ) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        linarith
      · right
        have h9 : 9 / 10 ≤ 1 - K40 / p := by
          have : K40 / p ≤ 1 / 10 := by
            rw [div_le_iff₀ (by positivity)]
            simp only [K40] at hbig ⊢
            have : (10 : ℝ) ^ (41 : ℕ) = 10 * 10 ^ (40 : ℕ) := by ring
            linarith
          linarith
        have hkk : k' = k := by
          by_contra hne
          have h2 := alt_sp_two_slices G1 G1.V p k k' (Ne.symm hne)
          have h3 : 9 / 10 * wsum G1.μ G1.V ≤ wsum G1.μ (vslice G1.V p k') :=
            le_trans (mul_le_mul_of_nonneg_right h9 hV1.le) hV'
          linarith
        subst hkk
        exact hW'
    · right
      push_neg at hbig
      have h9 : 1 - K40 / p ≤ 9 / 10 := by
        have : 1 / 10 ≤ K40 / p := by
          rw [le_div_iff₀ (by positivity)]
          simp only [K40] at hbig ⊢
          have : (10 : ℝ) ^ (41 : ℕ) = 10 * 10 ^ (40 : ℕ) := by ring
          linarith
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right h9 hW1.le) hWk9
  rcases hsharp with hdone | hWk
  · exact hdone
  -- Lemma 11.3 with `r = 7000`
  rcases lemma113 G1 hδ1 p hp hpP1 7000 k (by norm_num) (alt_sp_T0_lt p hp) hWk with
    ⟨l, _, h2q, h2dq⟩ | hsmall
  · apply finish k l
    · by_contra hd
      have hd0 : (G1.restrictPrime p k l hp hpP1).density = 0 :=
        le_antisymm (not_lt.1 hd) (alt_sp_density_nonneg _)
      rw [hd0, zero_mul] at h2dq
      have : 0 < 2 * G1.density * G1.quality := by positivity
      linarith
    · refine le_trans ?_ (alt_sp_ratio_ge _ _ _ _ 2 ?_ ?_)
      · rw [div_le_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ 10 ^ (50 : ℕ) := one_le_pow₀ (by norm_num)
        linarith
      · rw [le_div_iff₀ hq1]; linarith
      · rw [div_mul_div_comm, le_div_iff₀ (by positivity)]; linarith
  -- the graph `G2`
  set r : ℕ := 7000 with hr
  set V2 := vslice G1.V p k with hV2
  set W2 := G1.W.filter (fun w => (k - w.factorization p) + (w.factorization p - k) ≤ r) with hW2
  set E2 := G1.E.filter (fun e => e.1.factorization p = k ∧
    (k - e.2.factorization p) + (e.2.factorization p - k) ≤ r) with hE2
  have hE2sub : E2 ⊆ V2 ×ˢ W2 := by
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  set G2 := G1.induce V2 W2 E2 (filter_subset _ _) (filter_subset _ _) (filter_subset _ _) hE2sub
    with hG2
  -- `μ(E2) ≥ μ(E1)/2`
  set E1 := esum G1.μ G1.E with hE1def
  set V1 := wsum G1.μ G1.V with hV1def
  set W1 := wsum G1.μ G1.W with hW1def
  have hδ1eq : G1.density = E1 / (V1 * W1) := rfl
  have hEk : 81 / 100 * E1 ≤ esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k)) := by
    have hset : G1.E.filter (fun e => e.1.factorization p = k) =
        G1.E.filter (fun e => e.1 ∈ V2) := by
      apply filter_congr
      intro e he
      have hv := (mem_product.1 (G1.E_sub he)).1
      simp only [hV2, vslice, mem_filter]
      exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
    rw [hset, alt_sp_esum_nbhd G1 V2 (filter_subset _ _)]
    have hpt : ∀ v ∈ V2, G1.μ v * (9 * G1.density / 10 * W1) ≤ G1.μ v * wsum G1.μ (G1.nbhdV v) :=
      fun v hv => mul_le_mul_of_nonneg_left (hHD.1 v (mem_filter.1 hv).1) (G1.μ_nonneg v)
    refine le_trans ?_ (sum_le_sum hpt)
    rw [← sum_mul]
    have hsum : ∑ v ∈ V2, G1.μ v = wsum G1.μ V2 := rfl
    rw [hsum, hδ1eq]
    have hE1eq : E1 = E1 / (V1 * W1) * V1 * W1 := by field_simp
    have hVW : 0 ≤ E1 / (V1 * W1) * W1 := by positivity
    calc 81 / 100 * E1 = 9 / 10 * (9 * (E1 / (V1 * W1)) / 10 * W1) * V1 := by
          conv_lhs => rw [hE1eq]
          ring
      _ ≤ 9 / 10 * (9 * (E1 / (V1 * W1)) / 10 * W1) * (10 / 9 * wsum G1.μ V2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = wsum G1.μ V2 * (9 * (E1 / (V1 * W1)) / 10 * W1) := by ring
  have hbad : esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧
      r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤ E1 / 4 := by
    refine le_trans hsmall ?_
    apply div_le_div_of_nonneg_left (alt_sp_esum_nonneg G1 _) (by norm_num)
    have : (1 : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  have hsplit : esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k)) =
      esum G1.μ E2 + esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧
        r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) := by
    unfold esum
    rw [← sum_filter_add_sum_filter_not (G1.E.filter (fun e => e.1.factorization p = k))
      (fun e => (k - e.2.factorization p) + (e.2.factorization p - k) ≤ r)]
    congr 1
    · rw [filter_filter]
    · rw [filter_filter]
      apply sum_congr _ (fun _ _ => rfl)
      apply filter_congr
      intro e _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hE2 : E1 / 2 ≤ esum G1.μ E2 := by linarith
  have hE2pos : 0 < esum G1.μ E2 := by linarith
  have hVW2 := alt_sp_esum_le_prod G1 V2 W2 E2 hE2sub
  have hV2pos : 0 < wsum G1.μ V2 := by
    have : 0 < 9 / 10 * V1 := by positivity
    linarith
  have hW2pos : 0 < wsum G1.μ W2 := by
    by_contra h
    have h0 := le_antisymm (not_lt.1 h) (alt_sp_wsum_nonneg G1 W2)
    rw [h0, mul_zero] at hVW2
    linarith
  have hV2le : wsum G1.μ V2 ≤ V1 := alt_sp_vslice_le G1 _ _ _
  have hW2le : wsum G1.μ W2 ≤ W1 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G1.μ_nonneg i)
  have hδ2eq : G2.density = esum G1.μ E2 / (wsum G1.μ V2 * wsum G1.μ W2) := rfl
  have hδ2pos : 0 < G2.density := by rw [hδ2eq]; positivity
  have hδ2 : G1.density / 2 ≤ G2.density := by
    rw [hδ2eq, hδ1eq, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : wsum G1.μ V2 * wsum G1.μ W2 ≤ V1 * W1 :=
      mul_le_mul hV2le hW2le (alt_sp_wsum_nonneg G1 _) hV1.le
    calc E1 * (wsum G1.μ V2 * wsum G1.μ W2) ≤ (2 * esum G1.μ E2) * (V1 * W1) :=
          mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = esum G1.μ E2 * (V1 * W1 * 2) := by ring
  -- the product of local factors is unchanged
  set Pi1 := ∏ q ∈ G1.P, G1.qualityFactor q with hPi1
  have hq1eq : G1.quality = E1 ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 := quality_eq G1
  have hPi1pos : 0 < Pi1 := by
    have h := hq1
    rw [hq1eq] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hq2eq : G2.quality =
      esum G1.μ E2 ^ 10 / (wsum G1.μ V2 ^ 9 * wsum G1.μ W2 ^ 9) * Pi1 := quality_eq G2
  have hq2 : G1.quality / 2 ^ 10 ≤ G2.quality := by
    rw [hq1eq, hq2eq]
    have h1 : (E1 / 2) ^ 10 ≤ esum G1.μ E2 ^ 10 := pow_le_pow_left₀ (by positivity) hE2 10
    have h2 : wsum G1.μ V2 ^ 9 * wsum G1.μ W2 ^ 9 ≤ V1 ^ 9 * W1 ^ 9 :=
      mul_le_mul (pow_le_pow_left₀ hV2pos.le hV2le 9) (pow_le_pow_left₀ hW2pos.le hW2le 9)
        (by positivity) (by positivity)
    have h3 : E1 ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 / 2 ^ 10 = (E1 / 2) ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 := by
      ring
    rw [h3]
    apply mul_le_mul_of_nonneg_right _ hPi1pos.le
    exact div_le_div₀ (by positivity) h1 (by positivity) h2
  -- Lemma 11.2 on `G2`
  obtain ⟨i, hi, j, hj, G3, hG3, hV3, hW3, hE3, hP3, hf3, hg3, hδ3, hδ3b, hq3b⟩ :=
    exists_block_subgraph G2 hδ2pos {0} (Icc (k - r) (k + r)) (fun _ => 0)
      (fun w => w.factorization p) (fun _ _ => mem_singleton_self 0)
      (by
        intro w hw
        have := (mem_filter.1 hw).2
        rw [mem_Icc]; omega)
  have hi0 : i = 0 := mem_singleton.1 hi
  subst hi0
  have hjk : (k - j) + (j - k) ≤ r := by rw [mem_Icc] at hj; omega
  have hcardJ : ((Icc (k - r) (k + r)).card : ℝ) ≤ 14001 := by
    rw [Nat.card_Icc]
    have : k + r + 1 - (k - r) ≤ 14001 := by omega
    exact_mod_cast this
  have hcard1 : (({0} : Finset ℕ).card : ℝ) = 1 := by simp
  rw [hcard1, one_mul] at hδ3b hq3b
  set J := ((Icc (k - r) (k + r)).card : ℝ) with hJ
  have hJpos : 0 < J := by
    rw [hJ]; exact_mod_cast card_pos.2 ⟨k, by rw [mem_Icc]; omega⟩
  clear_value J
  -- identify `G3` with `G1_{p^k,p^j}`
  set G' := G1.restrictPrime p k j hp hpP1 with hG'
  have hμ3 : G3.μ = G1.μ := hG3.1
  have hV3' : G3.V = vslice G1.V p k := by
    rw [hV3]; ext v
    rw [mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have hW3' : G3.W = vslice G1.W p j := by
    rw [hW3]; ext w
    constructor
    · intro hw
      obtain ⟨hw2, h3⟩ := mem_filter.1 hw
      obtain ⟨hw1, -⟩ := mem_filter.1 (show w ∈ W2 from hw2)
      exact mem_filter.2 ⟨hw1, h3⟩
    · intro hw
      obtain ⟨hw1, h3⟩ := mem_filter.1 hw
      refine mem_filter.2 ⟨show w ∈ W2 from mem_filter.2 ⟨hw1, ?_⟩, h3⟩
      rw [h3]; exact hjk
  have hE3' : G3.E = G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = j) := by
    rw [hE3]; ext e
    constructor
    · intro he
      obtain ⟨he2, -, h4⟩ := mem_filter.1 he
      obtain ⟨he1, h1, -⟩ := mem_filter.1 (show e ∈ E2 from he2)
      exact mem_filter.2 ⟨he1, h1, h4⟩
    · intro he
      obtain ⟨he1, h1, h4⟩ := mem_filter.1 he
      refine mem_filter.2 ⟨show e ∈ E2 from mem_filter.2 ⟨he1, h1, ?_⟩, rfl, h4⟩
      rw [h4]; exact hjk
  have hδ'eq : G'.density = G3.density := by
    show esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = j)) /
      (wsum G1.μ (vslice G1.V p k) * wsum G1.μ (vslice G1.W p j)) = _
    unfold density
    rw [hμ3, hV3', hW3', hE3']
  obtain ⟨hE3pos, hV3pos, hW3pos⟩ := alt_sp_pos G3 hδ3
  rw [hμ3, hV3'] at hV3pos
  rw [hμ3, hW3'] at hW3pos
  rw [hμ3, hE3'] at hE3pos
  have hqG' := quality_restrictPrime G1 p k j hp hpP1 hE1 hV3pos hW3pos
  have hq3eq := quality_eq G3
  have hPi3 : ∏ q ∈ G3.P, G3.qualityFactor q = Pi1 := by
    rw [hP3]
    apply prod_congr rfl
    intro q _
    unfold qualityFactor fgDist
    rw [hf3, hg3]
    rfl
  rw [hPi3, hμ3, hV3', hW3', hE3'] at hq3eq
  set F := (p : ℝ) ^ ((k - j) + (j - k)) /
          ((1 - (if k = j ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) with hFdef
  have hF : 1 ≤ F := by
    have := alt_sp_F_ge p hp ((k - j) + (j - k))
      (if k = j ∧ 1 ≤ k then 1 / (p : ℝ) else 0) (by split_ifs <;> positivity)
      (by
        split_ifs
        · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        · norm_num)
    exact le_trans (one_le_pow₀ (by linarith)) this
  have hq'eq : G'.quality = G3.quality * F := by
    rw [hqG', hq3eq, hq1eq]
    show E1 ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 *
        (esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = j)) /
          E1) ^ 10 * (V1 / wsum G1.μ (vslice G1.V p k)) ^ 9 *
        (W1 / wsum G1.μ (vslice G1.W p j)) ^ 9 * F = _
    field_simp
  have hq3pos : 0 < G3.quality := (quality_pos_iff G3).2 hδ3
  have hq' : G3.quality ≤ G'.quality := by
    rw [hq'eq]; exact le_mul_of_one_le_right hq3pos.le hF
  have hδ'pos : 0 < G'.density := by rw [hδ'eq]; exact hδ3
  apply finish k j hδ'pos
  -- final numerics
  have hq'1 : G1.quality / (2 ^ 10 * J ^ 10) ≤ G'.quality := by
    calc G1.quality / (2 ^ 10 * J ^ 10) = G1.quality / 2 ^ 10 / J ^ 10 := by rw [div_div]
      _ ≤ G2.quality / J ^ 10 := div_le_div_of_nonneg_right hq2 (by positivity)
      _ ≤ G3.quality := hq3b
      _ ≤ G'.quality := hq'
  have hδ'1 : G1.density / (2 * J) ≤ G'.density := by
    rw [hδ'eq]
    calc G1.density / (2 * J) = G1.density / 2 / J := by rw [div_div]
      _ ≤ G2.density / J := div_le_div_of_nonneg_right hδ2 hJpos.le
      _ ≤ G3.density := hδ3b
  have hJ10 : 2 ^ 10 * J ^ 10 ≤ (10 : ℝ) ^ (50 : ℕ) := by
    have : J ^ 10 ≤ 14001 ^ 10 := pow_le_pow_left₀ hJpos.le hcardJ 10
    calc 2 ^ 10 * J ^ 10 ≤ 2 ^ 10 * 14001 ^ 10 := by gcongr
      _ ≤ (10 : ℝ) ^ (50 : ℕ) := by norm_num
  have hJ11 : 2 * J * (2 ^ 10 * J ^ 10) ≤ (10 : ℝ) ^ (50 : ℕ) := by
    have : J ^ 11 ≤ 14001 ^ 11 := pow_le_pow_left₀ hJpos.le hcardJ 11
    calc 2 * J * (2 ^ 10 * J ^ 10) = 2 ^ 11 * J ^ 11 := by ring
      _ ≤ 2 ^ 11 * 14001 ^ 11 := by gcongr
      _ ≤ (10 : ℝ) ^ (50 : ℕ) := by norm_num
  apply alt_sp_ratio_ge
  · rw [le_div_iff₀ hq1]
    calc 1 / (10 : ℝ) ^ (50 : ℕ) * G1.quality ≤ G1.quality / (2 ^ 10 * J ^ 10) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hq1.le (by positivity) hJ10
      _ ≤ G'.quality := hq'1
  · rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    calc 1 / (10 : ℝ) ^ (50 : ℕ) * (G1.density * G1.quality) ≤
        G1.density * G1.quality / (2 * J * (2 ^ 10 * J ^ 10)) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hJ11
      _ = G1.density / (2 * J) * (G1.quality / (2 ^ 10 * J ^ 10)) := by
          rw [div_mul_div_comm]
      _ ≤ G'.density * G'.quality :=
          mul_le_mul hδ'1 hq'1 (by positivity) (le_of_lt hδ'pos)

/-! ### Proposition 8.3 -/

theorem alt_sp_iter (G : GCDGraph) (n : ℕ) :
    ∀ H : GCDGraph, H.IsSubgraph G → 0 < H.density → (∀ p ∈ H.P, (p : ℝ) ≤ T0) →
      (H.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).card ≤ n →
      ∃ G' : GCDGraph, G'.IsSubgraph H ∧ 0 < G'.density ∧ (∀ p ∈ G'.P, (p : ℝ) ≤ T0) ∧
        (∀ p ∈ G'.R, T0 < (p : ℝ)) ∧
        (1 / (10 : ℝ) ^ (50 : ℕ)) ^ n ≤
          min 1 (G'.density / H.density) * (G'.quality / H.quality) := by
  induction n with
  | zero =>
    intro H _ hδ hP hc
    have hq : 0 < H.quality := (quality_pos_iff H).2 hδ
    refine ⟨H, IsSubgraph.refl H, hδ, hP, ?_, ?_⟩
    · intro p hp
      by_contra h
      push_neg at h
      have : p ∈ H.R.filter (fun p : ℕ => (p : ℝ) ≤ T0) := mem_filter.2 ⟨hp, h⟩
      rw [card_eq_zero.1 (Nat.le_zero.1 hc)] at this
      exact absurd this (notMem_empty p)
    · rw [div_self hδ.ne', div_self hq.ne']; simp
  | succ n ih =>
    intro H hHG hδ hP hc
    have hq : 0 < H.quality := (quality_pos_iff H).2 hδ
    by_cases hex : ∃ p ∈ H.R, (p : ℝ) ≤ T0
    · obtain ⟨p, hpR, hpT⟩ := hex
      obtain ⟨H', hH', hδ', hP', hR', hrat⟩ :=
        lemma132 H hδ p (H.prime_of_mem_R hpR) (H.not_mem_P_of_mem_R hpR) hpT
      have hc' : (H'.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).card ≤ n := by
        have hsub : H'.R.filter (fun p : ℕ => (p : ℝ) ≤ T0) ⊆
            (H.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).erase p := by
          intro q hq
          obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
          have := hR' hq1
          rw [mem_erase] at this ⊢
          exact ⟨this.1, mem_filter.2 ⟨this.2, hq2⟩⟩
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_filter.2 ⟨hpR, hpT⟩)] at this
        omega
      have hP'' : ∀ q ∈ H'.P, (q : ℝ) ≤ T0 := by
        intro q hq
        rw [hP'] at hq
        rcases mem_insert.1 hq with rfl | hq
        · exact hpT
        · exact hP q hq
      obtain ⟨G', hG', hδG', hPG', hRG', hratG'⟩ := ih H' (hH'.trans hHG) hδ' hP'' hc'
      have hq' : 0 < H'.quality := (quality_pos_iff H').2 hδ'
      refine ⟨G', hG'.trans hH', hδG', hPG', hRG', ?_⟩
      refine le_trans ?_ (alt_sp_ratio_chain _ _ _ _ _ _ hδ hδ' (alt_sp_density_nonneg _) hq hq'
        (quality_nonneg _))
      rw [pow_succ]
      exact mul_le_mul hratG' hrat (by positivity)
        (le_trans (by positivity) hratG')
    · push_neg at hex
      refine ⟨H, IsSubgraph.refl H, hδ, hP, hex, ?_⟩
      rw [div_self hδ.ne', div_self hq.ne']
      simp only [min_self, mul_one]
      apply pow_le_one₀ (by positivity)
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)

/-- Proposition 8.3 (bounded quality loss for small primes). -/
theorem prop83 (G : GCDGraph) (hP : G.P = ∅) (hδ : 0 < G.density) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ (∀ p ∈ G'.P, (p : ℝ) ≤ T0) ∧
      (∀ p ∈ G'.R, T0 < (p : ℝ)) ∧
      1 / (10 : ℝ) ^ ((10 : ℕ) ^ 3000) ≤
        min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
  set N := (G.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).card with hN
  obtain ⟨G', hG', hδ', hP', hR', hrat⟩ :=
    alt_sp_iter G N G (IsSubgraph.refl G) hδ (by rw [hP]; simp) le_rfl
  refine ⟨G', hG', hδ', hP', hR', le_trans ?_ hrat⟩
  -- `N ≤ 10^2000 + 1`
  have hNle : N ≤ 10 ^ 2000 + 1 := by
    have hsub : G.R.filter (fun p : ℕ => (p : ℝ) ≤ T0) ⊆ range (10 ^ 2000 + 1) := by
      intro q hq
      have h := (mem_filter.1 hq).2
      rw [mem_range, Nat.lt_succ_iff]
      have : (q : ℝ) ≤ ((10 ^ 2000 : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; exact h
      exact_mod_cast this
    have := card_le_card hsub
    rwa [card_range] at this
  have hexp : 50 * N ≤ 10 ^ 3000 := by
    have h1 : (10 : ℕ) ^ 3000 = 10 ^ 1000 * 10 ^ 2000 := by rw [← pow_add]
    have h2 : 100 ≤ (10 : ℕ) ^ 1000 := by
      calc 100 = (10 : ℕ) ^ 2 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h3 : 1 ≤ (10 : ℕ) ^ 2000 := Nat.one_le_pow _ _ (by norm_num)
    rw [h1]
    have hN' := hNle
    generalize (10 : ℕ) ^ 1000 = Y at h2 ⊢
    generalize (10 : ℕ) ^ 2000 = X at h3 hN' ⊢
    calc 50 * N ≤ 50 * (X + 1) := Nat.mul_le_mul_left 50 hN'
      _ ≤ 100 * X := by omega
      _ ≤ Y * X := Nat.mul_le_mul_right X h2
  rw [one_div_pow, ← pow_mul]
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  exact pow_le_pow_right₀ (by norm_num) hexp

end GCDGraph

end DuffinSchaeffer
