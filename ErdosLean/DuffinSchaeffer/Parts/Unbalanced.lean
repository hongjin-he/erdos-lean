import ErdosLean.DuffinSchaeffer.Parts.GraphBasics

/-!
# Duffin–Schaeffer — Part 12: few edges between unbalanced sets (KM Lemmas 11.3, 11.4)


Proof strategy (following KM): if the edges towards far-away slices are too many, then by a
weighted pigeonhole (weights `2^{-|k-ℓ|/20}/100`, whose total is `≤ 1`) there is a single
slice `ℓ` with `μ(E_{p^k,p^ℓ}) > 2^{-|k-ℓ|/20} μ(E) / (400 p^{31/30})`, and then Lemma 11.1
together with an explicit (logarithmic) numerical estimate shows the quality doubles.
-/

open Finset

namespace DuffinSchaeffer

namespace GCDGraph

namespace Unbalanced

/-- A finite partial sum of a geometric series. -/
lemma sum_pow_le_tsum {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (T : Finset ℕ) :
    ∑ i ∈ T, y ^ i ≤ (1 - y)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hy0 hy1]
  exact (summable_geometric_of_lt_one hy0 hy1).sum_le_tsum T (fun i _ => pow_nonneg hy0 i)

/-- `∑_{ℓ ∈ S} y^{|ℓ - k|} ≤ 2/(1-y)`. -/
lemma sum_pow_dist_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (S : Finset ℕ) (k : ℕ) :
    ∑ l ∈ S, y ^ ((k - l) + (l - k)) ≤ 2 * (1 - y)⁻¹ := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun l => k ≤ l)]
  have h1 : ∑ l ∈ S.filter (fun l => k ≤ l), y ^ ((k - l) + (l - k)) ≤ (1 - y)⁻¹ := by
    have : ∑ l ∈ S.filter (fun l => k ≤ l), y ^ ((k - l) + (l - k)) =
        ∑ i ∈ (S.filter (fun l => k ≤ l)).image (fun l => l - k), y ^ i := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro l hl
        have : k ≤ l := (Finset.mem_filter.1 hl).2
        rw [Nat.sub_eq_zero_of_le this, zero_add]
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        simp only at hab
        omega
    rw [this]
    exact sum_pow_le_tsum hy0 hy1 _
  have h2 : ∑ l ∈ S.filter (fun l => ¬ k ≤ l), y ^ ((k - l) + (l - k)) ≤ (1 - y)⁻¹ := by
    have : ∑ l ∈ S.filter (fun l => ¬ k ≤ l), y ^ ((k - l) + (l - k)) =
        ∑ i ∈ (S.filter (fun l => ¬ k ≤ l)).image (fun l => k - l), y ^ i := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro l hl
        have : ¬ k ≤ l := (Finset.mem_filter.1 hl).2
        rw [Nat.sub_eq_zero_of_le (show l ≤ k by omega), add_zero]
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        simp only at hab
        omega
    rw [this]
    exact sum_pow_le_tsum hy0 hy1 _
  linarith

/-- Positive edge measure forces positive vertex measures. -/
lemma wsum_pos_of_esum_pos {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) {V W : Finset ℕ}
    {E : Finset (ℕ × ℕ)} (hE : E ⊆ V ×ˢ W) (h : 0 < esum μ E) :
    0 < wsum μ V ∧ 0 < wsum μ W := by
  have hV0 : 0 ≤ wsum μ V := Finset.sum_nonneg (fun v _ => hμ v)
  have hW0 : 0 ≤ wsum μ W := Finset.sum_nonneg (fun v _ => hμ v)
  refine ⟨lt_of_le_of_ne hV0 ?_, lt_of_le_of_ne hW0 ?_⟩
  · intro h0
    unfold wsum at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hμ v)).1 h0.symm
    have : esum μ E = 0 := Finset.sum_eq_zero (fun e he => by
      rw [hz e.1 (Finset.mem_product.1 (hE he)).1, zero_mul])
    linarith
  · intro h0
    unfold wsum at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hμ v)).1 h0.symm
    have : esum μ E = 0 := Finset.sum_eq_zero (fun e he => by
      rw [hz e.2 (Finset.mem_product.1 (hE he)).2, mul_zero])
    linarith

/-- Two distinct slices are disjoint parts of the whole set. -/
lemma wsum_slice_add_le {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (W : Finset ℕ) (p k l : ℕ)
    (hkl : k ≠ l) : wsum μ (vslice W p k) + wsum μ (vslice W p l) ≤ wsum μ W := by
  unfold wsum vslice
  rw [← Finset.sum_union]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      rcases Finset.mem_union.1 hv with h | h <;> exact (Finset.mem_filter.1 h).1
    · intro i _ _
      exact hμ i
  · rw [Finset.disjoint_left]
    intro v h1 h2
    exact hkl ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)

/-- From a `(1 - 10^40/p)`-proportion slice, any other slice is `≤ 10^40/p` of the whole. -/
lemma small_other_slice {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (W : Finset ℕ) (p k l : ℕ)
    (hp : 0 < (p : ℝ)) (hkl : k ≠ l)
    (hW : (1 - K40 / p) * wsum μ W ≤ wsum μ (vslice W p k)) :
    (p : ℝ) * wsum μ (vslice W p l) ≤ K40 * wsum μ W := by
  have hsum := wsum_slice_add_le hμ W p k l hkl
  have h1 := mul_le_mul_of_nonneg_left hW hp.le
  have h2 := mul_le_mul_of_nonneg_left hsum hp.le
  have h3 : (p : ℝ) * ((1 - K40 / p) * wsum μ W) = p * wsum μ W - K40 * wsum μ W := by
    field_simp
  linarith

lemma log_ten_ge : Real.log 2 ≤ Real.log 10 :=
  Real.log_le_log (by norm_num) (by norm_num)

/-- The numerical heart of Lemma 11.3 (in logarithmic form). -/
lemma core_ineq (p : ℝ) (hp : 2 ≤ p) (r d : ℕ) (hr : 1 ≤ r) (hd : r + 1 ≤ d)
    (hpr : T0 < p ^ r) (X M den : ℝ)
    (hX : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * p ^ ((31 : ℝ) / 30)) < X)
    (hM : p / K40 ≤ M) (hden0 : 0 < den) (hden1 : den ≤ 1) :
    2 < X ^ 10 * M ^ 9 * (p ^ d / den) ∧ 2 < X ^ 11 * M ^ 10 * (p ^ d / den) := by
  have hp0 : 0 < p := by linarith
  have hK : (0 : ℝ) < K40 := by unfold K40; positivity
  have hy : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 20) := by positivity
  have hP : (0 : ℝ) < p ^ ((31 : ℝ) / 30) := by positivity
  have hc : 0 < 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * p ^ ((31 : ℝ) / 30)) := by
    positivity
  have hX0 : 0 < X := lt_trans hc hX
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  set L := Real.log p with hL
  set l2 := Real.log 2 with hl2
  set l10 := Real.log 10 with hl10
  have hl2pos : 0 < l2 := Real.log_pos (by norm_num)
  have hl210 : l2 ≤ l10 := log_ten_ge
  have hLl2 : l2 ≤ L := Real.log_le_log (by norm_num) hp
  -- log X
  have hlogc : Real.log (1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * p ^ ((31 : ℝ) / 30)))
      = -(2 * l10) + d * (-(1 : ℝ) / 20 * l2) - (2 * l2 + (31 : ℝ) / 30 * L) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_rpow (by norm_num), Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hp0]
    have e1 : Real.log (1 / 100 : ℝ) = -(2 * l10) := by
      rw [one_div, Real.log_inv, show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have e2 : Real.log (4 : ℝ) = 2 * l2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e1, e2]
  have hlogX : -(2 * l10) + d * (-(1 : ℝ) / 20 * l2) - (2 * l2 + (31 : ℝ) / 30 * L) <
      Real.log X := by
    rw [← hlogc]; exact Real.log_lt_log hc hX
  -- log M
  have hlogM : L - 40 * l10 ≤ Real.log M := by
    have := Real.log_le_log (by positivity) hM
    rw [Real.log_div hp0.ne' hK.ne'] at this
    have e : Real.log K40 = 40 * l10 := by
      unfold K40; rw [Real.log_pow]; push_cast; ring
    linarith
  -- log p^r
  have hrL : 2000 * l10 < r * L := by
    have := Real.log_lt_log (by unfold T0; positivity) hpr
    rw [Real.log_pow] at this
    have e : Real.log T0 = 2000 * l10 := by
      unfold T0; rw [Real.log_pow]; push_cast; ring
    linarith
  have hlogden : Real.log den ≤ 0 := Real.log_nonpos hden0.le hden1
  have hdR : (r : ℝ) + 1 ≤ d := by exact_mod_cast hd
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hZ1 : 0 < X ^ 10 * M ^ 9 * (p ^ d / den) := by positivity
  have hZ2 : 0 < X ^ 11 * M ^ 10 * (p ^ d / den) := by positivity
  have hlogZ : ∀ a b : ℕ, Real.log (X ^ a * M ^ b * (p ^ d / den)) =
      a * Real.log X + b * Real.log M + (d * L - Real.log den) := by
    intro a b
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) hden0.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  have hm1 : 0 ≤ ((d : ℝ) - (2 * r / 3 + 4 / 3)) * (L - l2 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hm2 : 0 ≤ (r : ℝ) * (L - l2) := mul_nonneg (by linarith) (by linarith)
  have hm3 : 0 ≤ ((d : ℝ) - (19 * r / 30 + 41 / 30)) * (L - 11 * l2 / 20) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · rw [← Real.log_lt_log_iff two_pos hZ1, hlogZ]
    push_cast
    nlinarith
  · rw [← Real.log_lt_log_iff two_pos hZ2, hlogZ]
    push_cast
    nlinarith

lemma y_le : ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ≤ 49 / 50 := by
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 20) := by positivity
  have h20 : ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ (20 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra h
  push Not at h
  have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (20 : ℕ) ≠ 0)
  rw [h20] at this
  norm_num at this

/-- Weighted pigeonhole over the fibres of a map `g : ℕ × ℕ → ℕ`. -/
lemma pigeonhole (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n) (F : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℕ)
    (c : ℕ) (Efib : ℕ → Finset (ℕ × ℕ)) (hfib : ∀ l, F.filter (fun e => g e = l) ⊆ Efib l)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : B < esum μ F) :
    ∃ l ∈ F.image g, 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ ((c - l) + (l - c)) * B <
      esum μ (Efib l) := by
  by_contra hcon
  push Not at hcon
  set y : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 20)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 49 / 50 := y_le
  set S := F.image g
  have hsum : esum μ F ≤ ∑ l ∈ S, esum μ (Efib l) := by
    unfold esum
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := S)
      (fun e he => Finset.mem_image_of_mem _ he)]
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum_of_subset_of_nonneg (hfib l)
    intro e _ _
    exact mul_nonneg (hμ _) (hμ _)
  have hs : ∑ l ∈ S, 1 / 100 * y ^ ((c - l) + (l - c)) ≤ 1 := by
    rw [← Finset.mul_sum]
    have h := sum_pow_dist_le hy0 (by linarith) S c
    have h1y : (1 - y)⁻¹ ≤ 50 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hnn : 0 ≤ ∑ l ∈ S, y ^ ((c - l) + (l - c)) :=
      Finset.sum_nonneg (fun l _ => pow_nonneg hy0 _)
    linarith
  have hw : ∑ l ∈ S, 1 / 100 * y ^ ((c - l) + (l - c)) * B ≤ B := by
    rw [← Finset.sum_mul]
    calc (∑ l ∈ S, 1 / 100 * y ^ ((c - l) + (l - c))) * B ≤ 1 * B :=
          mul_le_mul_of_nonneg_right hs hB0
      _ = B := one_mul B
  have := Finset.sum_le_sum hcon
  linarith

/-- The conclusion (a), once a heavy far-away block `G_{p^k,p^ℓ}` has been found. -/
lemma conclude (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (r k l : ℕ) (hr : 1 ≤ r) (hpr : T0 < (p : ℝ) ^ r) (hdist : r + 1 ≤ (k - l) + (l - k))
    (hX : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ ((k - l) + (l - k)) *
        (esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) <
      esum G.μ (G.restrictPrime p k l hp hpP).E)
    (hsmall : (p : ℝ) * wsum G.μ (vslice G.V p k) ≤ K40 * wsum G.μ G.V ∨
      (p : ℝ) * wsum G.μ (vslice G.W p l) ≤ K40 * wsum G.μ G.W) :
    2 * G.quality < (G.restrictPrime p k l hp hpP).quality ∧
      2 * G.density * G.quality <
        (G.restrictPrime p k l hp hpP).density * (G.restrictPrime p k l hp hpP).quality := by
  set H := G.restrictPrime p k l hp hpP with hH
  have hkl : k ≠ l := by omega
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hK : (0 : ℝ) < K40 := by unfold K40; positivity
  have hEpos : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hq : 0 < G.quality := (G.quality_pos_iff).2 hδ
  have hP1 : (1 : ℝ) < (p : ℝ) ^ ((31 : ℝ) / 30) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hPpos : (0 : ℝ) < (p : ℝ) ^ ((31 : ℝ) / 30) := by linarith
  have hy : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 20) := by positivity
  have hHE : 0 < esum G.μ H.E := by
    refine lt_of_le_of_lt ?_ hX
    positivity
  have hHV := wsum_pos_of_esum_pos G.μ_nonneg H.E_sub hHE
  have hVk : 0 < wsum G.μ (vslice G.V p k) := hHV.1
  have hWl : 0 < wsum G.μ (vslice G.W p l) := hHV.2
  have hVpos := wsum_V_pos_of_density_pos G hδ
  have hWpos := wsum_W_pos_of_density_pos G hδ
  have hquality := G.quality_restrictPrime p k l hp hpP hEpos hVk hWl
  rw [show (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0) = 0 by simp [hkl]] at hquality
  set X := esum G.μ H.E / esum G.μ G.E with hXdef
  set A := wsum G.μ G.V / wsum G.μ (vslice G.V p k) with hA
  set Bw := wsum G.μ G.W / wsum G.μ (vslice G.W p l) with hBw
  set den := (1 - (0 : ℝ)) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 with hden
  set d := (k - l) + (l - k) with hd
  have hden0 : 0 < den := by
    have : 0 < 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by
      rw [sub_pos, div_lt_one hPpos]; exact hP1
    positivity
  have hden1 : den ≤ 1 := by
    have h1 : 0 ≤ 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by
      rw [sub_nonneg, div_le_one hPpos]; exact hP1.le
    have h2 : 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 := by
      have : 0 ≤ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
      linarith
    rw [hden]
    simp only [sub_zero, one_pow, one_mul]
    exact pow_le_one₀ h1 h2
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hVk, one_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _; exact G.μ_nonneg i
  have hB1 : 1 ≤ Bw := by
    rw [hBw, le_div_iff₀ hWl, one_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _; exact G.μ_nonneg i
  have hM : (p : ℝ) / K40 ≤ A * Bw := by
    rcases hsmall with h | h
    · have hA' : (p : ℝ) / K40 ≤ A := by
        rw [hA, le_div_iff₀ hVk, div_mul_eq_mul_div, div_le_iff₀ hK]; linarith
      nlinarith
    · have hB' : (p : ℝ) / K40 ≤ Bw := by
        rw [hBw, le_div_iff₀ hWl, div_mul_eq_mul_div, div_le_iff₀ hK]; linarith
      nlinarith
  have hXc : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) < X := by
    rw [hXdef, lt_div_iff₀ hEpos]
    calc 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) *
          esum G.μ G.E
        = 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d *
          (esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) := by ring
      _ < esum G.μ H.E := hX
  obtain ⟨c1, c2⟩ := core_ineq (p : ℝ) hp2 r d hr hdist hpr X (A * Bw) den hXc hM hden0 hden1
  have hqH : H.quality = G.quality * (X ^ 10 * (A * Bw) ^ 9 * ((p : ℝ) ^ d / den)) := by
    rw [hquality]; ring
  have hδH : H.density = G.density * (X * (A * Bw)) := by
    have e1 : H.density = esum G.μ H.E /
        (wsum G.μ (vslice G.V p k) * wsum G.μ (vslice G.W p l)) := rfl
    have e2 : G.density = esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W) := rfl
    rw [e1, e2, hXdef, hA, hBw]
    field_simp
  constructor
  · rw [hqH]
    nlinarith
  · have : H.density * H.quality =
        (G.density * G.quality) * (X ^ 11 * (A * Bw) ^ 10 * ((p : ℝ) ^ d / den)) := by
      rw [hqH, hδH]; ring
    rw [this]
    have hδq : 0 < G.density * G.quality := mul_pos hδ hq
    nlinarith

end Unbalanced

open Unbalanced

/-- Lemma 11.3.  If `p^k` exactly divides a `(1 - 10^40/p)`-proportion of `W` and `p^r > 10^2000`,
then either some `ℓ` with `|ℓ - k| ≥ r + 1` gives a quality (and density·quality) doubling
`G_{p^k,p^ℓ}`, or the edges from `V_{p^k}` to `⋃_{|ℓ-k| ≥ r+1} W_{p^ℓ}` have measure
`≤ μ(E)/(4 p^{31/30})`. -/
theorem lemma113 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (r k : ℕ) (hr : 1 ≤ r) (hpr : T0 < (p : ℝ) ^ r)
    (hW : (1 - K40 / p) * wsum G.μ G.W ≤ wsum G.μ (vslice G.W p k)) :
    (∃ l : ℕ, r + 1 ≤ (k - l) + (l - k) ∧
        2 * G.quality < (G.restrictPrime p k l hp hpP).quality ∧
        2 * G.density * G.quality <
          (G.restrictPrime p k l hp hpP).density * (G.restrictPrime p k l hp hpP).quality) ∨
      esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧
          r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by
  by_cases hb : esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧
          r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))
  · exact Or.inr hb
  left
  push Not at hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hEpos : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hB0 : 0 ≤ esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by positivity
  obtain ⟨l, hlS, hl⟩ := pigeonhole G.μ G.μ_nonneg _ (fun e => e.2.factorization p) k
    (fun l => G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    (by
      intro l e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨he.1.1, he.1.2.1, he.2⟩)
    _ hB0 hb
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hlS
  have hdist := (Finset.mem_filter.1 he).2.2
  refine ⟨e.2.factorization p, hdist, ?_⟩
  refine conclude G hδ p hp hpP r k _ hr hpr hdist hl (Or.inr ?_)
  exact small_other_slice G.μ_nonneg G.W p k _ hp0 (by omega) hW

/-- Lemma 11.4 (the symmetric version of Lemma 11.3). -/
theorem lemma114 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (r l : ℕ) (hr : 1 ≤ r) (hpr : T0 < (p : ℝ) ^ r)
    (hV : (1 - K40 / p) * wsum G.μ G.V ≤ wsum G.μ (vslice G.V p l)) :
    (∃ k : ℕ, r + 1 ≤ (k - l) + (l - k) ∧
        2 * G.quality < (G.restrictPrime p k l hp hpP).quality ∧
        2 * G.density * G.quality <
          (G.restrictPrime p k l hp hpP).density * (G.restrictPrime p k l hp hpP).quality) ∨
      esum G.μ (G.E.filter (fun e => e.2.factorization p = l ∧
          r + 1 ≤ (e.1.factorization p - l) + (l - e.1.factorization p))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by
  by_cases hb : esum G.μ (G.E.filter (fun e => e.2.factorization p = l ∧
          r + 1 ≤ (e.1.factorization p - l) + (l - e.1.factorization p))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))
  · exact Or.inr hb
  left
  push Not at hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hEpos : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hB0 : 0 ≤ esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by positivity
  obtain ⟨k, hkS, hk⟩ := pigeonhole G.μ G.μ_nonneg _ (fun e => e.1.factorization p) l
    (fun k => G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    (by
      intro k e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨he.1.1, he.2, he.1.2.1⟩)
    _ hB0 hb
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hkS
  have hdist := (Finset.mem_filter.1 he).2.2
  refine ⟨e.1.factorization p, hdist, ?_⟩
  have hk' : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^
      ((e.1.factorization p - l) + (l - e.1.factorization p)) *
      (esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) <
      esum G.μ (G.restrictPrime p (e.1.factorization p) l hp hpP).E := by
    rw [Nat.add_comm (e.1.factorization p - l)]
    exact hk
  refine conclude G hδ p hp hpP r _ l hr hpr hdist hk' (Or.inl ?_)
  exact small_other_slice G.μ_nonneg G.V p l _ hp0 (by omega) hV

end GCDGraph

end DuffinSchaeffer

