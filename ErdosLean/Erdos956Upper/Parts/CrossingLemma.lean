import ErdosLean.Erdos956Upper.Parts.PlanarBound
import ErdosLean.Erdos956Upper.Parts.SubsetAverage

/-!
# Erdős #956 upper bound — P13: the crossing lemma

Székely's amplification: for every `S ⊆ V`, deleting one edge per crossing pair of the induced drawing and applying P11 gives `e_S ≤ 4|S| + cr_S/2`; averaging with weights `p^{|S|}(1-p)^{v-|S|}` gives `p²e ≤ 4pv + (p⁴·#crossDisj + p³·#crossAdj)/2`, and with `#crossAdj ≤ 4e`, `p ≤ 1/4` this yields the bound.
-/

namespace Erdos956Upper

open Erdos956 Metric

lemma Arc.crosses_symm {a b : Arc} (h : a.Crosses b) : b.Crosses a := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨x, h2, h1, h3.symm⟩

lemma Arc.left_zero' (a : Arc) : a.left 0 = a.l := by simp [Arc.left]

lemma Arc.right_zero' (a : Arc) : a.right 0 = a.r := by simp [Arc.right]

lemma Arc.left_ne_right' {a : Arc} (ha : a.Valid) : a.left ≠ a.right := by
  intro h
  have h0 : a.left 0 = a.right 0 := by rw [h]
  rw [Arc.left_zero', Arc.right_zero'] at h0
  exact absurd h0 (ne_of_lt ha.1)

/-- Deleting one arc per crossing pair: `|B| ≤ 4|W| + cr(B)/2` (cr counts ordered pairs). -/
lemma crossing_amplify {ι : Type*} (W : Finset E) (arc : ι → Arc) (B : Finset ι)
    (hvalid : ∀ i ∈ B, (arc i).Valid)
    (hend : ∀ i ∈ B, (arc i).left ∈ W ∧ (arc i).right ∈ W)
    (havoid : ∀ i ∈ B, ∀ z ∈ W, (arc i).Avoids z)
    (hsimple : ∀ i ∈ B, ∀ j ∈ B, (arc i).left = (arc j).left →
      (arc i).right = (arc j).right → i = j) :
    (B.card : ℝ) ≤ 4 * W.card + (crossAll B arc).card / 2 := by
  classical
  induction B using Finset.strongInduction with
  | H B ih =>
  by_cases hnc : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ¬ (arc i).Crosses (arc j)
  · have h := planar_bound W B arc hvalid hend havoid hsimple hnc
    have h' : (B.card : ℝ) ≤ 4 * W.card := by exact_mod_cast h
    have : (0:ℝ) ≤ (crossAll B arc).card / 2 := by positivity
    linarith
  · push Not at hnc
    obtain ⟨i, hi, j, hj, hij, hcr⟩ := hnc
    have hsub : B.erase i ⊂ B := Finset.erase_ssubset hi
    have hmem : ∀ k ∈ B.erase i, k ∈ B := fun k hk => Finset.mem_of_mem_erase hk
    have ih' := ih (B.erase i) hsub (fun k hk => hvalid k (hmem k hk))
      (fun k hk => hend k (hmem k hk))
      (fun k hk => havoid k (hmem k hk))
      (fun k hk l hl => hsimple k (hmem k hk) l (hmem l hl))
    have hcard : (B.erase i).card + 1 = B.card := Finset.card_erase_add_one hi
    have hcross : (crossAll (B.erase i) arc).card + 2 ≤ (crossAll B arc).card := by
      have hdisj : Disjoint (crossAll (B.erase i) arc) {(i, j), (j, i)} := by
        rw [Finset.disjoint_left]
        intro q hq hq2
        simp only [crossAll, Finset.mem_filter, Finset.mem_product] at hq
        rcases Finset.mem_insert.1 hq2 with h | h
        · subst h; exact (Finset.notMem_erase i B) hq.1.1
        · have h' := Finset.mem_singleton.1 h
          subst h'
          exact (Finset.notMem_erase i B) hq.1.2
      have hpair : ({(i, j), (j, i)} : Finset (ι × ι)).card = 2 := by
        apply Finset.card_pair
        intro h; exact hij (Prod.mk.inj h).1
      have hsubset : crossAll (B.erase i) arc ∪ {(i, j), (j, i)} ⊆ crossAll B arc := by
        intro q hq
        simp only [crossAll, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq with ⟨⟨h1, h2⟩, h3, h4⟩ | rfl | rfl
        · exact ⟨⟨hmem _ h1, hmem _ h2⟩, h3, h4⟩
        · exact ⟨⟨hi, hj⟩, hij, hcr⟩
        · exact ⟨⟨hj, hi⟩, hij.symm, Arc.crosses_symm hcr⟩
      have := Finset.card_le_card hsubset
      rw [Finset.card_union_of_disjoint hdisj, hpair] at this
      exact this
    have hcr' : ((crossAll (B.erase i) arc).card : ℝ) + 2 ≤ (crossAll B arc).card := by
      exact_mod_cast hcross
    have hc' : ((B.erase i).card : ℝ) + 1 = B.card := by exact_mod_cast hcard
    linarith

/-- Binomial averaging of a filtered count. -/
lemma weighted_filter_card {α : Type*} [DecidableEq E] (V : Finset E) (p : ℝ) (s : Finset α)
    (F : α → Finset E) (hF : ∀ a ∈ s, F a ⊆ V) :
    ∑ S ∈ V.powerset, p ^ S.card * (1 - p) ^ (V.card - S.card) *
        ((s.filter (fun a => F a ⊆ S)).card : ℝ) = ∑ a ∈ s, p ^ (F a).card := by
  calc ∑ S ∈ V.powerset, p ^ S.card * (1 - p) ^ (V.card - S.card) *
        ((s.filter (fun a => F a ⊆ S)).card : ℝ)
      = ∑ S ∈ V.powerset, ∑ a ∈ s,
          (if F a ⊆ S then p ^ S.card * (1 - p) ^ (V.card - S.card) else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.natCast_card_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
    _ = ∑ a ∈ s, ∑ S ∈ V.powerset,
          (if F a ⊆ S then p ^ S.card * (1 - p) ^ (V.card - S.card) else 0) :=
        Finset.sum_comm
    _ = ∑ a ∈ s, p ^ (F a).card :=
        Finset.sum_congr rfl fun a ha => sum_weight_subset V (F a) (hF a ha) p

theorem crossing_lemma {ι : Type*} (V : Finset E) (A : Finset ι) (arc : ι → Arc)
    (hvalid : ∀ i ∈ A, (arc i).Valid)
    (hend : ∀ i ∈ A, (arc i).left ∈ V ∧ (arc i).right ∈ V)
    (havoid : ∀ i ∈ A, ∀ z ∈ V, (arc i).Avoids z)
    (hsimple : ∀ i ∈ A, ∀ j ∈ A, (arc i).left = (arc j).left →
      (arc i).right = (arc j).right → i = j)
    (hadj : (crossAdj A arc).card ≤ 4 * A.card) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 4) :
    (A.card : ℝ) ≤ 8 * V.card / p + p ^ 2 * (crossDisj A arc).card := by
  classical
  have hp1 : p ≤ 1 := by linarith
  set w : Finset E → ℝ := fun S => p ^ S.card * (1 - p) ^ (V.card - S.card) with hw_def
  have hw : ∀ S, 0 ≤ w S := fun S =>
    mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)
  set T : ι → Finset E := fun i => {(arc i).left, (arc i).right} with hT_def
  set U : ι × ι → Finset E := fun q =>
    insert (arc q.1).left (insert (arc q.1).right {(arc q.2).left, (arc q.2).right}) with hU_def
  set AS : Finset E → Finset ι := fun S => A.filter (fun i => T i ⊆ S) with hAS_def
  -- per-subset bound
  have hS : ∀ S ∈ V.powerset,
      ((AS S).card : ℝ) ≤ 4 * S.card + (crossAll (AS S) arc).card / 2 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hmem : ∀ i ∈ AS S, i ∈ A ∧ T i ⊆ S := fun i hi => Finset.mem_filter.1 hi
    apply crossing_amplify S arc (AS S)
    · intro i hi; exact hvalid i (hmem i hi).1
    · intro i hi
      have h := (hmem i hi).2
      exact ⟨h (by simp [T]), h (by simp [T])⟩
    · intro i hi z hz; exact havoid i (hmem i hi).1 z (hS hz)
    · intro i hi j hj; exact hsimple i (hmem i hi).1 j (hmem j hj).1
  have hsum : ∑ S ∈ V.powerset, w S * (AS S).card ≤
      ∑ S ∈ V.powerset, w S * (4 * S.card + (crossAll (AS S) arc).card / 2) :=
    Finset.sum_le_sum fun S hS' => mul_le_mul_of_nonneg_left (hS S hS') (hw S)
  have hexp : ∑ S ∈ V.powerset, w S * (4 * S.card + (crossAll (AS S) arc).card / 2) =
      4 * ∑ S ∈ V.powerset, w S * S.card +
        (∑ S ∈ V.powerset, w S * (crossAll (AS S) arc).card) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  -- left side
  have hL : ∑ S ∈ V.powerset, w S * (AS S).card = A.card * p ^ 2 := by
    have := weighted_filter_card V p A T (fun i hi => by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hend i hi).1
      · exact (hend i hi).2)
    rw [this]
    rw [Finset.sum_congr rfl (g := fun _ => p ^ 2)]
    · simp
    · intro i hi
      simp only [T]
      rw [Finset.card_pair (Arc.left_ne_right' (hvalid i hi))]
  -- vertex term
  have hV : ∑ S ∈ V.powerset, w S * S.card = V.card * p := by
    have := weighted_filter_card V p V (fun z => {z}) (fun z hz => by simpa using hz)
    have hc : ∀ S ∈ V.powerset, (V.filter (fun z => ({z} : Finset E) ⊆ S)).card = S.card := by
      intro S hS
      rw [Finset.mem_powerset] at hS
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.singleton_subset_iff]
      exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
    rw [Finset.sum_congr rfl (fun S hS => by rw [hc S hS])] at this
    rw [this]
    simp
  -- crossing term
  have hUV : ∀ q ∈ crossAll A arc, U q ⊆ V := by
    intro q hq
    simp only [crossAll, Finset.mem_filter, Finset.mem_product] at hq
    intro x hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hend _ hq.1.1).1
    · exact (hend _ hq.1.1).2
    · exact (hend _ hq.1.2).1
    · exact (hend _ hq.1.2).2
  have hC1 : ∀ S ∈ V.powerset, ((crossAll (AS S) arc).card : ℝ) ≤
      ((crossAll A arc).filter (fun q => U q ⊆ S)).card := by
    intro S _
    have hsub : crossAll (AS S) arc ⊆ (crossAll A arc).filter (fun q => U q ⊆ S) := by
      intro q hq
      simp only [crossAll, AS, Finset.mem_filter, Finset.mem_product] at hq ⊢
      obtain ⟨⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩, h3, h4⟩ := hq
      refine ⟨⟨⟨h1, h2⟩, h3, h4⟩, ?_⟩
      intro x hx
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h1' (by simp [T])
      · exact h1' (by simp [T])
      · exact h2' (by simp [T])
      · exact h2' (by simp [T])
    exact_mod_cast Finset.card_le_card hsub
  have hC : ∑ S ∈ V.powerset, w S * (crossAll (AS S) arc).card ≤
      ∑ q ∈ crossAll A arc, p ^ (U q).card := by
    rw [← weighted_filter_card V p (crossAll A arc) U hUV]
    exact Finset.sum_le_sum fun S hS' => mul_le_mul_of_nonneg_left (hC1 S hS') (hw S)
  -- cardinalities of `U`
  have hU3 : ∀ q ∈ crossAll A arc, 3 ≤ (U q).card := by
    intro q hq
    simp only [crossAll, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, h3, _⟩ := hq
    set a := arc q.1
    set b := arc q.2
    have ha := hvalid _ h1
    have hb := hvalid _ h2
    have hab : a.left ≠ a.right := Arc.left_ne_right' ha
    have hbb : b.left ≠ b.right := Arc.left_ne_right' hb
    have hex : ∃ x, (x = b.left ∨ x = b.right) ∧ x ≠ a.left ∧ x ≠ a.right := by
      by_cases hl : b.left = a.left ∨ b.left = a.right
      · by_cases hr : b.right = a.left ∨ b.right = a.right
        · exfalso
          rcases hl with hl | hl <;> rcases hr with hr | hr
          · exact hbb (hl.trans hr.symm)
          · exact h3 (hsimple _ h1 _ h2 hl.symm hr.symm)
          · have e1 : b.left 0 = a.right 0 := by rw [hl]
            have e2 : b.right 0 = a.left 0 := by rw [hr]
            rw [Arc.left_zero', Arc.right_zero'] at e1 e2
            linarith [ha.1, hb.1]
          · exact hbb (hl.trans hr.symm)
        · push Not at hr
          exact ⟨b.right, Or.inr rfl, hr.1, hr.2⟩
      · push Not at hl
        exact ⟨b.left, Or.inl rfl, hl.1, hl.2⟩
    obtain ⟨x, hx, hxa, hxb⟩ := hex
    have hsubU : ({x, a.left, a.right} : Finset E) ⊆ U q := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      simp only [U, Finset.mem_insert, Finset.mem_singleton]
      rcases hy with rfl | rfl | rfl
      · rcases hx with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have h3c : ({x, a.left, a.right} : Finset E).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxa, hxb⟩
    rw [← h3c]
    exact Finset.card_le_card hsubU
  have hU4 : ∀ q ∈ crossAll A arc, ¬ (arc q.1).ShareEnd (arc q.2) → 4 ≤ (U q).card := by
    intro q hq hns
    simp only [crossAll, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, _, _⟩ := hq
    simp only [Arc.ShareEnd, not_or] at hns
    obtain ⟨n1, n2, n3, n4⟩ := hns
    have hab : (arc q.1).left ≠ (arc q.1).right := Arc.left_ne_right' (hvalid _ h1)
    have hbb : (arc q.2).left ≠ (arc q.2).right := Arc.left_ne_right' (hvalid _ h2)
    simp only [U]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hbb]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n3, n4⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, n1, n2⟩
  have hsplit : ∑ q ∈ crossAll A arc, p ^ (U q).card ≤
      p ^ 3 * (crossAdj A arc).card + p ^ 4 * (crossDisj A arc).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (crossAll A arc)
      (fun q => (arc q.1).ShareEnd (arc q.2))]
    have e1 : (crossAll A arc).filter (fun q => (arc q.1).ShareEnd (arc q.2)) =
        crossAdj A arc := by
      unfold crossAdj; congr 1
    have e2 : (crossAll A arc).filter (fun q => ¬ (arc q.1).ShareEnd (arc q.2)) =
        crossDisj A arc := by
      unfold crossDisj; congr 1
    rw [e1, e2]
    gcongr
    · calc ∑ q ∈ crossAdj A arc, p ^ (U q).card ≤ ∑ q ∈ crossAdj A arc, p ^ 3 := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hq' : q ∈ crossAll A arc := by
              rw [← e1] at hq; exact (Finset.mem_filter.1 hq).1
            exact pow_le_pow_of_le_one hp0.le hp1 (hU3 q hq')
        _ = p ^ 3 * (crossAdj A arc).card := by simp [mul_comm]
    · calc ∑ q ∈ crossDisj A arc, p ^ (U q).card ≤ ∑ q ∈ crossDisj A arc, p ^ 4 := by
            refine Finset.sum_le_sum fun q hq => ?_
            rw [← e2] at hq
            obtain ⟨hq', hns⟩ := Finset.mem_filter.1 hq
            exact pow_le_pow_of_le_one hp0.le hp1 (hU4 q hq' hns)
        _ = p ^ 4 * (crossDisj A arc).card := by simp [mul_comm]
  -- final arithmetic
  have hadj' : ((crossAdj A arc).card : ℝ) ≤ 4 * A.card := by exact_mod_cast hadj
  set e : ℝ := (A.card : ℝ) with he
  set v : ℝ := (V.card : ℝ) with hv
  set Dj : ℝ := ((crossDisj A arc).card : ℝ) with hDj
  set Ad : ℝ := ((crossAdj A arc).card : ℝ) with hAd
  have hmain : e * p ^ 2 ≤ 4 * (v * p) + (p ^ 3 * Ad + p ^ 4 * Dj) / 2 := by
    have := hsum
    rw [hexp, hL, hV] at this
    linarith
  have he0 : 0 ≤ e := by positivity
  have hp3 : p ^ 3 * Ad ≤ p ^ 3 * (4 * e) :=
    mul_le_mul_of_nonneg_left hadj' (pow_nonneg hp0.le 3)
  have h2 : 2 * p ^ 3 * e ≤ p ^ 2 * e / 2 := by
    have : 0 ≤ p ^ 2 * e := by positivity
    nlinarith
  have key : p ^ 2 * e ≤ p ^ 2 * (8 * v / p + p ^ 2 * Dj) := by
    have hq : p ^ 2 * (8 * v / p) = 8 * p * v := by field_simp
    rw [mul_add, hq]
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

end Erdos956Upper
