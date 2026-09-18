import ErdosLean.Erdos956Upper.Parts.UpperDrawing

/-!
# Erdős #956 upper bound — P15: counting crossings of the upper drawing

Two distinct curves meet in an interval containing at most one point of `X` (P8, P9), so they contribute at most 4 crossing edge pairs; an edge crosses at most one other edge with the same left (resp. right) endpoint (P9, three curves).
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

/-! ### Auxiliary facts -/

lemma mem_upperEdges_iff {e : E × E × E} :
    e ∈ upperEdges D X ↔ (e.1 ∈ X ∧ e.2.1 ∈ X ∧ e.2.2 ∈ X) ∧ Consec D X e.1 e.2.1 e.2.2 := by
  classical
  unfold upperEdges
  simp only [Finset.mem_filter, Finset.mem_product]

lemma onUpper_curve {c p : E} (h : OnUpper D (p - c)) : p 1 = curve D c (p 0) := by
  obtain ⟨_, h2⟩ := h
  simp only [PiLp.sub_apply] at h2
  simp only [curve]; linarith

lemma onUpper_abs {c p : E} (h : OnUpper D (p - c)) : |p 0 - c 0| < wid D := by
  simpa using h.1

lemma onUpper_of_curve {c z : E} (h0 : |z 0 - c 0| < wid D) (h1 : z 1 = curve D c (z 0)) :
    OnUpper D (z - c) := by
  refine ⟨by simpa using h0, ?_⟩
  simp only [PiLp.sub_apply, curve] at *; linarith

lemma pt_ext' {p q : E} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i; fin_cases i
  · exact h0
  · exact h1

lemma abs_between {a b s k w : ℝ} (ha : |a - k| < w) (hb : |b - k| < w) (h1 : a ≤ s)
    (h2 : s ≤ b) : |s - k| < w := by
  obtain ⟨a1, a2⟩ := abs_lt.1 ha
  obtain ⟨b1, b2⟩ := abs_lt.1 hb
  exact abs_lt.2 ⟨by linarith, by linarith⟩

lemma zero_mid (hS : SepConfig D X) {c c' : E} {t1 s t2 : ℝ}
    (h1 : |t1 - c 0| < wid D ∧ |t1 - c' 0| < wid D)
    (hs : |s - c 0| < wid D ∧ |s - c' 0| < wid D)
    (h2 : |t2 - c 0| < wid D ∧ |t2 - c' 0| < wid D) (hts1 : t1 ≤ s) (hts2 : s ≤ t2)
    (e1 : curve D c t1 = curve D c' t1) (e2 : curve D c t2 = curve D c' t2) :
    curve D c s = curve D c' s := by
  rcases le_total (c 0) (c' 0) with h | h
  · have A := curve_sub_antitoneOn hS h
    have a1 := A h1 hs hts1
    have a2 := A hs h2 hts2
    simp only at a1 a2
    linarith
  · have A := curve_sub_antitoneOn hS h
    have a1 := A ⟨h1.2, h1.1⟩ ⟨hs.2, hs.1⟩ hts1
    have a2 := A ⟨hs.2, hs.1⟩ ⟨h2.2, h2.1⟩ hts2
    simp only at a1 a2
    linarith

/-- Two edges on the same curve whose open intervals meet are equal. -/
lemma same_center_eq {e e' : E × E × E} (he : e ∈ upperEdges D X) (he' : e' ∈ upperEdges D X)
    (hc : e.1 = e'.1) {x : ℝ} (hx : x ∈ Set.Ioo (e.2.1 0) (e.2.2 0))
    (hx' : x ∈ Set.Ioo (e'.2.1 0) (e'.2.2 0)) : e = e' := by
  obtain ⟨c, p, q⟩ := e
  obtain ⟨c', p', q'⟩ := e'
  simp only at hc hx hx'
  subst hc
  rw [mem_upperEdges_iff] at he he'
  obtain ⟨⟨_, hpX, hqX⟩, hp, hq, _, hno⟩ := he
  obtain ⟨⟨_, hp'X, hq'X⟩, hp', hq', _, hno'⟩ := he'
  simp only at hpX hqX hp hq hno hp'X hq'X hp' hq' hno'
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hx1', hx2'⟩ := hx'
  have hpp : p 0 = p' 0 := by
    rcases lt_trichotomy (p 0) (p' 0) with h | h | h
    · exact absurd ⟨h, by linarith⟩ (hno p' hp'X hp')
    · exact h
    · exact absurd ⟨h, by linarith⟩ (hno' p hpX hp)
  have hqq : q 0 = q' 0 := by
    rcases lt_trichotomy (q 0) (q' 0) with h | h | h
    · exact absurd ⟨by linarith, h⟩ (hno' q hqX hq)
    · exact h
    · exact absurd ⟨by linarith, h⟩ (hno q' hq'X hq')
  have e1 : p = p' := pt_ext' hpp (by rw [onUpper_curve hp, onUpper_curve hp', hpp])
  have e2 : q = q' := pt_ext' hqq (by rw [onUpper_curve hq, onUpper_curve hq', hqq])
  subst e1 e2; rfl

lemma dom_of_edge {e : E × E × E} (he : e ∈ upperEdges D X) {x : ℝ} (h1 : e.2.1 0 ≤ x)
    (h2 : x ≤ e.2.2 0) : |x - e.1 0| < wid D := by
  rw [mem_upperEdges_iff] at he
  exact abs_between (onUpper_abs he.2.1) (onUpper_abs he.2.2.1) h1 h2

lemma mem_crossAll_iff {e e' : E × E × E} :
    (e, e') ∈ crossAll (upperEdges D X) (upperArc D) ↔
      e ∈ upperEdges D X ∧ e' ∈ upperEdges D X ∧ e ≠ e' ∧
        ∃ x, x ∈ Set.Ioo (e.2.1 0) (e.2.2 0) ∧ x ∈ Set.Ioo (e'.2.1 0) (e'.2.2 0) ∧
          curve D e.1 x = curve D e'.1 x := by
  unfold crossAll
  rw [@Finset.mem_filter _ _ (_) _ _, Finset.mem_product]
  simp only [Arc.Crosses, upperArc]
  tauto

lemma arc_left {e : E × E × E} (he : e ∈ upperEdges D X) : (upperArc D e).left = e.2.1 := by
  rw [mem_upperEdges_iff] at he
  exact pt_ext' (by simp [Arc.left, upperArc]) (by simp [Arc.left, upperArc, onUpper_curve he.2.1])

lemma arc_right {e : E × E × E} (he : e ∈ upperEdges D X) : (upperArc D e).right = e.2.2 := by
  rw [mem_upperEdges_iff] at he
  exact pt_ext' (by simp [Arc.right, upperArc])
    (by simp [Arc.right, upperArc, onUpper_curve he.2.2.1])

/-! ### Disjoint crossings -/

/-- Edges of centre `c` whose open interval meets the coincidence set with the curve of `c'`. -/
noncomputable def meetSet (D : Set E) (X : Finset E) (c c' : E) : Finset (E × E × E) := by
  classical
  exact (upperEdges D X).filter fun e => e.1 = c ∧ c ≠ c' ∧
    ∃ x ∈ Set.Ioo (e.2.1 0) (e.2.2 0), |x - c' 0| < wid D ∧ curve D c x = curve D c' x

lemma mem_meetSet {c c' : E} {e : E × E × E} :
    e ∈ meetSet D X c c' ↔ e ∈ upperEdges D X ∧ e.1 = c ∧ c ≠ c' ∧
      ∃ x ∈ Set.Ioo (e.2.1 0) (e.2.2 0), |x - c' 0| < wid D ∧ curve D c x = curve D c' x := by
  classical
  unfold meetSet
  simp only [Finset.mem_filter]

lemma meetSet_order {c c' : E} {a b : E × E × E} (ha : a ∈ meetSet D X c c')
    (hb : b ∈ meetSet D X c c') (hab : a ≠ b) : a.2.2 0 ≤ b.2.1 0 ∨ b.2.2 0 ≤ a.2.1 0 := by
  rw [mem_meetSet] at ha hb
  by_contra h
  rw [not_or, not_le, not_le] at h
  have hae := ha.1
  have hbe := hb.1
  rw [mem_upperEdges_iff] at hae hbe
  have hpa := hae.2.2.2.1
  have hpb := hbe.2.2.2.1
  have hlt : max (a.2.1 0) (b.2.1 0) < min (a.2.2 0) (b.2.2 0) :=
    max_lt (lt_min hpa h.2) (lt_min h.1 hpb)
  refine hab (same_center_eq ha.1 hb.1 (ha.2.1.trans hb.2.1.symm)
    (x := (max (a.2.1 0) (b.2.1 0) + min (a.2.2 0) (b.2.2 0)) / 2) ?_ ?_)
  · constructor
    · linarith [le_max_left (a.2.1 0) (b.2.1 0)]
    · linarith [min_le_left (a.2.2 0) (b.2.2 0)]
  · constructor
    · linarith [le_max_right (a.2.1 0) (b.2.1 0)]
    · linarith [min_le_right (a.2.2 0) (b.2.2 0)]

lemma meetSet_middle (hS : SepConfig D X) {c c' : E} (hc : c ∈ X) (hc' : c' ∈ X)
    {a m b : E × E × E} (ha : a ∈ meetSet D X c c') (hm : m ∈ meetSet D X c c')
    (hb : b ∈ meetSet D X c c') (ham : a.2.2 0 ≤ m.2.1 0) (hmb : m.2.2 0 ≤ b.2.1 0) : False := by
  rw [mem_meetSet] at ha hm hb
  obtain ⟨hae, rfl, hcc, ta, ⟨ta1, ta2⟩, tad, taz⟩ := ha
  obtain ⟨hme, hmc, -, tm, ⟨tm1, tm2⟩, tmd, tmz⟩ := hm
  obtain ⟨hbe, hbc, -, tb, ⟨tb1, tb2⟩, tbd, tbz⟩ := hb
  have hme' := hme
  rw [mem_upperEdges_iff] at hme'
  obtain ⟨⟨-, hpX, hqX⟩, hp, hq, hpq, -⟩ := hme'
  rw [hmc] at hp hq
  have dA := dom_of_edge hae ta1.le ta2.le
  have dM := dom_of_edge hme tm1.le tm2.le
  have dB := dom_of_edge hbe tb1.le tb2.le
  rw [hmc] at dM
  rw [hbc] at dB
  -- the left endpoint of `m`
  have hsp : curve D a.1 (m.2.1 0) = curve D c' (m.2.1 0) :=
    zero_mid hS ⟨dA, tad⟩ ⟨onUpper_abs hp, abs_between tad tmd (by linarith) (by linarith)⟩
      ⟨dM, tmd⟩ (by linarith) (by linarith) taz tmz
  have hsq : curve D a.1 (m.2.2 0) = curve D c' (m.2.2 0) :=
    zero_mid hS ⟨dM, tmd⟩ ⟨onUpper_abs hq, abs_between tmd tbd (by linarith) (by linarith)⟩
      ⟨dB, tbd⟩ (by linarith) (by linarith) tmz tbz
  have hp' : OnUpper D (m.2.1 - c') := onUpper_of_curve
    (abs_between tad tmd (by linarith) (by linarith)) (by rw [onUpper_curve hp, hsp])
  have hq' : OnUpper D (m.2.2 - c') := onUpper_of_curve
    (abs_between tmd tbd (by linarith) (by linarith)) (by rw [onUpper_curve hq, hsq])
  have hne : m.2.1 ≠ m.2.2 := fun h => by rw [h] at hpq; exact lt_irrefl _ hpq
  exact no_two_common_points hS hc hc' hpX hqX hcc hne hp hq hp' hq'

lemma meetSet_card (hS : SepConfig D X) {c c' : E} (hc : c ∈ X) (hc' : c' ∈ X) :
    (meetSet D X c c').card ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.1 h
  have M := fun {x y z : E × E × E} (hx : x ∈ meetSet D X c c') (hy : y ∈ meetSet D X c c')
    (hz : z ∈ meetSet D X c c') (h1 : x.2.2 0 ≤ y.2.1 0) (h2 : y.2.2 0 ≤ z.2.1 0) =>
    meetSet_middle hS hc hc' hx hy hz h1 h2
  rcases meetSet_order ha hb hab with h1 | h1 <;>
  rcases meetSet_order hb hd hbd with h2 | h2 <;>
  rcases meetSet_order ha hd had with h3 | h3
  · exact M ha hb hd h1 h2
  · exact M ha hb hd h1 h2
  · exact M ha hd hb h3 h2
  · exact M hd ha hb h3 h1
  · exact M hb ha hd h1 h3
  · exact M hb hd ha h2 h3
  · exact M hd hb ha h2 h1
  · exact M hd hb ha h2 h1

theorem crossAll_upper_le (hS : SepConfig D X) :
    (crossAll (upperEdges D X) (upperArc D)).card ≤ 4 * X.card ^ 2 := by
  classical
  have hsub : crossAll (upperEdges D X) (upperArc D) ⊆
      (X ×ˢ X).biUnion (fun cc => meetSet D X cc.1 cc.2 ×ˢ meetSet D X cc.2 cc.1) := by
    rintro ⟨e, e'⟩ hq
    obtain ⟨he, he', hne, x, hx, hx', hxe⟩ := mem_crossAll_iff.1 hq
    have hcc : e.1 ≠ e'.1 := fun h => hne (same_center_eq he he' h hx hx')
    have hcX : e.1 ∈ X := ((mem_upperEdges_iff.1 he).1).1
    have hc'X : e'.1 ∈ X := ((mem_upperEdges_iff.1 he').1).1
    rw [Finset.mem_biUnion]
    refine ⟨(e.1, e'.1), Finset.mem_product.2 ⟨hcX, hc'X⟩, Finset.mem_product.2 ⟨?_, ?_⟩⟩
    · exact mem_meetSet.2 ⟨he, rfl, hcc, x, hx, dom_of_edge he' hx'.1.le hx'.2.le, hxe⟩
    · exact mem_meetSet.2 ⟨he', rfl, Ne.symm hcc, x, hx', dom_of_edge he hx.1.le hx.2.le,
        hxe.symm⟩
  calc (crossAll (upperEdges D X) (upperArc D)).card
      ≤ ((X ×ˢ X).biUnion (fun cc => meetSet D X cc.1 cc.2 ×ˢ meetSet D X cc.2 cc.1)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ cc ∈ X ×ˢ X, (meetSet D X cc.1 cc.2 ×ˢ meetSet D X cc.2 cc.1).card :=
        Finset.card_biUnion_le
    _ ≤ (X ×ˢ X).card • 4 := by
        refine Finset.sum_le_card_nsmul _ _ _ fun cc hcc => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hcc
        rw [Finset.card_product]
        have a1 := meetSet_card hS h1 h2
        have a2 := meetSet_card hS h2 h1
        calc _ ≤ 2 * 2 := Nat.mul_le_mul a1 a2
          _ = 4 := by norm_num
    _ = 4 * X.card ^ 2 := by rw [Finset.card_product, smul_eq_mul]; ring

theorem crossDisj_upper_le (hS : SepConfig D X) :
    (crossDisj (upperEdges D X) (upperArc D)).card ≤ 4 * X.card ^ 2 := by
  classical
  refine le_trans (Finset.card_le_card ?_) (crossAll_upper_le hS)
  unfold crossDisj
  exact Finset.filter_subset _ _

/-! ### Adjacent crossings -/

/-- Two edges crossing `e` and sharing its left endpoint are equal. -/
lemma left_unique (hS : SepConfig D X) {e e1 e2 : E × E × E}
    (h1 : (e, e1) ∈ crossAll (upperEdges D X) (upperArc D))
    (h2 : (e, e2) ∈ crossAll (upperEdges D X) (upperArc D))
    (l1 : e1.2.1 = e.2.1) (l2 : e2.2.1 = e.2.1) : e1 = e2 := by
  obtain ⟨he, he1, hne1, x1, hx1, hx1', hz1⟩ := mem_crossAll_iff.1 h1
  obtain ⟨-, he2, hne2, x2, hx2, hx2', hz2⟩ := mem_crossAll_iff.1 h2
  have hc1 : e.1 ≠ e1.1 := fun h => hne1 (same_center_eq he he1 h hx1 hx1')
  have hc2 : e.1 ≠ e2.1 := fun h => hne2 (same_center_eq he he2 h hx2 hx2')
  rw [l1] at hx1'
  rw [l2] at hx2'
  obtain ⟨hx1a, hx1b⟩ := hx1
  obtain ⟨-, hx1c⟩ := hx1'
  obtain ⟨hx2a, hx2b⟩ := hx2
  obtain ⟨-, hx2c⟩ := hx2'
  by_cases h12 : e1.1 = e2.1
  · refine same_center_eq he1 he2 h12 (x := (e.2.1 0 + min x1 x2) / 2) ?_ ?_
    · rw [l1]; constructor
      · have := lt_min hx1a hx2a; linarith
      · linarith [min_le_left x1 x2]
    · rw [l2]; constructor
      · have := lt_min hx1a hx2a; linarith
      · linarith [min_le_right x1 x2]
  exfalso
  have E0 := mem_upperEdges_iff.1 he
  have E1 := mem_upperEdges_iff.1 he1
  have E2 := mem_upperEdges_iff.1 he2
  rw [l1] at E1
  rw [l2] at E2
  have hp0 := onUpper_curve E0.2.1
  have hp1 := onUpper_curve E1.2.1
  have hp2 := onUpper_curve E2.2.1
  set p := e.2.1
  have d0 : ∀ y, p 0 ≤ y → y ≤ x1 → |y - e.1 0| < wid D := fun y a b =>
    dom_of_edge he a (by linarith)
  have d1 : ∀ y, p 0 ≤ y → y ≤ x1 → |y - e1.1 0| < wid D := fun y a b =>
    dom_of_edge he1 (by rw [l1]; exact a) (by linarith)
  have d0' : ∀ y, p 0 ≤ y → y ≤ x2 → |y - e.1 0| < wid D := fun y a b =>
    dom_of_edge he a (by linarith)
  have d2 : ∀ y, p 0 ≤ y → y ≤ x2 → |y - e2.1 0| < wid D := fun y a b =>
    dom_of_edge he2 (by rw [l2]; exact a) (by linarith)
  refine no_three_coincident hS E0.1.1 E1.1.1 E2.1.1 hc1 hc2 h12 (α := p 0) (β := min x1 x2)
    (lt_min hx1a hx2a) fun y ⟨ya, yb⟩ => ?_
  have yb1 := yb.trans (min_le_left x1 x2)
  have yb2 := yb.trans (min_le_right x1 x2)
  refine ⟨d0 y ya yb1, d1 y ya yb1, d2 y ya yb2, ?_, ?_⟩
  · exact zero_mid hS ⟨d0 _ le_rfl hx1a.le, d1 _ le_rfl hx1a.le⟩ ⟨d0 y ya yb1, d1 y ya yb1⟩
      ⟨d0 _ hx1a.le le_rfl, d1 _ hx1a.le le_rfl⟩ ya yb1 (by rw [← hp0, ← hp1]) hz1
  · exact zero_mid hS ⟨d0' _ le_rfl hx2a.le, d2 _ le_rfl hx2a.le⟩ ⟨d0' y ya yb2, d2 y ya yb2⟩
      ⟨d0' _ hx2a.le le_rfl, d2 _ hx2a.le le_rfl⟩ ya yb2 (by rw [← hp0, ← hp2]) hz2

/-- Two edges crossing `e` and sharing its right endpoint are equal. -/
lemma right_unique (hS : SepConfig D X) {e e1 e2 : E × E × E}
    (h1 : (e, e1) ∈ crossAll (upperEdges D X) (upperArc D))
    (h2 : (e, e2) ∈ crossAll (upperEdges D X) (upperArc D))
    (l1 : e1.2.2 = e.2.2) (l2 : e2.2.2 = e.2.2) : e1 = e2 := by
  obtain ⟨he, he1, hne1, x1, hx1, hx1', hz1⟩ := mem_crossAll_iff.1 h1
  obtain ⟨-, he2, hne2, x2, hx2, hx2', hz2⟩ := mem_crossAll_iff.1 h2
  have hc1 : e.1 ≠ e1.1 := fun h => hne1 (same_center_eq he he1 h hx1 hx1')
  have hc2 : e.1 ≠ e2.1 := fun h => hne2 (same_center_eq he he2 h hx2 hx2')
  rw [l1] at hx1'
  rw [l2] at hx2'
  obtain ⟨hx1a, hx1b⟩ := hx1
  obtain ⟨hx1c, -⟩ := hx1'
  obtain ⟨hx2a, hx2b⟩ := hx2
  obtain ⟨hx2c, -⟩ := hx2'
  by_cases h12 : e1.1 = e2.1
  · refine same_center_eq he1 he2 h12 (x := (max x1 x2 + e.2.2 0) / 2) ?_ ?_
    · rw [l1]; constructor
      · linarith [le_max_left x1 x2]
      · have := max_lt hx1b hx2b; linarith
    · rw [l2]; constructor
      · linarith [le_max_right x1 x2]
      · have := max_lt hx1b hx2b; linarith
  exfalso
  have E0 := mem_upperEdges_iff.1 he
  have E1 := mem_upperEdges_iff.1 he1
  have E2 := mem_upperEdges_iff.1 he2
  rw [l1] at E1
  rw [l2] at E2
  have hq0 := onUpper_curve E0.2.2.1
  have hq1 := onUpper_curve E1.2.2.1
  have hq2 := onUpper_curve E2.2.2.1
  set q := e.2.2
  have d0 : ∀ y, x1 ≤ y → y ≤ q 0 → |y - e.1 0| < wid D := fun y a b =>
    dom_of_edge he (by linarith) b
  have d1 : ∀ y, x1 ≤ y → y ≤ q 0 → |y - e1.1 0| < wid D := fun y a b =>
    dom_of_edge he1 (by linarith) (by rw [l1]; exact b)
  have d0' : ∀ y, x2 ≤ y → y ≤ q 0 → |y - e.1 0| < wid D := fun y a b =>
    dom_of_edge he (by linarith) b
  have d2 : ∀ y, x2 ≤ y → y ≤ q 0 → |y - e2.1 0| < wid D := fun y a b =>
    dom_of_edge he2 (by linarith) (by rw [l2]; exact b)
  refine no_three_coincident hS E0.1.1 E1.1.1 E2.1.1 hc1 hc2 h12 (α := max x1 x2) (β := q 0)
    (max_lt hx1b hx2b) fun y ⟨ya, yb⟩ => ?_
  have ya1 := (le_max_left x1 x2).trans ya
  have ya2 := (le_max_right x1 x2).trans ya
  refine ⟨d0 y ya1 yb, d1 y ya1 yb, d2 y ya2 yb, ?_, ?_⟩
  · exact zero_mid hS ⟨d0 _ le_rfl hx1b.le, d1 _ le_rfl hx1b.le⟩ ⟨d0 y ya1 yb, d1 y ya1 yb⟩
      ⟨d0 _ hx1b.le le_rfl, d1 _ hx1b.le le_rfl⟩ ya1 yb hz1 (by rw [← hq0, ← hq1])
  · exact zero_mid hS ⟨d0' _ le_rfl hx2b.le, d2 _ le_rfl hx2b.le⟩ ⟨d0' y ya2 yb, d2 y ya2 yb⟩
      ⟨d0' _ hx2b.le le_rfl, d2 _ hx2b.le le_rfl⟩ ya2 yb hz2 (by rw [← hq0, ← hq2])

theorem crossAdj_upper_le (hS : SepConfig D X) :
    (crossAdj (upperEdges D X) (upperArc D)).card ≤ 4 * (upperEdges D X).card := by
  classical
  have hmem : ∀ q ∈ crossAdj (upperEdges D X) (upperArc D),
      q ∈ crossAll (upperEdges D X) (upperArc D) ∧
        (q.1.2.1 = q.2.2.1 ∨ q.1.2.2 = q.2.2.2) := by
    rintro ⟨e, e'⟩ hq
    unfold crossAdj at hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hq, hsh⟩ := hq
    refine ⟨hq, ?_⟩
    obtain ⟨he, he', -, x, ⟨hx1, hx2⟩, ⟨hx1', hx2'⟩, -⟩ := mem_crossAll_iff.1 hq
    simp only [Arc.ShareEnd, arc_left he, arc_right he, arc_left he', arc_right he'] at hsh
    rcases hsh with h | h | h | h
    · exact Or.inl h
    · exfalso; have := congrArg (fun v : E => v 0) h; simp only at this; linarith
    · exfalso; have := congrArg (fun v : E => v 0) h; simp only at this; linarith
    · exact Or.inr h
  calc (crossAdj (upperEdges D X) (upperArc D)).card
      ≤ (upperEdges D X ×ˢ (Finset.univ : Finset Bool)).card := by
        refine Finset.card_le_card_of_injOn
          (fun q => (q.1, decide (q.1.2.1 = q.2.2.1))) ?_ ?_
        · intro q hq
          have := (mem_crossAll_iff.1 ((hmem q hq).1)).1
          exact Finset.mem_product.2 ⟨this, Finset.mem_univ _⟩
        · rintro ⟨e, e1⟩ hq1 ⟨e', e2⟩ hq2 heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, ht⟩ := heq
          obtain ⟨m1, s1⟩ := hmem _ hq1
          obtain ⟨m2, s2⟩ := hmem _ hq2
          simp only at s1 s2 m1 m2
          congr 1
          by_cases hl : e.2.1 = e1.2.1
          · have hl2 : e.2.1 = e2.2.1 := by simpa [hl] using ht
            exact left_unique hS m1 m2 hl.symm hl2.symm
          · have hl2 : ¬ e.2.1 = e2.2.1 := by simpa [hl] using ht
            exact right_unique hS m1 m2 (s1.resolve_left hl).symm (s2.resolve_left hl2).symm
    _ = 2 * (upperEdges D X).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
    _ ≤ 4 * (upperEdges D X).card := by omega

end Erdos956Upper
