import ErdosLean.Erdos956Upper.Parts.TranslateMono
import ErdosLean.Erdos956Upper.Parts.SegmentLemma

/-!
# Erdős #956 upper bound — P9: flat overlaps are harmless

Two distinct curves cannot share two points of `X`, and three distinct curves cannot coincide on a nondegenerate interval: in both cases `g` is affine on an interval `J`, the graph over `J` is a segment of `∂K`, and the half-chord lemma puts a difference of two points (or two centres) of `X` into `D`.
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

/-! ### Auxiliary lemmas -/

lemma eq_of_coords {u v : E} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext j
  fin_cases j
  · exact h0
  · exact h1

/-- Three-point concavity inequality, cleared of denominators. -/
lemma conc3 {I : Set ℝ} {G : ℝ → ℝ} (hG : ConcaveOn ℝ I G) {p m r : ℝ} (hp : p ∈ I)
    (hr : r ∈ I) (hpm : p < m) (hmr : m < r) :
    (r - m) * G p + (m - p) * G r ≤ (r - p) * G m := by
  have hrp : 0 < r - p := by linarith
  have h := hG.2 hp hr
    (div_nonneg (by linarith : (0:ℝ) ≤ r - m) hrp.le) (div_nonneg (by linarith : (0:ℝ) ≤ m - p) hrp.le)
    (by rw [← add_div, div_eq_one_iff_eq hrp.ne']; ring)
  have hm : ((r - m) / (r - p)) • p + ((m - p) / (r - p)) • r = m := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hm, smul_eq_mul, smul_eq_mul] at h
  have e : (r - p) * ((r - m) / (r - p) * G p + (m - p) / (r - p) * G r) =
      (r - m) * G p + (m - p) * G r := by
    field_simp
  have := mul_le_mul_of_nonneg_left h hrp.le
  linarith

lemma concaveOn_affine' {I : Set ℝ} (hI : Convex ℝ I) (A B : ℝ) :
    ConcaveOn ℝ I (fun x => A + B * x) := by
  refine ⟨hI, fun x _ y _ a b _ _ hab => ?_⟩
  simp only [smul_eq_mul]
  apply le_of_eq
  rw [show b = 1 - a by linarith]
  ring

lemma conc_nonpos_right {I : Set ℝ} {G : ℝ → ℝ} (hG : ConcaveOn ℝ I G) {p q x : ℝ}
    (hp : p ∈ I) (hx : x ∈ I) (hpq : p < q) (hqx : q < x) (h1 : G p = 0) (h2 : G q = 0) :
    G x ≤ 0 := by
  have := conc3 hG hp hx hpq hqx
  rw [h1, h2] at this
  nlinarith

lemma conc_nonpos_left {I : Set ℝ} {G : ℝ → ℝ} (hG : ConcaveOn ℝ I G) {p q x : ℝ}
    (hx : x ∈ I) (hq : q ∈ I) (hxp : x < p) (hpq : p < q) (h1 : G p = 0) (h2 : G q = 0) :
    G x ≤ 0 := by
  have := conc3 hG hx hq hxp hpq
  rw [h1, h2] at this
  nlinarith

lemma conc_nonneg_mid {I : Set ℝ} {G : ℝ → ℝ} (hG : ConcaveOn ℝ I G) {p q x : ℝ}
    (hp : p ∈ I) (hq : q ∈ I) (hpx : p < x) (hxq : x < q) (h1 : G p = 0) (h2 : G q = 0) :
    0 ≤ G x := by
  have := conc3 hG hp hq hpx hxq
  rw [h1, h2] at this
  nlinarith

/-- If a concave function has equal increments of step `h` at `p < q ≤ p + h`,
it is affine on `[p, q + h]`. -/
lemma flat_of_incr {g : ℝ → ℝ} {l r : ℝ} (hg : ConcaveOn ℝ (Set.Ioo l r) g) {p q h : ℝ}
    (hpq : p < q) (hqh : q ≤ p + h) (hlp : l < p) (hr : q + h < r)
    (hinc : g (p + h) - g p = g (q + h) - g q) :
    ∃ m : ℝ, ∀ x ∈ Set.Icc p (q + h), g x = g p + m * (x - p) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m * (q - p) = g q - g p :=
    ⟨(g q - g p) / (q - p), div_mul_cancel₀ _ (sub_pos.2 hpq).ne'⟩
  refine ⟨m, ?_⟩
  obtain ⟨G, hGx⟩ : ∃ G : ℝ → ℝ, ∀ x, G x = g x + ((m * p - g p) + (-m) * x) :=
    ⟨_, fun x => rfl⟩
  have hGe : G = g + fun x => (m * p - g p) + (-m) * x := funext fun x => hGx x
  have hG : ConcaveOn ℝ (Set.Ioo l r) G := by
    rw [hGe]; exact hg.add (concaveOn_affine' (convex_Ioo l r) _ _)
  have hh : 0 < h := by linarith
  have mem : ∀ x, p ≤ x → x ≤ q + h → x ∈ Set.Ioo l r := fun x h1 h2 =>
    ⟨by linarith, by linarith⟩
  have G0 : G p = 0 := by rw [hGx]; ring
  have G1 : G q = 0 := by rw [hGx]; linear_combination -hm
  have G23 : G (p + h) = G (q + h) := by rw [hGx, hGx]; linear_combination hinc + hm
  have G2 : G (p + h) = 0 := by
    rcases eq_or_lt_of_le hqh with e | hlt
    · rw [← e]; exact G1
    · have up := conc_nonpos_right hG (mem p le_rfl (by linarith))
        (mem _ (by linarith) (by linarith)) hpq hlt G0 G1
      have c3 := conc3 hG (mem q hpq.le (by linarith)) (mem _ (by linarith) le_rfl) hlt
        (by linarith : p + h < q + h)
      rw [G1, ← G23] at c3
      have lo : 0 ≤ G (p + h) := by nlinarith
      exact le_antisymm up lo
  have G3 : G (q + h) = 0 := G23 ▸ G2
  intro x ⟨hx1, hx2⟩
  have lo : 0 ≤ G x := by
    rcases eq_or_lt_of_le hx1 with e | h1
    · rw [← e, G0]
    rcases eq_or_lt_of_le hx2 with e | h2
    · rw [e, G3]
    exact conc_nonneg_mid hG (mem p le_rfl (by linarith)) (mem _ (by linarith) le_rfl) h1 h2 G0 G3
  have hi : G x ≤ 0 := by
    by_cases hxq : q < x
    · exact conc_nonpos_right hG (mem p le_rfl (by linarith)) (mem x hx1 hx2) hpq hxq G0 G1
    by_cases hxp : x < p + h
    · exact conc_nonpos_left hG (mem x hx1 hx2) (mem _ (by linarith) le_rfl) hxp
        (by linarith) G2 G3
    · have : x = q := by linarith
      rw [this, G1]
  have := le_antisymm hi lo
  rw [hGx] at this
  linear_combination this

/-- Equal increments of step `s` at `t` and `t + ρ` (`s ≤ ρ`) force equal consecutive
increments at `t` and `t + s`. -/
lemma step_eq {g : ℝ → ℝ} {l r : ℝ} (hg : ConcaveOn ℝ (Set.Ioo l r) g) {t s ρ : ℝ}
    (hs : 0 ≤ s) (hsρ : s ≤ ρ) (hl : l < t) (hr : t + ρ + s < r)
    (hinc : g (t + s) - g t = g (t + ρ + s) - g (t + ρ)) :
    g (t + s + s) - g (t + s) = g (t + s) - g t := by
  have hF := hg.neg
  have mem : ∀ x, t ≤ x → x ≤ t + ρ + s → x ∈ Set.Ioo l r := fun x h1 h2 =>
    ⟨by linarith, by linarith⟩
  have k1 := convex_incr_mono hF (u := t) (v := t + s) (h := s) (mem _ le_rfl (by linarith))
    (mem _ (by linarith) (by linarith)) (mem _ (by linarith) (by linarith))
    (mem _ (by linarith) (by linarith)) hs (by linarith)
  have k2 := convex_incr_mono hF (u := t + s) (v := t + ρ) (h := s)
    (mem _ (by linarith) (by linarith)) (mem _ (by linarith) (by linarith))
    (mem _ (by linarith) (by linarith)) (mem _ (by linarith) le_rfl) hs (by linarith)
  simp only [Pi.neg_apply] at k1 k2
  linarith

/-- A chord of the upper arc of horizontal span `2s` whose midpoint is on the arc. -/
lemma chord_mem (hS : SepConfig D X) {t s : ℝ} (hs : 0 ≤ s) (ht : |t| < wid D)
    (ht2 : |t + s + s| < wid D)
    (hmid : gUp D (t + s + s) - gUp D (t + s) = gUp D (t + s) - gUp D t) :
    pt2 s (gUp D (t + s) - gUp D t) ∈ D := by
  have hts : |t + s| < wid D := by
    rw [abs_lt] at *; constructor <;> linarith
  have unit : ∀ u, |u| < wid D → infDist (pt2 u (gUp D u)) D = 1 := fun u hu =>
    onUpper_unit hS ⟨by simpa using hu, by simp⟩
  have hmp : midpoint ℝ (pt2 t (gUp D t)) (pt2 (t + s + s) (gUp D (t + s + s))) =
      pt2 (t + s) (gUp D (t + s)) := by
    apply eq_of_coords
    · simp [midpoint_eq_smul_add]; ring
    · simp [midpoint_eq_smul_add]; linarith
  have := half_chord_mem hS.compact hS.convex ⟨0, hS.zero_mem⟩ hS.neg_mem (unit t ht)
    (unit _ ht2) (by rw [hmp]; exact unit _ hts)
  convert this using 1
  apply eq_of_coords
  · simp; ring
  · simp; linarith

/-! ### Two curves, two common points -/

theorem two_core (hS : SepConfig D X) {c c' p q : E} (hc : c ∈ X) (hc' : c' ∈ X)
    (hp : p ∈ X) (hq : q ∈ X) (hcc : c ≠ c') (hpq : p ≠ q)
    (h1 : OnUpper D (p - c)) (h2 : OnUpper D (q - c))
    (h3 : OnUpper D (p - c')) (h4 : OnUpper D (q - c')) (o1 : p 0 ≤ q 0)
    (o2 : c 0 ≤ c' 0) : False := by
  have hg := gUp_concaveOn hS
  simp only [OnUpper, PiLp.sub_apply] at h1 h2 h3 h4
  obtain ⟨b1, e1⟩ := h1
  obtain ⟨b2, e2⟩ := h2
  obtain ⟨b3, e3⟩ := h3
  obtain ⟨b4, e4⟩ := h4
  rw [abs_lt] at b1 b2 b3 b4
  obtain ⟨a, ha⟩ : ∃ a, a = p 0 - c' 0 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = c' 0 - c 0 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = q 0 - p 0 := ⟨_, rfl⟩
  have h0 : 0 ≤ h := by rw [hh]; linarith
  have d0 : 0 ≤ d := by rw [hd]; linarith
  have r1 : p 0 - c 0 = a + h := by rw [ha, hh]; ring
  have r2 : q 0 - c' 0 = a + d := by rw [ha, hd]; ring
  have r3 : q 0 - c 0 = a + d + h := by rw [ha, hd, hh]; ring
  rw [r1] at e1 b1
  rw [← ha] at e3 b3
  rw [r2] at e4 b4
  rw [r3] at e2 b2
  rcases le_total h d with hhd | hhd
  · have st := step_eq hg (t := a) (s := h) (ρ := d) h0 hhd (by linarith) (by linarith)
      (by linarith)
    have hm := chord_mem hS (t := a) (s := h) h0 (abs_lt.2 ⟨by linarith, by linarith⟩)
      (abs_lt.2 ⟨by linarith, by linarith⟩) st
    apply hS.sep c hc c' hc' hcc
    convert hm using 1
    apply eq_of_coords
    · simp [hh]
    · simp; linarith
  · have e2' : gUp D (a + h + d) = q 1 - c 1 := by
      rw [show a + h + d = a + d + h by ring]; linarith
    have st := step_eq hg (t := a) (s := d) (ρ := h) d0 hhd (by linarith) (by linarith)
      (by linarith)
    have hm := chord_mem hS (t := a) (s := d) d0 (abs_lt.2 ⟨by linarith, by linarith⟩)
      (abs_lt.2 ⟨by linarith, by linarith⟩) st
    apply hS.sep p hp q hq hpq
    convert hm using 1
    apply eq_of_coords
    · simp [hd]
    · simp; linarith

theorem no_two_common_points (hS : SepConfig D X) {c c' p q : E} (hc : c ∈ X) (hc' : c' ∈ X)
    (hp : p ∈ X) (hq : q ∈ X) (hcc : c ≠ c') (hpq : p ≠ q)
    (h1 : OnUpper D (p - c)) (h2 : OnUpper D (q - c))
    (h3 : OnUpper D (p - c')) (h4 : OnUpper D (q - c')) : False := by
  rcases le_total (p 0) (q 0) with o1 | o1 <;> rcases le_total (c 0) (c' 0) with o2 | o2
  · exact two_core hS hc hc' hp hq hcc hpq h1 h2 h3 h4 o1 o2
  · exact two_core hS hc' hc hp hq hcc.symm hpq h3 h4 h1 h2 o1 o2
  · exact two_core hS hc hc' hq hp hcc hpq.symm h2 h1 h4 h3 o1 o2
  · exact two_core hS hc' hc hq hp hcc.symm hpq.symm h4 h3 h2 h1 o1 o2

/-! ### Three curves coinciding on an interval -/

theorem three_core (hS : SepConfig D X) {c c' c'' : E} (hc : c ∈ X) (hc' : c' ∈ X)
    (hc'' : c'' ∈ X) (h12 : c ≠ c') (h23 : c' ≠ c'') (o1 : c 0 < c' 0) (o2 : c' 0 < c'' 0)
    {α β : ℝ} (hαβ : α < β)
    (w1 : ∀ x ∈ Set.Icc α β, |x - c 0| < wid D) (w2 : ∀ x ∈ Set.Icc α β, |x - c' 0| < wid D)
    (w3 : ∀ x ∈ Set.Icc α β, |x - c'' 0| < wid D)
    (e1 : ∀ x ∈ Set.Icc α β, curve D c x = curve D c' x)
    (e2 : ∀ x ∈ Set.Icc α β, curve D c' x = curve D c'' x) : False := by
  have hg := gUp_concaveOn hS
  obtain ⟨a, ha⟩ : ∃ a, a = α - c'' 0 := ⟨_, rfl⟩
  obtain ⟨h1, hh1⟩ : ∃ h1, h1 = c' 0 - c 0 := ⟨_, rfl⟩
  obtain ⟨h2, hh2⟩ : ∃ h2, h2 = c'' 0 - c' 0 := ⟨_, rfl⟩
  have h1p : 0 < h1 := by rw [hh1]; linarith
  have h2p : 0 < h2 := by rw [hh2]; linarith
  obtain ⟨ε, hε0, hεL, hεh⟩ : ∃ ε, 0 < ε ∧ ε ≤ β - α ∧ ε ≤ h2 :=
    ⟨min (β - α) h2, lt_min (by linarith) h2p, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ε', hε0', hεL', hεh'⟩ : ∃ ε, 0 < ε ∧ ε ≤ β - α ∧ ε ≤ h1 :=
    ⟨min (β - α) h1, lt_min (by linarith) h1p, min_le_left _ _, min_le_right _ _⟩
  have hα : α ∈ Set.Icc α β := ⟨le_rfl, hαβ.le⟩
  have hαε : α + ε ∈ Set.Icc α β := ⟨by linarith, by linarith⟩
  have hαε' : α + ε' ∈ Set.Icc α β := ⟨by linarith, by linarith⟩
  have E1 : ∀ x ∈ Set.Icc α β, gUp D (x - c 0) - gUp D (x - c' 0) = c' 1 - c 1 :=
    fun x hx => by have := e1 x hx; simp only [curve] at this; linarith
  have E2 : ∀ x ∈ Set.Icc α β, gUp D (x - c' 0) - gUp D (x - c'' 0) = c'' 1 - c' 1 :=
    fun x hx => by have := e2 x hx; simp only [curve] at this; linarith
  -- values at `α`
  have E1α := E1 α hα
  have E2α := E2 α hα
  rw [show α - c 0 = a + h2 + h1 by rw [ha, hh1, hh2]; ring,
    show α - c' 0 = a + h2 by rw [ha, hh2]; ring] at E1α
  rw [show α - c' 0 = a + h2 by rw [ha, hh2]; ring, ← ha] at E2α
  have E1ε := E1 _ hαε'
  rw [show α + ε' - c 0 = a + h2 + ε' + h1 by rw [ha, hh1, hh2]; ring,
    show α + ε' - c' 0 = a + h2 + ε' by rw [ha, hh2]; ring] at E1ε
  have E2ε := E2 _ hαε
  rw [show α + ε - c' 0 = a + ε + h2 by rw [ha, hh2]; ring,
    show α + ε - c'' 0 = a + ε by rw [ha]; ring] at E2ε
  -- bounds
  have lA : -wid D < a := by have := (abs_lt.mp (w3 α hα)).1; rw [← ha] at this; exact this
  have rA : a + h1 + h2 < wid D := by
    have := (abs_lt.mp (w1 α hα)).2
    rw [show α - c 0 = a + h1 + h2 by rw [ha, hh1, hh2]; ring] at this; exact this
  have lB : -wid D < a + h2 := by
    have := (abs_lt.mp (w2 α hα)).1
    rw [show α - c' 0 = a + h2 by rw [ha, hh2]; ring] at this; exact this
  have rB : a + ε + h2 < wid D := by
    have := (abs_lt.mp (w2 _ hαε)).2
    rw [show α + ε - c' 0 = a + ε + h2 by rw [ha, hh2]; ring] at this; exact this
  have rC : a + h2 + ε' + h1 < wid D := by
    have := (abs_lt.mp (w1 _ hαε')).2
    rw [show α + ε' - c 0 = a + h2 + ε' + h1 by rw [ha, hh1, hh2]; ring] at this; exact this
  -- two flat pieces
  obtain ⟨m1, F1⟩ := flat_of_incr hg (p := a) (q := a + ε) (h := h2) (by linarith)
    (by linarith) lA rB (by linarith)
  obtain ⟨m2, F2⟩ := flat_of_incr hg (p := a + h2) (q := a + h2 + ε') (h := h1) (by linarith)
    (by linarith) lB rC (by linarith)
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ ε' :=
    ⟨min ε ε', lt_min hε0 hε0', min_le_left _ _, min_le_right _ _⟩
  have A1 := F1 (a + h2) ⟨by linarith, by linarith⟩
  have A2 := F1 (a + h2 + δ) ⟨by linarith, by linarith⟩
  have A3 := F2 (a + h2 + δ) ⟨by linarith, by linarith⟩
  have hmm : (m1 - m2) * δ = 0 := by linear_combination A3 - A2 + A1
  have hm12 : m1 = m2 := by
    rcases mul_eq_zero.mp hmm with h | h
    · linarith
    · linarith
  have aff : ∀ x ∈ Set.Icc a (a + h1 + h2), gUp D x = gUp D a + m1 * (x - a) := by
    intro x ⟨hx1, hx2⟩
    by_cases hx : x ≤ a + ε + h2
    · exact F1 x ⟨hx1, hx⟩
    · have := F2 x ⟨by linarith, by linarith⟩
      rw [← hm12] at this
      linear_combination this + A1
  have hch : ∀ t s, a ≤ t → 0 ≤ s → t + s + s ≤ a + h1 + h2 → pt2 s (m1 * s) ∈ D := by
    intro t s ht hs hts
    have Ht := aff t ⟨ht, by linarith⟩
    have Hts := aff (t + s) ⟨by linarith, by linarith⟩
    have Htss := aff (t + s + s) ⟨by linarith, by linarith⟩
    have := chord_mem hS (t := t) (s := s) hs (abs_lt.2 ⟨by linarith, by linarith⟩)
      (abs_lt.2 ⟨by linarith, by linarith⟩)
      (by linear_combination Htss - 2 * Hts + Ht)
    rwa [show gUp D (t + s) - gUp D t = m1 * s by linear_combination Hts - Ht] at this
  rcases le_total h2 h1 with hh | hh
  · have := hch a h2 le_rfl h2p.le (by linarith)
    apply hS.sep c' hc' c'' hc'' h23
    convert this using 1
    apply eq_of_coords
    · simp [hh2]
    · simp only [PiLp.sub_apply, pt2_one]
      linear_combination A1 - E2α
  · have := hch (a + h2 - h1) h1 (by linarith) h1p.le (by linarith)
    have B := aff (a + h2 + h1) ⟨by linarith, by linarith⟩
    apply hS.sep c hc c' hc' h12
    convert this using 1
    apply eq_of_coords
    · simp [hh1]
    · simp only [PiLp.sub_apply, pt2_one]
      linear_combination B - A1 - E1α

theorem no_three_coincident (hS : SepConfig D X) {c c' c'' : E} (hc : c ∈ X) (hc' : c' ∈ X)
    (hc'' : c'' ∈ X) (h12 : c ≠ c') (h13 : c ≠ c'') (h23 : c' ≠ c'') {α β : ℝ} (hαβ : α < β)
    (h : ∀ x ∈ Set.Icc α β, |x - c 0| < wid D ∧ |x - c' 0| < wid D ∧ |x - c'' 0| < wid D ∧
      curve D c x = curve D c' x ∧ curve D c x = curve D c'' x) : False := by
  have w1 : ∀ x ∈ Set.Icc α β, |x - c 0| < wid D := fun x hx => (h x hx).1
  have w2 : ∀ x ∈ Set.Icc α β, |x - c' 0| < wid D := fun x hx => (h x hx).2.1
  have w3 : ∀ x ∈ Set.Icc α β, |x - c'' 0| < wid D := fun x hx => (h x hx).2.2.1
  have e12 : ∀ x ∈ Set.Icc α β, curve D c x = curve D c' x := fun x hx => (h x hx).2.2.2.1
  have e13 : ∀ x ∈ Set.Icc α β, curve D c x = curve D c'' x := fun x hx => (h x hx).2.2.2.2
  have e21 : ∀ x ∈ Set.Icc α β, curve D c' x = curve D c x := fun x hx => (e12 x hx).symm
  have e31 : ∀ x ∈ Set.Icc α β, curve D c'' x = curve D c x := fun x hx => (e13 x hx).symm
  have e23 : ∀ x ∈ Set.Icc α β, curve D c' x = curve D c'' x :=
    fun x hx => (e12 x hx).symm.trans (e13 x hx)
  have e32 : ∀ x ∈ Set.Icc α β, curve D c'' x = curve D c' x := fun x hx => (e23 x hx).symm
  have hα : α ∈ Set.Icc α β := ⟨le_rfl, hαβ.le⟩
  have d0 : ∀ {y y' : E}, y ≠ y' → curve D y α = curve D y' α → y 0 ≠ y' 0 := by
    intro y y' hne he h0
    apply hne
    simp only [curve] at he
    rw [h0] at he
    exact eq_of_coords h0 (by linarith)
  have n12 := d0 h12 (e12 α hα)
  have n13 := d0 h13 (e13 α hα)
  have n23 := d0 h23 (e23 α hα)
  rcases lt_or_gt_of_ne n12 with a12 | a12 <;> rcases lt_or_gt_of_ne n13 with a13 | a13 <;>
    rcases lt_or_gt_of_ne n23 with a23 | a23
  · exact three_core hS hc hc' hc'' h12 h23 a12 a23 hαβ w1 w2 w3 e12 e23
  · exact three_core hS hc hc'' hc' h13 h23.symm a13 a23 hαβ w1 w3 w2 e13 e32
  · linarith
  · exact three_core hS hc'' hc hc' h13.symm h12 a13 a12 hαβ w3 w1 w2 e31 e12
  · exact three_core hS hc' hc hc'' h12.symm h13 a12 a13 hαβ w2 w1 w3 e21 e13
  · linarith
  · exact three_core hS hc' hc'' hc h23 h13.symm a23 a13 hαβ w2 w3 w1 e23 e31
  · exact three_core hS hc'' hc' hc h23.symm h12.symm a23 a12 hαβ w3 w2 w1 e32 e21

end Erdos956Upper
