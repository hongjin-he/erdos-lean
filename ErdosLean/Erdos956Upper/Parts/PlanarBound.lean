import ErdosLean.Erdos956Upper.Parts.ArcOrder

/-!
# Erdős #956 upper bound — P11: non-crossing x-monotone drawings have at most 4v edges

Combinatorial replacement of Euler's formula (no Jordan curve theorem): at a vertex `u` with
right-going arcs ordered from bottom to top, every arc `b` that is not the topmost one has an
immediate upper neighbour `a` (its *successor*).  The *wedge* `(b, a)` is closed by the vertex `z`
of smallest abscissa in the closed region between `b` and `a` (to the right of `u`, up to the
first right end among `a`, `b`).  Nothing lies strictly between `b` and `a` to the left of `z`
(*adjacency*), and from this one shows that `b ↦ (z, [z = right end of a])` is injective.
Topmost arcs are determined by their left endpoint.  Hence `e ≤ 2v + v = 3v ≤ 4v`.
-/

namespace Erdos956Upper

open Erdos956 Metric Filter Topology

lemma pb_cwa_Ici {f : ℝ → ℝ} {l r p : ℝ} (hf : ContinuousOn f (Set.Icc l r)) (hlp : l ≤ p)
    (hpr : p < r) : ContinuousWithinAt f (Set.Ici p) p :=
  (hf p ⟨hlp, hpr.le⟩).mono_of_mem_nhdsWithin
    (Filter.mem_of_superset (Icc_mem_nhdsGE hpr) (Set.Icc_subset_Icc_left hlp))

lemma pb_cwa_Iic {f : ℝ → ℝ} {l r p : ℝ} (hf : ContinuousOn f (Set.Icc l r)) (hlp : l < p)
    (hpr : p ≤ r) : ContinuousWithinAt f (Set.Iic p) p :=
  (hf p ⟨hlp.le, hpr⟩).mono_of_mem_nhdsWithin
    (Filter.mem_of_superset (Icc_mem_nhdsLE hlp) (Set.Icc_subset_Icc_right hpr))

lemma pb_exists_right {g h : ℝ → ℝ} {p x : ℝ} (hg : ContinuousWithinAt g (Set.Ici p) p)
    (hh : ContinuousWithinAt h (Set.Ici p) p) (hlt : g p < h p) (hpx : p < x) :
    ∃ y, p < y ∧ y < x ∧ g y < h y := by
  have h1 : ∀ᶠ y in 𝓝[≥] p, g y < h y := Filter.Tendsto.eventually_lt hg hh hlt
  have h2 : ∀ᶠ y in 𝓝[>] p, g y < h y :=
    h1.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have h3 : ∀ᶠ y in 𝓝[>] p, y ∈ Set.Ioo p x := Ioo_mem_nhdsGT hpx
  obtain ⟨y, hy, hy'⟩ := (h2.and h3).exists
  exact ⟨y, hy'.1, hy'.2, hy⟩

lemma pb_exists_left {g h : ℝ → ℝ} {q x : ℝ} (hg : ContinuousWithinAt g (Set.Iic q) q)
    (hh : ContinuousWithinAt h (Set.Iic q) q) (hlt : g q < h q) (hxq : x < q) :
    ∃ y, x < y ∧ y < q ∧ g y < h y := by
  have h1 : ∀ᶠ y in 𝓝[≤] q, g y < h y := Filter.Tendsto.eventually_lt hg hh hlt
  have h2 : ∀ᶠ y in 𝓝[<] q, g y < h y :=
    h1.filter_mono (nhdsWithin_mono _ Set.Iio_subset_Iic_self)
  have h3 : ∀ᶠ y in 𝓝[<] q, y ∈ Set.Ioo x q := Ioo_mem_nhdsLT hxq
  obtain ⟨y, hy, hy'⟩ := (h2.and h3).exists
  exact ⟨y, hy'.1, hy'.2, hy⟩

lemma pb_E_ext {z w : E} (h0 : z 0 = w 0) (h1 : z 1 = w 1) : z = w := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma pb_left_zero (a : Arc) : a.left 0 = a.l := rfl

theorem planar_bound {ι : Type*} (V : Finset E) (A : Finset ι) (arc : ι → Arc)
    (hvalid : ∀ i ∈ A, (arc i).Valid)
    (hend : ∀ i ∈ A, (arc i).left ∈ V ∧ (arc i).right ∈ V)
    (havoid : ∀ i ∈ A, ∀ z ∈ V, (arc i).Avoids z)
    (hsimple : ∀ i ∈ A, ∀ j ∈ A, (arc i).left = (arc j).left →
      (arc i).right = (arc j).right → i = j)
    (hnc : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ (arc i).Crosses (arc j)) :
    A.card ≤ 4 * V.card := by
  classical
  -- order tools
  have ord : ∀ i ∈ A, ∀ j ∈ A, ∀ x y : ℝ, x ∈ Set.Ioo (arc i).l (arc i).r →
      x ∈ Set.Ioo (arc j).l (arc j).r → y ∈ Set.Ioo (arc i).l (arc i).r →
      y ∈ Set.Ioo (arc j).l (arc j).r → (arc i).f x < (arc j).f x → (arc i).f y < (arc j).f y := by
    intro i hi j hj x y hxi hxj hyi hyj hlt
    by_cases hij : i = j
    · subst hij; exact absurd hlt (lt_irrefl _)
    · exact Arc.lt_of_lt_of_not_crosses (hvalid i hi) (hvalid j hj) (hnc i hi j hj hij)
        hxi hxj hyi hyj hlt
  have sep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ x, x ∈ Set.Ioo (arc i).l (arc i).r →
      x ∈ Set.Ioo (arc j).l (arc j).r → (arc i).f x < (arc j).f x ∨ (arc j).f x < (arc i).f x := by
    intro i hi j hj hij x hxi hxj
    exact lt_or_gt_of_ne (fun h => hnc i hi j hj hij ⟨x, hxi, hxj, h⟩)
  have leq : ∀ i j, (arc i).left = (arc j).left →
      (arc i).l = (arc j).l ∧ (arc i).f (arc j).l = (arc j).f (arc j).l := by
    intro i j h
    have h0 : (arc i).l = (arc j).l := congrArg (fun p : E => p 0) h
    have h1 : (arc i).f (arc i).l = (arc j).f (arc j).l := congrArg (fun p : E => p 1) h
    refine ⟨h0, ?_⟩
    calc (arc i).f (arc j).l = (arc i).f (arc i).l := by rw [h0]
      _ = _ := h1
  -- a common abscissa just right of each vertex
  have hxs0 : ∀ u : E, ∃ x : ℝ, ∀ j ∈ A, (arc j).left = u → x ∈ Set.Ioo (arc j).l (arc j).r := by
    intro u
    by_cases hne : (A.filter fun j => (arc j).left = u).Nonempty
    · obtain ⟨j0, hj0, hmin⟩ := (A.filter fun j => (arc j).left = u).exists_min_image
        (fun j => (arc j).r) hne
      obtain ⟨hj0A, hj0u⟩ := Finset.mem_filter.1 hj0
      refine ⟨(u 0 + (arc j0).r) / 2, fun j hj hju => ?_⟩
      have hl : (arc j).l = u 0 := congrArg (fun p : E => p 0) hju
      have hl0 : (arc j0).l = u 0 := congrArg (fun p : E => p 0) hj0u
      have h1 := (hvalid j0 hj0A).1
      have h2 := (hvalid j hj).1
      have h3 : (arc j0).r ≤ (arc j).r := hmin j (Finset.mem_filter.2 ⟨hj, hju⟩)
      constructor <;> linarith
    · exact ⟨0, fun j hj hju => absurd ⟨j, Finset.mem_filter.2 ⟨hj, hju⟩⟩ hne⟩
  choose xs hxs using hxs0
  have hxsb : ∀ b ∈ A, xs (arc b).left ∈ Set.Ioo (arc b).l (arc b).r :=
    fun b hb => hxs _ b hb rfl
  -- `Up b j`: `j` starts at the left end of `b` and lies above `b`
  obtain ⟨Up, hUp⟩ : ∃ P : ι → ι → Prop, ∀ b j, P b j ↔ (j ∈ A ∧ (arc j).left = (arc b).left ∧
      (arc b).f (xs (arc b).left) < (arc j).f (xs (arc b).left)) := ⟨_, fun _ _ => Iff.rfl⟩
  -- the successor (immediate upper neighbour)
  have hsucc0 : ∀ b, ∃ a, (∃ j, Up b j) → Up b a ∧
      ∀ c, Up b c → (arc a).f (xs (arc b).left) ≤ (arc c).f (xs (arc b).left) := by
    intro b
    by_cases h : ∃ j, Up b j
    · obtain ⟨j, hj⟩ := h
      have hne : (A.filter (Up b)).Nonempty :=
        ⟨j, Finset.mem_filter.2 ⟨((hUp b j).1 hj).1, hj⟩⟩
      obtain ⟨a, ha, hmin⟩ := (A.filter (Up b)).exists_min_image
        (fun c => (arc c).f (xs (arc b).left)) hne
      exact ⟨a, fun _ => ⟨(Finset.mem_filter.1 ha).2,
        fun c hc => hmin c (Finset.mem_filter.2 ⟨((hUp b c).1 hc).1, hc⟩)⟩⟩
    · exact ⟨b, fun h' => absurd h' h⟩
  choose sc hsc using hsucc0
  have basic : ∀ b ∈ A, (∃ j, Up b j) →
      sc b ∈ A ∧ sc b ≠ b ∧ (arc (sc b)).l = (arc b).l ∧
      (arc (sc b)).f (arc b).l = (arc b).f (arc b).l ∧
      (arc b).l < (arc b).r ∧ (arc b).l < (arc (sc b)).r := by
    intro b hb hT
    obtain ⟨haA, hal, hlt⟩ := (hUp b (sc b)).1 (hsc b hT).1
    obtain ⟨h0, h1⟩ := leq _ _ hal
    refine ⟨haA, ?_, h0, h1, (hvalid b hb).1, ?_⟩
    · intro h; rw [h] at hlt; exact lt_irrefl _ hlt
    · rw [← h0]; exact (hvalid _ haA).1
  have hscleft : ∀ b, (∃ j, Up b j) → (arc (sc b)).left = (arc b).left :=
    fun b hT => ((hUp b (sc b)).1 (hsc b hT).1).2.1
  have hxsa : ∀ b, (∃ j, Up b j) → xs (arc b).left ∈ Set.Ioo (arc (sc b)).l (arc (sc b)).r :=
    fun b hT => hxs _ _ ((hUp b (sc b)).1 (hsc b hT).1).1 (hscleft b hT)
  have hxsab : ∀ b, (∃ j, Up b j) →
      (arc b).f (xs (arc b).left) < (arc (sc b)).f (xs (arc b).left) :=
    fun b hT => ((hUp b (sc b)).1 (hsc b hT).1).2.2
  -- `b` stays weakly below its successor
  have hbelow : ∀ b ∈ A, (∃ j, Up b j) → ∀ x, (arc b).l < x → x ≤ (arc b).r →
      x ≤ (arc (sc b)).r → (arc b).f x ≤ (arc (sc b)).f x := by
    intro b hb hT x h1 h2 h3
    obtain ⟨haA, -, hal, -, -, -⟩ := basic b hb hT
    by_contra hh
    rw [not_le] at hh
    obtain ⟨y, hy1, hy2, hy3⟩ := pb_exists_left
      (pb_cwa_Iic (hvalid _ haA).2 (by rw [hal]; exact h1) h3)
      (pb_cwa_Iic (hvalid b hb).2 h1 h2) hh h1
    have := ord b hb _ haA _ y (hxsb b hb) (hxsa b hT) ⟨hy1, by linarith⟩
      ⟨by linarith, by linarith⟩ (hxsab b hT)
    linarith
  -- the closing vertex of the wedge
  have hz0 : ∀ b, ∃ z : E, (b ∈ A ∧ ∃ j, Up b j) → z ∈ V ∧ (arc b).l < z 0 ∧
      z 0 ≤ (arc b).r ∧ z 0 ≤ (arc (sc b)).r ∧ (arc b).f (z 0) ≤ z 1 ∧
      z 1 ≤ (arc (sc b)).f (z 0) ∧
      ∀ w ∈ V, (arc b).l < w 0 → w 0 ≤ (arc b).r → w 0 ≤ (arc (sc b)).r →
        (arc b).f (w 0) ≤ w 1 → w 1 ≤ (arc (sc b)).f (w 0) → z 0 ≤ w 0 := by
    intro b
    by_cases hbT : b ∈ A ∧ ∃ j, Up b j
    · obtain ⟨hb, hT⟩ := hbT
      obtain ⟨haA, -, hal, -, hbl, hal'⟩ := basic b hb hT
      have hne : (V.filter (fun w : E => (arc b).l < w 0 ∧ w 0 ≤ (arc b).r ∧
          w 0 ≤ (arc (sc b)).r ∧ (arc b).f (w 0) ≤ w 1 ∧ w 1 ≤ (arc (sc b)).f (w 0))).Nonempty := by
        rcases le_total (arc b).r (arc (sc b)).r with hr | hr
        · refine ⟨(arc b).right, Finset.mem_filter.2 ⟨(hend b hb).2, hbl, le_rfl, hr, le_rfl, ?_⟩⟩
          exact hbelow b hb hT (arc b).r hbl le_rfl hr
        · refine ⟨(arc (sc b)).right,
            Finset.mem_filter.2 ⟨(hend _ haA).2, hal', hr, le_rfl, ?_, le_rfl⟩⟩
          exact hbelow b hb hT (arc (sc b)).r hal' hr le_rfl
      obtain ⟨z, hzR, hzmin⟩ := Finset.exists_min_image _ (fun w : E => w 0) hne
      obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5⟩ := Finset.mem_filter.1 hzR
      exact ⟨z, fun _ => ⟨hzV, hz1, hz2, hz3, hz4, hz5,
        fun w hw h1 h2 h3 h4 h5 => hzmin w (Finset.mem_filter.2 ⟨hw, h1, h2, h3, h4, h5⟩)⟩⟩
    · exact ⟨0, fun h => absurd h hbT⟩
  choose z hz using hz0
  -- adjacency: nothing lies strictly between `b` and its successor left of `z b`
  have hadj : ∀ b ∈ A, (∃ j, Up b j) → ∀ c ∈ A, ∀ x, (arc b).l < x → x < z b 0 →
      x ∈ Set.Ioo (arc c).l (arc c).r → (arc b).f x < (arc c).f x →
      (arc c).f x < (arc (sc b)).f x → False := by
    intro b hb hT c hc x hbx hxz hxc h1 h2
    obtain ⟨haA, -, hal, haf, hbl, hal'⟩ := basic b hb hT
    obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5, hzmin⟩ := hz b ⟨hb, hT⟩
    have hxb : x ∈ Set.Ioo (arc b).l (arc b).r := ⟨hbx, by linarith⟩
    have hxa : x ∈ Set.Ioo (arc (sc b)).l (arc (sc b)).r := ⟨by linarith, by linarith⟩
    have hcr := (hvalid c hc).1
    have hxc1 := hxc.1
    have hxc2 := hxc.2
    have hxb2 := hxb.2
    have hxa2 := hxa.2
    rcases lt_or_ge (arc b).l (arc c).l with hcl | hcl
    · have hA : (arc b).f (arc c).l ≤ (arc c).f (arc c).l := by
        by_contra hh
        rw [not_le] at hh
        obtain ⟨y, hy1, hy2, hy3⟩ := pb_exists_right (pb_cwa_Ici (hvalid c hc).2 le_rfl hcr)
          (pb_cwa_Ici (hvalid b hb).2 hcl.le (by linarith)) hh hxc1
        have := ord c hc b hb y x ⟨hy1, by linarith⟩ ⟨by linarith, by linarith⟩ hxc hxb hy3
        linarith
      have hB : (arc c).f (arc c).l ≤ (arc (sc b)).f (arc c).l := by
        by_contra hh
        rw [not_le] at hh
        obtain ⟨y, hy1, hy2, hy3⟩ := pb_exists_right
          (pb_cwa_Ici (hvalid _ haA).2 (by linarith) (by linarith))
          (pb_cwa_Ici (hvalid c hc).2 le_rfl hcr) hh hxc1
        have := ord _ haA c hc y x ⟨by linarith, by linarith⟩ ⟨hy1, by linarith⟩ hxa hxc hy3
        linarith
      have hm : z b 0 ≤ (arc c).l := hzmin (arc c).left (hend c hc).1 hcl
        (by rw [pb_left_zero]; linarith) (by rw [pb_left_zero]; linarith) hA hB
      linarith
    · have hcu : (arc b).l < (arc c).r := hbx.trans hxc2
      rcases lt_trichotomy ((arc c).f (arc b).l) ((arc b).f (arc b).l) with hlt | heq | hgt
      · obtain ⟨y, hy1, hy2, hy3⟩ := pb_exists_right (pb_cwa_Ici (hvalid c hc).2 hcl hcu)
          (pb_cwa_Ici (hvalid b hb).2 le_rfl hbl) hlt hbx
        have := ord c hc b hb y x ⟨by linarith, by linarith⟩ ⟨hy1, by linarith⟩ hxc hxb hy3
        linarith
      · rcases lt_or_eq_of_le hcl with hcl' | hcl'
        · exact havoid c hc _ (hend b hb).1 ⟨⟨hcl', hcu⟩, heq.symm⟩
        · have hcleft : (arc c).left = (arc b).left := by
            apply pb_E_ext hcl'
            show (arc c).f (arc c).l = (arc b).f (arc b).l
            rw [hcl']
            exact heq
          have hxsc := hxs _ c hc hcleft
          have hup : Up b c :=
            (hUp b c).2 ⟨hc, hcleft, ord b hb c hc x _ hxb hxc (hxsb b hb) hxsc h1⟩
          have hle := (hsc b hT).2 c hup
          have := ord c hc (sc b) haA x _ hxc hxa hxsc (hxsa b hT) h2
          linarith
      · have hgt' : (arc (sc b)).f (arc b).l < (arc c).f (arc b).l := by rw [haf]; exact hgt
        obtain ⟨y, hy1, hy2, hy3⟩ := pb_exists_right
          (pb_cwa_Ici (hvalid _ haA).2 hal.le hal') (pb_cwa_Ici (hvalid c hc).2 hcl hcu) hgt' hbx
        have := ord _ haA c hc y x ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hxa hxc hy3
        linarith
  -- an arc ending near `z b` cannot lie above `b` there (unless above the successor)
  have hLB : ∀ b ∈ A, (∃ j, Up b j) → ∀ c ∈ A, (arc c).l < z b 0 → z b 0 ≤ (arc c).r →
      (arc c).f (z b 0) < (arc (sc b)).f (z b 0) → ∀ y, (arc b).l < y → (arc c).l < y →
      y < z b 0 → (arc b).f y < (arc c).f y → False := by
    intro b hb hT c hc hcz hzc hlt y hby hcy hyz hbc
    obtain ⟨haA, -, hal, haf, hbl, hal'⟩ := basic b hb hT
    obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5, hzmin⟩ := hz b ⟨hb, hT⟩
    obtain ⟨y', hy1, hy2, hy3⟩ := pb_exists_left (pb_cwa_Iic (hvalid c hc).2 hcz hzc)
      (pb_cwa_Iic (hvalid _ haA).2 (by linarith) hz3) hlt hyz
    have := ord b hb c hc y y' ⟨hby, by linarith⟩ ⟨hcy, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ hbc
    exact hadj b hb hT c hc y' (by linarith) hy2 ⟨by linarith, by linarith⟩ this hy3
  have hLA : ∀ b ∈ A, (∃ j, Up b j) → ∀ c ∈ A, (arc c).l < z b 0 → z b 0 ≤ (arc c).r →
      (arc b).f (z b 0) < (arc c).f (z b 0) → ∀ y, (arc b).l < y → (arc c).l < y →
      y < z b 0 → (arc c).f y < (arc (sc b)).f y → False := by
    intro b hb hT c hc hcz hzc hlt y hby hcy hyz hca
    obtain ⟨haA, -, hal, haf, hbl, hal'⟩ := basic b hb hT
    obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5, hzmin⟩ := hz b ⟨hb, hT⟩
    obtain ⟨y', hy1, hy2, hy3⟩ := pb_exists_left (pb_cwa_Iic (hvalid b hb).2 hz1 hz2)
      (pb_cwa_Iic (hvalid c hc).2 hcz hzc) hlt hyz
    have := ord c hc _ haA y y' ⟨hcy, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hca
    exact hadj b hb hT c hc y' (by linarith) hy2 ⟨by linarith, by linarith⟩ hy3 this
  -- position of `z b`
  have hzA : ∀ b ∈ A, (∃ j, Up b j) → z b ≠ (arc (sc b)).right →
      z b 1 < (arc (sc b)).f (z b 0) := by
    intro b hb hT hne
    obtain ⟨haA, -, hal, haf, hbl, hal'⟩ := basic b hb hT
    obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5, hzmin⟩ := hz b ⟨hb, hT⟩
    rcases lt_or_eq_of_le hz5 with h | h
    · exact h
    · exfalso
      rcases lt_or_eq_of_le hz3 with h' | h'
      · exact havoid _ haA _ hzV ⟨⟨by linarith, h'⟩, h⟩
      · apply hne
        apply pb_E_ext h'
        show z b 1 = (arc (sc b)).f (arc (sc b)).r
        rw [h, h']
  have hzB : ∀ b ∈ A, (∃ j, Up b j) → z b ≠ (arc b).right →
      (arc b).f (z b 0) < z b 1 := by
    intro b hb hT hne
    obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5, hzmin⟩ := hz b ⟨hb, hT⟩
    rcases lt_or_eq_of_le hz4 with h | h
    · exact h
    · exfalso
      rcases lt_or_eq_of_le hz2 with h' | h'
      · exact havoid b hb _ hzV ⟨⟨hz1, h'⟩, h.symm⟩
      · apply hne
        apply pb_E_ext h'
        show z b 1 = (arc b).f (arc b).r
        rw [← h, h']
  have hzAB : ∀ b ∈ A, (∃ j, Up b j) → z b = (arc (sc b)).right → z b ≠ (arc b).right := by
    intro b hb hT h1 h2
    obtain ⟨haA, hne, -⟩ := basic b hb hT
    exact hne (hsimple _ haA b hb (hscleft b hT) (h1.symm.trans h2))
  -- counting
  have hcard := Finset.card_filter_add_card_filter_not (s := A) (fun b => ∃ j, Up b j)
  have hTc : (A.filter fun b => ∃ j, Up b j).card ≤ (V ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun b => (z b, decide (z b = (arc (sc b)).right)))
    · intro b hb
      obtain ⟨hbA, hT⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨(hz b ⟨hbA, hT⟩).1, Finset.mem_univ _⟩)
    · intro b hb b' hb' heq
      obtain ⟨hbA, hT⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      obtain ⟨hbA', hT'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb')
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hzz, hdec⟩ := heq
      have hiff := decide_eq_decide.1 hdec
      obtain ⟨haA, -, hal, haf, hbl, hal'⟩ := basic b hbA hT
      obtain ⟨haA', -, hal2, haf2, hbl2, hal2'⟩ := basic b' hbA' hT'
      obtain ⟨hzV, hz1, hz2, hz3, hz4, hz5, -⟩ := hz b ⟨hbA, hT⟩
      obtain ⟨hzV', hz1', hz2', hz3', hz4', hz5', -⟩ := hz b' ⟨hbA', hT'⟩
      have e0 : z b' 0 = z b 0 := by rw [hzz]
      have e1 : z b' 1 = z b 1 := by rw [hzz]
      rw [e0, e1] at hz4' hz5'
      rw [e0] at hz1' hz2' hz3'
      by_cases hAr : z b = (arc (sc b)).right
      · have hAr' : z b' = (arc (sc b')).right := hiff.1 hAr
        have f0 : z b 0 = (arc (sc b)).r := congrArg (fun p : E => p 0) hAr
        have f1 : z b 1 = (arc (sc b)).f (arc (sc b)).r := congrArg (fun p : E => p 1) hAr
        have f0' : z b' 0 = (arc (sc b')).r := congrArg (fun p : E => p 0) hAr'
        have f1' : z b' 1 = (arc (sc b')).f (arc (sc b')).r := congrArg (fun p : E => p 1) hAr'
        rw [e0] at f0'
        rw [e1] at f1'
        have g1 : (arc (sc b)).f (z b 0) = z b 1 := by rw [f1, f0]
        have g1' : (arc (sc b')).f (z b 0) = z b 1 := by rw [f1', f0']
        have hB1 := hzB b hbA hT (hzAB b hbA hT hAr)
        have hB1' := hzB b' hbA' hT' (hzAB b' hbA' hT' hAr')
        rw [e0, e1] at hB1'
        have haa : sc b = sc b' := by
          by_contra hne
          have hyl : max (arc (sc b)).l (arc (sc b')).l < z b 0 := max_lt (by linarith) (by linarith)
          have hy1 : max (arc (sc b)).l (arc (sc b')).l < (max (arc (sc b)).l (arc (sc b')).l + z b 0) / 2 := by linarith
          have hy2 : (max (arc (sc b)).l (arc (sc b')).l + z b 0) / 2 < z b 0 := by linarith
          have ha1 := le_max_left (arc (sc b)).l (arc (sc b')).l
          have ha2 := le_max_right (arc (sc b)).l (arc (sc b')).l
          set y := (max (arc (sc b)).l (arc (sc b')).l + z b 0) / 2
          rcases sep _ haA _ haA' hne y ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
            with h | h
          · refine hLA b' hbA' hT' (sc b) haA (by linarith) (by linarith) ?_ y (by linarith)
              (by linarith) (by linarith) h
            rw [e0]; linarith
          · exact hLA b hbA hT (sc b') haA' (by linarith) (by linarith) (by linarith) y
              (by linarith) (by linarith) (by linarith) h
        by_contra hne
        have hbb : (arc b').left = (arc b).left := by
          rw [← hscleft b' hT', ← hscleft b hT, haa]
        have hXb := hxsb b hbA
        have hXb' := hxs _ b' hbA' hbb
        rcases sep b hbA b' hbA' hne _ hXb hXb' with h | h
        · have hup : Up b b' := (hUp b b').2 ⟨hbA', hbb, h⟩
          have h1 := (hsc b hT).2 b' hup
          have h2 := hxsab b' hT'
          rw [hbb, ← haa] at h2
          linarith
        · have hup : Up b' b := (hUp b' b).2 ⟨hbA, hbb.symm, by rw [hbb]; exact h⟩
          have h1 := (hsc b' hT').2 b hup
          have h2 := hxsab b hT
          rw [hbb, ← haa] at h1
          linarith
      · have hAr' : z b' ≠ (arc (sc b')).right := fun h => hAr (hiff.2 h)
        have hA1 := hzA b hbA hT hAr
        have hA1' := hzA b' hbA' hT' hAr'
        rw [e0, e1] at hA1'
        by_contra hne
        have hyl : max (arc b).l (arc b').l < z b 0 := max_lt (by linarith) (by linarith)
        have hy1 : max (arc b).l (arc b').l < (max (arc b).l (arc b').l + z b 0) / 2 := by linarith
        have hy2 : (max (arc b).l (arc b').l + z b 0) / 2 < z b 0 := by linarith
        have ha1 := le_max_left (arc b).l (arc b').l
        have ha2 := le_max_right (arc b).l (arc b').l
        set y := (max (arc b).l (arc b').l + z b 0) / 2
        rcases sep b hbA b' hbA' hne y ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
          with h | h
        · exact hLB b hbA hT b' hbA' (by linarith) (by linarith) (by linarith) y (by linarith)
            (by linarith) (by linarith) h
        · refine hLB b' hbA' hT' b hbA (by linarith) (by linarith) ?_ y (by linarith)
            (by linarith) (by linarith) h
          rw [e0]; linarith
  have hNc : (A.filter fun b => ¬ ∃ j, Up b j).card ≤ V.card := by
    apply Finset.card_le_card_of_injOn (fun b => (arc b).left)
    · intro b hb
      obtain ⟨hbA, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      exact Finset.mem_coe.2 (hend b hbA).1
    · intro b hb b' hb' heq
      obtain ⟨hbA, hT⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      obtain ⟨hbA', hT'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb')
      have heq' : (arc b).left = (arc b').left := heq
      by_contra hne
      have hXb := hxsb b hbA
      have hXb' := hxs _ b' hbA' heq'.symm
      rcases sep b hbA b' hbA' hne _ hXb hXb' with h | h
      · exact hT ⟨b', (hUp b b').2 ⟨hbA', heq'.symm, h⟩⟩
      · exact hT' ⟨b, (hUp b' b).2 ⟨hbA, heq', by rw [← heq']; exact h⟩⟩
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hTc
  omega

end Erdos956Upper
