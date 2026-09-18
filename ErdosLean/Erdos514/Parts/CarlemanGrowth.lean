import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: Carleman's growth estimate in a tract — the core

If the complement of a tract `D = tract g K z₀` meets every large circle, then
`log (|g| / K)` reaches `c √r` on `D ∩ {|z| = r}` for all large `r`.

Proof plan (Carleman's method): put `u = log (‖g‖/K)` on `D`, `0` off `D`,
`v = (u - ε)⁺` for a small `ε > 0` below `u z₀`, pass to logarithmic coordinates
`z = e^{s+iθ}`, and let `m(s) = ∫₀^{2π} v(e^{s+iθ})² dθ`.
(a) `v` is locally Lipschitz and vanishes near `∂D`; `m` is `C¹` with `m'` Lipschitz,
    and a.e. `m'' = 2 ∫ (v_s² + v_θ²) dθ` (harmonicity of `u` in `D`, `u_ss = -u_θθ`,
    integration by parts in `θ` over the period).
(b) Wirtinger with one zero on each circle (the complement meets every circle):
    `∫ v_θ² ≥ ¼ ∫ v²`.
(c) Cauchy–Schwarz `m'² ≤ 4 m ∫ v_s²`, so `y = √m` satisfies `y'' ≥ y/4` (weakly).
(d) `y` is bounded below by a positive constant for large `s` (circle means of the
    subharmonic `v` do not decrease), hence `y(s) ≥ c e^{s/2}`.
(e) `m(s) ≤ 2π · (max over the circle of v)²`, and the maximum is attained in `D`. -/

open Real Set Filter Topology intervalIntegral

namespace Erdos514

/-- A `C²` convex cutoff: `Φ = 0` on `(-∞, 0]`, `0 < Φ t ≤ t` for `t > 0`. -/
lemma alt_phi_exists : ∃ Φ Φ1 Φ2 : ℝ → ℝ, Continuous Φ2 ∧ (∀ t, HasDerivAt Φ (Φ1 t) t) ∧
    (∀ t, HasDerivAt Φ1 (Φ2 t) t) ∧ (∀ t, 0 ≤ Φ2 t) ∧
    (∀ t ≤ 0, Φ t = 0) ∧ (∀ t < 0, Φ1 t = 0 ∧ Φ2 t = 0) ∧ (∀ t, 0 < t → 0 < Φ t ∧ Φ t ≤ t) ∧
    (∀ t, 0 ≤ Φ t) := by
  set st := Real.smoothTransition with hst
  have hcont : Continuous st := Real.smoothTransition.continuous
  have hz : ∀ x ≤ 0, st x = 0 := fun x hx => Real.smoothTransition.zero_of_nonpos hx
  refine ⟨fun t => ∫ x in (0:ℝ)..t, st x, st, deriv st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  · intro t
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  · intro t
    exact ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) t).hasDerivAt
  · intro t
    exact Real.smoothTransition.monotone.deriv_nonneg
  · intro t ht
    beta_reduce
    rw [intervalIntegral.integral_of_ge ht, neg_eq_zero]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (g := fun _ => (0:ℝ)) (fun x hx => hz x hx.2)]
    simp
  · intro t ht
    refine ⟨hz t ht.le, ?_⟩
    · have : st =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (show t < 0 from ht)] with x hx using hz x hx.le
      rw [this.deriv_eq]; simp
  · intro t ht
    constructor
    · apply intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
        (fun x hx => Real.smoothTransition.pos_of_pos hx.1) ht
    · have h1 : ∫ x in (0:ℝ)..t, st x ≤ ∫ x in (0:ℝ)..t, (1:ℝ) :=
        intervalIntegral.integral_mono_on ht.le (hcont.intervalIntegrable _ _)
          intervalIntegrable_const (fun x _ => Real.smoothTransition.le_one x)
      simpa using h1
  · intro t
    rcases le_or_gt t 0 with ht | ht
    · beta_reduce
      rw [intervalIntegral.integral_of_ge ht]
      have : ∫ x in Ioc t 0, st x ≤ 0 := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          (g := fun _ => (0:ℝ)) (fun x hx => Real.smoothTransition.zero_of_nonpos hx.2)]
        simp
      linarith
    · exact intervalIntegral.integral_nonneg ht.le (fun x _ => Real.smoothTransition.nonneg x)

/-- Differentiation under the integral sign, jointly continuous version. -/
lemma alt_hasDerivAt_integral {F F' : ℝ → ℝ → ℝ} (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × ℝ => F' p.1 p.2)) (hd : ∀ x t, HasDerivAt (fun x => F x t) (F' x t) x)
    (a b x₀ : ℝ) :
    HasDerivAt (fun x => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
    (hF'.continuousOn (s := Metric.closedBall x₀ 1 ×ˢ uIcc a b))
  have hcF : ∀ x, Continuous (F x) := fun x => hF.comp (Continuous.prodMk_right x)
  have hcF' : ∀ x, Continuous (F' x) := fun x => hF'.comp (Continuous.prodMk_right x)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (hcF x).aestronglyMeasurable)
    ((hcF x₀).intervalIntegrable _ _) (hcF' x₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx =>
      hM (x, t) ⟨Metric.ball_subset_closedBall hx, Set.uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const (Filter.Eventually.of_forall fun t _ x _ => hd x t)).2

/-- Cauchy–Schwarz for interval integrals of continuous functions. -/
lemma alt_cauchy_schwarz {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  set A := ∫ x in a..b, f x ^ 2
  set P := ∫ x in a..b, f x * g x
  set B := ∫ x in a..b, g x ^ 2
  have key : ∀ l : ℝ, 0 ≤ A * (l * l) + (-2 * P) * l + B := by
    intro l
    have h0 : 0 ≤ ∫ x in a..b, (g x - l * f x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : ∫ x in a..b, (g x - l * f x) ^ 2 = A * (l * l) + (-2 * P) * l + B := by
      have e : (fun x => (g x - l * f x) ^ 2) =
          fun x => (g x ^ 2 - (2 * l) * (f x * g x)) + (l * l) * f x ^ 2 := by
        funext x; ring
      rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      · ring
      all_goals first
        | exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith


/-- Picone-type estimate: `α² ∫ f² ≤ ∫ f'²` on `[a, a + 2π]` for `f` vanishing at both ends,
for every `0 < α < 1/2`. -/
lemma alt_wirtinger_alpha {f f1 : ℝ → ℝ} (hf1 : Continuous f1)
    (hd : ∀ x, HasDerivAt f (f1 x) x) {a : ℝ} (ha : f a = 0) (hb : f (a + 2 * π) = 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2) :
    α ^ 2 * ∫ x in a..a + 2 * π, f x ^ 2 ≤ ∫ x in a..a + 2 * π, f1 x ^ 2 := by
  set b := a + 2 * π with hbdef
  have hab : a ≤ b := by rw [hbdef]; linarith [pi_pos]
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  set c := a + π
  -- the argument stays in `(-π/2, π/2)`
  have harg : ∀ x ∈ uIcc a b, |α * (x - c)| < π / 2 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have h1 : |x - c| ≤ π := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rw [abs_mul, abs_of_pos hα0]
    calc α * |x - c| ≤ α * π := by gcongr
      _ < 1 / 2 * π := by gcongr
      _ = π / 2 := by ring
  have hcos : ∀ x ∈ uIcc a b, 0 < Real.cos (α * (x - c)) := by
    intro x hx
    apply Real.cos_pos_of_mem_Ioo
    have := harg x hx
    rw [abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  -- τ = -α tan(α (x - c)),  τ' = -α² / cos²
  set τ : ℝ → ℝ := fun x => -α * Real.tan (α * (x - c)) with hτ
  set τ' : ℝ → ℝ := fun x => -α * (α * (1 / Real.cos (α * (x - c)) ^ 2)) with hτ'
  have hτd : ∀ x ∈ uIcc a b, HasDerivAt τ (τ' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => α * (x - c)) α x := by
      simpa using ((hasDerivAt_id x).sub_const c).const_mul α
    have h2 := (Real.hasDerivAt_tan (hcos x hx).ne').comp x h1
    have h3 : HasDerivAt τ (-α * (1 / Real.cos (α * (x - c)) ^ 2 * α)) x := h2.const_mul (-α)
    exact h3.congr_deriv (by simp only [hτ']; ring)
  have hτ'c : ContinuousOn τ' (uIcc a b) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const
    · exact (Continuous.continuousOn (by fun_prop))
    · intro x hx; exact pow_ne_zero _ (hcos x hx).ne'
  have hτc : ContinuousOn τ (uIcc a b) := fun x hx => (hτd x hx).continuousAt.continuousWithinAt
  -- G = f² τ
  set G' : ℝ → ℝ := fun x => 2 * f x * f1 x * τ x + f x ^ 2 * τ' x with hG'
  have hGd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => f x ^ 2 * τ x) (G' x) x := by
    intro x hx
    exact (((hd x).pow 2).mul (hτd x hx)).congr_deriv
      (by simp only [hG', Pi.pow_apply]; first | ring | (norm_num <;> ring))
  have hG'c : ContinuousOn G' (uIcc a b) := by
    apply ContinuousOn.add
    · exact ((Continuous.continuousOn (by fun_prop)).mul hτc)
    · exact ((Continuous.continuousOn (by fun_prop)).mul hτ'c)
  have hGint : ∫ x in a..b, G' x = 0 := by
    rw [integral_eq_sub_of_hasDerivAt hGd (hG'c.intervalIntegrable)]
    simp [ha, hb]
  -- pointwise identity
  have hpt : ∀ x ∈ uIcc a b, (f1 x - f x * τ x) ^ 2 = f1 x ^ 2 - α ^ 2 * f x ^ 2 - G' x := by
    intro x hx
    have hc := (hcos x hx).ne'
    simp only [hG', hτ, hτ', Real.tan_eq_sin_div_cos]
    have hs := Real.sin_sq_add_cos_sq (α * (x - c))
    field_simp
    linear_combination (f x ^ 2 * α ^ 2) * hs
  have h0 : 0 ≤ ∫ x in a..b, (f1 x - f x * τ x) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, hGint] at h0
  · linarith
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact ((Continuous.intervalIntegrable (by fun_prop) _ _).sub
      (Continuous.intervalIntegrable (by fun_prop) _ _))
  · exact hG'c.intervalIntegrable

/-- Wirtinger's inequality for a function with a zero, on a period of length `2π`. -/
lemma alt_wirtinger {f f1 : ℝ → ℝ} (hf1 : Continuous f1)
    (hd : ∀ x, HasDerivAt f (f1 x) x) {a : ℝ} (ha : f a = 0) (hb : f (a + 2 * π) = 0) :
    (∫ x in a..a + 2 * π, f x ^ 2) / 4 ≤ ∫ x in a..a + 2 * π, f1 x ^ 2 := by
  set I1 := ∫ x in a..a + 2 * π, f x ^ 2
  set I2 := ∫ x in a..a + 2 * π, f1 x ^ 2
  have hI1 : 0 ≤ I1 := intervalIntegral.integral_nonneg (by linarith [pi_pos])
    (fun x _ => sq_nonneg _)
  have hI2 : 0 ≤ I2 := intervalIntegral.integral_nonneg (by linarith [pi_pos])
    (fun x _ => sq_nonneg _)
  by_contra hcon
  push Not at hcon
  have hI1pos : 0 < I1 := by linarith
  set β := I2 / I1
  have hβ : β < 1 / 4 := by
    rw [div_lt_iff₀ hI1pos]; linarith
  have hβ0 : 0 ≤ β := div_nonneg hI2 hI1
  set α := Real.sqrt ((β + 1 / 4) / 2)
  have hαsq : α ^ 2 = (β + 1 / 4) / 2 := Real.sq_sqrt (by linarith)
  have hα0 : 0 < α := Real.sqrt_pos.2 (by linarith)
  have hα1 : α < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have := alt_wirtinger_alpha hf1 hd ha hb hα0 hα1
  rw [hαsq] at this
  change (β + 1 / 4) / 2 * I1 ≤ I2 at this
  have h2 : I2 = β * I1 := by rw [div_mul_cancel₀ _ hI1pos.ne']
  rw [h2] at this
  nlinarith [mul_pos (sub_pos.2 hβ) hI1pos]

/-- Convexity plus boundedness at `-∞` forces a nonnegative derivative. -/
lemma alt_deriv_nonneg_of_convex {m m1 m2 : ℝ → ℝ} (hm : ∀ s, HasDerivAt m (m1 s) s)
    (hm1 : ∀ s, HasDerivAt m1 (m2 s) s) (hm2 : ∀ s, 0 ≤ m2 s) {B : ℝ}
    (hB : ∀ s ≤ 0, m s ≤ B) : ∀ s, 0 ≤ m1 s := by
  intro s₁
  by_contra hcon
  push Not at hcon
  set δ := -m1 s₁ with hδ
  have hδpos : 0 < δ := by linarith
  have hmono : Monotone m1 := monotone_of_hasDerivAt_nonneg hm1 hm2
  -- k s = m s + δ s is antitone on `(-∞, s₁]`
  have hanti : AntitoneOn (fun s => m s + δ * s) (Iic s₁) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic s₁)
      (f' := fun s => m1 s + δ)
    · intro x _
      exact ((hm x).add ((hasDerivAt_id x).const_mul δ)).continuousAt.continuousWithinAt
    · intro x _
      exact (((hm x).add ((hasDerivAt_id' x).const_mul δ)).congr_deriv
        (by ring)).hasDerivWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      have := hmono hx.le
      linarith
  set s := min s₁ 0 - (B - m s₁ + 1) / δ - |B - m s₁ + 1| / δ
  have hs1 : s ≤ s₁ := by
    have : 0 ≤ (B - m s₁ + 1) / δ + |B - m s₁ + 1| / δ := by
      rw [← add_div]; apply div_nonneg _ hδpos.le
      linarith [neg_abs_le (B - m s₁ + 1)]
    have := min_le_left s₁ 0
    simp only [s]; linarith
  have hs0 : s ≤ 0 := by
    have : 0 ≤ (B - m s₁ + 1) / δ + |B - m s₁ + 1| / δ := by
      rw [← add_div]; apply div_nonneg _ hδpos.le
      linarith [neg_abs_le (B - m s₁ + 1)]
    have := min_le_right s₁ 0
    simp only [s]; linarith
  have hk := hanti (mem_Iic.2 hs1) (mem_Iic.2 le_rfl) hs1
  simp only at hk
  have hBs := hB s hs0
  -- δ (s₁ - s) ≥ B - m s₁ + 1
  have hgap : B - m s₁ + 1 ≤ δ * (s₁ - s) := by
    have e1 : s₁ - s ≥ (B - m s₁ + 1) / δ + |B - m s₁ + 1| / δ := by
      have := min_le_left s₁ 0
      simp only [s]; linarith
    have e2 : δ * ((B - m s₁ + 1) / δ + |B - m s₁ + 1| / δ) =
        (B - m s₁ + 1) + |B - m s₁ + 1| := by
      field_simp
    have e3 : δ * ((B - m s₁ + 1) / δ + |B - m s₁ + 1| / δ) ≤ δ * (s₁ - s) :=
      mul_le_mul_of_nonneg_left e1 hδpos.le
    linarith [abs_nonneg (B - m s₁ + 1)]
  nlinarith

/-- The ODE comparison: `2 m m'' ≥ m'² + m²` forces `m ≥ c eˢ`. -/
lemma alt_ode {m m1 m2 : ℝ → ℝ} (hm : ∀ s, HasDerivAt m (m1 s) s)
    (hm1 : ∀ s, HasDerivAt m1 (m2 s) s) {s₀ : ℝ} (hpos : ∀ s ≥ s₀, 0 < m s)
    (hm1nn : ∀ s ≥ s₀, 0 ≤ m1 s) (hineq : ∀ s ≥ s₀, m1 s ^ 2 + m s ^ 2 ≤ 2 * m s * m2 s) :
    ∃ c > 0, ∃ S, ∀ s ≥ S, c * Real.exp s ≤ m s := by
  set y : ℝ → ℝ := fun s => Real.sqrt (m s) with hy
  set y1 : ℝ → ℝ := fun s => m1 s / (2 * Real.sqrt (m s)) with hy1
  set y2 : ℝ → ℝ := fun s => (m2 s * (2 * Real.sqrt (m s)) - m1 s * (2 * (m1 s /
    (2 * Real.sqrt (m s))))) / (2 * Real.sqrt (m s)) ^ 2 with hy2
  have hyd : ∀ s ≥ s₀, HasDerivAt y (y1 s) s := fun s hs =>
    (hm s).sqrt (hpos s hs).ne'
  have hy1d : ∀ s ≥ s₀, HasDerivAt y1 (y2 s) s := by
    intro s hs
    have hsq : 0 < Real.sqrt (m s) := Real.sqrt_pos.2 (hpos s hs)
    exact (hm1 s).div (((hm s).sqrt (hpos s hs).ne').const_mul 2) (by positivity)
  have hy_pos : ∀ s ≥ s₀, 0 < y s := fun s hs => Real.sqrt_pos.2 (hpos s hs)
  have hy1_nn : ∀ s ≥ s₀, 0 ≤ y1 s := fun s hs =>
    div_nonneg (hm1nn s hs) (by positivity)
  have hy2_ge : ∀ s ≥ s₀, y s / 4 ≤ y2 s := by
    intro s hs
    have hR : 0 < Real.sqrt (m s) := Real.sqrt_pos.2 (hpos s hs)
    have hRR : Real.sqrt (m s) ^ 2 = m s := Real.sq_sqrt (hpos s hs).le
    simp only [hy, hy2]
    rw [le_div_iff₀ (by positivity)]
    have hi := hineq s hs
    rw [← hRR] at hi
    field_simp
    nlinarith [hi, hR]
  -- z = y1 + y/2 satisfies z' ≥ z/2
  set z : ℝ → ℝ := fun s => y1 s + y s / 2 with hz
  have hzd : ∀ s ≥ s₀, HasDerivAt z (y2 s + y1 s / 2) s := fun s hs =>
    (hy1d s hs).add ((hyd s hs).div_const 2)
  -- P = e^{-s/2} z is monotone on [s₀, ∞)
  set P : ℝ → ℝ := fun s => Real.exp (-s / 2) * z s with hP
  have hPd : ∀ s ≥ s₀, HasDerivAt P (Real.exp (-s / 2) * (-1 / 2) * z s +
      Real.exp (-s / 2) * (y2 s + y1 s / 2)) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (-s / 2)) (Real.exp (-s / 2) * (-1 / 2)) s := by
      have := ((hasDerivAt_id s).neg.div_const 2).exp
      simpa using this
    exact he.mul (hzd s hs)
  have hPmono : MonotoneOn P (Ici s₀) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s₀)
    · intro x hx; exact (hPd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hPd x (le_of_lt hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : x ≥ s₀ := le_of_lt hx
      have h1 := hy2_ge x hx'
      have he := Real.exp_pos (-x / 2)
      simp only [hz]
      nlinarith [hy1_nn x hx']
  set C₁ := P s₀ with hC₁
  have hC₁pos : 0 < C₁ := by
    simp only [hC₁, hP, hz]
    have := hy_pos s₀ le_rfl
    have := hy1_nn s₀ le_rfl
    positivity
  have hzlow : ∀ s ≥ s₀, C₁ * Real.exp (s / 2) ≤ z s := by
    intro s hs
    have h : C₁ ≤ Real.exp (-s / 2) * z s := hPmono (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs
    have e : Real.exp (-s / 2) * Real.exp (s / 2) = 1 := by
      rw [← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]
    calc C₁ * Real.exp (s / 2) ≤ Real.exp (-s / 2) * z s * Real.exp (s / 2) := by
          gcongr
      _ = z s := by rw [mul_comm (Real.exp (-s/2)) (z s), mul_assoc, e, mul_one]
  -- Q = e^{s/2} y - C₁ eˢ is monotone
  set Q : ℝ → ℝ := fun s => Real.exp (s / 2) * y s - C₁ * Real.exp s with hQ
  have hQd : ∀ s ≥ s₀, HasDerivAt Q (Real.exp (s / 2) * (1 / 2) * y s +
      Real.exp (s / 2) * y1 s - C₁ * Real.exp s) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (s / 2)) (Real.exp (s / 2) * (1 / 2)) s := by
      have := ((hasDerivAt_id s).div_const 2).exp
      simpa using this
    exact (he.mul (hyd s hs)).sub ((Real.hasDerivAt_exp s).const_mul C₁)
  have hQmono : MonotoneOn Q (Ici s₀) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s₀)
    · intro x hx; exact (hQd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hQd x (le_of_lt hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : x ≥ s₀ := le_of_lt hx
      have h1 := hzlow x hx'
      have he := Real.exp_pos (x / 2)
      have e : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
        rw [← Real.exp_add]; ring_nf
      simp only [hz] at h1
      rw [e]
      nlinarith
  set Q₀ := Q s₀
  refine ⟨C₁ ^ 2 / 4, by positivity, max s₀ (Real.log (2 * |Q₀| / C₁ + 1)), fun s hs => ?_⟩
  have hs0 : s ≥ s₀ := le_trans (le_max_left _ _) hs
  have hsl : Real.log (2 * |Q₀| / C₁ + 1) ≤ s := le_trans (le_max_right _ _) hs
  have hexp : 2 * |Q₀| / C₁ + 1 ≤ Real.exp s := by
    rw [← Real.exp_log (show 0 < 2 * |Q₀| / C₁ + 1 by positivity)]
    exact Real.exp_le_exp.2 hsl
  have hQs := hQmono (mem_Ici.2 le_rfl) (mem_Ici.2 hs0) hs0
  simp only [hQ] at hQs
  have e : Real.exp s = Real.exp (s / 2) * Real.exp (s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have he2 := Real.exp_pos (s / 2)
  have hys := hy_pos s hs0
  -- e^{s/2} y ≥ (C₁/2) eˢ
  have h1 : 2 * |Q₀| ≤ C₁ * Real.exp s := by
    have := mul_le_mul_of_nonneg_left hexp hC₁pos.le
    rw [mul_add, mul_div_cancel₀ _ hC₁pos.ne'] at this
    linarith
  have h2 : C₁ / 2 * Real.exp s ≤ Real.exp (s / 2) * y s := by
    have := neg_abs_le Q₀
    change Q s₀ ≤ Real.exp (s / 2) * y s - C₁ * Real.exp s at hQs
    linarith
  -- so y ≥ (C₁/2) e^{s/2}
  have h3 : C₁ / 2 * Real.exp (s / 2) ≤ y s := by
    rw [e] at h2
    have := le_of_mul_le_mul_left (by linarith : Real.exp (s / 2) * (C₁ / 2 * Real.exp (s / 2))
      ≤ Real.exp (s / 2) * y s) he2
    exact this
  have h4 : (C₁ / 2 * Real.exp (s / 2)) ^ 2 ≤ y s ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have hysq : y s ^ 2 = m s := Real.sq_sqrt (hpos s hs0).le
  rw [hysq] at h4
  calc C₁ ^ 2 / 4 * Real.exp s = (C₁ / 2 * Real.exp (s / 2)) ^ 2 := by rw [e]; ring
    _ ≤ m s := h4


/-- Data for Carleman's method. -/
structure alt_CData where
  g : ℂ → ℂ
  K : ℝ
  ε : ℝ
  D : Set ℂ
  Φ : ℝ → ℝ
  Φ1 : ℝ → ℝ
  Φ2 : ℝ → ℝ
  hg : Differentiable ℂ g
  hK : 0 < K
  hε : 0 < ε
  hDopen : IsOpen D
  hDpos : ∀ z ∈ D, K < ‖g z‖
  hloc : ∀ z ∉ D, ∀ᶠ z' in 𝓝 z, z' ∉ D ∨ Real.log (‖g z'‖ / K) - ε < 0
  hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t
  hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t
  hΦ2c : Continuous Φ2
  hΦ0 : ∀ t ≤ 0, Φ t = 0
  hΦ10 : ∀ t < 0, Φ1 t = 0
  hΦ20 : ∀ t < 0, Φ2 t = 0
  hΦ2nn : ∀ t, 0 ≤ Φ2 t
  hΦnn : ∀ t, 0 ≤ Φ t
  hΦle : ∀ t, 0 < t → Φ t ≤ t

namespace alt_CData

variable (S : alt_CData)

/-- `u - ε` in the `z`-plane. -/
noncomputable def U (z : ℂ) : ℝ := Real.log (‖S.g z‖ / S.K) - S.ε

open Classical in
/-- The cut-off subharmonic function in the `z`-plane. -/
noncomputable def Vz (z : ℂ) : ℝ := if z ∈ S.D then S.Φ (S.U z) else 0

/-- `g ∘ exp`. -/
noncomputable def h (w : ℂ) : ℂ := S.g (Complex.exp w)

/-- logarithmic derivative of `h`. -/
noncomputable def q (w : ℂ) : ℂ := deriv S.h w / S.h w

/-- `V` in logarithmic coordinates. -/
noncomputable def V (w : ℂ) : ℝ := S.Vz (Complex.exp w)

open Classical in
/-- directional derivative of `V` in direction `d`. -/
noncomputable def V1 (d w : ℂ) : ℝ :=
  if Complex.exp w ∈ S.D then S.Φ1 (S.U (Complex.exp w)) * (d * S.q w).re else 0

open Classical in
/-- second directional derivative of `V` in direction `d`. -/
noncomputable def V2 (d w : ℂ) : ℝ :=
  if Complex.exp w ∈ S.D then
    S.Φ2 (S.U (Complex.exp w)) * (d * S.q w).re ^ 2 +
      S.Φ1 (S.U (Complex.exp w)) * (d ^ 2 * deriv S.q w).re
  else 0

lemma Φ_cont : Continuous S.Φ := continuous_iff_continuousAt.2 fun t => (S.hΦ t).continuousAt
lemma Φ1_cont : Continuous S.Φ1 :=
  continuous_iff_continuousAt.2 fun t => (S.hΦ1 t).continuousAt

lemma h_diff : Differentiable ℂ S.h := S.hg.comp Complex.differentiable_exp

lemma h_analytic (w : ℂ) : AnalyticAt ℂ S.h w := S.h_diff.analyticAt w

lemma g_ne {z : ℂ} (hz : z ∈ S.D) : S.g z ≠ 0 := by
  intro h0
  have := S.hDpos z hz
  rw [h0, norm_zero] at this
  linarith [S.hK]

lemma h_ne {w : ℂ} (hw : Complex.exp w ∈ S.D) : S.h w ≠ 0 := S.g_ne hw

lemma q_analytic {w : ℂ} (hw : Complex.exp w ∈ S.D) : AnalyticAt ℂ S.q w :=
  (S.h_analytic w).deriv.div (S.h_analytic w) (S.h_ne hw)

lemma evD {w : ℂ} (hw : Complex.exp w ∈ S.D) : ∀ᶠ w' in 𝓝 w, Complex.exp w' ∈ S.D :=
  Complex.continuous_exp.continuousAt.preimage_mem_nhds (S.hDopen.mem_nhds hw)

lemma evOut {w : ℂ} (hw : Complex.exp w ∉ S.D) :
    ∀ᶠ w' in 𝓝 w, Complex.exp w' ∉ S.D ∨ S.U (Complex.exp w') < 0 :=
  Complex.continuous_exp.continuousAt.eventually (S.hloc _ hw)

lemma zero_out {w : ℂ} (d : ℂ) (hw : Complex.exp w ∉ S.D ∨ S.U (Complex.exp w) < 0) :
    S.V w = 0 ∧ S.V1 d w = 0 ∧ S.V2 d w = 0 := by
  rcases hw with hw | hw
  · simp [V, Vz, V1, V2, hw]
  · simp [V, Vz, V1, V2, S.hΦ0 _ hw.le, S.hΦ10 _ hw, S.hΦ20 _ hw]

lemma U_eq {z : ℂ} (hz : z ∈ S.D) :
    S.U z = Real.log ‖S.g z‖ - Real.log S.K - S.ε := by
  have h1 : ‖S.g z‖ ≠ 0 := norm_ne_zero_iff.2 (S.g_ne hz)
  simp only [U]
  rw [Real.log_div h1 S.hK.ne']

lemma U_contAt {z : ℂ} (hz : z ∈ S.D) : ContinuousAt S.U z := by
  have h1 : ‖S.g z‖ / S.K ≠ 0 :=
    div_ne_zero (norm_ne_zero_iff.2 (S.g_ne hz)) S.hK.ne'
  have hc : ContinuousAt (fun z => ‖S.g z‖ / S.K) z :=
    ((S.hg.continuous.norm).div_const S.K).continuousAt
  exact (hc.log h1).sub continuousAt_const

lemma Vz_cont : Continuous S.Vz := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ S.D
  · have heq : (fun z => S.Φ (S.U z)) =ᶠ[𝓝 z] S.Vz := by
      filter_upwards [S.hDopen.mem_nhds hz] with z' hz'
      simp [Vz, hz']
    exact ((S.Φ_cont.continuousAt).comp (S.U_contAt hz)).congr heq
  · have hev := S.hloc z hz
    have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 z] S.Vz := by
      filter_upwards [hev] with z' hz'
      rcases hz' with hz' | hz'
      · simp [Vz, hz']
      · have h' : S.U z' < 0 := hz'
        simp [Vz, S.hΦ0 _ h'.le]
    exact continuousAt_const.congr heq

lemma V_cont : Continuous S.V := S.Vz_cont.comp Complex.continuous_exp

lemma V_nonneg (w : ℂ) : 0 ≤ S.V w := by
  simp only [V, Vz]
  split_ifs
  · exact S.hΦnn _
  · exact le_rfl

lemma V_periodic (w : ℂ) : S.V (w + 2 * π * Complex.I) = S.V w := by
  simp only [V, Complex.exp_periodic w]

lemma V1_cont (d : ℂ) : Continuous (S.V1 d) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : Complex.exp w ∈ S.D
  · have heq : (fun w => S.Φ1 (S.U (Complex.exp w)) * (d * S.q w).re) =ᶠ[𝓝 w] S.V1 d := by
      filter_upwards [S.evD hw] with w' hw'
      simp [V1, hw']
    refine ContinuousAt.congr ?_ heq
    have hU : ContinuousAt (fun w => S.U (Complex.exp w)) w :=
      (S.U_contAt hw).comp Complex.continuous_exp.continuousAt
    have hq : ContinuousAt S.q w := (S.q_analytic hw).continuousAt
    exact ((S.Φ1_cont.continuousAt).comp hU).mul
      (Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hq))
  · have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 w] S.V1 d := by
      filter_upwards [S.evOut hw] with w' hw'
      exact (S.zero_out d hw').2.1.symm
    exact continuousAt_const.congr heq

lemma V2_cont (d : ℂ) : Continuous (S.V2 d) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : Complex.exp w ∈ S.D
  · have heq : (fun w => S.Φ2 (S.U (Complex.exp w)) * (d * S.q w).re ^ 2 +
        S.Φ1 (S.U (Complex.exp w)) * (d ^ 2 * deriv S.q w).re) =ᶠ[𝓝 w] S.V2 d := by
      filter_upwards [S.evD hw] with w' hw'
      simp [V2, hw']
    refine ContinuousAt.congr ?_ heq
    have hU : ContinuousAt (fun w => S.U (Complex.exp w)) w :=
      (S.U_contAt hw).comp Complex.continuous_exp.continuousAt
    have hq : ContinuousAt S.q w := (S.q_analytic hw).continuousAt
    have hq' : ContinuousAt (deriv S.q) w := (S.q_analytic hw).deriv.continuousAt
    apply ContinuousAt.add
    · exact ((S.hΦ2c.continuousAt).comp hU).mul
        ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hq)).pow 2)
    · exact ((S.Φ1_cont.continuousAt).comp hU).mul
        (Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hq'))
  · have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 w] S.V2 d := by
      filter_upwards [S.evOut hw] with w' hw'
      exact (S.zero_out d hw').2.2.symm
    exact continuousAt_const.congr heq

/-- The Laplacian of `V` is nonnegative. -/
lemma lap_nonneg (w : ℂ) : 0 ≤ S.V2 1 w + S.V2 Complex.I w := by
  simp only [V2]
  split_ifs with hw
  · have e1 : ((1 : ℂ) ^ 2 * deriv S.q w).re + (Complex.I ^ 2 * deriv S.q w).re = 0 := by
      simp [Complex.I_sq]
    have : S.Φ2 (S.U (Complex.exp w)) * (1 * S.q w).re ^ 2 +
        S.Φ1 (S.U (Complex.exp w)) * ((1 : ℂ) ^ 2 * deriv S.q w).re +
        (S.Φ2 (S.U (Complex.exp w)) * (Complex.I * S.q w).re ^ 2 +
        S.Φ1 (S.U (Complex.exp w)) * (Complex.I ^ 2 * deriv S.q w).re) =
        S.Φ2 (S.U (Complex.exp w)) * ((1 * S.q w).re ^ 2 + (Complex.I * S.q w).re ^ 2) +
        S.Φ1 (S.U (Complex.exp w)) * (((1 : ℂ) ^ 2 * deriv S.q w).re +
          (Complex.I ^ 2 * deriv S.q w).re) := by ring
    rw [this, e1, mul_zero, add_zero]
    exact mul_nonneg (S.hΦ2nn _) (by positivity)
  · simp

/-! ### Directional derivatives -/

lemma path_cont (a d : ℂ) : Continuous (fun t : ℝ => a + (t : ℂ) * d) := by fun_prop

lemma ev_path {a d : ℂ} {t₀ : ℝ} {P : ℂ → Prop} (hP : ∀ᶠ w in 𝓝 (a + (t₀ : ℂ) * d), P w) :
    ∀ᶠ t : ℝ in 𝓝 t₀, P (a + (t : ℂ) * d) :=
  ((path_cont a d).tendsto t₀).eventually hP

lemma hasDerivAt_path (a d : ℂ) (t₀ : ℂ) : HasDerivAt (fun ζ : ℂ => a + ζ * d) d t₀ := by
  simpa using ((hasDerivAt_id t₀).mul_const d).const_add a

/-- Directional derivative of `log ‖h‖`. -/
lemma dir_logh {a d : ℂ} {t₀ : ℝ} (hw : Complex.exp (a + (t₀ : ℂ) * d) ∈ S.D) :
    HasDerivAt (fun t : ℝ => Real.log ‖S.h (a + (t : ℂ) * d)‖)
      ((d * S.q (a + (t₀ : ℂ) * d)).re) t₀ := by
  set w₀ := a + (t₀ : ℂ) * d with hw₀
  have hne : S.h w₀ ≠ 0 := S.h_ne hw
  have hF : HasDerivAt S.h (deriv S.h w₀) w₀ := (S.h_diff w₀).hasDerivAt
  have hcomp : HasDerivAt (S.h ∘ fun ζ : ℂ => a + ζ * d) (deriv S.h w₀ * d) (t₀ : ℂ) :=
    HasDerivAt.comp (h₂ := S.h) (t₀ : ℂ) hF (hasDerivAt_path a d t₀)
  have hdiv := hcomp.div_const (S.h w₀)
  have hmem : S.h (a + (t₀ : ℂ) * d) / S.h w₀ ∈ Complex.slitPlane := by
    rw [← hw₀, div_self hne]; exact Complex.one_mem_slitPlane
  have hre := (hdiv.clog hmem).real_of_complex
  have hval : (deriv S.h w₀ * d / S.h w₀ / (S.h (a + (t₀ : ℂ) * d) / S.h w₀)) =
      d * S.q w₀ := by
    rw [← hw₀, div_self hne, div_one]; simp only [q]; ring
  have hre' : HasDerivAt (fun x : ℝ => (Complex.log (S.h (a + (x : ℂ) * d) / S.h w₀)).re)
      ((d * S.q w₀).re) t₀ := hre.congr_deriv (congrArg Complex.re hval)
  have hre2 := hre'.add_const (Real.log ‖S.h w₀‖)
  refine hre2.congr_of_eventuallyEq ?_
  have hcont : Continuous (fun t : ℝ => S.h (a + (t : ℂ) * d)) :=
    S.h_diff.continuous.comp (path_cont a d)
  filter_upwards [hcont.continuousAt.eventually_ne (show S.h (a + (t₀ : ℂ) * d) ≠ 0 from hne)]
    with t ht
  rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 ht)
    (norm_ne_zero_iff.2 hne)]
  ring

/-- Directional derivative of `re (d * Q)`. -/
lemma dir_re {Q : ℂ → ℂ} {Q' : ℂ} {a d : ℂ} {t₀ : ℝ}
    (hQ : HasDerivAt Q Q' (a + (t₀ : ℂ) * d)) :
    HasDerivAt (fun t : ℝ => (d * Q (a + (t : ℂ) * d)).re) ((d * (Q' * d)).re) t₀ := by
  have hcomp : HasDerivAt (fun ζ : ℂ => d * Q (a + ζ * d)) (d * (Q' * d)) (t₀ : ℂ) :=
    (hQ.comp (t₀ : ℂ) (hasDerivAt_path a d t₀)).const_mul d
  exact hcomp.real_of_complex

lemma dir_V (a d : ℂ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => S.V (a + (t : ℂ) * d)) (S.V1 d (a + (t₀ : ℂ) * d)) t₀ := by
  by_cases hw : Complex.exp (a + (t₀ : ℂ) * d) ∈ S.D
  · set ℓ : ℝ → ℝ := fun t => Real.log ‖S.h (a + (t : ℂ) * d)‖ - Real.log S.K - S.ε
    have hℓ : HasDerivAt ℓ ((d * S.q (a + (t₀ : ℂ) * d)).re) t₀ :=
      ((S.dir_logh hw).sub_const _).sub_const _
    have hℓ0 : ℓ t₀ = S.U (Complex.exp (a + (t₀ : ℂ) * d)) := by
      simp only [ℓ, S.U_eq hw, h]
    have hc := (S.hΦ (ℓ t₀)).comp t₀ hℓ
    rw [hℓ0] at hc
    have hv : S.V1 d (a + (t₀ : ℂ) * d) =
        S.Φ1 (S.U (Complex.exp (a + (t₀ : ℂ) * d))) * (d * S.q (a + (t₀ : ℂ) * d)).re := by
      simp [V1, hw]
    rw [hv]
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [ev_path (S.evD hw)] with t ht
    simp only [Function.comp, V, Vz, ℓ, h]
    rw [if_pos ht, S.U_eq ht]
  · have hev := ev_path (S.evOut hw)
    have hv : S.V1 d (a + (t₀ : ℂ) * d) = 0 := (S.zero_out d hev.self_of_nhds).2.1
    rw [hv]
    refine (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    exact (S.zero_out d ht).1

lemma dir_V1 (a d : ℂ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => S.V1 d (a + (t : ℂ) * d)) (S.V2 d (a + (t₀ : ℂ) * d)) t₀ := by
  by_cases hw : Complex.exp (a + (t₀ : ℂ) * d) ∈ S.D
  · set ℓ : ℝ → ℝ := fun t => Real.log ‖S.h (a + (t : ℂ) * d)‖ - Real.log S.K - S.ε
    have hℓ : HasDerivAt ℓ ((d * S.q (a + (t₀ : ℂ) * d)).re) t₀ :=
      ((S.dir_logh hw).sub_const _).sub_const _
    have hℓ0 : ℓ t₀ = S.U (Complex.exp (a + (t₀ : ℂ) * d)) := by
      simp only [ℓ, h]; rw [S.U_eq hw]
    have hc := (S.hΦ1 (ℓ t₀)).comp t₀ hℓ
    rw [hℓ0] at hc
    have hq : HasDerivAt S.q (deriv S.q (a + (t₀ : ℂ) * d)) (a + (t₀ : ℂ) * d) :=
      (S.q_analytic hw).differentiableAt.hasDerivAt
    have hr := dir_re (d := d) (a := a) (t₀ := t₀) hq
    have hprod := hc.mul hr
    have hv : S.V2 d (a + (t₀ : ℂ) * d) =
        S.Φ2 (S.U (Complex.exp (a + (t₀ : ℂ) * d))) * (d * S.q (a + (t₀ : ℂ) * d)).re ^ 2 +
        S.Φ1 (S.U (Complex.exp (a + (t₀ : ℂ) * d))) *
          (d ^ 2 * deriv S.q (a + (t₀ : ℂ) * d)).re := by
      simp [V2, hw]
    rw [hv]
    refine (hprod.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [show d * (deriv S.q (a + (t₀ : ℂ) * d) * d) =
        d ^ 2 * deriv S.q (a + (t₀ : ℂ) * d) by ring]
      simp only [Function.comp, hℓ0]
      ring
    · filter_upwards [ev_path (S.evD hw)] with t ht
      simp only [Function.comp, V1, ℓ, h]
      rw [if_pos ht, S.U_eq ht]
      rfl
  · have hev := ev_path (S.evOut hw)
    have hv : S.V2 d (a + (t₀ : ℂ) * d) = 0 := (S.zero_out d hev.self_of_nhds).2.2
    rw [hv]
    refine (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    exact (S.zero_out d ht).2.1

end alt_CData


/-! ### Auxiliary real lemmas for the integral part -/

lemma alt_deriv_periodic {f f1 : ℝ → ℝ} {T : ℝ} (hd : ∀ x, HasDerivAt f (f1 x) x)
    (hp : Function.Periodic f T) : Function.Periodic f1 T := by
  intro x
  have h1 : HasDerivAt (fun y => f (y + T)) (f1 (x + T)) x :=
    HasDerivAt.comp_add_const x T (hd (x + T))
  have h2 : (fun y => f (y + T)) = f := funext hp
  rw [h2] at h1
  exact h1.unique (hd x)

lemma alt_integral_pos {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) {a b x : ℝ}
    (hax : a < x) (hxb : x < b) (hx : 0 < f x) : 0 < ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hnn) (hf.intervalIntegrable _ _)]
  refine ⟨hax.trans hxb, ?_⟩
  have hopen : IsOpen (Function.support f ∩ Ioo a b) :=
    (isOpen_ne_fun hf continuous_const).inter isOpen_Ioo
  have hne : (Function.support f ∩ Ioo a b).Nonempty := ⟨x, hx.ne', hax, hxb⟩
  exact lt_of_lt_of_le (hopen.measure_pos MeasureTheory.volume hne)
    (MeasureTheory.measure_mono (inter_subset_inter_right _ Ioo_subset_Ioc_self))

lemma alt_exp_log_pt {z : ℂ} (hz : z ≠ 0) :
    Complex.exp ((Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I) = z := by
  have : ((Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I) = Complex.log z := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  rw [this, Complex.exp_log hz]

namespace alt_CData

variable (S : alt_CData)

/-- the point `s + iθ`. -/
noncomputable def pt (s θ : ℝ) : ℂ := (s : ℂ) + (θ : ℂ) * Complex.I

lemma pt_cont : Continuous (fun p : ℝ × ℝ => pt p.1 p.2) := by
  unfold pt; fun_prop

lemma dV_s (θ s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => S.V (pt s θ)) (S.V1 1 (pt s₀ θ)) s₀ := by
  have e : ∀ t : ℝ, pt t θ = (θ : ℂ) * Complex.I + (t : ℂ) * 1 := fun t => by
    simp only [pt]; ring
  simp only [e]
  exact S.dir_V _ _ _

lemma dV1_s (θ s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => S.V1 1 (pt s θ)) (S.V2 1 (pt s₀ θ)) s₀ := by
  have e : ∀ t : ℝ, pt t θ = (θ : ℂ) * Complex.I + (t : ℂ) * 1 := fun t => by
    simp only [pt]; ring
  simp only [e]
  exact S.dir_V1 _ _ _

lemma dV_θ (s θ₀ : ℝ) :
    HasDerivAt (fun θ : ℝ => S.V (pt s θ)) (S.V1 Complex.I (pt s θ₀)) θ₀ :=
  S.dir_V _ _ _

lemma dV1_θ (s θ₀ : ℝ) :
    HasDerivAt (fun θ : ℝ => S.V1 Complex.I (pt s θ)) (S.V2 Complex.I (pt s θ₀)) θ₀ :=
  S.dir_V1 _ _ _

lemma V_pt_periodic (s : ℝ) : Function.Periodic (fun θ : ℝ => S.V (pt s θ)) (2 * π) := by
  intro θ
  have : pt s (θ + 2 * π) = pt s θ + 2 * π * Complex.I := by
    simp only [pt]; push_cast; ring
  simp only [this, S.V_periodic]

lemma V1_pt_periodic (s : ℝ) :
    Function.Periodic (fun θ : ℝ => S.V1 Complex.I (pt s θ)) (2 * π) :=
  alt_deriv_periodic (fun θ => S.dV_θ s θ) (S.V_pt_periodic s)

/-- `m(s) = ∫ V²`. -/
noncomputable def M (s : ℝ) : ℝ := ∫ θ in (0:ℝ)..2 * π, S.V (pt s θ) ^ 2
noncomputable def M1 (s : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..2 * π, 2 * S.V (pt s θ) * S.V1 1 (pt s θ)
noncomputable def M2 (s : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..2 * π, (2 * S.V1 1 (pt s θ) * S.V1 1 (pt s θ) +
    2 * S.V (pt s θ) * S.V2 1 (pt s θ))
/-- `∫ V_s²` -/
noncomputable def E (s : ℝ) : ℝ := ∫ θ in (0:ℝ)..2 * π, S.V1 1 (pt s θ) ^ 2
/-- `∫ V_θ²` -/
noncomputable def T (s : ℝ) : ℝ := ∫ θ in (0:ℝ)..2 * π, S.V1 Complex.I (pt s θ) ^ 2

lemma V_eq_of_mem {w : ℂ} (hw : Complex.exp w ∈ S.D) :
    S.V w = S.Φ (S.U (Complex.exp w)) := by
  simp only [V, Vz]; rw [if_pos hw]

lemma V_eq_of_not_mem {w : ℂ} (hw : Complex.exp w ∉ S.D) : S.V w = 0 := by
  simp only [V, Vz]; rw [if_neg hw]

lemma cV : Continuous (fun p : ℝ × ℝ => S.V (pt p.1 p.2)) := S.V_cont.comp pt_cont
lemma cV1 (d : ℂ) : Continuous (fun p : ℝ × ℝ => S.V1 d (pt p.1 p.2)) :=
  (S.V1_cont d).comp pt_cont
lemma cV2 (d : ℂ) : Continuous (fun p : ℝ × ℝ => S.V2 d (pt p.1 p.2)) :=
  (S.V2_cont d).comp pt_cont

lemma cVθ (s : ℝ) : Continuous (fun θ : ℝ => S.V (pt s θ)) :=
  S.cV.comp (Continuous.prodMk_right s)
lemma cV1θ (d : ℂ) (s : ℝ) : Continuous (fun θ : ℝ => S.V1 d (pt s θ)) :=
  (S.cV1 d).comp (Continuous.prodMk_right s)
lemma cV2θ (d : ℂ) (s : ℝ) : Continuous (fun θ : ℝ => S.V2 d (pt s θ)) :=
  (S.cV2 d).comp (Continuous.prodMk_right s)

lemma hasDerivAt_M (s₀ : ℝ) : HasDerivAt S.M (S.M1 s₀) s₀ := by
  have := alt_hasDerivAt_integral (F := fun s θ => S.V (pt s θ) ^ 2)
    (F' := fun s θ => 2 * S.V (pt s θ) * S.V1 1 (pt s θ))
    (S.cV.pow 2) ((continuous_const.mul S.cV).mul (S.cV1 1))
    (fun s θ => ((S.dV_s θ s).pow 2).congr_deriv (by ring)) 0 (2 * π) s₀
  exact this

lemma hasDerivAt_M1 (s₀ : ℝ) : HasDerivAt S.M1 (S.M2 s₀) s₀ := by
  have := alt_hasDerivAt_integral (F := fun s θ => 2 * S.V (pt s θ) * S.V1 1 (pt s θ))
    (F' := fun s θ => 2 * S.V1 1 (pt s θ) * S.V1 1 (pt s θ) +
      2 * S.V (pt s θ) * S.V2 1 (pt s θ))
    ((continuous_const.mul S.cV).mul (S.cV1 1))
    (((continuous_const.mul (S.cV1 1)).mul (S.cV1 1)).add
      ((continuous_const.mul S.cV).mul (S.cV2 1)))
    (fun s θ => ((((S.dV_s θ s).const_mul 2).mul (S.dV1_s θ s))).congr_deriv (by ring))
    0 (2 * π) s₀
  exact this

/-- Integration by parts in `θ`: `∫ V V_θθ = - ∫ V_θ²`. -/
lemma ibp (s : ℝ) :
    ∫ θ in (0:ℝ)..2 * π, S.V (pt s θ) * S.V2 Complex.I (pt s θ) = - S.T s := by
  have hd : ∀ θ ∈ uIcc (0:ℝ) (2 * π), HasDerivAt
      (fun θ => S.V (pt s θ) * S.V1 Complex.I (pt s θ))
      (S.V1 Complex.I (pt s θ) * S.V1 Complex.I (pt s θ) +
        S.V (pt s θ) * S.V2 Complex.I (pt s θ)) θ :=
    fun θ _ => (S.dV_θ s θ).mul (S.dV1_θ s θ)
  have hint := integral_eq_sub_of_hasDerivAt hd
    ((((S.cV1θ Complex.I s).mul (S.cV1θ Complex.I s)).add
      ((S.cVθ s).mul (S.cV2θ Complex.I s))).intervalIntegrable _ _)
  have hp0 : S.V (pt s (2 * π)) = S.V (pt s 0) := by
    have := S.V_pt_periodic s 0; simpa using this
  have hp1 : S.V1 Complex.I (pt s (2 * π)) = S.V1 Complex.I (pt s 0) := by
    have := S.V1_pt_periodic s 0; simpa using this
  rw [hp0, hp1, sub_self, intervalIntegral.integral_add] at hint
  · simp only [T, ← sq] at hint ⊢
    linarith
  · exact ((S.cV1θ Complex.I s).mul (S.cV1θ Complex.I s)).intervalIntegrable _ _
  · exact ((S.cVθ s).mul (S.cV2θ Complex.I s)).intervalIntegrable _ _

lemma M2_ge (s : ℝ) : 2 * S.E s + 2 * S.T s ≤ S.M2 s := by
  have hle : ∀ θ ∈ Icc (0:ℝ) (2 * π),
      2 * S.V1 1 (pt s θ) ^ 2 - 2 * (S.V (pt s θ) * S.V2 Complex.I (pt s θ)) ≤
      2 * S.V1 1 (pt s θ) * S.V1 1 (pt s θ) + 2 * S.V (pt s θ) * S.V2 1 (pt s θ) := by
    intro θ _
    have h1 := S.lap_nonneg (pt s θ)
    have h2 := S.V_nonneg (pt s θ)
    nlinarith [mul_nonneg h2 h1]
  have c1 := S.cV1θ 1 s
  have c2 := S.cVθ s
  have c3 := S.cV2θ Complex.I s
  have c4 := S.cV2θ 1 s
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by positivity : (0:ℝ) ≤ 2 * π)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) hle
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, S.ibp s] at hmono
  · simp only [M2, E] at hmono ⊢
    linarith
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma E_nonneg (s : ℝ) : 0 ≤ S.E s :=
  intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _)
lemma T_nonneg (s : ℝ) : 0 ≤ S.T s :=
  intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _)
lemma M_nonneg (s : ℝ) : 0 ≤ S.M s :=
  intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _)

lemma M2_nonneg (s : ℝ) : 0 ≤ S.M2 s := by
  have := S.M2_ge s
  have := S.E_nonneg s
  have := S.T_nonneg s
  linarith

/-- Wirtinger: a zero on the circle gives `T ≥ M/4`. -/
lemma T_ge {s θ₀ : ℝ} (h0 : S.V (pt s θ₀) = 0) : S.M s / 4 ≤ S.T s := by
  have hb : S.V (pt s (θ₀ + 2 * π)) = 0 := by
    have := S.V_pt_periodic s θ₀
    simp only at this
    rw [this, h0]
  have hw := alt_wirtinger (S.cV1θ Complex.I s) (fun θ => S.dV_θ s θ) h0 hb
  have hp1 : Function.Periodic (fun θ : ℝ => S.V (pt s θ) ^ 2) (2 * π) := by
    intro θ; simp only [S.V_pt_periodic s θ]
  have hp2 : Function.Periodic (fun θ : ℝ => S.V1 Complex.I (pt s θ) ^ 2) (2 * π) := by
    intro θ; simp only [S.V1_pt_periodic s θ]
  rw [hp1.intervalIntegral_add_eq θ₀ 0, hp2.intervalIntegral_add_eq θ₀ 0, zero_add] at hw
  exact hw

/-- Cauchy–Schwarz: `M1² ≤ 4 M E`. -/
lemma M1_sq_le (s : ℝ) : S.M1 s ^ 2 ≤ 4 * S.M s * S.E s := by
  have hcs := alt_cauchy_schwarz (S.cVθ s) (S.cV1θ 1 s) (by positivity : (0:ℝ) ≤ 2 * π)
  have hM1 : S.M1 s = 2 * ∫ θ in (0:ℝ)..2 * π, S.V (pt s θ) * S.V1 1 (pt s θ) := by
    simp only [M1, mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  rw [hM1]
  simp only [M, E]
  nlinarith [hcs]

/-- `M` is bounded for `s ≤ 0`. -/
lemma M_bdd : ∃ B, ∀ s ≤ 0, S.M s ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    S.Vz_cont.continuousOn
  refine ⟨2 * π * B ^ 2, fun s hs => ?_⟩
  have hle : ∀ θ ∈ Icc (0:ℝ) (2 * π), S.V (pt s θ) ^ 2 ≤ B ^ 2 := by
    intro θ _
    have hmem : Complex.exp (pt s θ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
      simp only [pt, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]
      simp only [mul_zero, sub_zero, add_zero, zero_mul]
      exact Real.exp_le_one_iff.2 hs
    have h1 := hB _ hmem
    rw [Real.norm_eq_abs] at h1
    have h2 : |S.V (pt s θ)| ≤ B := h1
    nlinarith [abs_nonneg (S.V (pt s θ)), sq_abs (S.V (pt s θ))]
  have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by positivity : (0:ℝ) ≤ 2 * π)
    (((S.cVθ s).pow 2).intervalIntegrable _ _) intervalIntegrable_const hle
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
  exact this

/-- The main conclusion of Carleman's method. -/
theorem growth {z₁ : ℂ} (hz₁D : z₁ ∈ S.D) (hz₁0 : z₁ ≠ 0) (hU : 0 < S.U z₁)
    (hΦpos : ∀ t, 0 < t → 0 < S.Φ t)
    (hcross : ∃ r₀ : ℝ, ∀ r ≥ r₀, ∃ w : ℂ, ‖w‖ = r ∧ w ∉ S.D) :
    ∃ c > (0 : ℝ), ∃ r₁ : ℝ, ∀ r ≥ r₁, ∃ z ∈ S.D,
      ‖z‖ = r ∧ c * Real.sqrt r ≤ Real.log (‖S.g z‖ / S.K) := by
  obtain ⟨r₀, hr₀⟩ := hcross
  -- `M1 ≥ 0` everywhere
  obtain ⟨B, hB⟩ := S.M_bdd
  have hM1nn : ∀ s, 0 ≤ S.M1 s :=
    alt_deriv_nonneg_of_convex S.hasDerivAt_M S.hasDerivAt_M1 S.M2_nonneg hB
  have hMmono : Monotone S.M := monotone_of_hasDerivAt_nonneg S.hasDerivAt_M hM1nn
  -- positivity at `s₁`
  set s₁ := Real.log ‖z₁‖
  have hMs₁ : 0 < S.M s₁ := by
    have hθ := Complex.neg_pi_lt_arg z₁
    have hθ' := Complex.arg_le_pi z₁
    have hp : Function.Periodic (fun θ : ℝ => S.V (pt s₁ θ) ^ 2) (2 * π) := by
      intro θ; simp only [S.V_pt_periodic s₁ θ]
    have e := hp.intervalIntegral_add_eq 0 (Complex.arg z₁ - π)
    rw [zero_add] at e
    simp only [M]
    rw [e]
    apply alt_integral_pos ((S.cVθ s₁).pow 2) (fun _ => sq_nonneg _)
      (x := Complex.arg z₁) (by linarith [pi_pos]) (by linarith [pi_pos])
    have hpt1 : Complex.exp (pt s₁ (Complex.arg z₁)) = z₁ := by
      simp only [pt, s₁]; exact alt_exp_log_pt hz₁0
    have hv : S.V (pt s₁ (Complex.arg z₁)) = S.Φ (S.U z₁) := by
      rw [S.V_eq_of_mem (by rw [hpt1]; exact hz₁D), hpt1]
    show 0 < S.V (pt s₁ (Complex.arg z₁)) ^ 2
    rw [hv]
    exact pow_pos (hΦpos _ hU) 2
  -- the differential inequality for large `s`
  set s₀ := max s₁ (Real.log (max r₀ 1))
  have hpos : ∀ s ≥ s₀, 0 < S.M s := fun s hs =>
    lt_of_lt_of_le hMs₁ (hMmono (le_trans (le_max_left _ _) hs))
  have hineq : ∀ s ≥ s₀, S.M1 s ^ 2 + S.M s ^ 2 ≤ 2 * S.M s * S.M2 s := by
    intro s hs
    have hr : r₀ ≤ Real.exp s := by
      have h1 : Real.log (max r₀ 1) ≤ s := le_trans (le_max_right _ _) hs
      have h2 : max r₀ 1 ≤ Real.exp s := by
        rw [← Real.exp_log (show 0 < max r₀ 1 by positivity)]
        exact Real.exp_le_exp.2 h1
      exact le_trans (le_max_left _ _) h2
    obtain ⟨w, hwn, hwD⟩ := hr₀ _ hr
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwn; exact (Real.exp_pos s).ne' hwn.symm
    have hzero : S.V (pt s (Complex.arg w)) = 0 := by
      have e : pt s (Complex.arg w) = (Real.log ‖w‖ : ℂ) + (Complex.arg w : ℂ) * Complex.I := by
        rw [hwn, Real.log_exp]; rfl
      apply S.V_eq_of_not_mem
      rw [e, alt_exp_log_pt hw0]; exact hwD
    have hT := S.T_ge hzero
    have hM2 := S.M2_ge s
    have hCS := S.M1_sq_le s
    have hM := S.M_nonneg s
    have hE := S.E_nonneg s
    nlinarith [mul_le_mul_of_nonneg_left hM2 hM, mul_le_mul_of_nonneg_left hT hM]
  obtain ⟨c, hc, S₁, hS₁⟩ := alt_ode S.hasDerivAt_M S.hasDerivAt_M1 hpos
    (fun s _ => hM1nn s) hineq
  -- conclusion
  refine ⟨Real.sqrt (c / (2 * π)), Real.sqrt_pos.2 (by positivity),
    Real.exp (max S₁ 0), fun r hr => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le (Real.exp_pos _) hr
  set s := Real.log r with hsdef
  have hsS : S₁ ≤ s := by
    have := Real.log_le_log (Real.exp_pos _) hr
    rw [Real.log_exp] at this
    exact le_trans (le_max_left _ _) this
  have hMs := hS₁ s hsS
  rw [hsdef, Real.exp_log hr0] at hMs
  -- maximum on the circle
  obtain ⟨θs, hθs, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_isMaxOn
    (nonempty_Icc.2 (by positivity)) ((S.cVθ s).pow 2).continuousOn
  have hMle : S.M s ≤ 2 * π * S.V (pt s θs) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by positivity : (0:ℝ) ≤ 2 * π)
      (((S.cVθ s).pow 2).intervalIntegrable _ _) intervalIntegrable_const
      (fun θ hθ => (isMaxOn_iff.1 hmax) θ hθ)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    exact this
  set v := S.V (pt s θs)
  have hv0 : 0 ≤ v := S.V_nonneg _
  have hsq : c * r / (2 * π) ≤ v ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hkey : Real.sqrt (c / (2 * π)) * Real.sqrt r ≤ v := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq hv0]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div]; exact hsq
  have hvpos : 0 < v := lt_of_lt_of_le (by positivity) hkey
  have hzD : Complex.exp (pt s θs) ∈ S.D := by
    by_contra hz
    have : v = 0 := S.V_eq_of_not_mem hz
    linarith
  refine ⟨Complex.exp (pt s θs), hzD, ?_, ?_⟩
  · simp only [Complex.norm_exp, pt, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero, zero_mul]
    rw [hsdef, Real.exp_log hr0]
  · have hvz : v = S.Φ (S.U (Complex.exp (pt s θs))) := S.V_eq_of_mem hzD
    have hUpos : 0 < S.U (Complex.exp (pt s θs)) := by
      by_contra hn
      push Not at hn
      rw [S.hΦ0 _ hn] at hvz
      linarith
    have := S.hΦle _ hUpos
    simp only [U] at this hvz
    linarith [S.hε]

end alt_CData

/-- Points outside the tract have a neighbourhood outside the tract or where `u < ε`. -/
lemma alt_tract_loc {g : ℂ → ℂ} (hg : Continuous g) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    {z₀ z : ℂ} (hz : z ∉ tract g K z₀) :
    ∀ᶠ z' in 𝓝 z, z' ∉ tract g K z₀ ∨ Real.log (‖g z'‖ / K) - ε < 0 := by
  by_cases hgz : K < ‖g z‖
  · have hopen := isOpen_tract hg K z
    filter_upwards [hopen.mem_nhds (mem_tract_self hgz)] with z' hz'
    left
    intro hz'D
    apply hz
    have h1 : tract g K z = tract g K z' := connectedComponentIn_eq hz'
    have h2 : tract g K z₀ = tract g K z' := connectedComponentIn_eq hz'D
    rw [h2, ← h1]
    exact mem_tract_self hgz
  · push Not at hgz
    have hlt : ‖g z‖ < K * Real.exp ε := by
      have : K < K * Real.exp ε := by
        have := Real.one_lt_exp_iff.2 hε
        nlinarith
      linarith
    have hopen : IsOpen {z' | ‖g z'‖ < K * Real.exp ε} :=
      isOpen_lt (continuous_norm.comp hg) continuous_const
    filter_upwards [hopen.mem_nhds hlt] with z' hz'
    right
    by_cases h0 : ‖g z'‖ = 0
    · rw [h0, zero_div, Real.log_zero]; linarith
    · have hpos : 0 < ‖g z'‖ / K := div_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hK
      have : ‖g z'‖ / K < Real.exp ε := by rwa [div_lt_iff₀ hK, mul_comm]
      have := Real.log_lt_log hpos this
      rw [Real.log_exp] at this
      linarith

theorem carleman_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ} (hK : 0 < K) {z₀ : ℂ}
    (hz₀ : K < ‖g z₀‖)
    (hcross : ∃ r₀ : ℝ, ∀ r ≥ r₀, ∃ w : ℂ, ‖w‖ = r ∧ w ∉ tract g K z₀) :
    ∃ c > (0 : ℝ), ∃ r₁ : ℝ, ∀ r ≥ r₁, ∃ z ∈ tract g K z₀,
      ‖z‖ = r ∧ c * Real.sqrt r ≤ Real.log (‖g z‖ / K) := by
  obtain ⟨Φ, Φ1, Φ2, hΦ2c, hΦ, hΦ1, hΦ2nn, hΦ0, hΦ10, hΦpos, hΦnn⟩ := alt_phi_exists
  have hDopen := isOpen_tract hg.continuous K z₀
  have hz₀D := mem_tract_self hz₀
  -- a nonzero point of the tract
  obtain ⟨z₁, hz₁D, hz₁0⟩ : ∃ z₁ ∈ tract g K z₀, z₁ ≠ 0 := by
    by_cases h0 : z₀ = 0
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hDopen z₀ hz₀D
      refine ⟨z₀ + ((δ / 2 : ℝ) : ℂ), hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      · rw [h0, zero_add]
        exact_mod_cast (show (δ / 2 : ℝ) ≠ 0 by positivity)
    · exact ⟨z₀, hz₀D, h0⟩
  have hgz₁ : K < ‖g z₁‖ := tract_subset_superlevel g K z₀ hz₁D
  set ε := Real.log (‖g z₁‖ / K) / 2 with hε
  have hlog : 0 < Real.log (‖g z₁‖ / K) :=
    Real.log_pos (by rw [one_lt_div hK]; exact hgz₁)
  have hεpos : 0 < ε := by positivity
  let S : alt_CData :=
    { g := g, K := K, ε := ε, D := tract g K z₀, Φ := Φ, Φ1 := Φ1, Φ2 := Φ2,
      hg := hg, hK := hK, hε := hεpos, hDopen := hDopen,
      hDpos := fun z hz => tract_subset_superlevel g K z₀ hz,
      hloc := fun z hz => alt_tract_loc hg.continuous hK hεpos hz,
      hΦ := hΦ, hΦ1 := hΦ1, hΦ2c := hΦ2c, hΦ0 := hΦ0,
      hΦ10 := fun t ht => (hΦ10 t ht).1, hΦ20 := fun t ht => (hΦ10 t ht).2,
      hΦ2nn := hΦ2nn, hΦnn := hΦnn, hΦle := fun t ht => (hΦpos t ht).2 }
  have hU : 0 < S.U z₁ := by
    show 0 < Real.log (‖g z₁‖ / K) - ε
    rw [hε]; linarith
  exact S.growth hz₁D hz₁0 hU (fun t ht => (hΦpos t ht).1) hcross

end Erdos514
