import ErdosLean.Erdos514.Parts.ShiftEq
import ErdosLean.Erdos514.Parts.ShiftDifferentiable
import ErdosLean.Erdos514.Parts.ShiftTranscendental
import ErdosLean.Erdos514.Parts.SuperlevelFar
import ErdosLean.Erdos514.Parts.TractGrowth

/-! # Erdős #514 — Part: a nested chain of tracts of the Taylor shifts

Write `gₙ = shift f n`, `aₙ = gₙ 0`, so `gₙ z = aₙ + z g_{n+1} z` (`shift_eq_add_mul`).
Choose levels first: `K n ≥ 1`, `K (n+1) ≥ K n + ‖a_{n+1}‖`, and
`superlevel g_{n+1} (K n) ⊆ {n < ‖z‖}` (`superlevel_subset_far`).  Then for `‖z‖ ≥ 1`,
`K (n+1) < ‖g_{n+2} z‖ ⇒ K n < ‖g_{n+1} z‖`, i.e.
`superlevel g_{n+2} (K (n+1)) ⊆ superlevel g_{n+1} (K n)`.
Put `D n = tract g_{n+1} (K n) (zₙ)` with points chosen recursively:
`z₀` with `K 0 < ‖g₁ z₀‖` (`g₁` is non-constant, hence unbounded by Liouville), and
`z_{n+1} ∈ D n` with `K (n+1) < ‖g_{n+2} z_{n+1}‖`, which exists by `tract_growth`
applied to `g_{n+1}` with `A = K (n+1) + ‖a_{n+1}‖`.
`D (n+1) ⊆ D n` by `IsPreconnected.subset_connectedComponentIn`. -/

namespace Erdos514

theorem nested_chain {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) :
    ∃ D : ℕ → Set ℂ, (∀ n, IsOpen (D n) ∧ IsPreconnected (D n) ∧ (D n).Nonempty) ∧
      (∀ n, D (n + 1) ⊆ D n) ∧
      (∀ n, ∀ z ∈ D n, (n : ℝ) < ‖z‖ ∧ 1 < ‖shift f (n + 1) z‖) := by
  have hcont : ∀ n, Continuous (shift f n) := fun n =>
    (shift_differentiable hf.1 n).continuous
  have hT : ∀ n, IsTranscendentalEntire (shift f n) := shift_transcendental hf
  have hsf : ∀ (n : ℕ) (K₀ : ℝ), ∃ K : ℝ, K₀ ≤ K ∧
      superlevel (shift f (n+1)) K ⊆ {z | (n:ℝ) < ‖z‖} :=
    fun n K₀ => superlevel_subset_far (hcont (n+1)) n K₀
  choose Kf hKf1 hKf2 using hsf
  let K : ℕ → ℝ := fun n => Nat.rec (motive := fun _ => ℝ) (Kf 0 1)
    (fun m Km => Kf (m+1) (Km + ‖shift f (m+1) 0‖)) n
  have hK0 : K 0 = Kf 0 1 := rfl
  have hKs : ∀ n, K (n+1) = Kf (n+1) (K n + ‖shift f (n+1) 0‖) := fun n => rfl
  have hKstep : ∀ n, K n + ‖shift f (n+1) 0‖ ≤ K (n+1) := fun n => by
    rw [hKs]; exact hKf1 _ _
  have hK1 : ∀ n, 1 ≤ K n := by
    intro n
    induction n with
    | zero => rw [hK0]; exact hKf1 _ _
    | succ n ih => linarith [hKstep n, norm_nonneg (shift f (n+1) 0)]
  have hfar : ∀ n, superlevel (shift f (n+1)) (K n) ⊆ {z | (n:ℝ) < ‖z‖} := by
    intro n
    cases n with
    | zero => exact hKf2 _ _
    | succ n => rw [hKs]; exact hKf2 _ _
  have hincl : ∀ n, superlevel (shift f (n+2)) (K (n+1)) ⊆ superlevel (shift f (n+1)) (K n) := by
    intro n z hz
    have hz1 : ((n+1 : ℕ) : ℝ) < ‖z‖ := hfar (n+1) hz
    have hz1' : 1 ≤ ‖z‖ := by
      push_cast at hz1; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hz' : K (n+1) < ‖shift f (n+2) z‖ := hz
    have heq : shift f (n+1) z = shift f (n+1) 0 + z * shift f (n+2) z :=
      shift_eq_add_mul f (n+1) z
    have h1 : ‖z * shift f (n+2) z‖ ≤ ‖shift f (n+1) z‖ + ‖shift f (n+1) 0‖ := by
      have : z * shift f (n+2) z = shift f (n+1) z - shift f (n+1) 0 := by rw [heq]; ring
      rw [this]; exact norm_sub_le _ _
    rw [norm_mul] at h1
    have h2 : ‖shift f (n+2) z‖ ≤ ‖z‖ * ‖shift f (n+2) z‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hz1'
    show K n < ‖shift f (n+1) z‖
    linarith [hKstep n]
  have hz0 : ∃ w, K 0 < ‖shift f 1 w‖ := by
    by_contra h
    push Not at h
    have hb : Bornology.IsBounded (Set.range (shift f 1)) := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      exact ⟨K 0, by rintro _ ⟨w, rfl⟩; simpa using h w⟩
    apply (hT 1).2
    refine ⟨Polynomial.C (shift f 1 0), fun z => ?_⟩
    rw [Polynomial.eval_C]
    exact (hT 1).1.apply_eq_apply_of_bounded hb z 0
  have step : ∀ n (w : ℂ), ∃ z : ℂ, K n < ‖shift f (n+1) w‖ →
      z ∈ tract (shift f (n+1)) (K n) w ∧ K (n+1) < ‖shift f (n+2) z‖ := by
    intro n w
    by_cases hw : K n < ‖shift f (n+1) w‖
    · obtain ⟨z, hzt, hz⟩ := tract_growth (hT (n+1)) (by linarith [hK1 n]) hw
        (K (n+1) + ‖shift f (n+1) 0‖)
      refine ⟨z, fun _ => ⟨hzt, ?_⟩⟩
      by_contra hle
      push Not at hle
      have heq : shift f (n+1) z = shift f (n+1) 0 + z * shift f (n+2) z :=
        shift_eq_add_mul f (n+1) z
      have h1 : ‖shift f (n+1) z‖ ≤ ‖shift f (n+1) 0‖ + ‖z‖ * ‖shift f (n+2) z‖ := by
        rw [heq, ← norm_mul]; exact norm_add_le _ _
      have h2 : ‖z‖ * ‖shift f (n+2) z‖ ≤ ‖z‖ * K (n+1) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      have h3 : 0 ≤ ‖shift f (n+1) 0‖ * ‖z‖ := by positivity
      nlinarith [hK1 (n+1), norm_nonneg z]
    · exact ⟨w, fun h => absurd h hw⟩
  choose F hF using step
  obtain ⟨w0, hw0⟩ := hz0
  let z : ℕ → ℂ := fun n => Nat.rec (motive := fun _ => ℂ) w0 (fun m zm => F m zm) n
  have hzs : ∀ n, z (n+1) = F n (z n) := fun n => rfl
  have hinv : ∀ n, K n < ‖shift f (n+1) (z n)‖ := by
    intro n
    induction n with
    | zero => exact hw0
    | succ n ih => rw [hzs]; exact (hF n (z n) ih).2
  refine ⟨fun n => tract (shift f (n+1)) (K n) (z n),
    fun n => ⟨isOpen_tract (hcont _) _ _, isPreconnected_tract _ _ _,
      ⟨z n, mem_tract_self (hinv n)⟩⟩, ?_, ?_⟩
  · intro n
    have hmem : z (n+1) ∈ connectedComponentIn (superlevel (shift f (n+1)) (K n)) (z n) := by
      rw [hzs]; exact (hF n (z n) (hinv n)).1
    have hsub : tract (shift f (n+1+1)) (K (n+1)) (z (n+1)) ⊆
        superlevel (shift f (n+1)) (K n) :=
      (tract_subset_superlevel _ _ _).trans (hincl n)
    have := (isPreconnected_tract (shift f (n+1+1)) (K (n+1)) (z (n+1))).subset_connectedComponentIn
      (mem_tract_self (hinv (n+1))) hsub
    show tract _ _ _ ⊆ connectedComponentIn (superlevel (shift f (n+1)) (K n)) (z n)
    rw [connectedComponentIn_eq hmem]
    exact this
  · intro n w hw
    have h1 : K n < ‖shift f (n+1) w‖ := tract_subset_superlevel _ _ _ hw
    exact ⟨hfar n h1, by linarith [hK1 n]⟩

end Erdos514
