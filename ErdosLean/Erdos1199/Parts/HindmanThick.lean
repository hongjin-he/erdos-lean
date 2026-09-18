import ErdosLean.Erdos1199.Defs
import ErdosLean.Erdos1199.Parts.HindmanLocal

/-!
# Erdős #1199 — Part 13: a thick colour class forces a monochromatic `B + B`

Paper: arXiv:2607.17333, Proposition A.2 with `m = ℓ = 1` (Hindman 1979, Cor. 2.10, for thick
partitions).
-/

namespace Erdos1199

/-- `a` is *good* (for colour `γ₀` and length `L`): the even block `{2(a+s) : s < L}` contains at
most one point of colour `γ₀`. -/
private def HTGood (c : ℕ → Bool) (γ₀ : Bool) (L a : ℕ) : Prop :=
  ((Finset.range L).filter (fun s => c (2 * (a + s)) = γ₀)).card ≤ 1

/-- Proposition A.2 (`m = ℓ = 1`): if the colour class `c⁻¹(γ₀)` contains arbitrarily long
intervals arbitrarily far to the right, then some infinite `B ⊆ ℕ` has `B + B`
monochromatic. -/
theorem hindman_thick (c : ℕ → Bool) (γ₀ : Bool)
    (hthick : ∀ L N : ℕ, ∃ n, N ≤ n ∧ ∀ j ≤ L, c (n + j) = γ₀) :
    ∃ B : Set ℕ, B.Infinite ∧ IsMonoSumset c B := by
  classical
  by_contra hcon
  have hno : ∀ j : Bool, ¬ ∃ B : Set ℕ, B.Infinite ∧ ∀ x ∈ B, ∀ y ∈ B, c (x + y) = j :=
    fun j ⟨B, hB, h⟩ => hcon ⟨B, hB, j, h⟩
  obtain ⟨C₀, hC₀⟩ := hindman_local c γ₀ (hno γ₀)
  obtain ⟨C₁, hC₁⟩ := hindman_local c (!γ₀) (hno (!γ₀))
  simp only [Bool.not_not] at hC₁
  obtain ⟨L, hL⟩ : ∃ L, L = C₁ + 1 := ⟨_, rfl⟩
  -- Step 1: long even blocks of colour `γ₀`
  have hblk : ∀ N M : ℕ, ∃ K, N ≤ K ∧ ∀ s < M, c (2 * (K + s)) = γ₀ := by
    intro N M
    obtain ⟨n, hn, hc⟩ := hthick (2 * M) (2 * N)
    refine ⟨(n + 1) / 2, by omega, fun s hs => ?_⟩
    have := hc (2 * ((n + 1) / 2 + s) - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  choose blk hblkN hblkc using hblk
  obtain ⟨K, hKc, hK0, hKs⟩ : ∃ K : ℕ → ℕ,
      (∀ n, ∀ s < n + L + C₀ + 1, c (2 * (K n + s)) = γ₀) ∧ C₀ + C₁ + 1 ≤ K 0 ∧
        ∀ n, L + 3 + 2 * K n ≤ K (n + 1) := by
    refine ⟨fun n => Nat.rec (motive := fun _ => ℕ) (blk (C₀ + C₁ + 1) (0 + L + C₀ + 1))
      (fun n Kn => blk (L + 3 + 2 * Kn) (n + 1 + L + C₀ + 1)) n, fun n => ?_,
      hblkN _ _, fun n => hblkN _ _⟩
    cases n <;> exact hblkc _ _
  have hKlb : ∀ n, C₀ + C₁ + 1 ≤ K n := by
    intro n; induction n with
    | zero => exact hK0
    | succ n ih => have := hKs n; omega
  -- Step 2: `X_n = 2 K_n + 1` is good
  have hX : ∀ n, HTGood c γ₀ L (2 * K n + 1) := by
    intro n
    unfold HTGood
    have : (Finset.range L).filter (fun s => c (2 * (2 * K n + 1 + s)) = γ₀) = ∅ := by
      apply Finset.filter_false_of_mem
      intro s hs
      have hs' := Finset.mem_range.1 hs
      have hKn := hKlb n
      have hcard : ((Finset.range (n + L + C₀ + 1)).filter
          (fun s => c (2 * (K n + s)) = !γ₀)).card ≤ 1 := by
        rw [Finset.filter_false_of_mem]
        · simp
        · intro t ht
          simp [hKc n t (Finset.mem_range.1 ht)]
      have h := hC₀ (K n) (n + L + C₀ + 1) (2 * K n + 1 + s) hcard (by omega) (by omega)
        (by omega)
      simp [h]
    rw [this]; simp
  -- Step 3: `a_n` = greatest good integer below `K_{n+1}`
  obtain ⟨a, ha_good, ha_lt, ha_ge, ha_max⟩ : ∃ a : ℕ → ℕ, (∀ n, HTGood c γ₀ L (a n)) ∧
      (∀ n, a n < K (n + 1)) ∧ (∀ n, 2 * K n + 1 ≤ a n) ∧
      (∀ n b, a n < b → b < K (n + 1) → ¬ HTGood c γ₀ L b) := by
    refine ⟨fun n => Nat.findGreatest (HTGood c γ₀ L) (K (n + 1) - 1), fun n => ?_, fun n => ?_,
      fun n => ?_, fun n b h1 h2 => ?_⟩
    · have := hKs n
      exact Nat.findGreatest_spec (P := HTGood c γ₀ L) (m := 2 * K n + 1) (by omega) (hX n)
    · have := hKs n
      have := Nat.findGreatest_le (P := HTGood c γ₀ L) (K (n + 1) - 1)
      show Nat.findGreatest (HTGood c γ₀ L) (K (n + 1) - 1) < K (n + 1)
      omega
    · have := hKs n
      exact Nat.le_findGreatest (P := HTGood c γ₀ L) (by omega) (hX n)
    · exact Nat.findGreatest_is_greatest h1 (by omega)
  -- Step 4: `z_n = 2 a_n + 1`
  have hz : ∀ n, ∀ s < L, c (2 * (2 * a n + 1 + s)) = γ₀ := by
    intro n s hs
    have h1 := ha_ge n
    have h2 := hKlb n
    exact hC₁ (a n) L (2 * a n + 1 + s) (ha_good n) (by omega) (by omega) (by omega)
  have hamono : StrictMono a := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have := ha_lt n
    have := ha_ge (n + 1)
    omega
  let z : ℕ → ℕ := fun n => 2 * a n + 1
  have hzmono : StrictMono z := fun m n h => by
    have := hamono h
    show 2 * a m + 1 < 2 * a n + 1
    omega
  -- Step 5: Ramsey
  obtain ⟨τ, u, hu, -, hχ⟩ := ramsey_pairs (κ := Fin L → Bool)
    (fun r t => fun s : Fin L => c (z r + z t + 2 * (s : ℕ))) Set.univ Set.infinite_univ
  by_cases hτ : ∃ s : Fin L, τ s = γ₀
  · obtain ⟨s, hs⟩ := hτ
    apply hno γ₀
    refine ⟨Set.range (fun i => z (u i) + s), Set.infinite_range_of_injective ?_, ?_⟩
    · intro i k hik
      exact (hzmono.comp hu).injective (by simpa using hik)
    · rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
      rcases lt_trichotomy i k with h | rfl | h
      · have := congrFun (hχ i k h) s
        rw [← hs, ← this]
        congr 1; ring
      · have := hz (u i) s s.2
        rw [← this]
        congr 1; simp only [z]; ring
      · have := congrFun (hχ k i h) s
        rw [← hs, ← this]
        congr 1; ring
  · simp only [not_exists] at hτ
    -- Step 6
    set D := a (u 0) + 1 with hD
    set n := u (D + 1) with hn
    have hnD : D + 1 ≤ n := hu.id_le (D + 1)
    set α := a n + D with hα
    have hcol : ∀ s < L, c (2 * (α + s)) ≠ γ₀ := by
      intro s hs
      have := congrFun (hχ 0 (D + 1) (by omega)) ⟨s, hs⟩
      simp only at this
      have e : z (u 0) + z (u (D + 1)) + 2 * s = 2 * (α + s) := by
        simp only [z, hα, hD, hn]; ring
      rw [← e, this]
      exact hτ _
    have hgood : HTGood c γ₀ L α := by
      unfold HTGood
      rw [Finset.filter_false_of_mem]
      · simp
      · intro s hs
        exact hcol s (Finset.mem_range.1 hs)
    have hge : K (n + 1) ≤ α := by
      by_contra hlt
      exact ha_max n α (by omega) (by omega) hgood
    have hlt := ha_lt n
    have hmem := hKc (n + 1) (α - K (n + 1)) (by omega)
    rw [Nat.add_sub_cancel' hge] at hmem
    have hL1 : 0 < L := by omega
    exact hcol 0 hL1 (by simpa using hmem)

end Erdos1199
