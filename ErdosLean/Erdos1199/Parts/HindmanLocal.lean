import ErdosLean.Erdos1199.Parts.Ramsey

/-!
# Erdős #1199 — Part 12: Hindman's local lemma (`m = ℓ = 1`)

Paper: arXiv:2607.17333, Lemma A.1 with `m = ℓ = 1`, so `Q(K, M) = {2(K+s) : s < M}`.
-/

namespace Erdos1199

/-- Lemma A.1 (`m = ℓ = 1`): if no infinite `B` has `B + B ⊆ c⁻¹(j)`, there is `C` such that
whenever the even block `Q(K, M) = {2(K+s) : s < M}` contains at most one point of colour `¬j`,
and `C < x`, `2K < x`, `x + C < 2(K + M)`, then `c(2x) = ¬j`. -/
theorem hindman_local (c : ℕ → Bool) (j : Bool)
    (hno : ¬ ∃ B : Set ℕ, B.Infinite ∧ ∀ x ∈ B, ∀ y ∈ B, c (x + y) = j) :
    ∃ C : ℕ, ∀ K M x : ℕ,
      ((Finset.range M).filter (fun s => c (2 * (K + s)) = !j)).card ≤ 1 →
      C < x → 2 * K < x → x + C < 2 * (K + M) → c (2 * x) = !j := by
  by_contra hcon
  push Not at hcon
  choose K M X hcard hC hK hM hc using hcon
  let idx : ℕ → ℕ := fun r => Nat.rec 0 (fun _ i => X i + 1) r
  have hidx_succ : ∀ r, idx (r + 1) = X (idx r) + 1 := fun r => rfl
  let x : ℕ → ℕ := fun r => X (idx r)
  have hlt : ∀ r, idx r < x r := fun r => hC _
  have hidx_mono : StrictMono idx := strictMono_nat_of_lt_succ (fun r => by
    rw [hidx_succ]; have := hlt r; simp only [x] at this; omega)
  have key : ∀ t r, t < r → x t < idx r := fun t r htr => by
    have h1 : idx (t + 1) ≤ idx r := hidx_mono.monotone htr
    rw [hidx_succ] at h1; simp only [x]; omega
  have xmono : StrictMono x := fun t r htr => lt_trans (key t r htr) (hlt r)
  have hcj : ∀ r, c (2 * x r) = j := fun r => by
    have := hc (idx r)
    simp only [x]
    cases h : c (2 * X (idx r)) <;> cases j <;> simp_all
  obtain ⟨⟨k1, k2⟩, u, hu, -, hhom⟩ := ramsey_pairs (κ := Bool × Bool)
    (fun t r => (c (x t + x r), decide (Even (x t + x r)))) Set.univ Set.infinite_univ
  simp only [Prod.mk.injEq] at hhom
  cases k2
  · have h01 := (hhom 0 1 (by norm_num)).2
    have h12 := (hhom 1 2 (by norm_num)).2
    have h02 := (hhom 0 2 (by norm_num)).2
    simp only [decide_eq_false_iff_not, Nat.not_even_iff_odd, Nat.odd_iff] at h01 h12 h02
    omega
  · by_cases hk : k1 = j
    · apply hno
      refine ⟨Set.range (x ∘ u), Set.infinite_range_of_injective (xmono.comp hu).injective, ?_⟩
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rcases lt_trichotomy a b with hab | rfl | hab
      · exact (hhom a b hab).1.trans hk
      · simp only [Function.comp_apply]; rw [← two_mul]; exact hcj _
      · simp only [Function.comp_apply]; rw [add_comm]; exact (hhom b a hab).1.trans hk
    · have hk' : k1 = !j := by cases k1 <;> cases j <;> simp_all
      obtain ⟨c02, e02⟩ := hhom 0 2 (by norm_num)
      obtain ⟨c12, e12⟩ := hhom 1 2 (by norm_num)
      simp only [decide_eq_true_eq] at e02 e12
      obtain ⟨m1, hm1⟩ := e02
      obtain ⟨m2, hm2⟩ := e12
      have hab : x (u 0) < x (u 1) := xmono (hu (by norm_num))
      have k0 := key (u 0) (u 2) (hu (by norm_num))
      have k1' := key (u 1) (u 2) (hu (by norm_num))
      have hK2 := hK (idx (u 2))
      have hM2 := hM (idx (u 2))
      have hcard2 := hcard (idx (u 2))
      set KK := K (idx (u 2))
      set MM := M (idx (u 2))
      have hxr : X (idx (u 2)) = x (u 2) := rfl
      rw [hxr] at hK2 hM2
      set I := idx (u 2)
      have mem1 : m1 - KK ∈ (Finset.range MM).filter (fun s => c (2 * (KK + s)) = !j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : 2 * (KK + (m1 - KK)) = x (u 0) + x (u 2) := by omega
        rw [this, c02, hk']
      have mem2 : m2 - KK ∈ (Finset.range MM).filter (fun s => c (2 * (KK + s)) = !j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : 2 * (KK + (m2 - KK)) = x (u 1) + x (u 2) := by omega
        rw [this, c12, hk']
      have hne : m1 - KK ≠ m2 - KK := by omega
      have := Finset.one_lt_card.mpr ⟨_, mem1, _, mem2, hne⟩
      omega

end Erdos1199
