import ErdosLean.Erdos790.Defs

/-! Part: relating the `sSup` definition of `l` to universal bounds. -/

namespace Erdos790

/-- Every admissible `k` is at most `n`. -/
theorem l_set_upper (n : ℕ) :
    n ∈ upperBounds {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ k ≤ B.card} := by
  intro k hk
  have hA : ((Finset.range n).image (fun i : ℕ => (i : ℤ))).card = n := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨B, hBA, -, hkB⟩ := hk _ hA
  exact hkB.trans ((Finset.card_le_card hBA).trans hA.le)

/-- A universal bound `n ≤ M |B|` transfers to `n ≤ M l(n)`. -/
theorem l_lower_of (n M : ℕ) (hM : 0 < M)
    (h : ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ n ≤ M * B.card) :
    n ≤ M * l n := by
  set k0 := (n + M - 1) / M with hk0
  have hmem : k0 ∈ {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ k ≤ B.card} := by
    intro A hA
    obtain ⟨B, hBA, hB, hnB⟩ := h A hA
    refine ⟨B, hBA, hB, ?_⟩
    rw [hk0, Nat.div_le_iff_le_mul_add_pred hM]
    omega
  have hle : k0 ≤ l n := le_csSup ⟨n, l_set_upper n⟩ hmem
  have h1 := Nat.div_add_mod (n + M - 1) M
  have h2 := Nat.mod_lt (n + M - 1) hM
  rw [← hk0] at h1
  have h3 : M * k0 ≤ M * l n := Nat.mul_le_mul_left M hle
  generalize M * k0 = x at h1 h3
  omega

/-- Trivial upper bound. -/
theorem l_le_self (n : ℕ) : l n ≤ n :=
  csSup_le' (l_set_upper n)

end Erdos790
