import ErdosLean.Erdos1199.Parts.DiagonalRecursion

/-!
# Erdős #1199 — Part 4: the key identity `(p+p)𝐜 = J (D p) 𝐜`

Paper: arXiv:2607.17333, Proposition 3.2 (with Lemma 3.3).
-/

namespace Erdos1199

open Filter

/-- Core of Proposition 3.2: if some colour class `A` of the sampled sequence
`n ↦ ext2 b (R + s n)` lies in both `p + p` and `D p`, then `b` has the Owings property. -/
theorem owings_of_mem_add_mem_dbl (b : ℕ → Bool) {p : Ultrafilter ℕ} (hp : Nonprincipal p)
    (R s : ℤ) (hs : 1 ≤ s) (γ : Bool)
    (h1 : {n : ℕ | ext2 b (R + s * (n : ℤ)) = γ} ∈ p + p)
    (h2 : {n : ℕ | ext2 b (R + s * (n : ℤ)) = γ} ∈ dbl p) : Owings b := by
  obtain ⟨v, hv, hvA⟩ := diagonal_recursion hp h1 h2
  set i0 : ℕ := (-R).toNat + 1 with hi0
  let f : ℕ → ℤ := fun i => 2 * (s * (v (i + i0) : ℤ)) + R
  have hvge : ∀ i, i ≤ v i := hv.id_le
  have fpos : ∀ i, 0 < f i := by
    intro i
    have h := hvge (i + i0)
    have h' : ((i + i0 : ℕ) : ℤ) ≤ (v (i + i0) : ℤ) := by exact_mod_cast h
    have h'' : (v (i + i0) : ℤ) ≤ s * (v (i + i0) : ℤ) := by
      have : (0 : ℤ) ≤ (v (i + i0) : ℤ) := by positivity
      nlinarith
    simp only [f]
    omega
  have fmono : StrictMono f := by
    intro i j hij
    have h := hv (show i + i0 < j + i0 by omega)
    have h' : (v (i + i0) : ℤ) < v (j + i0) := by exact_mod_cast h
    simp only [f]
    nlinarith
  refine ⟨Set.range (fun i => (f i).toNat), ?_, ?_, γ, ?_⟩
  · apply Set.infinite_range_of_injective
    intro i j hij
    apply fmono.injective
    have := fpos i
    have := fpos j
    simp only at hij
    omega
  · rintro _ ⟨i, rfl⟩
    have := fpos i
    show 0 < (f i).toNat
    omega
  · have key : ∀ i j, i ≤ j → b ((f i).toNat + (f j).toNat) = γ := by
      intro i j hij
      have hA := hvA (i + i0) (j + i0) (by omega)
      simp only [Set.mem_ofPred_eq, ext2] at hA
      rw [← hA]
      congr 1
      have hi := fpos i
      have hj := fpos j
      simp only [f] at hi hj ⊢
      push_cast
      rw [mul_add]
      generalize s * (v (i + i0) : ℤ) = a at hi hj ⊢
      generalize s * (v (j + i0) : ℤ) = c at hi hj ⊢
      omega
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rcases le_total i j with h | h
    · exact key i j h
    · rw [add_comm]; exact key j i h

/-- Proposition 3.2: if `b` has no infinite set of positive integers with monochromatic `B + B`,
then for `c(n) = b(2n)` and every nonprincipal `p`, `(p + p) · 𝐜 = J ((D p) · 𝐜)`. -/
theorem key_identity (b : ℕ → Bool) (hb : ¬ Owings b) {p : Ultrafilter ℕ}
    (hp : Nonprincipal p) :
    act (p + p) (encode (ext2 b)) = cmpl (act (dbl p) (encode (ext2 b))) := by
  funext i
  obtain ⟨k, R⟩ := i
  have hs : (1 : ℤ) ≤ stride (k, R) := by
    simp only [stride]; omega
  have hT : ∀ γ : Bool, {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = γ} ∈ p + p →
      {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = γ} ∈ dbl p → False :=
    fun γ h1 h2 => hb (owings_of_mem_add_mem_dbl b hp R _ hs γ h1 h2)
  have hcompl : ∀ q : Ultrafilter ℕ,
      {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = true} ∉ q →
      {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = false} ∈ q := by
    intro q hq
    have := (Ultrafilter.compl_mem_iff_notMem (f := q)).2 hq
    convert this using 1
    ext n
    simp
  simp only [act, cmpl, encode]
  by_cases h1 : {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = true} ∈ p + p <;>
    by_cases h2 : {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = true} ∈ dbl p
  · exact (hT true h1 h2).elim
  · simp [h1, h2]
  · simp [h1, h2]
  · exact (hT false (hcompl _ h1) (hcompl _ h2)).elim

end Erdos1199
