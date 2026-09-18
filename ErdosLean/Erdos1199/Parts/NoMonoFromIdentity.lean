import ErdosLean.Erdos1199.Parts.UltraBasics

/-!
# Erdős #1199 — Part 10: the identity `(p+p)h = J (D p) h` forbids monochromatic `B + B`

Paper: arXiv:2607.17333, Proposition 3.7(i).
-/

namespace Erdos1199

open Filter

/-- If for every `p ∈ ℕ*` exactly one of `p + p`, `D p` contains `{n | h n = true}`, then no
infinite `B ⊆ ℕ` has `B + B` monochromatic under `h`. -/
theorem no_mono_of_identity (h : ℕ → Bool)
    (hid : ∀ p : Ultrafilter ℕ, Nonprincipal p →
      ({n : ℕ | h n = true} ∈ p + p ↔ {n : ℕ | h n = true} ∉ dbl p)) :
    ¬ ∃ B : Set ℕ, B.Infinite ∧ IsMonoSumset h B := by
  rintro ⟨B, hB, γ, hγ⟩
  obtain ⟨p, hp, hBp⟩ := exists_nonprincipal_mem hB
  have hD : {n : ℕ | h n = γ} ∈ dbl p := by
    rw [mem_dbl_iff]
    exact Filter.mem_of_superset hBp fun n hn => by
      show h (2 * n) = γ
      rw [two_mul]; exact hγ n hn n hn
  have hS : {n : ℕ | h n = γ} ∈ p + p := by
    rw [mem_add_iff]
    exact Filter.mem_of_superset hBp fun u hu =>
      Filter.mem_of_superset hBp fun m hm => hγ u hu m hm
  cases γ with
  | false =>
    have e : {n : ℕ | h n = false} = {n : ℕ | h n = true}ᶜ := by
      ext n; simp
    rw [e, Ultrafilter.compl_mem_iff_notMem] at hD hS
    exact hS ((hid p hp).2 hD)
  | true => exact (hid p hp).1 hS hD

end Erdos1199
