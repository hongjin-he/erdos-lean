import ErdosLean.Erdos1199.Statement
import ErdosLean.Erdos1199.Parts.KeyIdentity
import ErdosLean.Erdos1199.Parts.MinimalExists
import ErdosLean.Erdos1199.Parts.DisjointMinimal
import ErdosLean.Erdos1199.Parts.FiniteSeparation
import ErdosLean.Erdos1199.Parts.Coding
import ErdosLean.Erdos1199.Parts.ThickRuns
import ErdosLean.Erdos1199.Parts.NoMonoFromIdentity
import ErdosLean.Erdos1199.Parts.HindmanThick

/-!
# Erdős Problem 1199 (JSP-001004): main theorem

Owings's question has an affirmative answer (Huang–Lian–Shao–Xiao–Xu–Zhang,
arXiv:2607.17333, Theorem 1.1).  The proof below assembles the parts in `Parts/`
following §3 of the paper.
-/

namespace Erdos1199

open Filter Pointwise

/-- Theorem 1.1 for Boolean colourings: every `b : ℕ → Bool` has an infinite set `B` of
positive integers with `B + B` monochromatic. -/
theorem owings_bool (b : ℕ → Bool) : Owings b := by
  by_contra H
  -- the encoded point `𝐜` of `c(n) = b(2n)`
  have hkey : ∀ p : Ultrafilter ℕ, Nonprincipal p →
      act (p + p) (encode (ext2 b)) = cmpl (act (dbl p) (encode (ext2 b))) :=
    fun p hp => key_identity b H hp
  have hdil : dil (encode (ext2 b)) = encode (ext2 b) := dil_encode _
  -- a minimal subsystem `M ⊆ ω(𝐜)` with `M ∩ J M = ∅`
  obtain ⟨M, hM⟩ := exists_minimal (encode (ext2 b))
  have hdisj := disjoint_minimal (encode (ext2 b)) hdil hkey M hM
  -- a finitely determined `J`-odd `G` with `G ≡ true` on `M`
  obtain ⟨G, F, hF, hGc, hGM⟩ := finite_separation M hM.2.1 hdisj
  have hcode := coding G F hF (encode (ext2 b))
  -- the new colouring `h n = G (Tⁿ 𝐜)` satisfies `(p+p) h = J (D p) h`
  have hid : ∀ p : Ultrafilter ℕ, Nonprincipal p →
      ({n : ℕ | G (act (pure n) (encode (ext2 b))) = true} ∈ p + p ↔
        {n : ℕ | G (act (pure n) (encode (ext2 b))) = true} ∉ dbl p) := by
    intro p hp
    rw [hcode (p + p), hcode (dbl p), hkey p hp, hGc]
    cases G (act (dbl p) (encode (ext2 b))) <;> simp
  -- so `h` has no monochromatic `B + B` ...
  have hno := no_mono_of_identity (fun n => G (act (pure n) (encode (ext2 b)))) hid
  -- ... but its colour class `true` is thick, so Hindman's theorem gives one.
  have hthick := thick_of_minimal (encode (ext2 b)) M hM G hGM hcode
  exact hno (hindman_thick (fun n => G (act (pure n) (encode (ext2 b)))) true hthick)

/-- **Erdős #1199 / Owings's question**, original form over the positive integers. -/
theorem erdos_1199_pos : Erdos1199StatementPos := by
  intro color
  obtain ⟨B, hBinf, hBpos, γ, hγ⟩ := owings_bool (fun n => decide (color n = 1))
  refine ⟨B, hBinf, hBpos, ?_⟩
  have key : ∀ n ∈ B + B, decide (color n = 1) = γ := by
    rintro n ⟨a, ha, a', ha', rfl⟩
    exact hγ a ha a' ha'
  intro n hn m hm
  have hnm : decide (color n = 1) = decide (color m = 1) := (key n hn).trans (key m hm).symm
  have two : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases two (color n) with h | h <;> rcases two (color m) with h' | h' <;>
    simp [h, h'] at hnm ⊢

/-- **Erdős #1199**, in the formal-conjectures formulation. -/
theorem erdos_1199 : Erdos1199Statement := by
  intro color
  obtain ⟨A, h1, -, h3⟩ := erdos_1199_pos color
  exact ⟨A, h1, h3⟩

/-- The formal-conjectures statement `answer(?) ↔ …` with the answer `True` filled in. -/
theorem erdos_1199_fc :
    True ↔ ∀ (color : ℕ → Fin 2), ∃ (A : Set ℕ),
      A.Infinite ∧ ∀ n ∈ (A + A), ∀ m ∈ (A + A), color n = color m :=
  ⟨fun _ => erdos_1199, fun _ => trivial⟩

end Erdos1199
