import ErdosLean.Erdos612.Main
import ErdosLean.Erdos612All.Defs
import ErdosLean.Erdos612All.Parts.EvenWin
import ErdosLean.Erdos612All.Parts.EvenGrowth
import ErdosLean.Erdos612All.Parts.OddWin
import ErdosLean.Erdos612All.Parts.OddGrowth

/-!
# Erdős Problem 612 (JSP-000497), all `r`: main theorem

* Part (i) is false for every `r ≥ 2`: the blow-ups of `fam [] (evPer s) [] p`
  (Czabarka–Singgih–Székely's block, `s = r - 1`, `δ = 4s(s+1)(3s+5)`).
* Part (ii) is false for every `r ≥ 4`: the blow-ups of `fam (odPre q) (odPer q) (odSuf q) p`
  (Chen–Chen's `J_{p,r}`, `q = r - 4`, `δ = 6(6r-5)(2r-1)(3r-1)`).

Both go through the engine `Erdos612.not_diamBound_of_fam` of `ErdosLean/Erdos612/Main.lean`; the
window hypotheses on the two-period instance are proved **symbolically** (no `decide`) in
`Parts/EvenWin.lean`, `Parts/OddWin.lean`, the growth inequalities in `Parts/*Growth.lean`.
-/

namespace Erdos612All

open Erdos612

/-- Part (i) of Erdős #612 fails for every `r ≥ 2`. -/
theorem not_evenConjAt (r : ℕ) (hr : 2 ≤ r) : ¬ EvenConjAt r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs : 1 ≤ s := by omega
  unfold EvenConjAt
  refine not_diamBound_of_fam (δ := evDelta s) [] (evPer s) []
    (by rw [evPer_length]; omega) ?_ ?_ (ev_pos s hs) (ev_deg s hs) (ev_tight s hs)
    (ev_cliq s hs) (ev_growth s hs)
  · unfold evDelta evW
    have h1 : 0 < 2 * (s + 1) * (3 * s + 5) := by positivity
    have h2 : 2 * 1 * 1 ≤ 2 * s * (2 * (s + 1) * (3 * s + 5)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hs) h1
    simpa using h2
  · rw [Nat.add_sub_cancel]
    exact ⟨4 * (s + 1), by unfold evDelta evW; ring⟩

/-- Part (ii) of Erdős #612 fails for every `r ≥ 4`. -/
theorem not_oddConjAt (r : ℕ) (hr : 4 ≤ r) : ¬ OddConjAt r := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 4 := ⟨r - 4, by omega⟩
  unfold OddConjAt
  refine not_diamBound_of_fam (δ := odDelta q) (odPre q) (odPer q) (odSuf q)
    (by rw [odPer_length]; omega) ?_ ?_ (od_pos q) (od_deg q) (od_tight q)
    (od_cliq q) (od_growth q)
  · unfold odDelta odX odU
    have h1 : 0 < (3 * q + 11) * (2 * (6 * q + 19)) := by positivity
    have h2 : 1 * (3 * 1) ≤ (2 * q + 7) * (3 * ((3 * q + 11) * (2 * (6 * q + 19)))) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 3 h1)
    omega
  · rw [show 3 * (q + 4) - 1 = 3 * q + 11 by omega]
    exact ⟨(2 * q + 7) * 3 * (2 * (6 * q + 19)), by unfold odDelta odX odU; ring⟩

/-- **Erdős #612, all `r`**: part (i) fails for every `r ≥ 2`, part (ii) fails for every
`r ≥ 4`, in the weak and in the uniform reading of `O(1)`. -/
theorem erdos_612_all : Erdos612AllAnswer :=
  ⟨not_evenConjAt, not_oddConjAt,
    fun r hr h => not_evenConjAt r hr (diamBound_of_uniform h),
    fun r hr h => not_oddConjAt r hr (diamBound_of_uniform h)⟩

end Erdos612All
