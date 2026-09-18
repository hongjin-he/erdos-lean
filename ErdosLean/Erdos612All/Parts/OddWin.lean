import ErdosLean.Erdos612All.Parts.RangeWin
import ErdosLean.Erdos612All.Parts.OddDeg
import ErdosLean.Erdos612All.Parts.OddCliq

/-!
# Erdős 612 (all `r`), part (ii): the window conditions of the two-period family

`fam (odPre q) (odPer q) (odSuf q) 2 = odPre q ++ odPer q ++ odPer q ++ odSuf q`.  Writing
`odPre q = (List.range 2).map (fun _ => [δ])` and
`odSuf q = (List.range 3).map (fun i => if i = 0 then [1] else [δ])`, `map_range_append`
turns it into `(List.range (2(6q+19) + 5)).map G`.  Windows at the prefix/suffix layers are
checked directly (`δ ≥ x`, clump counts `≤ 2`); windows inside a period use the block lemmas
with left context `[δ]` or `odE q` (sum `x`) and right context `[1]`.
-/

namespace Erdos612All

open Erdos612

/-- The global layer function of the two-period family. -/
def odGlob (q ℓ : ℕ) : List ℕ :=
  if ℓ < 2 then [odDelta q]
  else if ℓ < 2 + (6 * q + 19) then odBlock q (ℓ - 2)
  else if ℓ < 2 + (6 * q + 19) + (6 * q + 19) then odBlock q (ℓ - 2 - (6 * q + 19))
  else if ℓ = 2 + (6 * q + 19) + (6 * q + 19) then [1]
  else [odDelta q]

theorem od_fam (q : ℕ) : fam (odPre q) (odPer q) (odSuf q) 2 =
    (List.range (2 + (6 * q + 19) + (6 * q + 19) + 3)).map (odGlob q) := by
  have hpre : odPre q = (List.range 2).map (fun _ => [odDelta q]) := rfl
  have hsuf : odSuf q = (List.range 3).map (fun i => if i = 0 then [1] else [odDelta q]) := rfl
  simp only [fam, List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [hpre, hsuf, odPer, map_range_append, map_range_append, map_range_append]
  rw [show 2 + (6 * q + 19 + (6 * q + 19)) + 3 = 2 + (6 * q + 19) + (6 * q + 19) + 3 by ring]
  congr 1
  funext ℓ
  unfold odGlob
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem odE_ne (q : ℕ) : odBlock q (6 * q + 19 - 1) = odE q := by
  rw [show 6 * q + 19 - 1 = 6 * q + 18 by omega, odBlock_E3]

theorem odGlob_pre (q ℓ : ℕ) (h : ℓ < 2) : odGlob q ℓ = [odDelta q] := by
  unfold odGlob; rw [ite_eq_left h]

theorem odGlob_blk (q ℓ : ℕ) (h1 : 2 ≤ ℓ) (h2 : ℓ < 2 + (6 * q + 19)) :
    odGlob q ℓ = odBlock q (ℓ - 2) := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_left h2]

theorem odGlob_blk2 (q ℓ : ℕ) (h1 : 2 + (6 * q + 19) ≤ ℓ)
    (h2 : ℓ < 2 + (6 * q + 19) + (6 * q + 19)) :
    odGlob q ℓ = odBlock q (ℓ - 2 - (6 * q + 19)) := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

theorem odGlob_junc (q ℓ : ℕ) (h : ℓ = 2 + (6 * q + 19) + (6 * q + 19)) : odGlob q ℓ = [1] := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

theorem odGlob_suf (q ℓ : ℕ) (h : 2 + (6 * q + 19) + (6 * q + 19) < ℓ) :
    odGlob q ℓ = [odDelta q] := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Every window of the two-period family is an end window or a block window. -/
theorem od_win (q : ℕ) {Q : List ℕ → List ℕ → List ℕ → Prop}
    (hQ : ∀ m, m < 6 * q + 19 → ∀ a c : List ℕ, (m ≠ 0 → a = odBlock q (m - 1)) →
      (m = 0 → odX q ≤ a.sum) → (m + 1 ≠ 6 * q + 19 → c = odBlock q (m + 1)) →
      (m + 1 = 6 * q + 19 → c = [1]) → Q a (odBlock q m) c)
    (h0 : Q [] [odDelta q] [odDelta q]) (h1 : Q [odDelta q] [odDelta q] [1])
    (h2 : Q (odE q) [1] [odDelta q]) (h3 : Q [1] [odDelta q] [odDelta q])
    (h4 : Q [odDelta q] [odDelta q] []) :
    AllWin Q (fam (odPre q) (odPer q) (odSuf q) 2) := by
  have hB0 : odBlock q 0 = [1] := odBlock_three q 0 (by omega)
  have hxδ : odX q ≤ odDelta q := by unfold odDelta; nlinarith
  have hxE : odX q ≤ (odE q).sum := by rw [odE_sum]; rfl
  rw [od_fam, allWin_map_range]
  intro ℓ hℓ
  by_cases hA : ℓ < 2
  · by_cases hz : ℓ = 0
    · rw [ite_eq_left hz, ite_eq_left (by omega), odGlob_pre q ℓ hA, odGlob_pre q (ℓ + 1) (by omega)]
      exact h0
    · rw [ite_eq_right hz, ite_eq_left (by omega), odGlob_pre q ℓ hA, odGlob_pre q (ℓ - 1) (by omega),
        odGlob_blk q (ℓ + 1) (by omega) (by omega), show ℓ + 1 - 2 = 0 by omega, hB0]
      exact h1
  by_cases hB : ℓ < 2 + (6 * q + 19)
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_blk q ℓ (by omega) hB]
    apply hQ (ℓ - 2) (by omega)
    · intro h; rw [odGlob_blk q (ℓ - 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h; rw [odGlob_pre q (ℓ - 1) (by omega)]; simpa using hxδ
    · intro h; rw [odGlob_blk q (ℓ + 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h
      rw [odGlob_blk2 q (ℓ + 1) (by omega) (by omega), show ℓ + 1 - 2 - (6 * q + 19) = 0 by omega]
      exact hB0
  by_cases hC : ℓ < 2 + (6 * q + 19) + (6 * q + 19)
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_blk2 q ℓ (by omega) hC]
    apply hQ (ℓ - 2 - (6 * q + 19)) (by omega)
    · intro h; rw [odGlob_blk2 q (ℓ - 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h
      rw [odGlob_blk q (ℓ - 1) (by omega) (by omega), show ℓ - 1 - 2 = 6 * q + 19 - 1 by omega,
        odE_ne]
      exact hxE
    · intro h; rw [odGlob_blk2 q (ℓ + 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h; exact odGlob_junc q (ℓ + 1) (by omega)
  by_cases hD : ℓ = 2 + (6 * q + 19) + (6 * q + 19)
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_junc q ℓ hD,
      odGlob_blk2 q (ℓ - 1) (by omega) (by omega),
      show ℓ - 1 - 2 - (6 * q + 19) = 6 * q + 19 - 1 by omega, odE_ne,
      odGlob_suf q (ℓ + 1) (by omega)]
    exact h2
  by_cases hE : ℓ = 2 + (6 * q + 19) + (6 * q + 19) + 1
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_suf q ℓ (by omega),
      odGlob_junc q (ℓ - 1) (by omega), odGlob_suf q (ℓ + 1) (by omega)]
    exact h3
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), odGlob_suf q ℓ (by omega),
      odGlob_suf q (ℓ - 1) (by omega)]
    exact h4

theorem od_pos (q : ℕ) : AllWin PosQ (fam (odPre q) (odPer q) (odSuf q) 2) := by
  have hδ : 0 < odDelta q := by unfold odDelta odX odU; positivity
  exact od_win q (fun m hm a c _ _ _ _ => odBlock_pos q m hm)
    ⟨by simp, by simpa using hδ⟩ ⟨by simp, by simpa using hδ⟩ ⟨by simp, by simp⟩
    ⟨by simp, by simpa using hδ⟩ ⟨by simp, by simpa using hδ⟩

theorem od_deg (q : ℕ) : AllWin (DegQ (odDelta q)) (fam (odPre q) (odPer q) (odSuf q) 2) := by
  have hE := odE_sum q
  refine od_win q (fun m hm a c ha ha0 hc hc0 => odBlock_deg q m hm a c ha ha0 hc hc0) ?_ ?_ ?_ ?_ ?_ <;>
    · intro w hw; simp at hw; subst hw; simp

theorem od_tight (q : ℕ) : SomeWin (TightQ (odDelta q)) (fam (odPre q) (odPer q) (odSuf q) 2) := by
  rw [od_fam, someWin_map_range]
  refine ⟨5, by omega, ?_⟩
  unfold odGlob
  simp (disch := omega) only [ite_eq_right, ite_eq_left]
  exact odBlock_tight q

theorem od_cliq (q : ℕ) :
    AllWin (CliqQ (2 * (q + 4) + 1)) (fam (odPre q) (odPer q) (odSuf q) 2) := by
  refine od_win q (fun m hm a c _ _ hc hc0 => odBlock_cliq q m hm a c hc
    (fun h => by rw [hc0 h]; simp)) ?_ ?_ ?_ ?_ ?_ <;> (unfold CliqQ; simp)

end Erdos612All
