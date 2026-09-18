import ErdosLean.Erdos790.Statement
import ErdosLean.Erdos790.Parts.BitSplit
import ErdosLean.Erdos790.Parts.RankElem
import ErdosLean.Erdos790.Parts.DistanceLists
import ErdosLean.Erdos790.Parts.Dyadic
import ErdosLean.Erdos790.Parts.Window
import ErdosLean.Erdos790.Parts.FsetCard
import ErdosLean.Erdos790.Parts.RelationShape
import ErdosLean.Erdos790.Parts.Obstruction
import ErdosLean.Erdos790.Parts.Averaging
import ErdosLean.Erdos790.Parts.Pigeon
import ErdosLean.Erdos790.Parts.CastIdx
import ErdosLean.Erdos790.Parts.SignSplit
import ErdosLean.Erdos790.Parts.LBridge
import ErdosLean.Erdos790.Parts.LogBound
import ErdosLean.Erdos790.Parts.Asymptotics

/-!
# Erdős Problem 790 (JSP-000649): main theorem

Samuel Korsky's bound `l(n) ≫ n/(log n)²` (Theorem 1 of *Large Sum-Free Subsets of Sets of
Integers*, preprint, 13 September 2026, posted as a proof claim at
<https://www.erdosproblems.com/forum/thread/790/proof-claims>), assembled from the lemmas in
`Parts/`.  The random selection of dyadic intervals in the paper is replaced by an averaging
argument over colourings, and the constant is made explicit (`c = 1/1024`).
-/

namespace Erdos790

open Filter

/-- For every colouring `χ` of the dyadic indices and every colour `c`, the selected set
(elements whose own index has colour `c` and none of whose forbidden indices do) is sum-free. -/
theorem selected_sumFree (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) {m : ℕ}
    (χ : Fin (topIdx A + 1) → Fin m) (c : Fin m) :
    IsSumFree (A.filter (fun a => χ (idx A (dyIdx a)) = c ∧
      ∀ j ∈ (Fset A a).image (idx A), χ j ≠ c)) := by
  set B := A.filter (fun a => χ (idx A (dyIdx a)) = c ∧
      ∀ j ∈ (Fset A a).image (idx A), χ j ≠ c) with hBdef
  intro x hx S hS hxS h2 hsum
  have hSA : S ⊆ A := hS.trans (Finset.filter_subset _ _)
  obtain ⟨z, hzS, a, ha, hmem⟩ :=
    obstruction A hpos (Finset.mem_filter.1 hx).1 hSA hxS h2 hsum
  have hz := (Finset.mem_filter.1 (hS hzS)).2.1
  have haB : a ∈ B := by
    rcases ha with rfl | ha
    · exact hx
    · exact hS ha
  exact (Finset.mem_filter.1 haB).2.2 _ (Finset.mem_image_of_mem _ hmem) hz

/-- Theorem 1 for sets of positive integers: `|A| ≤ 4 K(|A|) |B|`. -/
theorem positive_case (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) (hA : 1 ≤ A.card) :
    ∃ B ⊆ A, IsSumFree B ∧ A.card ≤ 4 * K A.card * B.card := by
  have hm : 0 < 2 * K A.card := by have := K_pos A.card; omega
  obtain ⟨χ, hχ⟩ := exists_coloring_many_good A (fun a => idx A (dyIdx a))
    (fun a => (Fset A a).image (idx A)) (2 * K A.card) hm
    (fun a ha => idx_not_mem_image_Fset ha)
    (fun a _ => by
      have h1 := Finset.card_image_le (s := Fset A a) (f := idx A)
      have h2 := card_Fset_le A hA a
      omega)
  set T := A.filter (fun a => ∀ j ∈ (Fset A a).image (idx A),
    χ j ≠ χ (idx A (dyIdx a))) with hT
  obtain ⟨c, hc⟩ := exists_color_fiber T hm (fun a => χ (idx A (dyIdx a)))
  set B := A.filter (fun a => χ (idx A (dyIdx a)) = c ∧
      ∀ j ∈ (Fset A a).image (idx A), χ j ≠ c) with hB
  refine ⟨B, Finset.filter_subset _ _, selected_sumFree A hpos χ c, ?_⟩
  have hsub : T.filter (fun a => χ (idx A (dyIdx a)) = c) ⊆ B := by
    intro a ha
    rw [Finset.mem_filter, hT, Finset.mem_filter] at ha
    obtain ⟨⟨haA, hgood⟩, hca⟩ := ha
    rw [hB, Finset.mem_filter]
    refine ⟨haA, hca, fun j hj => ?_⟩
    rw [← hca]
    exact hgood j hj
  have h1 := Finset.card_le_card hsub
  have h2 : 2 * K A.card * (T.filter (fun a => χ (idx A (dyIdx a)) = c)).card ≤
      2 * K A.card * B.card := Nat.mul_le_mul_left _ h1
  have h0 : A.card ≤ 2 * T.card := by rw [hT]; convert hχ
  linarith

/-- Theorem 1 for arbitrary integer sets with `|A| ≥ 2`: `|A| ≤ 16 K(|A|) |B|`. -/
theorem general_case (A : Finset ℤ) (hA : 2 ≤ A.card) :
    ∃ B ⊆ A, IsSumFree B ∧ A.card ≤ 16 * K A.card * B.card := by
  rcases sign_split A hA with h | h
  · set P := A.filter (fun x => 0 < x) with hP
    have hP1 : 1 ≤ P.card := by omega
    obtain ⟨B, hBP, hB, hcard⟩ :=
      positive_case P (fun a ha => (Finset.mem_filter.1 ha).2) hP1
    have hK : K P.card ≤ K A.card := K_mono (Finset.card_le_card (Finset.filter_subset _ _))
    refine ⟨B, hBP.trans (Finset.filter_subset _ _), hB, ?_⟩
    have : K P.card * B.card ≤ K A.card * B.card := Nat.mul_le_mul_right _ hK
    nlinarith
  · set N := A.filter (fun x => x < 0) with hN
    set P := N.image (fun x => -x) with hP
    have hPc : P.card = N.card := Finset.card_image_of_injective _ neg_injective
    have hP1 : 1 ≤ P.card := by omega
    have hpos : ∀ a ∈ P, 0 < a := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
      have := (Finset.mem_filter.1 hy).2
      omega
    obtain ⟨B, hBP, hB, hcard⟩ := positive_case P hpos hP1
    refine ⟨B.image (fun x => -x), ?_, isSumFree_image_neg hB, ?_⟩
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hBP hw)
      simpa using (Finset.mem_filter.1 hv).1
    · rw [Finset.card_image_of_injective _ neg_injective]
      have hK : K P.card ≤ K A.card :=
        K_mono (by rw [hPc]; exact Finset.card_le_card (Finset.filter_subset _ _))
      have : K P.card * B.card ≤ K A.card * B.card := Nat.mul_le_mul_right _ hK
      nlinarith

/-- **Erdős Problem 790** (Korsky 2026): `l(n) ≥ n / (1024 (log n)²)`; hence
`l(n)/√n → ∞`, `l(n) = n^{1-o(1)}`, and `l(n) < n^{1-c}` fails for every `c > 0`. -/
theorem erdos_790 : Erdos790Answer := by
  have hlow : ∀ n : ℕ, 2 ≤ n → n ≤ 16 * K n * l n := by
    intro n hn
    apply l_lower_of n (16 * K n) (by have := K_pos n; omega)
    intro A hA
    obtain ⟨B, hBA, hB, h⟩ := general_case A (by omega)
    exact ⟨B, hBA, hB, by rw [hA] at h; exact h⟩
  have hc : ∀ n : ℕ, 2 ≤ n → (1 / 1024 : ℝ) * n / Real.log n ^ 2 ≤ l n := by
    intro n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h1 : (n : ℝ) ≤ 16 * K n * l n := by exact_mod_cast hlow n hn
    have h2 := K_le_log_sq n hn
    have hl : (0 : ℝ) ≤ l n := Nat.cast_nonneg _
    have h3 : (K n : ℝ) * l n ≤ 64 * Real.log n ^ 2 * l n := mul_le_mul_of_nonneg_right h2 hl
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h3, h4⟩ := asymptotics l (1 / 1024) (by norm_num) hc
  refine ⟨⟨1 / 1024, by norm_num, hc⟩, l_le_self, h3, h4, ?_⟩
  rintro ⟨c, hc0, hfreq⟩
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (h4 c hc0)).exists
  linarith

end Erdos790
