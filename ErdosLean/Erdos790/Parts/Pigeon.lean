import ErdosLean.Erdos790.Defs

/-! Part: pigeonhole over `m` colours. -/

namespace Erdos790

open Classical in
theorem exists_color_fiber {α : Type*} (T : Finset α) {m : ℕ} (hm : 0 < m) (f : α → Fin m) :
    ∃ c : Fin m, T.card ≤ m * (T.filter (fun a => f a = c)).card := by
  by_contra h
  push Not at h
  have hsum : T.card = ∑ c : Fin m, (T.filter (fun a => f a = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hlt : ∑ c : Fin m, m * (T.filter (fun a => f a = c)).card
      < ∑ _c : Fin m, T.card := Finset.sum_lt_sum_of_nonempty hne (fun c _ => h c)
  rw [← Finset.mul_sum, ← hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hlt
  exact lt_irrefl _ hlt

end Erdos790
