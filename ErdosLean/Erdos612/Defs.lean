import ErdosLean.Erdos612.Statement

/-!
# Erdős 612: shared definitions — blow-ups of weighted layered clique graphs

A *layer sequence* `L : List (List ℕ)` lists, for each layer, the weights of its clumps.
The *weighted layered clique graph* on the clumps joins two distinct clumps iff their layers
differ by at most one; its *blow-up* `blowup L` replaces each clump of weight `w` by an
independent set of `w` vertices, and each edge by a complete bipartite graph
(Czabarka–Singgih–Székely 2021, §2–3; Chen–Chen 2026, §1).

Both counterexample families used in `Main.lean` are blow-ups of periodic layer sequences
`fam pre per suf p = pre ++ per ++ ⋯ ++ per ++ suf` (`p` copies of the period `per`), and all
their properties are *local*: they are statements about windows of three consecutive layers
(`AllWin`), which are checked by `decide` on the instance with two periods.
-/

open SimpleGraph

namespace Erdos612

/-- A layer sequence: layer `ℓ` is the list of weights of its clumps. -/
abbrev Layers := List (List ℕ)

namespace Layers

/-- Layer `ℓ` (empty beyond the end). -/
def lay (L : Layers) (ℓ : ℕ) : List ℕ := L.getD ℓ []

/-- The layer to the left of `ℓ` (empty for `ℓ = 0`). -/
def lft (L : Layers) (ℓ : ℕ) : List ℕ := ([] :: L).getD ℓ []

/-- Number of clumps in layer `ℓ`. -/
def cnt (L : Layers) (ℓ : ℕ) : ℕ := (L.lay ℓ).length

/-- Weight of clump `j` of layer `ℓ`. -/
def wt (L : Layers) (ℓ j : ℕ) : ℕ := (L.lay ℓ).getD j 0

/-- Total weight of layer `ℓ`. -/
def tot (L : Layers) (ℓ : ℕ) : ℕ := (L.lay ℓ).sum

/-- Total weight of layers `ℓ - 1`, `ℓ`, `ℓ + 1` (the closed neighbourhood weight). -/
def nbr (L : Layers) (ℓ : ℕ) : ℕ := (L.lft ℓ).sum + L.tot ℓ + L.tot (ℓ + 1)

/-- Total weight of all layers (the number of vertices of the blow-up). -/
def total (L : Layers) : ℕ := (L.map List.sum).sum

end Layers

/-- Clumps of `L`: a layer index and a clump index inside it. -/
abbrev Clump (L : Layers) := Σ ℓ : Fin L.length, Fin (L.cnt ℓ)

/-- Vertices of the blow-up: a clump and an index below its weight. -/
abbrev Vtx (L : Layers) := Σ c : Clump L, Fin (L.wt c.1 c.2)

/-- The layer of a vertex. -/
def Vtx.layer {L : Layers} (v : Vtx L) : ℕ := v.1.1

/-- The blow-up of the weighted layered clique graph with layer sequence `L`: two vertices are
adjacent iff they lie in different clumps whose layers differ by at most one. -/
def blowup (L : Layers) : SimpleGraph (Vtx L) where
  Adj u v := u.1 ≠ v.1 ∧ u.layer ≤ v.layer + 1 ∧ v.layer ≤ u.layer + 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (L : Layers) : DecidableRel (blowup L).Adj := fun u v => by
  unfold blowup; exact inferInstance

/-! ### Local (three-layer window) conditions -/

/-- A predicate on windows `(left layer, layer, right layer)` holds at every layer of `L`. -/
def AllWin (Q : List ℕ → List ℕ → List ℕ → Prop) (L : Layers) : Prop :=
  ∀ ℓ, ℓ < L.length → Q (L.lft ℓ) (L.lay ℓ) (L.lay (ℓ + 1))

/-- Some layer of `L` has a window satisfying `Q`. -/
def SomeWin (Q : List ℕ → List ℕ → List ℕ → Prop) (L : Layers) : Prop :=
  ∃ ℓ, ℓ < L.length ∧ Q (L.lft ℓ) (L.lay ℓ) (L.lay (ℓ + 1))

/-- Every layer is nonempty and every weight is positive. -/
def PosQ (_a b _c : List ℕ) : Prop := b ≠ [] ∧ ∀ w ∈ b, 0 < w

/-- Every clump `w` of the middle layer has neighbourhood weight `≥ δ`. -/
def DegQ (δ : ℕ) (a b c : List ℕ) : Prop := ∀ w ∈ b, δ + w ≤ a.sum + b.sum + c.sum

/-- Some clump `w` of the middle layer has neighbourhood weight exactly `δ`. -/
def TightQ (δ : ℕ) (a b c : List ℕ) : Prop := ∃ w ∈ b, δ + w = a.sum + b.sum + c.sum

/-- Two consecutive layers have fewer than `s` clumps in total. -/
def CliqQ (s : ℕ) (_a b c : List ℕ) : Prop := b.length + c.length < s

instance (a b c : List ℕ) : Decidable (PosQ a b c) :=
  inferInstanceAs (Decidable (b ≠ [] ∧ ∀ w ∈ b, 0 < w))
instance (δ : ℕ) (a b c : List ℕ) : Decidable (DegQ δ a b c) :=
  inferInstanceAs (Decidable (∀ w ∈ b, δ + w ≤ a.sum + b.sum + c.sum))
instance (δ : ℕ) (a b c : List ℕ) : Decidable (TightQ δ a b c) :=
  inferInstanceAs (Decidable (∃ w ∈ b, δ + w = a.sum + b.sum + c.sum))
instance (s : ℕ) (a b c : List ℕ) : Decidable (CliqQ s a b c) :=
  inferInstanceAs (Decidable (b.length + c.length < s))
instance (Q : List ℕ → List ℕ → List ℕ → Prop) [∀ a b c, Decidable (Q a b c)] (L : Layers) :
    Decidable (AllWin Q L) :=
  inferInstanceAs (Decidable (∀ ℓ, ℓ < L.length → Q (L.lft ℓ) (L.lay ℓ) (L.lay (ℓ + 1))))
instance (Q : List ℕ → List ℕ → List ℕ → Prop) [∀ a b c, Decidable (Q a b c)] (L : Layers) :
    Decidable (SomeWin Q L) :=
  inferInstanceAs (Decidable (∃ ℓ, ℓ < L.length ∧ Q (L.lft ℓ) (L.lay ℓ) (L.lay (ℓ + 1))))

/-! ### Periodic families -/

/-- `pre`, then `p` copies of the period `per`, then `suf`. -/
def fam (pre per suf : Layers) (p : ℕ) : Layers :=
  pre ++ (List.replicate p per).flatten ++ suf

end Erdos612
