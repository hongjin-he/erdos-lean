import Mathlib
import ErdosLean.DuffinSchaeffer.Statement

/-!
# Duffin–Schaeffer — shared definitions

Lean-oriented encoding of Koukoulopoulos–Maynard, *On the Duffin–Schaeffer conjecture*
(Annals 2020, arXiv:1907.04593).

* §A (measure side): the weight `w(q) = φ(q)ψ(q)/q`, the capped function `capψ`, the sets
  `A_q ⊆ ℝ/ℤ` (Mathlib's `approxAddOrderOf`), `M(q,r)`, `L_t(a,b)`, `P(q,r)` and the edge set
  `E_t` of Proposition 5.4.
* §B (GCD graphs, KM §6): the structure `GCDGraph` (Definition 6.1, with bundled axioms),
  weighted sums, edge density, quality `q(G)`, the prime sets `R, R♯, R♭`, GCD subgraphs
  (Definition 6.4), the special subgraphs `G_{p^k,p^ℓ}` (Definition 6.5) and induced subgraphs.

All definitions here are complete.-/

open MeasureTheory Filter Finset

namespace DuffinSchaeffer

/-! ## §A. The measure-theoretic side -/

/-- The Duffin–Schaeffer weight `w(q) = φ(q) ψ(q) / q` (so `w 0 = 0`). -/
noncomputable def weight (ψ : ℕ → ℝ) (q : ℕ) : ℝ := (Nat.totient q : ℝ) * ψ q / q

theorem dsSeriesDiverges_iff (ψ : ℕ → ℝ) : DSSeriesDiverges ψ ↔ ¬ Summable (weight ψ) :=
  Iff.rfl

/-- `ψ` capped so that `w(q) ≤ 1/2`: `capψ ψ q = min (ψ q) (q / (2 φ(q)))`.
For `q ≥ 1`, `weight (capψ ψ) q = min (weight ψ q) (1/2)` and the radius `capψ ψ q / q` is at
most `1 / (2 φ(q)) → 0`. -/
noncomputable def capψ (ψ : ℕ → ℝ) (q : ℕ) : ℝ := min (ψ q) ((q : ℝ) / (2 * Nat.totient q))

/-- The set `A_q = {x ∈ ℝ/ℤ : ‖x - a/q‖ < ψ(q)/q for some a with gcd(a,q) = 1}`,
i.e. Mathlib's `approxAddOrderOf (ℝ/ℤ) q (ψ q / q)`. -/
noncomputable def Aq (ψ : ℕ → ℝ) (q : ℕ) : Set UnitAddCircle :=
  approxAddOrderOf UnitAddCircle q (ψ q / q)

/-- `M(q, r) = max(r ψ(q), q ψ(r))` (KM Lemma 5.3). -/
noncomputable def Mqr (ψ : ℕ → ℝ) (q r : ℕ) : ℝ := max (r * ψ q) (q * ψ r)

/-- `ab / gcd(a,b)^2 = (a / gcd a b) * (b / gcd a b)`. -/
def coprimePart (a b : ℕ) : ℕ := (a / Nat.gcd a b) * (b / Nat.gcd a b)

/-- `L_t(a, b) = ∑_{p | ab/gcd(a,b)^2, p ≥ t} 1/p` (KM (5.1)). -/
noncomputable def Lsum (t : ℝ) (a b : ℕ) : ℝ :=
  ∑ p ∈ (coprimePart a b).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p

/-- `P(q, r) = ∏_{p | qr/gcd(q,r)^2, p > M(q,r)/gcd(q,r)} (1 + 1/p)` (KM Lemma 5.3). -/
noncomputable def Pfac (ψ : ℕ → ℝ) (q r : ℕ) : ℝ :=
  ∏ p ∈ (coprimePart q r).primeFactors.filter (fun p : ℕ => Mqr ψ q r / Nat.gcd q r < (p : ℝ)),
    (1 + 1 / (p : ℝ))

/-- The edge set `E_t ⊆ [X,Y]^2` of Proposition 5.4:
`gcd(v,w) ≥ M(v,w)/t` and `L_t(v,w) ≥ 10`. -/
noncomputable def Et (ψ : ℕ → ℝ) (X Y : ℕ) (t : ℝ) : Finset (ℕ × ℕ) :=
  (Icc X Y ×ˢ Icc X Y).filter
    (fun e => Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2 ∧ 10 ≤ Lsum t e.1 e.2)

/-- The threshold `10^2000` used throughout KM §§7–14. -/
noncomputable def T0 : ℝ := (10 : ℝ) ^ (2000 : ℕ)

/-- The constant `10^40` in the definition of `R♯` (KM Definition 6.6(c)). -/
noncomputable def K40 : ℝ := (10 : ℝ) ^ (40 : ℕ)

/-! ## §B. GCD graphs (KM §6) -/

/-- `μ(S) = ∑_{v ∈ S} μ(v)`. -/
def wsum (μ : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ v ∈ S, μ v

/-- `μ(N) = ∑_{(n₁,n₂) ∈ N} μ(n₁) μ(n₂)` for `N ⊆ ℕ²`. -/
def esum (μ : ℕ → ℝ) (E : Finset (ℕ × ℕ)) : ℝ := ∑ e ∈ E, μ e.1 * μ e.2

/-- `S_{p^k} = {v ∈ S : p^k ‖ v}` (KM Definition 6.5(a)); `k = 0` means `p ∤ v`. -/
def vslice (S : Finset ℕ) (p k : ℕ) : Finset ℕ := S.filter (fun v => v.factorization p = k)

/-- A bipartite GCD graph `(μ, V, W, E, P, f, g)` (KM Definition 6.1).  The functions `f, g`
are total on `ℕ`; only their values on `P` matter. -/
structure GCDGraph where
  μ : ℕ → ℝ
  V : Finset ℕ
  W : Finset ℕ
  E : Finset (ℕ × ℕ)
  P : Finset ℕ
  f : ℕ → ℕ
  g : ℕ → ℕ
  μ_nonneg : ∀ n, 0 ≤ μ n
  V_pos : ∀ v ∈ V, 0 < v
  W_pos : ∀ w ∈ W, 0 < w
  E_sub : E ⊆ V ×ˢ W
  P_prime : ∀ p ∈ P, p.Prime
  /-- (e)(i) -/
  dvd_V : ∀ p ∈ P, ∀ v ∈ V, p ^ f p ∣ v
  dvd_W : ∀ p ∈ P, ∀ w ∈ W, p ^ g p ∣ w
  /-- (e)(ii): `p^{min(f p, g p)} ‖ gcd(v,w)` on edges -/
  gcd_E : ∀ p ∈ P, ∀ e ∈ E, (Nat.gcd e.1 e.2).factorization p = min (f p) (g p)
  /-- (e)(iii) -/
  exact_V : ∀ p ∈ P, f p ≠ g p → ∀ v ∈ V, v.factorization p = f p
  exact_W : ∀ p ∈ P, f p ≠ g p → ∀ w ∈ W, w.factorization p = g p

namespace GCDGraph

variable (G : GCDGraph)

/-- Non-trivial: `μ(E) > 0` (KM Definition 6.2). -/
def Nontrivial : Prop := 0 < esum G.μ G.E

/-- Edge density `δ(G) = μ(E) / (μ(V) μ(W))` (`= 0` if `μ(V) μ(W) = 0`, by Lean's `x/0 = 0`). -/
noncomputable def density : ℝ := esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W)

/-- `Γ_G(v) = {w ∈ W : (v,w) ∈ E}`. -/
def nbhdV (v : ℕ) : Finset ℕ := G.W.filter (fun w => (v, w) ∈ G.E)

/-- `Γ_G(w) = {v ∈ V : (v,w) ∈ E}`. -/
def nbhdW (w : ℕ) : Finset ℕ := G.V.filter (fun v => (v, w) ∈ G.E)

/-- `|f(p) - g(p)|`. -/
def fgDist (p : ℕ) : ℕ := (G.f p - G.g p) + (G.g p - G.f p)

/-- The local factor of the quality at `p ∈ P`:
`p^{|f(p)-g(p)|} / ((1 - 1_{f(p)=g(p)≥1}/p)^2 (1 - 1/p^{31/30})^{10})`. -/
noncomputable def qualityFactor (p : ℕ) : ℝ :=
  (p : ℝ) ^ G.fgDist p /
    ((1 - (if G.f p = G.g p ∧ 1 ≤ G.f p then 1 / (p : ℝ) else 0)) ^ 2 *
      (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)

/-- The quality `q(G) = δ^{10} μ(V) μ(W) ∏_{p ∈ P} (local factor)` (KM Definition 6.6(d)). -/
noncomputable def quality : ℝ :=
  G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p

/-- `R(G) = {p ∉ P : p | gcd(v,w) for some (v,w) ∈ E}` (KM Definition 6.6(c)). -/
def R : Finset ℕ := (G.E.biUnion (fun e => (Nat.gcd e.1 e.2).primeFactors)) \ G.P

/-- `p` is "sharp": some `p^k` exactly divides a `(1 - 10^40/p)`-proportion of both `V` and `W`. -/
def IsSharp (p : ℕ) : Prop :=
  ∃ k : ℕ, (1 - K40 / p) * wsum G.μ G.V ≤ wsum G.μ (vslice G.V p k) ∧
    (1 - K40 / p) * wsum G.μ G.W ≤ wsum G.μ (vslice G.W p k)

open scoped Classical in
/-- `R♯(G)`. -/
noncomputable def Rsharp : Finset ℕ := G.R.filter G.IsSharp

open scoped Classical in
/-- `R♭(G) = R(G) \ R♯(G)`. -/
noncomputable def Rflat : Finset ℕ := G.R.filter (fun p => ¬ G.IsSharp p)

/-- `a = ∏_{p ∈ P} p^{f(p)}` divides every `v ∈ V`. -/
def aProd : ℕ := ∏ p ∈ G.P, p ^ G.f p

/-- `b = ∏_{p ∈ P} p^{g(p)}` divides every `w ∈ W`. -/
def bProd : ℕ := ∏ p ∈ G.P, p ^ G.g p

/-- `G'` is a GCD subgraph of `G` (KM Definition 6.4): same measure, smaller vertex and edge sets,
more primes, same multiplicative data on the old primes. -/
def IsSubgraph (G' G : GCDGraph) : Prop :=
  G'.μ = G.μ ∧ G'.V ⊆ G.V ∧ G'.W ⊆ G.W ∧ G'.E ⊆ G.E ∧ G.P ⊆ G'.P ∧
    ∀ p ∈ G.P, G'.f p = G.f p ∧ G'.g p = G.g p

/-- The GCD subgraph with vertex sets `V' ⊆ V`, `W' ⊆ W` and edge set `E' ⊆ E ∩ (V' × W')`,
keeping the multiplicative data. -/
def induce (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ)) (hV : V' ⊆ G.V) (hW : W' ⊆ G.W)
    (hE : E' ⊆ G.E) (hE' : E' ⊆ V' ×ˢ W') : GCDGraph where
  μ := G.μ
  V := V'
  W := W'
  E := E'
  P := G.P
  f := G.f
  g := G.g
  μ_nonneg := G.μ_nonneg
  V_pos := fun v hv => G.V_pos v (hV hv)
  W_pos := fun w hw => G.W_pos w (hW hw)
  E_sub := hE'
  P_prime := G.P_prime
  dvd_V := fun p hp v hv => G.dvd_V p hp v (hV hv)
  dvd_W := fun p hp w hw => G.dvd_W p hp w (hW hw)
  gcd_E := fun p hp e he => G.gcd_E p hp e (hE he)
  exact_V := fun p hp hfg v hv => G.exact_V p hp hfg v (hV hv)
  exact_W := fun p hp hfg w hw => G.exact_W p hp hfg w (hW hw)

/-- The special GCD subgraph `G_{p^k,p^ℓ} = (μ, V_{p^k}, W_{p^ℓ}, E_{p^k,p^ℓ}, P ∪ {p}, f_{p^k},
g_{p^ℓ})` for a prime `p ∉ P` (KM Definition 6.5(c)). -/
def restrictPrime (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) : GCDGraph where
  μ := G.μ
  V := vslice G.V p k
  W := vslice G.W p l
  E := G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)
  P := insert p G.P
  f := Function.update G.f p k
  g := Function.update G.g p l
  μ_nonneg := G.μ_nonneg
  V_pos := fun v hv => G.V_pos v (Finset.mem_filter.1 hv).1
  W_pos := fun w hw => G.W_pos w (Finset.mem_filter.1 hw).1
  E_sub := by
    intro e he
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hv, h1⟩, Finset.mem_filter.2 ⟨hw, h2⟩⟩
  P_prime := by
    intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hp
    · exact G.P_prime q hq
  dvd_V := by
    intro q hq v hv
    obtain ⟨hv, hvk⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self, ← hvk]
      exact Nat.ordProj_dvd v q
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_V q hq' v hv
  dvd_W := by
    intro q hq w hw
    obtain ⟨hw, hwl⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self, ← hwl]
      exact Nat.ordProj_dvd w q
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_W q hq' w hw
  gcd_E := by
    intro q hq e he0
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he0
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · subst hqp
      obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
      have hv0 : e.1 ≠ 0 := (G.V_pos _ hv).ne'
      have hw0 : e.2 ≠ 0 := (G.W_pos _ hw).ne'
      rw [Function.update_self, Function.update_self, Nat.factorization_gcd hv0 hw0,
        Finsupp.inf_apply, h1, h2]
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact G.gcd_E q hq' e he
  exact_V := by
    intro q hq hfg v hv
    obtain ⟨hv, hvk⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self]
      exact hvk
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_V q hq' hfg v hv
  exact_W := by
    intro q hq hfg w hw
    obtain ⟨hw, hwl⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self]
      exact hwl
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_W q hq' hfg w hw

theorem prime_of_mem_R {p : ℕ} (h : p ∈ G.R) : p.Prime := by
  obtain ⟨h1, -⟩ := Finset.mem_sdiff.1 h
  obtain ⟨e, -, he⟩ := Finset.mem_biUnion.1 h1
  exact Nat.prime_of_mem_primeFactors he

theorem not_mem_P_of_mem_R {p : ℕ} (h : p ∈ G.R) : p ∉ G.P := (Finset.mem_sdiff.1 h).2

/-- Minimum degree condition of KM Proposition 7.1(b)(c) / Lemma 8.5(c):
`μ(Γ(v)) ≥ (9δ/10) μ(W)` for all `v ∈ V` and `μ(Γ(w)) ≥ (9δ/10) μ(V)` for all `w ∈ W`. -/
def HighDegree : Prop :=
  (∀ v ∈ G.V, 9 * G.density / 10 * wsum G.μ G.W ≤ wsum G.μ (G.nbhdV v)) ∧
    (∀ w ∈ G.W, 9 * G.density / 10 * wsum G.μ G.V ≤ wsum G.μ (G.nbhdW w))

/-- The number `N = #{p ∈ P' \ P : f'(p) ≠ g'(p)}` of KM Proposition 8.1. -/
def newUnequal (G' G : GCDGraph) : ℕ := ((G'.P \ G.P).filter (fun p => G'.f p ≠ G'.g p)).card

end GCDGraph

end DuffinSchaeffer
