# erdos-lean

Lean 4 + Mathlib formalizations of problems from [erdosproblems.com](https://www.erdosproblems.com/).

## Erdős Problem #996 (JSP-000829) — answer: **no**

This repository contains a complete Lean 4 / Mathlib formalization of the negative answer to
Erdős Problem #996. The main theorem

```lean
theorem Erdos996.erdos_996 : ¬ Erdos996Statement
```

in `ErdosLean/Erdos996/Main.lean` shows that there is no absolute constant `C > 0` such that
`‖f − S_n f‖₂ ≪ (log log log n)^{-C}` forces `(1/N) ∑_{k<N} f(n_k x) → ∫ f` for almost every `x`
along every lacunary sequence `n_k`.

- **Statement.** `ErdosLean/Erdos996/Statement.lean` follows
  `FormalConjectures/ErdosProblems/996.lean` from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (commit `a9fb8e86c0`), used under the Apache License 2.0; see `NOTICE`.
- **Mathematics.** The argument is the dyadic spike-block counterexample of Boon Suan Ho,
  *Counterexamples for lacunary dilates via dyadic spike blocks*,
  [arXiv:2604.18535](https://arxiv.org/abs/2604.18535) (Corollary 1.4), adapted to the L² setting
  of #996. The mathematical result is due to B. S. Ho.
- **Checks.** `#print axioms Erdos996.erdos_996` reports only `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no custom `axiom` and no `native_decide`.

## Erdős Problem #1199 (JSP-001004) — answer: **yes**

This repository also contains a complete Lean 4 / Mathlib formalization of the affirmative answer
to Erdős Problem #1199 (Owings's question). The main theorems

```lean
theorem Erdos1199.erdos_1199     : Erdos1199Statement
theorem Erdos1199.erdos_1199_pos : Erdos1199StatementPos
theorem Erdos1199.erdos_1199_fc  : True ↔ ∀ (color : ℕ → Fin 2), ∃ (A : Set ℕ),
    A.Infinite ∧ ∀ n ∈ (A + A), ∀ m ∈ (A + A), color n = color m
```

in `ErdosLean/Erdos1199/Main.lean` show that for every 2-colouring of ℕ there is an infinite
set `A` such that `A + A = {a + a' : a, a' ∈ A}` (including the doubles `2a`) is monochromatic.
`erdos_1199_pos` additionally takes `A` to consist of positive integers, matching the
formulation on erdosproblems.com.

- **Statement.** `ErdosLean/Erdos1199/Statement.lean` follows
  `FormalConjectures/ErdosProblems/1199.lean` from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (commit `a14a7a739a`), used under the Apache License 2.0; see `NOTICE`.
- **Mathematics.** The argument follows §3 and Appendix A of W. Huang, Z. Lian, S. Shao, R. Xiao, L. Xu and
  S. Zhang, *An affirmative answer to Owings's sumset question*,
  [arXiv:2607.17333](https://arxiv.org/abs/2607.17333) (v3, Theorem 1.1). The mathematical
  result is due to these authors.
- **Checks.** `#print axioms` for each of the three theorems reports only `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no custom `axiom` and no
  `native_decide`.

## Erdős Problem #612 (JSP-000497) — answer: **no** (both parts are false)

This repository also contains a complete Lean 4 / Mathlib formalization showing that both parts of
the Erdős–Pach–Pollack–Tuza conjecture (Erdős Problem #612) are false. The main theorem

```lean
theorem Erdos612.erdos_612 : Erdos612Answer
```

in `ErdosLean/Erdos612/Main.lean` states

```lean
Erdos612Answer := ¬ PartI ∧ ¬ PartII ∧ ¬ PartIUniform ∧ ¬ PartIIUniform ∧
  ¬ EvenConjAt 2 ∧ ¬ OddConjAt 4
```

that is: (i) it is false that for every `r ≥ 2` every connected `K_{2r}`-free graph on `n`
vertices with minimum degree `d`, `(r-1)(3r+2) ∣ d`, has diameter at most
`2(r-1)(3r+2)/(2r²-1) · n/d + O(1)`; and (ii) it is false that for every `r ≥ 2` every connected
`K_{2r+1}`-free graph with minimum degree `d`, `3r-1 ∣ d`, has diameter at most
`(3r-1)/r · n/d + O(1)`. Each part is refuted separately, under two readings of `O(1)`: the weak
reading (the constant may depend on `r` and `d`) and the uniform reading (one constant for all
graphs). The explicit witnesses are `r = 2`, `d = 24` (`K₄`-free) for part (i) and `r = 4`,
`d = 8778` (`K₉`-free) for part (ii). The corollary
`theorem Erdos612.erdos_612_false : ¬ Erdos612Conjecture` negates the conjunction of the two parts.

- **Statement.** `ErdosLean/Erdos612/Statement.lean` was written independently from the text on
  [erdosproblems.com/612](https://www.erdosproblems.com/612) and from P. Erdős, J. Pach, R. Pollack
  and Zs. Tuza, *Radius, diameter, and minimum degree*, J. Combin. Theory Ser. B 47 (1989) 73–79.
  Formal Conjectures has no file for #612. The graphs-on-`Fin n` shape follows the Formal
  Conjectures convention and is similar to the draft by Kenta Kitamura in
  [formal-conjectures#828](https://github.com/google-deepmind/formal-conjectures/issues/828).
  No code from that draft or from any other Lean development is used.
- **Scope.** Each part is formalized as a statement about all `r ≥ 2` and refuted by one value of
  `r`. The case-by-case status for individual `r` is not formalized here. It is:

  | Part | `r` | Status | Mathematics | Lean |
  |---|---|---|---|---|
  | (i) `K_{2r}`-free | every `r ≥ 2` | false (for `d > 2(r-1)(3r+2)(2r-3)`) | Czabarka–Singgih–Székely [CSS21] | `r = 2`: this repository |
  | (ii) `K_{2r+1}`-free | `r = 1` | true | Erdős–Pach–Pollack–Tuza [EPPT89] | — |
  | (ii) `K_{2r+1}`-free | `r = 2` | true | K. Kitamura, S. Cambie (erdosproblems.com forum, 2026) | [KitaKen1/erdos-612-lean](https://github.com/KitaKen1/erdos-612-lean) |
  | (ii) `K_{2r+1}`-free | `r = 3` | false | K. Kitamura, S. Cambie (erdosproblems.com forum, 2026) | [KitaKen1/erdos-612-lean](https://github.com/KitaKen1/erdos-612-lean) (uniform reading, 2026-09-08) |
  | (ii) `K_{2r+1}`-free | every `r ≥ 4` | false | H. Chen–Y. Chen [CC26] | `r = 4`: this repository |

  In particular, a Lean refutation of part (ii) in the uniform reading (at `r = 3`) was already
  public in KitaKen1/erdos-612-lean before this development. What is new here is a single Lean
  theorem that covers both parts of the statement, in both readings of `O(1)`, including the
  first Lean refutation of part (i).
- **Mathematics.** Part (i) uses the construction of É. Czabarka, I. Singgih and L. A. Székely,
  *Counterexamples to a conjecture of Erdős, Pach, Pollack and Tuza*, J. Combin. Theory Ser. B 151
  (2021) 38–45, [doi:10.1016/j.jctb.2021.06.001](https://doi.org/10.1016/j.jctb.2021.06.001)
  [CSS21]. Theorem and figure numbers in the Lean files refer to the preprint
  [arXiv:2009.02611v1](https://arxiv.org/abs/2009.02611) (titled *On the maximum diameter of
  k-colorable graphs*): §3, Figure 1, Lemma 5 and Theorem 6, with `r = 2`, `δ = 24`. Part (ii) uses
  the construction of Hangdi Chen and Yaojun Chen, *Counterexamples to two conjectures on the
  diameter of clique-free graphs*, [arXiv:2609.03346](https://arxiv.org/abs/2609.03346) (v1,
  Theorem 2.7) [CC26], with `r = 4`, `δ = 8778`. Both are blow-ups of periodic weighted layered
  clique graphs. Their local properties are checked by kernel `decide` on a two-period instance and
  extended to all periods by a general window lemma. The mathematical results are due to these
  authors.
- **Checks.** `#print axioms` for both theorems reports only `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no custom `axiom` and no `native_decide`.

## Erdős Problem #514 (JSP-000412) — answer: **yes**

This repository also contains a complete Lean 4 / Mathlib formalization of the affirmative answer
to the first question of Erdős Problem #514, which is the question catalogued as JSP-000412. The
main theorem

```lean
theorem Erdos514.erdos_514 : Erdos514Statement
```

in `ErdosLean/Erdos514/Main.lean` shows that every transcendental entire function `f` (entire
and not a polynomial) has a continuous path `γ : ℝ → ℂ` with `‖γ t‖ → ∞` such that
`‖f (γ t) / γ t ^ n‖ → ∞` as `t → ∞` for every `n : ℕ`, i.e. `|f|` grows faster than every
polynomial along the path. The second and third questions on erdosproblems.com (length of the
path, growth relative to `M(r)`) are not part of JSP-000412 and are not formalized here.

- **Statement.** `ErdosLean/Erdos514/Statement.lean` was written from the problem text;
  `google-deepmind/formal-conjectures` has no file for Problem 514.
- **Mathematics.** erdosproblems.com records that Boas (unpublished) proved this part. The
  result is implicit in J. L. Lewis, J. Rossi and A. Weitsman, *On the growth of subharmonic
  functions along paths*, Ark. Mat. 22 (1984), 109–119, and follows directly from Jang-Mei Wu,
  *Length of paths for subharmonic functions*, J. London Math. Soc. (2) 32 (1985), 497–505,
  Theorem B ([doi:10.1112/jlms/s2-32.3.497](https://doi.org/10.1112/jlms/s2-32.3.497)), applied
  to `log⁺ |f|`, as pointed out by P. Chojecki and N. Sothanaphan in the
  [forum thread](https://www.erdosproblems.com/forum/thread/514). The mathematical result is due
  to these authors. The Lean proof does not formalize Wu's theorem; it is a self-contained
  argument: iterated Taylor shifts `shift f n` (entire and transcendental), unbounded tracts of
  their superlevel sets (maximum modulus principle), a Carleman-type estimate showing that
  `log |g|` grows at least like `c √r` in a tract whose complement meets every large circle, and a
  nested chain of tracts through which the path runs.
- **Checks.** `#print axioms Erdos514.erdos_514` reports only `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no custom `axiom` and no `native_decide`.

## Erdős Problem #956 (JSP-000796) — answer: **yes** (lower bound `h(n) ≫ n^{4/3}`)

This repository also contains a complete Lean 4 / Mathlib formalization of the affirmative answer
to the question of Erdős Problem #956. Here `h(n)` is the maximal number of pairs at set-distance
exactly 1 among `n` pairwise disjoint translates of one compact convex set in the plane. The main
theorems

```lean
theorem Erdos956.erdos956      : Erdos956Statement
theorem Erdos956.erdos956_main : Erdos956Statement ∧ Erdos956LowerBound ∧ Erdos956AllExponents
```

in `ErdosLean/Erdos956/Main.lean` show that there is `c > 0` with `h(n) > n^{1+c}` for all large
`n` (`Erdos956Statement`, the question as posed), that `h(n) ≥ c₀ n^{4/3}` for some `c₀ > 0` and all
large `n` (`Erdos956LowerBound`), and that `h(n) > n^{1+c}` eventually for every `c < 1/3`
(`Erdos956AllExponents`).

- **Scope.** The problem asks to "determine `h(n)`". The answer in the literature is
  `h(n) = Θ(n^{4/3})`. Only the lower bound is formalized here. The upper bound
  `h(n) ≪ n^{4/3}` of Erdős and Pach (Combinatorica 10 (1990), 261–269) needs the crossing lemma,
  which is not in Mathlib. It is stated as `ErdosPachUpperBound` but **not proved**.
  `Erdos956.erdos956_theta_of_upper` derives `h(n) = Θ(n^{4/3})` from it, taking the upper bound
  as a hypothesis.
- **Statement.** `ErdosLean/Erdos956/Statement.lean` was written from scratch from the text of
  erdosproblems.com/956, because formal-conjectures has no file for #956. `h n` is an `sSup` over `ℕ`.
  The set of achievable counts is bounded, so this is a genuine maximum.
- **Mathematics.** The lower bound is due to Pavel Valtr. He announced `t₂(n) = Θ(n^{4/3})` in
  *The unit-distance problem for convex sets*, Oberwolfach Reports 2 (2005), Report 17/2005
  ([doi:10.4171/OWR/2005/17](https://doi.org/10.4171/OWR/2005/17)). The parabolic-grid mechanism
  appears in his manuscript *Strictly convex norms allowing many unit distances and related
  touching questions* ([kam.mff.cuni.cz/~valtr/n.pdf](https://kam.mff.cuni.cz/~valtr/n.pdf)).
  The formalization follows the self-contained note *Unit distances between disjoint convex
  translates* (27 April 2026, [ulam.ai/research/erdos956.pdf](https://www.ulam.ai/research/erdos956.pdf)).
  The note adapts Valtr's construction to disjoint translates. It was generated with GPT-5.5 Pro
  and posted by Przemek Chojecki on the
  [erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/956).
- **Prior Lean.** The Lean file that accompanies the note
  ([ulam.ai/research/erdos956.lean](https://www.ulam.ai/research/erdos956.lean), produced with
  Aristotle) formalizes only the counting and asymptotic arithmetic of the construction. It does
  not define `h(n)` or prove any statement about it. This repository does not use it.
- **Checks.** `#print axioms` for `Erdos956.erdos956` and `Erdos956.erdos956_main` reports only
  `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no custom `axiom` and no
  `native_decide`.

## Erdős Problem #265 (JSP-000229) — partial: **51/50 ≤ β\* ≤ 2** (optimal exponent open)

This repository contains a Lean 4 / Mathlib formalization of the two known halves of
Erdős Problem #265. This is **not** a complete answer: the problem remains open on
erdosproblems.com, because the optimal doubly exponential exponent is unknown. The main theorems

```lean
theorem Erdos265.erdos_265        : Erdos265Statement
theorem Erdos265.erdos_265_limsup : Erdos265LimsupNegative
theorem Erdos265.growth_half      : ∃ a : ℕ → ℕ, IsRationalPair a ∧
    Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (51 / 50 : ℝ) ^ n)) atTop atTop
```

are in `ErdosLean/Erdos265/Main.lean`. Here `IsRationalPair a` means that `a` is strictly
increasing with `2 ≤ a 0`, and that `∑ 1/aₙ` and `∑ 1/(aₙ − 1)` are summable with rational
sums. `Erdos265Statement` says that
(1) some admissible sequence satisfies `aₙ^{1/βⁿ} → ∞` for some `β > 1`,
(2) some admissible sequence satisfies `aₙ^{1/n} → ∞`, and
(3) every admissible sequence satisfies `aₙ^{1/2ⁿ} → 1`.
If `β*` is the supremum of the achievable exponents, then (1) with `β = 51/50` and (3) together give
`51/50 ≤ β* ≤ 2`. The exact value of `β*` is still open.

- **Statement.** `ErdosLean/Erdos265/Statement.lean`. The shapes of `IsRationalPair` and
  `Erdos265LimsupNegative` come from
  [KitaKen1/erdos-265-lean](https://github.com/KitaKen1/erdos-265-lean), used under the
  Apache License 2.0; see `NOTICE`.
- **Mathematics (growth half).** V. Kovač and T. Tao, *On several irrationality problems for
  Ahmes series*, [arXiv:2406.17593](https://arxiv.org/abs/2406.17593) (v4, Theorem 2.8 and
  Corollary 2.9 with `d = 2`, proved in §7); Acta Math. Hungar. 175 (2025), 572–608,
  [doi:10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0). Their result uses
  `1/aₙ` and `1/(aₙ+1)`, so we shift the index by one. Our parameters differ from the paper's:
  `N_k = 4^{m_k}`, `M_k = 2^{m_k}`, `m_0 = 40`, `m_{k+1} = m_k + ⌊m_k/10⌋ + 1`,
  `f₂(x) = 1/(x(x−1))` and `β = 51/50`, so the constants are not the ones in the paper. The
  mathematical result is due to Kovač and Tao. As far as we know, this is the first Lean
  formalization of the Kovač–Tao construction.
- **Mathematics (barrier half).** Kenta Kitamura proved that `aₙ^{1/2ⁿ} → 1` for every admissible
  sequence, which settles the `limsup aₙ^{1/2ⁿ} > 1` sub-question negatively. He also
  formalized it first, in [KitaKen1/erdos-265-lean](https://github.com/KitaKen1/erdos-265-lean)
  (2026-09-07). `barrier_half` here is an independent Lean formalization of Kitamura's
  argument (tail envelope, square recurrence, second residual). The mathematics of this half
  is due to K. Kitamura.
- **Checks.** `#print axioms` for `erdos_265`, `erdos_265_limsup`, `growth_half` and
  `barrier_half` reports only `propext`, `Classical.choice` and `Quot.sound`. There is no
  `sorry`, no custom `axiom` and no `native_decide`.
- **AI assistance.** The Lean code for this result was written with substantial AI assistance
  (Claude, Anthropic), including proof search and drafting of the documentation. It was checked by
  the Lean kernel and reviewed by HongJin HE.

## Erdős Problem #995 (JSP-000828): growth is **N (log N)^{1/2+o(1)}**

This repository also contains a complete Lean 4 / Mathlib formalization of the answer to
Erdős Problem #995. The main theorem

```lean
theorem Erdos995.erdos_995 : Erdos995Answer
```

in `ErdosLean/Erdos995/Main.lean` proves the conjunction of four statements:

1. **Upper bound** (`ErdosUpperBound`). For every lacunary `(n_k)`, every `f ∈ L²(𝕋)` and every
   `ε > 0`, for almost every `x`, `∑_{k<N} f(n_k x) = o(N (log N)^{1/2+ε})`.
   The Lean proof works for every integer sequence, lacunary or not.
2. **Lower bound** (`HoLowerBound`). There are a real-valued mean-zero `f ∈ L²(𝕋)` and a sequence
   `(n_k)` with `n_0 ≥ 1` and `n_{k+1} ≥ 2 n_k` such that, for almost every `x` and every `ε > 0`,
   `limsup_N ∑_{k<N} f(n_k x) / (N (log N)^{1/2−ε}) = +∞`.
3. **Critical exponent** (`Erdos995CriticalExponent`). The a.e. bound `O(N (log N)^θ)` holds for
   every lacunary `(n_k)` and every `f ∈ L²` when `θ > 1/2`. It fails for some `(n_k)` and `f`
   when `θ < 1/2`.
4. **The concrete question** (`¬ LogLogQuestion`). The bound `∑_{k≤N} f(n_k x) = o(N √(log log N))`
   a.e. is false in general.

`Erdos995.erdos_995_logLog : ¬ LogLogQuestion` states item 4 on its own.

- **Statement.** `ErdosLean/Erdos995/Statement.lean` transcribes the problem text of
  [erdosproblems.com/995](https://www.erdosproblems.com/995). The definition `IsLacunary` and the
  conventions (the circle `AddCircle 1` with Haar measure, `f({α n_k})` written as `f (n_k • x)`)
  come from `FormalConjectures/ErdosProblems/996.lean` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (commit `a9fb8e86c0`), used under the Apache License 2.0; see `NOTICE`. Formal Conjectures has
  no statement of #995.
- **Mathematics.** The lower bound is Theorem 1.6 (`p = 2`) of Boon Suan Ho,
  *Counterexamples for lacunary dilates via dyadic spike blocks*,
  [arXiv:2604.18535](https://arxiv.org/abs/2604.18535) (v2). The upper bound was stated by
  P. Erdős, *Problems and results on diophantine approximations*, Compositio Math. **16** (1964),
  52–65. Its elementary proof is Remark 7.1 of Ho's paper. The mathematical results are due to
  these authors. The formalization reuses the spike, block and hit-event machinery of
  `ErdosLean/Erdos996/`.
- **Scope.** The problem asks to "estimate the growth". The formalization records the
  worst-case answer `N (log N)^{1/2+o(1)}`, which B. S. Ho proposed as a resolution on the
  [erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/995). As of 2026-09-19,
  erdosproblems.com still lists #995 as open.
- **Checks.** `#print axioms Erdos995.erdos_995` reports only `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no custom `axiom` and no `native_decide`.

## Erdős Problem #790 (JSP-000649): `l(n) = n^{1-o(1)}`; answers **yes** and **no**

This repository also contains a complete Lean 4 / Mathlib formalization of the lower bound
`l(n) ≫ n/(log n)²` for Erdős Problem #790 and of its consequences for the two questions. The
main theorem

```lean
theorem Erdos790.erdos_790 : Erdos790Answer
```

in `ErdosLean/Erdos790/Main.lean` concerns `l(n)`, the largest `k` such that every set of `n`
integers contains a sum-free subset of size at least `k`. Here `B` is sum-free if no element of
`B` is the sum of two or more distinct other elements of `B`. The theorem proves five statements:

1. **Lower bound.** There is `c > 0` with `c · n / (log n)² ≤ l(n)` for all `n ≥ 2`. The proof
   gives `c = 1/1024`.
2. **Trivial upper bound.** `l(n) ≤ n` for all `n`.
3. **First question: yes.** `l(n) / √n → ∞`.
4. **Exponent.** For every `ε > 0`, `n^{1-ε} ≤ l(n)` for all large `n`, so `l(n) = n^{1-o(1)}`.
   This is the conjecture of Choi, Komlós and Szemerédi.
5. **Second question: no.** There is no `c > 0` such that `l(n) < n^{1-c}`, not even for
   infinitely many `n`.

- **Statement.** `ErdosLean/Erdos790/Statement.lean` was written from the problem text on
  [erdosproblems.com/790](https://www.erdosproblems.com/790). Formal Conjectures has no file for
  #790. `IsSumFree B` says that no `x ∈ B` equals `∑ S` for a set `S ⊆ B` with `x ∉ S` and
  `|S| ≥ 2`, that is, no `a₁ = a₂ + ⋯ + a_r` with `r ≥ 3` and all `aᵢ ∈ B` distinct. `l n` is the
  `sSup` of the admissible `k`, which is the literal reading of "`l(n)` maximal such that ...".
- **Mathematics.** The argument is Theorem 1 of Samuel Korsky, *Large Sum-Free Subsets of Sets of
  Integers* (preprint, 13 September 2026). It was posted as a
  [proof claim on the erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/790/proof-claims)
  on 2026-09-13. The paper says the main idea was developed by GPT Astra. The mathematical
  result is due to S. Korsky. In the Lean proof the random choice of dyadic intervals is replaced
  by an averaging argument over all colourings, and all constants are explicit.
- **Scope.** The problem asks to "estimate" `l(n)`. The formalization records the exponent
  (`l(n) = n^{1-o(1)}`) and answers both specific questions. It does not formalize the upper bound
  `l(n) ≪ n / log n` of Choi, Komlós and Szemerédi (Trans. Amer. Math. Soc. 212 (1975),
  307–313). The gap between `n/(log n)²` and `n/log n` is still open. As of 2026-09-19,
  erdosproblems.com still lists #790 as open and Korsky's proof has not appeared in a journal or
  on arXiv.
- **Checks.** `#print axioms Erdos790.erdos_790` reports only `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no custom `axiom` and no `native_decide`.
- **AI assistance.** The Lean code for this result was written with substantial AI assistance
  (Claude, Anthropic), including proof search and drafting of the documentation. It was checked by
  the Lean kernel and reviewed by HongJin HE.

## The Duffin–Schaeffer theorem, Erdős Problem #999 (JSP-000832): answer **yes**

This repository also contains a complete Lean 4 / Mathlib formalization of the Duffin–Schaeffer
theorem of Koukoulopoulos and Maynard, for an arbitrary real accuracy function
`ψ : ℕ → [0, ∞)`. The main theorems

```lean
theorem DuffinSchaeffer.duffin_schaeffer : DuffinSchaefferStatement
theorem DuffinSchaeffer.erdos_999        : Erdos999Statement
```

are in `ErdosLean/DuffinSchaeffer/Main.lean`. For every `ψ : ℕ → ℝ` with `ψ q ≥ 0` for all `q`,
`DuffinSchaefferStatement` proves the following four statements:

1. For almost every real `α`, `|α − a/q| < ψ(q)/q` has infinitely many solutions
   `(a, q) ∈ ℤ × ℕ` with `q ≥ 1` and `gcd(a, q) = 1`, **if and only if**
   `∑_{q ≥ 1} φ(q) ψ(q) / q = ∞`.
2. The same equivalence with `≤` in place of `<`. This is inequality (1.7) of Koukoulopoulos–Maynard.
3. The same equivalence (with `<`) for almost every `α ∈ [0, 1]`, which is the setting of
   Koukoulopoulos–Maynard, Theorem 1.
4. If the series converges, then for almost every `α` there are only finitely many solutions,
   even with `≤`. This is the Borel–Cantelli direction (1.5).

"Almost every" refers to Lebesgue measure on `ℝ`, or to Lebesgue measure restricted to `[0, 1]`
in item 3. Divergence of the series is written `¬ Summable`, which for nonnegative terms means
that the series sums to `+∞`. `Erdos999Statement` is the wording of
[erdosproblems.com/999](https://www.erdosproblems.com/999) with `f : ℕ → ℕ`. It is the special case of
item 1 for integer-valued `ψ`.

- **Statement.** `ErdosLean/DuffinSchaeffer/Statement.lean` was written from scratch from the
  catalog entry, from [erdosproblems.com/999](https://www.erdosproblems.com/999) and from
  Theorem 1 of the paper. Formal Conjectures has no file for #999.
- **Mathematics.** D. Koukoulopoulos and J. Maynard, *On the Duffin–Schaeffer conjecture*,
  Ann. of Math. (2) **192** (2020), no. 1, 251–307,
  [doi:10.4007/annals.2020.192.1.5](https://doi.org/10.4007/annals.2020.192.1.5)
  ([arXiv:1907.04593](https://arxiv.org/abs/1907.04593)), Theorem 1. The mathematical result is
  due to Koukoulopoulos and Maynard. The formalization follows their proof: the overlap estimate
  of Pollington–Vaughan (their Lemma 5.3), the reduction to Proposition 5.4, and the GCD-graph
  iteration of §§6–14 (Propositions 6.3, 7.1, 8.1–8.3). Gallagher's zero-one law is taken from
  Mathlib (`AddCircle.addWellApproximable_ae_empty_or_univ`). Where it is convenient, the constants differ
  from the paper. For example, `t ≥ 10^2000` in place of `t ≥ 300`, and a geometric weight
  `(20/21)^{|k−ℓ|}` in Lemma 12.1. The Hall–Tenenbaum bound used in Lemma 7.3 is replaced by
  an elementary estimate. No result of the paper is assumed.
- **Prior Lean.** [plby/lean-proofs](https://github.com/plby/lean-proofs) contains
  `ErdosProblems/Erdos999.lean` (formal authors credited there: Codex and GPT-5.6 Sol), which
  proves the `f : ℕ → ℕ` wording of erdosproblems.com. There every nonzero radius `f(q)/q` is at
  least `1/q`, and real-valued `ψ` is not covered. The Lean
  statement of Koukoulopoulos–Maynard's Theorem 1 in
  [ImperialCollegeLondon/AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge)
  and the blueprint [korbonits/duffin-schaeffer-blueprint](https://github.com/korbonits/duffin-schaeffer-blueprint)
  have no proof. Some auxiliary second-moment lemmas in
  `ErdosLean/DuffinSchaeffer/Parts/MeasureLower.lean` are adapted from
  `ErdosProblems/Erdos1165/SecondMoment.lean` in plby/lean-proofs (Copyright 2026 The Formal
  Conjectures Authors), used under the Apache License 2.0; see `NOTICE`.
- **Checks.** `#print axioms` for `DuffinSchaeffer.duffin_schaeffer` and
  `DuffinSchaeffer.erdos_999` reports only `propext`, `Classical.choice` and `Quot.sound`. There
  is no `sorry`, no custom `axiom` and no `native_decide`.
- **AI assistance.** The Lean code for this result was written with substantial AI assistance
  (Claude, Anthropic), including proof search and drafting of the documentation. It was checked by
  the Lean kernel and reviewed by HongJin HE.

## Erdős Problem #494 (JSP-000399) — answer: **yes** for all sufficiently large `|A|` (Gordon–Fraenkel–Straus)

This repository also contains a complete Lean 4 / Mathlib formalization of the
Gordon–Fraenkel–Straus theorem, which answers Erdős Problem #494. The main theorems

```lean
theorem Erdos494.gordon_fraenkel_straus : GFSStatement
theorem Erdos494.erdos_494              : Erdos494Full
```

in `ErdosLean/Erdos494/Main.lean` state

```lean
GFSStatement := ∀ k > 2, ∀ᶠ card in atTop, Erdos494Unique k card
Erdos494Full := (∀ k > 2, ¬ Erdos494Unique k k) ∧ (∀ k > 2, ¬ Erdos494Unique k (2 * k)) ∧
  GFSStatement
```

where `sumMultiset A k` is the multiset `A_k` of all sums of `k` distinct elements of a finite
set `A ⊂ ℂ`, and `Erdos494Unique k n` says that any two sets `A, B ⊂ ℂ` with `|A| = |B| = n` and
`A_k = B_k` are equal. So for every `k > 2` there is a threshold `N(k)` such that every finite set
`A ⊂ ℂ` with `|A| ≥ N(k)` is determined by `A_k` and `|A|`. `erdos_494` also records why a size
condition is needed: uniqueness fails for `|A| = k` (Kruyt) and for `|A| = 2k` (Tao), for every
`k > 2`.

- **Statement.** `ErdosLean/Erdos494/Statement.lean` copies the definitions `sumMultiset`,
  `Erdos494Unique` and the statements of `erdos_494.variants.gordon_fraenkel_straus`,
  `k_eq_card` and `card_eq_2k` verbatim from `FormalConjectures/ErdosProblems/494.lean` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (commit `1e668fa332`), used under the Apache License 2.0; see `NOTICE`. The repository does not
  depend on Formal Conjectures.
- **Mathematics.** The theorem is due to B. Gordon, A. S. Fraenkel and E. G. Straus, *On the
  determination of sets by the sets of sums of a certain order*, Pacific J. Math. **12** (1962),
  no. 1, 187–196 ([doi:10.2140/pjm.1962.12.187](https://doi.org/10.2140/pjm.1962.12.187)), §4.
  The algebraic reduction is from J. L. Selfridge and E. G. Straus, *On the determination of
  numbers by their sums of a fixed order*, Pacific J. Math. **8** (1958), no. 4, 847–856
  ([doi:10.2140/pjm.1958.8.847](https://doi.org/10.2140/pjm.1958.8.847)). The counterexamples
  for `|A| = k` and `|A| = 2k` are due to D. Kruyt and T. Tao, as recorded on
  [erdosproblems.com/494](https://www.erdosproblems.com/494). The mathematical results are due to
  these authors.
- **Proof route.** Power sums and Newton's identities reduce uniqueness for `|A| = n` to the
  non-vanishing of the integer `f_k(n, j) = Σ_{i=1}^{k} (-1)^{i-1} i^{j-1} C(n, k-i)` for all
  `j ≥ 1` (`unique_of_gfsPoly_ne_zero`). The number-theoretic core `gfs_core` proves this for
  large `n`, following §4 of the paper: bounded `j` is elementary; for large `j`, `f_k(n, j) = 0`
  forces two `(k+1)`-smooth integers to be very close, which a gap theorem for smooth numbers
  rules out except in an exact case that is handled directly.
- **Ridout's theorem.** Gordon, Fraenkel and Straus quote Ridout's `p`-adic Thue–Siegel–Roth
  theorem for the gap theorem. That theorem is not in Mathlib, and this repository does not assume
  it. The development proves the special case it needs (`smooth_gap`, `ridout_smooth`): for
  coprime `P`-smooth `x, y`, `|x - y| ≥ max(x, y)^{1-δ}` once `max(x, y)` is large. The proof
  uses Mahler's reduction to rational approximations of `(b/a)^{1/r}`, and a Thue–Siegel–Dyson
  type theorem (`dyson_binomial`, exponent `10√r`) proved by Roth's method in two variables:
  Siegel's lemma (Mathlib), and Roth's lemma for two variables with the Wronskian proof of
  W. M. Schmidt, *Diophantine Approximation*, LNM 785, Ch. V. The full `p`-adic Ridout theorem
  is not formalized.
- **Checks.** `#print axioms` for `Erdos494.erdos_494` and `Erdos494.gordon_fraenkel_straus`
  reports only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no custom
  `axiom` and no `native_decide`. No published theorem is taken as a hypothesis.
- **AI assistance.** The Lean code for this result was written with substantial AI assistance
  (Claude, Anthropic), including proof search and drafting of the documentation. It was checked by
  the Lean kernel and reviewed by HongJin HE.

## Build

Toolchain pinned in `lean-toolchain`; Mathlib pinned in `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

## Authorship

Formalization by HongJin HE ([@hongjin-he](https://github.com/hongjin-he)), with AI assistance (Claude).
Per-result provenance (mathematical authors, statement source, formalization author, first complete
commit) is recorded in [`data/sources.yaml`](data/sources.yaml).

## License

Apache License 2.0 (see `LICENSE` and `NOTICE`).
