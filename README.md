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
