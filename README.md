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

## Build

Toolchain pinned in `lean-toolchain`; Mathlib pinned in `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

## Authorship

Formalization by HongJin HE ([@hongjin-he](https://github.com/hongjin-he)), with AI assistance (Claude).

## License

Apache License 2.0 (see `LICENSE` and `NOTICE`).
