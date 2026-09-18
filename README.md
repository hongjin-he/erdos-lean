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
