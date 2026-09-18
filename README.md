# erdos-lean

Lean 4 + Mathlib formalizations of problems from [erdosproblems.com](https://www.erdosproblems.com/) and related open-problem lists.

- Toolchain: see `lean-toolchain`; Mathlib pinned in `lake-manifest.json`.
- Every main theorem is checked with `#print axioms` and uses only `propext`, `Classical.choice`, `Quot.sound` — no `sorry`, no custom `axiom`, no `native_decide`.

Build:

```bash
lake exe cache get
lake build
```

Author: HongJin HE ([@hongjin-he](https://github.com/hongjin-he))
