# Lean Formalization Portfolio

Lean 4 + Mathlib formalizations, written from scratch for practice.

## Module 1: Order theory (`LeanFormalizationPortfolio/Order/`)

| File | Contents |
|---|---|
| `KnasterTarski.lean` | `lfp`, `gfp` on a complete lattice. Fixed-point theorems, leastness/greatestness, monotonicity of `lfp` |
| `SchroederBernstein.lean` | Cantor–Schröder–Bernstein proved using `lfp` from the previous file |

Informal proofs: [`docs/informal_proofs.md`](docs/informal_proofs.md).

Mathlib already has these results (`OrderHom.lfp`, `Function.Embedding.schroeder_bernstein`).
The proofs here are independent re-developments for learning.

## Build

```
lake update
lake exe cache get
lake build
```
On Windows you can run `./setup.ps1`. No `sorry` is used in this repository.

## Planned modules
Number theory (Fermat n = 4), combinatorics (Mantel, Erdős–Szekeres), analysis (Weierstrass), group theory (groups of order pq).
