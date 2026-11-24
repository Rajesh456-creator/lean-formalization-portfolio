![Lean CI](https://github.com/Rajesh456-creator/lean-formalization-portfolio/actions/workflows/lean_action_ci.yml/badge.svg)

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

## Module 2: Finite Ramsey theory (`LeanFormalizationPortfolio/Combinatorics/`)

| File | Result |
|---|---|
| `Ramsey33.lean` | `R(3,3) = 6`: every 2-colouring of the pairs of a 6-set has a monochromatic triangle; the pentagon colouring of a 5-set has none. Corollary: the "party of six" problem |
| `VanDerWaerden.lean` | `W(2;3) = 9`: every 2-colouring of `{0..8}` has a monochromatic 3-term AP; `RRBBRRBB` on `{0..7}` has none |
| `Schur.lean` | `S(2) = 4`: every 2-colouring of `{1..5}` has a monochromatic `x + y = z`; a colouring of `{1..4}` has none |

These files use only core Lean (no Mathlib import).

## Build

```
lake update
lake exe cache get
lake build
```
On Windows you can run `./setup.ps1`. No `sorry` is used in this repository.

## Planned modules
Number theory (Fermat n = 4), combinatorics (Mantel, Erdős–Szekeres), analysis (Weierstrass), group theory (groups of order pq).
