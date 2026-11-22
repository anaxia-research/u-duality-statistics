# U-Duality Statistics

Lean 4 formalization accompanying the series *Arithmetic Statistics of U-Duality Orbits* (Deep Bhattacharjee):

- Part I: The Mass of Integral E₇ Black Hole Charges
- Part II: Quarter-BPS Dyons in Heterotic String Theory

| File | Content |
|---|---|
| `UDuality/FiniteField.lean` | Albert algebra counts, level-set counts of the E₇ quartic over 𝔽_q (Theorem A), rank strata and orbit–stabiliser identities |
| `UDuality/Igusa.lean` | Igusa zeta functions of the cubic norm and of the quartic: the residue-class linear systems and their closed-form solutions, for the trivial and the quadratic character |
| `UDuality/Densities.lean` | Denef–Meuser functional equation, generating function of the local densities (Theorem B), corollary factorisations |
| `UDuality/Cubes.lean` | Invariance of the quartic form for the triple system over R³ (Bhargava cubes) and the slice lemma |
| `UDuality/Dyons.lean` | Part II: S-duality transformation of the quartic invariant and of the attractor equation, discriminants under substitution, Witt count from orthogonal group orders (all ranks), finite-field counts of Δ = Q²P² − (Q·P)² on the Narain lattice, Euler factors |

Build (Lean v4.36.0, Mathlib v4.36.0):

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

All 57 theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see `axioms.txt`.
