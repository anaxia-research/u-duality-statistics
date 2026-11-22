# U-Duality Statistics

Lean 4 formalization accompanying *Arithmetic Statistics of U-Duality Orbits I: The Mass of Integral E₇ Black Hole Charges* (Deep Bhattacharjee).

| File | Content |
|---|---|
| `UDuality/FiniteField.lean` | Albert algebra counts, level-set counts of the E₇ quartic over 𝔽_q (Theorem A), rank strata and orbit–stabiliser identities |
| `UDuality/Igusa.lean` | Igusa zeta functions of the cubic norm and of the quartic: the residue-class linear systems and their closed-form solutions, for the trivial and the quadratic character |
| `UDuality/Densities.lean` | Denef–Meuser functional equation, generating function of the local densities (Theorem B), corollary factorisations |
| `UDuality/Cubes.lean` | Invariance of the quartic form for the triple system over R³ (Bhargava cubes) and the slice lemma |

Build (Lean v4.36.0, Mathlib v4.36.0):

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

All 48 theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see `axioms.txt`.
