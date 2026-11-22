import Mathlib

/-!
# Part II: dyons in heterotic string theory on `T⁶`

Algebraic identities behind the classification and counting of quarter-BPS dyon charges
`(Q, P)` under `SL₂(ℤ) × O(6,22;ℤ)`.  We write `A = Q²`, `B = Q·P`, `C = P²`.
-/

namespace UDuality.Dyons

open Finset

section Sduality

variable {R : Type*} [CommRing R]

/-- Gram entries after the S-duality move `(Q, P) ↦ (aQ + bP, cQ + dP)`. -/
def A' (a b A B C : R) : R := a ^ 2 * A + 2 * a * b * B + b ^ 2 * C
def B' (a b c d A B C : R) : R := a * c * A + (a * d + b * c) * B + b * d * C
def C' (c d A B C : R) : R := c ^ 2 * A + 2 * c * d * B + d ^ 2 * C

/-- The quartic invariant `Δ = Q²P² - (Q·P)²` is multiplied by `(ad - bc)²`. -/
theorem delta_transform (a b c d A B C : R) :
    A' a b A B C * C' c d A B C - B' a b c d A B C ^ 2 = (a * d - b * c) ^ 2 * (A * C - B ^ 2) := by
  unfold A' B' C'; ring

/-- Equivariance of the attractor equation `P² z² - 2 (Q·P) z + Q² = 0`: with
`w = (a z + b)/(c z + d)`, cleared of denominators. -/
theorem attractor_equivariant (a b c d A B C z : R) :
    C' c d A B C * (a * z + b) ^ 2 - 2 * B' a b c d A B C * (a * z + b) * (c * z + d)
      + A' a b A B C * (c * z + d) ^ 2 = (a * d - b * c) ^ 2 * (C * z ^ 2 - 2 * B * z + A) := by
  unfold A' B' C'; ring

/-- If `z` solves the attractor equation for `(Q,P)` then `w = (az+b)/(cz+d)` solves it for the
transformed charges (over a field, with `cz + d ≠ 0`). -/
theorem attractor_root {K : Type*} [Field K] (a b c d A B C z : K) (hz : C * z ^ 2 - 2 * B * z + A = 0)
    (h : c * z + d ≠ 0) :
    C' c d A B C * ((a * z + b) / (c * z + d)) ^ 2
      - 2 * B' a b c d A B C * ((a * z + b) / (c * z + d)) + A' a b A B C = 0 := by
  have key := attractor_equivariant a b c d A B C z
  rw [hz, mul_zero] at key
  set w := (a * z + b) / (c * z + d) with hwdef
  have hw : w * (c * z + d) = a * z + b := div_mul_cancel₀ _ h
  rw [← hw] at key
  have e : (c * z + d) ^ 2 * (C' c d A B C * w ^ 2 - 2 * B' a b c d A B C * w + A' a b A B C) = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp e with h0 | h0
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) h
  · exact h0

/-- Discriminant of a binary form `n u² + ℓ u v + m v²` after substitution by an integer matrix:
`disc (g ∘ M) = (det M)² disc g`. -/
theorem disc_comp (n l m α β γ δ : R) :
    let n' := n * α ^ 2 + l * α * γ + m * γ ^ 2
    let l' := 2 * n * α * β + l * (α * δ + β * γ) + 2 * m * γ * δ
    let m' := n * β ^ 2 + l * β * δ + m * δ ^ 2
    l' ^ 2 - 4 * n' * m' = (α * δ - β * γ) ^ 2 * (l ^ 2 - 4 * n * m) := by
  intro n' l' m'; simp only [n', l', m']; ring

end Sduality

section FiniteField

variable {R : Type*} [CommRing R]

/-- `|O^ε(2m, q)| = 2 q^{m(m-1)} (q^m - ε) ∏_{i=1}^{m-1} (q^{2i} - 1)`. -/
def ordO (q e : R) (m : ℕ) : R :=
  2 * q ^ (m * (m - 1)) * (q ^ m - e) * ∏ i ∈ range (m - 1), (q ^ (2 * (i + 1)) - 1)

/-- Witt count: the number of pairs `(Q, P)` in the split space of dimension `2(m+1)` with a
given nondegenerate Gram matrix of determinant `t` is `|O⁺(2m+2)| / |O^ε(2m)|` with
`ε = η(-t)`, and equals `q^{2m} (q^{m+1} - 1)(q^m + ε)`. -/
theorem witt_count (q e : R) (he : e ^ 2 = 1) (m : ℕ) (hm : 1 ≤ m) :
    ordO q 1 (m + 1) = ordO q e m * (q ^ (2 * m) * (q ^ (m + 1) - 1) * (q ^ m + e)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : (q ^ (k + 1) - e) * (q ^ (k + 1) + e) = q ^ (2 * (k + 1)) - 1 := by
    linear_combination (-1 : R) * he
  unfold ordO
  simp only [Nat.add_sub_cancel, prod_range_succ]
  linear_combination (-(2 * q ^ ((k + 1) * k) * q ^ (2 * (k + 1)) * (q ^ (k + 1 + 1) - 1)
      * ∏ i ∈ range k, (q ^ (2 * (i + 1)) - 1))) * h1

/-- Symmetric `2 × 2` matrices of determinant `t ≠ 0` over `𝔽_q`: `q(q-1) + (1+η(-t)) q`. -/
theorem ternary_count (q e : R) : q * (q - 1) + (1 + e) * q = q ^ 2 + e * q := by ring

/-- Theorem D for the lattice `II_{6,22}` (`2k = 28`). -/
theorem countD (q e : R) :
    q ^ 26 * (q ^ 14 - 1) * (q ^ 13 + e) * (q ^ 2 + e * q)
      = q ^ 27 * (q ^ 14 - 1) * (q ^ 13 + e) * (q + e) := by ring

/-- The zero level: `q^{56} - (q-1)/2 · (count(+1) + count(-1)) = q^{55} + q^{28} - q^{27}`. -/
theorem countD_zero (q : R) :
    2 * q ^ 56 - (q - 1) * (q ^ 27 * (q ^ 14 - 1) * (q ^ 13 + 1) * (q + 1)
      + q ^ 27 * (q ^ 14 - 1) * (q ^ 13 - 1) * (q - 1)) = 2 * (q ^ 55 + q ^ 28 - q ^ 27) := by ring

end FiniteField

section Densities

variable {K : Type*} [Field K]

/-- The local density at `p ∤ 2Δ` as an Euler factor:
`(1-p^{-14})(1+χp^{-13})(1+χp^{-1}) = (1-p^{-2})(1-p^{-14})(1-p^{-26}) / ((1-χp^{-1})(1-χp^{-13}))`. -/
theorem euler_factor (x e : K) (he : e ^ 2 = 1) (h1 : 1 - e * x ≠ 0) (h13 : 1 - e * x ^ 13 ≠ 0) :
    (1 - x ^ 14) * (1 + e * x ^ 13) * (1 + e * x)
      = (1 - x ^ 2) * (1 - x ^ 14) * (1 - x ^ 26) / ((1 - e * x) * (1 - e * x ^ 13)) := by
  rw [eq_div_iff (mul_ne_zero h1 h13)]
  linear_combination (-x ^ 2 * (x ^ 14 - 1) * (e ^ 2 * x ^ 26 + x ^ 26 - x ^ 24 - 1)) * he

end Densities

end UDuality.Dyons
