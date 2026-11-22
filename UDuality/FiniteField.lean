import Mathlib

/-!
# Finite-field counts for the E7 quartic invariant

Polynomial identities in `q` behind the level-set counts of the quartic invariant on the
56-dimensional Freudenthal triple system over `𝔽_q` (`p ≥ 5`), and behind the counts of
the cubic norm of the Albert algebra.  All statements are identities in a commutative ring,
so they hold for every prime power `q`.
-/

namespace UDuality

variable {R : Type*} [CommRing R]

/-- Number of solutions of `N(A) = c`, `c ≠ 0`, in the Albert algebra over `𝔽_q`. -/
def albertM (q : R) : R := q ^ 12 * (q ^ 5 - 1) * (q ^ 9 - 1)
/-- The character sum `∑_A ψ(c N(A))`. -/
def albertS (q : R) : R := q ^ 22 + q ^ 18 - q ^ 13
/-- Elements of rank one in the Albert algebra. -/
def albertR1 (q : R) : R := (q ^ 8 + q ^ 4 + 1) * (q ^ 9 - 1)
/-- Elements of rank two in the Albert algebra. -/
def albertR2 (q : R) : R := (q ^ 9 - q ^ 4) * albertR1 q

/-- Null octonions in the split octonions over `𝔽_q`. -/
def nullOct (q : R) : R := q ^ 7 + q ^ 4 - q ^ 3

/-- Pairs of null octonions with `yz = 0`. -/
theorem nullPairs (q : R) : nullOct q + (nullOct q - 1) * q ^ 4 = q ^ 11 + q ^ 8 - q ^ 3 := by
  unfold nullOct; ring

/-- The character sum splits as `(q-1) q^21 + q^10 P`. -/
theorem albertS_split (q : R) :
    (q - 1) * q ^ 21 + q ^ 10 * (q ^ 11 + q ^ 8 - q ^ 3) = albertS q := by
  unfold albertS; ring

/-- `#{N = 0} - #{N = c} = S`, i.e. `q^27 - S = q M`. -/
theorem albert_M_of_S (q : R) : q ^ 27 - albertS q = q * albertM q := by
  unfold albertS albertM; ring

/-- Rank one and rank two elements add up to the nonzero elements of norm zero. -/
theorem albert_rank_sum (q : R) :
    albertR1 q + albertR2 q = q ^ 27 - 1 - (q - 1) * albertM q := by
  unfold albertR2 albertR1 albertM; ring

/-- The Gauss-sum relation `1 + r1 = 1 + q^{-5} r1 + q^{-9} r2`, cleared of denominators. -/
theorem albert_gauss (q : R) : q ^ 9 * albertR1 q = q ^ 4 * albertR1 q + albertR2 q := by
  unfold albertR2; ring

/-- The identity `(q-1)S + q^5 r1 = (q^14-1)(q^9+q^5)`. -/
theorem key_identity (q : R) :
    (q - 1) * albertS q + q ^ 5 * albertR1 q = (q ^ 14 - 1) * (q ^ 9 + q ^ 5) := by
  unfold albertS albertR1; ring

/-- Theorem A, nonzero values: the two parts of the count (`β ≠ 0` and `β = 0`) add up to
`q^27 (q^14-1)(q^9+η)(q^5+η)` for `η = ±1`. -/
theorem countA (q e : R) (he : e ^ 2 = 1) :
    (q - 1) * q ^ 27 * (q ^ 27 + e * albertS q)
      + (q ^ 27 * ((q - 1) * albertM q + albertR1 q + albertR2 q)
         + e * q ^ 27 * (albertR1 q + (q ^ 5 - 1) * albertR1 q))
      = q ^ 27 * (q ^ 14 - 1) * (q ^ 9 + e) * (q ^ 5 + e) := by
  unfold albertS albertR2 albertR1 albertM
  linear_combination (-(q ^ 27 * (q ^ 14 - 1))) * he

/-- Theorem A, value zero: `q^56 - ∑_{n≠0} #{Δ=n} = q^55 + q^28 - q^27`. -/
theorem countA_zero (q : R) :
    q ^ 56 - (q - 1) * (q ^ 27 * (q ^ 28 - 1)) = q ^ 55 + q ^ 28 - q ^ 27 := by ring

/-- Orbit sizes of the rank strata. -/
def R1 (q : R) : R := (q ^ 14 - 1) * (q ^ 9 + 1) * (q ^ 5 + 1)
def R2 (q : R) : R := q ^ 5 * (q ^ 8 + q ^ 4 + 1) * (q ^ 14 - 1) * (q ^ 18 - 1)
def R3 (q : R) : R := q ^ 13 * (q ^ 10 - 1) * (q ^ 14 - 1) * (q ^ 18 - 1)

/-- The strata exhaust the zero locus. -/
theorem strata_sum (q : R) : 1 + R1 q + R2 q + R3 q = q ^ 55 + q ^ 28 - q ^ 27 := by
  unfold R1 R2 R3; ring

/-- Orders of the finite groups of Lie type involved. -/
def ordE7 (q : R) : R :=
  q ^ 63 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 10 - 1) * (q ^ 12 - 1) * (q ^ 14 - 1)
    * (q ^ 18 - 1)
def ordE6 (q : R) : R :=
  q ^ 36 * (q ^ 2 - 1) * (q ^ 5 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 9 - 1) * (q ^ 12 - 1)
def ordB5 (q : R) : R :=
  q ^ 25 * (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 10 - 1)
def ordF4 (q : R) : R := q ^ 24 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 12 - 1)

/-- Orbit-stabiliser for rank one: stabiliser `E6 ⋉ U27`. -/
theorem orbit_rank1 (q : R) : R1 q * (q ^ 27 * ordE6 q) = ordE7 q := by
  unfold R1 ordE6 ordE7; ring

/-- Orbit-stabiliser for rank two: stabiliser `B5 ⋉ U33`. -/
theorem orbit_rank2 (q : R) : R2 q * (q ^ 33 * ordB5 q) = ordE7 q := by
  unfold R2 ordB5 ordE7; ring

/-- Orbit-stabiliser for rank three: stabiliser `F4 ⋉ U26`. -/
theorem orbit_rank3 (q : R) : R3 q * (q ^ 26 * ordF4 q) = ordE7 q := by
  unfold R3 ordF4 ordE7; ring

/-- The rank-two part of the `β = 0` count: with `r2 = (q^9 - q^4) r1`, the term
`q^{-4} r2` equals `(q^5 - 1) r1`. -/
theorem rank2_eta (q : R) : q ^ 4 * ((q ^ 5 - 1) * albertR1 q) = albertR2 q := by
  unfold albertR2; ring

/-- The rank-two quadratic form `(a-b)^2 + 4 n(z)` on `𝔽_q^{27}` (rank `9`) takes each nonzero
value `q^{18}(q^8 + η q^4)` times; with the free coordinate `α` this gives
`q^{27} + η q^{23}` solutions for each `A` of rank two. -/
theorem rank2_count (q e : R) : q * (q ^ 18 * (q ^ 8 + e * q ^ 4)) = q ^ 27 + e * q ^ 23 := by
  ring

/-- Values of the quartic form: `Δ(r, 1, 0, diag(k,1,1)) = r^2 + 4k`, using
`Δ = (αβ)^2 + 4 β N(B)` when `A = 0`. -/
theorem value_witness (r k : R) : (r * 1) ^ 2 + 4 * 1 * (k * 1 * 1) = r ^ 2 + 4 * k := by ring

end UDuality
