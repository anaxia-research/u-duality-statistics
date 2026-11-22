import Mathlib

/-!
# Functional equation and local densities

The Denef–Meuser functional equation of the Igusa zeta functions of the quartic invariant,
the generating function of the local densities (Theorem B) and its corollaries.
-/

namespace UDuality.Densities

variable {K : Type*} [Field K]

/-- Numerator and denominator of the Igusa zeta function, trivial character. -/
def num1 (p T : K) : K := (p - 1) * (p ^ 14 - 1) * (p ^ 44 + p ^ 30 - (p ^ 33 + p ^ 29 + p ^ 25 - p ^ 15) * T + (p ^ 29 - p ^ 19 - p ^ 15 - p ^ 11) * T ^ 2 + (p ^ 14 + 1) * T ^ 3)
def den1 (p T : K) : K := (p - T) * (p ^ 28 - T ^ 2) * (p ^ 11 - T ^ 2) * (p ^ 19 - T ^ 2)
/-- Numerator and denominator of the Igusa zeta function, quadratic character. -/
def numE (p T : K) : K := (p - 1) * (p ^ 14 - 1) * (p ^ 4 + 1) * (p ^ 29 - T ^ 2) * p ^ 5
def denE (p T : K) : K := (p ^ 28 - T ^ 2) * (p ^ 11 - T ^ 2) * (p ^ 19 - T ^ 2)

/-- Closed form of the Igusa zeta function, trivial character. -/
def Z1 (p T : K) : K := num1 p T / den1 p T

/-- Closed form of the Igusa zeta function, quadratic character. -/
def Zeta (p T : K) : K := numE p T / denE p T

set_option maxRecDepth 100000 in
theorem num1_inv (p T : K) (hp : p ≠ 0) (hT : T ≠ 0) :
    num1 p⁻¹ T⁻¹ * (T ^ 3 * p ^ 59) = num1 p T := by
  unfold num1; field_simp; ring

set_option maxRecDepth 100000 in
theorem den1_inv (p T : K) (hp : p ≠ 0) (hT : T ≠ 0) :
    den1 p⁻¹ T⁻¹ * (T ^ 7 * p ^ 59) = den1 p T := by
  unfold den1; field_simp; ring

set_option maxRecDepth 100000 in
theorem numE_inv (p T : K) (hp : p ≠ 0) (hT : T ≠ 0) :
    numE p⁻¹ T⁻¹ * (T ^ 2 * p ^ 58) = -numE p T := by
  unfold numE; field_simp; ring

set_option maxRecDepth 100000 in
theorem denE_inv (p T : K) (hp : p ≠ 0) (hT : T ≠ 0) :
    denE p⁻¹ T⁻¹ * (T ^ 6 * p ^ 58) = -denE p T := by
  unfold denE; field_simp; ring

/-- Denef–Meuser functional equation, trivial character:
`Z(p^{-1}, T^{-1}) = T^4 Z(p, T)`. -/
theorem fe_Z1 (p T : K) (hp : p ≠ 0) (hT : T ≠ 0) (hd : den1 p T ≠ 0) :
    Z1 p⁻¹ T⁻¹ = T ^ 4 * Z1 p T := by
  have c1 : T ^ 3 * p ^ 59 ≠ 0 := mul_ne_zero (pow_ne_zero _ hT) (pow_ne_zero _ hp)
  have c2 : T ^ 7 * p ^ 59 ≠ 0 := mul_ne_zero (pow_ne_zero _ hT) (pow_ne_zero _ hp)
  have e1 : num1 p⁻¹ T⁻¹ = num1 p T / (T ^ 3 * p ^ 59) := by
    rw [← num1_inv p T hp hT]; field_simp
  have e2 : den1 p⁻¹ T⁻¹ = den1 p T / (T ^ 7 * p ^ 59) := by
    rw [← den1_inv p T hp hT]; field_simp
  unfold Z1
  rw [e1, e2]
  field_simp

/-- Denef–Meuser functional equation, quadratic character. -/
theorem fe_Zeta (p T : K) (hp : p ≠ 0) (hT : T ≠ 0) (hd : denE p T ≠ 0) :
    Zeta p⁻¹ T⁻¹ = T ^ 4 * Zeta p T := by
  have c1 : T ^ 2 * p ^ 58 ≠ 0 := mul_ne_zero (pow_ne_zero _ hT) (pow_ne_zero _ hp)
  have c2 : T ^ 6 * p ^ 58 ≠ 0 := mul_ne_zero (pow_ne_zero _ hT) (pow_ne_zero _ hp)
  have e1 : numE p⁻¹ T⁻¹ = -numE p T / (T ^ 2 * p ^ 58) := by
    rw [← numE_inv p T hp hT]; field_simp
  have e2 : denE p⁻¹ T⁻¹ = -denE p T / (T ^ 6 * p ^ 58) := by
    rw [← denE_inv p T hp hT]; field_simp
  unfold Zeta
  rw [e1, e2]
  field_simp

/-- Theorem B: generating function of `β_p(p^v u)` for `u` a square. -/
theorem thmB_sq (p X : K) (hp : p ≠ 0) (hp1 : p - 1 ≠ 0) (h1 : 1 - X ≠ 0) (h9 : p ^ 9 - X ^ 2 ≠ 0) (h17 : p ^ 17 - X ^ 2 ≠ 0) (h26 : p ^ 26 - X ^ 2 ≠ 0) :
    (Z1 p (p * X) + (1) * Zeta p (p * X)) / (1 - 1 / p) =
      (1 - 1 / p ^ 14) * (1 + (1) / p ^ 9) * (1 + (1) / p ^ 5) * (1 - (1 * (1 / p ^ 5 + 1 / p ^ 9) - 1 / p ^ 14) * X + (1 / p ^ 13 - (1) * (1 / p ^ 18 + 1 / p ^ 22)) * X ^ 2 + X ^ 3 / p ^ 27) / ((1 - X) * (1 - X ^ 2 / p ^ 9) * (1 - X ^ 2 / p ^ 17) * (1 - X ^ 2 / p ^ 26)) := by
  have e1 : p - p * X ≠ 0 := by
    have : p - p * X = p * (1 - X) := by ring
    rw [this]; exact mul_ne_zero hp h1
  have e11 : p ^ 11 - (p * X) ^ 2 ≠ 0 := by
    have : p ^ 11 - (p * X) ^ 2 = p ^ 2 * (p ^ 9 - X ^ 2) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hp) h9
  have e19 : p ^ 19 - (p * X) ^ 2 ≠ 0 := by
    have : p ^ 19 - (p * X) ^ 2 = p ^ 2 * (p ^ 17 - X ^ 2) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hp) h17
  have e28 : p ^ 28 - (p * X) ^ 2 ≠ 0 := by
    have : p ^ 28 - (p * X) ^ 2 = p ^ 2 * (p ^ 26 - X ^ 2) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hp) h26
  have f9 : 1 - X ^ 2 / p ^ 9 ≠ 0 := by
    rw [sub_div' (pow_ne_zero _ hp)] ; simpa using div_ne_zero (by simpa [one_mul] using h9) (pow_ne_zero 9 hp)
  have f17 : 1 - X ^ 2 / p ^ 17 ≠ 0 := by
    rw [sub_div' (pow_ne_zero _ hp)] ; simpa using div_ne_zero (by simpa [one_mul] using h17) (pow_ne_zero 17 hp)
  have f26 : 1 - X ^ 2 / p ^ 26 ≠ 0 := by
    rw [sub_div' (pow_ne_zero _ hp)] ; simpa using div_ne_zero (by simpa [one_mul] using h26) (pow_ne_zero 26 hp)
  have g : 1 - 1 / p ≠ 0 := by
    rw [sub_div' hp]; simpa using div_ne_zero hp1 hp
  unfold Z1 Zeta num1 den1 numE denE
  field_simp
  ring

/-- Theorem B: generating function of `β_p(p^v u)` for `u` a nonsquare. -/
theorem thmB_nsq (p X : K) (hp : p ≠ 0) (hp1 : p - 1 ≠ 0) (h1 : 1 - X ≠ 0) (h9 : p ^ 9 - X ^ 2 ≠ 0) (h17 : p ^ 17 - X ^ 2 ≠ 0) (h26 : p ^ 26 - X ^ 2 ≠ 0) :
    (Z1 p (p * X) + (-1) * Zeta p (p * X)) / (1 - 1 / p) =
      (1 - 1 / p ^ 14) * (1 + (-1) / p ^ 9) * (1 + (-1) / p ^ 5) * (1 - (-1 * (1 / p ^ 5 + 1 / p ^ 9) - 1 / p ^ 14) * X + (1 / p ^ 13 - (-1) * (1 / p ^ 18 + 1 / p ^ 22)) * X ^ 2 + X ^ 3 / p ^ 27) / ((1 - X) * (1 - X ^ 2 / p ^ 9) * (1 - X ^ 2 / p ^ 17) * (1 - X ^ 2 / p ^ 26)) := by
  have e1 : p - p * X ≠ 0 := by
    have : p - p * X = p * (1 - X) := by ring
    rw [this]; exact mul_ne_zero hp h1
  have e11 : p ^ 11 - (p * X) ^ 2 ≠ 0 := by
    have : p ^ 11 - (p * X) ^ 2 = p ^ 2 * (p ^ 9 - X ^ 2) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hp) h9
  have e19 : p ^ 19 - (p * X) ^ 2 ≠ 0 := by
    have : p ^ 19 - (p * X) ^ 2 = p ^ 2 * (p ^ 17 - X ^ 2) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hp) h17
  have e28 : p ^ 28 - (p * X) ^ 2 ≠ 0 := by
    have : p ^ 28 - (p * X) ^ 2 = p ^ 2 * (p ^ 26 - X ^ 2) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hp) h26
  have f9 : 1 - X ^ 2 / p ^ 9 ≠ 0 := by
    rw [sub_div' (pow_ne_zero _ hp)] ; simpa using div_ne_zero (by simpa [one_mul] using h9) (pow_ne_zero 9 hp)
  have f17 : 1 - X ^ 2 / p ^ 17 ≠ 0 := by
    rw [sub_div' (pow_ne_zero _ hp)] ; simpa using div_ne_zero (by simpa [one_mul] using h17) (pow_ne_zero 17 hp)
  have f26 : 1 - X ^ 2 / p ^ 26 ≠ 0 := by
    rw [sub_div' (pow_ne_zero _ hp)] ; simpa using div_ne_zero (by simpa [one_mul] using h26) (pow_ne_zero 26 hp)
  have g : 1 - 1 / p ≠ 0 := by
    rw [sub_div' hp]; simpa using div_ne_zero hp1 hp
  unfold Z1 Zeta num1 den1 numE denE
  field_simp
  ring

/-- Corollary (densities at `p ‖ n`): the factorisation used for the coefficient of `X`. -/
theorem coeff_X (a b e : K) (he : e ^ 2 = 1) :
    (1 + e * a) * (1 + e * b) * (1 - e * a - e * b + a * b) = (1 - a ^ 2) * (1 - b ^ 2) := by
  linear_combination (a^2*b^2 - a^2*b*e - a^2 - a*b^2*e - a*b - b^2) * he

/-- Corollary (densities): `1 + ε p^{-k} = (1 - p^{-2k}) / (1 - ε p^{-k})` for `ε = ±1`. -/
theorem euler_factor (x e : K) (he : e ^ 2 = 1) (h : 1 - e * x ≠ 0) :
    1 + e * x = (1 - x ^ 2) / (1 - e * x) := by
  rw [eq_div_iff h]
  linear_combination (-x ^ 2) * he

end UDuality.Densities
