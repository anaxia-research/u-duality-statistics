import Mathlib

/-!
# Igusa zeta functions of the cubic norm and of the E7 quartic invariant

The local zeta functions are determined by linear equations obtained by splitting `ℤ_p^m`
into residue classes modulo `p`.  Each theorem below states that the closed form given in the
paper satisfies the corresponding equation, as an identity of rational functions in `p` and
`T = p^{-s}` over an arbitrary field.  The coefficients of the equations are the
finite-field counts of `UDuality.FiniteField`.
-/

namespace UDuality.Igusa

variable {K : Type*} [Field K]

/-- The split quadratic form in ten variables. -/
theorem zetaQ10 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h5 : p ^ 5 - T ≠ 0) :
    (p - 1) * (p ^ 5 - 1) / ((p - T) * (p ^ 5 - T)) =
      ((p - 1) * (p ^ 9 - p ^ 4) + (p ^ 9 + p ^ 5 - p ^ 4 - 1) * T * ((p - 1) / (p - T))) / p ^ 10 + T ^ 2 / p ^ 10 * ((p - 1) * (p ^ 5 - 1) / ((p - T) * (p ^ 5 - T))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- The form `Q11 = w0^2 + Q10`, trivial character. -/
theorem zetaQ11 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) :
    (p - 1) * (p ^ 11 - T) / ((p - T) * (p ^ 11 - T ^ 2)) =
      ((p - 1) * p ^ 10 + (p ^ 10 - 1) * T * ((p - 1) / (p - T))) / p ^ 11 + T ^ 2 / p ^ 11 * ((p - 1) * (p ^ 11 - T) / ((p - T) * (p ^ 11 - T ^ 2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- The form `Q11`, quadratic character. -/
theorem zetaQ11_eta (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) :
    (p - 1) * p ^ 5 / (p ^ 11 - T ^ 2) =
      (p - 1) * p ^ 5 / p ^ 11 + T ^ 2 / p ^ 11 * ((p - 1) * p ^ 5 / (p ^ 11 - T ^ 2)) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- The cubic norm of the Albert algebra (Proposition on the Albert zeta function). -/
theorem zetaNorm (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h5 : p ^ 5 - T ≠ 0) (h9 : p ^ 9 - T ≠ 0) :
    ((p - 1) * (p ^ 5 - 1) * (p ^ 9 - 1) / ((p - T) * (p ^ 5 - T) * (p ^ 9 - T))) =
      ((p - 1) * (p^12*(p^5 - 1)*(p^9 - 1)) + ((p^9 - 1)*(p^9 - p^4)*(p^8 + p^4 + 1)) * T * ((p - 1) / (p - T)) + ((p^9 - 1)*(p^8 + p^4 + 1)) * T ^ 2 * ((p - 1) * (p ^ 5 - 1) / ((p - T) * (p ^ 5 - T)))) / p ^ 27 + T ^ 3 / p ^ 27 * ((p - 1) * (p ^ 5 - 1) * (p ^ 9 - 1) / ((p - T) * (p ^ 5 - T) * (p ^ 9 - T))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System for `a^2 + pN(b)`, trivial character: unit `a`. -/
theorem W_one_1 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(T^3 + T^2*p^24 + T^2*p^20 - T^2*p^19 - T^2*p^15 - T^2*p^11 - T*p^24 - T*p^20 + T*p^15 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) =
      (1 - 1 / p) + T / p * ((p - 1)*(T^4 - T^3*p - T^2*p^19 - T^2*p^11 + T^2*p + T*p^25 + T*p^21 - T*p^16 + p^30 - p^25 - p^21 + p^16)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, trivial character: `N(b) + p a^2` split by the class of `b`. -/
theorem W_one_2 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(T^4 - T^3*p - T^2*p^19 - T^2*p^11 + T^2*p + T*p^25 + T*p^21 - T*p^16 + p^30 - p^25 - p^21 + p^16)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) =
      ((p - 1) * (p^12*(p^5 - 1)*(p^9 - 1)) + ((p^9 - 1)*(p^9 - p^4)*(p^8 + p^4 + 1)) * T * ((p - 1) / (p - T)) + ((p^9 - 1)*(p^8 + p^4 + 1)) * T * ((p - 1)*(T^2*p^5 - T^2 - T*p^5 + p^11)/((p - T)*(p^11 - T^2)))) / p ^ 27 + T / p ^ 27 * ((p - 1)*(T^4*p^14 - T^4*p^9 - T^4*p^5 + T^4 - T^3*p^14 + T^3*p^9 + T^3*p^5 + T^2*p^29 - T^2*p^19 - T^2*p^11 - T*p^29 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, trivial character: `a^2 + p^2 N(b)`. -/
theorem W_one_3 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(T^4*p^14 - T^4*p^9 - T^4*p^5 + T^4 - T^3*p^14 + T^3*p^9 + T^3*p^5 + T^2*p^29 - T^2*p^19 - T^2*p^11 - T*p^29 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) =
      (1 - 1 / p) + T ^ 2 / p * ((p - 1)*(T^3 + T^2*p^15 - T^2*p^10 - T^2*p^6 - T*p^19 - T*p^15 - T*p^11 + T*p^10 + T*p^6 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, trivial character: `a^2 + N(b)` split by residue classes. -/
theorem W_one_4 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(T^3 + T^2*p^15 - T^2*p^10 - T^2*p^6 - T*p^19 - T*p^15 - T*p^11 + T*p^10 + T*p^6 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2))) =
      (p ^ 28 - p ^ 27 + (p ^ 27 - 1 - ((p^9 - 1)*(p^8 + p^4 + 1))) * T * ((p - 1) / (p - T)) + ((p^9 - 1)*(p^8 + p^4 + 1)) * T ^ 2 * ((p - 1) * (p ^ 11 - T) / ((p - T) * (p ^ 11 - T ^ 2))) + T ^ 2 * ((p - 1)*(T^3 + T^2*p^24 + T^2*p^20 - T^2*p^19 - T^2*p^15 - T^2*p^11 - T*p^24 - T*p^20 + T*p^15 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2)))) / p ^ 28 := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, trivial character: `a^2 + p Q10(w)`. -/
theorem W_one_5 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(T^2*p^5 - T^2 - T*p^5 + p^11)/((p - T)*(p^11 - T^2))) =
      (1 - 1 / p) + T / p * ((p - 1)*(T*p^6 - T^2 + p^11 - p^6)/((p - T)*(p^11 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, trivial character: `Q10(w) + p a^2`. -/
theorem W_one_6 (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(T*p^6 - T^2 + p^11 - p^6)/((p - T)*(p^11 - T^2))) =
      (p - 1) * (p ^ 9 - p ^ 4) / p ^ 10 + (p ^ 9 + p ^ 5 - p ^ 4 - 1) * T / p ^ 10 * ((p - 1) / (p - T)) + T / p ^ 10 * ((p - 1)*(T^2*p^5 - T^2 - T*p^5 + p^11)/((p - T)*(p^11 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System for `a^2 + pN(b)`, quadratic character: unit `a`. -/
theorem W_eta_1 (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    (p^5*(p - 1)*(T^2*p^9 - T^2*p^4 - T^2 + p^24)/((p^11 - T^2)*(p^19 - T^2))) =
      (1 - 1 / p) + T / p * (T*(p - 1)*(p^19 + p^15 + p^11 - p^10 - p^6 - T^2)/((p^11 - T^2)*(p^19 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, quadratic character: `N(b) + p a^2` split by the class of `b`. -/
theorem W_eta_2 (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    (T*(p - 1)*(p^19 + p^15 + p^11 - p^10 - p^6 - T^2)/((p^11 - T^2)*(p^19 - T^2))) =
      (((p^9 - 1)*(p^8 + p^4 + 1)) * T * (p^10*(p - 1)/(p^11 - T^2))) / p ^ 27 + T / p ^ 27 * (p^10*(p - 1)*(T^2*p^13 + T^2*p^9 - T^2*p^8 - T^2*p^4 - T^2 + p^19)/((p^11 - T^2)*(p^19 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, quadratic character: `a^2 + p^2 N(b)`. -/
theorem W_eta_3 (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    (p^10*(p - 1)*(T^2*p^13 + T^2*p^9 - T^2*p^8 - T^2*p^4 - T^2 + p^19)/((p^11 - T^2)*(p^19 - T^2))) =
      (1 - 1 / p) + T ^ 2 / p * ((p - 1)*(p^24 + p^20 - p^15 - T^2)/((p^11 - T^2)*(p^19 - T^2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, quadratic character: `a^2 + N(b)` split by residue classes. -/
theorem W_eta_4 (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    ((p - 1)*(p^24 + p^20 - p^15 - T^2)/((p^11 - T^2)*(p^19 - T^2))) =
      ((p - 1) * (p^22 + p^18 - p^13) + ((p^9 - 1)*(p^8 + p^4 + 1)) * T ^ 2 * ((p - 1) * p ^ 5 / (p ^ 11 - T ^ 2)) + T ^ 2 * (p^5*(p - 1)*(T^2*p^9 - T^2*p^4 - T^2 + p^24)/((p^11 - T^2)*(p^19 - T^2)))) / p ^ 28 := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, quadratic character: `a^2 + p Q10(w)`. -/
theorem W_eta_5 (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    (p^10*(p - 1)/(p^11 - T^2)) =
      (1 - 1 / p) + T / p * (T*(p - 1)/(p^11 - T^2)) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- System, quadratic character: `Q10(w) + p a^2`. -/
theorem W_eta_6 (p T : K) (hp : p ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) :
    (T*(p - 1)/(p^11 - T^2)) =
      T / p ^ 10 * (p^10*(p - 1)/(p^11 - T^2)) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- Theorem (Igusa zeta function of the quartic invariant), trivial character. -/
theorem zetaDelta_one (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) (h28 : p ^ 28 - T ^ 2 ≠ 0) :
    ((p - 1) * (p ^ 14 - 1) * (p ^ 44 + p ^ 30 - (p ^ 33 + p ^ 29 + p ^ 25 - p ^ 15) * T + (p ^ 29 - p ^ 19 - p ^ 15 - p ^ 11) * T ^ 2 + (p ^ 14 + 1) * T ^ 3) / ((p - T) * (p ^ 28 - T ^ 2) * (p ^ 11 - T ^ 2) * (p ^ 19 - T ^ 2))) =
      ((p - 1) * p ^ 27 * (p ^ 28 - 1) + (p^13*(p^10 - 1)*(p^14 - 1)*(p^18 - 1)) * T * ((p - 1) / (p - T)) + (p^5*(p^14 - 1)*(p^18 - 1)*(p^8 + p^4 + 1)) * T ^ 2 * ((p - 1) * (p ^ 11 - T) / ((p - T) * (p ^ 11 - T ^ 2))) + ((p^5 + 1)*(p^9 + 1)*(p^14 - 1)) * T ^ 2 * ((p - 1)*(T^3 + T^2*p^24 + T^2*p^20 - T^2*p^19 - T^2*p^15 - T^2*p^11 - T*p^24 - T*p^20 + T*p^15 + p^30)/((p - T)*(p^11 - T^2)*(p^19 - T^2)))) / p ^ 56 + T ^ 4 / p ^ 56 * ((p - 1) * (p ^ 14 - 1) * (p ^ 44 + p ^ 30 - (p ^ 33 + p ^ 29 + p ^ 25 - p ^ 15) * T + (p ^ 29 - p ^ 19 - p ^ 15 - p ^ 11) * T ^ 2 + (p ^ 14 + 1) * T ^ 3) / ((p - T) * (p ^ 28 - T ^ 2) * (p ^ 11 - T ^ 2) * (p ^ 19 - T ^ 2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- Theorem (Igusa zeta function of the quartic invariant), quadratic character. -/
theorem zetaDelta_eta (p T : K) (hp : p ≠ 0) (h1 : p - T ≠ 0) (h11 : p ^ 11 - T ^ 2 ≠ 0) (h19 : p ^ 19 - T ^ 2 ≠ 0) (h28 : p ^ 28 - T ^ 2 ≠ 0) :
    ((p - 1) * (p ^ 14 - 1) * (p ^ 4 + 1) * (p ^ 29 - T ^ 2) * p ^ 5 / ((p ^ 28 - T ^ 2) * (p ^ 11 - T ^ 2) * (p ^ 19 - T ^ 2))) =
      ((p - 1) * p ^ 27 * (p ^ 14 - 1) * (p ^ 9 + p ^ 5) + (p^5*(p^14 - 1)*(p^18 - 1)*(p^8 + p^4 + 1)) * T ^ 2 * ((p - 1) * p ^ 5 / (p ^ 11 - T ^ 2)) + ((p^5 + 1)*(p^9 + 1)*(p^14 - 1)) * T ^ 2 * (p^5*(p - 1)*(T^2*p^9 - T^2*p^4 - T^2 + p^24)/((p^11 - T^2)*(p^19 - T^2)))) / p ^ 56 + T ^ 4 / p ^ 56 * ((p - 1) * (p ^ 14 - 1) * (p ^ 4 + 1) * (p ^ 29 - T ^ 2) * p ^ 5 / ((p ^ 28 - T ^ 2) * (p ^ 11 - T ^ 2) * (p ^ 19 - T ^ 2))) := by
  first
  | (field_simp; done)
  | (field_simp; ring)

end UDuality.Igusa
