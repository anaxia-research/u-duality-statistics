import Mathlib

/-!
# Part III: the mean entropy of quarter-BPS dyons

Identities and inequalities behind the averages of the attractor correction
`S₁ = -log((2τ₂)^12 |η(τ)|^48)` over U-duality orbits.

* `heegner_norm`: the Epstein zeta function at a Heegner point is the zeta function of the form.
* `jacobian_det`: the change of variables `(a, b, c) ↦ (a, x, y)` for reduced forms.
* `hecke_sign`: the leading coefficient of `∏_b Δ((aτ + b)/d)`.
* `cusp_lower`, `four_lt_const`: the lower bound `S₁ > 4`.
* constant bookkeeping for the mean values.
-/

namespace UDuality.Entropy

open Real Finset

/-- At the Heegner point `τ = (-b + i√Δ)/(2a)` of the form `[a, b, c]`, `Δ = 4ac - b²`,
one has `a |mτ + n|² = a n² - b m n + c m²`. -/
theorem heegner_norm (a b c m n : ℝ) (ha : 0 < a) (hΔ : 0 ≤ 4 * a * c - b ^ 2) :
    a * Complex.normSq (m * (⟨-b / (2 * a), √(4 * a * c - b ^ 2) / (2 * a)⟩ : ℂ) + n) =
      a * n ^ 2 - b * m * n + c * m ^ 2 := by
  have hs : √(4 * a * c - b ^ 2) ^ 2 = 4 * a * c - b ^ 2 := Real.sq_sqrt hΔ
  have ha' : a ≠ 0 := ha.ne'
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  generalize √(4 * a * c - b ^ 2) = s at hs ⊢
  field_simp
  linear_combination m ^ 2 * hs

/-- The Jacobian of `(a, x, y) ↦ (a, b, c) = (a, -2ax, a(x² + y²))` is `-4a²y`. -/
theorem jacobian_det (a x y : ℝ) :
    Matrix.det !![1, 0, 0; -2 * x, -2 * a, 0; x ^ 2 + y ^ 2, 2 * a * x, 2 * a * y] =
      -4 * a ^ 2 * y := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- `∑_{b<d} b = d(d-1)/2`, hence `∏_{b<d} e^{2πib/d} = (-1)^{d-1}`: the leading coefficient of
`∏_{b mod d} Δ((aτ+b)/d)` has absolute value one. -/
theorem hecke_sign (d : ℕ) (hd : 1 ≤ d) :
    Complex.exp (2 * π * Complex.I * ((∑ b ∈ range d, (b : ℂ)) / d)) = (-1) ^ (d - 1) := by
  have hsum : (∑ b ∈ range d, (b : ℂ)) = d * ((d : ℂ) - 1) / 2 := by
    have h := Finset.sum_range_id_mul_two d
    have h' : ((∑ i ∈ range d, i : ℕ) : ℂ) * 2 = ((d * (d - 1) : ℕ) : ℂ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub hd] at h'
    linear_combination h' / 2
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have key : 2 * π * Complex.I * ((∑ b ∈ range d, (b : ℂ)) / d) =
      ((d - 1 : ℕ) : ℂ) * (π * Complex.I) := by
    rw [hsum]
    push_cast [Nat.cast_sub hd]
    field_simp
  rw [key, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- The Hecke defect at a prime: `∑_{ad=p} d log(a/d) = (1 - p) log p`. -/
theorem ell_prime (p : ℝ) :
    1 * log (p / 1) + p * log (1 / p) = (1 - p) * log p := by
  rw [div_one, one_div, Real.log_inv]; ring

/-- The cusp part of `S₁`: for `y > 0`, `4πy - 12 log(2y) ≥ 12 (1 - log(6/π))`,
with equality at `y = 3/π`. -/
theorem cusp_lower (y : ℝ) (hy : 0 < y) :
    12 * (1 - log (6 / π)) ≤ 4 * π * y - 12 * log (2 * y) := by
  set t := π * y / 3 with ht
  have htp : 0 < t := by positivity
  have h2y : 2 * y = 6 / π * t := by rw [ht]; field_simp; ring
  have hlog : log (2 * y) = log (6 / π) + log t := by
    rw [h2y, Real.log_mul (by positivity) htp.ne']
  have := Real.log_le_sub_one_of_pos htp
  have h4 : 4 * π * y = 12 * t := by rw [ht]; ring
  rw [hlog, h4]
  linarith

lemma log_six_div_pi_le : log (6 / π) ≤ 0.648 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h := Real.sum_le_exp_of_nonneg (x := (0.648 : ℝ)) (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have hpi := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma exp_pi_sqrt3_ge : (227 : ℝ) ≤ exp (π * √3) := by
  have h3 : (1.732 : ℝ) ≤ √3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpi := Real.pi_gt_d6
  have hx : (5.44 : ℝ) ≤ π * √3 := by nlinarith
  have h := Real.sum_le_exp_of_nonneg (x := (5.44 : ℝ)) (by norm_num) 20
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  calc (227 : ℝ) ≤ exp 5.44 := by linarith
    _ ≤ exp (π * √3) := Real.exp_le_exp.mpr hx

/-- The numerical core of `S₁ > 4`: with `u = e^{-π√3}` (the largest value of `|q|` on the
fundamental domain), `12 (1 - log(6/π)) - 48 u/(1-u) > 4`. -/
theorem four_lt_const :
    4 < 12 * (1 - log (6 / π)) - 48 * exp (-(π * √3)) / (1 - exp (-(π * √3))) := by
  have hl := log_six_div_pi_le
  have he := exp_pi_sqrt3_ge
  set u := exp (-(π * √3)) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u ≤ 1 / 227 := by
    rw [hu, Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using he
  have hden : 0 < 1 - u := by linarith
  have hfrac : 48 * u / (1 - u) ≤ 48 / 226 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  linarith

/-! ### Constant bookkeeping -/

/-- The constant of Theorem D: the cusp contribution plus one sixth of `∫_{F₁} S₁ dμ`
equals `C = 8ζ'(2)/π - 2π(1 + 3γ)/9`. -/
theorem const_C (z γ l : ℝ) (hπ : π ≠ 0) :
    ((2 * π / 3) * (γ - l) - 2 * π / 9 - 2 * l - 2) +
      (4 * π * l - 8 * π * γ + 48 * z / π + 12 * l + 12) / 6 =
      8 * z / π - 2 * π * (1 + 3 * γ) / 9 := by
  field_simp; ring

/-- Mean value for torsion one: `18 C / π = 24 ζ'(2)/ζ(2) - 4 - 12γ`, using `ζ(2) = π²/6`. -/
theorem mean_torsion_one (z γ : ℝ) (hπ : π ≠ 0) :
    18 * (8 * z / π - 2 * π * (1 + 3 * γ) / 9) / π = 24 * z / (π ^ 2 / 6) - 4 - 12 * γ := by
  field_simp; ring

/-- Mean value over all torsions: the extra constant `(4π/3) ζ'(3)/ζ(3)` contributes
`24 ζ'(3)/ζ(3)`. -/
theorem mean_all (C z3 ζ3 : ℝ) (hπ : π ≠ 0) (h3 : ζ3 ≠ 0) :
    18 * (C + 4 * π / 3 * (z3 / ζ3)) / π = 18 * C / π + 24 * z3 / ζ3 := by
  field_simp; ring

/-- The Dirichlet series identity behind the all-torsion constant:
`∑ σ₁ log r / r³ = -(ζ'(3)ζ(2) + ζ(3)ζ'(2))`, `∑ ℓ(r)/r³ = ζ(3)ζ'(2) - ζ'(3)ζ(2)`, and
`-(2π/3)(first) - (2π/3)(second) = (4π/3) ζ(2) ζ'(3)`. -/
theorem all_torsion_const (ζ2 ζ3 z2 z3 : ℝ) :
    -(2 * π / 3) * (-(z3 * ζ2 + ζ3 * z2)) - (2 * π / 3) * (ζ3 * z2 - z3 * ζ2) =
      4 * π / 3 * ζ2 * z3 := by
  ring

end UDuality.Entropy
