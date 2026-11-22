import Mathlib

/-!
# The Freudenthal triple system over `R³` (Bhargava cubes)

For the cubic Jordan algebra `J = R³` with `N(a) = a₁a₂a₃`, the triple system `R ⊕ R ⊕ J ⊕ J`
carries the quartic form `Δ`.  We check that `Δ` is invariant under the transformations
`φ(C)`, `ψ(D)` and `τ` that generate the duality group, and the slice formula.
-/

namespace UDuality.Cubes

variable {R : Type*} [CommRing R]

/-- An element of `J = R³`. -/
structure J (R : Type*) where
  a1 : R
  a2 : R
  a3 : R

variable (A B C : J R)

def N (A : J R) : R := A.a1 * A.a2 * A.a3
def sharp (A : J R) : J R := ⟨A.a2 * A.a3, A.a1 * A.a3, A.a1 * A.a2⟩
def tr (A B : J R) : R := A.a1 * B.a1 + A.a2 * B.a2 + A.a3 * B.a3
def cross (A B : J R) : J R :=
  ⟨A.a2 * B.a3 + B.a2 * A.a3, A.a1 * B.a3 + B.a1 * A.a3, A.a1 * B.a2 + B.a1 * A.a2⟩
def add (A B : J R) : J R := ⟨A.a1 + B.a1, A.a2 + B.a2, A.a3 + B.a3⟩
def smul (r : R) (A : J R) : J R := ⟨r * A.a1, r * A.a2, r * A.a3⟩

/-- An element `(α, β, A, B)` of the triple system. -/
structure M (R : Type*) where
  α : R
  β : R
  A : J R
  B : J R

/-- The quartic form `Δ = ((A,B) - αβ)² - 4(A#,B#) + 4αN(A) + 4βN(B)`. -/
def Δ (x : M R) : R :=
  (tr x.A x.B - x.α * x.β) ^ 2 - 4 * tr (sharp x.A) (sharp x.B) + 4 * x.α * N x.A
    + 4 * x.β * N x.B

def φ (C : J R) (x : M R) : M R :=
  ⟨x.α + tr x.B C + tr x.A (sharp C) + x.β * N C, x.β, add x.A (smul x.β C),
    add (add x.B (cross x.A C)) (smul x.β (sharp C))⟩

def ψ (D : J R) (x : M R) : M R :=
  ⟨x.α, x.β + tr x.A D + tr x.B (sharp D) + x.α * N D,
    add (add x.A (cross x.B D)) (smul x.α (sharp D)), add x.B (smul x.α D)⟩

def τ (x : M R) : M R := ⟨-x.β, x.α, smul (-1) x.B, x.A⟩

theorem Δ_φ (C : J R) (x : M R) : Δ (φ C x) = Δ x := by
  obtain ⟨α, β, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := x
  obtain ⟨c1, c2, c3⟩ := C
  simp only [Δ, φ, tr, sharp, N, cross, add, smul]
  ring

theorem Δ_ψ (D : J R) (x : M R) : Δ (ψ D x) = Δ x := by
  obtain ⟨α, β, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := x
  obtain ⟨d1, d2, d3⟩ := D
  simp only [Δ, ψ, tr, sharp, N, cross, add, smul]
  ring

theorem Δ_τ (x : M R) : Δ (τ x) = Δ x := by
  obtain ⟨α, β, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := x
  simp only [Δ, τ, tr, sharp, N, smul]
  ring

/-- Slice formula: for `A = 0`, `Δ = α²β² + 4βN(B)`. -/
theorem Δ_slice (α β : R) (B : J R) : Δ ⟨α, β, ⟨0, 0, 0⟩, B⟩ = α ^ 2 * β ^ 2 + 4 * β * N B := by
  simp only [Δ, tr, sharp, N]
  ring

/-- The slice lemma: `φ(-β⁻¹A)` kills `A` when `β` is a unit. -/
theorem slice {K : Type*} [Field K] (α β : K) (hβ : β ≠ 0) (A B : J K) :
    (φ (smul (-β⁻¹) A) ⟨α, β, A, B⟩).A = ⟨0, 0, 0⟩ := by
  obtain ⟨a1, a2, a3⟩ := A
  simp only [φ, add, smul]
  congr 1 <;> field_simp <;> ring

end UDuality.Cubes
