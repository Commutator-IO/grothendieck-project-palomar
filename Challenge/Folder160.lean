module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot

@[expose] public section

open Matrix Polynomial

namespace Grothendieck.Folder160

variable {R : Type*} [CommRing R] (p : ℕ)

/-- The Moore matrix `(ξ_j^{p^i})`. -/
def mooreMat {n : ℕ} (ξ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => ξ j ^ p ^ (i : ℕ)

/-- The Moore determinant `Δₙ(ξ) = det(ξ_j^{p^i})`. -/
def moore {n : ℕ} (ξ : Fin n → R) : R := (mooreMat p ξ).det

variable [hp : Fact p.Prime]

/-- `D(T) = Δ_{n+1}(T, X₁, …, Xₙ)`, a polynomial in `T` over `𝔽_p[X₁, …, Xₙ]`. -/
noncomputable def D (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  moore p (Fin.cons Polynomial.X fun k => Polynomial.C (MvPolynomial.X k))

/-- `P(T) = ∏_{λ ∈ 𝔽_p^n} (T − λ · X) = D(T)/((−1)ⁿ Δₙ)`. -/
noncomputable def P (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  ((D p n).roots.map fun a => Polynomial.X - Polynomial.C a).prod

/-- The Dickson coefficients `A_i`, polynomials in `X₁, …, Xₙ`. -/
noncomputable def A (n i : ℕ) : MvPolynomial (Fin n) (ZMod p) := (P p n).coeff (p ^ i)

variable {S : Type*} [CommRing S] [Algebra (ZMod p) S]

theorem A_zero_eval {n : ℕ} (ξ : Fin n → S) :
    MvPolynomial.aeval ξ (A p n 0) = (-1) ^ n * moore p ξ ^ (p - 1) := by
  sorry

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

local notation "ι" n:max => algebraMap (MvPolynomial (Fin n) (ZMod p)) (𝕂 n)

end Grothendieck.Folder160
