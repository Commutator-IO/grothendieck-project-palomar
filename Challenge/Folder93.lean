module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.NumberTheory.Wilson
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open Polynomial

open scoped Ring

namespace Grothendieck.Folder93

variable {R : Type*} [CommRing R]

local notation "D" => Polynomial.hasseDeriv

/-- Numerator of `G₀`: `G₀(t, f) · (D⁽¹⁾f)² = (D⁽²⁾f)² − D⁽³⁾f · D⁽¹⁾f`. -/
noncomputable def N (f : R[X]) : R[X] := D 2 f ^ 2 - D 3 f * D 1 f

/-- Numerator of the classical `G = −2 f⁽³⁾/f' + 3 (f⁽²⁾/f')²`. -/
noncomputable def Ncl (f : R[X]) : R[X] :=
  3 * (derivative^[2] f) ^ 2 - 2 * derivative^[3] f * derivative f

open CategoryTheory CochainComplex HomComplex

end Grothendieck.Folder93

namespace Grothendieck.Folder93.Alpha

open Polynomial

open scoped Ring

local notation "D" => Polynomial.hasseDeriv

variable {A : Type*} [CommRing A] (p n : ℕ) (α : A)

/-- `T^(p^n) − α`. -/
noncomputable abbrev P : A[X] := X ^ p ^ n - C α

variable {p n α}

variable (p n α)

/-- The Proposition of pages 121–123 in `B = A[T]/(T^(p^n) − α)` for a local ring `A`
(so `Pic(A) = 0`), `α` arbitrary: if `C(k,3)` is a unit for `3 ≤ k < p^n`, `D⁽¹⁾s` is a unit
of `B` and `G₀(t, s) = 0` in `B`, then `s = (at + b)/(ct + d)` in `B` with `a, b, c, d ∈ A`
and `ct + d` a unit of `B`. -/
theorem rigidity_alpha_local [IsLocalRing A] [Fact p.Prime] [CharP A p] (hq : 3 < p ^ n)
    (hC : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : A)) (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P p n α) (D 1 s))) (hN : AdjoinRoot.mk (P p n α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p n α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p n α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p n α) (C c * X + C d)) := by
  sorry

end Grothendieck.Folder93.Alpha
