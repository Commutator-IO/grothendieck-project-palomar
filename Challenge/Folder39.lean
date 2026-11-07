module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib

@[expose] public section

namespace Grothendieck.Folder39.Henselian

open MvPowerSeries

variable {k : Type*} [CommRing k]

/-- Conditions (I), (S), (R), (H) of pages 9–11 on a family `A n ⊆ k[[t₁, …, tₙ]]`; (R) is
built in, each `A n` being a unital subring. (S) is taken in its strong form (constants
allowed in `φ`), (H) with « isomorphisme formel » read as « has a two-sided inverse for
substitution ». -/
structure IsFormalClass (A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)) : Prop where
  /-- (I) -/
  X_mem : ∀ n (i : Fin n), X i ∈ A n
  /-- (S) -/
  subst_mem : ∀ {n m : ℕ} {φ : MvPowerSeries (Fin n) k} {f : Fin n → MvPowerSeries (Fin m) k},
    φ ∈ A n → (∀ i, f i ∈ A m) → (∀ i, IsNilpotent (constantCoeff (f i))) → subst f φ ∈ A m
  /-- (H) -/
  inv_mem : ∀ {n : ℕ} {f g : Fin n → MvPowerSeries (Fin n) k}, (∀ i, f i ∈ A n) →
    (∀ i, IsNilpotent (constantCoeff (f i))) → (∀ i, IsNilpotent (constantCoeff (g i))) →
    (∀ i, subst g (f i) = X i) → (∀ i, subst f (g i) = X i) → ∀ i, g i ∈ A n

variable {A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)}

/-- Corollary 3 of page 12 (the implicit function theorem in the class), under (I), (S), (R),
(H) alone: if `P ∈ A_{n+1}` (variables `Z, t₁, …, tₙ`) has `P(0) = 0` and `∂P/∂Z (0)` a unit
of `k`, the unique `F` with `F(0) = 0` and `P(F(t), t) = 0` lies in `A_n`. -/
theorem implicit_mem (hA : IsFormalClass A) {n : ℕ} {P : MvPowerSeries (Fin (n + 1)) k}
    (hP : P ∈ A (n + 1)) (h0 : constantCoeff P = 0)
    (h1 : IsUnit (coeff (Finsupp.single 0 1) P)) {F : MvPowerSeries (Fin n) k}
    (hF0 : constantCoeff F = 0)
    (hF : subst (Fin.cons F X : Fin (n + 1) → MvPowerSeries (Fin n) k) P = 0) : F ∈ A n := by
  sorry

end Grothendieck.Folder39.Henselian
