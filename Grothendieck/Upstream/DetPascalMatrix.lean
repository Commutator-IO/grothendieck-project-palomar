module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `det-pascal-matrix`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `det-pascal-matrix`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/LinearAlgebra/Matrix/Block.lean` -/


open Finset Function OrderDual
open Matrix
universe v
variable {α m n : Type*} {m' : α → Type*}
variable {R : Type v} {A : Type*} {M N : Matrix m m R} {b : m → α}
namespace Matrix
section LT
variable [LT α]
section Zero
variable [Zero R]
end Zero
end LT
section Preorder
variable [Preorder α]
section Zero
variable [Zero R]
variable [DecidableEq m]
end Zero
variable [CommRing R] [DecidableEq m]
end Preorder
section LinearOrder
variable [LinearOrder α]
end LinearOrder
variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
theorem isLowerTriangular_choose (n : ℕ) :
    (of fun i j : Fin n ↦ (i : ℕ).choose j).IsLowerTriangular :=
  fun _ _ h ↦ Nat.choose_eq_zero_of_lt h

/-- Vandermonde's identity in matrix form: the symmetric Pascal matrix `((i + j).choose i)` is
the product of the lower unitriangular matrix `(i.choose j)` and its transpose. -/
theorem choose_mul_transpose_choose (n : ℕ) :
    (of fun i j : Fin n ↦ (i : ℕ).choose j) * (of fun i j : Fin n ↦ (i : ℕ).choose j)ᵀ =
      of fun i j : Fin n ↦ (i + j : ℕ).choose i := by
  ext i j
  simp only [mul_apply, of_apply, transpose_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (i : ℕ).choose k * (j : ℕ).choose k),
    ← sum_subset (range_mono i.isLt) fun k _ hk ↦ by
      simp [Nat.choose_eq_zero_of_lt (not_lt.mp (mem_range.not.mp hk))],
    Nat.add_choose_eq, ← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_congr rfl fun k hk ↦ by simp [Nat.choose_symm (mem_range_succ_iff.mp hk)]

variable (R) in
/-- The symmetric Pascal matrix `((i + j).choose i)` has determinant `1`. -/
theorem det_pascal (n : ℕ) :
    (of fun i j : Fin n ↦ ((i + j : ℕ).choose i : R)).det = 1 := by
  change ((of fun i j : Fin n ↦ (i + j : ℕ).choose i).map (Nat.castRingHom R)).det = 1
  rw [← choose_mul_transpose_choose, Matrix.map_mul, transpose_map, det_mul, det_transpose,
    det_of_isLowerTriangular _ ((isLowerTriangular_choose n).map _)]
  simp

open Polynomial
end Matrix
