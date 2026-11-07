module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder83

open Polynomial TensorProduct

section Line

variable {k : Type*} [CommRing k]

/-- An element `x₀ + x₁u + x₂v + x₃uv` of `P = H ⊗ H'`, in the basis
`(1, u, v, uv)`. -/
@[ext] structure P (k : Type*) where
  x0 : k
  x1 : k
  x2 : k
  x3 : k

namespace P

instance : Add (P k) := ⟨fun x y => ⟨x.x0 + y.x0, x.x1 + y.x1, x.x2 + y.x2, x.x3 + y.x3⟩⟩

instance : SMul k (P k) := ⟨fun a x => ⟨a * x.x0, a * x.x1, a * x.x2, a * x.x3⟩⟩

@[simp] lemma add_x0 (x y : P k) : (x + y).x0 = x.x0 + y.x0 := rfl

@[simp] lemma add_x1 (x y : P k) : (x + y).x1 = x.x1 + y.x1 := rfl

@[simp] lemma add_x2 (x y : P k) : (x + y).x2 = x.x2 + y.x2 := rfl

@[simp] lemma add_x3 (x y : P k) : (x + y).x3 = x.x3 + y.x3 := rfl

@[simp] lemma smul_x0 (a : k) (x : P k) : (a • x).x0 = a * x.x0 := rfl

@[simp] lemma smul_x1 (a : k) (x : P k) : (a • x).x1 = a * x.x1 := rfl

@[simp] lemma smul_x2 (a : k) (x : P k) : (a • x).x2 = a * x.x2 := rfl

@[simp] lemma smul_x3 (a : k) (x : P k) : (a • x).x3 = a * x.x3 := rfl

/-- The basis vectors `1`, `u`, `v`, `uv`. -/
def one : P k := ⟨1, 0, 0, 0⟩

end P

open P

/-- The multiplication of `M(b, c; b', c'; t)` (table of page 92, left factor in
the row): `u² = bu − c`, `vu = (t − bb') + b'u + bv − uv`, `v(uv) = −bc' + c'u + tv`,
`(uv)u = −b'c + tu + cv`, `(uv)² = −cc' + t·uv`, and so on. -/
def mulM (b c b' c' t : k) (x y : P k) : P k where
  x0 := x.x0 * y.x0 - c * x.x1 * y.x1 - c' * x.x2 * y.x2 - c * c' * x.x3 * y.x3
    + (t - b * b') * x.x2 * y.x1 - b * c' * x.x2 * y.x3 - b' * c * x.x3 * y.x1
  x1 := x.x0 * y.x1 + x.x1 * y.x0 + b * x.x1 * y.x1 + b' * x.x2 * y.x1
    + c' * x.x2 * y.x3 - c' * x.x3 * y.x2 + t * x.x3 * y.x1
  x2 := x.x0 * y.x2 + x.x2 * y.x0 + b * x.x2 * y.x1 + b' * x.x2 * y.x2
    - c * x.x1 * y.x3 + c * x.x3 * y.x1 + t * x.x2 * y.x3
  x3 := x.x0 * y.x3 + x.x3 * y.x0 + b * x.x1 * y.x3 + b' * x.x3 * y.x2
    + t * x.x3 * y.x3 + x.x1 * y.x2 - x.x2 * y.x1

variable (b c b' c' t : k)

theorem one_mulM (x : P k) : mulM b c b' c' t one x = x := by
  ext <;> simp [mulM, one]

theorem mulM_one (x : P k) : mulM b c b' c' t x one = x := by
  ext <;> simp [mulM, one]

theorem mulM_add (x y z : P k) :
    mulM b c b' c' t x (y + z) = mulM b c b' c' t x y + mulM b c b' c' t x z := by
  ext <;> simp [mulM] <;> ring

theorem add_mulM (x y z : P k) :
    mulM b c b' c' t (x + y) z = mulM b c b' c' t x z + mulM b c b' c' t y z := by
  ext <;> simp [mulM] <;> ring

theorem mulM_smul (a : k) (x y : P k) :
    mulM b c b' c' t x (a • y) = a • mulM b c b' c' t x y := by
  ext <;> simp [mulM] <;> ring

theorem smul_mulM (a : k) (x y : P k) :
    mulM b c b' c' t (a • x) y = a • mulM b c b' c' t x y := by
  ext <;> simp [mulM] <;> ring

/-- Page 84 (« se vérifient »): `M(b, c; b', c'; t)` is associative, for every
value of the twist `t`, over any commutative ring. -/
theorem mulM_assoc (x y z : P k) :
    mulM b c b' c' t (mulM b c b' c' t x y) z = mulM b c b' c' t x (mulM b c b' c' t y z) := by
  ext <;> simp [mulM] <;> ring

end Line

section Locus

variable {k : Type*} [CommRing k] (b c b' c' t : k)

open P

/-- The quadratic polynomial of the twist line, `Q(t) = t² − bb't + b²c' + b'²c − 4cc'`. -/
def Q : k := t ^ 2 - b * b' * t + (b ^ 2 * c' + b' ^ 2 * c - 4 * c * c')

end Locus

end Grothendieck.Folder83

namespace Grothendieck.Folder83

open TensorProduct

section Azumaya

open scoped Kronecker

variable {k : Type*} [CommRing k]

/-- `M(b, c; b', c'; t)` as a type: `k⁴`, coordinates in the basis `(1, u, v, uv)`. -/
def MAlg (_b _c _b' _c' _t : k) : Type _ := Fin 4 → k

namespace MAlg

variable {b c b' c' t : k}

instance : AddCommGroup (MAlg b c b' c' t) := inferInstanceAs (AddCommGroup (Fin 4 → k))

instance : Module k (MAlg b c b' c' t) := inferInstanceAs (Module k (Fin 4 → k))

/-- The coordinates of an element of `MAlg`, as an element of `P k`. -/
def toP (x : MAlg b c b' c' t) : P k := ⟨x 0, x 1, x 2, x 3⟩

/-- The element of `MAlg` with given coordinates. -/
def ofP (x : P k) : MAlg b c b' c' t := ![x.x0, x.x1, x.x2, x.x3]

omit [CommRing k] in
lemma toP_injective : Function.Injective (toP : MAlg b c b' c' t → P k) := by
  intro x y h
  simp only [toP, P.mk.injEq] at h
  funext i; fin_cases i <;> simp [h]

lemma toP_add (x y : MAlg b c b' c' t) : toP (x + y) = toP x + toP y := rfl

lemma toP_smul (a : k) (x : MAlg b c b' c' t) : toP (a • x) = a • toP x := rfl

lemma toP_zero : toP (0 : MAlg b c b' c' t) = ⟨0, 0, 0, 0⟩ := rfl

instance : Mul (MAlg b c b' c' t) := ⟨fun x y => ofP (mulM b c b' c' t (toP x) (toP y))⟩

instance : One (MAlg b c b' c' t) := ⟨ofP P.one⟩

lemma toP_mul (x y : MAlg b c b' c' t) : toP (x * y) = mulM b c b' c' t (toP x) (toP y) := rfl

lemma toP_one : toP (1 : MAlg b c b' c' t) = P.one := rfl

instance : Ring (MAlg b c b' c' t) :=
  { (inferInstance : AddCommGroup (MAlg b c b' c' t)) with
    mul_assoc := fun x y z => toP_injective (by simp only [toP_mul]; exact mulM_assoc ..)
    one_mul := fun x => toP_injective (by rw [toP_mul, toP_one, one_mulM])
    mul_one := fun x => toP_injective (by rw [toP_mul, toP_one, mulM_one])
    left_distrib := fun x y z => toP_injective (by
      rw [toP_mul, toP_add, toP_add, mulM_add, toP_mul, toP_mul])
    right_distrib := fun x y z => toP_injective (by
      rw [toP_mul, toP_add, toP_add, add_mulM, toP_mul, toP_mul])
    zero_mul := fun x => toP_injective (by rw [toP_mul, toP_zero]; ext <;> simp [mulM])
    mul_zero := fun x => toP_injective (by rw [toP_mul, toP_zero]; ext <;> simp [mulM]) }

instance : Algebra k (MAlg b c b' c' t) :=
  Algebra.ofModule
    (fun a x y => toP_injective (by rw [toP_mul, toP_smul, smul_mulM, toP_smul, toP_mul]))
    (fun a x y => toP_injective (by rw [toP_mul, toP_smul, mulM_smul, toP_smul, toP_mul]))

/-- **Theorem of page 98.** `M(b, c; b', c'; t)` is an Azumaya algebra over `k`
(`IsAzumaya`: finite, projective, faithful, with `M ⊗ Mᵐᵒᵖ → End M` bijective) if and
only if `Q(t) = t² − bb't + b²c' + b'²c − 4cc'` is invertible in `k`. Over any
commutative ring, characteristic `2` included. -/
theorem isAzumaya_iff : IsAzumaya k (MAlg b c b' c' t) ↔ IsUnit (Q b c b' c' t) := by
  sorry

end MAlg

end Azumaya

end Grothendieck.Folder83
