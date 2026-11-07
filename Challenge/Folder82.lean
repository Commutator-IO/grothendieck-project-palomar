module

public import Mathlib

@[expose] public section

open Matrix

namespace Folder82

variable {R : Type*} [CommRing R]

/-- `xX̃ + yỸ + zH̃` with `X̃ = E₁₂`, `Ỹ = E₂₁`, `H̃ = diag(1, −1)`. -/
def coord (x y z : R) : Matrix (Fin 2) (Fin 2) R := !![z, x; y, -z]

open LieAlgebra.SpecialLinear in
/-- `sl(2)` over `R`. -/
abbrev Sl2 (R : Type*) [CommRing R] := sl (Fin 2) R

/-- The element `xX̃ + yỸ + zH̃` of `sl(2)`. -/
def slMk (x y z : R) : Sl2 R :=
  ⟨coord x y z, by simp [LieAlgebra.SpecialLinear.sl, coord, trace_fin_two]⟩

@[simp] theorem slMk_val (x y z : R) : (slMk x y z).val = coord x y z := rfl

theorem slMk_eta (u : Sl2 R) : u = slMk (u.val 0 1) (u.val 1 0) (u.val 0 0) := by
  have h : u.val.trace = 0 := u.2
  rw [trace_fin_two] at h
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; linear_combination h

theorem slMk_add (x y z x' y' z' : R) :
    slMk x y z + slMk x' y' z' = slMk (x + x') (y + y') (z + z') := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; ring

theorem slMk_smul (c x y z : R) : c • slMk x y z = slMk (c * x) (c * y) (c * z) := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]

/-- In characteristic 2, `sl(2)` is the Heisenberg algebra: `[u, u'] = (xy' − yx') H̃`. -/
theorem lie_slMk (h2 : (2 : R) = 0) (x y z x' y' z' : R) :
    ⁅slMk x y z, slMk x' y' z'⁆ = slMk 0 0 (x * y' - y * x') := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]
  · ring
  · linear_combination (z * x' - x * z') * h2
  · linear_combination (y * z' - z * y') * h2
  · ring

/-- The Lie endomorphism `xX̃ + yỸ + zH̃ ↦ g(x, y) + (ax + by + det g · z) H̃`, for a `2 × 2`
matrix `g` and `a, b ∈ R`: the pair `(g, (a, b))` of `GL(V) ⋉ Hom(V, det V)`. -/
def autFun (h2 : (2 : R) = 0) (g : Matrix (Fin 2) (Fin 2) R) (a b : R) : Sl2 R →ₗ⁅R⁆ Sl2 R where
  toFun u := slMk (g 0 0 * u.val 0 1 + g 0 1 * u.val 1 0) (g 1 0 * u.val 0 1 + g 1 1 * u.val 1 0)
    (a * u.val 0 1 + b * u.val 1 0 + g.det * u.val 0 0)
  map_add' u v := by
    rw [slMk_add]; congr 1 <;> simp <;> ring
  map_smul' c u := by
    rw [RingHom.id_apply, slMk_smul]; congr 1 <;> simp <;> ring
  map_lie' {u v} := by
    conv_lhs => rw [slMk_eta u, slMk_eta v, lie_slMk h2]
    rw [lie_slMk h2]
    simp only [slMk_val, coord, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one, det_fin_two]
    congr 1 <;> ring

/-- **Automorphisms of `sl(2)` in characteristic 2**: a Lie endomorphism is bijective iff it is
`autFun g a b` with `det g` a unit, the parameters being unique. So `Aut(sl(2))(R)` is
`GL₂(R) ⋉ R²` (`autFun_comp`), the automorphisms of the split pair `(V, E)`, `E` an extension
of `V` by `det V`: an affine group of dimension 6. -/
theorem bijective_iff (h2 : (2 : R) = 0) (φ : Sl2 R →ₗ⁅R⁆ Sl2 R) :
    Function.Bijective φ ↔ ∃ (g : Matrix (Fin 2) (Fin 2) R) (a b : R),
      IsUnit g.det ∧ φ = autFun h2 g a b := by
  sorry

end Folder82
