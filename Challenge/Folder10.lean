module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder10.NormOneTorus

open CategoryTheory groupCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (χ : Γ →* ℤˣ) (M : Rep.{0} k Γ)

/-- `M` twisted by the sign `χ`: `g ⋆ x = χ(g) · g x`. For `M = Lˣ` this is the norm-one torus
`G = Ker(N : R_{Z/k} 𝔾_m → 𝔾_m)` on `L`-points, `g ⋆ x = g(x)^{χ g}`. -/
def twistRep : Representation k Γ M.V where
  toFun g := (χ g : ℤ) • M.ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

/-- The identity of `M × M` when `χ g = 1`, the swap of the two factors otherwise. -/
def swapLin (g : Γ) : M.V × M.V →ₗ[k] M.V × M.V :=
  if χ g = 1 then LinearMap.id else (LinearMap.snd k M.V M.V).prod (LinearMap.fst k M.V M.V)

lemma swapLin_apply (g : Γ) (v : M.V × M.V) :
    swapLin χ M g v = if χ g = 1 then v else (v.2, v.1) := by
  unfold swapLin; split_ifs <;> rfl

/-- `M × M` with `g · (x, y) = (g x, g y)` if `χ g = 1` and `(g y, g x)` otherwise: for
`M = Lˣ` and `χ` the sign of a quadratic `Z ⊆ L`, this is `(Z ⊗_k L)ˣ`, the `L`-points of
`R_{Z/k} 𝔾_m`, written in the basis of the two idempotents. -/
def indRep : Representation k Γ (M.V × M.V) where
  toFun g := ((M.ρ g).prodMap (M.ρ g)) ∘ₗ swapLin χ M g
  map_one' := by
    ext v <;> simp [swapLin_apply]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, swapLin_apply, map_mul, Module.End.mul_apply]
    rcases Int.units_eq_one_or (χ g) with hg | hg <;>
      rcases Int.units_eq_one_or (χ h) with hh | hh <;> simp [hg, hh]

lemma indRep_apply (g : Γ) (v : M.V × M.V) :
    indRep χ M g v = if χ g = 1 then (M.ρ g v.1, M.ρ g v.2) else (M.ρ g v.2, M.ρ g v.1) := by
  change (M.ρ g).prodMap (M.ρ g) (swapLin χ M g v) = _
  rw [swapLin_apply]; split_ifs <;> rfl

lemma twistRep_apply (g : Γ) (v : M.V) : twistRep χ M g v = (χ g : ℤ) • M.ρ g v := rfl

/-- `x ↦ (x, -x)`. -/
def torusIncl : (twistRep χ M).IntertwiningMap (indRep χ M) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (twistRep χ M) (indRep χ M)
    (LinearMap.id.prod (-LinearMap.id))
    fun g v => by
      rw [indRep_apply, twistRep_apply]
      rcases Int.units_eq_one_or (χ g) with hg | hg <;> simp [hg]

/-- `(x, y) ↦ x + y`. -/
def normMap : (indRep χ M).IntertwiningMap M.ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (indRep χ M) M.ρ
    (LinearMap.coprod LinearMap.id LinearMap.id)
    fun g v => by
      rw [indRep_apply]
      split_ifs <;> simp [add_comm]

/-- `0 → G → Z^* → 𝔾_m → 0` of page 65, at the level of `Γ`-modules. -/
def torusSeq : ShortComplex (Rep.{0} k Γ) where
  X₁ := Rep.of (twistRep χ M)
  X₂ := Rep.of (indRep χ M)
  X₃ := M
  f := Rep.ofHom (torusIncl χ M)
  g := Rep.ofHom (normMap χ M)
  zero := by
    ext v
    simp [torusIncl_apply, normMap_apply]

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Page 65, Exemple 1, at a finite level: by Hilbert 90 (`H1ofAutOnUnitsUnique`),
`H²(Gal(L/K), G(L)) → H²(Gal(L/K), (Z ⊗_K L)ˣ)` is injective, for every sign `χ`. -/
theorem norm_one_torus_H2_injective (χ : Gal(L/K) →* ℤˣ) :
    Function.Injective
      (map (MonoidHom.id _) (A := Rep.of (twistRep χ (Rep.ofAlgebraAutOnUnits K L)))
        (torusSeq χ (Rep.ofAlgebraAutOnUnits K L)).f 2).hom := by
  sorry

end Grothendieck.Folder10.NormOneTorus
