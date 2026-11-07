module

public import Mathlib

@[expose] public section

universe u

namespace Grothendieck.Folder84

open Polynomial TensorProduct

section Coordinates

variable {R : Type*} [CommRing R]

/-- The matrix of `σᵢ : x ↦ ψ(x)Tᵢ − x` in the basis `(eᵢ, xᵢ)` of `Eᵢ`, where
`Tᵢ = 2xᵢ − bᵢeᵢ`: `σᵢ(eᵢ) = −eᵢ`, `σᵢ(xᵢ) = xᵢ − bᵢeᵢ`. -/
def sigmaE (b : R) : Matrix (Fin 2) (Fin 2) R := !![-1, -b; 0, 1]

/-- `σ₁ ⊗ σ₂` on `E₁ ⊗ E₂`, in the basis `(eᵢ ⊗ eⱼ)` indexed by `Fin 2 × Fin 2`
(`0` for `e`, `1` for `x`). -/
def sigmaTensor (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) :=
  Matrix.mulVecLin (Matrix.kronecker (sigmaE b₁) (sigmaE b₂))

/-- The map `E₁ ⊗ E₂ → E₁ * E₂` of page 63 in coordinates: the coefficient of
`e₁ ⊗ e₂` in the image is `2a + b₂a' + b₁a''` (from `u₁ ⊗ u₂ ↦ 2u₁u₂`,
`u₁ ⊗ x₂ ↦ u₁b₂`, `x₁ ⊗ u₂ ↦ b₁u₂`), that of `x₁ * x₂` is the coefficient of
`x₁ ⊗ x₂`. -/
def starMap (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v := ![2 * v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0), v (1, 1)]
  map_add' v w := by
    funext i; fin_cases i <;> first | (simp; done) | (simp; ring)
  map_smul' r v := by
    funext i; fin_cases i <;> first | (simp; done) | (simp; ring)

lemma sigmaTensor_apply (b₁ b₂ : R) (v : Fin 2 × Fin 2 → R) :
    sigmaTensor b₁ b₂ v (0, 0) = v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (0, 1) = -v (0, 1) - b₁ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (1, 0) = -v (1, 0) - b₂ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (1, 1) = v (1, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp [sigmaTensor, sigmaE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; done)
      | (simp [sigmaTensor, sigmaE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; ring)

/-- Page 83: `E₁ ⊗ E₂ → E₁ * E₂` kills `Im(σ₁ ⊗ σ₂ − id)`. -/
theorem range_le_ker (b₁ b₂ : R) :
    LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id) ≤ LinearMap.ker (starMap b₁ b₂) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := sigmaTensor_apply b₁ b₂ v
  simp only [LinearMap.mem_ker, starMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply, h0, h1, h2, h3]
  funext i; fin_cases i <;> first | (simp; done) | (simp; ring)

/-- The induced map `E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂`. -/
noncomputable def coinvMap (b₁ b₂ : R) :
    ((Fin 2 × Fin 2 → R) ⧸ LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id)) →ₗ[R]
      (Fin 2 → R) :=
  (LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id)).liftQ (starMap b₁ b₂) (range_le_ker b₁ b₂)

/-- **Proposition (page 85), in coordinates.** The map
`E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂` is bijective if and only if
`2R + b₁R + b₂R = R`. -/
theorem coinvariants_bijective_iff (b₁ b₂ : R) :
    Function.Bijective (coinvMap b₁ b₂) ↔ Ideal.span {2, b₁, b₂} = ⊤ := by
  sorry

end Coordinates

end Grothendieck.Folder84

open CategoryTheory MonoidalCategory TensorProduct

open CategoryTheory TensorProduct
