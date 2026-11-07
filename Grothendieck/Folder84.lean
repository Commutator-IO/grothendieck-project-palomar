module

public import Mathlib

@[expose] public section


/-!
# Folder 84: the product of quadratic algebras, in split coordinates

The modernised reading `transcripts/84/84.modern.tex` (« Le produit contracté,
deviné », pages 62 to 65; « Le cas χ = 2 : involution et coinvariants »,
pages 79 to 87; « Trace et norme de A₁ ⊗ A₂ sur A₁ * A₂ », pages 98 to 106)
states, for quadratic algebras `Aᵢ` with bases `(1, Uᵢ)`,
`Uᵢ² + bᵢUᵢ + cᵢ = 0`:

> `A = A₁ * A₂ ≅ 𝒪[𝒰]/(𝒰² + b𝒰 + c)` with `b = b₁b₂`,
> `c = c₁b₂² + c₂b₁² − 4c₁c₂`, hence `δ = δ₁δ₂` (`δ = b² − 4c`), and
> `i(𝒰) = 2U₁U₂ + b₁U₂ + b₂U₁` in `A₁ ⊗ A₂`; that `i(𝒰)` satisfies the equation
> is the identity of page 64.
>
> **Proposition (page 85).** `E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂` is an
> isomorphism iff `2𝒪 + b₁𝒪 + b₂𝒪 = 𝒪` (in bases and splittings).
>
> **Corollaire (page 86).** Under that condition `A₁ * A₂ ≅ (A₁ ⊗ A₂)^{σ₁⊗σ₂}`,
> and conversely if this stays true after every base change.

These are findings `84-product-quadratic-algebras-formula` and
`84-product-coinvariants-one-etale` of `src/content/findings.ts`. Proving them
says only that the claims hold as stated in coordinates; whether they stand in
the literature is a separate question.

What is formalised, over an arbitrary commutative ring `R`, without dividing
by `2`:

* `identity_page64`, the polynomial identity of page 64, and its consequences
  `root_of_roots` (in any commutative ring) and `tensor_root` (in `A₁ ⊗[R] A₂`
  for any `R`-algebras `A₁`, `A₂` with roots `u₁`, `u₂`), together with the
  algebra map `productToTensor : R[𝒰]/(𝒰² + b𝒰 + c) → A₁ ⊗[R] A₂`,
  `𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`; `disc_mul` is `δ = δ₁δ₂`, and `four_mul_c` the
  relation `4c = b² − δ` of page 63;
* the proposition of page 85 in coordinates (`coinvariants_bijective_iff`):
  `E₁ ⊗ E₂ = R⁴` in the basis `(e₁⊗e₂, e₁⊗x₂, x₁⊗e₂, x₁⊗x₂)`, `σᵢ` the
  matrix of `x ↦ ψ(x)Tᵢ − x` in the basis `(eᵢ, xᵢ)` and `σ₁ ⊗ σ₂` their
  Kronecker product, `E₁ * E₂ = R²` in the basis `(e₁⊗e₂, x₁*x₂)` and
  `E₁ ⊗ E₂ → E₁ * E₂` the map `(x₁ + u₁) ⊗ (x₂ + u₂) ↦ x₁*x₂ + u₁b₂ + u₂b₁ + 2u₁u₂`
  of page 63; the induced map on the coinvariants is bijective iff
  `Ideal.span {2, b₁, b₂} = ⊤`. Both directions hold over `R` itself, with no
  base change;
* the corollary of page 86 in coordinates: `invariants_of_span_eq_top` (the
  map `A → A₁ ⊗ A₂`, `1 ↦ 1`, `𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`, is injective with
  image the invariants of `σ₁ ⊗ σ₂`), and `invariants_universally_iff`, the
  converse « after every base change »;
* `invariants_not_iff`: the converse needs the base change. Over `ℤ[X]`, with
  `b₁ = X` and `b₂ = 0`, the map `A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism,
  though `2, X, 0` generate a proper ideal.
* the theorem of page 48 in the free case (finding
  `84-two-regular-triplet-classification`): `qalg_iso_iff_moves` (over any `R`,
  `R[U]/(U² + bU + c) ≅ R[V]/(V² + b'V + c')` iff `V = εU + t`),
  `qalg_iso_iff_disc` (if `2` is a non-zero-divisor, iff `δ' = ε²δ` and
  `b' ≡ εb mod 2`), `translates_iff` and `translates_unique` (`L` with its basis
  fixed), `lift_indep` and `exists_of_congr` (every `δ ≡ τ² mod 4` occurs, any
  `R`), `int_disc_iff` and `int_qalg_iso_iff` (over `ℤ`), and
  `two_regular_needed` (over `𝔽₂`, `𝔽₂ × 𝔽₂` and `𝔽₄` share `δ` and `T₀`);
* `χ`-split extensions in coordinates (finding
  `84-chi-trivialised-extension-product`): `isChiSplitting_of`,
  `chiSplitting_eq`, `iso_iff` (morphisms are transvections, `b = b' + χw`),
  `prod_change` and `uProd_cocycle` (pages 129 and 131), `prod_comm`,
  `prod_assoc`, `prod_unit`, `chiRel_mul`, `invertible_iff` and
  `span_eq_top_iff_isUnit` (page 79, `L = 𝒪`), `push_pull`,
  `push_pull_square` and `push_pull_unit_iff` (pages 125 to 169: the comparison
  of pushout and pullback needs and uses `γχ = 2`).
-/

universe u

namespace Grothendieck.Folder84

open Polynomial TensorProduct

/-! ## The formula of pages 63, 64 and 89 -/

section Formula

variable {A : Type*} [CommRing A]

/-- The identity of page 64: with `Qᵢ = uᵢ² + bᵢuᵢ + cᵢ` and
`u = u₁b₂ + u₂b₁ + 2u₁u₂`, `u² + bu + c = b₂²Q₁ + b₁²Q₂ + 4(Q₁Q₂ − c₁Q₂ − c₂Q₁)`
for `b = b₁b₂`, `c = c₁b₂² + c₂b₁² − 4c₁c₂`. -/
theorem identity_page64 (b₁ c₁ b₂ c₂ u₁ u₂ : A) :
    (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁) ^ 2 + b₁ * b₂ * (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁)
        + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = b₂ ^ 2 * (u₁ ^ 2 + b₁ * u₁ + c₁) + b₁ ^ 2 * (u₂ ^ 2 + b₂ * u₂ + c₂)
        + 4 * ((u₁ ^ 2 + b₁ * u₁ + c₁) * (u₂ ^ 2 + b₂ * u₂ + c₂)
          - c₁ * (u₂ ^ 2 + b₂ * u₂ + c₂) - c₂ * (u₁ ^ 2 + b₁ * u₁ + c₁)) := by
  ring

/-- Pages 64 and 102: if `U₁² + b₁U₁ + c₁ = 0` and `U₂² + b₂U₂ + c₂ = 0` in a
commutative ring, then `𝒰 = 2U₁U₂ + b₁U₂ + b₂U₁` satisfies `𝒰² + b𝒰 + c = 0`
with `b = b₁b₂` and `c = c₁b₂² + c₂b₁² − 4c₁c₂`. -/
theorem root_of_roots {b₁ c₁ b₂ c₂ U₁ U₂ : A}
    (h₁ : U₁ ^ 2 + b₁ * U₁ + c₁ = 0) (h₂ : U₂ ^ 2 + b₂ * U₂ + c₂ = 0) :
    (2 * U₁ * U₂ + b₁ * U₂ + b₂ * U₁) ^ 2 + b₁ * b₂ * (2 * U₁ * U₂ + b₁ * U₂ + b₂ * U₁)
      + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂) = 0 := by
  rw [identity_page64, h₁, h₂]; ring

/-- Corollary of page 89: `δ = δ₁δ₂`, where `δ = b² − 4c`. -/
theorem disc_mul (b₁ c₁ b₂ c₂ : A) :
    (b₁ * b₂) ^ 2 - 4 * (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = (b₁ ^ 2 - 4 * c₁) * (b₂ ^ 2 - 4 * c₂) := by
  ring

/-- Page 63: the first form of the boxed `c`, `c₁δ₂ + c₂δ₁ + 4c₁c₂`, is the
second, `c₁b₂² + c₂b₁² − 4c₁c₂`. -/
theorem c_two_forms (b₁ c₁ b₂ c₂ : A) :
    c₁ * (b₂ ^ 2 - 4 * c₂) + c₂ * (b₁ ^ 2 - 4 * c₁) + 4 * c₁ * c₂
      = c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂ := by
  ring

variable {R : Type*} [CommRing R] {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂]
  [Algebra R A₁] [Algebra R A₂]

/-- The element `i(𝒰) = 2U₁U₂ + b₁U₂ + b₂U₁` of `A₁ ⊗[R] A₂`, with `U₁ = u₁ ⊗ 1`
and `U₂ = 1 ⊗ u₂`. -/
noncomputable def iU (b₁ b₂ : R) (u₁ : A₁) (u₂ : A₂) : A₁ ⊗[R] A₂ :=
  2 * (u₁ ⊗ₜ 1) * (1 ⊗ₜ u₂) + algebraMap R _ b₁ * (1 ⊗ₜ u₂) + algebraMap R _ b₂ * (u₁ ⊗ₜ 1)

/-- Page 102, in `A₁ ⊗[R] A₂`: the element `i(𝒰)` satisfies
`𝒰² + b₁b₂𝒰 + (c₁b₂² + c₂b₁² − 4c₁c₂) = 0`. -/
theorem tensor_root {b₁ c₁ b₂ c₂ : R} {u₁ : A₁} {u₂ : A₂}
    (h₁ : u₁ ^ 2 + algebraMap R A₁ b₁ * u₁ + algebraMap R A₁ c₁ = 0)
    (h₂ : u₂ ^ 2 + algebraMap R A₂ b₂ * u₂ + algebraMap R A₂ c₂ = 0) :
    iU b₁ b₂ u₁ u₂ ^ 2 + algebraMap R _ (b₁ * b₂) * iU b₁ b₂ u₁ u₂
      + algebraMap R _ (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂) = 0 := by
  have e₁ := congrArg (Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := A₂)) h₁
  have e₂ := congrArg (Algebra.TensorProduct.includeRight (R := R) (A := A₁)) h₂
  simp only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at e₁ e₂
  simp only [iU, map_mul, map_sub, map_add, map_pow, map_ofNat]
  linear_combination root_of_roots e₁ e₂

/-- The quadratic polynomial `𝒰² + b𝒰 + c` of the product. -/
noncomputable def prodPoly (b₁ c₁ b₂ c₂ : R) : R[X] :=
  X ^ 2 + C (b₁ * b₂) * X + C (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)

/-- Pages 98 to 102: the algebra map `i : R[𝒰]/(𝒰² + b𝒰 + c) → A₁ ⊗[R] A₂`,
`𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`. -/
noncomputable def productToTensor {b₁ c₁ b₂ c₂ : R} {u₁ : A₁} {u₂ : A₂}
    (h₁ : u₁ ^ 2 + algebraMap R A₁ b₁ * u₁ + algebraMap R A₁ c₁ = 0)
    (h₂ : u₂ ^ 2 + algebraMap R A₂ b₂ * u₂ + algebraMap R A₂ c₂ = 0) :
    AdjoinRoot (prodPoly b₁ c₁ b₂ c₂) →ₐ[R] A₁ ⊗[R] A₂ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (iU b₁ b₂ u₁ u₂) (by
    simp only [prodPoly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]
    simpa using tensor_root h₁ h₂)

theorem productToTensor_root {b₁ c₁ b₂ c₂ : R} {u₁ : A₁} {u₂ : A₂}
    (h₁ : u₁ ^ 2 + algebraMap R A₁ b₁ * u₁ + algebraMap R A₁ c₁ = 0)
    (h₂ : u₂ ^ 2 + algebraMap R A₂ b₂ * u₂ + algebraMap R A₂ c₂ = 0) :
    productToTensor h₁ h₂ (AdjoinRoot.root _) = iU b₁ b₂ u₁ u₂ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

end Formula

/-! ## The proposition of page 85 and the corollary of page 86, in coordinates -/

section Coordinates

variable {R : Type*} [CommRing R]

/-- The condition `2R + b₁R + b₂R = R`, written with coefficients. -/
theorem span_eq_top_iff (b₁ b₂ : R) :
    Ideal.span {2, b₁, b₂} = ⊤ ↔ ∃ g₀ g₁ g₂ : R, 2 * g₀ + b₁ * g₁ + b₂ * g₂ = 1 := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_insert]
  constructor
  · rintro ⟨a, z, hz, e⟩
    obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.1 hz
    exact ⟨a, p, q, by rw [e, ← hpq]; ring⟩
  · rintro ⟨g₀, g₁, g₂, e⟩
    exact ⟨g₀, b₁ * g₁ + b₂ * g₂, Ideal.mem_span_pair.2 ⟨g₁, g₂, by ring⟩, by
      rw [← e]; ring⟩

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

/-- Page 85, the inclusion that needs the condition: if `2R + b₁R + b₂R = R`,
the kernel of `E₁ ⊗ E₂ → E₁ * E₂` is in `Im(σ₁ ⊗ σ₂ − id)`. The preimage is
written with the Koszul relations of the unimodular row `(2, b₂, b₁)`. -/
theorem ker_le_range {b₁ b₂ : R} (h : Ideal.span {2, b₁, b₂} = ⊤) :
    LinearMap.ker (starMap b₁ b₂) ≤ LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id) := by
  obtain ⟨g₀, g₂, g₁, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
  intro v hv
  have hv0 : 2 * v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0) = 0 := by
    simpa [starMap] using congrFun hv 0
  have hv3 : v (1, 1) = 0 := by simpa [starMap] using congrFun hv 1
  set a := v (0, 0)
  set a' := v (0, 1)
  set a'' := v (1, 0)
  -- Koszul coefficients for `f = (2, b₂, b₁)`, `g = (g₀, g₁, g₂)`
  set c01 := g₁ * a - g₀ * a'
  set c02 := g₂ * a - g₀ * a''
  set c12 := g₂ * a' - g₁ * a''
  let w : Fin 2 × Fin 2 → R := fun p =>
    if p = (0, 1) then c01 - b₁ * c12 else if p = (1, 0) then c02 else if p = (1, 1) then c12
    else 0
  refine ⟨w, ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := sigmaTensor_apply b₁ b₂ w
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
    rw [h0]; simp [w]
    linear_combination a * hg - g₀ * hv0
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h1 ⊢
    rw [h1]; simp [w]
    linear_combination a' * hg - g₁ * hv0
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h2 ⊢
    rw [h2]; simp [w]
    linear_combination a'' * hg - g₂ * hv0
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.isValue, Fin.mk_one] at h3 ⊢
    rw [h3]; simp [hv3]

/-- **Proposition (page 85), in coordinates.** The map
`E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂` is bijective if and only if
`2R + b₁R + b₂R = R`. -/
theorem coinvariants_bijective_iff (b₁ b₂ : R) :
    Function.Bijective (coinvMap b₁ b₂) ↔ Ideal.span {2, b₁, b₂} = ⊤ := by
  constructor
  · rintro ⟨-, hs⟩
    obtain ⟨q, hq⟩ := hs ![1, 0]
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e := congrFun hq 0
    simp only [coinvMap, Submodule.liftQ_apply, starMap, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.isValue, Matrix.cons_val_zero] at e
    exact (span_eq_top_iff b₁ b₂).2 ⟨v (0, 0), v (1, 0), v (0, 1), by rw [← e]; ring⟩
  · intro h
    obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_le_range h)
    · intro y
      refine ⟨Submodule.Quotient.mk (fun p =>
        if p = (0, 0) then y 0 * g₀ else if p = (0, 1) then y 0 * g₂
        else if p = (1, 0) then y 0 * g₁ else y 1), ?_⟩
      simp only [coinvMap, Submodule.liftQ_apply, starMap, LinearMap.coe_mk, AddHom.coe_mk]
      ext i; fin_cases i
      · simp; linear_combination y 0 * hg
      · simp

/-- The map `i : A → A₁ ⊗ A₂` in coordinates: `A` in the basis `(1, 𝒰)`,
`A₁ ⊗ A₂` in the basis `(1, U₁, U₂, U₁U₂)`, indexed by `Fin 2 × Fin 2`
(`(1, 0)` for `U₁`, `(0, 1)` for `U₂`); `1 ↦ 1`, `𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`. -/
def iMap (b₁ b₂ : R) : (Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) where
  toFun v p :=
    if p = (0, 0) then v 0 else if p = (1, 0) then b₂ * v 1
    else if p = (0, 1) then b₁ * v 1 else 2 * v 1
  map_add' v w := by
    ext p; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' r v := by
    ext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- The matrix of the conjugation `σᵢ(x) = Tr(x) − x` of `Aᵢ` in the basis
`(1, Uᵢ)`: `σᵢ(1) = 1`, `σᵢ(Uᵢ) = −bᵢ − Uᵢ`. -/
def sigmaA (b : R) : Matrix (Fin 2) (Fin 2) R := !![1, -b; 0, -1]

/-- `σ₁ ⊗ σ₂` on `A₁ ⊗ A₂`. -/
def sigmaATensor (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) :=
  Matrix.mulVecLin (Matrix.kronecker (sigmaA b₁) (sigmaA b₂))

lemma sigmaATensor_apply (b₁ b₂ : R) (v : Fin 2 × Fin 2 → R) :
    sigmaATensor b₁ b₂ v (0, 0) = v (0, 0) - b₂ * v (0, 1) - b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) ∧
    sigmaATensor b₁ b₂ v (0, 1) = -v (0, 1) + b₁ * v (1, 1) ∧
    sigmaATensor b₁ b₂ v (1, 0) = -v (1, 0) + b₂ * v (1, 1) ∧
    sigmaATensor b₁ b₂ v (1, 1) = v (1, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp [sigmaATensor, sigmaA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; done)
      | (simp [sigmaATensor, sigmaA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; ring)

/-- `A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism: `i` is injective and its image is
the submodule of invariants of `σ₁ ⊗ σ₂`. -/
def InvariantsIso (b₁ b₂ : R) : Prop :=
  Function.Injective (iMap b₁ b₂) ∧
    LinearMap.range (iMap b₁ b₂) = LinearMap.ker (sigmaATensor b₁ b₂ - LinearMap.id)

lemma mem_invariants_iff {b₁ b₂ : R} (v : Fin 2 × Fin 2 → R) :
    v ∈ LinearMap.ker (sigmaATensor b₁ b₂ - LinearMap.id) ↔
      -b₂ * v (0, 1) - b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) = 0 ∧
      2 * v (0, 1) = b₁ * v (1, 1) ∧ 2 * v (1, 0) = b₂ * v (1, 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := sigmaATensor_apply b₁ b₂ v
  rw [LinearMap.mem_ker]
  constructor
  · intro hv
    have e0 := congrFun hv (0, 0)
    have e1 := congrFun hv (0, 1)
    have e2 := congrFun hv (1, 0)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Pi.zero_apply,
      h0, h1, h2] at e0 e1 e2
    refine ⟨by linear_combination e0, by linear_combination -e1, by linear_combination -e2⟩
  · rintro ⟨e0, e1, e2⟩
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Pi.zero_apply] <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h0 h1 h2 h3 ⊢
    · rw [h0]; linear_combination e0
    · rw [h1]; linear_combination -e1
    · rw [h2]; linear_combination -e2
    · rw [h3]; ring

lemma iMap_apply (b₁ b₂ : R) (v : Fin 2 → R) :
    iMap b₁ b₂ v (0, 0) = v 0 ∧ iMap b₁ b₂ v (1, 0) = b₂ * v 1 ∧
      iMap b₁ b₂ v (0, 1) = b₁ * v 1 ∧ iMap b₁ b₂ v (1, 1) = 2 * v 1 := by
  simp [iMap]

/-- **Corollaire (page 86), in coordinates.** If `2R + b₁R + b₂R = R`, then
`A → A₁ ⊗ A₂` is injective with image `(A₁ ⊗ A₂)^{σ₁⊗σ₂}`. -/
theorem invariants_of_span_eq_top {b₁ b₂ : R} (h : Ideal.span {2, b₁, b₂} = ⊤) :
    InvariantsIso b₁ b₂ := by
  obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
  refine ⟨?_, ?_⟩
  · intro v w hvw
    have k := fun p => congrFun hvw p
    obtain ⟨a0, a1, a2, a3⟩ := iMap_apply b₁ b₂ v
    obtain ⟨b0, b1, b2, b3⟩ := iMap_apply b₁ b₂ w
    have e0 := k (0, 0); have e1 := k (1, 0); have e2 := k (0, 1); have e3 := k (1, 1)
    rw [a0, b0] at e0; rw [a1, b1] at e1; rw [a2, b2] at e2; rw [a3, b3] at e3
    ext i; fin_cases i
    · exact e0
    · simp only [Fin.mk_one, Fin.isValue]
      linear_combination (w 1 - v 1) * hg + g₀ * e3 + g₁ * e2 + g₂ * e1
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨a0, a1, a2, a3⟩ := iMap_apply b₁ b₂ v
      rw [mem_invariants_iff, a1, a2, a3]
      refine ⟨by ring, by ring, by ring⟩
    · intro v hv
      obtain ⟨e0, e1, e2⟩ := (mem_invariants_iff v).1 hv
      refine ⟨![v (0, 0), v (1, 1) * g₀ + v (0, 1) * g₁ + v (1, 0) * g₂], ?_⟩
      obtain ⟨a0, a1, a2, a3⟩ := iMap_apply b₁ b₂ ![v (0, 0), v (1, 1) * g₀ + v (0, 1) * g₁ + v (1, 0) * g₂]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 a2 a3
      have key : b₁ * v (1, 0) = b₂ * v (0, 1) := by
        linear_combination -e0 - b₂ * e1
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      · exact a0
      · rw [a2]; linear_combination v (0, 1) * hg - g₀ * e1 + g₂ * key
      · rw [a1]; linear_combination v (1, 0) * hg - g₀ * e2 - g₁ * key
      · rw [a3]; linear_combination v (1, 1) * hg + g₁ * e1 + g₂ * e2

/-- **Corollaire (page 86), the converse « après tout changement de base ».**
`A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism after every base change `R → S` if
and only if `2R + b₁R + b₂R = R`. Base change to `R/(2, b₁, b₂)` is enough. -/
theorem invariants_universally_iff {R : Type u} [CommRing R] (b₁ b₂ : R) :
    (∀ (S : Type u) [CommRing S] (f : R →+* S), InvariantsIso (f b₁) (f b₂)) ↔
      Ideal.span {2, b₁, b₂} = ⊤ := by
  constructor
  · intro H
    by_contra hI
    set I := Ideal.span ({2, b₁, b₂} : Set R)
    have hS : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
    have hz : ∀ x ∈ ({2, b₁, b₂} : Set R), Ideal.Quotient.mk I x = 0 :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
    have h2 := hz 2 (by simp)
    have hb₁ := hz b₁ (by simp)
    have hb₂ := hz b₂ (by simp)
    obtain ⟨-, hr⟩ := H (R ⧸ I) (Ideal.Quotient.mk I)
    rw [hb₁, hb₂] at hr
    -- the invariant `U₂` is not in the image
    have hmem : (fun p => if p = ((0 : Fin 2), (1 : Fin 2)) then (1 : R ⧸ I) else 0) ∈
        LinearMap.ker (sigmaATensor (0 : R ⧸ I) 0 - LinearMap.id) := by
      rw [mem_invariants_iff]
      have : (2 : R ⧸ I) = 0 := (map_ofNat (Ideal.Quotient.mk I) 2).symm.trans h2
      simp [this]
    rw [← hr] at hmem
    obtain ⟨v, hv⟩ := hmem
    have e := congrFun hv (0, 1)
    obtain ⟨-, -, a2, -⟩ := iMap_apply (0 : R ⧸ I) 0 v
    rw [a2] at e
    simp at e
  · intro h S _ f
    apply invariants_of_span_eq_top
    obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
    exact (span_eq_top_iff _ _).2 ⟨f g₀, f g₁, f g₂, by
      rw [← map_one f, ← hg]; simp only [map_add, map_mul, map_ofNat]⟩

/-- The converse of page 86 needs the base change: over `ℤ[X]`, with `b₁ = X`
and `b₂ = 0`, `A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism, while `2`, `X`, `0`
generate the proper ideal `(2, X)`. -/
lemma two_eq_C : (2 : ℤ[X]) = C 2 := by simp

theorem invariants_not_iff :
    InvariantsIso (X : ℤ[X]) 0 ∧ Ideal.span {(2 : ℤ[X]), X, 0} ≠ ⊤ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v w hvw
    obtain ⟨a0, -, -, a3⟩ := iMap_apply (X : ℤ[X]) 0 v
    obtain ⟨b0, -, -, b3⟩ := iMap_apply (X : ℤ[X]) 0 w
    have e0 := congrFun hvw (0, 0); have e3 := congrFun hvw (1, 1)
    rw [a0, b0] at e0; rw [a3, b3] at e3
    funext i; fin_cases i
    · exact e0
    · exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ[X]) ≠ 0) e3
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨-, a1, a2, a3⟩ := iMap_apply (X : ℤ[X]) 0 v
      rw [mem_invariants_iff, a1, a2, a3]
      refine ⟨by ring, by ring, by ring⟩
    · intro v hv
      obtain ⟨-, e1, e2⟩ := (mem_invariants_iff v).1 hv
      -- `2 v(1,0) = 0`, so `v(1,0) = 0`; `2 v(0,1) = X v(1,1)`, so `2 ∣ v(1,1)`
      have z : v (1, 0) = 0 := by
        rw [zero_mul] at e2; exact (mul_eq_zero.1 e2).resolve_left two_ne_zero
      have hp : Prime (2 : ℤ[X]) := by
        simpa using (Polynomial.prime_C_iff (r := (2 : ℤ))).2 Int.prime_two
      have hd : (2 : ℤ[X]) ∣ X * v (1, 1) := ⟨v (0, 1), e1.symm⟩
      have h2X : ¬ (2 : ℤ[X]) ∣ X := by
        rintro ⟨q, hq⟩
        have := congrArg (fun p => p.coeff 1) hq
        simp only [coeff_X_one] at this
        rw [two_eq_C, coeff_C_mul] at this
        omega
      obtain ⟨μ, hμ⟩ := (hp.dvd_or_dvd hd).resolve_left h2X
      refine ⟨![v (0, 0), μ], ?_⟩
      obtain ⟨a0, a1, a2, a3⟩ := iMap_apply (X : ℤ[X]) 0 ![v (0, 0), μ]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 a2 a3
      funext p; obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      · exact a0
      · rw [a2]
        apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ[X]) ≠ 0)
        rw [e1, hμ]; ring
      · simp [a1, z]
      · rw [a3, hμ]
  · intro htop
    obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff (X : ℤ[X]) 0).1 htop
    rw [two_eq_C] at hg
    have := congrArg (fun p : ℤ[X] => p.coeff 0) hg
    simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, zero_mul, add_zero,
      coeff_one_zero] at this
    omega

end Coordinates

/-! ## The theorem of page 48 in the free case: quadratic algebras and `(δ, T₀)` -/

section TwoRegular

variable {R : Type*} [CommRing R]

/-- The polynomial `U² + bU + c`. -/
noncomputable def qpoly (b c : R) : R[X] := X ^ 2 + C b * X + C c

lemma qpoly_monic (b c : R) : (qpoly b c).Monic := by
  unfold qpoly; monicity!

lemma qpoly_natDegree [Nontrivial R] (b c : R) : (qpoly b c).natDegree = 2 := by
  unfold qpoly; compute_degree!

lemma qpoly_eval₂ {S : Type*} [CommRing S] (f : R →+* S) (x : S) (b c : R) :
    (qpoly b c).eval₂ f x = x ^ 2 + f b * x + f c := by
  simp [qpoly]

/-- The quadratic algebra `R[U]/(U² + bU + c)`. -/
abbrev QAlg (b c : R) := AdjoinRoot (qpoly b c)

lemma root_sq (b c : R) :
    AdjoinRoot.root (qpoly b c) ^ 2 + algebraMap R (QAlg b c) b * AdjoinRoot.root _
      + algebraMap R (QAlg b c) c = 0 := by
  have : AdjoinRoot.mk (qpoly b c) (X ^ 2 + C b * X + C c) = 0 := AdjoinRoot.mk_self
  simpa using this

/-- `(1, U)` is free in `R[U]/(U² + bU + c)`. -/
lemma coords_zero {b c a e : R}
    (h : algebraMap R (QAlg b c) a + algebraMap R (QAlg b c) e * AdjoinRoot.root _ = 0) :
    a = 0 ∧ e = 0 := by
  have hm : AdjoinRoot.mk (qpoly b c) (C e * X + C a) = 0 := by
    rw [← h]; simp [add_comm]
  rw [AdjoinRoot.mk_eq_zero] at hm
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hp : C e * X + C a = 0
  · exact ⟨by simpa using congrArg (coeff · 0) hp, by simpa using congrArg (coeff · 1) hp⟩
  · refine absurd hm ((qpoly_monic b c).not_dvd_of_natDegree_lt hp ?_)
    rw [qpoly_natDegree]
    exact lt_of_le_of_lt natDegree_linear_le (by norm_num)

/-- `(1, U)` generates `R[U]/(U² + bU + c)`. -/
lemma coords_exist {b c : R} (y : QAlg b c) :
    ∃ a e : R, y = algebraMap R _ a + algebraMap R _ e * AdjoinRoot.root _ := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have h10 : (1 : R) = 0 := Subsingleton.elim _ _
    refine ⟨0, 0, ?_⟩
    have : (1 : QAlg b c) = 0 := by rw [← map_one (algebraMap R (QAlg b c)), h10, map_zero]
    rw [← mul_one y, this]; simp
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  have hm := qpoly_monic b c
  have h1 : qpoly b c ≠ 1 := fun h => by simpa [qpoly_natDegree] using congrArg natDegree h
  have hq : (p %ₘ qpoly b c).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm h1
    rw [qpoly_natDegree] at this; omega
  refine ⟨(p %ₘ qpoly b c).coeff 0, (p %ₘ qpoly b c).coeff 1, ?_⟩
  have e : AdjoinRoot.mk (qpoly b c) p = AdjoinRoot.mk (qpoly b c) (p %ₘ qpoly b c) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ qpoly b c, by linear_combination -modByMonic_add_div p (qpoly b c)⟩
  rw [e, eq_X_add_C_of_natDegree_le_one hq]
  simp [add_comm]

/-- The change of variables `V = εU + t` of the quadratic data:
`(b, c) ↦ (εb − 2t, ε²c − εbt + t²)`. -/
def Moves (b c b' c' : R) : Prop :=
  ∃ (ε : Rˣ) (t : R), b' = ε * b - 2 * t ∧ c' = ε ^ 2 * c - ε * b * t + t ^ 2

/-- If `(b', c')` comes from `(b, c)` by `V = εU + t`, the algebras are isomorphic. -/
noncomputable def movesHom {b c b' c' : R} (ε : Rˣ) (t : R)
    (hb : b' = ε * b - 2 * t) (hc : c' = ε ^ 2 * c - ε * b * t + t ^ 2) :
    QAlg b' c' →ₐ[R] QAlg b c :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R _ (ε : R) * AdjoinRoot.root _ + algebraMap R _ t) (by
      have r := root_sq b c
      show (qpoly b' c').eval₂ (algebraMap R (QAlg b c)) _ = 0
      rw [qpoly_eval₂, hb, hc]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap R (QAlg b c) (ε : R)) ^ 2 * r)

lemma moves_symm {b c b' c' : R} (ε : Rˣ) (t : R)
    (hb : b' = ε * b - 2 * t) (hc : c' = ε ^ 2 * c - ε * b * t + t ^ 2) :
    b = ((ε⁻¹ : Rˣ) : R) * b' - 2 * (-((ε⁻¹ : Rˣ) : R) * t) ∧
      c = ((ε⁻¹ : Rˣ) : R) ^ 2 * c' - ((ε⁻¹ : Rˣ) : R) * b' * (-((ε⁻¹ : Rˣ) : R) * t)
        + (-((ε⁻¹ : Rˣ) : R) * t) ^ 2 := by
  have u : ((ε⁻¹ : Rˣ) : R) * ε = 1 := by simp
  constructor
  · rw [hb]; linear_combination (-b) * u
  · rw [hc, hb]; linear_combination (-c * (((ε⁻¹ : Rˣ) : R) * ε + 1)) * u

/-- **The free case of the classification, any base.** `R[U]/(U² + bU + c)` and
`R[V]/(V² + b'V + c')` are isomorphic `R`-algebras if and only if
`(b', c')` comes from `(b, c)` by a change of variables `V = εU + t`,
`ε` a unit. -/
theorem qalg_iso_iff_moves (b c b' c' : R) :
    Nonempty (QAlg b c ≃ₐ[R] QAlg b' c') ↔ Moves b c b' c' := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨t, ε, hV⟩ := coords_exist (φ.symm (AdjoinRoot.root (qpoly b' c')))
    obtain ⟨s, η, hU⟩ := coords_exist (φ (AdjoinRoot.root (qpoly b c)))
    -- `ηε = 1`
    have hηε : η * ε = 1 := by
      have e := φ.symm_apply_apply (AdjoinRoot.root (qpoly b c))
      rw [hU, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hV] at e
      have : algebraMap R (QAlg b c) (s + η * t) + algebraMap R (QAlg b c) (η * ε - 1)
          * AdjoinRoot.root _ = 0 := by
        simp only [map_add, map_mul, map_sub, map_one]; linear_combination e
      linear_combination (coords_zero this).2
    have key := congrArg φ.symm (root_sq b' c')
    simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, map_zero, hV] at key
    have r := root_sq b c
    have : algebraMap R (QAlg b c) (t ^ 2 + b' * t + c' - ε ^ 2 * c)
        + algebraMap R (QAlg b c) (2 * t * ε + b' * ε - ε ^ 2 * b) * AdjoinRoot.root _ = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination key - (algebraMap R (QAlg b c) ε) ^ 2 * r
    obtain ⟨h0, h1⟩ := coords_zero this
    have hb' : b' = ε * b - 2 * t := by
      linear_combination η * h1 - (2 * t + b' - ε * b) * hηε
    refine ⟨Units.mkOfMulEqOne ε η (by rw [mul_comm]; exact hηε), t, hb', ?_⟩
    simp only [Units.val_mkOfMulEqOne]
    linear_combination h0 - t * hb'
  · rintro ⟨ε, t, hb, hc⟩
    obtain ⟨hb₁, hc₁⟩ := moves_symm ε t hb hc
    refine ⟨AlgEquiv.ofAlgHom (movesHom _ _ hb₁ hc₁) (movesHom ε t hb hc) ?_ ?_⟩
    · apply AdjoinRoot.algHom_ext
      simp only [movesHom, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftAlgHom_root,
        map_add, map_mul, AlgHom.commutes, AlgHom.id_apply]
      rw [← sub_eq_zero]
      have u : ((ε⁻¹ : Rˣ) : R) * ε = 1 := by simp
      have := congrArg (algebraMap R (QAlg b' c')) u
      simp only [map_mul, map_one] at this
      simp only [map_neg]
      linear_combination (AdjoinRoot.root (qpoly b' c') - algebraMap R _ t) * this
    · apply AdjoinRoot.algHom_ext
      simp only [movesHom, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftAlgHom_root,
        map_add, map_mul, AlgHom.commutes, AlgHom.id_apply]
      rw [← sub_eq_zero]
      have u : (ε : R) * ((ε⁻¹ : Rˣ) : R) = 1 := by simp
      have := congrArg (algebraMap R (QAlg b c)) u
      simp only [map_mul, map_one] at this
      simp only [map_neg]
      linear_combination AdjoinRoot.root (qpoly b c) * this

/-- The discriminant `δ = b² − 4c`. -/
def disc (b c : R) : R := b ^ 2 - 4 * c

/-- Page 47: `δ ≡ b² (mod 4)`, over any base. -/
theorem disc_congr (b c : R) : b ^ 2 - disc b c = 4 * c := by unfold disc; ring

/-- Page 47: the congruence `T₀² ≡ δ (mod 4)` does not depend on the lift `τ` of
`T₀ ∈ R/2R`, since `(τ + 2a)² ≡ τ² (mod 4)`. -/
theorem lift_indep (τ a δ : R) (h : ∃ k, τ ^ 2 - δ = 4 * k) :
    ∃ k, (τ + 2 * a) ^ 2 - δ = 4 * k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + a * τ + a ^ 2, by linear_combination hk⟩

/-- Under `V = εU + t`, `δ' = ε²δ` and `b' ≡ εb (mod 2)`, over any base. -/
theorem moves_invariants {b c b' c' : R} (h : Moves b c b' c') :
    ∃ ε : Rˣ, disc b' c' = (ε : R) ^ 2 * disc b c ∧ ∃ s, b' = ε * b + 2 * s := by
  obtain ⟨ε, t, hb, hc⟩ := h
  exact ⟨ε, by rw [disc, disc, hb, hc]; ring, -t, by rw [hb]; ring⟩

lemma cancel_four (h2 : ∀ x : R, 2 * x = 0 → x = 0) {x y : R} (h : 4 * x = 4 * y) : x = y := by
  rw [← sub_eq_zero]
  apply h2; apply h2
  linear_combination h

/-- **Théorème (page 48), the free affine case.** If `2` is a non-zero-divisor
in `R`, `(b, c)` and `(b', c')` differ by a change of variables `V = εU + t`
if and only if `δ' = ε²δ` and `b' ≡ εb (mod 2)` for some unit `ε`. -/
theorem moves_iff_disc (h2 : ∀ x : R, 2 * x = 0 → x = 0) (b c b' c' : R) :
    Moves b c b' c' ↔
      ∃ ε : Rˣ, disc b' c' = (ε : R) ^ 2 * disc b c ∧ ∃ s, b' = ε * b + 2 * s := by
  refine ⟨moves_invariants, ?_⟩
  rintro ⟨ε, hd, s, hs⟩
  refine ⟨ε, -s, by rw [hs]; ring, cancel_four h2 ?_⟩
  unfold disc at hd
  rw [hs] at hd
  linear_combination -hd

/-- The isomorphism classes of free quadratic algebras over `R`, `2` regular, are
classified by `(δ, b mod 2)` up to `(ε²δ, εb)`. -/
theorem qalg_iso_iff_disc (h2 : ∀ x : R, 2 * x = 0 → x = 0) (b c b' c' : R) :
    Nonempty (QAlg b c ≃ₐ[R] QAlg b' c') ↔
      ∃ ε : Rˣ, disc b' c' = (ε : R) ^ 2 * disc b c ∧ ∃ s, b' = ε * b + 2 * s := by
  rw [qalg_iso_iff_moves, moves_iff_disc h2]

/-- With `L` and its basis fixed (`ε = 1`), the translations `V = U + t`. -/
def Translates (b c b' c' : R) (t : R) : Prop := b' = b - 2 * t ∧ c' = c - b * t + t ^ 2

/-- **Théorème (page 48), with `L` trivialised.** If `2` is regular, a
translation from `(b, c)` to `(b', c')` exists iff `δ' = δ` and
`b' ≡ b (mod 2)`, and it is unique: the groupoid of free quadratic algebras with
`L = R` is equivalent to the discrete set of pairs `(δ, T₀)`. -/
theorem translates_iff (h2 : ∀ x : R, 2 * x = 0 → x = 0) (b c b' c' : R) :
    (∃ t, Translates b c b' c' t) ↔ disc b' c' = disc b c ∧ ∃ s, b' = b + 2 * s := by
  constructor
  · rintro ⟨t, hb, hc⟩
    exact ⟨by rw [disc, disc, hb, hc]; ring, -t, by rw [hb]; ring⟩
  · rintro ⟨hd, s, hs⟩
    refine ⟨-s, by rw [hs]; ring, cancel_four h2 ?_⟩
    unfold disc at hd; rw [hs] at hd
    linear_combination -hd

theorem translates_unique (h2 : ∀ x : R, 2 * x = 0 → x = 0) {b c b' c' t t' : R}
    (h : Translates b c b' c' t) (h' : Translates b c b' c' t') : t = t' := by
  rw [← sub_eq_zero]; apply h2; linear_combination h.1 - h'.1

/-- **Théorème (page 48), essential surjectivity.** Over any base, every `δ` with
a `τ` such that `τ² ≡ δ (mod 4)` is the discriminant of `(τ, c)` for some `c`;
conversely `b² ≡ δ (mod 4)` for every `(b, c)`. -/
theorem exists_of_congr (δ τ : R) (h : ∃ k, τ ^ 2 - δ = 4 * k) :
    ∃ c, disc τ c = δ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by unfold disc; linear_combination hk⟩

/-- Page 53, over `ℤ`: the discriminants are the integers `≡ 0, 1 (mod 4)`. -/
theorem int_disc_iff (δ : ℤ) : (∃ b c : ℤ, disc b c = δ) ↔ δ % 4 = 0 ∨ δ % 4 = 1 := by
  constructor
  · rintro ⟨b, c, rfl⟩
    rcases Int.even_or_odd b with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have e : disc (k + k) c = 4 * (k ^ 2 - c) := by unfold disc; ring
      rw [e]; generalize k ^ 2 - c = m; omega
    · have e : disc (2 * k + 1) c = 4 * (k ^ 2 + k - c) + 1 := by unfold disc; ring
      rw [e]; generalize k ^ 2 + k - c = m; omega
  · rintro (h | h)
    · exact ⟨0, -(δ / 4), by unfold disc; omega⟩
    · exact ⟨1, (1 - δ) / 4, by unfold disc; omega⟩

/-- Page 53, over `ℤ`: `T₀` is determined by `δ`, and two quadratic rings
`ℤ[U]/(U² + bU + c)` are isomorphic iff they have the same discriminant. -/
theorem int_qalg_iso_iff (b c b' c' : ℤ) :
    Nonempty (QAlg b c ≃ₐ[ℤ] QAlg b' c') ↔ disc b c = disc b' c' := by
  have h2 : ∀ x : ℤ, 2 * x = 0 → x = 0 := fun x hx => by omega
  rw [qalg_iso_iff_disc h2]
  constructor
  · rintro ⟨ε, hd, -⟩
    have : (ε : ℤ) ^ 2 = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
    rw [hd, this, one_mul]
  · intro hd
    refine ⟨1, by rw [hd]; simp, ?_⟩
    have hev : Even ((b' - b) * (b' + b)) := ⟨2 * (c' - c), by
      unfold disc at hd; linear_combination -hd⟩
    have hsub : Even (b' - b) :=
      (Int.even_mul.1 hev).elim id fun h => by rwa [Int.even_sub, ← Int.even_add]
    obtain ⟨s, hs⟩ := hsub
    exact ⟨s, by simp; linear_combination hs⟩

/-- The hypothesis « 2 regular » is needed: over `𝔽₂`, `(b, c) = (1, 0)` and
`(1, 1)` have the same `δ = 1` and the same `b mod 2`, but `𝔽₂[U]/(U² + U)` and
`𝔽₂[U]/(U² + U + 1)` (that is `𝔽₂ × 𝔽₂` and `𝔽₄`) are not isomorphic. -/
theorem two_regular_needed :
    disc (1 : ZMod 2) 0 = disc (1 : ZMod 2) 1 ∧
      ¬ Nonempty (QAlg (1 : ZMod 2) 0 ≃ₐ[ZMod 2] QAlg (1 : ZMod 2) 1) := by
  refine ⟨by unfold disc; decide, ?_⟩
  rw [qalg_iso_iff_moves]
  rintro ⟨ε, t, -, hc⟩
  have hε : (ε : ZMod 2) = 1 := by
    clear hc
    have := ε.ne_zero
    generalize (ε : ZMod 2) = e at this ⊢
    fin_cases e <;> first | rfl | exact (this rfl).elim
  rw [hε] at hc
  fin_cases t <;> revert hc <;> decide

end TwoRegular

/-! ## `χ`-split extensions and their product, in coordinates -/

section ChiSplit

variable {R : Type*} [CommRing R] (χ : R)
variable {M L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup L] [Module R L]

/-- The `χ`-retraction of `E = M ⊕ L` given by `b : M → L`:
`π(η, ξ) = b(η) + χξ` (pages 77 and 129). -/
def piOf (b : M →ₗ[R] L) : M × L →ₗ[R] L :=
  b ∘ₗ LinearMap.fst R M L + χ • LinearMap.snd R M L

/-- The `χ`-section `ϖ(η) = (χη, −b(η))`. -/
def varpiOf (b : M →ₗ[R] L) : M →ₗ[R] M × L :=
  LinearMap.prod (χ • LinearMap.id) (-b)

/-- A `χ`-scindage `(π, ϖ)` of `0 → L → M ⊕ L → M → 0` (page 169):
`πα = χ`, `ψϖ = χ`, `απ + ϖψ = χ`. -/
structure IsChiSplitting (π : M × L →ₗ[R] L) (ϖ : M →ₗ[R] M × L) : Prop where
  retr : π ∘ₗ LinearMap.inr R M L = χ • LinearMap.id
  sect : LinearMap.fst R M L ∘ₗ ϖ = χ • LinearMap.id
  sum : LinearMap.inr R M L ∘ₗ π + ϖ ∘ₗ LinearMap.fst R M L = χ • LinearMap.id

theorem isChiSplitting_of (b : M →ₗ[R] L) : IsChiSplitting χ (piOf χ b) (varpiOf χ b) where
  retr := by ext; simp [piOf]
  sect := by ext; simp [varpiOf]
  sum := by
    apply LinearMap.prod_ext <;> ext <;> simp [piOf, varpiOf]

/-- Page 129: on a split extension, a `χ`-scindage is determined by
`b = π|_M : M → L`, and it is `(piOf b, varpiOf b)`. -/
theorem chiSplitting_eq {π : M × L →ₗ[R] L} {ϖ : M →ₗ[R] M × L}
    (h : IsChiSplitting χ π ϖ) :
    π = piOf χ (π ∘ₗ LinearMap.inl R M L) ∧ ϖ = varpiOf χ (π ∘ₗ LinearMap.inl R M L) := by
  constructor
  · apply LinearMap.prod_ext
    · ext; simp [piOf]
    · ext ξ
      have := LinearMap.congr_fun h.retr ξ
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.inr_apply] at this
      simp [piOf]
      rw [show ((0 : M), (0 : L)) = 0 from rfl, map_zero, zero_add, this]
  · ext η
    · simpa [varpiOf] using LinearMap.congr_fun h.sect η
    · have := congrArg Prod.snd (LinearMap.congr_fun h.sum (η, 0))
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.inr_apply, LinearMap.fst_apply, Prod.snd_add, LinearMap.smul_apply,
        LinearMap.id_apply, Prod.smul_snd, smul_zero] at this
      simp [varpiOf]
      linear_combination (norm := module) this

/-- The transvection `(η, ξ) ↦ (η, ξ + w(η))` of `M ⊕ L`. -/
def transv (w : M →ₗ[R] L) : M × L →ₗ[R] M × L :=
  LinearMap.id + LinearMap.inr R M L ∘ₗ w ∘ₗ LinearMap.fst R M L

theorem transv_comp (w w' : M →ₗ[R] L) : transv w ∘ₗ transv w' = transv (w + w') := by
  refine LinearMap.ext fun p => Prod.ext ?_ ?_
  · simp [transv]
  · simp [transv]; abel

/-- A transvection carries the scindage of `b' + χw` to that of `b'`. -/
theorem piOf_comp_transv (b' w : M →ₗ[R] L) :
    piOf χ b' ∘ₗ transv w = piOf χ (b' + χ • w) := by
  apply LinearMap.prod_ext <;> ext <;> simp [piOf, transv]

theorem transv_comp_varpiOf (b' w : M →ₗ[R] L) :
    transv w ∘ₗ varpiOf χ (b' + χ • w) = varpiOf χ b' := by
  ext <;> simp [varpiOf, transv]

/-- **Morphisms in coordinates (pages 77 and 129).** An endomorphism `f` of
`M ⊕ L` inducing the identity on `L` and on `M` carries the scindage of `b` to
that of `b'` if and only if it is a transvection `T_w` with `b = b' + χw`; there
is such an `f` iff `b ≡ b' (mod χ)`. Every such `f` is invertible, `T_w⁻¹ = T_{−w}`. -/
theorem iso_iff (b b' : M →ₗ[R] L) :
    (∃ f : M × L →ₗ[R] M × L, LinearMap.fst R M L ∘ₗ f = LinearMap.fst R M L ∧
        f ∘ₗ LinearMap.inr R M L = LinearMap.inr R M L ∧ piOf χ b' ∘ₗ f = piOf χ b) ↔
      ∃ w : M →ₗ[R] L, b = b' + χ • w := by
  constructor
  · rintro ⟨f, h1, h2, h3⟩
    set w := LinearMap.snd R M L ∘ₗ f ∘ₗ LinearMap.inl R M L with hw
    have hf : f = transv w := by
      refine LinearMap.ext fun p => ?_
      obtain ⟨η, ξ⟩ := p
      have hp : ((η, ξ) : M × L) = (η, 0) + (0, ξ) := by simp
      have h1' := LinearMap.congr_fun h1 (η, 0)
      have h2' := LinearMap.congr_fun h2 ξ
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
        LinearMap.inr_apply] at h1' h2'
      rw [hp, map_add, map_add, h2']
      refine Prod.ext ?_ ?_
      · simp [transv, h1']
      · simp [transv, hw]
        rw [show ((0 : M), (0 : L)) = 0 from rfl, map_zero]; rfl
    refine ⟨w, ?_⟩
    have e := h3.symm.trans (by rw [hf, piOf_comp_transv])
    ext η
    simpa [piOf] using LinearMap.congr_fun e (η, 0)
  · rintro ⟨w, rfl⟩
    refine ⟨transv w, ?_, ?_, piOf_comp_transv χ b' w⟩
    · ext <;> simp [transv]
    · ext <;> simp [transv]

variable {M₁ M₂ M₃ L₁ L₂ L₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M₃] [Module R M₃] [AddCommGroup L₁] [Module R L₁]
  [AddCommGroup L₂] [Module R L₂] [AddCommGroup L₃] [Module R L₃]

/-- The transvection datum of page 129: `u = b₁ ⊗ u₂ + u₁ ⊗ b₂ + χ u₁ ⊗ u₂`. -/
noncomputable def uProd (b₁ u₁ : M₁ →ₗ[R] L₁) (b₂ u₂ : M₂ →ₗ[R] L₂) :
    M₁ ⊗[R] M₂ →ₗ[R] L₁ ⊗[R] L₂ :=
  TensorProduct.map b₁ u₂ + TensorProduct.map u₁ b₂ + χ • TensorProduct.map u₁ u₂

/-- **Page 129.** Changing the scindages, `bᵢ ↦ bᵢ + χuᵢ`, changes the product
datum `b = b₁ ⊗ b₂` by `χu`: `b′₁ ⊗ b′₂ = b₁ ⊗ b₂ + χu`. -/
theorem prod_change (b₁ u₁ : M₁ →ₗ[R] L₁) (b₂ u₂ : M₂ →ₗ[R] L₂) :
    TensorProduct.map (b₁ + χ • u₁) (b₂ + χ • u₂)
      = TensorProduct.map b₁ b₂ + χ • uProd χ b₁ u₁ b₂ u₂ := by
  simp only [uProd, TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_add]
  abel

/-- **Page 131, the cocycle relation `u″ = u + u′`.** Two successive changes,
`uᵢ` then `u′ᵢ` (the second computed with `b′ᵢ = bᵢ + χuᵢ`), compose to the
change `uᵢ + u′ᵢ`. -/
theorem uProd_cocycle (b₁ u₁ u₁' : M₁ →ₗ[R] L₁) (b₂ u₂ u₂' : M₂ →ₗ[R] L₂) :
    uProd χ b₁ u₁ b₂ u₂ + uProd χ (b₁ + χ • u₁) u₁' (b₂ + χ • u₂) u₂'
      = uProd χ b₁ (u₁ + u₁') b₂ (u₂ + u₂') := by
  simp only [uProd, TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_add]
  abel

/-- **Page 78, commutativity.** Under `M₁ ⊗ M₂ ≅ M₂ ⊗ M₁` and
`L₁ ⊗ L₂ ≅ L₂ ⊗ L₁`, `b₁ ⊗ b₂` is `b₂ ⊗ b₁`. -/
theorem prod_comm (b₁ : M₁ →ₗ[R] L₁) (b₂ : M₂ →ₗ[R] L₂) :
    (TensorProduct.comm R L₁ L₂).toLinearMap ∘ₗ TensorProduct.map b₁ b₂
      = TensorProduct.map b₂ b₁ ∘ₗ (TensorProduct.comm R M₁ M₂).toLinearMap :=
  (TensorProduct.map_comp_comm_eq b₂ b₁).symm

/-- **Page 78, associativity.** -/
theorem prod_assoc (b₁ : M₁ →ₗ[R] L₁) (b₂ : M₂ →ₗ[R] L₂) (b₃ : M₃ →ₗ[R] L₃) :
    (TensorProduct.assoc R L₁ L₂ L₃).toLinearMap ∘ₗ TensorProduct.map (TensorProduct.map b₁ b₂) b₃
      = TensorProduct.map b₁ (TensorProduct.map b₂ b₃) ∘ₗ
          (TensorProduct.assoc R M₁ M₂ M₃).toLinearMap :=
  (TensorProduct.map_map_comp_assoc_eq b₁ b₂ b₃).symm

/-- **Page 78, unit.** The unit object is `M = L = R` with `b = id`
(`π(u, λ) = λ + χu`); under `R ⊗ M ≅ M`, `R ⊗ L ≅ L`, `id ⊗ b` is `b`. -/
theorem prod_unit (b : M →ₗ[R] L) :
    (TensorProduct.lid R L).toLinearMap ∘ₗ TensorProduct.map LinearMap.id b
      = b ∘ₗ (TensorProduct.lid R M).toLinearMap := by
  ext; simp

/-! ### `M = L = R`: the monoid of classes and its units -/

/-- Two scalar data `b`, `b'` (for `M = L = R`) give isomorphic objects, allowing
an automorphism `ε` of `L = R`: `εb ≡ b' (mod χ)`. -/
def ChiRel (b b' : R) : Prop := ∃ (ε : Rˣ) (w : R), ε * b = b' + χ * w

/-- The product `b = b₁b₂` is compatible with the relation. -/
theorem chiRel_mul {b₁ b₁' b₂ b₂' : R} (h₁ : ChiRel χ b₁ b₁') (h₂ : ChiRel χ b₂ b₂') :
    ChiRel χ (b₁ * b₂) (b₁' * b₂') := by
  obtain ⟨ε₁, w₁, e₁⟩ := h₁
  obtain ⟨ε₂, w₂, e₂⟩ := h₂
  refine ⟨ε₁ * ε₂, b₁' * w₂ + w₁ * b₂' + χ * w₁ * w₂, ?_⟩
  push_cast
  linear_combination (ε₂ * b₂) * e₁ + (b₁' + χ * w₁) * e₂

/-- **Page 79, the invertibility criterion, for `L = 𝒪` trivial.** The class of
`b` is invertible for the product (`bb' ≡ ε (mod χ)` for some `b'`) iff
`T₀ = −b₀` generates `L₀ = R/χR` on `V(χ)`, that is iff `b` and `χ` generate the
unit ideal. -/
theorem invertible_iff (b : R) :
    (∃ b', ChiRel χ (b * b') 1) ↔ Ideal.span {b, χ} = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  constructor
  · rintro ⟨b', ε, w, e⟩
    exact ⟨ε * b', -w, by linear_combination e⟩
  · rintro ⟨g, h, e⟩
    exact ⟨g, 1, -h, by simp; linear_combination e⟩

/-- The same criterion, as the page states it: `b` is a unit in `R/χR`. -/
theorem span_eq_top_iff_isUnit (b : R) :
    Ideal.span {b, χ} = ⊤ ↔ IsUnit (Ideal.Quotient.mk (Ideal.span {χ}) b) := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair, isUnit_iff_exists_inv]
  constructor
  · rintro ⟨g, h, e⟩
    refine ⟨Ideal.Quotient.mk _ g, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨-h, by linear_combination e⟩
  · rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨g, -k, by linear_combination hk⟩

/-! ### Pushout and pullback products (pages 125, 127, 167 and 169) -/

/-- **Pages 125 and 127.** In coordinates the pullback product carries the
scindage `−b`, `b = b₁ ⊗ b₂`. If `γχ = 2`, the transvection `T_{γb}` carries the
pushout scindage `b` to the pullback scindage `−b`. -/
theorem push_pull {γ : R} (hγ : γ * χ = 2) (b : M →ₗ[R] L) :
    piOf χ (-b) ∘ₗ transv (γ • b) = piOf χ b := by
  rw [piOf_comp_transv, smul_smul, mul_comm, hγ, two_smul]
  congr 1; abel

/-- **Page 125, « commute ! ».** The comparison `T_{γb}` is compatible with the
changes of scindage: for `b ↦ b + χu` on the pushout side and `−b ↦ −b − χu` on
the pullback side, `T_{γb} ∘ T_u = T_{−u} ∘ T_{γ(b + χu)}`. -/
theorem push_pull_square {γ : R} (hγ : γ * χ = 2) (b u : M →ₗ[R] L) :
    transv (γ • b) ∘ₗ transv u = transv (-u) ∘ₗ transv (γ • (b + χ • u)) := by
  rw [transv_comp, transv_comp, smul_add, smul_smul, hγ, two_smul]
  congr 1; abel

/-- The hypothesis `γχ = 2` is necessary: for the unit objects (`M = L = R`,
`b₁ = b₂ = id`, so `b = id`), an isomorphism from the pushout to the pullback
inducing the identity on `L` and `M` exists iff `2 ∈ χR`. -/
theorem push_pull_unit_iff :
    (∃ f : R × R →ₗ[R] R × R, LinearMap.fst R R R ∘ₗ f = LinearMap.fst R R R ∧
        f ∘ₗ LinearMap.inr R R R = LinearMap.inr R R R ∧
        piOf χ (-LinearMap.id) ∘ₗ f = piOf χ LinearMap.id) ↔ ∃ γ : R, γ * χ = 2 := by
  rw [iso_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w 1, ?_⟩
    have := LinearMap.congr_fun hw 1
    simp at this
    linear_combination -this
  · rintro ⟨γ, hγ⟩
    refine ⟨γ • LinearMap.id, ?_⟩
    rw [smul_smul, mul_comm, hγ, two_smul]
    abel

/-- Over `ℤ` with `χ = 4`, there is no such `γ`. -/
theorem no_gamma_four : ¬ ∃ γ : ℤ, γ * 4 = 2 := by
  rintro ⟨γ, h⟩; omega

end ChiSplit

/-! ## The theorem of page 48 with `L` invertible, over an affine base

Finding `84-two-regular-triplet-classification`, the case `L` not trivial. Over
an affine base `Spec R` the reading's quadratic cover is, by page 45, a triple
`(L, P₁, Q)`: `L` invertible, `P₁` an `L`-torsor (trivial on an affine base, so
`P₁ = L` once an origin `x₀` is chosen) and `Q(x₀ + u) = u² + bu + c` with
`b ∈ L`, `c ∈ L^{⊗2}`. A morphism is `φ : L ≅ L'` with a map of torsors
`x₀ + u ↦ x'₀ + t + φ(u)` carrying `Q` to `Q'` (`IsCoverHom`). The triplet is
`(L, δ, T₀)` with `δ = b² − 4c ∈ L^{⊗2}` (`discL`) and `T₀ = b mod 2L` in
`L/2L = Γ(V(2), L₀)`; `T₀² ≡ δ (mod 4)` is `TripletCond`.

* `isCoverHom_iff`: morphisms in coordinates, `φ(b) = b' + 2t`,
  `φ(c) = c' + b't + t²`, any `R`; `isCoverHom_refl`, `isCoverHom_trans`,
  `isCoverHom_symm`: a groupoid;
* `tripletCond_iff_forall` (page 47, `L` invertible): the congruence does not
  depend on the lift; `tripletCond_discL` and `isCoverHom_triplet`: the functor,
  any `R`;
* `triplet_full_faithful`, `triplet_ess_surj`, `triplet_classification` and
  `cover_iso_iff_triplet_iso`: if `2` is a non-zero-divisor in `R`, the functor
  is fully faithful (each triplet isomorphism lifts to exactly one morphism) and
  essentially surjective (any `R`): page 48 for every invertible `L`.

Symmetry of `L ⊗ L` (`Module.Invertible.tmul_comm`) is used for `b·u = u·b`;
`2` regular on `L ⊗ L` follows from projectivity
(`two_smul_injective_of_projective`). Not formalised: that `(L, P₁, Q)` is the
same as a quadratic algebra (page 45), non-affine bases, base change, and the
reconstruction of `E`, `A`, trace, norm and product of pages 49 to 52. -/
section Triplets

variable {R : Type*} [CommRing R]
variable {L L' L'' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
  [AddCommGroup L''] [Module R L'']

/-- If `2` is regular in `R`, it is regular on every projective `R`-module, in
particular on `L` and on `L ⊗ L` for `L` invertible. -/
theorem two_smul_injective_of_projective (h2 : ∀ x : R, 2 * x = 0 → x = 0)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M] {x : M}
    (hx : (2 : R) • x = 0) : x = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def.1 (inferInstance : Module.Projective R M)
  have h0 : s x = 0 := by
    have e : (2 : R) • s x = 0 := by rw [← map_smul, hx, map_zero]
    ext i
    exact h2 _ (by simpa using congrArg (· i) e)
  rw [← hs x, h0, map_zero]

lemma four_smul_injective (h2 : ∀ x : R, 2 * x = 0 → x = 0)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M] {x y : M}
    (h : (4 : R) • x = (4 : R) • y) : x = y := by
  rw [← sub_eq_zero]
  apply two_smul_injective_of_projective h2
  apply two_smul_injective_of_projective h2
  rw [smul_smul, smul_sub, show (2 : R) * 2 = 4 by norm_num, h, sub_self]

/-- For `L` invertible, `x ⊗ w = 0` for every `w` forces `x = 0`. -/
theorem eq_zero_of_tmul_eq_zero [Module.Invertible R L] {x : L}
    (h : ∀ w : L, x ⊗ₜ[R] w = 0) : x = 0 := by
  obtain ⟨z, hz⟩ := (Module.Invertible.bijective (R := R) (M := L)).2 1
  let F : Module.Dual R L ⊗[R] L →ₗ[R] L := (contractLeft R L).smulRight x
  have hF : F = 0 := by
    apply TensorProduct.ext'
    intro γ w
    have e := congrArg (fun y => TensorProduct.rid R L (LinearMap.lTensor L γ y)) (h w)
    simp only [LinearMap.lTensor_tmul, rid_tmul, map_zero] at e
    simpa [F] using e
  have : F z = x := by simp [F, hz]
  rw [← this, hF, LinearMap.zero_apply]

/-- `2L`, the submodule whose quotient `L/2L` is `Γ(V(2), L₀)` over an affine base. -/
def twoL (R L : Type*) [CommRing R] [AddCommGroup L] [Module R L] : Submodule R L :=
  LinearMap.range (LinearMap.lsmul R L (2 : R))

lemma mem_twoL {x : L} : x ∈ twoL R L ↔ ∃ t, (2 : R) • t = x := by
  simp [twoL]

lemma twoL_le_comap (φ : L →ₗ[R] L') : twoL R L ≤ (twoL R L').comap φ := by
  rintro x hx
  obtain ⟨t, rfl⟩ := mem_twoL.1 hx
  exact mem_twoL.2 ⟨φ t, by simp⟩

/-- The map `L/2L → L'/2L'` induced by `φ`, that is `φ₀ : L₀ → L'₀` on `V(2)`. -/
def mod2 (φ : L →ₗ[R] L') : L ⧸ twoL R L →ₗ[R] L' ⧸ twoL R L' :=
  (twoL R L).mapQ (twoL R L') φ (twoL_le_comap φ)

@[simp] lemma mod2_mk (φ : L →ₗ[R] L') (x : L) :
    mod2 φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ x) := rfl

/-- The quadratic function `Q(x₀ + u) = u² + bu + c` of page 45 on the torsor
`P₁ = L` with origin `x₀`, with values in `L^{⊗2}`; `b = 2x₀ − T`. -/
def qform (b : L) (c : L ⊗[R] L) (u : L) : L ⊗[R] L := u ⊗ₜ u + b ⊗ₜ u + c

/-- A morphism of quadratic covers `(L, P₁, Q) → (L', P'₁, Q')`, the torsors
trivialised (an affine base): `φ : L ≅ L'` and the map of torsors
`x₀ + u ↦ x'₀ + t + φ(u)`, carrying `Q` to `Q'`. -/
def IsCoverHom (b : L) (c : L ⊗[R] L) (b' : L') (c' : L' ⊗[R] L') (φ : L ≃ₗ[R] L') (t : L') :
    Prop :=
  ∀ u : L, qform b' c' (t + φ u) = TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (qform b c u)

lemma map_tmul' (φ : L ≃ₗ[R] L') (x y : L) :
    TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (x ⊗ₜ y) = φ x ⊗ₜ φ y := rfl

/-- **Morphisms in coordinates.** For `L'` invertible, `(φ, t)` is a morphism iff
`φ(b) = b' + 2t` and `φ(c) = c' + b't + t²`, over any base. -/
theorem isCoverHom_iff [Module.Invertible R L'] (b : L) (c : L ⊗[R] L) (b' : L')
    (c' : L' ⊗[R] L') (φ : L ≃ₗ[R] L') (t : L') :
    IsCoverHom b c b' c' φ t ↔
      φ b = b' + (2 : R) • t ∧
        TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') c = c' + b' ⊗ₜ t + t ⊗ₜ t := by
  constructor
  · intro h
    have h0 := h 0
    simp only [qform, map_zero, add_zero, tmul_zero, zero_add] at h0
    refine ⟨?_, by rw [← h0]; abel⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_tmul_eq_zero (R := R)
    intro w
    have hu := h (φ.symm w)
    simp only [qform, map_add, LinearEquiv.apply_symm_apply, map_tmul', add_tmul, tmul_add,
      ← h0] at hu
    rw [Module.Invertible.tmul_comm (m₁ := w) (m₂ := t)] at hu
    rw [sub_tmul, sub_eq_zero, add_tmul, two_smul, add_tmul]
    linear_combination (norm := module) -hu
  · rintro ⟨hb, hc⟩ u
    simp only [qform, map_add, map_tmul', hb, hc, add_tmul, tmul_add, two_smul]
    rw [Module.Invertible.tmul_comm (m₁ := φ u) (m₂ := t)]
    abel

/-- The identity is a morphism, and morphisms compose: `(ψ, s) ∘ (φ, t) = (ψφ, s + ψ(t))`.
The quadratic covers with `L` invertible over `R` form a groupoid. -/
theorem isCoverHom_refl (b : L) (c : L ⊗[R] L) : IsCoverHom b c b c (LinearEquiv.refl R L) 0 :=
  fun u => by simp [TensorProduct.map_id]

theorem isCoverHom_trans {b : L} {c : L ⊗[R] L} {b' : L'} {c' : L' ⊗[R] L'} {b'' : L''}
    {c'' : L'' ⊗[R] L''} {φ : L ≃ₗ[R] L'} {ψ : L' ≃ₗ[R] L''} {t : L'} {s : L''}
    (h : IsCoverHom b c b' c' φ t) (h' : IsCoverHom b' c' b'' c'' ψ s) :
    IsCoverHom b c b'' c'' (φ.trans ψ) (s + ψ t) := by
  intro u
  have e : s + ψ t + (φ.trans ψ) u = s + ψ (t + φ u) := by simp [add_assoc]
  rw [e, h', h, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

/-- The inverse of a morphism: `(φ, t)⁻¹ = (φ⁻¹, −φ⁻¹(t))`. -/
theorem isCoverHom_symm {b : L} {c : L ⊗[R] L} {b' : L'} {c' : L' ⊗[R] L'} {φ : L ≃ₗ[R] L'}
    {t : L'} (h : IsCoverHom b c b' c' φ t) : IsCoverHom b' c' b c φ.symm (-φ.symm t) := by
  intro u
  have e := h (-φ.symm t + φ.symm u)
  simp only [map_add, map_neg, LinearEquiv.apply_symm_apply, add_neg_cancel_left] at e
  have hinv : TensorProduct.map (φ.symm : L' →ₗ[R] L) (φ.symm : L' →ₗ[R] L)
      (TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (qform b c (-φ.symm t + φ.symm u)))
        = qform b c (-φ.symm t + φ.symm u) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp [TensorProduct.map_id]
  rw [← hinv, ← e]

/-- The discriminant `δ = b² − 4c = T² − 4N`, a section of `L^{⊗2}`. -/
def discL (b : L) (c : L ⊗[R] L) : L ⊗[R] L := b ⊗ₜ b - (4 : R) • c

/-- The triplet condition of page 47, `T₀² ≡ δ (mod 4)`: some lift `τ ∈ L` of
`T₀ ∈ L/2L` has `τ² − δ ∈ 4L^{⊗2}`. -/
def TripletCond (δ : L ⊗[R] L) (T₀ : L ⧸ twoL R L) : Prop :=
  ∃ τ : L, Submodule.Quotient.mk τ = T₀ ∧ ∃ k : L ⊗[R] L, τ ⊗ₜ τ - δ = (4 : R) • k

/-- Page 47: for `L` invertible the condition does not depend on the lift,
`(τ + 2a)² ≡ τ² (mod 4)`. -/
theorem tripletCond_iff_forall [Module.Invertible R L] (δ : L ⊗[R] L) (T₀ : L ⧸ twoL R L) :
    TripletCond δ T₀ ↔
      (∃ τ : L, Submodule.Quotient.mk τ = T₀) ∧
        ∀ τ : L, Submodule.Quotient.mk τ = T₀ → ∃ k : L ⊗[R] L, τ ⊗ₜ τ - δ = (4 : R) • k := by
  constructor
  · rintro ⟨τ, hτ, k, hk⟩
    refine ⟨⟨τ, hτ⟩, fun τ' hτ' => ?_⟩
    rw [← hτ', Submodule.Quotient.eq] at hτ
    obtain ⟨a, ha⟩ := mem_twoL.1 hτ
    have e : τ' = τ - (2 : R) • a := by rw [ha]; abel
    refine ⟨k - τ ⊗ₜ a + a ⊗ₜ a, ?_⟩
    rw [e]
    simp only [sub_tmul, tmul_sub, ← smul_tmul', tmul_smul, smul_sub]
    rw [Module.Invertible.tmul_comm (m₁ := a) (m₂ := τ)]
    rw [sub_eq_iff_eq_add] at hk
    rw [hk]
    module
  · rintro ⟨⟨τ, hτ⟩, h⟩; exact ⟨τ, hτ, h τ hτ⟩

/-- **The functor on objects** (page 47): `(L, b, c) ↦ (L, δ, T₀)` with `T₀ = b mod 2`
satisfies `T₀² ≡ δ (mod 4)`, over any base. -/
theorem tripletCond_discL (b : L) (c : L ⊗[R] L) :
    TripletCond (discL b c) (Submodule.Quotient.mk b) :=
  ⟨b, rfl, c, by simp [discL]⟩

/-- **The functor on morphisms**, over any base: a morphism `(φ, t)` of quadratic
covers carries `δ` to `δ'` and `T₀` to `T'₀`. -/
theorem isCoverHom_triplet [Module.Invertible R L'] {b : L} {c : L ⊗[R] L} {b' : L'}
    {c' : L' ⊗[R] L'} {φ : L ≃ₗ[R] L'} {t : L'} (h : IsCoverHom b c b' c' φ t) :
    TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (discL b c) = discL b' c' ∧
      mod2 (φ : L →ₗ[R] L') (Submodule.Quotient.mk b) = Submodule.Quotient.mk b' := by
  obtain ⟨hb, hc⟩ := (isCoverHom_iff b c b' c' φ t).1 h
  constructor
  · simp only [discL, map_sub, map_smul, map_tmul', hb, hc, add_tmul, tmul_add, ← smul_tmul',
      tmul_smul]
    rw [Module.Invertible.tmul_comm (m₁ := t) (m₂ := b')]
    module
  · rw [mod2_mk, LinearEquiv.coe_coe, hb, Submodule.Quotient.eq]
    exact mem_twoL.2 ⟨t, by abel⟩

/-- **Full faithfulness** (page 48). If `2` is a non-zero-divisor in `R` and `L`, `L'`
are invertible, every isomorphism `φ : L ≅ L'` of triplets (`φ(δ) = δ'`,
`φ₀(T₀) = T'₀`) lifts to exactly one morphism `(φ, t)` of quadratic covers. -/
theorem triplet_full_faithful (h2 : ∀ x : R, 2 * x = 0 → x = 0)
    [Module.Invertible R L'] (b : L) (c : L ⊗[R] L) (b' : L') (c' : L' ⊗[R] L')
    (φ : L ≃ₗ[R] L')
    (hδ : TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (discL b c) = discL b' c')
    (hT : mod2 (φ : L →ₗ[R] L') (Submodule.Quotient.mk b) = Submodule.Quotient.mk b') :
    ∃! t : L', IsCoverHom b c b' c' φ t := by
  rw [mod2_mk, LinearEquiv.coe_coe, Submodule.Quotient.eq] at hT
  obtain ⟨t, ht⟩ := mem_twoL.1 hT
  have hb : φ b = b' + (2 : R) • t := by rw [ht]; abel
  refine ⟨t, (isCoverHom_iff b c b' c' φ t).2 ⟨hb, ?_⟩, ?_⟩
  · apply four_smul_injective h2
    have e : (4 : R) • TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') c
        = φ b ⊗ₜ φ b - discL b' c' := by
      rw [← hδ]; simp only [discL, map_sub, map_smul, map_tmul']; abel
    rw [e, hb]
    simp only [discL, add_tmul, tmul_add, ← smul_tmul', tmul_smul]
    rw [Module.Invertible.tmul_comm (m₁ := t) (m₂ := b')]
    module
  · intro t' h'
    obtain ⟨hb', -⟩ := (isCoverHom_iff b c b' c' φ t').1 h'
    rw [← sub_eq_zero]
    apply two_smul_injective_of_projective h2
    rw [smul_sub, sub_eq_zero]
    exact add_left_cancel (hb'.symm.trans hb)

/-- **Essential surjectivity** (page 48), over any base: every triplet `(L, δ, T₀)`
with `T₀² ≡ δ (mod 4)` comes from a quadratic cover on the same `L`, namely
`b = τ`, `c = (τ² − δ)/4` for a lift `τ` of `T₀`. -/
theorem triplet_ess_surj (δ : L ⊗[R] L) (T₀ : L ⧸ twoL R L) (h : TripletCond δ T₀) :
    ∃ (b : L) (c : L ⊗[R] L), discL b c = δ ∧ Submodule.Quotient.mk b = T₀ := by
  obtain ⟨τ, hτ, k, hk⟩ := h
  exact ⟨τ, k, by rw [discL, ← hk]; abel, hτ⟩

/-- **Théorème (page 48), `L` invertible, over an affine base.** If `2` is a
non-zero-divisor in `R`, then for invertible `L`, `L'` and an isomorphism
`φ : L ≅ L'`, the morphisms `(φ, t)` of quadratic covers `(L, b, c) → (L', b', c')`
exist iff `φ` is an isomorphism of triplets, and are then unique; every triplet
occurs. Together: the groupoid of quadratic covers is equivalent, by
`(L, b, c) ↦ (L, δ, T₀)`, to the groupoid of triplets. -/
theorem triplet_classification (h2 : ∀ x : R, 2 * x = 0 → x = 0)
    [Module.Invertible R L'] (b : L) (c : L ⊗[R] L) (b' : L') (c' : L' ⊗[R] L')
    (φ : L ≃ₗ[R] L') :
    (∃ t : L', IsCoverHom b c b' c' φ t) ↔
      TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (discL b c) = discL b' c' ∧
        mod2 (φ : L →ₗ[R] L') (Submodule.Quotient.mk b) = Submodule.Quotient.mk b' := by
  exact ⟨fun ⟨_, h⟩ => isCoverHom_triplet h,
    fun ⟨hδ, hT⟩ => (triplet_full_faithful h2 b c b' c' φ hδ hT).exists⟩

/-- On isomorphism classes: two quadratic covers with `L`, `L'` invertible are
isomorphic iff their triplets are. -/
theorem cover_iso_iff_triplet_iso (h2 : ∀ x : R, 2 * x = 0 → x = 0)
    [Module.Invertible R L'] (b : L) (c : L ⊗[R] L) (b' : L') (c' : L' ⊗[R] L') :
    (∃ (φ : L ≃ₗ[R] L') (t : L'), IsCoverHom b c b' c' φ t) ↔
      ∃ φ : L ≃ₗ[R] L',
        TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') (discL b c) = discL b' c' ∧
          mod2 (φ : L →ₗ[R] L') (Submodule.Quotient.mk b) = Submodule.Quotient.mk b' := by
  simp only [← triplet_classification h2]

end Triplets

end Grothendieck.Folder84

/-! ## The symmetric monoidal category of `χ`-split extensions (pages 65 to 79)

Continuation of the `χ`-split coordinates above, for finding
`84-chi-trivialised-extension-product`. An object is a split extension
`0 → L → M ⊕ L → M → 0` with the `χ`-scindage of `b : M → L` (`ChiExt`); a morphism is a map
of extensions compatible with the scindages, recorded as `(f, φ, w)` with
`φ ∘ b = b' ∘ f + χ w` (`extMap`, `eq_extMap`, `extMap_pi_iff`, `extMap_varpi_iff`). The
product is `b₁ ⊗ b₂` (page 78), that of morphisms carries the datum `u` of page 129. Over
any commutative ring, without dividing by `χ` or `2`:

* `ChiExt.instMonoidalCategory`, `ChiExt.instSymmetricCategory`: a symmetric monoidal
  category (all coherence axioms checked by Lean);
* `ChiExt.isIso_of`: a morphism is invertible as soon as it is on `M` and on `L`;
* `ChiExt.invertible_iff_generates` (page 79, for any `L`): `(𝒪, L, b)` is invertible iff
  `L` is an invertible module and `b` generates `L` modulo `χ`; `generates_iff_span` is the
  form « `T₀` generates `L₀` on `V(χ)` », used in `ChiExt.invertible_iff_span`.

The intrinsic product by amalgamated sum for a non-split extension (pages 68 to 70), the
universal property of bi-affine maps (pages 75 and 76) and the passage from an affine base
to a scheme are not formalised.
-/

open CategoryTheory MonoidalCategory TensorProduct

namespace Grothendieck.Folder84

section ChiCategory

variable {R : Type u} [CommRing R]

section ExtMap

variable (χ : R) {M L M' L' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup L]
  [Module R L] [AddCommGroup M'] [Module R M'] [AddCommGroup L'] [Module R L']

/-- The map `(η, ξ) ↦ (f η, φ ξ + w η)` of `M ⊕ L → M' ⊕ L'`. -/
def extMap (f : M →ₗ[R] M') (φ : L →ₗ[R] L') (w : M →ₗ[R] L') : M × L →ₗ[R] M' × L' :=
  LinearMap.prod (f ∘ₗ LinearMap.fst R M L) (φ ∘ₗ LinearMap.snd R M L + w ∘ₗ LinearMap.fst R M L)

/-- Every map of split extensions inducing `f` on `M` and `φ` on `L` is an `extMap`. -/
theorem eq_extMap (F : M × L →ₗ[R] M' × L') (f : M →ₗ[R] M') (φ : L →ₗ[R] L')
    (h₁ : LinearMap.fst R M' L' ∘ₗ F = f ∘ₗ LinearMap.fst R M L)
    (h₂ : F ∘ₗ LinearMap.inr R M L = LinearMap.inr R M' L' ∘ₗ φ) :
    F = extMap f φ (LinearMap.snd R M' L' ∘ₗ F ∘ₗ LinearMap.inl R M L) := by
  apply LinearMap.prod_ext
  · ext η
    · simpa [extMap] using LinearMap.congr_fun h₁ (η, 0)
    · simp [extMap]
  · ext ξ
    · simpa [extMap] using congrArg Prod.fst (LinearMap.congr_fun h₂ ξ)
    · simpa [extMap, Prod.mk_zero_zero] using congrArg Prod.snd (LinearMap.congr_fun h₂ ξ)

/-- A map of extensions respects the `χ`-retractions iff `φ ∘ b = b' ∘ f + χw`. -/
theorem extMap_pi_iff (b : M →ₗ[R] L) (b' : M' →ₗ[R] L') (f : M →ₗ[R] M') (φ : L →ₗ[R] L')
    (w : M →ₗ[R] L') :
    piOf χ b' ∘ₗ extMap f φ w = φ ∘ₗ piOf χ b ↔ φ ∘ₗ b = b' ∘ₗ f + χ • w := by
  constructor
  · intro h
    ext η
    simpa [piOf, extMap] using (LinearMap.congr_fun h (η, 0)).symm
  · intro h
    apply LinearMap.prod_ext
    · ext η
      simpa [piOf, extMap] using (LinearMap.congr_fun h η).symm
    · ext ξ
      simp [piOf, extMap]

/-- A map of extensions respects the `χ`-sections iff `φ ∘ b = b' ∘ f + χw`. -/
theorem extMap_varpi_iff (b : M →ₗ[R] L) (b' : M' →ₗ[R] L') (f : M →ₗ[R] M') (φ : L →ₗ[R] L')
    (w : M →ₗ[R] L') :
    extMap f φ w ∘ₗ varpiOf χ b = varpiOf χ b' ∘ₗ f ↔ φ ∘ₗ b = b' ∘ₗ f + χ • w := by
  constructor
  · intro h
    ext η
    have := congrArg Prod.snd (LinearMap.congr_fun h η)
    simp [extMap, varpiOf] at this
    simp
    linear_combination (norm := module) -this
  · intro h
    ext η
    · simp [extMap, varpiOf]
    · have := LinearMap.congr_fun h η
      simp at this
      simp [extMap, varpiOf, this]

open scoped Pointwise in
/-- `b` generates `L` modulo `χ` iff its class generates `L/χL`. -/
theorem generates_iff_span (b : L) :
    (∀ x : L, ∃ (r : R) (y : L), x = r • b + χ • y) ↔
      Submodule.span R {Submodule.Quotient.mk (p := χ • (⊤ : Submodule R L)) b} = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨r, y, rfl⟩ := h x
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    simpa using Submodule.smul_mem_pointwise_smul y χ ⊤ trivial
  · intro h x
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (h ▸ Submodule.mem_top :
      Submodule.Quotient.mk (p := χ • (⊤ : Submodule R L)) x ∈ _)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hr
    obtain ⟨y, -, hy⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp
      (Submodule.neg_mem _ hr)
    exact ⟨r, y, by rw [hy]; abel⟩
end ExtMap

/-- A split extension `0 → L → M ⊕ L → M → 0` with the `χ`-scindage of `b : M → L`,
`π(η, ξ) = b(η) + χξ`, `ϖ(η) = (χη, −b(η))` (`piOf`, `varpiOf`; every `χ`-scindage of a
split extension is of this form, `chiSplitting_eq`). -/
structure ChiExt (χ : R) where
  M : ModuleCat.{u} R
  L : ModuleCat.{u} R
  b : M ⟶ L

/-- Scalars pass through `⊗ₘ` in `ModuleCat` (left factor). -/
lemma smul_tensorHom' {A B C D : ModuleCat.{u} R} (r : R) (f : A ⟶ B) (g : C ⟶ D) :
    (r • f) ⊗ₘ g = r • (f ⊗ₘ g) :=
  ModuleCat.MonoidalCategory.tensor_ext fun x y => by
    simp [ModuleCat.MonoidalCategory.tensorHom_tmul]; rw [TensorProduct.smul_tmul']

/-- Scalars pass through `⊗ₘ` in `ModuleCat` (right factor). -/
lemma tensorHom_smul' {A B C D : ModuleCat.{u} R} (r : R) (f : A ⟶ B) (g : C ⟶ D) :
    f ⊗ₘ (r • g) = r • (f ⊗ₘ g) :=
  ModuleCat.MonoidalCategory.tensor_ext fun x y => by
    simp [ModuleCat.MonoidalCategory.tensorHom_tmul, TensorProduct.tmul_smul]

namespace ChiExt
variable {χ : R}

/-- A morphism `(M, L, b) → (M', L', b')`: the map `(η, ξ) ↦ (f η, φ ξ + w η)` of
`M ⊕ L → M' ⊕ L'` (a map of extensions inducing `f` on `M` and `φ` on `L`), compatible
with the `χ`-scindages: `φ ∘ b = b' ∘ f + χ w` (`extMap_pi_iff`, `extMap_varpi_iff`). -/
@[ext]
structure Hom (X Y : ChiExt χ) where
  f : X.M ⟶ Y.M
  φ : X.L ⟶ Y.L
  w : X.M ⟶ Y.L
  comm : X.b ≫ φ = f ≫ Y.b + χ • w

/-- Composition: `(f, φ, w)` then `(g, ψ, v)` is `(gf, ψφ, ψw + vf)`. -/
instance : Category (ChiExt χ) where
  Hom := Hom
  id X := ⟨𝟙 _, 𝟙 _, 0, by simp⟩
  comp p q := ⟨p.f ≫ q.f, p.φ ≫ q.φ, p.w ≫ q.φ + p.f ≫ q.w, by
    rw [← Category.assoc, p.comm, Preadditive.add_comp, Category.assoc, q.comm]
    simp only [Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul, smul_add, Category.assoc]
    abel⟩
  assoc p q r := by
    refine Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _) ?_
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]; abel

@[ext]
lemma hom_ext {X Y : ChiExt χ} {p q : X ⟶ Y} (h₁ : p.f = q.f) (h₂ : p.φ = q.φ)
    (h₃ : p.w = q.w) : p = q := Hom.ext h₁ h₂ h₃

@[simp] lemma id_f (X : ChiExt χ) : Hom.f (𝟙 X) = 𝟙 _ := rfl
@[simp] lemma id_φ (X : ChiExt χ) : Hom.φ (𝟙 X) = 𝟙 _ := rfl
@[simp] lemma id_w (X : ChiExt χ) : Hom.w (𝟙 X) = 0 := rfl
@[simp] lemma comp_f {X Y Z : ChiExt χ} (p : X ⟶ Y) (q : Y ⟶ Z) :
    (p ≫ q).f = p.f ≫ q.f := rfl
@[simp] lemma comp_φ {X Y Z : ChiExt χ} (p : X ⟶ Y) (q : Y ⟶ Z) :
    (p ≫ q).φ = p.φ ≫ q.φ := rfl
@[simp] lemma comp_w {X Y Z : ChiExt χ} (p : X ⟶ Y) (q : Y ⟶ Z) :
    (p ≫ q).w = p.w ≫ q.φ + p.f ≫ q.w := rfl

/-- Page 78: the product of `(M₁, L₁, b₁)` and `(M₂, L₂, b₂)` is
`(M₁ ⊗ M₂, L₁ ⊗ L₂, b₁ ⊗ b₂)`, « Il n'y a pas plus simple ! ». -/
abbrev tensorObj (X Y : ChiExt χ) : ChiExt χ := ⟨X.M ⊗ Y.M, X.L ⊗ Y.L, X.b ⊗ₘ Y.b⟩

/-- The product of morphisms (page 129): `w = b′₁f₁ ⊗ w₂ + w₁ ⊗ b′₂f₂ + χ w₁ ⊗ w₂`. -/
def tensorHom {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X' Y' :=
  ⟨p.f ⊗ₘ q.f, p.φ ⊗ₘ q.φ, (p.f ≫ X'.b) ⊗ₘ q.w + p.w ⊗ₘ (q.f ≫ Y'.b) + χ • (p.w ⊗ₘ q.w), by
    change (X.b ⊗ₘ Y.b) ≫ _ = (p.f ⊗ₘ q.f) ≫ (X'.b ⊗ₘ Y'.b) + _
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, p.comm, q.comm]
    simp only [MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add,
      smul_tensorHom', tensorHom_smul', smul_add, smul_smul]
    abel⟩

@[simp] lemma tensorHom_f {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    (tensorHom p q).f = p.f ⊗ₘ q.f := rfl
@[simp] lemma tensorHom_φ {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    (tensorHom p q).φ = p.φ ⊗ₘ q.φ := rfl
@[simp] lemma tensorHom_w {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    (tensorHom p q).w = (p.f ≫ X'.b) ⊗ₘ q.w + p.w ⊗ₘ (q.f ≫ Y'.b) + χ • (p.w ⊗ₘ q.w) := rfl

/-- An isomorphism of underlying `M` and `L` commuting strictly with `b` (`w = 0`). -/
@[simps]
def strictIso {X Y : ChiExt χ} (eM : X.M ≅ Y.M) (eL : X.L ≅ Y.L)
    (h : X.b ≫ eL.hom = eM.hom ≫ Y.b) : X ≅ Y where
  hom := ⟨eM.hom, eL.hom, 0, by simp [h]⟩
  inv := ⟨eM.inv, eL.inv, 0, by
    rw [smul_zero, add_zero, Iso.eq_inv_comp, ← Category.assoc, ← h]; simp⟩
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

instance : MonoidalCategoryStruct (ChiExt χ) where
  tensorObj := tensorObj
  whiskerLeft X _ _ q := tensorHom (𝟙 X) q
  whiskerRight p Y := tensorHom p (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := ⟨𝟙_ _, 𝟙_ _, 𝟙 _⟩
  associator X Y Z := strictIso (α_ X.M Y.M Z.M) (α_ X.L Y.L Z.L) (by simp)
  leftUnitor X := strictIso (λ_ X.M) (λ_ X.L) (by simp)
  rightUnitor X := strictIso (ρ_ X.M) (ρ_ X.L) (by simp)

@[simp] lemma tensorHom_f' {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    (p ⊗ₘ q).f = p.f ⊗ₘ q.f := rfl
@[simp] lemma tensorHom_φ' {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    (p ⊗ₘ q).φ = p.φ ⊗ₘ q.φ := rfl
@[simp] lemma tensorHom_w' {X X' Y Y' : ChiExt χ} (p : X ⟶ X') (q : Y ⟶ Y') :
    (p ⊗ₘ q).w = (p.f ≫ X'.b) ⊗ₘ q.w + p.w ⊗ₘ (q.f ≫ Y'.b) + χ • (p.w ⊗ₘ q.w) := rfl
@[simp] lemma tensorObj_M (X Y : ChiExt χ) : (X ⊗ Y).M = X.M ⊗ Y.M := rfl
@[simp] lemma tensorObj_L (X Y : ChiExt χ) : (X ⊗ Y).L = X.L ⊗ Y.L := rfl
@[simp] lemma tensorObj_b (X Y : ChiExt χ) : (X ⊗ Y).b = X.b ⊗ₘ Y.b := rfl
@[simp] lemma unit_M : (𝟙_ (ChiExt χ)).M = 𝟙_ _ := rfl
@[simp] lemma unit_L : (𝟙_ (ChiExt χ)).L = 𝟙_ _ := rfl
@[simp] lemma unit_b : (𝟙_ (ChiExt χ)).b = 𝟙 _ := rfl
@[simp] lemma associator_hom_f (X Y Z : ChiExt χ) :
    (α_ X Y Z).hom.f = (α_ X.M Y.M Z.M).hom := rfl
@[simp] lemma associator_hom_φ (X Y Z : ChiExt χ) :
    (α_ X Y Z).hom.φ = (α_ X.L Y.L Z.L).hom := rfl
@[simp] lemma associator_hom_w (X Y Z : ChiExt χ) : (α_ X Y Z).hom.w = 0 := rfl
@[simp] lemma leftUnitor_hom_f (X : ChiExt χ) : (λ_ X).hom.f = (λ_ X.M).hom := rfl
@[simp] lemma leftUnitor_hom_φ (X : ChiExt χ) : (λ_ X).hom.φ = (λ_ X.L).hom := rfl
@[simp] lemma leftUnitor_hom_w (X : ChiExt χ) : (λ_ X).hom.w = 0 := rfl
@[simp] lemma rightUnitor_hom_f (X : ChiExt χ) : (ρ_ X).hom.f = (ρ_ X.M).hom := rfl
@[simp] lemma rightUnitor_hom_φ (X : ChiExt χ) : (ρ_ X).hom.φ = (ρ_ X.L).hom := rfl
@[simp] lemma rightUnitor_hom_w (X : ChiExt χ) : (ρ_ X).hom.w = 0 := rfl

/-- The product is a bifunctor. -/
theorem tensorHom_comp_tensorHom' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ChiExt χ} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  refine hom_ext (by simp) (by simp) ?_
  simp only [comp_w, tensorHom_w', tensorHom_φ', tensorHom_f', comp_f, Preadditive.add_comp,
    Linear.smul_comp, tensorHom_comp_tensorHom, Category.assoc]
  rw [g₁.comm, g₂.comm]
  simp only [Preadditive.comp_add, Linear.comp_smul, MonoidalPreadditive.add_tensor,
    MonoidalPreadditive.tensor_add, smul_tensorHom', tensorHom_smul', smul_add]
  simp only [tensorHom_comp_tensorHom]
  abel

/-- Naturality of the associativity constraint `(x₁ * x₂) * x₃ ↦ x₁ * (x₂ * x₃)`. -/
theorem associator_naturality' {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ChiExt χ} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  refine hom_ext (by simp) (by simp) ?_
  simp only [comp_w, tensorHom_w', tensorHom_φ', tensorHom_f', associator_hom_w,
    associator_hom_f, associator_hom_φ, tensorObj_b, Limits.zero_comp, Limits.comp_zero,
    zero_add, add_zero]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
    MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add, smul_tensorHom',
    tensorHom_smul', smul_add, smul_smul, associator_naturality, tensorHom_comp_tensorHom]
  abel

@[simp] lemma associator_inv_f (X Y Z : ChiExt χ) :
    (α_ X Y Z).inv.f = (α_ X.M Y.M Z.M).inv := rfl
@[simp] lemma associator_inv_φ (X Y Z : ChiExt χ) :
    (α_ X Y Z).inv.φ = (α_ X.L Y.L Z.L).inv := rfl
@[simp] lemma associator_inv_w (X Y Z : ChiExt χ) : (α_ X Y Z).inv.w = 0 := rfl
@[simp] lemma whiskerLeft_f' (X : ChiExt χ) {Y Y' : ChiExt χ} (q : Y ⟶ Y') :
    (X ◁ q).f = 𝟙 X.M ⊗ₘ q.f := rfl
@[simp] lemma whiskerLeft_φ' (X : ChiExt χ) {Y Y' : ChiExt χ} (q : Y ⟶ Y') :
    (X ◁ q).φ = 𝟙 X.L ⊗ₘ q.φ := rfl
@[simp] lemma whiskerLeft_w' (X : ChiExt χ) {Y Y' : ChiExt χ} (q : Y ⟶ Y') :
    (X ◁ q).w = (𝟙 X.M ≫ X.b) ⊗ₘ q.w + 0 ⊗ₘ (q.f ≫ Y'.b) + χ • (0 ⊗ₘ q.w) := rfl
@[simp] lemma whiskerRight_f' {X X' : ChiExt χ} (p : X ⟶ X') (Y : ChiExt χ) :
    (p ▷ Y).f = p.f ⊗ₘ 𝟙 Y.M := rfl
@[simp] lemma whiskerRight_φ' {X X' : ChiExt χ} (p : X ⟶ X') (Y : ChiExt χ) :
    (p ▷ Y).φ = p.φ ⊗ₘ 𝟙 Y.L := rfl
@[simp] lemma whiskerRight_w' {X X' : ChiExt χ} (p : X ⟶ X') (Y : ChiExt χ) :
    (p ▷ Y).w = (p.f ≫ X'.b) ⊗ₘ 0 + p.w ⊗ₘ (𝟙 Y.M ≫ Y.b) + χ • (p.w ⊗ₘ 0) := rfl

/-- **Pages 77 and 78.** `χ`-split extensions form a monoidal category; the unit is
`(𝒪, 𝒪, id)`, `π(u, λ) = λ + χu`. -/
instance : MonoidalCategory (ChiExt χ) := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun _ _ => by ext <;> simp)
  (id_tensorHom := fun _ _ _ _ => rfl)
  (tensorHom_id := fun _ _ => rfl)
  (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom')
  (associator_naturality := associator_naturality')
  (leftUnitor_naturality := fun _ => by ext <;> simp)
  (rightUnitor_naturality := fun _ => by ext <;> simp)
  (pentagon := fun _ _ _ _ => by ext <;> simp [pentagon])
  (triangle := fun _ _ => by ext <;> simp)

/-- The commutativity constraint `x₁ * x₂ ↦ x₂ * x₁`. -/
def braiding (X Y : ChiExt χ) : X ⊗ Y ≅ Y ⊗ X :=
  strictIso (β_ X.M Y.M) (β_ X.L Y.L) (by simp)

@[simp] lemma braiding_hom_f (X Y : ChiExt χ) :
    (braiding X Y).hom.f = (β_ X.M Y.M).hom := rfl
@[simp] lemma braiding_hom_φ (X Y : ChiExt χ) :
    (braiding X Y).hom.φ = (β_ X.L Y.L).hom := rfl
@[simp] lemma braiding_hom_w (X Y : ChiExt χ) : (braiding X Y).hom.w = 0 := rfl

/-- **Pages 77 and 78.** The monoidal category of `χ`-split extensions is symmetric. -/
instance : SymmetricCategory (ChiExt χ) where
  braiding := braiding
  braiding_naturality_right X _ _ f := by refine hom_ext ?_ ?_ ?_ <;> simp
  braiding_naturality_left f Z := by refine hom_ext ?_ ?_ ?_ <;> simp
  hexagon_forward X Y Z := by refine hom_ext ?_ ?_ ?_ <;> simp
  hexagon_reverse X Y Z := by refine hom_ext ?_ ?_ ?_ <;> simp
  symmetry X Y := by refine hom_ext ?_ ?_ ?_ <;> simp

/-- A morphism whose components on `M` and on `L` are isomorphisms is an isomorphism. -/
theorem isIso_of {X Y : ChiExt χ} (p : X ⟶ Y) [IsIso p.f] [IsIso p.φ] : IsIso p := by
  refine ⟨⟨⟨inv p.f, inv p.φ, -(inv p.f ≫ p.w ≫ inv p.φ), ?_⟩, ?_, ?_⟩⟩
  · have h := congrArg (fun g => inv p.f ≫ g ≫ inv p.φ) p.comm
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Preadditive.add_comp,
      Preadditive.comp_add, IsIso.inv_hom_id_assoc, Linear.smul_comp, Linear.comp_smul] at h
    rw [h, smul_neg]; abel
  all_goals refine hom_ext (by simp) (by simp) ?_; simp

/-- An isomorphism has isomorphisms as components on `L`. -/
def isoL {X Y : ChiExt χ} (e : X ≅ Y) : X.L ≅ Y.L where
  hom := e.hom.φ
  inv := e.inv.φ
  hom_inv_id := by rw [← comp_φ, e.hom_inv_id]; rfl
  inv_hom_id := by rw [← comp_φ, e.inv_hom_id]; rfl

/-- An isomorphism has isomorphisms as components on `M`. -/
def isoM {X Y : ChiExt χ} (e : X ≅ Y) : X.M ≅ Y.M where
  hom := e.hom.f
  inv := e.inv.f
  hom_inv_id := by rw [← comp_f, e.hom_inv_id]; rfl
  inv_hom_id := by rw [← comp_f, e.inv_hom_id]; rfl

variable (χ) in
/-- The object `(𝒪, L, b)` of a section `b` of `L` (page 77, `M = 𝒪`: `b = π(x₀)`). -/
def ofSection (L : ModuleCat.{u} R) (b : L) : ChiExt χ :=
  ⟨ModuleCat.of R R, L, ModuleCat.ofHom (LinearMap.toSpanSingleton R L b)⟩

/-- **Page 79, the invertibility criterion, for any `L`.** The object `(𝒪, L, b)` is
invertible for the product iff `L` is an invertible module and `b` generates `L` modulo
`χ`, i.e. `T₀ = −b₀` generates `L₀ = L/χL` on `V(χ)`. -/
theorem invertible_iff_generates (L : ModuleCat.{u} R) (b : L) :
    (∃ Y : ChiExt χ, Nonempty (ofSection χ L b ⊗ Y ≅ 𝟙_ _)) ↔
      Module.Invertible R L ∧ ∀ x : L, ∃ (r : R) (y : L), x = r • b + χ • y := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    have eL := (isoL e).toLinearEquiv
    have hinv : Module.Invertible R L := Module.Invertible.left eL
    refine ⟨hinv, fun x => ?_⟩
    let φ : L ⊗[R] Y.L →ₗ[R] R := e.hom.φ.hom
    let f : R ⊗[R] Y.M →ₗ[R] R := e.hom.f.hom
    let w : R ⊗[R] Y.M →ₗ[R] R := e.hom.w.hom
    have hcomm : φ ∘ₗ TensorProduct.map (LinearMap.toSpanSingleton R L b) Y.b.hom = f + χ • w :=
      congrArg ModuleCat.Hom.hom e.hom.comm
    obtain ⟨t, ht⟩ : ∃ t, f t = 1 := (isoM e).toLinearEquiv.surjective (1 : R)
    obtain ⟨m', rfl⟩ : ∃ m' : Y.M, (1 : R) ⊗ₜ m' = t :=
      ⟨TensorProduct.lid R Y.M t, by
        rw [← TensorProduct.lid_symm_apply]; exact (TensorProduct.lid R Y.M).symm_apply_apply t⟩
    set y := Y.b.hom m'
    have hc : φ (b ⊗ₜ y) = 1 + χ * w ((1 : R) ⊗ₜ m') := by
      have := LinearMap.congr_fun hcomm ((1 : R) ⊗ₜ m')
      simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.toSpanSingleton_apply,
        one_smul, LinearMap.add_apply, LinearMap.smul_apply, ht, smul_eq_mul] using this
    have key : φ (b ⊗ₜ y) • x = φ (x ⊗ₜ y) • b := by
      have h1 := congrArg (fun z => TensorProduct.rid R L (LinearMap.lTensor L φ
        (TensorProduct.assoc R L L Y.L (z ⊗ₜ y)))) (Module.Invertible.tmul_comm (m₁ := x) (m₂ := b))
      simpa only [LinearMap.lTensor_tmul, TensorProduct.assoc_tmul, TensorProduct.rid_tmul] using h1
    refine ⟨φ (x ⊗ₜ y), -(w ((1 : R) ⊗ₜ m')) • x, ?_⟩
    rw [← key, hc]
    module
  · rintro ⟨hinv, hgen⟩
    -- a linear form `β` with `β(b) ≡ 1 mod χ`
    obtain ⟨β, c, hβ⟩ : ∃ (β : Module.Dual R L) (c : R), β b = 1 + χ * c := by
      let I : Submodule R R := LinearMap.range (Module.Dual.eval R L b) ⊔ Ideal.span {χ}
      have hI : ∀ t : Module.Dual R L ⊗[R] L, contractLeft R L t ∈ I := by
        intro t
        induction t with
        | tmul γ x =>
          obtain ⟨r, y, rfl⟩ := hgen x
          rw [contractLeft_apply, map_add, map_smul, map_smul]
          refine Submodule.add_mem_sup ⟨r • γ, by simp⟩ ?_
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self χ)
        | add t t' ht ht' => rw [map_add]; exact I.add_mem ht ht'
      obtain ⟨t, ht⟩ := hinv.bijective.2 1
      have h1 := hI t
      rw [ht, Submodule.mem_sup] at h1
      obtain ⟨a, ⟨β, rfl⟩, z, hz, haz⟩ := h1
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      exact ⟨β, -d, by rw [Module.Dual.eval_apply] at haz; linear_combination haz⟩
    let Y : ChiExt χ :=
      ⟨ModuleCat.of R R, ModuleCat.of R (Module.Dual R L),
        ModuleCat.ofHom (LinearMap.toSpanSingleton R (Module.Dual R L) β)⟩
    let eM : R ⊗[R] R ≃ₗ[R] R := TensorProduct.lid R R
    let eL : L ⊗[R] Module.Dual R L ≃ₗ[R] R :=
      (TensorProduct.comm R L (Module.Dual R L)).trans (Module.Invertible.linearEquiv R L)
    have hlin : eL.toLinearMap ∘ₗ TensorProduct.map (LinearMap.toSpanSingleton R L b)
        (LinearMap.toSpanSingleton R (Module.Dual R L) β)
          = eM.toLinearMap + χ • (c • eM.toLinearMap) := by
      refine TensorProduct.ext' fun r s => ?_
      simp only [eL, eM, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, TensorProduct.comm_tmul, Module.Invertible.linearEquiv,
        LinearEquiv.ofBijective_apply, contractLeft_apply, LinearMap.add_apply,
        LinearMap.smul_apply, TensorProduct.lid_tmul, LinearMap.toSpanSingleton_apply,
        map_smul, hβ, smul_eq_mul, LinearMap.smul_apply]
      ring
    let p : ofSection χ L b ⊗ Y ⟶ 𝟙_ _ :=
      ⟨eM.toModuleIso.hom, eL.toModuleIso.hom, ModuleCat.ofHom (c • eM.toLinearMap),
        ModuleCat.hom_ext hlin⟩
    have : IsIso p.f := inferInstanceAs (IsIso eM.toModuleIso.hom)
    have : IsIso p.φ := inferInstanceAs (IsIso eL.toModuleIso.hom)
    have := isIso_of p
    exact ⟨Y, ⟨asIso p⟩⟩

open scoped Pointwise in
/-- The criterion in the page's words: `(𝒪, L, b)` is invertible iff `L` is invertible and
the class of `b` generates `L₀ = L/χL`. -/
theorem invertible_iff_span (L : ModuleCat.{u} R) (b : L) :
    (∃ Y : ChiExt χ, Nonempty (ofSection χ L b ⊗ Y ≅ 𝟙_ _)) ↔ Module.Invertible R L ∧
      Submodule.span R {Submodule.Quotient.mk (p := χ • (⊤ : Submodule R L)) b} = ⊤ := by
  rw [invertible_iff_generates, generates_iff_span]

end ChiExt

end ChiCategory

end Grothendieck.Folder84


/-! ## The intrinsic product of `χ`-trivialised extensions (pages 65 to 76)

Finding `84-chi-trivialised-extension-product`, the product by amalgamated sum. A
`χ`-trivialised extension of `𝒪` by `L` (`ChiTriv`) is `ι : L → E`, `ψ : E → 𝒪` with `ψι = 0`
and a `χ`-rétraction `π : E → L` with `πι = χ`; nothing is split. The product `E₁ * E₂`
(`Amal`) is the amalgamated sum of `E₁ ⊗ E₂` and `L₁ ⊗ L₂` along
`μ : (L₁ ⊗ E₂) ⊕ (E₁ ⊗ L₂) → L₁ ⊗ L₂`, `μ = (id ⊗ π₂, π₁ ⊗ id)` (page 68), over any
commutative ring and without division:

* `isPushout`: it is a pushout in `ModuleCat` (Mathlib's `IsPushout`); `amalDesc`,
  `amal_hom_ext`: its universal property;
* `prodA`: it is `χ`-trivialised, `π(x₁ * x₂) = π₁(x₁) ⊗ π₂(x₂)` (`piA_star`, page 70),
  `ψ(x₁ * x₂) = ψ₁(x₁)ψ₂(x₂)`; `star_ι_left`, `star_ι_right`, `star_add`: the formulaire of
  pages 72 to 74;
* `ChiTriv.splittingOf`: every extension of `𝒪` splits on an affine base;
  `splitEquiv`, `split_coords`, `prod_exact`, `prodSplitting_b`: for any splittings
  `E₁ * E₂ ≅ 𝒪 × (L₁ ⊗ L₂)`, an extension with `b = b₁ ⊗ b₂` (page 78), and
  `ChiExt.ofSectionTensorIso` identifies it with the coordinate product of `ChiExt`;
* `biaffine_universal`, `biaffine_of_linear` (pages 75 and 76): bi-affine pairs `(f, α)` on
  `P₁ × P₂` are exactly the linear maps out of `E₁ * E₂`.

Not formalised: the intrinsic functoriality and coherence constraints (they are transported
from `ChiExt` through the splittings), extensions of a general `M` and non-affine bases. -/

open CategoryTheory TensorProduct

namespace Grothendieck.Folder84

section Amalgam

variable {R : Type*} [CommRing R] (χ : R)

/-- A `χ`-trivialised extension of `𝒪` by `L` (page 65): `ι : L → E`, `ψ : E → 𝒪` with
`ψι = 0`, and the `χ`-rétraction `π : E → L` with `πι = χ`. -/
structure ChiTriv (L E : Type*) [AddCommGroup L] [Module R L] [AddCommGroup E] [Module R E] where
  ι : L →ₗ[R] E
  ψ : E →ₗ[R] R
  π : E →ₗ[R] L
  ψ_ι : ψ ∘ₗ ι = 0
  π_ι : π ∘ₗ ι = χ • LinearMap.id

variable {χ}
variable {L E : Type*} [AddCommGroup L] [Module R L] [AddCommGroup E] [Module R E]

/-- A splitting: a section `x₀` of `P₁ = ψ⁻¹(1)` and the retraction `p : E → L` it defines. -/
structure ChiTriv.Splitting (X : ChiTriv χ L E) where
  x₀ : E
  p : E →ₗ[R] L
  ψ_x₀ : X.ψ x₀ = 1
  p_ι : p ∘ₗ X.ι = LinearMap.id
  decomp : ∀ e, X.ι (p e) + X.ψ e • x₀ = e

namespace ChiTriv

variable {X : ChiTriv χ L E}

attribute [simp] Splitting.ψ_x₀

@[simp] lemma ψ_ι_apply (u : L) : X.ψ (X.ι u) = 0 := LinearMap.congr_fun X.ψ_ι u
@[simp] lemma π_ι_apply (u : L) : X.π (X.ι u) = χ • u := LinearMap.congr_fun X.π_ι u
@[simp] lemma Splitting.p_ι_apply (s : X.Splitting) (u : L) : s.p (X.ι u) = u :=
  LinearMap.congr_fun s.p_ι u

@[simp] lemma Splitting.p_x₀ (s : X.Splitting) : s.p s.x₀ = 0 := by
  simpa using congrArg s.p (by simpa using s.decomp s.x₀ : X.ι (s.p s.x₀) = 0)

/-- In a splitting, `π = χ p + ψ·b` with `b = π(x₀)`. -/
lemma Splitting.π_eq (s : X.Splitting) (e : E) : X.π e = χ • s.p e + X.ψ e • X.π s.x₀ := by
  conv_lhs => rw [← s.decomp e]
  simp

/-- **Every extension of `𝒪` splits** on an affine base: if `0 → L → E → R → 0` is exact,
it has a splitting. -/
noncomputable def splittingOf (hι : Function.Injective X.ι) (hex : ∀ e, X.ψ e = 0 → ∃ u, X.ι u = e)
    (hψ : Function.Surjective X.ψ) : X.Splitting := by
  let x₀ := (hψ 1).choose
  have hx₀ : X.ψ x₀ = 1 := (hψ 1).choose_spec
  let q : E →ₗ[R] E := LinearMap.id - (LinearMap.toSpanSingleton R E x₀) ∘ₗ X.ψ
  have hr : LinearMap.range q ≤ LinearMap.range X.ι := by
    rintro _ ⟨e, rfl⟩
    exact hex _ (by simp [q, hx₀])
  let eι := LinearEquiv.ofInjective X.ι hι
  let p : E →ₗ[R] L := eι.symm.toLinearMap ∘ₗ Submodule.inclusion hr ∘ₗ q.rangeRestrict
  have hp : ∀ e, X.ι (p e) = q e := fun e => by simp [p, eι]
  exact ⟨x₀, p, hx₀, LinearMap.ext fun u => hι (by simp [hp, q]), fun e => by simp [hp, q]⟩

end ChiTriv

variable {L₁ E₁ L₂ E₂ : Type*} [AddCommGroup L₁] [Module R L₁] [AddCommGroup E₁] [Module R E₁]
  [AddCommGroup L₂] [Module R L₂] [AddCommGroup E₂] [Module R E₂]
  (X₁ : ChiTriv χ L₁ E₁) (X₂ : ChiTriv χ L₂ E₂)

/-- `(L₁ ⊗ E₂) ⊕ (E₁ ⊗ L₂)`, which maps onto `E₁ ⊗₀ E₂ = L₁ ⊗ E₂ + E₁ ⊗ L₂ ⊂ E₁ ⊗ E₂`. -/
abbrev Kdom := (L₁ ⊗[R] E₂) × (E₁ ⊗[R] L₂)

/-- The map `(L₁ ⊗ E₂) ⊕ (E₁ ⊗ L₂) → E₁ ⊗ E₂`, with image `E₁ ⊗₀ E₂`. -/
noncomputable def jK : Kdom (R := R) (L₁ := L₁) (E₁ := E₁) (L₂ := L₂) (E₂ := E₂) →ₗ[R] E₁ ⊗[R] E₂ :=
  (map X₁.ι LinearMap.id) ∘ₗ LinearMap.fst R _ _ + (map LinearMap.id X₂.ι) ∘ₗ LinearMap.snd R _ _

/-- `μ`, equal to `id ⊗ π₂` on `L₁ ⊗ E₂` and to `π₁ ⊗ id` on `E₁ ⊗ L₂` (page 68). -/
noncomputable def μK : Kdom (R := R) (L₁ := L₁) (E₁ := E₁) (L₂ := L₂) (E₂ := E₂) →ₗ[R]
    L₁ ⊗[R] L₂ :=
  (map LinearMap.id X₂.π) ∘ₗ LinearMap.fst R _ _ + (map X₁.π LinearMap.id) ∘ₗ LinearMap.snd R _ _

/-- The relations of the amalgamated sum. -/
noncomputable def relK : Kdom (R := R) (L₁ := L₁) (E₁ := E₁) (L₂ := L₂) (E₂ := E₂) →ₗ[R]
    (E₁ ⊗[R] E₂) × (L₁ ⊗[R] L₂) :=
  LinearMap.prod (jK X₁ X₂) (-μK X₁ X₂)

/-- **The product `E₁ * E₂` (pages 68 to 70)**: the amalgamated sum of `E₁ ⊗ E₂` and
`L₁ ⊗ L₂` along `μ : E₁ ⊗₀ E₂ → L₁ ⊗ L₂`, with no splitting chosen. -/
abbrev Amal := ((E₁ ⊗[R] E₂) × (L₁ ⊗[R] L₂)) ⧸ LinearMap.range (relK X₁ X₂)

/-- `x₁ ⊗ x₂ ↦ x₁ * x₂`. -/
noncomputable def starA : E₁ ⊗[R] E₂ →ₗ[R] Amal X₁ X₂ :=
  (LinearMap.range (relK X₁ X₂)).mkQ ∘ₗ LinearMap.inl R _ _

/-- `L₁ ⊗ L₂ → E₁ * E₂`. -/
noncomputable def incl : L₁ ⊗[R] L₂ →ₗ[R] Amal X₁ X₂ :=
  (LinearMap.range (relK X₁ X₂)).mkQ ∘ₗ LinearMap.inr R _ _

theorem star_comp_jK : starA X₁ X₂ ∘ₗ jK X₁ X₂ = incl X₁ X₂ ∘ₗ μK X₁ X₂ := by
  exact LinearMap.ext fun k => (Submodule.Quotient.eq _).2 ⟨k, by simp [relK]⟩

/-- The descent of `(g, h)` with `g ∘ j = h ∘ μ` to the amalgamated sum. -/
noncomputable def amalDesc {N : Type*} [AddCommGroup N] [Module R N] (g : E₁ ⊗[R] E₂ →ₗ[R] N)
    (h : L₁ ⊗[R] L₂ →ₗ[R] N) (w : g ∘ₗ jK X₁ X₂ = h ∘ₗ μK X₁ X₂) : Amal X₁ X₂ →ₗ[R] N :=
  (LinearMap.range (relK X₁ X₂)).liftQ (LinearMap.coprod g h) (by
    rintro _ ⟨k, rfl⟩
    simpa [relK, add_neg_eq_zero] using LinearMap.congr_fun w k)

variable {N : Type*} [AddCommGroup N] [Module R N]

@[simp] lemma amalDesc_starA (g : E₁ ⊗[R] E₂ →ₗ[R] N) (h : L₁ ⊗[R] L₂ →ₗ[R] N)
    (w : g ∘ₗ jK X₁ X₂ = h ∘ₗ μK X₁ X₂) (x : E₁ ⊗[R] E₂) :
    amalDesc X₁ X₂ g h w (starA X₁ X₂ x) = g x := by simp [amalDesc, starA]

@[simp] lemma amalDesc_incl (g : E₁ ⊗[R] E₂ →ₗ[R] N) (h : L₁ ⊗[R] L₂ →ₗ[R] N)
    (w : g ∘ₗ jK X₁ X₂ = h ∘ₗ μK X₁ X₂) (x : L₁ ⊗[R] L₂) :
    amalDesc X₁ X₂ g h w (incl X₁ X₂ x) = h x := by simp [amalDesc, incl]

theorem amal_hom_ext {F G : Amal X₁ X₂ →ₗ[R] N} (h₁ : F ∘ₗ starA X₁ X₂ = G ∘ₗ starA X₁ X₂)
    (h₂ : F ∘ₗ incl X₁ X₂ = G ∘ₗ incl X₁ X₂) : F = G :=
  Submodule.linearMap_qext _ (LinearMap.prod_ext h₁ h₂)

/-- **The amalgamated sum is a pushout** (in `ModuleCat`, Mathlib's `IsPushout`). -/
theorem isPushout {R : Type u} [CommRing R] {χ : R} {L₁ E₁ L₂ E₂ : Type u} [AddCommGroup L₁]
    [Module R L₁] [AddCommGroup E₁] [Module R E₁] [AddCommGroup L₂] [Module R L₂]
    [AddCommGroup E₂] [Module R E₂] (X₁ : ChiTriv χ L₁ E₁) (X₂ : ChiTriv χ L₂ E₂) :
    IsPushout (ModuleCat.ofHom (jK X₁ X₂)) (ModuleCat.ofHom (μK X₁ X₂))
      (ModuleCat.ofHom (starA X₁ X₂)) (ModuleCat.ofHom (incl X₁ X₂)) := by
  have w : ModuleCat.ofHom (jK X₁ X₂) ≫ ModuleCat.ofHom (starA X₁ X₂) =
      ModuleCat.ofHom (μK X₁ X₂) ≫ ModuleCat.ofHom (incl X₁ X₂) := by
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, star_comp_jK]
  refine IsPushout.of_isColimit (Limits.PushoutCocone.IsColimit.mk w
    (fun s => ModuleCat.ofHom (amalDesc X₁ X₂ s.inl.hom s.inr.hom
      (congrArg ModuleCat.Hom.hom s.condition))) ?_ ?_ ?_)
  · intro s; ext x; simp
  · intro s; ext x; simp
  · intro s m h₁ h₂
    ext1
    exact amal_hom_ext _ _ (LinearMap.ext fun x => by simpa using congrArg (fun f => f.hom x) h₁)
      (LinearMap.ext fun x => by simpa using congrArg (fun f => f.hom x) h₂)

/-- `ψ₁ ⊗ ψ₂ : E₁ ⊗ E₂ → 𝒪`. -/
noncomputable def psiT : E₁ ⊗[R] E₂ →ₗ[R] R := LinearMap.mul' R R ∘ₗ map X₁.ψ X₂.ψ

@[simp] lemma psiT_tmul (x₁ : E₁) (x₂ : E₂) : psiT X₁ X₂ (x₁ ⊗ₜ x₂) = X₁.ψ x₁ * X₂.ψ x₂ := rfl

/-- The augmentation `ψ : E₁ * E₂ → 𝒪`. -/
noncomputable def psiA : Amal X₁ X₂ →ₗ[R] R :=
  amalDesc X₁ X₂ (psiT X₁ X₂) 0 (by ext <;> simp [psiT, jK])

/-- The `χ`-rétraction `π(x₁ * x₂) = π₁(x₁) ⊗ π₂(x₂)` (page 70, « On y gagne ! »). -/
noncomputable def piA : Amal X₁ X₂ →ₗ[R] L₁ ⊗[R] L₂ :=
  amalDesc X₁ X₂ (map X₁.π X₂.π) (χ • LinearMap.id) (by
    ext <;> simp [jK, μK, smul_tmul', tmul_smul])

/-- **The product is a `χ`-trivialised extension**, constructed without any division and
without choosing a splitting. -/
noncomputable def prodA : ChiTriv χ (L₁ ⊗[R] L₂) (Amal X₁ X₂) where
  ι := incl X₁ X₂
  ψ := psiA X₁ X₂
  π := piA X₁ X₂
  ψ_ι := by ext; simp [psiA]
  π_ι := by ext; simp [piA]

@[simp] lemma piA_star (x₁ : E₁) (x₂ : E₂) :
    piA X₁ X₂ (starA X₁ X₂ (x₁ ⊗ₜ x₂)) = X₁.π x₁ ⊗ₜ X₂.π x₂ := by simp [piA]

@[simp] lemma psiA_star (x₁ : E₁) (x₂ : E₂) :
    psiA X₁ X₂ (starA X₁ X₂ (x₁ ⊗ₜ x₂)) = X₁.ψ x₁ * X₂.ψ x₂ := by simp [psiA, psiT]

/-- **Formulaire (pages 72 to 74)**: `u₁ * x₂ = u₁ ⊗ π₂(x₂)`. -/
lemma star_ι_left (u₁ : L₁) (x₂ : E₂) :
    starA X₁ X₂ (X₁.ι u₁ ⊗ₜ x₂) = incl X₁ X₂ (u₁ ⊗ₜ X₂.π x₂) := by
  simpa [jK, μK] using LinearMap.congr_fun (star_comp_jK X₁ X₂) (u₁ ⊗ₜ x₂, 0)

/-- `x₁ * u₂ = π₁(x₁) ⊗ u₂`. -/
lemma star_ι_right (x₁ : E₁) (u₂ : L₂) :
    starA X₁ X₂ (x₁ ⊗ₜ X₂.ι u₂) = incl X₁ X₂ (X₁.π x₁ ⊗ₜ u₂) := by
  simpa [jK, μK] using LinearMap.congr_fun (star_comp_jK X₁ X₂) (0, x₁ ⊗ₜ u₂)

/-- `(x₁ + u₁) * (x₂ + u₂) = x₁ * x₂ + u₁ ⊗ π₂(x₂) + π₁(x₁) ⊗ u₂ + χ u₁ ⊗ u₂`. -/
theorem star_add (x₁ : E₁) (u₁ : L₁) (x₂ : E₂) (u₂ : L₂) :
    starA X₁ X₂ ((x₁ + X₁.ι u₁) ⊗ₜ (x₂ + X₂.ι u₂)) = starA X₁ X₂ (x₁ ⊗ₜ x₂) +
      incl X₁ X₂ (u₁ ⊗ₜ X₂.π x₂ + X₁.π x₁ ⊗ₜ u₂ + χ • u₁ ⊗ₜ u₂) := by
  simp only [add_tmul, tmul_add, map_add, star_ι_left, star_ι_right, ChiTriv.π_ι_apply]
  abel

variable {X₁ X₂}

/-- The coordinates `E₁ * E₂ → 𝒪 × (L₁ ⊗ L₂)` of a pair of splittings. -/
noncomputable def coordT (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    E₁ ⊗[R] E₂ →ₗ[R] R × (L₁ ⊗[R] L₂) :=
  LinearMap.prod (psiT X₁ X₂)
    (map s₁.p X₂.π + map (LinearMap.toSpanSingleton R L₁ (X₁.π s₁.x₀) ∘ₗ X₁.ψ) s₂.p)

noncomputable def coord (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    Amal X₁ X₂ →ₗ[R] R × (L₁ ⊗[R] L₂) :=
  amalDesc X₁ X₂ (coordT s₁ s₂) (LinearMap.inr R R _) (by
    ext u e <;> simp [coordT, psiT, jK, μK]
    rw [s₁.π_eq u, add_tmul, smul_tmul'])

@[simp] lemma coord_star (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) (x : E₁ ⊗[R] E₂) :
    coord s₁ s₂ (starA X₁ X₂ x) = coordT s₁ s₂ x := amalDesc_starA ..

@[simp] lemma coord_incl (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) (x : L₁ ⊗[R] L₂) :
    coord s₁ s₂ (incl X₁ X₂ x) = (0, x) := amalDesc_incl ..

noncomputable def uncoord (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    R × (L₁ ⊗[R] L₂) →ₗ[R] Amal X₁ X₂ :=
  LinearMap.coprod (LinearMap.toSpanSingleton R _ (starA X₁ X₂ (s₁.x₀ ⊗ₜ s₂.x₀))) (incl X₁ X₂)

/-- Every `e₁ * e₂` in the coordinates of two splittings. -/
lemma star_eq_split (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) (e₁ : E₁) (e₂ : E₂) :
    starA X₁ X₂ (e₁ ⊗ₜ e₂) = (X₁.ψ e₁ * X₂.ψ e₂) • starA X₁ X₂ (s₁.x₀ ⊗ₜ s₂.x₀) +
      incl X₁ X₂ (s₁.p e₁ ⊗ₜ X₂.π e₂ + X₁.ψ e₁ • X₁.π s₁.x₀ ⊗ₜ s₂.p e₂) := by
  conv_lhs => rw [← s₁.decomp e₁, ← s₂.decomp e₂]
  rw [s₂.π_eq e₂]
  simp only [add_tmul, tmul_add, ← smul_tmul', tmul_smul, map_add, map_smul, star_ι_left,
    star_ι_right, ChiTriv.π_ι_apply]
  module

/-- **The split case (pages 77 and 78).** A splitting of each factor identifies the
amalgamated sum with `𝒪 × (L₁ ⊗ L₂)`. -/
noncomputable def splitEquiv (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    Amal X₁ X₂ ≃ₗ[R] R × (L₁ ⊗[R] L₂) :=
  LinearEquiv.ofLinearMap (coord s₁ s₂) (uncoord s₁ s₂)
    (by ext <;> simp [coord, uncoord, coordT, psiT])
    (by
      refine amal_hom_ext _ _ (TensorProduct.ext' fun e₁ e₂ => ?_) (by ext; simp [coord, uncoord])
      rw [LinearMap.id_comp, LinearMap.comp_apply, LinearMap.comp_apply, star_eq_split s₁ s₂]
      simp [coord, uncoord, coordT, psiT])

@[simp] lemma splitEquiv_apply (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) (z : Amal X₁ X₂) :
    splitEquiv s₁ s₂ z = coord s₁ s₂ z := rfl

@[simp] lemma splitEquiv_symm_apply (s₁ : X₁.Splitting) (s₂ : X₂.Splitting)
    (z : R × (L₁ ⊗[R] L₂)) : (splitEquiv s₁ s₂).symm z = uncoord s₁ s₂ z := rfl

/-- In the coordinates of two splittings, the product is the split extension
`0 → L₁ ⊗ L₂ → 𝒪 × (L₁ ⊗ L₂) → 𝒪 → 0` (`ψ = fst`, `ι = inr`) with the `χ`-rétraction
`π(λ, u) = λ b₁ ⊗ b₂ + χu`: **`b = b₁ ⊗ b₂`** (page 78, « Il n'y a pas plus simple ! »). -/
theorem split_coords (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    psiA X₁ X₂ ∘ₗ (splitEquiv s₁ s₂).symm.toLinearMap = LinearMap.fst R R _ ∧
      (splitEquiv s₁ s₂).toLinearMap ∘ₗ incl X₁ X₂ = LinearMap.inr R R _ ∧
      piA X₁ X₂ ∘ₗ (splitEquiv s₁ s₂).symm.toLinearMap =
        LinearMap.coprod (LinearMap.toSpanSingleton R _ (X₁.π s₁.x₀ ⊗ₜ X₂.π s₂.x₀))
          (χ • LinearMap.id) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp [uncoord, coord, psiA, piA]

/-- **The product is an extension** of `𝒪` by `L₁ ⊗ L₂` as soon as the factors are split
(which they always are on an affine base, `ChiTriv.splittingOf`). -/
theorem prod_exact (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    Function.Injective (incl X₁ X₂) ∧ LinearMap.ker (psiA X₁ X₂) = LinearMap.range (incl X₁ X₂) ∧
      Function.Surjective (psiA X₁ X₂) := by
  refine ⟨fun a b h => by simpa using congrArg (coord s₁ s₂) h, ?_, fun r =>
    ⟨starA X₁ X₂ (r • s₁.x₀ ⊗ₜ s₂.x₀), by simp [psiA]⟩⟩
  ext z
  refine ⟨fun hz => ⟨(coord s₁ s₂ z).2, ?_⟩, ?_⟩
  · have h1 : LinearMap.fst R R _ ∘ₗ coord s₁ s₂ = psiA X₁ X₂ := by
      apply amal_hom_ext <;> ext <;> simp [coordT, psiA]
    simpa [uncoord, show (coord s₁ s₂ z).1 = 0 from (LinearMap.congr_fun h1 z).trans hz] using
      (splitEquiv s₁ s₂).symm_apply_apply z
  · rintro ⟨u, rfl⟩
    simp [psiA]

/-- The splitting `x₁ * x₂` of the product, with `b = π(x₁ * x₂) = b₁ ⊗ b₂`. -/
noncomputable def prodSplitting (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    (prodA X₁ X₂).Splitting where
  x₀ := starA X₁ X₂ (s₁.x₀ ⊗ₜ s₂.x₀)
  p := LinearMap.snd R R _ ∘ₗ (splitEquiv s₁ s₂).toLinearMap
  ψ_x₀ := by simp [prodA]
  p_ι := by ext; simp [prodA, coord]
  decomp z := by
    obtain ⟨⟨r, u⟩, rfl⟩ := (splitEquiv s₁ s₂).symm.surjective z
    simp [prodA, uncoord, psiA, coordT, add_comm]

theorem prodSplitting_b (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) :
    (prodA X₁ X₂).π (prodSplitting s₁ s₂).x₀ = X₁.π s₁.x₀ ⊗ₜ X₂.π s₂.x₀ := piA_star ..

/-- **Universal property of bi-affine maps (pages 75 and 76).** A pair `(f, α)`, `f` defined on
`P₁ × P₂` (`ψᵢ(xᵢ) = 1`) and `α : L₁ ⊗ L₂ → N` linear, with
`f(x₁ + u₁, x₂) = f(x₁, x₂) + α(u₁ ⊗ π₂(x₂))` and `f(x₁, x₂ + u₂) = f(x₁, x₂) + α(π₁(x₁) ⊗ u₂)`,
factors uniquely through `(x₁, x₂) ↦ x₁ * x₂`: there is exactly one linear
`g : E₁ * E₂ → N` with `g(x₁ * x₂) = f(x₁, x₂)` and `g|_{L₁ ⊗ L₂} = α`. -/
theorem biaffine_universal (s₁ : X₁.Splitting) (s₂ : X₂.Splitting) (f : E₁ → E₂ → N)
    (α : L₁ ⊗[R] L₂ →ₗ[R] N)
    (h₁ : ∀ x₁ x₂ u₁, X₁.ψ x₁ = 1 → X₂.ψ x₂ = 1 →
      f (x₁ + X₁.ι u₁) x₂ = f x₁ x₂ + α (u₁ ⊗ₜ X₂.π x₂))
    (h₂ : ∀ x₁ x₂ u₂, X₁.ψ x₁ = 1 → X₂.ψ x₂ = 1 →
      f x₁ (x₂ + X₂.ι u₂) = f x₁ x₂ + α (X₁.π x₁ ⊗ₜ u₂)) :
    ∃! g : Amal X₁ X₂ →ₗ[R] N, (∀ x₁ x₂, X₁.ψ x₁ = 1 → X₂.ψ x₂ = 1 →
      g (starA X₁ X₂ (x₁ ⊗ₜ x₂)) = f x₁ x₂) ∧ g ∘ₗ incl X₁ X₂ = α := by
  refine ⟨LinearMap.coprod (LinearMap.toSpanSingleton R N (f s₁.x₀ s₂.x₀)) α ∘ₗ coord s₁ s₂,
    ⟨fun y₁ y₂ hy₁ hy₂ => ?_, by ext; simp [coord]⟩, fun g ⟨hg, hgα⟩ => ?_⟩
  · have d₁ := s₁.decomp y₁
    have d₂ := s₂.decomp y₂
    rw [hy₁, one_smul, add_comm] at d₁
    rw [hy₂, one_smul, add_comm] at d₂
    rw [← d₁, h₁ _ _ _ s₁.ψ_x₀ hy₂, ← d₂, h₂ _ _ _ s₁.ψ_x₀ s₂.ψ_x₀, d₂]
    simp [coord, coordT, hy₂]
    abel
  · subst hgα
    refine amal_hom_ext _ _ (TensorProduct.ext' fun e₁ e₂ => ?_) (by ext; simp [coord])
    rw [LinearMap.comp_apply, LinearMap.comp_apply, star_eq_split s₁ s₂ e₁ e₂]
    simp [hg _ _ s₁.ψ_x₀ s₂.ψ_x₀, coordT]

/-- Conversely every linear map out of `E₁ * E₂` restricts to a bi-affine pair, with no
condition on `ψ`. -/
theorem biaffine_of_linear (g : Amal X₁ X₂ →ₗ[R] N) (x₁ : E₁) (x₂ : E₂) (u₁ : L₁) (u₂ : L₂) :
    g (starA X₁ X₂ ((x₁ + X₁.ι u₁) ⊗ₜ x₂)) =
        g (starA X₁ X₂ (x₁ ⊗ₜ x₂)) + g (incl X₁ X₂ (u₁ ⊗ₜ X₂.π x₂)) ∧
      g (starA X₁ X₂ (x₁ ⊗ₜ (x₂ + X₂.ι u₂))) =
        g (starA X₁ X₂ (x₁ ⊗ₜ x₂)) + g (incl X₁ X₂ (X₁.π x₁ ⊗ₜ u₂)) := by
  simp [add_tmul, tmul_add, star_ι_left, star_ι_right]

end Amalgam

/-- **The two products agree.** For split objects with `M = 𝒪`, the coordinate product of
`ChiExt` is `(𝒪, L₁, b₁) ⊗ (𝒪, L₂, b₂) ≅ (𝒪, L₁ ⊗ L₂, b₁ ⊗ b₂)`, the coordinates of the
intrinsic product (`split_coords`, `prodSplitting_b`). -/
def ChiExt.ofSectionTensorIso {R : Type u} [CommRing R] (χ : R) (L₁ L₂ : ModuleCat.{u} R)
    (b₁ : L₁) (b₂ : L₂) :
    ChiExt.ofSection χ L₁ b₁ ⊗ ChiExt.ofSection χ L₂ b₂ ≅
      ChiExt.ofSection χ (L₁ ⊗ L₂) (b₁ ⊗ₜ[R] b₂) :=
  ChiExt.strictIso (λ_ (ModuleCat.of R R)) (Iso.refl _)
    (ModuleCat.MonoidalCategory.tensor_ext fun (r s : R) => by
      change (r • b₁) ⊗ₜ[R] (s • b₂) = (r • s) • (b₁ ⊗ₜ[R] b₂)
      rw [tmul_smul, ← smul_tmul', smul_smul, smul_eq_mul, mul_comm])



/-! ## Base change and the reconstruction of pages 49 to 52

Finding `84-two-regular-triplet-classification`, continued.

* `bc2`, `discL_baseChange`, `tripletCond_baseChange`, `isCoverHom_baseChange`,
  `tripletHom_baseChange`: the functor `(L, b, c) ↦ (L, δ, T₀)` commutes with every base
  change `R → S`, on objects and on morphisms (the fibred statement, affine bases);
* free case, with Mathlib's `Algebra.trace` and `Algebra.norm` (`trace_qalg`, `norm_qalg`):
  `recon : y ↦ (Tr y, γ)` has image `{β ≡ γ T₀ mod 2}` (`recon_range`, any `R`), is injective
  when `2` is regular (`recon_injective`), sends `1` to `(2, 0)`, and
  `2(yy') = (ββ' + γγ'δ, βγ' + γβ')`, `4N = β² − γ²δ` (`recon_mul`, `recon_norm`); on
  `E = Ǎ`, `eCoord : x ↦ (λ, ζ)` with image `{ζ ≡ λT₀}` (`eCoord_range`, `eCoord_injective`),
  the coupling `2⟨y, x⟩ = λβ + γζ` (`coupling`), `4Q = ζ² − λ²δ` (`four_qE`) and
  `φ_N(β, γ) = (β, −γδ)`, `Q(φ_N(y)) = −N(y)δ` (`phiN_coords`, the box of page 46);
* `L` invertible: each division of pages 49 to 52 is legitimate (`div_norm`,
  `div_prod_fst`, `div_prod_snd`, `div_qform`) and the product stays in `Γ A` (`div_prod_mem`).

Not formalised: the page-45 equivalence between rank-2 algebras and `(L, P₁, Q)` when `L` is
not trivial, and non-affine bases. -/

section BaseChange

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']

/-- `L ⊗ L → L_S ⊗_S L_S`, `x ⊗ y ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`: base change of a section of
`L^{⊗2}`. -/
noncomputable def bc2 (L : Type*) [AddCommGroup L] [Module R L] :
    L ⊗[R] L →ₗ[R] (S ⊗[R] L) ⊗[S] (S ⊗[R] L) :=
  TensorProduct.lift (LinearMap.mk₂ R (fun x y => ((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y))
    (fun _ _ _ => by simp [tmul_add, add_tmul]) (fun r x y => by
      rw [tmul_smul, ← smul_tmul', ← algebraMap_smul S r])
    (fun _ _ _ => by simp [tmul_add]) (fun r x y => by
      rw [tmul_smul, ← algebraMap_smul S r, ← algebraMap_smul S r, tmul_smul]))

@[simp] lemma bc2_tmul (x y : L) :
    bc2 S L (x ⊗ₜ y) = ((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y) := rfl

lemma bc2_smul (r : R) (z : L ⊗[R] L) : bc2 S L (r • z) = algebraMap R S r • bc2 S L z := by
  rw [map_smul, algebraMap_smul]

/-- Base change commutes with `φ ⊗ φ`. -/
lemma bc2_map (φ : L →ₗ[R] L') (z : L ⊗[R] L) :
    bc2 S L' (TensorProduct.map φ φ z) =
      TensorProduct.map (φ.baseChange S) (φ.baseChange S) (bc2 S L z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp
  | add z z' hz hz' => simp [hz, hz']

/-- **Base change of the discriminant**: `δ(b_S, c_S) = δ(b, c)_S`. -/
theorem discL_baseChange (b : L) (c : L ⊗[R] L) :
    discL ((1 : S) ⊗ₜ[R] b) (bc2 S L c) = bc2 S L (discL b c) := by
  simp only [discL, map_sub, bc2_tmul, bc2_smul, map_ofNat]

/-- **Base change of the triplet condition**: `T₀² ≡ δ mod 4` passes to every `S`. -/
theorem tripletCond_baseChange {δ : L ⊗[R] L} {τ : L}
    (h : TripletCond δ (Submodule.Quotient.mk τ)) :
    TripletCond (bc2 S L δ) (Submodule.Quotient.mk ((1 : S) ⊗ₜ[R] τ)) := by
  obtain ⟨τ', hτ', k, hk⟩ := h
  rw [Submodule.Quotient.eq] at hτ'
  obtain ⟨a, ha⟩ := mem_twoL.1 hτ'
  refine ⟨(1 : S) ⊗ₜ τ', ?_, bc2 S L k, ?_⟩
  · rw [Submodule.Quotient.eq]
    exact mem_twoL.2 ⟨(1 : S) ⊗ₜ a, by
      rw [← map_ofNat (algebraMap R S) 2, algebraMap_smul, ← tmul_smul, ha, tmul_sub]⟩
  · simpa only [map_sub, bc2_tmul, bc2_smul, map_ofNat] using congrArg (bc2 S L) hk

/-- **Base change of morphisms of covers.** If `(φ, t)` is a morphism
`(L, b, c) → (L', b', c')`, then `(φ_S, 1 ⊗ t)` is a morphism of the base-changed covers. -/
theorem isCoverHom_baseChange [Module.Invertible R L'] {b : L} {c : L ⊗[R] L} {b' : L'}
    {c' : L' ⊗[R] L'} {φ : L ≃ₗ[R] L'} {t : L'} (h : IsCoverHom b c b' c' φ t) :
    IsCoverHom ((1 : S) ⊗ₜ[R] b) (bc2 S L c) ((1 : S) ⊗ₜ[R] b') (bc2 S L' c')
      (φ.baseChange R S L L') ((1 : S) ⊗ₜ[R] t) := by
  obtain ⟨hb, hc⟩ := (isCoverHom_iff b c b' c' φ t).1 h
  refine (isCoverHom_iff _ _ _ _ _ _).2 ⟨?_, ?_⟩
  · rw [LinearEquiv.baseChange_tmul, hb, tmul_add, ← map_ofNat (algebraMap R S) 2,
      algebraMap_smul, tmul_smul]
  · have e := bc2_map S (φ : L →ₗ[R] L') c
    rw [hc, map_add, map_add, bc2_tmul, bc2_tmul] at e
    exact e.symm

/-- **Base change of morphisms of triplets**: `φ_S` is again an isomorphism of triplets. -/
theorem tripletHom_baseChange {δ : L ⊗[R] L} {δ' : L' ⊗[R] L'} {τ : L} {τ' : L'}
    (φ : L ≃ₗ[R] L') (hδ : TensorProduct.map (φ : L →ₗ[R] L') (φ : L →ₗ[R] L') δ = δ')
    (hT : mod2 (φ : L →ₗ[R] L') (Submodule.Quotient.mk τ) = Submodule.Quotient.mk τ') :
    TensorProduct.map ((φ.baseChange R S L L' : _ ≃ₗ[S] _) : S ⊗[R] L →ₗ[S] S ⊗[R] L')
        (φ.baseChange R S L L' : S ⊗[R] L →ₗ[S] S ⊗[R] L') (bc2 S L δ) = bc2 S L' δ' ∧
      mod2 (φ.baseChange R S L L' : S ⊗[R] L →ₗ[S] S ⊗[R] L')
        (Submodule.Quotient.mk ((1 : S) ⊗ₜ[R] τ)) = Submodule.Quotient.mk ((1 : S) ⊗ₜ[R] τ') := by
  refine ⟨by rw [← hδ, bc2_map]; rfl, ?_⟩
  rw [mod2_mk, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, Submodule.Quotient.eq]
  rw [mod2_mk, LinearEquiv.coe_coe, Submodule.Quotient.eq] at hT
  obtain ⟨a, ha⟩ := mem_twoL.1 hT
  exact mem_twoL.2 ⟨(1 : S) ⊗ₜ a, by
    rw [← map_ofNat (algebraMap R S) 2, algebraMap_smul, ← tmul_smul, ha, tmul_sub]⟩

end BaseChange

section Reconstruction

open Polynomial

variable {R : Type*} [CommRing R] (b c : R)

set_option backward.proofsInPublic true in
/-- The basis `(1, U)` of `R[U]/(U² + bU + c)`. -/
noncomputable def qbasis : Module.Basis (Fin 2) R (QAlg b c) :=
  .mk (v := ![1, AdjoinRoot.root (qpoly b c)])
    (LinearIndependent.pair_iff.2 fun s t h => coords_zero (by
      simpa [Algebra.smul_def] using h))
    (by
      rintro y -
      obtain ⟨a, e, rfl⟩ := coords_exist y
      rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))

variable {b c}

@[simp] lemma qbasis_zero : qbasis b c 0 = 1 := by simp [qbasis]
@[simp] lemma qbasis_one : qbasis b c 1 = AdjoinRoot.root _ := by simp [qbasis]

lemma qbasis_repr {y : QAlg b c} {a e : R}
    (hy : y = algebraMap R _ a + algebraMap R _ e * AdjoinRoot.root _) :
    (qbasis b c).repr y 0 = a ∧ (qbasis b c).repr y 1 = e := by
  rw [show y = a • qbasis b c 0 + e • qbasis b c 1 by simp [hy, Algebra.smul_def], map_add,
    map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  simp

/-- `y · U` in the basis `(1, U)`. -/
lemma mul_root (a e : R) :
    (algebraMap R (QAlg b c) a + algebraMap R _ e * AdjoinRoot.root _) * AdjoinRoot.root _ =
      algebraMap R _ (-(e * c)) + algebraMap R _ (a - e * b) * AdjoinRoot.root _ := by
  simp only [map_neg, map_sub, map_mul]
  linear_combination (algebraMap R (QAlg b c) e) * root_sq b c

/-- The trace (Mathlib's `Algebra.trace`) of `a + eU` is `2a − eb`. -/
theorem trace_qalg (a e : R) :
    Algebra.trace R (QAlg b c) (algebraMap R _ a + algebraMap R _ e * AdjoinRoot.root _) =
      2 * a - e * b := by
  rw [Algebra.trace_eq_matrix_trace (qbasis b c), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [qbasis_zero, qbasis_one, mul_one, mul_root]
  rw [(qbasis_repr rfl).1, (qbasis_repr rfl).2]
  ring

/-- The norm (Mathlib's `Algebra.norm`) of `a + eU` is `a² − abe + ce²`. -/
theorem norm_qalg (a e : R) :
    Algebra.norm R (algebraMap R (QAlg b c) a + algebraMap R _ e * AdjoinRoot.root _) =
      a ^ 2 - a * b * e + c * e ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (qbasis b c), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [qbasis_zero, qbasis_one, mul_one, mul_root]
  rw [(qbasis_repr rfl).1, (qbasis_repr rfl).2, (qbasis_repr rfl).1, (qbasis_repr rfl).2]
  ring

/-- Products in the basis `(1, U)`. -/
lemma mul_coords (a e a' e' : R) :
    (algebraMap R (QAlg b c) a + algebraMap R _ e * AdjoinRoot.root _) *
        (algebraMap R _ a' + algebraMap R _ e' * AdjoinRoot.root _) =
      algebraMap R _ (a * a' - e * e' * c) +
        algebraMap R _ (a * e' + a' * e - e * e' * b) * AdjoinRoot.root _ := by
  simp only [map_sub, map_mul, map_add]
  linear_combination (algebraMap R (QAlg b c) e * algebraMap R (QAlg b c) e') * root_sq b c

/-- The reconstruction map of pages 49 to 52: `y ↦ (Tr y, γ)`, with `y = (Tr y + γ z)/2`,
`z = 2U + b`, `z² = δ`. -/
noncomputable def recon : QAlg b c →ₗ[R] R × R :=
  (Algebra.trace R (QAlg b c)).prod (Finsupp.lapply 1 ∘ₗ (qbasis b c).repr.toLinearMap)

lemma recon_of (a e : R) :
    recon (algebraMap R (QAlg b c) a + algebraMap R _ e * AdjoinRoot.root _) =
      (2 * a - e * b, e) :=
  Prod.ext (trace_qalg a e) (qbasis_repr rfl).2

lemma recon_one : recon (1 : QAlg b c) = (2, 0) := by
  simpa using recon_of (b := b) (c := c) 1 0

/-- **The product of page 51**, without division:
`2 β(yy') = ββ' + γγ'δ` and `2 γ(yy') = βγ' + γβ'`. -/
theorem recon_mul (y y' : QAlg b c) :
    2 * (recon (y * y')).1 = (recon y).1 * (recon y').1 + (recon y).2 * (recon y').2 * disc b c ∧
      2 * (recon (y * y')).2 = (recon y).1 * (recon y').2 + (recon y).2 * (recon y').1 := by
  obtain ⟨a, e, rfl⟩ := coords_exist y
  obtain ⟨a', e', rfl⟩ := coords_exist y'
  rw [mul_coords, recon_of, recon_of, recon_of, disc]
  constructor <;> ring

/-- **The norm of page 51**: `4N(β, γ) = β² − γ²δ`, Mathlib's `Algebra.norm`. -/
theorem recon_norm (y : QAlg b c) :
    4 * Algebra.norm R y = (recon y).1 ^ 2 - (recon y).2 ^ 2 * disc b c := by
  obtain ⟨a, e, rfl⟩ := coords_exist y
  rw [norm_qalg, recon_of, disc]
  ring

/-- **The image (page 50)**: `Γ A = {(β, γ) | β ≡ γ T₀ mod 2}`, `T₀ = b mod 2`, any `R`. -/
theorem recon_range (β γ : R) :
    (∃ y : QAlg b c, recon y = (β, γ)) ↔ ∃ s, β = γ * b + 2 * s := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, e, rfl⟩ := coords_exist y
    rw [recon_of, Prod.mk.injEq] at hy
    exact ⟨a - e * b, by rw [← hy.1, ← hy.2]; ring⟩
  · rintro ⟨s, rfl⟩
    exact ⟨algebraMap R _ (s + γ * b) + algebraMap R _ γ * AdjoinRoot.root _, by
      rw [recon_of]; ext <;> simp; ring⟩

/-- **The reconstruction is faithful** when `2` is a non-zero-divisor: `y` is known by its
trace and `γ`. -/
theorem recon_injective (h2 : ∀ x : R, 2 * x = 0 → x = 0) :
    Function.Injective (recon (b := b) (c := c)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨a, e, rfl⟩ := coords_exist y
  rw [recon_of, Prod.mk_eq_zero] at hy
  obtain ⟨h1, rfl⟩ := hy
  simp [h2 a (by simpa using h1)]

/-- A linear form on `A` in the basis `(1, U)`. -/
lemma dual_coords (x : Module.Dual R (QAlg b c)) (a e : R) :
    x (algebraMap R _ a + algebraMap R _ e * AdjoinRoot.root _) =
      a * x 1 + e * x (AdjoinRoot.root _) := by
  rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def]
  simp

/-- The coordinates `(λ, ζ)` of `x ∈ E = Ǎ` (page 49): `λ = ψ(x) = x(1)` and
`ζ = 2x − ψ(x)T ∈ L`, read on `U`. -/
noncomputable def eCoord (x : Module.Dual R (QAlg b c)) : R × R :=
  (x 1, (2 • x - x 1 • Algebra.trace R (QAlg b c)) (AdjoinRoot.root _))

lemma eCoord_eq (x : Module.Dual R (QAlg b c)) :
    eCoord x = (x 1, 2 * x (AdjoinRoot.root _) + x 1 * b) := by
  have := trace_qalg (b := b) (c := c) 0 1
  simp only [map_zero, map_one, one_mul, zero_add, mul_zero, zero_sub] at this
  simp [eCoord, this]

/-- **`Γ E = {(λ, ζ) | ζ ≡ λ T₀ mod 2}` (page 49)**, any `R`. -/
theorem eCoord_range (l ζ : R) :
    (∃ x : Module.Dual R (QAlg b c), eCoord x = (l, ζ)) ↔ ∃ s, ζ = l * b + 2 * s := by
  constructor
  · rintro ⟨x, hx⟩
    rw [eCoord_eq, Prod.mk.injEq] at hx
    exact ⟨x (AdjoinRoot.root _), by rw [← hx.1, ← hx.2]; ring⟩
  · rintro ⟨s, rfl⟩
    refine ⟨l • (qbasis b c).coord 0 + s • (qbasis b c).coord 1, ?_⟩
    rw [eCoord_eq]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, ← qbasis_zero, ← qbasis_one, Module.Basis.coord_apply,
      Module.Basis.repr_self, smul_eq_mul]
    ext <;> simp; ring

theorem eCoord_injective (h2 : ∀ x : R, 2 * x = 0 → x = 0) {x x' : Module.Dual R (QAlg b c)}
    (h : eCoord x = eCoord x') : x = x' := by
  rw [eCoord_eq, eCoord_eq, Prod.mk.injEq] at h
  obtain ⟨h1, h2'⟩ := h
  rw [h1, add_left_inj] at h2'
  have hU : x (AdjoinRoot.root _) = x' (AdjoinRoot.root _) := by
    rw [← sub_eq_zero]; exact h2 _ (by rw [mul_sub, h2', sub_self])
  refine (qbasis b c).ext fun i => ?_
  fin_cases i <;> simp [h1, hU]

/-- **The coupling (page 50)**: `2⟨y, x⟩ = λβ + γζ`. -/
theorem coupling (x : Module.Dual R (QAlg b c)) (y : QAlg b c) :
    2 * x y = (eCoord x).1 * (recon y).1 + (recon y).2 * (eCoord x).2 := by
  obtain ⟨a, e, rfl⟩ := coords_exist y
  rw [eCoord_eq, recon_of, dual_coords]
  ring

/-- The quadratic function `Q` of page 45 on `E`, in the coordinates of the splitting
`x₀ = (1, 0)`: `Q(λ, μ) = μ² + bλμ + cλ²`, i.e. `Q(x₀ + u) = u² + bu + c`. -/
noncomputable def qE (x : Module.Dual R (QAlg b c)) : R :=
  x (AdjoinRoot.root _) ^ 2 + b * x 1 * x (AdjoinRoot.root _) + c * x 1 ^ 2

/-- **The form of page 52**: `Q(λ, ζ) = (ζ² − λ²δ)/4`, without division. -/
theorem four_qE (x : Module.Dual R (QAlg b c)) :
    4 * qE x = (eCoord x).2 ^ 2 - (eCoord x).1 ^ 2 * disc b c := by
  rw [eCoord_eq, qE, disc]; ring

/-- The polar form `φ_N(y) = Tr(y)Tr(·) − Tr(y·)` of the norm, `A → E` (page 46). -/
noncomputable def phiN (y : QAlg b c) : Module.Dual R (QAlg b c) :=
  Algebra.trace R _ y • Algebra.trace R _ - Algebra.trace R _ ∘ₗ LinearMap.mulLeft R y

/-- **Page 50**: `φ_N(β, γ) = (β, −γδ)`, and **the box of page 46**: `Q(φ_N(y)) = −N(y)δ`. -/
theorem phiN_coords (y : QAlg b c) :
    eCoord (phiN y) = ((recon y).1, -((recon y).2 * disc b c)) ∧
      qE (phiN y) = -(Algebra.norm R y * disc b c) := by
  obtain ⟨a, e, rfl⟩ := coords_exist y
  have h1 : phiN (algebraMap R (QAlg b c) a + algebraMap R _ e * AdjoinRoot.root _) 1 =
      2 * a - e * b := by
    have := trace_qalg (b := b) (c := c) 1 0
    simp only [map_one, map_zero, zero_mul, add_zero] at this
    simp only [phiN, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, mul_one, trace_qalg, smul_eq_mul, this]
    ring
  have hU : phiN (algebraMap R (QAlg b c) a + algebraMap R _ e * AdjoinRoot.root _)
      (AdjoinRoot.root _) = 2 * e * c - a * b := by
    have := trace_qalg (b := b) (c := c) 0 1
    simp only [map_one, map_zero, one_mul, zero_add] at this
    simp only [phiN, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, mul_root, trace_qalg, smul_eq_mul, this]
    ring
  rw [eCoord_eq, recon_of, norm_qalg, qE, h1, hU, disc]
  constructor
  · ext <;> simp; ring
  · ring

end Reconstruction

section ReconstructionL

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]

/-- `(γ, γ') ↦ (γ ⊗ γ')(−)`, the pairing `Ľ × Ľ × L^{⊗2} → 𝒪` used in `γγ'δ`. -/
noncomputable def pairL (γ γ' : Module.Dual R L) : L ⊗[R] L →ₗ[R] R :=
  LinearMap.mul' R R ∘ₗ TensorProduct.map γ γ'

@[simp] lemma pairL_tmul (γ γ' : Module.Dual R L) (x y : L) :
    pairL γ γ' (x ⊗ₜ y) = γ x * γ' y := rfl

variable {δ : L ⊗[R] L} {τ : L} {β β' : R} {γ γ' : Module.Dual R L}

/-- **The norm `(β² − γ²δ)/4` of page 51 is defined**: if `β ≡ γ(τ)` mod `2` and
`τ² ≡ δ` mod `4`, then `β² − γ²δ ∈ 4𝒪`. -/
theorem div_norm (hδ : ∃ k, τ ⊗ₜ τ - δ = (4 : R) • k) (hβ : ∃ s, β = γ τ + 2 * s) :
    ∃ n, β ^ 2 - pairL γ γ δ = 4 * n := by
  obtain ⟨k, hk⟩ := hδ
  obtain ⟨s, rfl⟩ := hβ
  refine ⟨γ τ * s + s ^ 2 + pairL γ γ k, ?_⟩
  rw [show δ = τ ⊗ₜ τ - (4 : R) • k by rw [← hk]; abel, map_sub, map_smul, pairL_tmul,
    smul_eq_mul]
  ring

/-- **The first coordinate `(ββ' + γγ'δ)/2` of the product (page 51) is defined.** -/
theorem div_prod_fst (hδ : ∃ k, τ ⊗ₜ τ - δ = (4 : R) • k) (hβ : ∃ s, β = γ τ + 2 * s)
    (hβ' : ∃ s, β' = γ' τ + 2 * s) : ∃ m, β * β' + pairL γ γ' δ = 2 * m := by
  obtain ⟨k, hk⟩ := hδ
  obtain ⟨s, rfl⟩ := hβ
  obtain ⟨s', rfl⟩ := hβ'
  refine ⟨γ τ * γ' τ + s * γ' τ + s' * γ τ + 2 * s * s' - 2 * pairL γ γ' k, ?_⟩
  rw [show δ = τ ⊗ₜ τ - (4 : R) • k by rw [← hk]; abel, map_sub, map_smul, pairL_tmul,
    smul_eq_mul]
  ring

/-- Symmetry of `Ľ ⊗ Ľ` for `L` invertible: `γ'(τ)γ = γ(τ)γ'`. -/
lemma dual_symm [Module.Invertible R L] (γ γ' : Module.Dual R L) (τ : L) :
    γ' τ • γ = γ τ • γ' := by
  have := congrArg (fun z => TensorProduct.rid R _ (LinearMap.lTensor (Module.Dual R L)
    (Module.Dual.eval R L τ) z)) (Module.Invertible.tmul_comm (R := R) (m₁ := γ) (m₂ := γ'))
  simpa using this

/-- **The second coordinate `(βγ' + γβ')/2` of the product (page 51) is defined**, for `L`
invertible. -/
theorem div_prod_snd [Module.Invertible R L] (hβ : ∃ s, β = γ τ + 2 * s)
    (hβ' : ∃ s, β' = γ' τ + 2 * s) : ∃ g : Module.Dual R L, β • γ' + β' • γ = (2 : R) • g := by
  obtain ⟨s, rfl⟩ := hβ
  obtain ⟨s', rfl⟩ := hβ'
  refine ⟨γ τ • γ' + s • γ' + s' • γ, ?_⟩
  rw [add_smul, add_smul, dual_symm γ γ' τ]
  module

/-- **The product stays in `Γ A`**: if `2` is regular, the halves `β''`, `γ''` satisfy
`β'' ≡ γ''(τ)` mod `2` again (page 51, « il le vérifie à chaque étape »). -/
theorem div_prod_mem (h2 : ∀ x : R, 2 * x = 0 → x = 0) (hδ : ∃ k, τ ⊗ₜ τ - δ = (4 : R) • k)
    (hβ : ∃ s, β = γ τ + 2 * s) (hβ' : ∃ s, β' = γ' τ + 2 * s) {β'' : R}
    {γ'' : Module.Dual R L} (h₁ : 2 * β'' = β * β' + pairL γ γ' δ)
    (h₂ : (2 : R) • γ'' = β • γ' + β' • γ) : ∃ s, β'' = γ'' τ + 2 * s := by
  obtain ⟨k, hk⟩ := hδ
  obtain ⟨s, rfl⟩ := hβ
  obtain ⟨s', rfl⟩ := hβ'
  have hτ := LinearMap.congr_fun h₂ τ
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at hτ
  rw [show δ = τ ⊗ₜ τ - (4 : R) • k by rw [← hk]; abel, map_sub, map_smul, pairL_tmul,
    smul_eq_mul] at h₁
  refine ⟨s * s' - pairL γ γ' k, ?_⟩
  rw [← sub_eq_zero]
  apply h2
  linear_combination h₁ - hτ

/-- **The form `(ζ² − λ²δ)/4` of page 52 is defined**, for `L` invertible: if `ζ ≡ λτ`
mod `2L`, then `ζ² − λ²δ ∈ 4L^{⊗2}`. -/
theorem div_qform [Module.Invertible R L] (hδ : ∃ k, τ ⊗ₜ τ - δ = (4 : R) • k) {l : R} {ζ : L}
    (hζ : ∃ a, ζ = l • τ + (2 : R) • a) : ∃ q, ζ ⊗ₜ ζ - l ^ 2 • δ = (4 : R) • q := by
  obtain ⟨k, hk⟩ := hδ
  obtain ⟨a, rfl⟩ := hζ
  refine ⟨l ^ 2 • k + l • (τ ⊗ₜ a) + a ⊗ₜ a, ?_⟩
  rw [show δ = τ ⊗ₜ τ - (4 : R) • k by rw [← hk]; abel]
  simp only [add_tmul, tmul_add, ← smul_tmul', tmul_smul]
  rw [Module.Invertible.tmul_comm (m₁ := a) (m₂ := τ)]
  module

end ReconstructionL

end Grothendieck.Folder84
