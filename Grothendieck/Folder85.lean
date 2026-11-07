module

public import Mathlib
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# Folder 85: the invariant of a rotation of order 5 (pages 10, 27, 30, 40)

**Partial, and chosen.** The finding `85-a5-pgl2-moduli-spec-z-phi`
(`src/content/findings.ts`) states the theorem of page 40 of the reading
(`transcripts/85/85.modern.tex`):

> For any scheme `S`, the groupoid of pairs `(G, φ)`, `G` a form of `PGL₂` over
> `S` and `φ : 𝔄₅ → G` a monomorphism, is rigid, and `φ ↦ A(φ(π))` (`π` a
> standard 5-cycle) makes its functor of isomorphism classes representable by
> `Spec ℤ[T]/(T² + T − 1)`.

Rigidity, representability and the passage to forms of `PGL₂` are out of
reach here. What this file proves is the computation under the statement:
the value `A(φ(π))` is a root of `T² + T − 1`, and, conversely, a root is
attained.

The invariant. For `PGL₂` the reading (pages 23 and 27) takes
`A(v) = (Tr v)² / det v − 2` for a lift `v ∈ GL₂`. Here `invA g` is this
expression for a `2 × 2` matrix `g` over a commutative ring `R`, with
`Ring.inverse` for the division; it is used only when `det g` is a unit. It
does not depend on the lift (`invA_smul`).

Order 5 on every fibre. For a matrix with invertible determinant, "the image
of `g` in `PGL₂(k(s))` is not `1`, for every point `s`" says that `g 0 1`,
`g 1 0` and `g 0 0 − g 1 1` do not all vanish in any residue field, that is,
that they generate the unit ideal (`NullePartScalaire`). Since 5 is prime,
"of order 5 on every fibre" is then `g⁵` scalar.

* `pow_five_eq`: `g⁵ = x₅ g + y₅` with `x₅ = t⁴ − 3dt² + d²` (Cayley–Hamilton,
  iterated), `t = Tr g`, `d = det g`; `coeff_eq`: `x₅ = d² (A² + A − 1)`.
* `sq_add_sub_of_pow_five` (the finding's computation): `g` nowhere scalar,
  `det g` a unit, `g⁵` scalar ⟹ `A(g)² + A(g) − 1 = 0`. Over any commutative
  ring: no hypothesis on 2, 5, reducedness.
* `pow_five_of_sq_add_sub`: the converse, without the nowhere-scalar hypothesis.
* `invA_sq`: `A(g²) = A(g)² − 2`, hence `A(g²) = −1 − A(g)` for a root
  (`invA_sq_of_root`), the corollary of page 40.
* The model (`sModel`, `pModel`): over any ring with `ζ⁴ + ζ³ + ζ² + ζ + 1 = 0`,
  `s = !![0, −1; 1, 0]` and `p = !![ζ, 1; 0, ζ⁴]` satisfy `s²`, `(sp)³`, `p⁵`
  scalar, all three nowhere scalar, with `A(p) = ζ² + ζ³` a root of
  `T² + T − 1`; `exists_model_adjoinRoot` instantiates it over `ℤ[ζ₅]`. These
  are the relations of the (2, 3, 5) triangle group, which is `𝔄₅`; the
  homomorphism from `𝔄₅` and its injectivity are not formalised.

What the formalisation found: the computation holds over every base, in
characteristics 2, 3 and 5 included; in characteristic 5 the model gives the
unipotent `p` (`ζ = 1`, `A = 2`). The model lives in the split `PGL₂` over
`ℤ[ζ₅]`, not over `ℤ[T]/(T² + T − 1)`: over `ℚ(√5)`, a real field, the split
`PGL₂` contains no `𝔄₅` (the criterion the reading cites from memory), so a
model over `ℤ[φ]` needs a non-split form, which is why the theorem speaks of
forms of `PGL₂`.

## Representations of `G₂` (pages 4 to 10), finding `85-g2-pgl2-moduli-over-z`

**Partial, and chosen.** `G₂ = ⟨τ₀, τ₁, τ₂ | τᵢ², (τ₀τ₂)²⟩`, `ρ₀ = τ₀τ₁`,
`ρ₁ = τ₁τ₂`, `α₀ = A(ρ₀)`, `α₁ = A(ρ₁)`. A homomorphism to `PGL₂(R)` is given by
`τᵢ ∈ GL₂(R)` with `τᵢ²` and `(τ₀τ₂)²` scalar. Condition (*) of page 4 at a
point (`ρ₀² ≠ 1`, `ρ₁² ≠ 1`, `ρ₀ρ₁ ≠ ρ₁ρ₀` in `PGL₂(k)`) is `Star`;
« at every point » is `Star` after reduction modulo every maximal ideal.

* `discr_isUnit_of_star` (part 1, any ring): (*) at every point forces the `τᵢ`
  and `τ₀τ₂` to be traceless and `(α₀ + 2)(α₁ + 2)(α₀ + α₁)` to be a unit;
  `star_of_discr_isUnit` is the converse. The computation: `α₀ + 2 = Tr(τ₀τ₁)²/d₀d₁`,
  `α₁ + 2 = Tr(τ₁τ₂)²/d₁d₂`, `α₀ + α₁ = −Tr(τ₀τ₁τ₂)²/d₀d₁d₂` (`invA_add_invA`), and
  `ρ₀ρ₁ − ρ₁ρ₀ = −Tr(τ₀τ₁τ₂) τ₁` (`commutator_eq`).
* `rigid` (part 2, rigidity, any ring): an element of `GL₂(R)` normalising each
  `τᵢ` up to a scalar is scalar.
* `conj_normalForm`, `conj_of_same_invariants` (part 2, conjugacy): over a field
  containing a root `ℓ` of `T² − α₀T + 1`, two triples with the same `(α₀, α₁)` are
  conjugate in `PGL₂`; each is conjugate to the normal form.
* `normalForm`, `exists_normalForm_adjoinRoot` (part 3): for any `α₀, α₁` with the
  discriminant a unit, an explicit triple in `GL₂(R[ℓ])`, `R[ℓ] = R[T]/(T² − α₀T + 1)`,
  with invariants `(α₀, α₁)` and (*) at every point.
* Orders (pages 6–7, 29–31): `gⁿ = xₙ g − d xₙ₋₁` (`pow_succ_eq`); for `g` nowhere
  scalar, `gⁿ` is scalar iff `xₙ = 0` and `gⁿ` is nowhere scalar iff `xₙ` is a unit;
  `x_{2k+1} = d^k P_{2k+1}(A)`, `x_{2k+2} = t d^k P_{2k+2}(A)` with `chebP` the
  recursion of the order-5 computation; `P₃ = A + 1`, `P₄ = A`, `P₅ = A² + A − 1`,
  `P₆ = A² − 1`, `P₇ = A³ + A² − 2A − 1`. Exact orders 3, 4, 6 on every fibre:
  `isScalar_pow_three_iff`, `order_four_iff` (needs `2` invertible),
  `order_six_iff` (needs `6` invertible), condition c) of the corollary.

Not formalised: forms of `PGL₂` and descent from `R[ℓ]` to `R` (the realisation
over `R` itself lives in a form, not in the split group in general); conjugacy
over a general base or over a field without `ℓ`; the identification of `Pₙ` with
`Fₙ = ∏_{d ∣ n, d ≥ 3} Ψ_d` for general `n`.

## Representations of `𝔻_∞` (pages 16 to 20), finding `85-dinfty-torsor-classification`

**Partial: the split group over a field.** A homomorphism `𝔻_∞ → PGL₂(K)` with `u² ≠ 1`,
`u = φ(τ₀τ₁)`, is given by `t₀, t₁ ∈ GL₂(K)` with `t₀²`, `t₁²` scalar and `(t₀t₁)²` not
scalar (`DRep`); conjugacy in `PGL₂(K)` is `PConj`.

* `exists_normal`: in a basis `(v, uv)`, `u` is the companion matrix of `T² − τT + d` and
  `t₀ = invD τ d p r`, `−det t₀ = p² + τpr + dr²` (the norm form of `K[u]`).
* `dinfty_conj_iff` (the classification): two representations are conjugate iff they have
  the same `α = A(u)` and `det t₀` in the same class of `K^×/K^×²`. The step is Hilbert 90
  for `K[u]`, split, non-split or non-reduced (`hilbert90`), with a case for characteristic 2.
* `exists_dinfty_iff`: the pair `(α, δ)` occurs iff `α + 2 ≠ 0` and `δ ≠ 0` is a value of
  `p² + (α+2)pr + (α+2)r²`.
* `centralizer_iff`, `det_commD`, `commD_not_isScalar` (page 19, `2 ≠ 0`): the centraliser in
  `PGL₂(K)` is `{1, [t₀, t₁]}`, `det [t₀, t₁] = det u · (2 − α)`: two elements if `ρ = 2 − α ≠ 0`,
  one if `α = 2` — `₂𝒰_ρ(K)`, Corollaries 1 and 2.
* `dinfty_not_conj_rat`: over `ℚ`, `α = −6` (`ρ = 8`, `𝒰_ρ ≅ 𝔾_m`) is carried by two
  representations that are not conjugate, `det t₀ = −1` and `det s₀ = 1`.

What the formalisation found: the equivalence of page 17 as read, with `R` a torsor under
`𝒰_{2−α}`, is false. Over `ℚ`, `H¹(ℚ, 𝔾_m) = 0` would leave one class for `α = −6`, and
automorphisms of `PGL₂` over a field are inner, so `dinfty_not_conj_rat` gives two; and the
automorphism group of an object of `C′` is `𝒰_ρ(S)`, against `₂𝒰_ρ` of page 19, which
`centralizer_iff` confirms. The classes match torsors under `₂𝒰_ρ` (`μ₂` for `ρ`
invertible). Also, « `u_s² ≠ 1`, that is `α + 2` invertible » is not an equivalence:
`t₁ = t₀` gives `u = 1`, `α = 2` (`dinfty_add_two_not_iff`). Forms of `PGL₂`, local rings
and torsors over `S` are not formalised.
-/

namespace Grothendieck.Folder85

open Matrix

variable {R : Type*} [CommRing R]

/-- The invariant `A` of pages 23 and 27 for `PGL₂`: `(Tr g)² / det g − 2`,
for a lift `g ∈ GL₂(R)`. -/
noncomputable def invA (g : Matrix (Fin 2) (Fin 2) R) : R :=
  g.trace ^ 2 * Ring.inverse g.det - 2

/-- `g` is nowhere scalar: its image in `PGL₂(k(s))` is not `1` for any point
`s` of `Spec R`, that is, `b`, `c`, `a − d` generate the unit ideal. -/
def NullePartScalaire (g : Matrix (Fin 2) (Fin 2) R) : Prop :=
  Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1} = ⊤

theorem nullePartScalaire_of_isUnit (g : Matrix (Fin 2) (Fin 2) R) (hu : IsUnit (g 0 1)) :
    NullePartScalaire g :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu

/-- The unit-ideal argument: if `x` kills `b`, `c`, `a − d` of a nowhere-scalar `g`,
then `x = 0`. -/
theorem eq_zero_of_nps {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g) {x : R}
    (h1 : x * g 0 1 = 0) (h2 : x * g 1 0 = 0) (h3 : x * (g 0 0 - g 1 1) = 0) : x = 0 := by
  have h : (1 : R) ∈ Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1} := by rw [hg]; trivial
  obtain ⟨a, b, c, e⟩ := Submodule.mem_span_triple.1 h
  simp only [smul_eq_mul] at e
  linear_combination (-x) * e + a * h1 + b * h2 + c * h3

/-- `A` depends only on the image in `PGL₂`: `A(μ g) = A(g)` for a unit `μ`. -/
theorem invA_smul (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) {μ : R} (hμ : IsUnit μ) :
    invA (μ • g) = invA g := by
  have hd : (μ • g).det = μ ^ 2 * g.det := by simp
  have ht : (μ • g).trace = μ * g.trace := by simp [Matrix.trace_smul]
  have h1 := Ring.inverse_mul_cancel _ (hd ▸ (hμ.pow 2).mul hg)
  have h2 := Ring.inverse_mul_cancel _ hg
  unfold invA
  rw [ht]
  rw [hd] at h1 ⊢
  linear_combination g.trace ^ 2 * (-(μ ^ 2 * Ring.inverse (μ ^ 2 * g.det)) * h2
    + Ring.inverse g.det * h1)

/-- Cayley–Hamilton iterated: `g⁵ = x₅ g + y₅` with `x₅ = t⁴ − 3dt² + d²`. -/
theorem pow_five_eq (g : Matrix (Fin 2) (Fin 2) R) :
    g ^ 5 = (g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2) • g
      + (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

/-- `x₅ = d² (A² + A − 1)`. -/
theorem coeff_eq (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) :
    g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2
      = g.det ^ 2 * (invA g ^ 2 + invA g - 1) := by
  have h := Ring.mul_inverse_cancel _ hg
  unfold invA
  linear_combination (-(g.trace ^ 4 * (g.det * Ring.inverse g.det + 1))
    + 3 * g.trace ^ 2 * g.det) * h

/-- **Pages 10, 30, 40.** If `g ∈ GL₂(R)` is nowhere scalar and `g⁵` is scalar
(the image of `g` in `PGL₂` has order 5 on every fibre), then `A(g)` is a root
of `T² + T − 1`. Over any commutative ring. -/
theorem sq_add_sub_of_pow_five (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hns : NullePartScalaire g)
    {c : R} (h5 : g ^ 5 = c • (1 : Matrix (Fin 2) (Fin 2) R)) :
    invA g ^ 2 + invA g - 1 = 0 := by
  set x := g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2 with hx
  have e := pow_five_eq g
  rw [h5] at e
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  simp at e01 e10 e00 e11
  have h1 : x = 0 := eq_zero_of_nps hns (by linear_combination -e01) (by linear_combination -e10)
    (by linear_combination e11 - e00)
  rw [hx, coeff_eq g hg] at h1
  exact ((hg.pow 2).mul_right_eq_zero).1 h1

/-- The converse: if `A(g)² + A(g) − 1 = 0`, then `g⁵` is scalar. No
hypothesis on `g` besides `det g` a unit. -/
theorem pow_five_of_sq_add_sub (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hA : invA g ^ 2 + invA g - 1 = 0) :
    g ^ 5 = (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) •
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [pow_five_eq g, coeff_eq g hg, hA]
  simp

/-- `A(g²) = A(g)² − 2` (the polynomial `S₂`). -/
theorem invA_sq (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) :
    invA (g ^ 2) = invA g ^ 2 - 2 := by
  have ht : (g ^ 2).trace = g.trace ^ 2 - 2 * g.det := by
    simp [sq, trace_fin_two, det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h := Ring.mul_inverse_cancel _ hg
  unfold invA
  rw [ht, det_pow, ← Ring.inverse_pow]
  linear_combination (-4 * g.trace ^ 2 * Ring.inverse g.det
    + 4 * (g.det * Ring.inverse g.det + 1)) * h

/-- **Corollary of page 40.** For a root, `A(g²) = −1 − A(g)`, the other root. -/
theorem invA_sq_of_root (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hA : invA g ^ 2 + invA g - 1 = 0) :
    invA (g ^ 2) = -1 - invA g := by
  rw [invA_sq g hg]; linear_combination hA

section Model

variable (ζ : R)

/-- The involution of the model. -/
def sModel : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]

/-- The rotation of order 5 of the model. -/
def pModel : Matrix (Fin 2) (Fin 2) R := !![ζ, 1; 0, ζ ^ 4]

theorem sModel_sq : (sModel : Matrix (Fin 2) (Fin 2) R) ^ 2 = (-1 : R) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, sModel, Matrix.mul_apply, Fin.sum_univ_two]

theorem sModel_nullePartScalaire : NullePartScalaire (sModel : Matrix (Fin 2) (Fin 2) R) :=
  nullePartScalaire_of_isUnit _ (by simp [sModel])

theorem pModel_nullePartScalaire : NullePartScalaire (pModel ζ) :=
  nullePartScalaire_of_isUnit _ (by simp [pModel])

variable {ζ} (h : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
include h

theorem zeta_pow_five : ζ ^ 5 = 1 := by linear_combination (ζ - 1) * h

theorem det_pModel : (pModel ζ).det = 1 := by
  simp [pModel, det_fin_two]; linear_combination zeta_pow_five h

/-- `A(p) = ζ² + ζ³` (that is `ζ² + ζ⁻²`). -/
theorem invA_pModel : invA (pModel ζ) = ζ ^ 2 + ζ ^ 3 := by
  unfold invA
  rw [det_pModel h, Ring.inverse_one]
  simp [pModel, trace_fin_two]
  linear_combination (2 + ζ ^ 3) * zeta_pow_five h

theorem invA_pModel_root : invA (pModel ζ) ^ 2 + invA (pModel ζ) - 1 = 0 := by
  rw [invA_pModel h]; linear_combination h + (2 + ζ) * zeta_pow_five h

/-- `p⁵` is scalar, by `pow_five_of_sq_add_sub`. -/
theorem pModel_pow_five : ∃ c : R, pModel ζ ^ 5 = c • (1 : Matrix (Fin 2) (Fin 2) R) :=
  ⟨_, pow_five_of_sq_add_sub _ (by rw [det_pModel h]; exact isUnit_one) (invA_pModel_root h)⟩

theorem sp_sq : sModel * pModel ζ * (sModel * pModel ζ) = sModel * pModel ζ - 1 := by
  have h5 := zeta_pow_five h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sModel, pModel, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h5 | linear_combination -h5

/-- `(sp)³ = −1`: the product `sp` has order 3 in `PGL₂`. -/
theorem sp_cube : (sModel * pModel ζ) ^ 3 = (-1 : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have e := sp_sq h
  set t := sModel * pModel ζ
  calc t ^ 3 = t * (t * t) := by rw [pow_succ, pow_two, mul_assoc]
    _ = t * t - t := by rw [e, mul_sub, mul_one, e]
    _ = (-1 : R) • 1 := by rw [e]; simp

theorem sp_nullePartScalaire : NullePartScalaire (sModel * pModel ζ) := by
  refine nullePartScalaire_of_isUnit _ ?_
  have : (sModel * pModel ζ : Matrix (Fin 2) (Fin 2) R) 0 1 = -ζ ^ 4 := by
    simp [sModel, pModel, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this]
  exact IsUnit.of_mul_eq_one (-ζ) (by linear_combination zeta_pow_five h)

end Model

/-- The model over `ℤ[ζ₅] = ℤ[X]/(X⁴ + X³ + X² + X + 1)`: a rotation `p` of order 5
on every fibre, `s` of order 2, `sp` of order 3, with `A(p)` a root of
`T² + T − 1`. -/
theorem exists_model_adjoinRoot :
    let f : Polynomial ℤ := Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2
      + Polynomial.X + 1
    let ζ := AdjoinRoot.root f
    (sModel : Matrix (Fin 2) (Fin 2) (AdjoinRoot f)) ^ 2 = (-1 : AdjoinRoot f) • 1 ∧ (sModel * pModel ζ) ^ 3 = (-1 : AdjoinRoot f) • 1 ∧
      (∃ c : AdjoinRoot f, pModel ζ ^ 5 = c • 1) ∧
      NullePartScalaire (sModel : Matrix (Fin 2) (Fin 2) (AdjoinRoot f)) ∧
      NullePartScalaire (pModel ζ) ∧ NullePartScalaire (sModel * pModel ζ) ∧
      invA (pModel ζ) ^ 2 + invA (pModel ζ) - 1 = 0 := by
  intro f ζ
  have h : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by simpa [f] using AdjoinRoot.eval₂_root f
  exact ⟨sModel_sq, sp_cube h, pModel_pow_five h, sModel_nullePartScalaire,
    pModel_nullePartScalaire ζ, sp_nullePartScalaire h, invA_pModel_root h⟩

/-! ## Representations of `G₂` in `PGL₂` (pages 4 to 10, 29 to 31)

General lemmas on `2 × 2` matrices first. -/


/-- `M` is scalar. -/
def IsScalar (M : Matrix (Fin 2) (Fin 2) R) : Prop := ∃ c : R, M = c • 1

theorem isScalar_iff (M : Matrix (Fin 2) (Fin 2) R) :
    IsScalar M ↔ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  constructor
  · rintro ⟨c, rfl⟩; simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨M 0 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

/-- Cayley–Hamilton in rank 2. -/
theorem sq_eq_trace (g : Matrix (Fin 2) (Fin 2) R) :
    g * g = g.trace • g - g.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

/-- `XY + YX = (Tr X) Y + (Tr Y) X + (Tr XY − Tr X Tr Y)`. -/
theorem mul_add_mul (X Y : Matrix (Fin 2) (Fin 2) R) :
    X * Y + Y * X = X.trace • Y + Y.trace • X
      + ((X * Y).trace - X.trace * Y.trace) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two] <;> ring

/-- `det (XY − YX)`, from the trace invariants. -/
theorem det_commutator (X Y : Matrix (Fin 2) (Fin 2) R) :
    (X * Y - Y * X).det = -(X.trace ^ 2 * Y.det + Y.trace ^ 2 * X.det + (X * Y).trace ^ 2
      - X.trace * Y.trace * (X * Y).trace - 4 * X.det * Y.det) := by
  simp [det_fin_two, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem nps_iff_maximal (g : Matrix (Fin 2) (Fin 2) R) :
    NullePartScalaire g ↔ ∀ m : Ideal R, m.IsMaximal →
      ¬ (g 0 1 ∈ m ∧ g 1 0 ∈ m ∧ g 0 0 - g 1 1 ∈ m) := by
  constructor
  · rintro h m hm ⟨h1, h2, h3⟩
    refine hm.ne_top (top_le_iff.1 ?_)
    rw [← h, Ideal.span_le]
    simp [Set.insert_subset_iff, h1, h2, h3]
  · intro h
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact h m hm ⟨hle (Ideal.subset_span (by simp)), hle (Ideal.subset_span (by simp)),
      hle (Ideal.subset_span (by simp))⟩

theorem isUnit_iff_maximal (x : R) : IsUnit x ↔ ∀ m : Ideal R, m.IsMaximal → x ∉ m := by
  constructor
  · intro hx m hm hxm; exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hxm hx)
  · intro h
    by_contra hx
    have hne : Ideal.span {x} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact h m hm (hle (Ideal.mem_span_singleton_self x))

/-- Over a field, « nowhere scalar » is « not scalar ». -/
theorem nps_iff_not_isScalar {K : Type*} [Field K] (g : Matrix (Fin 2) (Fin 2) K) :
    NullePartScalaire g ↔ ¬ IsScalar g := by
  rw [isScalar_iff, NullePartScalaire]
  constructor
  · rintro h ⟨h1, h2, h3⟩
    rw [h1, h2, h3, sub_self] at h
    simp at h
  · intro h
    rcases Ideal.eq_bot_or_top (Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1}) with hb | ht
    · rw [Ideal.span_eq_bot] at hb
      exact absurd ⟨hb _ (by simp), hb _ (by simp), sub_eq_zero.1 (hb _ (by simp))⟩ h
    · exact ht

/-- For `g` nowhere scalar, `x g + y` is scalar if and only if `x = 0`. -/
theorem isScalar_smul_add_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (x y : R) : IsScalar (x • g + y • (1 : Matrix (Fin 2) (Fin 2) R)) ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := (isScalar_iff _).1 h
    simp at h1 h2 h3
    exact eq_zero_of_nps hg h1 h2 (by linear_combination h3)
  · rintro rfl; exact ⟨y, by simp⟩

/-- For `g` nowhere scalar, `x g + y` is nowhere scalar if and only if `x` is a unit. -/
theorem nps_smul_add_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (x y : R) : NullePartScalaire (x • g + y • (1 : Matrix (Fin 2) (Fin 2) R)) ↔ IsUnit x := by
  rw [nps_iff_maximal, isUnit_iff_maximal]
  rw [nps_iff_maximal] at hg
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_apply_eq, mul_zero, add_zero, mul_one]
  refine forall₂_congr fun m hm => ?_
  have e : x * g 0 0 + y - (x * g 1 1 + y) = x * (g 0 0 - g 1 1) := by ring
  rw [e]
  have := hg m hm
  constructor
  · intro h hx
    exact h ⟨m.mul_mem_right _ hx, m.mul_mem_right _ hx, m.mul_mem_right _ hx⟩
  · rintro hx ⟨h1, h2, h3⟩
    have p := hm.isPrime
    exact this ⟨(p.mem_or_mem h1).resolve_left hx, (p.mem_or_mem h2).resolve_left hx,
      (p.mem_or_mem h3).resolve_left hx⟩


theorem trace_zero_entry {g : Matrix (Fin 2) (Fin 2) R} (h : g.trace = 0) : g 1 1 = -g 0 0 := by
  rw [trace_fin_two] at h; linear_combination h

theorem trace_eq_zero_of_isScalar_mul {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (h : IsScalar (g * g)) : g.trace = 0 := by
  rw [sq_eq_trace, sub_eq_add_neg, ← neg_smul] at h
  exact (isScalar_smul_add_iff hg _ _).1 h

theorem mul_self_of_trace_zero {g : Matrix (Fin 2) (Fin 2) R} (h : g.trace = 0) :
    g * g = (-g.det) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [sq_eq_trace, h, zero_smul, zero_sub, neg_smul]

theorem nps_of_isUnit_trace_mul {M Z : Matrix (Fin 2) (Fin 2) R} (hZ : Z.trace = 0)
    (h : IsUnit (M * Z).trace) : NullePartScalaire M := by
  have e : (M * Z).trace = Z 1 0 * M 0 1 + Z 0 1 * M 1 0 + Z 0 0 * (M 0 0 - M 1 1) := by
    simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, trace_zero_entry hZ]; ring
  refine Ideal.eq_top_of_isUnit_mem _ ?_ h
  rw [e]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-! ### Powers -/

/-- `x₀ = 0`, `x₁ = 1`, `xₙ₊₂ = t xₙ₊₁ − d xₙ`. -/
def powCoeff (t d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * powCoeff t d (n + 1) - d * powCoeff t d n

theorem pow_succ_eq (g : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    g ^ (n + 1) = powCoeff g.trace g.det (n + 1) • g
      - (g.det * powCoeff g.trace g.det n) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  induction n with
  | zero => simp [powCoeff]
  | succ n ih =>
    rw [pow_succ, ih, sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, sq_eq_trace]
    have e : powCoeff g.trace g.det (n + 1 + 1)
        = g.trace * powCoeff g.trace g.det (n + 1) - g.det * powCoeff g.trace g.det n := rfl
    rw [e]
    generalize powCoeff g.trace g.det (n + 1) = x
    generalize powCoeff g.trace g.det n = y
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem isScalar_pow_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g) (n : ℕ) :
    IsScalar (g ^ (n + 1)) ↔ powCoeff g.trace g.det (n + 1) = 0 := by
  rw [pow_succ_eq, sub_eq_add_neg, ← neg_smul]; exact isScalar_smul_add_iff hg _ _

theorem nps_pow_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g) (n : ℕ) :
    NullePartScalaire (g ^ (n + 1)) ↔ IsUnit (powCoeff g.trace g.det (n + 1)) := by
  rw [pow_succ_eq, sub_eq_add_neg, ← neg_smul]; exact nps_smul_add_iff hg _ _

/-- The polynomials of the order criterion, in the variable `A`:
`P₀ = 0`, `P₁ = 1`, `Pₙ₊₂ = Pₙ₊₁ − Pₙ` for `n` even and `(A + 2) Pₙ₊₁ − Pₙ` for `n` odd. -/
def chebP (a : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => (if n % 2 = 0 then 1 else a + 2) * chebP a (n + 1) - chebP a n

theorem powCoeff_eq_chebP (t d a : R) (h : t ^ 2 = (a + 2) * d) (k : ℕ) :
    powCoeff t d (2 * k + 1) = d ^ k * chebP a (2 * k + 1) ∧
      powCoeff t d (2 * k + 2) = t * d ^ k * chebP a (2 * k + 2) := by
  induction k with
  | zero => simp [powCoeff, chebP]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e3 : powCoeff t d (2 * (k + 1) + 1)
        = t * powCoeff t d (2 * k + 2) - d * powCoeff t d (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring]; rfl
    have c3 : chebP a (2 * (k + 1) + 1) = (a + 2) * chebP a (2 * k + 2) - chebP a (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring]
      simp only [chebP]
      rw [ite_eq_right (by omega)]
    have e4 : powCoeff t d (2 * (k + 1) + 2)
        = t * powCoeff t d (2 * (k + 1) + 1) - d * powCoeff t d (2 * k + 2) := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring]; rfl
    have c4 : chebP a (2 * (k + 1) + 2) = chebP a (2 * (k + 1) + 1) - chebP a (2 * k + 2) := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring]
      simp only [chebP]
      rw [ite_eq_left (by omega), one_mul]
      rfl
    have hx3 : powCoeff t d (2 * (k + 1) + 1) = d ^ (k + 1) * chebP a (2 * (k + 1) + 1) := by
      rw [e3, h1, h2, c3]; linear_combination d ^ k * chebP a (2 * k + 2) * h
    refine ⟨hx3, ?_⟩
    rw [e4, hx3, h2, c4]; ring

theorem chebP_three (a : R) : chebP a 3 = a + 1 := by simp [chebP]; ring
theorem chebP_four (a : R) : chebP a 4 = a := by simp [chebP]; ring
theorem chebP_five (a : R) : chebP a 5 = a ^ 2 + a - 1 := by simp [chebP]; ring
theorem chebP_six (a : R) : chebP a 6 = a ^ 2 - 1 := by simp [chebP]; ring
theorem chebP_seven (a : R) : chebP a 7 = a ^ 3 + a ^ 2 - 2 * a - 1 := by simp [chebP]; ring

theorem trace_sq_eq (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) :
    g.trace ^ 2 = (invA g + 2) * g.det := by
  have h := Ring.inverse_mul_cancel _ hg
  unfold invA; linear_combination (-(g.trace ^ 2)) * h

/-- **Pages 29 and 31, odd orders.** For `g` nowhere scalar with invertible determinant,
`g^(2k+1)` is scalar if and only if `P_{2k+1}(A(g)) = 0`. -/
theorem isScalar_pow_odd_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (hd : IsUnit g.det) (k : ℕ) :
    IsScalar (g ^ (2 * k + 1)) ↔ chebP (invA g) (2 * k + 1) = 0 := by
  rw [isScalar_pow_iff hg, (powCoeff_eq_chebP _ _ _ (trace_sq_eq g hd) k).1]
  exact (hd.pow k).mul_right_eq_zero

/-- Even orders: if moreover `Tr g` is a unit, `g^(2k+2)` is scalar if and only if
`P_{2k+2}(A(g)) = 0`. -/
theorem isScalar_pow_even_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (hd : IsUnit g.det) (ht : IsUnit g.trace) (k : ℕ) :
    IsScalar (g ^ (2 * k + 2)) ↔ chebP (invA g) (2 * k + 2) = 0 := by
  rw [isScalar_pow_iff hg, (powCoeff_eq_chebP _ _ _ (trace_sq_eq g hd) k).2]
  exact (ht.mul (hd.pow k)).mul_right_eq_zero

/-- **Order 3** (page 30): `g³` scalar iff `A(g) = −1`. -/
theorem isScalar_pow_three_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (hd : IsUnit g.det) : IsScalar (g ^ 3) ↔ invA g = -1 := by
  rw [show 3 = 2 * 1 + 1 from rfl, isScalar_pow_odd_iff hg hd, chebP_three]
  constructor <;> intro h <;> linear_combination h

/-- **Order 4, exactly, on every fibre** (pages 6–7, 30): `g⁴` scalar and `g²` nowhere scalar
iff `A(g) = 0` and `2` is invertible. -/
theorem order_four_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (hd : IsUnit g.det) :
    (IsScalar (g ^ 4) ∧ NullePartScalaire (g ^ 2)) ↔ (invA g = 0 ∧ IsUnit (2 : R)) := by
  have hts := trace_sq_eq g hd
  have h2 : NullePartScalaire (g ^ 2) ↔ IsUnit g.trace := by
    rw [nps_pow_iff hg 1]; simp [powCoeff]
  rw [h2]
  constructor
  · rintro ⟨h4, ht⟩
    rw [show 4 = 2 * 1 + 2 from rfl, isScalar_pow_even_iff hg hd ht, chebP_four] at h4
    refine ⟨h4, ?_⟩
    rw [h4, zero_add] at hts
    have : IsUnit (2 * g.det) := hts ▸ ht.pow 2
    exact isUnit_of_mul_isUnit_left this
  · rintro ⟨ha, h2u⟩
    have ht : IsUnit g.trace := by
      rw [ha, zero_add] at hts
      exact (isUnit_pow_iff two_ne_zero).1 (hts ▸ h2u.mul hd)
    refine ⟨?_, ht⟩
    rw [show 4 = 2 * 1 + 2 from rfl, isScalar_pow_even_iff hg hd ht, chebP_four, ha]

/-- **Order 6, exactly, on every fibre**: `g⁶` scalar, `g²` and `g³` nowhere scalar
iff `A(g) = 1` and `6` is invertible. -/
theorem order_six_iff {g : Matrix (Fin 2) (Fin 2) R} (hg : NullePartScalaire g)
    (hd : IsUnit g.det) :
    (IsScalar (g ^ 6) ∧ NullePartScalaire (g ^ 2) ∧ NullePartScalaire (g ^ 3)) ↔
      (invA g = 1 ∧ IsUnit (6 : R)) := by
  have hts := trace_sq_eq g hd
  have h2 : NullePartScalaire (g ^ 2) ↔ IsUnit g.trace := by
    rw [nps_pow_iff hg 1]; simp [powCoeff]
  have h3 : NullePartScalaire (g ^ 3) ↔ IsUnit (invA g + 1) := by
    rw [nps_pow_iff hg 2, show 2 + 1 = 2 * 1 + 1 from rfl,
      (powCoeff_eq_chebP _ _ _ hts 1).1, chebP_three, pow_one]
    exact ⟨fun h => isUnit_of_mul_isUnit_right h, fun h => hd.mul h⟩
  rw [h2, h3]
  constructor
  · rintro ⟨h6, ht, ha1⟩
    rw [show 6 = 2 * 2 + 2 from rfl, isScalar_pow_even_iff hg hd ht, chebP_six] at h6
    have ha : invA g = 1 := by
      linear_combination ha1.mul_left_eq_zero.1
        (by linear_combination h6 : (invA g - 1) * (invA g + 1) = 0)
    refine ⟨ha, ?_⟩
    rw [ha] at hts ha1
    have h3u : IsUnit (3 * g.det) := by
      rw [show (1 + 2 : R) = 3 by norm_num] at hts; exact hts ▸ ht.pow 2
    have h2u : IsUnit (2 : R) := by rwa [show (1 + 1 : R) = 2 by norm_num] at ha1
    rw [show (6 : R) = 2 * 3 by norm_num]; exact h2u.mul (isUnit_of_mul_isUnit_left h3u)
  · rintro ⟨ha, h6u⟩
    rw [show (6 : R) = 2 * 3 by norm_num] at h6u
    have h2u : IsUnit (2 : R) := isUnit_of_mul_isUnit_left h6u
    have h3u : IsUnit (3 : R) := isUnit_of_mul_isUnit_right h6u
    have ht : IsUnit g.trace := by
      rw [ha, show (1 : R) + 2 = 3 by norm_num] at hts
      exact (isUnit_pow_iff two_ne_zero).1 (hts ▸ h3u.mul hd)
    refine ⟨?_, ht, ?_⟩
    · rw [show 6 = 2 * 2 + 2 from rfl, isScalar_pow_even_iff hg hd ht, chebP_six, ha]; ring
    · rw [ha, show (1 : R) + 1 = 2 by norm_num]; exact h2u

/-! ### The trace invariants of a triple -/

section Triple

variable {τ₀ τ₁ τ₂ : Matrix (Fin 2) (Fin 2) R}

/-- `(α₀ + 2)(α₁ + 2)(α₀ + α₁)`. -/
def discr (a₀ a₁ : R) : R := (a₀ + 2) * (a₁ + 2) * (a₀ + a₁)

/-- Condition (*) of page 4, at a point: `ρ₀² ≠ 1`, `ρ₁² ≠ 1`, `ρ₀ρ₁ ≠ ρ₁ρ₀` in `PGL₂`. -/
def Star (τ₀ τ₁ τ₂ : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ¬ IsScalar ((τ₀ * τ₁) ^ 2) ∧ ¬ IsScalar ((τ₁ * τ₂) ^ 2) ∧
    ¬ ∃ μ : R, τ₀ * τ₁ * (τ₁ * τ₂) = μ • (τ₁ * τ₂ * (τ₀ * τ₁))

/-- `Tr(τ₀τ₁τ₂)² = 4 d₀d₁d₂ − Tr(τ₀τ₁)² d₂ − Tr(τ₁τ₂)² d₀` for traceless `τᵢ` with
`Tr(τ₀τ₂) = 0`. -/
theorem trace_triple_sq (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0)
    (h02 : (τ₀ * τ₂).trace = 0) :
    (τ₀ * τ₁ * τ₂).trace ^ 2 = 4 * τ₀.det * τ₁.det * τ₂.det - (τ₀ * τ₁).trace ^ 2 * τ₂.det
      - (τ₁ * τ₂).trace ^ 2 * τ₀.det := by
  have e0 := trace_zero_entry h0
  have e1 := trace_zero_entry h1
  have e2 := trace_zero_entry h2
  simp only [trace_fin_two, det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, e0, e1, e2] at h02 ⊢
  linear_combination (-(2*(τ₀ 0 0)*(τ₂ 0 0)*(τ₁ 0 0)^2 - 2*(τ₀ 0 0)*(τ₂ 0 0)*(τ₁ 0 1)*(τ₁ 1 0) + 2*(τ₀ 0 0)*(τ₂ 0 1)*(τ₁ 0 0)*(τ₁ 1 0) + 2*(τ₀ 0 0)*(τ₂ 1 0)*(τ₁ 0 0)*(τ₁ 0 1) + 2*(τ₀ 0 1)*(τ₂ 0 0)*(τ₁ 0 0)*(τ₁ 1 0) + (τ₀ 0 1)*(τ₂ 0 1)*(τ₁ 1 0)^2 - (τ₀ 0 1)*(τ₂ 1 0)*(τ₁ 0 0)^2 + 2*(τ₀ 1 0)*(τ₂ 0 0)*(τ₁ 0 0)*(τ₁ 0 1) - (τ₀ 1 0)*(τ₂ 0 1)*(τ₁ 0 0)^2 + (τ₀ 1 0)*(τ₂ 1 0)*(τ₁ 0 1)^2)) * h02

/-- `ρ₀ρ₁ − ρ₁ρ₀ = −Tr(τ₀τ₁τ₂) τ₁` for traceless `τᵢ`. -/
theorem commutator_eq (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) :
    τ₀ * τ₁ * (τ₁ * τ₂) - τ₁ * τ₂ * (τ₀ * τ₁) = (-(τ₀ * τ₁ * τ₂).trace) • τ₁ := by
  have e0 := trace_zero_entry h0
  have e1 := trace_zero_entry h1
  have e2 := trace_zero_entry h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, e0, e1, e2] <;> ring

theorem invA_mul_add_two (A B : Matrix (Fin 2) (Fin 2) R) :
    invA (A * B) + 2 = (A * B).trace ^ 2 * (Ring.inverse A.det * Ring.inverse B.det) := by
  unfold invA; rw [det_mul, Ring.mul_inverse_rev]; ring

/-- `α₀ + α₁ = −Tr(τ₀τ₁τ₂)² / (d₀ d₁ d₂)`. -/
theorem invA_add_invA (u0 : IsUnit τ₀.det) (u1 : IsUnit τ₁.det) (u2 : IsUnit τ₂.det)
    (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) (h02 : (τ₀ * τ₂).trace = 0) :
    invA (τ₀ * τ₁) + invA (τ₁ * τ₂) = -((τ₀ * τ₁ * τ₂).trace ^ 2 *
      (Ring.inverse τ₀.det * Ring.inverse τ₁.det * Ring.inverse τ₂.det)) := by
  have hT := trace_triple_sq h0 h1 h2 h02
  have k0 := Ring.mul_inverse_cancel _ u0
  have k1 := Ring.mul_inverse_cancel _ u1
  have k2 := Ring.mul_inverse_cancel _ u2
  unfold invA
  rw [det_mul, det_mul, Ring.mul_inverse_rev, Ring.mul_inverse_rev]
  set d0 := τ₀.det
  set d1 := τ₁.det
  set d2 := τ₂.det
  set j0 := Ring.inverse d0
  set j1 := Ring.inverse d1
  set j2 := Ring.inverse d2
  set s01 := (τ₀ * τ₁).trace
  set s12 := (τ₁ * τ₂).trace
  linear_combination (j0 * j1 * j2) * hT + (4 * d1 * j1 * d2 * j2 - s12 ^ 2 * j1 * j2) * k0
    + (4 * d2 * j2) * k1 + (4 - s01 ^ 2 * j0 * j1) * k2

/-- The discriminant `(α₀ + 2)(α₁ + 2)(α₀ + α₁)` is a unit if and only if `Tr(τ₀τ₁)`,
`Tr(τ₁τ₂)` and `Tr(τ₀τ₁τ₂)` are. -/
theorem isUnit_discr_iff (u0 : IsUnit τ₀.det) (u1 : IsUnit τ₁.det) (u2 : IsUnit τ₂.det)
    (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) (h02 : (τ₀ * τ₂).trace = 0) :
    IsUnit (discr (invA (τ₀ * τ₁)) (invA (τ₁ * τ₂))) ↔
      IsUnit (τ₀ * τ₁).trace ∧ IsUnit (τ₁ * τ₂).trace ∧ IsUnit (τ₀ * τ₁ * τ₂).trace := by
  unfold discr
  rw [invA_mul_add_two τ₀ τ₁, invA_mul_add_two τ₁ τ₂, invA_add_invA u0 u1 u2 h0 h1 h2 h02]
  have v0 := u0.ringInverse
  have v1 := u1.ringInverse
  have v2 := u2.ringInverse
  simp only [IsUnit.mul_iff, IsUnit.neg_iff, isUnit_pow_iff two_ne_zero, v0, v1, v2, and_true]
  tauto

/-- **Page 4, the invariants, at a point.** If the `τᵢ` are traceless with `Tr(τ₀τ₂) = 0`
and `Tr(τ₀τ₁)`, `Tr(τ₁τ₂)`, `Tr(τ₀τ₁τ₂)` are units, then (*) holds. Over any nontrivial
ring. -/
theorem star_of_isUnit [Nontrivial R] (u0 : IsUnit τ₀.det) (u1 : IsUnit τ₁.det)
    (u2 : IsUnit τ₂.det) (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0)
    (ht01 : IsUnit (τ₀ * τ₁).trace) (ht12 : IsUnit (τ₁ * τ₂).trace)
    (hT : IsUnit (τ₀ * τ₁ * τ₂).trace) : Star τ₀ τ₁ τ₂ := by
  refine ⟨fun hs => ?_, fun hs => ?_, ?_⟩
  · have hn : NullePartScalaire (τ₀ * τ₁) := nps_of_isUnit_trace_mul h2 hT
    rw [trace_eq_zero_of_isScalar_mul hn (by rwa [← sq])] at ht01
    exact not_isUnit_zero ht01
  · have hn : NullePartScalaire (τ₁ * τ₂) := by
      refine nps_of_isUnit_trace_mul h0 ?_
      rw [Matrix.trace_mul_comm, ← mul_assoc]; exact hT
    rw [trace_eq_zero_of_isScalar_mul hn (by rwa [← sq])] at ht12
    exact not_isUnit_zero ht12
  · rintro ⟨μ, hμ⟩
    have e : (τ₀ * (τ₀ * τ₁ * (τ₁ * τ₂))).trace
        = μ * (τ₀ * (τ₁ * τ₂ * (τ₀ * τ₁))).trace := by
      rw [hμ, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have e0 := trace_zero_entry h0
    have e1 := trace_zero_entry h1
    have e2 := trace_zero_entry h2
    have key : μ * ((τ₀ * τ₁).trace * (τ₀ * τ₁ * τ₂).trace) = 0 := by
      simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, e0, e1, e2] at e ⊢
      linear_combination -e
    have hμ0 : μ = 0 := (ht01.mul hT).mul_left_eq_zero.1 key
    rw [hμ0, zero_smul] at hμ
    have hu : IsUnit (τ₀ * τ₁ * (τ₁ * τ₂)).det := by
      simp only [det_mul]; exact (u0.mul u1).mul (u1.mul u2)
    rw [hμ] at hu
    simp at hu


/-- If `Tr(τ₀τ₁τ₂) = 0`, then `ρ₀` and `ρ₁` commute. Contrapositive form: (*) forces
`Tr(τ₀τ₁)`, `Tr(τ₁τ₂)`, `Tr(τ₀τ₁τ₂)` to be nonzero. -/
theorem traces_ne_zero_of_star (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0)
    (hS : Star τ₀ τ₁ τ₂) :
    (τ₀ * τ₁).trace ≠ 0 ∧ (τ₁ * τ₂).trace ≠ 0 ∧ (τ₀ * τ₁ * τ₂).trace ≠ 0 := by
  refine ⟨fun h => hS.1 ⟨_, by rw [sq, mul_self_of_trace_zero h]⟩,
    fun h => hS.2.1 ⟨_, by rw [sq, mul_self_of_trace_zero h]⟩, fun h => hS.2.2 ⟨1, ?_⟩⟩
  have e := commutator_eq h0 h1 h2
  rw [h, neg_zero, zero_smul, sub_eq_zero] at e
  rw [one_smul, e]

/-- Over a field, (*) forces the `τᵢ` and `τ₀τ₂` to be non-scalar. -/
theorem not_isScalar_of_star {K : Type*} [Field K] {τ₀ τ₁ τ₂ : Matrix (Fin 2) (Fin 2) K}
    (hd0 : τ₀.det ≠ 0) (hd2 : τ₂.det ≠ 0) (s0 : IsScalar (τ₀ * τ₀)) (s1 : IsScalar (τ₁ * τ₁))
    (hS : Star τ₀ τ₁ τ₂) :
    ¬ IsScalar τ₀ ∧ ¬ IsScalar τ₁ ∧ ¬ IsScalar τ₂ ∧ ¬ IsScalar (τ₀ * τ₂) := by
  obtain ⟨s, hs⟩ := s1
  obtain ⟨s', hs'⟩ := s0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨c, rfl⟩
    exact hS.1 ⟨c ^ 2 * s, by
      rw [sq, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul,
        smul_smul]; ring_nf⟩
  · rintro ⟨c, rfl⟩
    exact hS.1 ⟨c ^ 2 * s', by
      rw [sq, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hs', smul_smul,
        smul_smul]; ring_nf⟩
  · rintro ⟨c, rfl⟩
    exact hS.2.1 ⟨c ^ 2 * s, by
      rw [sq, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul,
        smul_smul]; ring_nf⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simpa [hd0, hd2] using congrArg Matrix.det hc
    have h20 : τ₂ * τ₀ = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h1 : τ₀ * (c⁻¹ • τ₂) = 1 := by
        rw [Matrix.mul_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      have h2 : (c⁻¹ • τ₂) * τ₀ = 1 := by
        rw [← Matrix.inv_eq_right_inv h1, Matrix.nonsing_inv_mul τ₀ (isUnit_iff_ne_zero.2 hd0)]
      rw [Matrix.smul_mul] at h2
      calc τ₂ * τ₀ = c • (c⁻¹ • (τ₂ * τ₀)) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
        _ = c • 1 := by rw [h2]
    refine hS.2.2 ⟨1, ?_⟩
    rw [one_smul]
    calc τ₀ * τ₁ * (τ₁ * τ₂) = τ₀ * (τ₁ * τ₁) * τ₂ := by simp only [mul_assoc]
      _ = (s * c) • 1 := by
        rw [hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hc, smul_smul]
      _ = τ₁ * (τ₂ * τ₀) * τ₁ := by
        rw [h20, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hs, smul_smul, mul_comm]
      _ = τ₁ * τ₂ * (τ₀ * τ₁) := by simp only [mul_assoc]

theorem isScalar_map {S : Type*} [CommRing S] (f : R →+* S) {A : Matrix (Fin 2) (Fin 2) R}
    (h : IsScalar A) : IsScalar (A.map f) := by
  rw [isScalar_iff] at h ⊢
  simp [Matrix.map_apply, h.1, h.2.1, h.2.2]

theorem nps_of_forall_map {A : Matrix (Fin 2) (Fin 2) R}
    (h : ∀ m : Ideal R, m.IsMaximal → ¬ IsScalar (A.map (Ideal.Quotient.mk m))) :
    NullePartScalaire A := by
  rw [nps_iff_maximal]
  rintro m hm ⟨h1, h2, h3⟩
  apply h m hm
  rw [isScalar_iff]
  simp only [Matrix.map_apply]
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.2 h1, Ideal.Quotient.eq_zero_iff_mem.2 h2,
    Ideal.Quotient.eq.2 h3⟩

theorem trace_map_mul {S : Type*} [CommRing S] (f : R →+* S) (A B : Matrix (Fin 2) (Fin 2) R) :
    (A.map f * B.map f).trace = f (A * B).trace := by
  rw [← Matrix.map_mul, AddMonoidHom.map_trace]

/-- **Theorem of page 4, part 1), over any ring.** Let `τ₀, τ₁, τ₂ ∈ GL₂(R)` with `τᵢ²` and
`(τ₀τ₂)²` scalar (a homomorphism `G₂ → PGL₂(R)`), satisfying (*) at every point of
`Spec R`. Then the `τᵢ` and `τ₀τ₂` are traceless and
`(α₀ + 2)(α₁ + 2)(α₀ + α₁)` is a unit, `α₀ = A(τ₀τ₁)`, `α₁ = A(τ₁τ₂)`. -/
theorem discr_isUnit_of_star (u0 : IsUnit τ₀.det) (u1 : IsUnit τ₁.det) (u2 : IsUnit τ₂.det)
    (s0 : IsScalar (τ₀ * τ₀)) (s1 : IsScalar (τ₁ * τ₁)) (s2 : IsScalar (τ₂ * τ₂))
    (s02 : IsScalar (τ₀ * τ₂ * (τ₀ * τ₂)))
    (hS : ∀ m : Ideal R, m.IsMaximal → Star (τ₀.map (Ideal.Quotient.mk m))
      (τ₁.map (Ideal.Quotient.mk m)) (τ₂.map (Ideal.Quotient.mk m))) :
    τ₀.trace = 0 ∧ τ₁.trace = 0 ∧ τ₂.trace = 0 ∧ (τ₀ * τ₂).trace = 0 ∧
      IsUnit (discr (invA (τ₀ * τ₁)) (invA (τ₁ * τ₂))) := by
  have fib : ∀ m : Ideal R, m.IsMaximal →
      ¬ IsScalar (τ₀.map (Ideal.Quotient.mk m)) ∧ ¬ IsScalar (τ₁.map (Ideal.Quotient.mk m)) ∧
      ¬ IsScalar (τ₂.map (Ideal.Quotient.mk m)) ∧
      ¬ IsScalar ((τ₀ * τ₂).map (Ideal.Quotient.mk m)) := by
    intro m hm
    let _ : Field (R ⧸ m) := Ideal.Quotient.field m
    have d0 : (τ₀.map (Ideal.Quotient.mk m)).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (u0.map _).ne_zero
    have d2 : (τ₂.map (Ideal.Quotient.mk m)).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (u2.map _).ne_zero
    rw [Matrix.map_mul]
    exact not_isScalar_of_star d0 d2 (by rw [← Matrix.map_mul]; exact isScalar_map _ s0)
      (by rw [← Matrix.map_mul]; exact isScalar_map _ s1) (hS m hm)
  have n0 := nps_of_forall_map fun m hm => (fib m hm).1
  have n1 := nps_of_forall_map fun m hm => (fib m hm).2.1
  have n2 := nps_of_forall_map fun m hm => (fib m hm).2.2.1
  have n02 := nps_of_forall_map fun m hm => (fib m hm).2.2.2
  have h0 := trace_eq_zero_of_isScalar_mul n0 s0
  have h1 := trace_eq_zero_of_isScalar_mul n1 s1
  have h2 := trace_eq_zero_of_isScalar_mul n2 s2
  have h02 := trace_eq_zero_of_isScalar_mul n02 s02
  refine ⟨h0, h1, h2, h02, (isUnit_discr_iff u0 u1 u2 h0 h1 h2 h02).2 ?_⟩
  have fib2 : ∀ m : Ideal R, m.IsMaximal →
      Ideal.Quotient.mk m (τ₀ * τ₁).trace ≠ 0 ∧ Ideal.Quotient.mk m (τ₁ * τ₂).trace ≠ 0 ∧
        Ideal.Quotient.mk m (τ₀ * τ₁ * τ₂).trace ≠ 0 := by
    intro m hm
    have z : ∀ A : Matrix (Fin 2) (Fin 2) R, A.trace = 0 →
        (A.map (Ideal.Quotient.mk m)).trace = 0 := fun A hA => by
      rw [← AddMonoidHom.map_trace, hA, map_zero]
    have := traces_ne_zero_of_star (z _ h0) (z _ h1) (z _ h2) (hS m hm)
    rwa [trace_map_mul, trace_map_mul, ← Matrix.map_mul, trace_map_mul] at this
  refine ⟨?_, ?_, ?_⟩ <;> rw [isUnit_iff_maximal] <;> intro m hm hx <;>
    [exact (fib2 m hm).1 (Ideal.Quotient.eq_zero_iff_mem.2 hx);
     exact (fib2 m hm).2.1 (Ideal.Quotient.eq_zero_iff_mem.2 hx);
     exact (fib2 m hm).2.2 (Ideal.Quotient.eq_zero_iff_mem.2 hx)]

/-- **Converse, over any ring.** Traceless `τᵢ` with `Tr(τ₀τ₂) = 0` and
`(α₀ + 2)(α₁ + 2)(α₀ + α₁)` a unit satisfy (*) at every point. -/
theorem star_of_discr_isUnit (u0 : IsUnit τ₀.det) (u1 : IsUnit τ₁.det) (u2 : IsUnit τ₂.det)
    (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) (h02 : (τ₀ * τ₂).trace = 0)
    (hU : IsUnit (discr (invA (τ₀ * τ₁)) (invA (τ₁ * τ₂)))) (m : Ideal R) (hm : m.IsMaximal) :
    Star (τ₀.map (Ideal.Quotient.mk m)) (τ₁.map (Ideal.Quotient.mk m))
      (τ₂.map (Ideal.Quotient.mk m)) := by
  let _ : Field (R ⧸ m) := Ideal.Quotient.field m
  obtain ⟨t1, t2, t3⟩ := (isUnit_discr_iff u0 u1 u2 h0 h1 h2 h02).1 hU
  have z : ∀ A : Matrix (Fin 2) (Fin 2) R, A.trace = 0 →
      (A.map (Ideal.Quotient.mk m)).trace = 0 := fun A hA => by
    rw [← AddMonoidHom.map_trace, hA, map_zero]
  have d : ∀ A : Matrix (Fin 2) (Fin 2) R, IsUnit A.det →
      IsUnit (A.map (Ideal.Quotient.mk m)).det := fun A hA => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hA.map _
  refine star_of_isUnit (d _ u0) (d _ u1) (d _ u2) (z _ h0) (z _ h1) (z _ h2) ?_ ?_ ?_
  · rw [trace_map_mul]; exact t1.map _
  · rw [trace_map_mul]; exact t2.map _
  · rw [← Matrix.map_mul, trace_map_mul]; exact t3.map _

theorem trace_conj {g : Matrix (Fin 2) (Fin 2) R} (hg : IsUnit g.det)
    (A : Matrix (Fin 2) (Fin 2) R) : (g⁻¹ * A * g).trace = A.trace := by
  rw [Matrix.trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left g A hg]

/-- The commutant of a nowhere-scalar `X` is `R[X]`. -/
theorem commutant_eq {X g : Matrix (Fin 2) (Fin 2) R} (hX : NullePartScalaire X)
    (h : g * X = X * g) : ∃ p q : R, g = p • 1 + q • X := by
  have h1 : (1 : R) ∈ Ideal.span {X 0 1, X 1 0, X 0 0 - X 1 1} := by rw [hX]; trivial
  obtain ⟨r₁, r₂, r₃, hr⟩ := Submodule.mem_span_triple.1 h1
  simp only [smul_eq_mul] at hr
  have A := congrFun (congrFun h 0) 0
  have B := congrFun (congrFun h 0) 1
  have C := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at A B C
  refine ⟨g 0 0 - (r₁ * g 0 1 + r₂ * g 1 0 + r₃ * (g 0 0 - g 1 1)) * X 0 0,
    r₁ * g 0 1 + r₂ * g 1 0 + r₃ * (g 0 0 - g 1 1), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination r₂ * A + (-r₃) * B + (-(g 0 1)) * hr
    | linear_combination (-r₁) * A + r₃ * C + (-(g 1 0)) * hr
    | linear_combination (-r₁) * B + r₂ * C + (g 0 0 - g 1 1) * hr

/-- **Theorem of page 4, part 2), rigidity, over any ring.** Under the hypotheses of the
converse, an element `g ∈ GL₂(R)` normalising each `τᵢ` up to a scalar is scalar: the
centraliser of the image of `G₂` in `PGL₂(R)` is trivial. -/
theorem rigid (u0 : IsUnit τ₀.det) (u1 : IsUnit τ₁.det) (u2 : IsUnit τ₂.det)
    (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) (h02 : (τ₀ * τ₂).trace = 0)
    (hU : IsUnit (discr (invA (τ₀ * τ₁)) (invA (τ₁ * τ₂))))
    {g : Matrix (Fin 2) (Fin 2) R} (hg : IsUnit g.det) {μ₀ μ₁ μ₂ : R}
    (k0 : g * τ₀ = μ₀ • (τ₀ * g)) (k1 : g * τ₁ = μ₁ • (τ₁ * g)) (k2 : g * τ₂ = μ₂ • (τ₂ * g)) :
    IsScalar g := by
  obtain ⟨t1, t2, t3⟩ := (isUnit_discr_iff u0 u1 u2 h0 h1 h2 h02).1 hU
  have conj : ∀ (A B : Matrix (Fin 2) (Fin 2) R) (μ ν : R), g * A = μ • (A * g) →
      g * B = ν • (B * g) → IsUnit (A * B).trace → g * (A * B) = A * B * g := by
    intro A B μ ν hA hB hu
    have r : g * (A * B) = (μ * ν) • (A * B * g) := by
      rw [← mul_assoc, hA, Matrix.smul_mul, mul_assoc, hB, Matrix.mul_smul, smul_smul,
        ← mul_assoc]
    have e : (g⁻¹ * (g * (A * B))).trace = (g⁻¹ * ((μ * ν) • (A * B * g))).trace := by rw [r]
    rw [Matrix.nonsing_inv_mul_cancel_left g _ hg, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, ← Matrix.mul_assoc, trace_conj hg] at e
    have e' : (1 - μ * ν) * (A * B).trace = 0 := by linear_combination e
    have hμν : μ * ν = 1 := by linear_combination -hu.mul_left_eq_zero.1 e'
    rw [r, hμν, one_smul]
  have c0 := conj τ₀ τ₁ μ₀ μ₁ k0 k1 t1
  have c1 := conj τ₁ τ₂ μ₁ μ₂ k1 k2 t2
  have n0 : NullePartScalaire (τ₀ * τ₁) := nps_of_isUnit_trace_mul h2 t3
  obtain ⟨p, q, hpq⟩ := commutant_eq n0 c0
  rw [hpq] at c1
  have e : q • (τ₀ * τ₁ * (τ₁ * τ₂) - τ₁ * τ₂ * (τ₀ * τ₁)) = 0 := by
    rw [smul_sub, sub_eq_zero]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one] at c1
    exact add_left_cancel c1
  rw [commutator_eq h0 h1 h2, smul_smul] at e
  have e2 := congrArg (· * τ₁) e
  simp only [Matrix.smul_mul, Matrix.zero_mul, mul_self_of_trace_zero h1, smul_smul] at e2
  have e3 := congrFun (congrFun e2 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.zero_apply] at e3
  have hq : q = 0 :=
    (t3.neg.mul u1.neg).mul_left_eq_zero.1 (by linear_combination e3)
  exact ⟨p, by rw [hpq, hq, zero_smul, add_zero]⟩

end Triple

/-! ### The normal form (page 4, part 3) -/

section NormalForm

variable (ℓ b : R)

/-- `ρ₀` in normal form: `A = ℓ + ℓ⁻¹`. -/
def rho0N : Matrix (Fin 2) (Fin 2) R := !![ℓ, 1; 0, 1]
/-- `ρ₁` in normal form: `Tr² / det = b`. -/
def rho1N : Matrix (Fin 2) (Fin 2) R := !![0, 1; -b, b]
def tau1N : Matrix (Fin 2) (Fin 2) R := !![b, 1 - ℓ - b; b * (1 - ℓ), -b]
def tau0N : Matrix (Fin 2) (Fin 2) R := rho0N ℓ * tau1N ℓ b
def tau2N : Matrix (Fin 2) (Fin 2) R := tau1N ℓ b * rho1N b

theorem trace_tau0N : (tau0N ℓ b).trace = 0 := by
  simp [tau0N, rho0N, tau1N, trace_fin_two]; ring
theorem trace_tau1N : (tau1N ℓ b).trace = 0 := by simp [tau1N, trace_fin_two]
theorem trace_tau2N : (tau2N ℓ b).trace = 0 := by
  simp [tau2N, rho1N, tau1N, trace_fin_two]; ring
theorem trace_tau0N_tau2N : (tau0N ℓ b * tau2N ℓ b).trace = 0 := by
  simp [tau0N, tau2N, rho0N, rho1N, tau1N, trace_fin_two]
  ring
theorem det_tau1N : (tau1N ℓ b).det = -(b * ((1 - ℓ) ^ 2 + ℓ * b)) := by
  simp [tau1N, det_fin_two]; ring
theorem det_rho0N : (rho0N ℓ).det = ℓ := by simp [rho0N, det_fin_two]
theorem det_rho1N : (rho1N b).det = b := by simp [rho1N, det_fin_two]

theorem tau0N_mul_tau1N : tau0N ℓ b * tau1N ℓ b = (b * ((1 - ℓ) ^ 2 + ℓ * b)) • rho0N ℓ := by
  rw [tau0N, mul_assoc, mul_self_of_trace_zero (trace_tau1N ℓ b), det_tau1N, neg_neg,
    Matrix.mul_smul, Matrix.mul_one]

theorem tau1N_mul_tau2N : tau1N ℓ b * tau2N ℓ b = (b * ((1 - ℓ) ^ 2 + ℓ * b)) • rho1N b := by
  rw [tau2N, ← mul_assoc, mul_self_of_trace_zero (trace_tau1N ℓ b), det_tau1N, neg_neg,
    Matrix.smul_mul, Matrix.one_mul]

theorem trace_rho0N : (rho0N ℓ).trace = ℓ + 1 := by simp [rho0N, trace_fin_two]
theorem trace_rho1N : (rho1N b).trace = b := by simp [rho1N, trace_fin_two]

variable {ℓ b}

/-- **Page 4, part 3), in normal form.** Let `α₀, α₁ ∈ R` with `(α₀ + 2)(α₁ + 2)(α₀ + α₁)`
a unit, and `ℓ` a root of `T² − α₀ T + 1`; put `b = α₁ + 2`. Then
`τ₁ = !![b, 1 − ℓ − b; b(1 − ℓ), −b]`, `τ₀ = ρ₀τ₁`, `τ₂ = τ₁ρ₁` with
`ρ₀ = !![ℓ, 1; 0, 1]`, `ρ₁ = !![0, 1; −b, b]` lie in `GL₂(R)`, are traceless with
`Tr(τ₀τ₂) = 0` (so `τᵢ²` and `(τ₀τ₂)²` are scalar), have invariants
`A(τ₀τ₁) = α₀`, `A(τ₁τ₂) = α₁`, and satisfy (*) at every point. -/
theorem normalForm {a₀ a₁ : R} (hℓ : ℓ ^ 2 - a₀ * ℓ + 1 = 0) (hb : b = a₁ + 2)
    (hU : IsUnit (discr a₀ a₁)) :
    IsUnit (tau0N ℓ b).det ∧ IsUnit (tau1N ℓ b).det ∧ IsUnit (tau2N ℓ b).det ∧
    invA (tau0N ℓ b * tau1N ℓ b) = a₀ ∧ invA (tau1N ℓ b * tau2N ℓ b) = a₁ ∧
    ∀ m : Ideal R, m.IsMaximal → Star ((tau0N ℓ b).map (Ideal.Quotient.mk m))
      ((tau1N ℓ b).map (Ideal.Quotient.mk m)) ((tau2N ℓ b).map (Ideal.Quotient.mk m)) := by
  have hU' := hU
  unfold discr at hU'
  have hb2 : IsUnit b := hb ▸ isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hU')
  have hs : IsUnit (a₀ + a₁) := isUnit_of_mul_isUnit_right hU'
  have hℓu : IsUnit ℓ := IsUnit.of_mul_eq_one (a₀ - ℓ) (by linear_combination -hℓ)
  have hk : (1 - ℓ) ^ 2 + ℓ * b = ℓ * (a₀ + a₁) := by rw [hb]; linear_combination hℓ
  have hku : IsUnit (b * ((1 - ℓ) ^ 2 + ℓ * b)) := by rw [hk]; exact hb2.mul (hℓu.mul hs)
  have d1 : IsUnit (tau1N ℓ b).det := by rw [det_tau1N]; exact hku.neg
  have d0 : IsUnit (tau0N ℓ b).det := by
    rw [tau0N, det_mul, det_rho0N]; exact hℓu.mul d1
  have d2 : IsUnit (tau2N ℓ b).det := by
    rw [tau2N, det_mul, det_rho1N]; exact d1.mul hb2
  have i0 : invA (tau0N ℓ b * tau1N ℓ b) = a₀ := by
    rw [tau0N_mul_tau1N, invA_smul _ (by rw [det_rho0N]; exact hℓu) hku]
    unfold invA
    rw [det_rho0N, trace_rho0N]
    have hj := Ring.mul_inverse_cancel _ hℓu
    linear_combination (Ring.inverse ℓ) * hℓ + (a₀ + 2) * hj
  have i1 : invA (tau1N ℓ b * tau2N ℓ b) = a₁ := by
    rw [tau1N_mul_tau2N, invA_smul _ (by rw [det_rho1N]; exact hb2) hku]
    unfold invA
    rw [det_rho1N, trace_rho1N]
    have hj := Ring.mul_inverse_cancel _ hb2
    linear_combination b * hj + hb
  refine ⟨d0, d1, d2, i0, i1, fun m hm => ?_⟩
  refine star_of_discr_isUnit d0 d1 d2 (trace_tau0N ℓ b) (trace_tau1N ℓ b) (trace_tau2N ℓ b)
    (trace_tau0N_tau2N ℓ b) ?_ m hm
  rw [i0, i1]; exact hU

/-- The normal form over `R[ℓ] = R[T]/(T² − α₀T + 1)`, for any `α₀, α₁ ∈ R` with
`(α₀ + 2)(α₁ + 2)(α₀ + α₁)` a unit. -/
theorem exists_normalForm_adjoinRoot {a₀ a₁ : R} (hU : IsUnit (discr a₀ a₁)) :
    let f : Polynomial R := Polynomial.X ^ 2 - Polynomial.C a₀ * Polynomial.X + 1
    let ℓ := AdjoinRoot.root f
    let b := AdjoinRoot.of f a₁ + 2
    IsUnit (tau0N ℓ b).det ∧ IsUnit (tau1N ℓ b).det ∧ IsUnit (tau2N ℓ b).det ∧
    invA (tau0N ℓ b * tau1N ℓ b) = AdjoinRoot.of f a₀ ∧
    invA (tau1N ℓ b * tau2N ℓ b) = AdjoinRoot.of f a₁ ∧
    ∀ m : Ideal (AdjoinRoot f), m.IsMaximal → Star ((tau0N ℓ b).map (Ideal.Quotient.mk m))
      ((tau1N ℓ b).map (Ideal.Quotient.mk m)) ((tau2N ℓ b).map (Ideal.Quotient.mk m)) := by
  intro f ℓ b
  have hℓ : ℓ ^ 2 - AdjoinRoot.of f a₀ * ℓ + 1 = 0 := by simpa [f] using AdjoinRoot.eval₂_root f
  have hU' : IsUnit (discr (AdjoinRoot.of f a₀) (AdjoinRoot.of f a₁)) := by
    have h2 : AdjoinRoot.of f (2 : R) = 2 := map_ofNat _ 2
    simpa [discr, h2] using hU.map (AdjoinRoot.of f)
  exact normalForm hℓ rfl hU'

end NormalForm

/-! ### Conjugacy over a field -/

section Conjugacy

variable {K : Type*} [Field K]

theorem eq_smul_tau1N {M : Matrix (Fin 2) (Fin 2) K} {ℓ b : K} (hb : b ≠ 0)
    (hT : M.trace = 0) (h0 : (M * rho0N ℓ).trace = 0) (h1 : (M * rho1N b).trace = 0) :
    M = (M 0 0 * b⁻¹) • tau1N ℓ b := by
  have hbi := mul_inv_cancel₀ hb
  rw [trace_fin_two] at hT
  simp only [trace_fin_two, rho0N, rho1N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1N] <;>
    first
    | linear_combination (-(M 0 0)) * hbi
    | linear_combination (b⁻¹ * (b - 1)) * hT + b⁻¹ * h0 + (-b⁻¹) * h1 + (-(M 0 1)) * hbi
    | linear_combination (-b * b⁻¹) * hT + (b * b⁻¹) * h0 + (-(M 1 0)) * hbi
    | linear_combination hT + (M 0 0) * hbi

/-- Two pairs: `X` with `Tr X = ℓ + 1`, `det X = ℓ`, `Y` with `Tr Y = det Y = b ≠ 0`,
`Tr XY = 0` and `det [X, Y] ≠ 0` are conjugate to `(ρ₀, ρ₁)` of the normal form. -/
theorem conj_pair {X Y : Matrix (Fin 2) (Fin 2) K} {ℓ b : K} (hb : b ≠ 0)
    (hTX : X.trace = ℓ + 1) (hDX : X.det = ℓ) (hTY : Y.trace = b) (hDY : Y.det = b)
    (hXY : (X * Y).trace = 0) (hC : (X * Y - Y * X).det ≠ 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, g.det ≠ 0 ∧ X * g = g * rho0N ℓ ∧ Y * g = g * rho1N b := by
  rw [trace_fin_two] at hTX hTY
  rw [det_fin_two] at hDX hDY
  simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hXY
  have hdet : (X - ℓ • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    simp [det_fin_two]; linear_combination hDX - ℓ * hTX
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have e0 : X 0 0 * v 0 + X 0 1 * v 1 = ℓ * v 0 := by
    have := congrFun hv 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linear_combination this
  have e1 : X 1 0 * v 0 + X 1 1 * v 1 = ℓ * v 1 := by
    have := congrFun hv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linear_combination this
  have hbi := mul_inv_cancel₀ hb
  obtain ⟨w0, hw0⟩ : ∃ w0 : K, b * w0 + (Y 0 0 * v 0 + Y 0 1 * v 1) = 0 :=
    ⟨-(Y 0 0 * v 0 + Y 0 1 * v 1) * b⁻¹, by
      linear_combination (-(Y 0 0 * v 0 + Y 0 1 * v 1)) * hbi⟩
  obtain ⟨w1, hw1⟩ : ∃ w1 : K, b * w1 + (Y 1 0 * v 0 + Y 1 1 * v 1) = 0 :=
    ⟨-(Y 1 0 * v 0 + Y 1 1 * v 1) * b⁻¹, by
      linear_combination (-(Y 1 0 * v 0 + Y 1 1 * v 1)) * hbi⟩
  have G1 : X 0 0 * w0 + X 0 1 * w1 = v 0 + w0 := mul_left_cancel₀ hb (by
    linear_combination (v 0 * Y 1 1 - v 1 * Y 0 1) * hTX + (v 0) * hTY + (-(v 0)) * hXY
      + (-(Y 1 1)) * e0 + (Y 0 1) * e1 + (X 0 0 - 1) * hw0 + (X 0 1) * hw1)
  have G2 : X 1 0 * w0 + X 1 1 * w1 = v 1 + w1 := mul_left_cancel₀ hb (by
    linear_combination (-(v 0) * Y 1 0 + v 1 * Y 0 0) * hTX + (v 1) * hTY + (-(v 1)) * hXY
      + (Y 1 0) * e0 + (-(Y 0 0)) * e1 + (X 1 0) * hw0 + (X 1 1 - 1) * hw1)
  have G3 : Y 0 0 * w0 + Y 0 1 * w1 = v 0 + b * w0 := mul_left_cancel₀ hb (by
    linear_combination (b * w0) * hTY + (v 0) * hDY + (-(Y 1 1)) * hw0 + (Y 0 1) * hw1)
  have G4 : Y 1 0 * w0 + Y 1 1 * w1 = v 1 + b * w1 := mul_left_cancel₀ hb (by
    linear_combination (b * w1) * hTY + (v 1) * hDY + (Y 1 0) * hw0 + (-(Y 0 0)) * hw1)
  refine ⟨!![v 0, w0; v 1, w1], ?_, ?_, ?_⟩
  · rw [det_fin_two_of]
    intro hd
    have a0 : b * (v 0 * ((X * Y - Y * X) *ᵥ v) 0) = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (b * v 1 * Y 0 1) * e0 + (-b * v 0 * Y 0 1) * e1
        + (-b * v 1 * X 0 1) * hw0 + (b * v 0 * X 0 1) * hw1 + (-b ^ 2 * X 0 1) * hd
    have a1 : b * (v 0 * ((X * Y - Y * X) *ᵥ v) 1) = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (b * (b * w1 + v 1 * Y 1 1)) * e0 + (-b * (b * w0 + v 0 * Y 1 1)) * e1
        + (b * v 0 * X 1 0) * hw0 + (-b * (v 0 * X 0 0 - v 0 * X 1 1 + v 1 * X 0 1)) * hw1
        + (-b ^ 2 * (-ℓ + X 1 1)) * hd
    have b0 : b * (v 1 * ((X * Y - Y * X) *ᵥ v) 0) = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-b * (b * w1 + v 1 * Y 0 0)) * e0 + (b * (b * w0 + v 0 * Y 0 0)) * e1
        + (b * (-(v 0) * X 1 0 + v 1 * X 0 0 - v 1 * X 1 1)) * hw0 + (b * v 1 * X 0 1) * hw1
        + (b ^ 2 * (-ℓ + X 0 0)) * hd
    have b1 : b * (v 1 * ((X * Y - Y * X) *ᵥ v) 1) = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-b * v 1 * Y 1 0) * e0 + (b * v 0 * Y 1 0) * e1
        + (b * v 1 * X 1 0) * hw0 + (-b * v 0 * X 1 0) * hw1 + (b ^ 2 * X 1 0) * hd
    have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      simp only [not_or, ne_eq, not_not] at h
      apply hv0
      funext i
      fin_cases i <;> simp [h.1, h.2]
    have hCv : (X * Y - Y * X) *ᵥ v = 0 := by
      funext i
      fin_cases i
      · rcases hv' with h | h
        · exact (mul_eq_zero.1 ((mul_eq_zero.1 a0).resolve_left hb)).resolve_left h
        · exact (mul_eq_zero.1 ((mul_eq_zero.1 b0).resolve_left hb)).resolve_left h
      · rcases hv' with h | h
        · exact (mul_eq_zero.1 ((mul_eq_zero.1 a1).resolve_left hb)).resolve_left h
        · exact (mul_eq_zero.1 ((mul_eq_zero.1 b1).resolve_left hb)).resolve_left h
    exact hC (Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hCv⟩)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rho0N, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
      | linear_combination e0 | linear_combination e1
      | linear_combination G1 | linear_combination G2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rho1N, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
      | linear_combination hw0 | linear_combination hw1
      | linear_combination G3 | linear_combination G4

/-- **Page 4, part 2), conjugacy, over a field containing `ℓ`.** Let `τ₀, τ₁, τ₂ ∈ GL₂(K)`
be traceless with `Tr(τ₀τ₂) = 0` and `(α₀ + 2)(α₁ + 2)(α₀ + α₁) ≠ 0`, and let `ℓ ∈ K` be a
root of `T² − α₀T + 1`. Then some `g ∈ GL₂(K)` conjugates the triple, up to scalars, to the
normal form with parameters `ℓ` and `b = α₁ + 2`. -/
theorem conj_normalForm {τ₀ τ₁ τ₂ : Matrix (Fin 2) (Fin 2) K}
    (d0 : τ₀.det ≠ 0) (d1 : τ₁.det ≠ 0) (d2 : τ₂.det ≠ 0)
    (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) (h02 : (τ₀ * τ₂).trace = 0)
    (hU : discr (invA (τ₀ * τ₁)) (invA (τ₁ * τ₂)) ≠ 0)
    {ℓ : K} (hℓ : ℓ ^ 2 - invA (τ₀ * τ₁) * ℓ + 1 = 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, g.det ≠ 0 ∧ ∃ c₀ c₁ c₂ : K,
      τ₀ * g = c₀ • (g * tau0N ℓ (invA (τ₁ * τ₂) + 2)) ∧
      τ₁ * g = c₁ • (g * tau1N ℓ (invA (τ₁ * τ₂) + 2)) ∧
      τ₂ * g = c₂ • (g * tau2N ℓ (invA (τ₁ * τ₂) + 2)) := by
  obtain ⟨t1, t2, t3⟩ := (isUnit_discr_iff (isUnit_iff_ne_zero.2 d0) (isUnit_iff_ne_zero.2 d1)
    (isUnit_iff_ne_zero.2 d2) h0 h1 h2 h02).1 (isUnit_iff_ne_zero.2 hU)
  rw [isUnit_iff_ne_zero] at t1 t2 t3
  have ha0 : (invA (τ₀ * τ₁) + 2) * (τ₀.det * τ₁.det) = (τ₀ * τ₁).trace ^ 2 := by
    rw [invA_mul_add_two]
    simp only [Ring.inverse_eq_inv']
    have k0 := inv_mul_cancel₀ d0
    have k1 := inv_mul_cancel₀ d1
    linear_combination (τ₀ * τ₁).trace ^ 2 * (τ₁.det⁻¹ * τ₁.det) * k0
      + (τ₀ * τ₁).trace ^ 2 * k1
  have hb0 : (invA (τ₁ * τ₂) + 2) * (τ₁.det * τ₂.det) = (τ₁ * τ₂).trace ^ 2 := by
    rw [invA_mul_add_two]
    simp only [Ring.inverse_eq_inv']
    have k1 := inv_mul_cancel₀ d1
    have k2 := inv_mul_cancel₀ d2
    linear_combination (τ₁ * τ₂).trace ^ 2 * (τ₂.det⁻¹ * τ₂.det) * k1
      + (τ₁ * τ₂).trace ^ 2 * k2
  generalize invA (τ₀ * τ₁) = a₀ at ha0 hℓ
  generalize invA (τ₁ * τ₂) + 2 = b at hb0 ⊢
  have hsq : (ℓ + 1) ^ 2 = (a₀ + 2) * ℓ := by linear_combination hℓ
  have hb : b ≠ 0 := fun h => pow_ne_zero 2 t2 (by rw [← hb0, h, zero_mul])
  have ha2 : a₀ + 2 ≠ 0 := fun h => pow_ne_zero 2 t1 (by rw [← ha0, h, zero_mul])
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ
  have hℓ1 : ℓ + 1 ≠ 0 := fun h => mul_ne_zero ha2 hℓ0 (by rw [← hsq, h]; ring)
  have hti := mul_inv_cancel₀ t1
  have hsi := mul_inv_cancel₀ t2
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (ℓ + 1) * (τ₀ * τ₁).trace⁻¹ := ⟨_, rfl⟩
  obtain ⟨c', hc'def⟩ : ∃ c' : K, c' = b * (τ₁ * τ₂).trace⁻¹ := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact mul_ne_zero hℓ1 (inv_ne_zero t1)
  have hc' : c' ≠ 0 := by rw [hc'def]; exact mul_ne_zero hb (inv_ne_zero t2)
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) K, X = c • (τ₀ * τ₁) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin 2) (Fin 2) K, Y = c' • (τ₁ * τ₂) := ⟨_, rfl⟩
  have hTX : X.trace = ℓ + 1 := by
    rw [hX, Matrix.trace_smul, smul_eq_mul, hcdef, mul_assoc, inv_mul_cancel₀ t1, mul_one]
  have hDX : X.det = ℓ := by
    rw [hX, det_smul, Fintype.card_fin, det_mul, hcdef]
    linear_combination ((τ₀ * τ₁).trace⁻¹ ^ 2 * (τ₀.det * τ₁.det)) * hsq
      + (ℓ * (τ₀ * τ₁).trace⁻¹ ^ 2) * ha0
      + (ℓ * ((τ₀ * τ₁).trace * (τ₀ * τ₁).trace⁻¹ + 1)) * hti
  have hTY : Y.trace = b := by
    rw [hY, Matrix.trace_smul, smul_eq_mul, hc'def, mul_assoc, inv_mul_cancel₀ t2, mul_one]
  have hDY : Y.det = b := by
    rw [hY, det_smul, Fintype.card_fin, det_mul, hc'def]
    linear_combination (b * (τ₁ * τ₂).trace⁻¹ ^ 2) * hb0
      + (b * ((τ₁ * τ₂).trace * (τ₁ * τ₂).trace⁻¹ + 1)) * hsi
  have hρρ : τ₀ * τ₁ * (τ₁ * τ₂) = (-τ₁.det) • (τ₀ * τ₂) := by
    rw [show τ₀ * τ₁ * (τ₁ * τ₂) = τ₀ * (τ₁ * τ₁) * τ₂ by simp only [Matrix.mul_assoc],
      mul_self_of_trace_zero h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hXY : (X * Y).trace = 0 := by
    rw [hX, hY, Matrix.smul_mul, Matrix.mul_smul, hρρ]
    simp [Matrix.trace_smul, h02]
  have hC : (X * Y - Y * X).det ≠ 0 := by
    have e : X * Y - Y * X = (c * c') • (τ₀ * τ₁ * (τ₁ * τ₂) - τ₁ * τ₂ * (τ₀ * τ₁)) := by
      rw [hX, hY, smul_sub]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm c' c]
    rw [e, commutator_eq h0 h1 h2, smul_smul, det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hc hc') (neg_ne_zero.2 t3))) d1
  obtain ⟨g, hg, hXg, hYg⟩ := conj_pair hb hTX hDX hTY hDY hXY hC
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = g⁻¹ * τ₁ * g := ⟨_, rfl⟩
  have hM0 : M.trace = 0 := by rw [hM, trace_conj hgu, h1]
  have z0 : (τ₁ * (τ₀ * τ₁)).trace = 0 := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, mul_self_of_trace_zero h1, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, h0, smul_zero]
  have z2 : (τ₁ * (τ₁ * τ₂)).trace = 0 := by
    rw [← Matrix.mul_assoc, mul_self_of_trace_zero h1, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, h2, smul_zero]
  have hM1 : (M * rho0N ℓ).trace = 0 := by
    rw [hM, Matrix.mul_assoc (g⁻¹ * τ₁), ← hXg,
      show g⁻¹ * τ₁ * (X * g) = g⁻¹ * (τ₁ * X) * g by simp only [Matrix.mul_assoc],
      trace_conj hgu, hX, Matrix.mul_smul, Matrix.trace_smul, z0, smul_zero]
  have hM2 : (M * rho1N b).trace = 0 := by
    rw [hM, Matrix.mul_assoc (g⁻¹ * τ₁), ← hYg,
      show g⁻¹ * τ₁ * (Y * g) = g⁻¹ * (τ₁ * Y) * g by simp only [Matrix.mul_assoc],
      trace_conj hgu, hY, Matrix.mul_smul, Matrix.trace_smul, z2, smul_zero]
  obtain ⟨k, hk⟩ : ∃ k : K, M = k • tau1N ℓ b := ⟨_, eq_smul_tau1N hb hM0 hM1 hM2⟩
  have hτ₁g : τ₁ * g = g * M := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgu,
      Matrix.one_mul]
  have hd1' : -τ₁.det ≠ 0 := neg_ne_zero.2 d1
  have hτ₀ : τ₀ = ((-τ₁.det)⁻¹ * c⁻¹) • (X * τ₁) := by
    rw [hX, Matrix.smul_mul, Matrix.mul_assoc, mul_self_of_trace_zero h1, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, smul_smul]
    rw [show (-τ₁.det)⁻¹ * c⁻¹ * c * -τ₁.det = 1 by field_simp, one_smul]
  have hτ₂ : τ₂ = ((-τ₁.det)⁻¹ * c'⁻¹) • (τ₁ * Y) := by
    rw [hY, Matrix.mul_smul, ← Matrix.mul_assoc, mul_self_of_trace_zero h1, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, smul_smul]
    rw [show (-τ₁.det)⁻¹ * c'⁻¹ * c' * -τ₁.det = 1 by field_simp, one_smul]
  refine ⟨g, hg, ((-τ₁.det)⁻¹ * c⁻¹) * k, k, ((-τ₁.det)⁻¹ * c'⁻¹) * k, ?_, ?_, ?_⟩
  · calc τ₀ * g = ((-τ₁.det)⁻¹ * c⁻¹) • (X * τ₁) * g := by rw [← hτ₀]
      _ = ((-τ₁.det)⁻¹ * c⁻¹) • (X * g * M) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hτ₁g, ← Matrix.mul_assoc]
      _ = ((-τ₁.det)⁻¹ * c⁻¹) • (g * rho0N ℓ * M) := by rw [hXg]
      _ = _ := by rw [hk, Matrix.mul_smul, smul_smul, tau0N, Matrix.mul_assoc]
  · rw [hτ₁g, hk, Matrix.mul_smul]
  · calc τ₂ * g = ((-τ₁.det)⁻¹ * c'⁻¹) • (τ₁ * Y) * g := by rw [← hτ₂]
      _ = ((-τ₁.det)⁻¹ * c'⁻¹) • (τ₁ * g * rho1N b) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hYg, ← Matrix.mul_assoc]
      _ = ((-τ₁.det)⁻¹ * c'⁻¹) • (g * M * rho1N b) := by rw [hτ₁g]
      _ = _ := by rw [hk, Matrix.mul_smul, Matrix.smul_mul, smul_smul, tau2N, Matrix.mul_assoc]

theorem conj_trans {A A' N g g' : Matrix (Fin 2) (Fin 2) K} {c c' : K} (hg' : g'.det ≠ 0)
    (hA' : A'.det ≠ 0) (H : A * g = c • (g * N)) (H' : A' * g' = c' • (g' * N)) :
    A * (g * g'⁻¹) = (c * c'⁻¹) • (g * g'⁻¹ * A') := by
  have hgu' := isUnit_iff_ne_zero.2 hg'
  have hc' : c' ≠ 0 := by
    rintro rfl
    simpa [hA', hg'] using congrArg Matrix.det H'
  have H1 : g'⁻¹ * A' = c' • (N * g'⁻¹) := by
    calc g'⁻¹ * A' = g'⁻¹ * (A' * g') * g'⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right g' A' hgu']
      _ = c' • (N * g'⁻¹) := by
          rw [H', Matrix.mul_smul, Matrix.smul_mul, Matrix.nonsing_inv_mul_cancel_left g' N hgu']
  have H2 : N * g'⁻¹ = c'⁻¹ • (g'⁻¹ * A') := by
    rw [H1, smul_smul, inv_mul_cancel₀ hc', one_smul]
  calc A * (g * g'⁻¹) = c • (g * (N * g'⁻¹)) := by
        rw [← Matrix.mul_assoc, H, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (c * c'⁻¹) • (g * g'⁻¹ * A') := by
        rw [H2, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]

/-- **Page 4, part 2), over a field containing a root of `T² − α₀T + 1`.** Two triples with
the same invariants `(α₀, α₁)` are conjugate in `PGL₂(K)`. -/
theorem conj_of_same_invariants {τ₀ τ₁ τ₂ σ₀ σ₁ σ₂ : Matrix (Fin 2) (Fin 2) K}
    (d0 : τ₀.det ≠ 0) (d1 : τ₁.det ≠ 0) (d2 : τ₂.det ≠ 0)
    (h0 : τ₀.trace = 0) (h1 : τ₁.trace = 0) (h2 : τ₂.trace = 0) (h02 : (τ₀ * τ₂).trace = 0)
    (d0' : σ₀.det ≠ 0) (d1' : σ₁.det ≠ 0) (d2' : σ₂.det ≠ 0)
    (h0' : σ₀.trace = 0) (h1' : σ₁.trace = 0) (h2' : σ₂.trace = 0) (h02' : (σ₀ * σ₂).trace = 0)
    (hU : discr (invA (τ₀ * τ₁)) (invA (τ₁ * τ₂)) ≠ 0)
    (e0 : invA (σ₀ * σ₁) = invA (τ₀ * τ₁)) (e1 : invA (σ₁ * σ₂) = invA (τ₁ * τ₂))
    {ℓ : K} (hℓ : ℓ ^ 2 - invA (τ₀ * τ₁) * ℓ + 1 = 0) :
    ∃ h : Matrix (Fin 2) (Fin 2) K, h.det ≠ 0 ∧ ∃ c₀ c₁ c₂ : K,
      τ₀ * h = c₀ • (h * σ₀) ∧ τ₁ * h = c₁ • (h * σ₁) ∧ τ₂ * h = c₂ • (h * σ₂) := by
  obtain ⟨g, hg, c₀, c₁, c₂, H0, H1, H2⟩ := conj_normalForm d0 d1 d2 h0 h1 h2 h02 hU hℓ
  obtain ⟨g', hg', c₀', c₁', c₂', H0', H1', H2'⟩ := conj_normalForm d0' d1' d2' h0' h1' h2' h02'
    (by rw [e0, e1]; exact hU) (by rw [e0]; exact hℓ)
  rw [e1] at H0' H1' H2'
  refine ⟨g * g'⁻¹, ?_, _, _, _, conj_trans hg' d0' H0 H0', conj_trans hg' d1' H1 H1',
    conj_trans hg' d2' H2 H2'⟩
  rw [det_mul]
  exact ((isUnit_iff_ne_zero.2 hg).mul
    (Matrix.isUnit_nonsing_inv_det g' (isUnit_iff_ne_zero.2 hg'))).ne_zero

/-- The three finite cases of pages 8–10: the discriminant is `−2`, `−2`, `−1`. -/
theorem discr_tetra : discr (-1 : R) (-1) = -2 := by unfold discr; ring
theorem discr_octa : discr (0 : R) (-1) = -2 := by unfold discr; ring
theorem discr_icosa {a : R} (h : a ^ 2 + a - 1 = 0) : discr (-1 : R) a = -1 := by
  unfold discr; linear_combination h

end Conjugacy

/-! ## Representations of `𝔻_∞` (pages 16 to 20), finding `85-dinfty-torsor-classification` -/

section Dinfty

variable {K : Type*} [Field K]

/-- A homomorphism `𝔻_∞ = ⟨τ₀, τ₁ | τ₀², τ₁²⟩ → PGL₂(K)` with `u² ≠ 1`, `u = φ(τ₀τ₁)`,
given by lifts `t₀, t₁ ∈ GL₂(K)`. -/
def DRep (t₀ t₁ : Matrix (Fin 2) (Fin 2) K) : Prop :=
  t₀.det ≠ 0 ∧ t₁.det ≠ 0 ∧ IsScalar (t₀ * t₀) ∧ IsScalar (t₁ * t₁) ∧
    ¬ IsScalar (t₀ * t₁ * (t₀ * t₁))

/-- Conjugacy in `PGL₂(K)` of two pairs. -/
def PConj (t₀ t₁ s₀ s₁ : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ g : Matrix (Fin 2) (Fin 2) K, g.det ≠ 0 ∧ ∃ c₀ c₁ : K,
    t₀ * g = c₀ • (g * s₀) ∧ t₁ * g = c₁ • (g * s₁)

/-- The companion matrix of `T² − τT + d`. -/
def compD (τ d : K) : Matrix (Fin 2) (Fin 2) K := !![0, -d; 1, τ]

/-- The normal form of `t₀` in the basis `(v, uv)`. -/
def invD (τ d p r : K) : Matrix (Fin 2) (Fin 2) K := !![p, τ * p + d * r; r, -p]

/-- The binary form `p² + τpr + dr²`, the norm of `ℤ[u]`. -/
def normD (τ d p r : K) : K := p ^ 2 + τ * p * r + d * r ^ 2

theorem det_invD (τ d p r : K) : (invD τ d p r).det = -normD τ d p r := by
  simp [invD, normD, det_fin_two]; ring

theorem isScalar_smul_mul {c : K} {M : Matrix (Fin 2) (Fin 2) K} (h : IsScalar M) :
    IsScalar (c • M) := by
  obtain ⟨a, rfl⟩ := h; exact ⟨c * a, by rw [smul_smul]⟩

theorem DRep.facts {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h : DRep t₀ t₁) :
    t₀.trace = 0 ∧ t₁.trace = 0 ∧ (t₀ * t₁).trace ≠ 0 ∧ ¬ IsScalar (t₀ * t₁) := by
  obtain ⟨-, -, s0, s1, hu⟩ := h
  have n0 : ¬ IsScalar t₀ := by
    rintro ⟨c, rfl⟩
    apply hu
    obtain ⟨a, ha⟩ := s1
    refine ⟨c ^ 2 * a, ?_⟩
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, ha, smul_smul]
    ring_nf
  have n1 : ¬ IsScalar t₁ := by
    rintro ⟨c, rfl⟩
    apply hu
    obtain ⟨a, ha⟩ := s0
    refine ⟨c ^ 2 * a, ?_⟩
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ha, smul_smul]
    ring_nf
  have h0 := trace_eq_zero_of_isScalar_mul ((nps_iff_not_isScalar _).2 n0) s0
  have h1 := trace_eq_zero_of_isScalar_mul ((nps_iff_not_isScalar _).2 n1) s1
  refine ⟨h0, h1, ?_, ?_⟩
  · intro ht
    apply hu
    rw [sq_eq_trace, ht, zero_smul, zero_sub]
    exact ⟨-(t₀ * t₁).det, by rw [neg_smul]⟩
  · rintro ⟨c, hc⟩
    exact hu ⟨c ^ 2, by
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]; ring_nf⟩


/-- `t₀ u t₀⁻¹ = Tr u − u`: `t₀` inverts `u` in `PGL₂`. -/
theorem t0_mul_u {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h0 : t₀.trace = 0) (h1 : t₁.trace = 0) :
    t₀ * (t₀ * t₁) = ((t₀ * t₁).trace • (1 : Matrix (Fin 2) (Fin 2) K) - t₀ * t₁) * t₀ := by
  have e := mul_add_mul t₀ t₁
  rw [h0, h1, zero_smul, zero_smul, add_zero, mul_zero, sub_zero, zero_add] at e
  rw [← e, add_sub_cancel_left, ← Matrix.mul_assoc, Matrix.mul_assoc t₁,
    mul_self_of_trace_zero h0, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- A cyclic vector: a non-scalar `u` has `v` with `(v, uv)` a basis. -/
theorem exists_cyclic {u : Matrix (Fin 2) (Fin 2) K} (hu : ¬ IsScalar u) :
    ∃ v₀ v₁ : K, v₀ * (u 1 0 * v₀ + u 1 1 * v₁) - v₁ * (u 0 0 * v₀ + u 0 1 * v₁) ≠ 0 := by
  rw [isScalar_iff] at hu
  by_cases h10 : u 1 0 = 0
  · by_cases h01 : u 0 1 = 0
    · refine ⟨1, 1, ?_⟩
      have : u 0 0 ≠ u 1 1 := fun h => hu ⟨h01, h10, h⟩
      rw [h10, h01]
      intro h; exact this (by linear_combination -h)
    · exact ⟨0, 1, by simpa using h01⟩
  · exact ⟨1, 0, by simpa using h10⟩

/-- **Normal form of a representation of `𝔻_∞`.** In the basis `(v, uv)`, `u = t₀t₁` is the
companion matrix of `T² − τT + d` and `t₀` is `invD τ d p r`. -/
theorem exists_normal {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h : DRep t₀ t₁) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, g.det ≠ 0 ∧ ∃ p r : K,
      t₀ * g = g * invD (t₀ * t₁).trace (t₀ * t₁).det p r ∧
      t₀ * t₁ * g = g * compD (t₀ * t₁).trace (t₀ * t₁).det := by
  obtain ⟨h0, h1, -, hu⟩ := h.facts
  obtain ⟨v₀, v₁, hv⟩ := exists_cyclic hu
  set u := t₀ * t₁ with hudef
  set g : Matrix (Fin 2) (Fin 2) K :=
    !![v₀, u 0 0 * v₀ + u 0 1 * v₁; v₁, u 1 0 * v₀ + u 1 1 * v₁] with hgdef
  have hg : g.det ≠ 0 := by rw [hgdef, det_fin_two_of]; convert hv using 1; ring
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have hC : u * g = g * compD u.trace u.det := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hgdef, compD, Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring
  set X := g⁻¹ * t₀ * g with hXdef
  have hX : t₀ * g = g * X := by
    rw [hXdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgu,
      Matrix.one_mul]
  have hXt : X.trace = 0 := by rw [hXdef, trace_conj hgu, h0]
  have hXC : X * compD u.trace u.det = (u.trace • 1 - compD u.trace u.det) * X := by
    have k : g * (compD u.trace u.det * X) = u * (t₀ * g) := by
      rw [← Matrix.mul_assoc, ← hC, Matrix.mul_assoc, ← hX]
    have e : g * (X * compD u.trace u.det) = g * ((u.trace • 1 - compD u.trace u.det) * X) := by
      calc g * (X * compD u.trace u.det) = t₀ * (t₀ * t₁) * g := by
            rw [← Matrix.mul_assoc, ← hX, Matrix.mul_assoc, ← hC]
            simp only [hudef, Matrix.mul_assoc]
        _ = (u.trace • 1 - u) * (t₀ * g) := by rw [t0_mul_u h0 h1, Matrix.mul_assoc]
        _ = _ := by
            rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, k, Matrix.smul_mul, Matrix.smul_mul,
              Matrix.one_mul, Matrix.one_mul, Matrix.mul_smul, hX]
    have := congrArg (g⁻¹ * ·) e
    simpa only [Matrix.nonsing_inv_mul_cancel_left g _ hgu] using this
  refine ⟨g, hg, X 0 0, X 1 0, ?_, hC⟩
  rw [hX]
  congr 1
  have e00 := congrFun (congrFun hXC 0) 0
  simp [compD, Matrix.mul_apply, Fin.sum_univ_two] at e00
  rw [trace_fin_two] at hXt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invD]
  · linear_combination e00
  · linear_combination hXt

/-- Scaling: `(τ, d)` and `(cτ, c²d)` give conjugate normal forms. -/
theorem scale_normal {τ d p r c : K} (hc : c ≠ 0) :
    invD (c * τ) (c ^ 2 * d) p r * !![1, 0; 0, c⁻¹] = !![1, 0; 0, c⁻¹] * invD τ d p (c * r) ∧
    compD (c * τ) (c ^ 2 * d) * !![1, 0; 0, c⁻¹] = c • (!![1, 0; 0, c⁻¹] * compD τ d) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [invD, compD, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- An element `a + bC` of `K[C]`, `C = compD τ d`. -/
def zD (τ d a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, -d * b; b, a + τ * b]

theorem comm_zD (τ d a b : K) : compD τ d * zD τ d a b = zD τ d a b * compD τ d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zD, compD, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- **Hilbert 90 for `K[C]`.** If `N(p, r) = e² N(p', r')`, the two normal forms of `t₀` are
conjugate by an element of `K[C]^×`, the torus of `u`. -/
theorem hilbert90 {τ d p r p' r' e : K} (hτ : τ ≠ 0) (hB : normD τ d p' r' ≠ 0)
    (hrel : normD τ d p r = e ^ 2 * normD τ d p' r') (he : e ≠ 0) :
    ∃ z : Matrix (Fin 2) (Fin 2) K, z.det ≠ 0 ∧ ∃ c : K,
      invD τ d p r * z = c • (z * invD τ d p' r') ∧ compD τ d * z = z * compD τ d := by
  -- the candidates `f + ȳ` (for `±e`) and `f C + ȳ C̄`, `y = w w̄'`, `f = e N(w')`
  set N := normD τ d p' r' with hN
  set Q := p * p' + τ * p * r' + d * r * r' with hQd
  set a₃ := -d * p * r' + d * p' * r + d * r * r' * τ + p * p' * τ + p * r' * τ ^ 2 with ha₃
  have z1 : ∀ e' : K, normD τ d p r = e' ^ 2 * N →
      invD τ d p r * zD τ d (Q + e' * N) (p' * r - p * r') =
        e' • (zD τ d (Q + e' * N) (p' * r - p * r') * invD τ d p' r') := by
    intro e' h
    unfold normD at h hN
    rw [hN] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [invD, zD, Matrix.mul_apply, Fin.sum_univ_two, hN, hQd]
    · linear_combination p' * h
    · linear_combination (d * r' + p' * τ) * h
    · linear_combination r' * h
    · linear_combination (-p') * h
  have z3 : invD τ d p r * zD τ d a₃ (e * N - Q) =
      e • (zD τ d a₃ (e * N - Q) * invD τ d p' r') := by
    unfold normD at hrel hN
    rw [hN] at hrel
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [invD, zD, Matrix.mul_apply, Fin.sum_univ_two, hN, hQd, ha₃]
    · linear_combination (-d * r') * hrel
    · linear_combination (d * p') * hrel
    · linear_combination (p' + r' * τ) * hrel
    · linear_combination (d * r') * hrel
  have hrel' : normD τ d p r = (-e) ^ 2 * N := by rw [hrel]; ring
  have d1 : ∀ e' : K, (zD τ d (Q + e' * N) (p' * r - p * r')).det
      = N * normD τ d (p + e' * p') (r + e' * r') := by
    intro e'; simp [zD, normD, det_fin_two, hN, hQd]; ring
  have d3 : (zD τ d a₃ (e * N - Q)).det = N * (e * τ ^ 2 * Q + d * (normD τ d p r + e ^ 2 * N)
      + e * τ * d * (p * r' + p' * r) - 2 * d * e * (d * r * r' + p * p' + 2 * p * r' * τ)) := by
    simp [zD, normD, det_fin_two, hN, hQd, ha₃]; ring
  by_cases k1 : normD τ d (p + e * p') (r + e * r') ≠ 0
  · exact ⟨_, by rw [d1]; exact mul_ne_zero hB k1, e, z1 e hrel, comm_zD _ _ _ _⟩
  by_cases k2 : normD τ d (p + -e * p') (r + -e * r') ≠ 0
  · exact ⟨_, by rw [d1]; exact mul_ne_zero hB k2, -e, z1 (-e) hrel', comm_zD _ _ _ _⟩
  push Not at k1 k2
  refine ⟨_, ?_, e, z3, comm_zD _ _ _ _⟩
  rw [d3]
  refine mul_ne_zero hB fun k3 => ?_
  unfold normD at k1 k2 k3 hrel hN
  have hBe : e ^ 2 * N ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hB
  have h4 : 4 * (e ^ 2 * N) = 0 := by linear_combination k1 + k2 - 2 * hrel + 2 * e ^ 2 * hN
  have h2 : (2 : K) = 0 := by
    have : (2 : K) * 2 = 0 := by
      linear_combination (mul_eq_zero.1 h4).resolve_right hBe
    exact mul_self_eq_zero.1 this
  have hpr : e * τ * (p * r' + p' * r) = 0 := by
    linear_combination k1 - hrel - (e * (p * p' + d * r * r') + e ^ 2 * N) * h2 + e ^ 2 * hN
  have hpr' : p * r' + p' * r = 0 :=
    (mul_eq_zero.1 hpr).resolve_left (mul_ne_zero he hτ)
  have hQ : e * τ ^ 2 * Q = 0 := by
    linear_combination k3 - d * hrel - (d * e ^ 2 * N
      - d * e * (d * r * r' + p * p' + 2 * p * r' * τ)) * h2 - e * τ * d * hpr'
  have hQ' : Q = 0 := (mul_eq_zero.1 hQ).resolve_left (mul_ne_zero he (pow_ne_zero 2 hτ))
  have hsq : e ^ 2 * N * N = 0 := by
    linear_combination -hrel * N + Q * hQ' - a₃ * hpr' + (p' * r) * a₃ * h2
      + (p ^ 2 + τ * p * r + d * r ^ 2) * hN
  exact mul_ne_zero hBe hB hsq

theorem ne_zero_of_conj {A B g : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) (hg : g.det ≠ 0)
    {c : K} (h : A * g = c • (g * B)) : c ≠ 0 := by
  rintro rfl
  simpa [hA, hg] using congrArg Matrix.det h

/-- `A` is invariant under conjugacy in `PGL₂(K)`. -/
theorem invA_conj {A B g : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) (hg : g.det ≠ 0) {c : K}
    (h : A * g = c • (g * B)) : invA A = invA B := by
  have hc := ne_zero_of_conj hA hg h
  have hgu := isUnit_iff_ne_zero.2 hg
  have e : A = c • (g * B * g⁻¹) := by
    rw [← Matrix.smul_mul, ← h, Matrix.mul_nonsing_inv_cancel_right _ _ hgu]
  have ht : A.trace = c * B.trace := by
    rw [e, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
      Matrix.nonsing_inv_mul_cancel_left _ _ hgu]
  have hd : A.det = c ^ 2 * B.det := by
    rw [e, det_smul, Fintype.card_fin, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det g).2 hgu)]
  have hB : B.det ≠ 0 := by
    rintro hB; rw [hd, hB, mul_zero] at hA; exact hA rfl
  unfold invA
  simp only [ht, hd, Ring.inverse_eq_inv']
  field_simp

/-- From the conjugacy of `t₀` and of `u = t₀t₁`, that of `t₁`. -/
theorem conj_t1 {t₀ t₁ s₀ s₁ Γ : Matrix (Fin 2) (Fin 2) K} (h0 : t₀.det ≠ 0) {a b : K}
    (ha : a ≠ 0) (H0 : t₀ * Γ = a • (Γ * s₀)) (Hu : t₀ * t₁ * Γ = b • (Γ * (s₀ * s₁))) :
    t₁ * Γ = (b * a⁻¹) • (Γ * s₁) := by
  have hu := isUnit_iff_ne_zero.2 h0
  have e : Γ * s₀ = a⁻¹ • (t₀ * Γ) := by rw [H0, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have k : t₀ * (t₁ * Γ) = t₀ * ((b * a⁻¹) • (Γ * s₁)) := by
    rw [← Matrix.mul_assoc, Hu, ← Matrix.mul_assoc, e, Matrix.smul_mul, smul_smul,
      Matrix.mul_smul, Matrix.mul_assoc, mul_comm]
  have := congrArg (t₀⁻¹ * ·) k
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this

/-- **Classification of the representations of `𝔻_∞` in `PGL₂(K)` with `u² ≠ 1`, over a
field.** Two of them are conjugate if and only if they have the same invariant `α = A(u)` and
`det t₀` in the same square class. -/
theorem dinfty_conj_iff {t₀ t₁ s₀ s₁ : Matrix (Fin 2) (Fin 2) K} (ht : DRep t₀ t₁)
    (hs : DRep s₀ s₁) :
    PConj t₀ t₁ s₀ s₁ ↔ invA (t₀ * t₁) = invA (s₀ * s₁) ∧ ∃ e : K, t₀.det = e ^ 2 * s₀.det := by
  have dt0 := ht.1
  have dt1 := ht.2.1
  have ds0 := hs.1
  have ds1 := hs.2.1
  constructor
  · rintro ⟨g, hg, c₀, c₁, H0, H1⟩
    have hc₀ := ne_zero_of_conj dt0 hg H0
    have Hu : t₀ * t₁ * g = (c₀ * c₁) • (g * (s₀ * s₁)) := by
      rw [Matrix.mul_assoc, H1, Matrix.mul_smul, ← Matrix.mul_assoc, H0, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc, mul_comm]
    refine ⟨invA_conj (by rw [det_mul]; exact mul_ne_zero dt0 dt1) hg Hu, c₀, ?_⟩
    have := congrArg Matrix.det H0
    rw [det_mul, det_smul, det_mul, Fintype.card_fin] at this
    exact mul_right_cancel₀ hg (by linear_combination this)
  · rintro ⟨hA, e, he⟩
    obtain ⟨-, -, hτ, -⟩ := ht.facts
    obtain ⟨-, -, hτ', -⟩ := hs.facts
    have hd : (t₀ * t₁).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero dt0 dt1
    have hd' : (s₀ * s₁).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero ds0 ds1
    obtain ⟨g, hg, p, r, T0, Tu⟩ := exists_normal ht
    obtain ⟨g', hg', p', r', S0, Su⟩ := exists_normal hs
    set τ := (t₀ * t₁).trace
    set d := (t₀ * t₁).det
    obtain ⟨c, hcdef⟩ : ∃ c : K, c = (s₀ * s₁).trace / τ := ⟨_, rfl⟩
    have hc : c ≠ 0 := by rw [hcdef]; exact div_ne_zero hτ' hτ
    have eτ : (s₀ * s₁).trace = c * τ := by rw [hcdef]; field_simp
    have eA : τ ^ 2 * (s₀ * s₁).det = (s₀ * s₁).trace ^ 2 * d := by
      unfold invA at hA
      simp only [Ring.inverse_eq_inv'] at hA
      field_simp at hA
      linear_combination hA
    have ed : (s₀ * s₁).det = c ^ 2 * d := by
      rw [eτ] at eA
      exact mul_left_cancel₀ (pow_ne_zero 2 hτ) (by linear_combination eA)
    rw [eτ, ed] at S0 Su
    obtain ⟨S0', Su'⟩ := scale_normal (τ := τ) (d := d) (p := p') (r := r') hc
    set Dm : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, c⁻¹]
    have hDm : Dm.det = c⁻¹ := by simp [Dm, det_fin_two]
    set h' := g' * Dm
    have hh' : h'.det ≠ 0 := by rw [det_mul, hDm]; exact mul_ne_zero hg' (inv_ne_zero hc)
    have H0' : s₀ * h' = (1 : K) • (h' * invD τ d p' (c * r')) := by
      rw [one_smul, ← Matrix.mul_assoc, S0, Matrix.mul_assoc, S0', Matrix.mul_assoc]
    have Hu' : s₀ * s₁ * h' = c • (h' * compD τ d) := by
      rw [← Matrix.mul_assoc, Su, Matrix.mul_assoc, Su', Matrix.mul_smul, Matrix.mul_assoc]
    -- the norms
    have nt : t₀.det = -normD τ d p r := by
      have := congrArg Matrix.det T0
      rw [det_mul, det_mul, det_invD] at this
      exact mul_right_cancel₀ hg (by linear_combination this)
    have ns : s₀.det = -normD τ d p' (c * r') := by
      have := congrArg Matrix.det H0'
      rw [one_smul, Matrix.det_mul s₀, Matrix.det_mul h', det_invD] at this
      exact mul_right_cancel₀ hh' (by linear_combination this)
    have he0 : e ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero, zero_mul] at he; exact dt0 he
    have hB : normD τ d p' (c * r') ≠ 0 := fun h0 => ds0 (by rw [ns, h0, neg_zero])
    obtain ⟨z, hz, c₂, Z0, Zu⟩ := hilbert90 (p := p) (r := r) hτ hB
      (by linear_combination nt - e ^ 2 * ns - he) he0
    have G0 : t₀ * (g * z) = c₂ • (g * z * invD τ d p' (c * r')) := by
      rw [← Matrix.mul_assoc, T0, Matrix.mul_assoc, Z0, Matrix.mul_smul, Matrix.mul_assoc]
    have Gu : t₀ * t₁ * (g * z) = (1 : K) • (g * z * compD τ d) := by
      rw [one_smul, ← Matrix.mul_assoc, Tu, Matrix.mul_assoc, Zu, Matrix.mul_assoc]
    have K0 := conj_trans hh' ds0 G0 H0'
    have Ku := conj_trans hh' hd' Gu Hu'
    have hΓ : (g * z * h'⁻¹).det ≠ 0 := by
      rw [det_mul, det_mul]
      exact mul_ne_zero (mul_ne_zero hg hz)
        (Matrix.isUnit_nonsing_inv_det h' (isUnit_iff_ne_zero.2 hh')).ne_zero
    have ha := ne_zero_of_conj dt0 hΓ K0
    exact ⟨_, hΓ, _, _, K0, conj_t1 dt0 ha K0 Ku⟩

/-- `det [t₀, t₁] = det u · (2 − α)`: the commutator is invertible iff `ρ = 2 − α ≠ 0`. -/
theorem det_commD {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h0 : t₀.trace = 0) (h1 : t₁.trace = 0)
    (hd : (t₀ * t₁).det ≠ 0) :
    (t₀ * t₁ - t₁ * t₀).det = (t₀ * t₁).det * (2 - invA (t₀ * t₁)) := by
  rw [det_commutator, h0, h1, invA, Ring.inverse_eq_inv', det_mul]
  rw [det_mul] at hd
  have d0 := left_ne_zero_of_mul hd
  have d1 := right_ne_zero_of_mul hd
  field_simp
  ring

/-- `a t₀ + b t₀u = 0` forces `a = b = 0`. -/
theorem eq_zero_of_t0 {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h : DRep t₀ t₁) {a b : K}
    (e : a • t₀ + b • (t₀ * (t₀ * t₁)) = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨h0, -, -, hu⟩ := h.facts
  have dt0 := h.1
  have e' := congrArg (t₀ * ·) e
  simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, mul_self_of_trace_zero h0,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero, smul_smul] at e'
  have hb : b = 0 := by
    have k := (isScalar_smul_add_iff ((nps_iff_not_isScalar _).2 hu) (b * -t₀.det)
      (a * -t₀.det)).1 ⟨0, by rw [add_comm, e', zero_smul]⟩
    exact (mul_eq_zero.1 k).resolve_right (neg_ne_zero.2 dt0)
  refine ⟨?_, hb⟩
  rw [hb, zero_smul, add_zero] at e
  rcases smul_eq_zero.1 e with e | e
  · exact e
  · exact absurd (by simp [e]) dt0

/-- **Page 19: the automorphisms of a representation.** For `2 ≠ 0` in `K`, an element of
`GL₂(K)` normalises `t₀` and `t₁` up to scalars if and only if it is scalar or a multiple of
the commutator `t₀t₁ − t₁t₀` (the point of order 2 of the torus of `u`). -/
theorem centralizer_iff {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h : DRep t₀ t₁) (h2 : (2 : K) ≠ 0)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det ≠ 0) :
    (∃ c₀ c₁ : K, g * t₀ = c₀ • (t₀ * g) ∧ g * t₁ = c₁ • (t₁ * g)) ↔
      IsScalar g ∨ ∃ c : K, g = c • (t₀ * t₁ - t₁ * t₀) := by
  obtain ⟨h0, h1, hτ, hu⟩ := h.facts
  have hgu := isUnit_iff_ne_zero.2 hg
  set τ := (t₀ * t₁).trace
  have hsum : t₀ * t₁ + t₁ * t₀ = τ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e := mul_add_mul t₀ t₁
    rwa [h0, h1, zero_smul, zero_smul, add_zero, mul_zero, sub_zero, zero_add] at e
  have hut : t₀ * t₁ * t₀ = τ • t₀ - t₀ * (t₀ * t₁) := by
    rw [Matrix.mul_assoc, eq_sub_iff_add_eq, ← Matrix.mul_add, add_comm, hsum,
      Matrix.mul_smul, Matrix.mul_one]
  have hcomm : t₀ * t₁ - t₁ * t₀ = (2 : K) • (t₀ * t₁) - τ • 1 := by
    rw [← sub_eq_zero]
    linear_combination (norm := module) -hsum
  constructor
  · rintro ⟨c₀, c₁, H0, H1⟩
    have Hu : g * (t₀ * t₁) = (c₀ * c₁) • (t₀ * t₁ * g) := by
      rw [← Matrix.mul_assoc, H0, Matrix.smul_mul, Matrix.mul_assoc, H1, Matrix.mul_smul,
        smul_smul, Matrix.mul_assoc]
    have hc : c₀ * c₁ = 1 := by
      have e : (g⁻¹ * (g * (t₀ * t₁))).trace = (g⁻¹ * ((c₀ * c₁) • (t₀ * t₁ * g))).trace := by
        rw [Hu]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hgu, Matrix.mul_smul, Matrix.trace_smul,
        ← Matrix.mul_assoc, trace_conj hgu, smul_eq_mul] at e
      change τ = c₀ * c₁ * τ at e
      exact mul_right_cancel₀ hτ (by linear_combination -e)
    rw [hc, one_smul] at Hu
    obtain ⟨p, q, hpq⟩ := commutant_eq ((nps_iff_not_isScalar _).2 hu) Hu
    rw [hpq] at H0
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hut] at H0
    obtain ⟨e1, e2⟩ := eq_zero_of_t0 h (a := p + q * τ - c₀ * p) (b := -q - c₀ * q)
      (by linear_combination (norm := module) H0)
    by_cases hq : q = 0
    · exact Or.inl ⟨p, by rw [hpq, hq, zero_smul, add_zero]⟩
    · have hc₀ : c₀ = -1 := mul_left_cancel₀ hq (by linear_combination -e2)
      rw [hc₀] at e1
      refine Or.inr ⟨q / 2, ?_⟩
      rw [hpq, hcomm, smul_sub, smul_smul, smul_smul, div_mul_cancel₀ q h2,
        show p = -(q / 2 * τ) by field_simp; linear_combination e1]
      module
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨1, 1, by simp, by simp⟩
    · have hu1 : t₀ * t₁ * t₁ = (-t₁.det) • t₀ := by
        rw [Matrix.mul_assoc, mul_self_of_trace_zero h1, Matrix.mul_smul, Matrix.mul_one]
      have ht1 : t₁ * (t₀ * t₁) = τ • t₁ - (-t₁.det) • t₀ := by
        rw [← hu1, eq_sub_iff_add_eq, ← Matrix.mul_assoc, ← Matrix.add_mul, add_comm, hsum,
          Matrix.smul_mul, Matrix.one_mul]
      refine ⟨-1, -1, ?_, ?_⟩
      · rw [hcomm]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, hut]
        linear_combination (norm := module)
      · rw [hcomm]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, hu1, ht1]
        linear_combination (norm := module)

/-- The commutator is not scalar when `2 ≠ 0`: the two classes `1`, `[t₀, t₁]` are distinct. -/
theorem commD_not_isScalar {t₀ t₁ : Matrix (Fin 2) (Fin 2) K} (h : DRep t₀ t₁) (h2 : (2 : K) ≠ 0) :
    ¬ IsScalar (t₀ * t₁ - t₁ * t₀) := by
  obtain ⟨h0, h1, -, hu⟩ := h.facts
  have hsum : t₀ * t₁ + t₁ * t₀ = (t₀ * t₁).trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e := mul_add_mul t₀ t₁
    rwa [h0, h1, zero_smul, zero_smul, add_zero, mul_zero, sub_zero, zero_add] at e
  have e : t₀ * t₁ - t₁ * t₀ = (2 : K) • (t₀ * t₁) + (-(t₀ * t₁).trace) • 1 := by
    rw [← sub_eq_zero]; linear_combination (norm := module) -hsum
  rw [e, isScalar_smul_add_iff ((nps_iff_not_isScalar _).2 hu)]
  exact h2

/-- **Which classes occur.** A representation with invariant `α` and `−det t₀ = δ` exists in
`PGL₂(K)` if and only if `α + 2 ≠ 0`, `δ ≠ 0` and `δ` is a value of `p² + (α+2)pr + (α+2)r²`. -/
theorem exists_dinfty_iff (α δ : K) :
    (∃ t₀ t₁ : Matrix (Fin 2) (Fin 2) K, DRep t₀ t₁ ∧ invA (t₀ * t₁) = α ∧ -t₀.det = δ) ↔
      α + 2 ≠ 0 ∧ δ ≠ 0 ∧ ∃ p r : K, δ = normD (α + 2) (α + 2) p r := by
  constructor
  · rintro ⟨t₀, t₁, ht, rfl, rfl⟩
    obtain ⟨-, -, hτ, -⟩ := ht.facts
    have hd : (t₀ * t₁).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero ht.1 ht.2.1
    obtain ⟨g, hg, p, r, T0, -⟩ := exists_normal ht
    have nt : t₀.det = -normD (t₀ * t₁).trace (t₀ * t₁).det p r := by
      have := congrArg Matrix.det T0
      rw [det_mul, det_mul, det_invD] at this
      exact mul_right_cancel₀ hg (by linear_combination this)
    have hA : invA (t₀ * t₁) + 2 = (t₀ * t₁).trace ^ 2 / (t₀ * t₁).det := by
      rw [invA, Ring.inverse_eq_inv']; ring
    refine ⟨by rw [hA]; exact div_ne_zero (pow_ne_zero 2 hτ) hd, neg_ne_zero.2 ht.1,
      p, r * (t₀ * t₁).det / (t₀ * t₁).trace, ?_⟩
    rw [hA, nt, neg_neg]
    unfold normD
    field_simp
  · rintro ⟨ha, hδ, p, r, rfl⟩
    set a := α + 2
    set t₀ := invD a a p r
    have h0 : t₀.trace = 0 := by simp [t₀, invD, trace_fin_two]
    have d0 : t₀.det = -normD a a p r := det_invD a a p r
    have sq0 : t₀ * t₀ = normD a a p r • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [mul_self_of_trace_zero h0, d0, neg_neg]
    have hC : (compD a a).det = a := by simp [compD, det_fin_two]
    have hu : t₀ * ((normD a a p r)⁻¹ • (t₀ * compD a a)) = compD a a := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, sq0, Matrix.smul_mul, Matrix.one_mul, smul_smul,
        inv_mul_cancel₀ hδ, one_smul]
    have h1' : (t₀ * compD a a).trace = 0 := by
      simp [t₀, invD, compD, trace_fin_two]; ring
    have h1 : ((normD a a p r)⁻¹ • (t₀ * compD a a)).trace = 0 := by
      rw [Matrix.trace_smul, h1', smul_zero]
    refine ⟨t₀, _, ⟨by rw [d0]; exact neg_ne_zero.2 hδ, ?_, ⟨_, sq0⟩,
      ⟨_, mul_self_of_trace_zero h1⟩, ?_⟩, ?_, by rw [d0, neg_neg]⟩
    · rw [det_smul, det_mul, d0, hC, Fintype.card_fin]
      exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hδ)) (mul_ne_zero (neg_ne_zero.2 hδ) ha)
    · rw [hu, isScalar_iff]
      rintro ⟨-, h10, -⟩
      apply ha
      simpa [compD, Matrix.mul_apply, Fin.sum_univ_two] using h10
    · rw [hu, invA, Ring.inverse_eq_inv', hC]
      simp only [compD, trace_fin_two, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one]
      field_simp
      ring

/-- **The page-17 equivalence fails as read, over `ℚ`.** Two representations with the same
invariant `α = −6` (so `ρ = 8` invertible and `𝒰_ρ ≅ 𝔾_m`) that are not conjugate in
`PGL₂(ℚ)`: `det t₀ = −1` and `det s₀ = 1` are in different square classes. -/
theorem dinfty_not_conj_rat :
    DRep !![(1 : ℚ), 0; 0, -1] !![1, 1; -2, -1] ∧ DRep !![(0 : ℚ), 1; -1, 0] !![1, 0; 2, -1] ∧
    invA (!![(1 : ℚ), 0; 0, -1] * !![1, 1; -2, -1]) = -6 ∧
    invA (!![(0 : ℚ), 1; -1, 0] * !![1, 0; 2, -1]) = -6 ∧
    ¬ PConj !![(1 : ℚ), 0; 0, -1] !![1, 1; -2, -1] !![0, 1; -1, 0] !![1, 0; 2, -1] := by
  have r1 : DRep !![(1 : ℚ), 0; 0, -1] !![1, 1; -2, -1] := by
    refine ⟨by norm_num [det_fin_two], by norm_num [det_fin_two], (isScalar_iff _).2 ?_,
      (isScalar_iff _).2 ?_, fun h => ?_⟩
    · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · have := ((isScalar_iff _).1 h).1
      norm_num [Matrix.mul_apply, Fin.sum_univ_two] at this
  have r2 : DRep !![(0 : ℚ), 1; -1, 0] !![1, 0; 2, -1] := by
    refine ⟨by norm_num [det_fin_two], by norm_num [det_fin_two], (isScalar_iff _).2 ?_,
      (isScalar_iff _).2 ?_, fun h => ?_⟩
    · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · have := ((isScalar_iff _).1 h).1
      norm_num [Matrix.mul_apply, Fin.sum_univ_two] at this
  have a1 : invA (!![(1 : ℚ), 0; 0, -1] * !![1, 1; -2, -1]) = -6 := by
    simp [invA, trace_fin_two, det_fin_two]; norm_num
  have a2 : invA (!![(0 : ℚ), 1; -1, 0] * !![1, 0; 2, -1]) = -6 := by
    simp [invA, trace_fin_two, det_fin_two]; norm_num
  refine ⟨r1, r2, a1, a2, fun h => ?_⟩
  obtain ⟨-, e, he⟩ := (dinfty_conj_iff r1 r2).1 h
  simp [det_fin_two] at he
  nlinarith [sq_nonneg e]

/-- « `u² ≠ 1` everywhere, that is `α + 2` invertible » is not an equivalence: `t₁ = t₀` has
`u = 1`, `α = 2`, `α + 2 = 4 ≠ 0`. -/
theorem dinfty_add_two_not_iff :
    invA (!![(1 : ℚ), 0; 0, -1] * !![1, 0; 0, -1]) = 2 ∧
      ¬ DRep !![(1 : ℚ), 0; 0, -1] !![1, 0; 0, -1] := by
  refine ⟨by simp [invA, trace_fin_two, det_fin_two]; norm_num,
    fun h => h.2.2.2.2 ((isScalar_iff _).2 ?_)⟩
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end Dinfty

end Grothendieck.Folder85
