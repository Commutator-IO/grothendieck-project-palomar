module

public import Mathlib

@[expose] public section

open TensorProduct

namespace Grothendieck.Folder128.Descent

universe u

section Defs

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A descent datum on an `S`-module `E` relative to `R → S` (Grothendieck, page 4), written as
a comodule over the coring `S ⊗_R S`: an `S`-linear `ψ : E → S ⊗_R E` (`ψ(e) = φ(1 ⊗ e)` for
the gluing isomorphism `φ`), with counit `Σ bᵢ eᵢ = e` and the cocycle condition. -/
structure DescentDatum (E : Type u) [AddCommGroup E] [Module S E] [Module R E]
    [IsScalarTower R S E] where
  /-- The coaction `e ↦ Σ bᵢ ⊗ eᵢ`. -/
  ψ : E →ₗ[S] S ⊗[R] E
  /-- Counit: `Σ bᵢ eᵢ = e`. -/
  counit : ∀ e, LinearMap.liftBaseChange S (LinearMap.id : E →ₗ[R] E) (ψ e) = e
  /-- Cocycle: `Σ bᵢ ⊗ ψ(eᵢ) = Σ bᵢ ⊗ 1 ⊗ eᵢ`. -/
  coassoc : ∀ e, (ψ.restrictScalars R).lTensor S (ψ e) =
    (TensorProduct.mk R S E 1).lTensor S (ψ e)

variable {R S}

namespace DescentDatum

variable {E : Type u} [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]

/-- The invariants `{e | ψ(e) = 1 ⊗ e}` (the `H⁰` of the descent complex). -/
def invariants (d : DescentDatum R S E) : Submodule R E :=
  LinearMap.eqLocus (d.ψ.restrictScalars R) (TensorProduct.mk R S E 1)

/-- The datum is effective: its invariants `E₀` are flat and `S ⊗_R E₀ → E` is bijective, so the
datum is isomorphic to the canonical one on `S ⊗_R E₀`. -/
def IsEffective (d : DescentDatum R S E) : Prop :=
  Module.Flat R d.invariants ∧
    Function.Bijective (LinearMap.liftBaseChange S d.invariants.subtype)

end DescentDatum

variable (R S) in
/-- The canonical descent datum on `S ⊗_R M`, `b ⊗ m ↦ b ⊗ 1 ⊗ m`. -/
noncomputable def canonical (M : Type u) [AddCommGroup M] [Module R M] :
    DescentDatum R S (S ⊗[R] M) where
  ψ := (TensorProduct.mk R S M 1).baseChange S
  counit x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy]
  coassoc x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp
    | add x y hx hy => simp only [map_add, hx, hy]

variable (R S) in
/-- `Spec S → Spec R` is a descent morphism for flat modules: for `M` flat, `M → S ⊗_R M` is
injective with image the invariants of the canonical datum (`M ≅ H⁰(S/R, M)`). -/
def IsDescentFlat : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M],
    Function.Injective (TensorProduct.mk R S M 1) ∧
      (canonical R S M).invariants ≤ LinearMap.range (TensorProduct.mk R S M 1)

variable (R S) in
/-- `Spec S → Spec R` is an effective descent morphism for flat modules: a descent morphism, and
every descent datum on a flat `S`-module is effective. -/
def IsEffectiveDescentFlat : Prop :=
  IsDescentFlat R S ∧
    ∀ (E : Type u) [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]
      [Module.Flat S E] (d : DescentDatum R S E), d.IsEffective

end Defs

section Reduction

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]

variable (S) in
/-- `I` is an ideal of `A` mapped injectively onto an ideal of `S` (Grothendieck, page 1): `I`
lies in the conductor, and `A → S`, `A/I → S/IS` is a Milnor square. -/
structure IsConductorIdeal (I : Ideal A) : Prop where
  inj : ∀ x ∈ I, algebraMap A S x = 0 → x = 0
  ideal : ∀ x ∈ I, ∀ b : S, ∃ y ∈ I, b * algebraMap A S x = algebraMap A S y

variable {I : Ideal A}

variable (I) {N : Type u} [AddCommGroup N] [Module A N]
  {M₀ : Type u} [AddCommMonoid M₀] [Module (A ⧸ I) M₀] [Module A M₀]
  [IsScalarTower A (A ⧸ I) M₀]

variable {I}

end Reduction

section Main

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {I : Ideal A}
  {E : Type u} [AddCommGroup E] [Module S E] [Module A E] [IsScalarTower A S E]

/-- **Folder 128, Cor. 1** (Grothendieck, page 7). Let `I` be a nilpotent ideal of `A` mapped
isomorphically onto an ideal of `S` (`I` in the conductor). If `Spec S/IS → Spec A/I` is an
effective descent morphism for flat modules, so is `Spec S → Spec A`. -/
theorem isEffectiveDescentFlat_of_quotient (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    (h₀ : IsEffectiveDescentFlat (A ⧸ I) (S ⧸ I.map (algebraMap A S))) :
    IsEffectiveDescentFlat A S := by
  sorry

end Main

end Grothendieck.Folder128.Descent
