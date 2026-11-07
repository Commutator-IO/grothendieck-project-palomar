module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder101

open IsLocalRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- `A` inside its fraction field `K`. -/
abbrev Aₖ : Submodule A K := LinearMap.range (Algebra.linearMap A K)

/-- `K/A = H¹_x(O_X)`, the module `I` of the page. -/
abbrev KA := K ⧸ Aₖ A K

variable {A K}

variable {M₀ M₁ : Type*} [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module K M₁]
  [Module A M₁] [IsScalarTower A K M₁] (u : M₀ →ₗ[A] M₁)

variable (K) in
/-- `Ext⁰(X; F, O_X)` for `F = (M₀, M₁, u)`: the kernel of
`Hom_K(M₁, K) → Hom_A(M₀, K/A)`, `g ↦ g ∘ u mod A`. -/
def Ext0 := {g : M₁ →ₗ[K] K // ∀ m, g (u m) ∈ Aₖ A K}

/-- The duality map on `Ext⁰`, to `Hom_A(Coker u, K/A) = Hom_A(H¹_x(F), I)`. -/
def phi0 (g : Ext0 K u) : (M₁ ⧸ LinearMap.range u) →ₗ[A] KA A K :=
  (LinearMap.range u).liftQ ((Aₖ A K).mkQ ∘ₗ g.1.restrictScalars A) (by
    rintro _ ⟨m, rfl⟩
    simpa [LinearMap.mem_ker] using g.2 m)

variable (K) in
/-- The image of `Hom_K(M₁, K) → Hom_A(M₀, K/A)`. -/
def imD : Submodule A (M₀ →ₗ[A] KA A K) where
  carrier := {h | ∃ g : M₁ →ₗ[K] K, ∀ m, h m = Submodule.Quotient.mk (g (u m))}
  add_mem' := fun ⟨g, hg⟩ ⟨g', hg'⟩ => ⟨g + g', fun m => by simp [hg, hg']⟩
  zero_mem' := ⟨0, fun m => by simp⟩
  smul_mem' a _ := fun ⟨g, hg⟩ => ⟨algebraMap A K a • g, fun m => by
    simp [hg, Algebra.smul_def, ← Submodule.Quotient.mk_smul]⟩

variable (K) in
/-- `Ext¹(X; F, O_X)`: the cokernel of `Hom_K(M₁, K) → Hom_A(M₀, K/A)`. -/
abbrev Ext1 := (M₀ →ₗ[A] KA A K) ⧸ imD K u

/-- The duality map on `Ext¹`, to `Hom_A(Ker u, K/A) = Hom_A(H⁰_x(F), I)`: restriction. -/
def phi1 : Ext1 K u →ₗ[A] (LinearMap.ker u →ₗ[A] KA A K) :=
  (imD K u).liftQ (LinearMap.lcomp A _ (LinearMap.ker u).subtype) (by
    rintro h ⟨g, hg⟩
    rw [LinearMap.mem_ker]
    ext ⟨m, hm⟩
    simp [hg, LinearMap.mem_ker.1 hm])

/-- **Local duality in dimension one, for every `O_X`-module** (pages 10–11), in the page's
model: for `A` a complete discrete valuation ring and any triple `(M₀, M₁, u)`, the duality
maps `Ext⁰ → Hom_A(Coker u, K/A)` and `Ext¹ → Hom_A(Ker u, K/A)` are bijective. -/
theorem duality_dim_one [IsAdicComplete (maximalIdeal A) A] :
    Function.Bijective (phi0 (K := K) u) ∧ Function.Bijective (phi1 (K := K) u) := by
  sorry

end Grothendieck.Folder101
