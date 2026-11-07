module

public import Mathlib

@[expose] public section

open TensorProduct LinearMap

namespace Grothendieck.Folder90Comodules

variable {A : Type*} [CommRing A]

/-- A comodule over an `A`-coalgebra `B`: an `A`-module `E` with a coaction `δ : E → B ⊗ E`,
counital and coassociative (page 7 of folder 90; « `A`-`G`-module »). -/
class Comodule (A : Type*) (B E : Type*) [CommRing A] [AddCommGroup B] [Module A B]
    [Coalgebra A B] [AddCommGroup E] [Module A E] where
  coact : E →ₗ[A] B ⊗[A] E
  counit_coact : (TensorProduct.lid A E).toLinearMap ∘ₗ
    (Coalgebra.counit (R := A) (A := B)).rTensor E ∘ₗ coact = LinearMap.id
  coassoc : (TensorProduct.assoc A B B E).toLinearMap ∘ₗ
    (Coalgebra.comul (R := A) (A := B)).rTensor E ∘ₗ coact = coact.lTensor B ∘ₗ coact

variable {B E : Type*} [AddCommGroup B] [Module A B] [Coalgebra A B] [AddCommGroup E] [Module A E]

/-- A submodule `N ⊆ E` is a **subcomodule** (« stable par `G` ») if `δ N ⊆ B ⊗ N`. -/
def IsSubcomodule (B : Type*) [AddCommGroup B] [Module A B] [Coalgebra A B]
    [Comodule A B E] (N : Submodule A E) : Prop :=
  ∀ e ∈ N, Comodule.coact (A := A) (B := B) e ∈ LinearMap.range (N.subtype.lTensor B)

/-- The hypothesis of pages 7 and 13: `B` is the filtered union of submodules `Bᵢ`, finite
projective, with `B ⧸ Bᵢ` flat and `Δ Bᵢ ⊆ Bᵢ ⊗ Bᵢ`. -/
structure Exhaustion (A : Type*) (B : Type*) [CommRing A] [AddCommGroup B] [Module A B]
    [Coalgebra A B] (ι : Type*) where
  Bi : ι → Submodule A B
  nonempty : Nonempty ι
  directed : Directed (· ≤ ·) Bi
  exhaustive : ∀ b : B, ∃ i, b ∈ Bi i
  finite : ∀ i, Module.Finite A (Bi i)
  projective : ∀ i, Module.Projective A (Bi i)
  flat : ∀ i, Module.Flat A (B ⧸ Bi i)
  comul_mem : ∀ i, ∀ b ∈ Bi i, Coalgebra.comul (R := A) b ∈
    LinearMap.range (TensorProduct.map (Bi i).subtype (Bi i).subtype)

namespace Exhaustion

variable {ι : Type*} (H : Exhaustion A B ι)

variable (E) in
/-- The action of `u ∈ Uᵢ` on an element `y ∈ Bᵢ ⊗ E`: `(u ⊗ id) y ∈ E`. When `y` is the
coaction of `e`, this is `u · e` of page 7. -/
noncomputable def coeff (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) : E :=
  TensorProduct.lid A E (u.rTensor E y)

section Comodule

variable [Comodule A B E]

/-- The generators `u · (F ∩ Eᵢ)` of `F′`: the `(u ⊗ id) y` with `y ∈ Bᵢ ⊗ E` lifting `δ f`,
`f ∈ F`, `u ∈ Uᵢ`. -/
def lifts (F : Submodule A E) : Set E :=
  {e | ∃ (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) (f : E), f ∈ F ∧
    (H.Bi i).subtype.rTensor E y = Comodule.coact (A := A) (B := B) f ∧ H.coeff E i y u = e}

/-- **`F′ = Σᵢ Uᵢ · (F ∩ Eᵢ)`** (the formula of the reading, pages 13–15). -/
def closure (F : Submodule A E) : Submodule A E :=
  Submodule.span A (H.lifts F)

/-- **Statement 1) of page 13, for `X = S = Spec A`**: every submodule `F` of a comodule lies
in a smallest subcomodule, `F′`. -/
theorem isLeast_closure (F : Submodule A E) :
    IsLeast {N : Submodule A E | IsSubcomodule B N ∧ F ≤ N} (H.closure F) := by
  sorry

end Comodule

end Exhaustion

end Grothendieck.Folder90Comodules
