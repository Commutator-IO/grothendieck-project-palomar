module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder67

open CategoryTheory

universe v u

variable (k : Type u) [Ring k]

section Basics

variable {k}

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- `M` is `2`-regular: multiplication by `2` is injective. -/
def TwoRegular (M : Type*) [AddCommGroup M] : Prop :=
  ∀ x : M, 2 • x = 0 → x = 0

/-- The linear map `x ↦ 2x`. -/
def twice (k : Type u) [Ring k] (M : Type*) [AddCommGroup M] [Module k M] : M →ₗ[k] M :=
  (2 : ℕ) • LinearMap.id

@[simp] lemma twice_apply (x : M) : twice k M x = 2 • x := rfl

/-- The submodule `2M`. -/
abbrev two (k : Type u) [Ring k] (M : Type*) [AddCommGroup M] [Module k M] : Submodule k M :=
  LinearMap.range (twice k M)

lemma mem_two {x : M} : x ∈ two k M ↔ ∃ y, 2 • y = x := by
  simp [two]

lemma two_smul_mem_two (y : M) : 2 • y ∈ two k M := mem_two.2 ⟨y, rfl⟩

end Basics

/-- A `2`-regular `k`-module with an involution. -/
structure InvMod where
  /-- the module `M` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- the involution -/
  σ : carrier →ₗ[k] carrier
  σ_σ : ∀ x, σ (σ x) = x
  reg : TwoRegular carrier

attribute [instance] InvMod.isAddCommGroup InvMod.isModule

namespace InvMod

variable {k}

/-- The `+1`-eigenmodule `M₊ = Ker(1 - σ)`. -/
def plus (X : InvMod.{v} k) : Submodule k X.carrier := LinearMap.ker (LinearMap.id - X.σ)

/-- The `-1`-eigenmodule `M₋ = Ker(1 + σ)`. -/
def minus (X : InvMod.{v} k) : Submodule k X.carrier := LinearMap.ker (LinearMap.id + X.σ)

variable (X : InvMod.{v} k)

lemma mem_plus {x : X.carrier} : x ∈ X.plus ↔ X.σ x = x := by
  rw [plus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, eq_comm]

lemma mem_minus {x : X.carrier} : x ∈ X.minus ↔ X.σ x = -x := by
  rw [minus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_neg_eq, eq_comm]

/-- Page 90: `2x = (x + σx) + (x - σx)`, with `x + σx ∈ M₊` and `x - σx ∈ M₋`. -/
lemma add_σ_mem_plus (x : X.carrier) : x + X.σ x ∈ X.plus := by
  rw [mem_plus, map_add, X.σ_σ, add_comm]

lemma sub_σ_mem_minus (x : X.carrier) : x - X.σ x ∈ X.minus := by
  rw [mem_minus, map_sub, X.σ_σ, neg_sub]

end InvMod

namespace InvMod

variable {k}

variable (X : InvMod.{v} k)

/-- The submodule `{(p, q) | p + q ∈ 2M}` of `M₊ × M₋`. -/
def S : Submodule k (X.plus × X.minus) :=
  (two k X.carrier).comap (X.plus.subtype.coprod X.minus.subtype)

/-- The submodule `m ⊂ M₊/2M₊ × M₋/2M₋` of page 90: the image of `2M`. -/
def m : Submodule k ((X.plus ⧸ two k X.plus) × (X.minus ⧸ two k X.minus)) :=
  X.S.map ((two k X.plus).mkQ.prodMap (two k X.minus).mkQ)

/-- `(p̄, q̄) ∈ m` if and only if `p + q ∈ 2M`. -/
theorem mk_mem_m_iff (p : X.plus) (q : X.minus) :
    (Submodule.Quotient.mk p, Submodule.Quotient.mk q) ∈ X.m ↔
      (p : X.carrier) + q ∈ two k X.carrier := by
  refine ⟨?_, fun h => ⟨(p, q), h, rfl⟩⟩
  rintro ⟨⟨p', q'⟩, hS, he⟩
  simp only [LinearMap.prodMap_apply, Submodule.mkQ_apply, Prod.mk.injEq,
    Submodule.Quotient.eq] at he
  obtain ⟨hp, hq⟩ := he
  have hS' : (p' : X.carrier) + q' ∈ two k X.carrier := hS
  have lift : ∀ (N : Submodule k X.carrier) (x : N), x ∈ two k N →
      (x : X.carrier) ∈ two k X.carrier := by
    intro N x hx
    obtain ⟨y, hy⟩ := mem_two.1 hx
    exact mem_two.2 ⟨y, by rw [← hy]; rfl⟩
  have h1 := lift _ _ hp
  have h2 := lift _ _ hq
  simp only [Submodule.coe_sub] at h1 h2
  rw [show (p : X.carrier) + q = ((p' : X.carrier) + q') - (p' - p) - (q' - q) by abel]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hS' h1) h2

/-- The preimage of `m` in `M₊ × M₋` (the module that `build` makes of `triple`). -/
def Nx : Submodule k (X.plus × X.minus) :=
  X.m.comap ((two k X.plus).mkQ.prodMap (two k X.minus).mkQ)

/-- `x ↦ (x + σx, x - σx)`, from `M` into the module rebuilt from its triple. -/
def toBuild : X.carrier →ₗ[k] X.Nx :=
  LinearMap.codRestrict X.Nx
    (LinearMap.prod
      (LinearMap.codRestrict X.plus (LinearMap.id + X.σ) (fun x => X.add_σ_mem_plus x))
      (LinearMap.codRestrict X.minus (LinearMap.id - X.σ) (fun x => X.sub_σ_mem_minus x)))
    (fun x => by
      change (Submodule.Quotient.mk (⟨x + X.σ x, X.add_σ_mem_plus x⟩ : X.plus),
        Submodule.Quotient.mk (⟨x - X.σ x, X.sub_σ_mem_minus x⟩ : X.minus)) ∈ X.m
      rw [mk_mem_m_iff]
      change (x + X.σ x) + (x - X.σ x) ∈ two k X.carrier
      rw [show (x + X.σ x) + (x - X.σ x) = 2 • x by rw [two_nsmul]; abel]
      exact two_smul_mem_two x)

lemma toBuild_bijective : Function.Bijective X.toBuild := by
  sorry

end InvMod

end Grothendieck.Folder67
