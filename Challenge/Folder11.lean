module

public import Mathlib

@[expose] public section

namespace Folder11.Simplicial

open TensorProduct

universe u

variable {k : Type u} [Field k]

/-- A Poincaré algebra: finite-dimensional, with `(x, y) ↦ κ(xy)` non-degenerate. -/
def IsPoincare (A : Type*) [CommRing A] [Algebra k A] (κ : A →ₗ[k] k) : Prop :=
  FiniteDimensional k A ∧ ∀ x : A, (∀ y, κ (y * x) = 0) → x = 0

/-- A contravariant functor from finite non-empty sets (all maps) to gauged commutative
`k`-algebras with morphisms `(f_*, f^*)` (page 33): for `α : I → J`, the pull-back
`A(I) → A(J)` is an algebra map, the push-forward `A(J) → A(I)` satisfies the projection
formula and preserves the gauges. -/
structure SFun (k : Type u) [Field k] where
  obj : ℕ → Type u
  [ring : ∀ n, CommRing (obj n)]
  [alg : ∀ n, Algebra k (obj n)]
  κ : ∀ n, obj n →ₗ[k] k
  pull : ∀ {m n : ℕ}, (Fin (m + 1) → Fin (n + 1)) → obj m →ₐ[k] obj n
  push : ∀ {m n : ℕ}, (Fin (m + 1) → Fin (n + 1)) → obj n →ₗ[k] obj m
  pull_id : ∀ n, pull (id : Fin (n + 1) → Fin (n + 1)) = AlgHom.id k (obj n)
  pull_comp : ∀ {l m n : ℕ} (α : Fin (l + 1) → Fin (m + 1)) (β : Fin (m + 1) → Fin (n + 1)),
    pull (β ∘ α) = (pull β).comp (pull α)
  push_id : ∀ n, push (id : Fin (n + 1) → Fin (n + 1)) = LinearMap.id
  push_comp : ∀ {l m n : ℕ} (α : Fin (l + 1) → Fin (m + 1)) (β : Fin (m + 1) → Fin (n + 1)),
    push (β ∘ α) = push α ∘ₗ push β
  proj : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)) (y : obj m) (x : obj n),
    push α (pull α y * x) = y * push α x
  gauge : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)) (x : obj n), κ m (push α x) = κ n x

attribute [instance] SFun.ring SFun.alg

namespace SFun

variable (A : SFun k)

/-- The Künneth map `A(I) ⊗ A(pt) → A(I ⊔ pt)` given by the two pull-backs. -/
noncomputable def kun (n : ℕ) : A.obj n ⊗[k] A.obj 0 →ₐ[k] A.obj (n + 1) :=
  Algebra.TensorProduct.productMap (A.pull (Fin.castSucc : Fin (n + 1) → Fin (n + 2)))
    (A.pull (m := 0) fun _ => Fin.last (n + 1))

end SFun

/-- A special simplicial algebra (pages 37 and 41, with the edition's precisions): `A(pt)` is
Poincaré, the Künneth maps `A(I) ⊗ A(pt) → A(I ⊔ pt)` are isomorphisms and the gauges are
multiplicative. -/
structure Special (A : SFun k) : Prop where
  poincare : IsPoincare (A.obj 0) (A.κ 0)
  kunneth : ∀ n, Function.Bijective (A.kun n)
  gauge_mul : ∀ n a b, A.κ (n + 1) (A.kun n (a ⊗ₜ b)) = A.κ n a * A.κ 0 b

/-- A morphism of `𝒞` between two gauged algebras (page 33): an algebra map `f^*` backwards and
an additive `f_*` forwards, with the projection formula and `κ_B f_* = κ_A`. -/
structure GHom (A B : Type*) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (κA : A →ₗ[k] k) (κB : B →ₗ[k] k) where
  push : A →ₗ[k] B
  pull : B →ₐ[k] A
  proj : ∀ y x, push (pull y * x) = y * push x
  gauge : ∀ x, κB (push x) = κA x

/-- A natural transformation `A → B` of simplicial bivariant algebras: a morphism of `𝒞` at each
`I`, natural for pull-backs and push-forwards. -/
structure NatT (A B : SFun k) where
  push : ∀ n, A.obj n →ₗ[k] B.obj n
  pull : ∀ n, B.obj n →ₐ[k] A.obj n
  proj : ∀ n y x, push n (pull n y * x) = y * push n x
  gauge : ∀ n x, B.κ n (push n x) = A.κ n x
  nat_pull : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)),
    (pull n).comp (B.pull α) = (A.pull α).comp (pull m)
  nat_push : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)),
    B.push α ∘ₗ push n = push m ∘ₗ A.push α

/-- **Pages 37 and 41, in the edition's precise form (commutative case).** Evaluation at a
point, from special simplicial bivariant algebras to Poincaré algebras, is faithful, full and
essentially surjective, hence an equivalence. -/
theorem evaluation_equivalence :
    (∀ {A B : SFun k}, Special B → ∀ φ ψ : NatT A B, φ.pull 0 = ψ.pull 0 →
      ∀ n, φ.pull n = ψ.pull n ∧ φ.push n = ψ.push n) ∧
    (∀ {A B : SFun k}, Special B → ∀ g : GHom (A.obj 0) (B.obj 0) (A.κ 0) (B.κ 0),
      ∃ φ : NatT A B, φ.pull 0 = g.pull ∧ φ.push 0 = g.push) ∧
    (∀ (P : Type u) [CommRing P] [Algebra k P] (κ : P →ₗ[k] k), IsPoincare P κ →
      ∃ (A : SFun k) (_ : Special A) (e : P ≃ₐ[k] A.obj 0), ∀ x, A.κ 0 (e x) = κ x) := by
  sorry

end Folder11.Simplicial
