module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.Polynomial.Basis

@[expose] public section

namespace Grothendieck.Folder153

open Polynomial TensorProduct

variable {k₀ K₀ : Type*} [CommRing k₀] [CommRing K₀] [Algebra k₀ K₀]

/-- Evaluation at `x ∈ k₀`, as a `k₀`-linear map `K₀[T] → K₀`. -/
noncomputable def ev (x : k₀) : K₀[X] →ₗ[k₀] K₀ :=
  (Polynomial.leval (algebraMap k₀ K₀ x)).restrictScalars k₀

variable (k₀ K₀) in
/-- `Ω = Int(k₀)`: the polynomials of `K₀[T]` taking values in `k₀` on `k₀`. -/
noncomputable def Omega : Subalgebra k₀ K₀[X] where
  carrier := {F | ∀ x : k₀, F.eval (algebraMap k₀ K₀ x) ∈ (algebraMap k₀ K₀).range}
  mul_mem' {F G} hF hG x := by rw [eval_mul]; exact mul_mem (hF x) (hG x)
  add_mem' {F G} hF hG x := by rw [eval_add]; exact add_mem (hF x) (hG x)
  algebraMap_mem' c x := by
    rw [Polynomial.algebraMap_apply, eval_C]; exact ⟨c, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module k₀ M]

variable (K₀ M) in
/-- The set of the Lemme: the `F ∈ K₀[T] ⊗ M` such that `F(x) ∈ M` for every
`x ∈ k₀`, i.e. `(ev_x ⊗ id) F` lies in the image of `m ↦ 1 ⊗ m`. -/
def valeursDansM : Set (K₀[X] ⊗[k₀] M) :=
  {F | ∀ x : k₀, (ev x).rTensor M F ∈ LinearMap.range (TensorProduct.mk k₀ K₀ M 1)}

/-- **Lemme (2).** For `M` free, the image of `Ω ⊗ M → K₀[T] ⊗ M` is exactly the
set of `F` with `F(x) ∈ M` for every `x ∈ k₀`. -/
theorem lemme_range [Module.Free k₀ M] :
    (LinearMap.range ((Omega k₀ K₀).val.toLinearMap.rTensor M) : Set (K₀[X] ⊗[k₀] M)) =
      valeursDansM K₀ M := by
  sorry

end Grothendieck.Folder153
