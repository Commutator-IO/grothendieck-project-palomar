module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.FiveLemma

@[expose] public section

namespace Grothendieck.Folder22

open TensorProduct LinearMap

universe u

variable {A : Type u} [CommRing A]

section SeveralVariablesSmooth

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {σ : Type*} [Finite σ]
  [DecidableEq σ]

/-- **Page 23's Proposition in `n ≥ 1` variables, formal smoothness**: for a field `K` over `R`
with `Ω_{K/R}` infinite-dimensional, `K⟦t₁, …, tₙ⟧` with the discrete topology is not formally
smooth over `K`. As for `n = 1`: a formally smooth `S` would give, by Jacobi–Zariski, a retraction
`r` of `S ⊗_K Ω_{K/R} → Ω_{S/R}` (`retraction_of_formallySmooth`), and `r ∘ d_{S/R}` would be a
derivation inducing `d_{K/R}`, which `no_derivation_mv` excludes. -/
theorem not_formallySmooth_mv (i₀ : σ) (h : ¬ Module.Finite K Ω[K⁄R]) :
    ¬ Algebra.FormallySmooth K (MvPowerSeries σ K) := by
  sorry

end SeveralVariablesSmooth

end Grothendieck.Folder22
