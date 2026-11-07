module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section SVD

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- `σ_n^m(T)`, the elementary symmetric function of degree `m` of the first `n` singular
values `s_0(T), …, s_{n-1}(T)` (page 71, (17)). -/
noncomputable def sigma (n m : ℕ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, T.singularValues i

end SVD

open scoped ComplexConjugate

end Grothendieck.Folder1

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace Matrix Polynomial

open scoped MatrixOrder ComplexOrder ComplexConjugate

section SigmaSystem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The system (16) of page 71**, for every `m` and `n`, for linear maps between
finite-dimensional complex inner product spaces:
`σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`. -/
theorem sigma_system (u v : E →ₗ[ℂ] F) (n m : ℕ) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  sorry

end SigmaSystem

end Grothendieck.Folder1
