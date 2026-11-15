module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/matrix-det-fin-two-cauchy-binet`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/matrix-det-fin-two-cauchy-binet`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean` -/

open Function
variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]
namespace exteriorPower
open Module Set Set.powersetCard
variable (R n) {I : Type*} [LinearOrder I] (b : Basis I R M)
variable {R}
variable (R)
section FiniteFree
variable (M) [Module.Free R M] [Module.Finite R M]
end FiniteFree
end exteriorPower

namespace Matrix

open Set exteriorPower

variable {l o ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The **Cauchy–Binet formula**: for `A : Matrix (Fin n) ι R` and `B : Matrix ι (Fin n) R`,
`det (A * B)` is the sum, over the `n`-element subsets `s` of `ι`, of the products of the
maximal minors of `A` and `B` indexed by `s`. -/
theorem det_mul_eq_sum_powersetCard (A : Matrix (Fin n) ι R) (B : Matrix ι (Fin n) R) :
    (A * B).det = ∑ s : powersetCard ι n,
      (A.submatrix id (powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix (powersetCard.ofFinEmbEquiv.symm s) id).det := by
  have h := congr(pairingDual R (ι → R) n (ιMulti R n fun j ↦ ∑ k, B k j • LinearMap.proj k)
    $(((Pi.basisFun R ι).exteriorPower n).sum_repr (ιMulti R n fun i ↦ A i))).symm
  eta_expand at h
  simpa [ιMulti_family, basis_repr_apply, Pi.single_apply, mul_comm (B _ _)] using! h

/-- The **Cauchy–Binet formula** for minors: the minor of `A * B` on rows `I` and columns `K` is
the sum, over the `n`-element subsets `s` of `ι`, of the products of the minors of `A` on rows
`I` and columns `s` and of `B` on rows `s` and columns `K`. -/
theorem det_submatrix_mul (A : Matrix l ι R) (B : Matrix ι o R) (I : Fin n → l) (K : Fin n → o) :
    ((A * B).submatrix I K).det = ∑ s : powersetCard ι n,
      (A.submatrix I (powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix (powersetCard.ofFinEmbEquiv.symm s) K).det := by
  simp [submatrix_mul A B I id K Function.bijective_id, det_mul_eq_sum_powersetCard]

end Matrix
