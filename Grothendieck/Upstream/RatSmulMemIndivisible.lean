module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/rat-smul-mem-indivisible`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/rat-smul-mem-indivisible`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/LinearAlgebra/Unimodular.lean` -/

namespace Module
variable (R : Type*) [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
variable {R} {v : M}
end Module
namespace Module.Basis
section CommSemiring
variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
end CommSemiring
section Algebra
variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Nontrivial A] [Algebra R A]
end Algebra
end Module.Basis
namespace Module.IsUnimodular
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
end Module.IsUnimodular

namespace AddSubgroup

theorem rat_smul_mem_iff {V : Type*} [AddCommGroup V] [Module ℚ V] {P : AddSubgroup V} {x : V}
    (hx : x ∈ P) (hx' : ∀ y ∈ P, ∀ m : ℤ, x = m • y → IsUnit m) {q : ℚ} :
    q • x ∈ P ↔ ∃ n : ℤ, q = n := by
  refine ⟨fun hq ↦ ?_, fun ⟨n, hn⟩ ↦ by simpa [hn, Int.cast_smul_eq_zsmul] using P.zsmul_mem hx n⟩
  obtain ⟨u, v, huv⟩ := q.isCoprime_num_den
  have hd := hx' _ (P.add_mem (P.zsmul_mem hq u) (P.zsmul_mem hx v)) q.den <| by
    have h : (u * q.num + v * q.den : ℚ) = 1 := by exact_mod_cast huv
    rw [← q.den_mul_eq_num] at h
    match_scalars
    linarith
  exact ⟨q.num, by simpa [Int.isUnit_iff_natAbs_eq, eq_comm, Rat.den_eq_one_iff] using hd⟩

end AddSubgroup
