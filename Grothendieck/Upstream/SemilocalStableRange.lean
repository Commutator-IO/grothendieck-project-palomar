module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/semilocal-stable-range`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/semilocal-stable-range`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/RingTheory/LocalProperties/Semilocal.lean` -/

section CommSemiring
variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
section IsLocalized
end IsLocalized
section Localized
end Localized
section IsLocalization
end IsLocalization
end CommSemiring
section CommRing
section IsLocalization
variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
end IsLocalization
variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]

/-- A semilocal ring has stable range one: if `a` and `b` are coprime, then `a + t * b` is a
unit for some `t`. This is due to Bass, see [Bass, *K-theory and stable algebra*][bass1964]. -/
theorem IsCoprime.exists_isUnit_add_mul {a b : R} (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R ↦ m.asIdeal) :=
    fun m n hmn ↦ Ideal.isCoprime_of_isMaximal fun e ↦ hmn (MaximalSpectrum.ext e)
  -- modulo `m`, take `t = 0` if `b ∈ m`, and `t = b⁻¹ (1 - a)` otherwise
  let x : MaximalSpectrum R → R := fun m ↦
    if hb : b ∈ m.asIdeal then 0 else (m.isMaximal.exists_inv hb).choose * (1 - a)
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hcop x
  refine ⟨t, by_contra fun hu ↦ ?_⟩
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  have htm := ht ⟨m, hm⟩
  obtain ⟨u, v, huv⟩ := h
  refine hm.ne_top <| (Ideal.eq_top_iff_one _).2 ?_
  by_cases hb : b ∈ m
  · simp only [x, hb, ↓reduceDIte, sub_zero] at htm
    have ha : a ∈ m := by simpa using m.sub_mem hmem (m.mul_mem_left t hb)
    rw [← huv]
    exact m.add_mem (m.mul_mem_left _ ha) (m.mul_mem_left _ hb)
  · obtain ⟨k, hk, hy⟩ := (hm.exists_inv hb).choose_spec
    simp only [x, hb, ↓reduceDIte] at htm
    have e : (1 : R) = (a + t * b) - (t - (hm.exists_inv hb).choose * (1 - a)) * b +
        (1 - a) * k := by
      linear_combination (-(1 - a)) * hy
    rw [e]
    exact m.add_mem (m.sub_mem hmem (m.mul_mem_right _ htm)) (m.mul_mem_left _ hk)

end CommRing
