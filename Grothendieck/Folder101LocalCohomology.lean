module

public import Mathlib
public import Grothendieck.Folder101Ext
public import StacksFrontier.RingTheory.LocalCohomology.CechModel

@[expose] public section


/-!
# Folder 101, page 10: local cohomology on `Spec A` lives in degrees `0` and `1`

Finding `101-sheaf-duality-dim-one`. Page 10 describes an `O_X`-module on `X = Spec A`, `A` a
discrete valuation ring, by a triple `(M₀, M₁, u)` and computes its local cohomology at the
closed point `x` as `H⁰_x = Ker u` and `H¹_x = Coker u`, with nothing in higher degrees. This
file checks the last point for quasi-coherent sheaves, with local cohomology taken as a derived
functor, using the vendored AxiomMath/Stacks files:
`Dualizing.localCohomologyFunctor` is `RΓ_{V(𝔪)}` on `D(A)`, the right adjoint of the inclusion
of the complexes with `𝔪`-power-torsion cohomology (Stacks tag 0A6Q), and
`Stacks.LocalCohomology.CechModel` computes it on a module by the extended Čech complex of a
generating family of `𝔪` (tag 0A6R at a module).

* `localCohomology`: `H^i_x(M) = H^i(RΓ_{V(𝔪)}(M))` for an `A`-module `M` (the quasi-coherent
  sheaf `M̃`);
* `localCohomologyIsoCech`: for a uniformizer `ϖ`, `H^i_x(M)` is the `i`-th cohomology of the
  extended Čech complex `M → M_ϖ` (in degrees `0` and `1`);
* `isZero_localCohomology`: `H^i_x(M) = 0` for `i ∉ {0, 1}`, since `𝔪 = (ϖ)` has one generator.

Not formalised: the identification of `H⁰_x(M)` and `H¹_x(M)` with the kernel and cokernel of
`M → M_ϖ = K ⊗_A M` (the cohomology of the two-term Čech complex is not unfolded here), and
local cohomology of `O_X`-modules that are not quasi-coherent, which the page also treats.
-/

namespace Grothendieck.Folder101LocalCohomology

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

lemma maximalIdeal_fg : (maximalIdeal A).FG := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact ⟨{ϖ}, by rw [hϖ.maximalIdeal_eq, Finset.coe_singleton]⟩

lemma span_range_eq {ϖ : A} (hϖ : Irreducible ϖ) :
    Ideal.span (Set.range ![ϖ]) = maximalIdeal A := by
  rw [hϖ.maximalIdeal_eq, Set.range_unique]
  rfl

variable (A) in
/-- `H^i_x(M)`: the `i`-th local cohomology at the closed point of `Spec A` of the module `M`
(the quasi-coherent sheaf `M̃`), the cohomology of `RΓ_{V(𝔪)}(M)`. -/
noncomputable abbrev localCohomology (M : ModuleCat.{u} A) (i : ℤ) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
    ((Dualizing.derivedPowerTorsionProperty A (maximalIdeal A) maximalIdeal_fg).ι.obj
      ((Dualizing.localCohomologyFunctor A (maximalIdeal A) maximalIdeal_fg).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))

/-- For a uniformizer `ϖ`, `H^i_x(M)` is the cohomology of the extended Čech complex
`M → M_ϖ`. -/
noncomputable def localCohomologyIsoCech {ϖ : A} (hϖ : Irreducible ϖ) (M : ModuleCat.{u} A)
    (i : ℤ) :
    localCohomology A M i ≅
      (Stacks.LocalCohomology.extendedCechComplex ![ϖ] M).homology i :=
  Stacks.LocalCohomology.localCohomologyIsoExtendedCechHomology ![ϖ] M (maximalIdeal A)
    maximalIdeal_fg (span_range_eq hϖ) i

/-- **Local cohomology at the closed point of `Spec A` vanishes outside degrees `0` and `1`**,
for every `A`-module. -/
theorem isZero_localCohomology (M : ModuleCat.{u} A) {i : ℤ} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    IsZero (localCohomology A M i) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact Stacks.LocalCohomology.isZero_homology_localCohomology_of_outside_range ![ϖ] M
    (maximalIdeal A) maximalIdeal_fg (span_range_eq hϖ) i (by omega)

end Grothendieck.Folder101LocalCohomology
