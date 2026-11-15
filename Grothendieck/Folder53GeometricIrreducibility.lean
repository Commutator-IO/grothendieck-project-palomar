module

public import Mathlib
public import Grothendieck.Folder53
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GaloisFixedComponentDescent

@[expose] public section


/-!
# Folder 53, page 9: the criterion of geometric irreducibility, at scheme level

`Grothendieck/Folder53.lean` proves the Galois step of page 9 in topological form
(`irreducibleSpace_of_stable`, `irreducibleSpace_of_map`) and leaves out the scheme-level
statement with Mathlib's `AlgebraicGeometry.GeometricallyIrreducible`: the Galois action on
`X_{k'}`, the reduction from all extensions of `k` to separable ones, and the radicial step.
This file supplies it with three results of the vendored AxiomMath/Stacks library:

* `AlgebraicGeometry.geometricallyIrreducible_tfae_of_isSepClosure` (Stacks tag 038I, file
  `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/IrreducibleSeparableClosure.lean`):
  `X` is geometrically irreducible over `k` as soon as `X_{k^sep}` is irreducible. This is the
  reduction to the separable closure, the radicial step included;
* `AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents` (file
  `…/Variety/Geometrically/IrreducibleGaloisAction.lean`): the action of `Aut(k^sep/k)` on the
  irreducible components of `X_{k^sep}`;
* `AlgebraicGeometry.fixed_geometricComponent_iff_exists_geometricallyIrreducible_component`
  (Stacks tag 038J, file `StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/
  GaloisFixedComponentDescent.lean`): a Galois-fixed component of `X_{k^sep}` is the inverse
  image of an irreducible component of `X`.

The survey of 2026-11-15 also named the transitivity of the Galois group on the components over
a component of `X` (tag 04KY). It is not needed here: the set the argument works with is the
whole inverse image `p⁻¹(g(Z))` in `X_{k^sep}` of the image of `g : Z → X`, which every
automorphism preserves because it commutes with the projection `p : X_{k^sep} → X`, and that
set is irreducible because it is the image of `Z ×_X X_{k^sep} ≅ Z_{k^sep}`.

**What is proved.**
* `isIrreducible_preimage_range`: for `g : Z → X` over `k` with `Z` geometrically irreducible,
  `p⁻¹(g(Z)) ⊆ X_{k^sep}` is irreducible;
* `geometricallyIrreducible_of_point` (the criterion of page 9 over `k^sep`): if `X` is
  irreducible, `Z` geometrically irreducible, and some point of `X_{k^sep}` over a point of
  `g(Z)` lies on a single irreducible component of `X_{k^sep}`, then `X` is geometrically
  irreducible;
* `unique_component_map`: for a continuous generalizing map `q : Y' → Y` of spaces with `Y`
  quasi-sober, a point of `Y'` lying on a single irreducible component maps to a point lying on
  a single irreducible component;
* `geometricallyIrreducible_of_point_extension` (the criterion as page 9 states it, with
  hypothesis b) over any extension `L ⊇ k^sep`, for instance an algebraic closure `k̄`): if `X`
  is irreducible, `Z` geometrically irreducible, and there is `z ∈ Z` such that every point of
  `X_L` over `g(z)` lies on a single irreducible component of `X_L`, then `X` is geometrically
  irreducible. Hypothesis b) is passed from `L` to `k^sep` by `unique_component_map` applied to
  the flat, surjective comparison map `X_L → X_{k^sep}` (`AlgebraicGeometry.baseChangeComparison`).

The page's hypothesis b) asks that `g(Z)` not be contained in the locus of points of `X` over
which two components of `X_k̄` meet; the hypothesis used here is that it contains one point
outside that locus, which is the same thing.

Not formalised: the sufficient condition by a geometrically normal point of `X_red`, and the
identification of `ℂ ⊗_ℝ ℝ[x,y]/(x² + y²)` used by the counterexample (done separately in
`Folder53.lean`).
-/

open CategoryTheory Limits AlgebraicGeometry

namespace Grothendieck.Folder53

universe u

section Topology

/-- A point of `Y'` through which a single irreducible component passes maps, under a
continuous generalizing map to a quasi-sober space, to a point through which a single
irreducible component passes. -/
theorem unique_component_map {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    [QuasiSober Y] (q : Y' → Y) (hq : Continuous q) (hgen : GeneralizingMap q) (y' : Y')
    (huniq : ∀ C ∈ irreducibleComponents Y', ∀ D ∈ irreducibleComponents Y',
      y' ∈ C → y' ∈ D → C = D) :
    ∀ C ∈ irreducibleComponents Y, ∀ D ∈ irreducibleComponents Y,
      q y' ∈ C → q y' ∈ D → C = D := by
  -- each component through `q y'` has its generic point in the image of a component through `y'`
  have lift : ∀ C (hC : C ∈ irreducibleComponents Y), q y' ∈ C →
      ∃ D ∈ irreducibleComponents Y', y' ∈ D ∧ hC.1.genericPoint ∈ q '' D := by
    intro C hC hyC
    have hgp := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    obtain ⟨η', hη', hqη'⟩ := hgen (hgp.specializes hyC)
    obtain ⟨D, hD, hsub⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible _
        (isIrreducible_singleton (x := η')).closure
    exact ⟨D, hD, hsub (specializes_iff_mem_closure.1 hη'), η', hsub (subset_closure rfl), hqη'⟩
  -- a component whose generic point lies in the irreducible set `q '' D` is its closure
  have eq_closure : ∀ C (hC : C ∈ irreducibleComponents Y), ∀ D : Set Y', IsIrreducible D →
      hC.1.genericPoint ∈ q '' D → C = closure (q '' D) := by
    intro C hC D hD hmem
    have hgp := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    have hsub : C ⊆ closure (q '' D) := by
      rw [← hgp.def]
      exact closure_mono (Set.singleton_subset_iff.2 hmem)
    exact le_antisymm hsub (hC.2 (hD.image q hq.continuousOn).closure hsub)
  intro C hC D hD hyC hyD
  obtain ⟨C', hC', hyC', hmC⟩ := lift C hC hyC
  obtain ⟨D', hD', hyD', hmD⟩ := lift D hD hyD
  obtain rfl := huniq C' hC' D' hD' hyC' hyD'
  rw [eq_closure C hC C' hC'.1 hmC, eq_closure D hD C' hC'.1 hmD]

end Topology

variable (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
  {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Z ⟶ X)

/-- `Spec k^sep → Spec k`. -/
local notation "gS" => Spec.map (CommRingCat.ofHom (algebraMap k ksep))

omit [IsSepClosure k ksep] in
/-- For `g : Z → X` over `k` with `Z` geometrically irreducible, the inverse image of `g(Z)`
in `X_{k^sep}` is irreducible: it is the image of `Z ×_X X_{k^sep} ≅ Z_{k^sep}`. -/
theorem isIrreducible_preimage_range [GeometricallyIrreducible (g ≫ f)] :
    IsIrreducible
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))) ⁻¹' Set.range g) := by
  have hZ : IrreducibleSpace ↥(pullback (g ≫ f) gS) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := g ≫ f) gS _ _
      (.of_hasPullback _ _)
  have hZ' : IrreducibleSpace ↥(pullback g (pullback.fst f gS)) :=
    (pullbackRightPullbackFstIso f gS g).schemeIsoToHomeo.irreducibleSpace_iff.mpr hZ
  rw [← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (pullback.snd g (pullback.fst f gS)).continuous.continuousOn

/-- **Folder 53, page 9, over the separable closure.** Let `X` be an irreducible `k`-scheme and
`g : Z → X` a morphism over `k` with `Z` geometrically irreducible. If some point `s` of
`X_{k^sep}` over a point of `g(Z)` lies on a single irreducible component of `X_{k^sep}`, then
`X` is geometrically irreducible. -/
theorem geometricallyIrreducible_of_point [IrreducibleSpace X] [GeometricallyIrreducible (g ≫ f)]
    (s : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))))
    (hs : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) s ∈ Set.range g)
    (huniq : ∀ C ∈ irreducibleComponents
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))),
      ∀ D ∈ irreducibleComponents
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))),
      s ∈ C → s ∈ D → C = D) :
    GeometricallyIrreducible f := by
  obtain ⟨C, hC, hSC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (isIrreducible_preimage_range k ksep f g)
  let Tbar : (galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).V := ⟨C, hC⟩
  -- every Galois automorphism fixes `C`: its image contains `S`, hence `s`
  have hfix : ∀ σ : MulOpposite (ksep ≃ₐ[k] ksep),
      ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).ρ σ).asHom Tbar =
        Tbar := by
    intro σ
    let a := ((galoisActionOnBaseChange k ksep (Over.mk f)).ρ σ).asHom
    have hcommute : a ≫ pullback.fst f gS = pullback.fst f gS := by
      dsimp [a, galoisActionOnBaseChange, pullback.map]
      rw [pullback.lift_fst]
      simp
    let e := Scheme.homeoOfIso ((galoisActionOnBaseChange k ksep (Over.mk f)).ρAut σ).asIso
    have hpe : ∀ x, pullback.fst f gS (e x) = pullback.fst f gS x := fun x =>
      congrArg (fun q : _ ⟶ X => q.base x) hcommute
    have himg := (ConcreteCategory.hom
      ((galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).ρ σ).asHom Tbar).2
    rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe] at himg
    change e '' C ∈ _ at himg
    apply Subtype.ext
    rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe]
    change e '' C = C
    refine huniq _ himg _ hC ⟨e.symm s, hSC ?_, e.apply_symm_apply s⟩ (hSC hs)
    change pullback.fst f gS (e.symm s) ∈ Set.range g
    rw [← hpe, e.apply_symm_apply]
    exact hs
  -- so `C` is the inverse image of a component of `X`, which is all of `X`
  obtain ⟨T, -, hpre⟩ :=
    (fixed_geometricComponent_iff_exists_geometricallyIrreducible_component k ksep X f Tbar).1
      hfix
  have hT : (T : Set X) = Set.univ :=
    Set.eq_univ_of_univ_subset (T.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _))
  have hCuniv : C = Set.univ := by
    change _ = C at hpre
    rw [← hpre, hT, Set.preimage_univ]
  have hirr : IrreducibleSpace ↥(pullback f gS) := by
    rw [irreducibleSpace_def]
    exact (hCuniv ▸ hC.1 : IsIrreducible (Set.univ : Set _))
  exact ((geometricallyIrreducible_tfae_of_isSepClosure k X f ksep).out 3 1).mp hirr

/-- **Folder 53, page 9, the criterion as stated.** Let `X` be an irreducible `k`-scheme,
`g : Z → X` a morphism over `k` with `Z` geometrically irreducible (hypothesis a)), and `L` an
extension of `k^sep` (an algebraic closure `k̄` on the page). If there is `z ∈ Z` such that every
point of `X_L` over `g(z)` lies on a single irreducible component of `X_L` (hypothesis b):
`g(Z)` is not contained in the locus of points over which two components of `X_L` meet), then
`X` is geometrically irreducible. -/
theorem geometricallyIrreducible_of_point_extension (L : Type u) [Field L] [Algebra k L]
    [Algebra ksep L] [IsScalarTower k ksep L] [IrreducibleSpace X]
    [GeometricallyIrreducible (g ≫ f)] (z : Z)
    (huniq : ∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))) y = g z →
      ∀ C ∈ irreducibleComponents
          ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        ∀ D ∈ irreducibleComponents
          ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        y ∈ C → y ∈ D → C = D) :
    GeometricallyIrreducible f := by
  let gL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let gSL := Spec.map (CommRingCat.ofHom (algebraMap ksep L))
  let q := baseChangeComparison k ksep L X f
  have htop : q ≫ pullback.fst f gS = pullback.fst f gL := pullback.lift_fst _ _ _
  have hleft : q ≫ pullback.snd f gS = pullback.snd f gL ≫ gSL := pullback.lift_snd _ _ _
  have hbot : gSL ≫ gS = gL := by
    rw [← Spec.map_comp]
    congr 2
    ext x
    exact (IsScalarTower.algebraMap_apply k ksep L x).symm
  -- `q : X_L → X_{k^sep}` is a base change of `Spec L → Spec k^sep`, hence flat
  have hpb : IsPullback q (pullback.snd f gL) (pullback.snd f gS) gSL := by
    refine IsPullback.of_right ?_ hleft (.of_hasPullback f gS)
    rw [htop, hbot]
    exact .of_hasPullback f gL
  have hflatSL : Flat gSL := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have hflat : Flat q := MorphismProperty.of_isPullback hpb.flip hflatSL
  obtain ⟨y, hy⟩ := (pullback.fst f gL).surjective (g z)
  refine geometricallyIrreducible_of_point k ksep f g (q y) ⟨z, ?_⟩ ?_
  · rw [← hy, ← htop]
    rfl
  · exact unique_component_map q q.continuous (Flat.generalizingMap q) y (huniq y hy)

end Grothendieck.Folder53
