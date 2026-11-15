module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/curry-r1-space`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/curry-r1-space`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/Topology/CompactOpen.lean` -/

open Set Filter TopologicalSpace Topology
namespace ContinuousMap
section CompactOpen
variable {α X Y Z T : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
variable {K : Set X} {U : Set Y}
section Curry
/-- Currying is continuous for `X` locally compact, with no hypothesis on `Y`. Mathlib's
`continuous_curry` asks for `LocallyCompactSpace (X × Y)`; the branch generalised it in place. -/
theorem continuous_curry_of_locallyCompactSpace [LocallyCompactSpace X] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  refine continuous_of_continuous_uncurry _ <| continuous_iff_continuousAt.2 fun ⟨f, x⟩ ↦
    tendsto_nhds_compactOpen.2 fun L hL U hU hxL ↦ ?_
  obtain ⟨C, hCx, hCU, hC⟩ := local_compact_nhds <|
    hL.eventually_forall_of_forall_eventually (P := fun x' y ↦ f (x', y) ∈ U) fun y hy ↦
      f.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (hxL hy))
  exact ((eventually_mapsTo (hC.prod hL) hU fun p hp ↦ hCU hp.1 p.2 hp.2).prod_nhds hCx).mono
    fun p hp y hy ↦ hp.1 ⟨hp.2, hy⟩

theorem continuous_curry_of_r1Space [R1Space X] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) :=
  continuous_iff_continuousAt.2 fun f ↦ (tendsto_compactOpen_iff_forall _ _).2 fun K hK ↦
    have := isCompact_iff_compactSpace.1 hK
    (continuous_curry_of_locallyCompactSpace.comp
      (continuous_precomp ((restrict K (.id X)).prodMap (.id Y)))).tendsto f
end Curry
end CompactOpen
end ContinuousMap

open Set Filter TopologicalSpace Topology
namespace ContinuousMap
section CompactOpen
variable {α X Y Z T : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
variable {K : Set X} {U : Set Y}
section Curry
set_option backward.defeqAttrib.useBackward true in
theorem continuous_uncurry_of_r1Space [R1Space X] [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) :=
  continuous_iff_continuousAt.2 fun g ↦ (tendsto_compactOpen_iff_forall _ _).2 fun M hM ↦
    have := isCompact_iff_compactSpace.1 (hM.image continuous_fst)
    let φ : C(M, (Prod.fst '' M) × Y) := ⟨fun p ↦ (⟨_, mem_image_of_mem _ p.2⟩, p.1.2), by fun_prop⟩
    (((continuous_precomp φ).comp continuous_uncurry).comp (continuous_restrict _)).tendsto g

end Curry
end CompactOpen
end ContinuousMap

open Set Filter TopologicalSpace Topology
open ContinuousMap
namespace Homeomorph
variable {X : Type*} {Y : Type*} {Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
/-- Currying as a homeomorphism between the function spaces `C(X × Y, Z)` and `C(X, C(Y, Z))`,
for `X` an `R1Space` (for instance a Hausdorff space) and `Y` locally compact. -/
def curryOfR1Space [R1Space X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry_of_r1Space, continuous_uncurry_of_r1Space⟩

end Homeomorph

