module

public import Mathlib
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.MvPowerSeries.HomExt
public import Grothendieck.Folder22

@[expose] public section


/-!
# Folder 22, pages 22 and 24: the `t`-adic half of the obstruction

Finding `22-power-series-discrete-obstruction`. For `k = ℚ(x_i : i ∈ I)`, `I` infinite, the
page contrasts two topologies on `A = k[[t]]`: `A` is formally smooth over `k` for its `t`-adic
topology, and not for the discrete one. The discrete half is in `Grothendieck/Folder22.lean`
(`k[[t]]` is not `Algebra.FormallySmooth` over `k`). This file proves the `t`-adic half, which
was left open there because mathlib has no formal smoothness for topological rings.

The notion used is the one of the vendored AxiomMath/Stacks file
`StacksFrontier/RingTheory/FormallySmooth/Topological.lean`: `RingHom.FormallySmoothNAdic φ n`
(Stacks tag 07NI, in the elementary form of tag 07EC (2)(b), EGA 0_IV 19.3.1): every square-zero
lifting problem `R → A`, `S → A/J` in which the map `S → A/J` kills a power of `n` has a solution.
For `n = (t)` this is formal smoothness of `k → k[[t]]` for the `t`-adic topology.

**What is proved.**
* `formallySmoothNAdic_C_X`: for every commutative ring `k`, `k → k[[t]]` is formally smooth for
  the `(t)`-adic topology. No hypothesis on `k` is needed: in particular it holds for
  `k = ℚ(x_i : i ∈ I)`, whatever `I`.
* `formallySmoothNAdic_C_of_X_mem`: the same for every ideal containing `t`, e.g. the maximal
  ideal when `k` is a field (`formallySmoothNAdic_C_maximalIdeal`).
* `adic_not_discrete`: the contrast of the page in one statement, for `k = ℚ(x_i)` with `I`
  infinite: formally smooth for the `t`-adic topology, not formally smooth for the discrete one
  (the second half quoted from `Grothendieck.Folder22`).

The proof: the image `ψ(t)` lifts to a `c ∈ A` with `cᵐ ∈ J`, so `c` is nilpotent; evaluation of
power series at `c` (mathlib's `PowerSeries.eval₂Hom`, `A` discrete) is a ring map
`k[[t]] → A` extending `f`, and it lifts `ψ` because two maps out of `k[[t]]` into a ring
separated for an ideal containing the image of `t` agree once they agree on constants and on `t`
(`powerSeries_hom_ext`, from the vendored `StacksFrontier/RingTheory/MvPowerSeries/HomExt.lean`).
The argument is the one-variable case of `formallySmoothNAdic_C_mvPowerSeries` in AxiomMath's
`StacksFrontier/RingTheory/FormallySmooth/CompleteLocalTransfer.lean`, whose import closure (628
files) is too large to vendor; it is redone here for `PowerSeries`.
-/

namespace Grothendieck.Folder22Adic

open RingHom PowerSeries

universe u v

/-- `k → k[[t]]` is formally smooth for the adic topology of any ideal `M` of `k[[t]]`
containing `t`. -/
theorem formallySmoothNAdic_C_of_X_mem (k : Type v) [CommRing k] (M : Ideal (PowerSeries k))
    (hX : (X : PowerSeries k) ∈ M) :
    FormallySmoothNAdic.{u} (C : k →+* PowerSeries k) M := by
  intro A _ J hJ f ψ hcomm ⟨m, _, hker⟩
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (ψ X)
  have hcJ : c ^ m ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, hc, ← map_pow]
    exact hker (Ideal.pow_mem_pow hX m)
  have hnil : IsNilpotent c := by
    refine ⟨m * 2, ?_⟩
    have h2 := Ideal.pow_mem_pow hcJ 2
    rwa [hJ, Ideal.mem_bot, ← pow_mul] at h2
  let _ : UniformSpace k := ⊥
  let _ : UniformSpace A := ⊥
  have hfc : Continuous f := continuous_of_discreteTopology
  have he : HasEval c := hnil.isTopologicallyNilpotent
  let F : PowerSeries k →+* A := eval₂Hom hfc he
  have hFC : ∀ a, F (C a) = f a := fun a => by
    simp only [F, coe_eval₂Hom, eval₂_C]
  have hFX : F X = c := by
    simp only [F, coe_eval₂Hom, eval₂_X]
  have : IsHausdorff (M.map ψ) (A ⧸ J) := by
    refine ⟨fun x hx => ?_⟩
    have h1 : x ∈ (M.map ψ) ^ m := by
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx m
    rw [← Ideal.map_pow] at h1
    exact (Ideal.mem_bot).mp
      (Ideal.map_le_iff_le_comap.mpr (hker.trans (RingHom.ker_eq_comap_bot ψ).le) h1)
  refine ⟨F, ?_, RingHom.ext hFC⟩
  apply powerSeries_hom_ext (M.map ψ)
  · intro a
    rw [RingHom.comp_apply, hFC]
    exact (RingHom.congr_fun hcomm a).symm
  · rw [RingHom.comp_apply, hFX, hc]
  · rw [RingHom.comp_apply, hFX, hc]
    exact Ideal.mem_map_of_mem ψ hX

/-- **The `t`-adic half of pages 22 and 24.** For every commutative ring `k`, the inclusion
`k → k[[t]]` is formally smooth for the `t`-adic topology. -/
theorem formallySmoothNAdic_C_X (k : Type v) [CommRing k] :
    FormallySmoothNAdic.{u} (C : k →+* PowerSeries k) (Ideal.span {X}) :=
  formallySmoothNAdic_C_of_X_mem k _ (Ideal.mem_span_singleton_self _)

/-- Over a field, the same for the adic topology of the maximal ideal `(t)`. -/
theorem formallySmoothNAdic_C_maximalIdeal (k : Type v) [Field k] :
    FormallySmoothNAdic.{u} (C : k →+* PowerSeries k)
      (IsLocalRing.maximalIdeal (PowerSeries k)) :=
  formallySmoothNAdic_C_of_X_mem k _ (by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
    simp)

/-- **The contrast of pages 22 and 24**, for `k = ℚ(x_i : i ∈ I)` with `I` infinite: `k[[t]]` is
formally smooth over `k` for the `t`-adic topology, and not formally smooth for the discrete
topology (`Grothendieck.Folder22.not_formallySmooth_discrete`). -/
theorem adic_not_discrete (I : Type) [Infinite I] :
    FormallySmoothNAdic.{u} (C : Folder22.K I →+* PowerSeries (Folder22.K I)) (Ideal.span {X}) ∧
      ¬ Algebra.FormallySmooth (Folder22.K I) (PowerSeries (Folder22.K I)) :=
  ⟨formallySmoothNAdic_C_X _, Folder22.not_formallySmooth_discrete I⟩

end Grothendieck.Folder22Adic

#print axioms Grothendieck.Folder22Adic.formallySmoothNAdic_C_X
#print axioms Grothendieck.Folder22Adic.formallySmoothNAdic_C_maximalIdeal
#print axioms Grothendieck.Folder22Adic.adic_not_discrete
