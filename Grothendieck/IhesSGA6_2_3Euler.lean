module

public import Mathlib
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.SuccPred.Int

@[expose] public section


/-!
# IHÉS FG_IL_5_SGA6_2_3, view 3, item 5: the Euler formula for any additive function

At view 3 the notes list, for an additive function `χ` on an abelian category `A` and a finite
complex `X^•`, the Euler formula `Σ (−1)ⁱ χ(Xⁱ) = Σ (−1)ⁱ χ(Hⁱ(X^•))`. The edition's
`Grothendieck/IhesSGA6_2_3.lean` proves it for `χ = dim` on finite-dimensional vector spaces
(`sum_finrank_eq_sum_finrank_cohomology`). This file proves it for every additive function on
every abelian category, using the group `KZero A` of the vendored AxiomMath/Stacks file
`StacksFrontier/CategoryTheory/Abelian/GrothendieckGroup.lean` (Stacks tag 02MU): the free
abelian group on the objects of `A` modulo `[X₂] = [X₁] + [X₃]` for every short exact sequence.

The identity is first proved once in `KZero A` (`sum_negOnePow_mk_X_eq`), where the class of each
term splits along two short exact sequences: `0 → Zⁱ → Xⁱ → Bⁱ⁺¹ → 0` (cycles, then the image of
the differential) and `0 → Bⁱ → Zⁱ → Hⁱ → 0`. The alternating sum of the boundary classes
telescopes, and the two end terms vanish because `X` is zero outside `[a, b]`. An additive
function `χ` with values in an abelian group `G` factors through `KZero A` by its universal
property (`KZero.lift`, `KZero.universal`), which gives the formula for `χ`
(`sum_negOnePow_eq_sum_negOnePow_homology`).

**What is proved.** For `X : CochainComplex A ℤ` with `Xⁱ = 0` for `i ∉ [a, b]`:
* `sum_negOnePow_mk_X_eq`: `Σ_{a ≤ i ≤ b} (−1)ⁱ [Xⁱ] = Σ_{a ≤ i ≤ b} (−1)ⁱ [Hⁱ(X)]` in `KZero A`;
* `sum_negOnePow_eq_sum_negOnePow_homology`: the same for any `χ : A → G` additive on short
  exact sequences;
* `sum_negOnePow_eq_zero_of_exact`: an exact bounded complex has `Σ (−1)ⁱ χ(Xⁱ) = 0`.
-/

namespace Grothendieck.IhesSGA6_2_3Euler

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The telescoping of alternating sums over an integer interval. -/
theorem sum_Icc_negOnePow_add {G : Type*} [AddCommGroup G] (g : ℤ → G) (a : ℤ) :
    ∀ b ≥ a - 1, ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • (g i + g (i + 1)) =
      (a.negOnePow : ℤ) • g a + (b.negOnePow : ℤ) • g (b + 1) := by
  intro b hb
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a - 1 + n := ⟨(b - (a - 1)).toNat, by omega⟩
  clear hb
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.cast_zero, add_zero,
      sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one, Units.val_neg,
      neg_smul, add_neg_cancel]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
      Finset.sum_insert (by simp), ih, Int.negOnePow_succ, Units.val_neg, neg_smul, neg_smul,
      smul_add, neg_add]
    abel

namespace KZero'

/-- For a monomorphism `m`, `f` and `f ≫ m` have images of the same class. -/
theorem mk_image_comp_mono {X Y Z : A} (f : X ⟶ Y) (m : Y ⟶ Z) [Mono m] :
    KZero.mk A (Abelian.image (f ≫ m)) = KZero.mk A (Abelian.image f) := by
  have h1 := KZero.mk_eq_kernel_add_image f
  have h2 := KZero.mk_eq_kernel_add_image (f ≫ m)
  rw [KZero.mk_eq_of_iso (kernelCompMono f m)] at h2
  exact add_left_cancel (h2.symm.trans h1)

/-- The image of a morphism out of a zero object has class `0`. -/
theorem mk_image_eq_zero_of_isZero_src {X Y : A} (f : X ⟶ Y) (hX : IsZero X) :
    KZero.mk A (Abelian.image f) = 0 := by
  have h := KZero.mk_eq_kernel_add_image f
  rw [KZero.mk_eq_zero_of_isZero hX,
    KZero.mk_eq_zero_of_isZero (IsZero.of_mono (kernel.ι f) hX), zero_add] at h
  exact h.symm

/-- The image of a morphism into a zero object has class `0`. -/
theorem mk_image_eq_zero_of_isZero_tgt {X Y : A} (f : X ⟶ Y) (hY : IsZero Y) :
    KZero.mk A (Abelian.image f) = 0 :=
  KZero.mk_eq_zero_of_isZero (IsZero.of_mono (Abelian.image.ι f) hY)

end KZero'

variable (X : CochainComplex A ℤ)

/-- The class of the boundaries `Bⁱ ⊆ Zⁱ`, the image of `Xⁱ⁻¹ → Zⁱ`. -/
noncomputable def bdry (i : ℤ) : KZero A :=
  KZero.mk A (Abelian.image (X.toCycles (i - 1) i))

theorem mk_image_toCycles_congr {j k : ℤ} (h : j = k) (i : ℤ) :
    KZero.mk A (Abelian.image (X.toCycles j i)) = KZero.mk A (Abelian.image (X.toCycles k i)) := by
  subst h; rfl

/-- `[Zⁱ] = [Bⁱ] + [Hⁱ]`. -/
theorem mk_cycles (i : ℤ) : KZero.mk A (X.cycles i) = bdry X i + KZero.mk A (X.homology i) := by
  rw [KZero.mk_eq_image_add_cokernel (X.toCycles (i - 1) i), bdry]
  congr 1
  exact KZero.mk_eq_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (X.homologyIsCokernel (i - 1) i (CochainComplex.prev ℤ i)))

/-- `[Xⁱ] = [Hⁱ] + [Bⁱ] + [Bⁱ⁺¹]`. -/
theorem mk_X (i : ℤ) :
    KZero.mk A (X.X i) = KZero.mk A (X.homology i) + (bdry X i + bdry X (i + 1)) := by
  have hk : KZero.mk A (kernel (X.d i (i + 1))) = KZero.mk A (X.cycles i) :=
    KZero.mk_eq_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
      (X.cyclesIsKernel i (i + 1) (CochainComplex.next ℤ i)))
  have hb : KZero.mk A (Abelian.image (X.d i (i + 1))) = bdry X (i + 1) := by
    rw [bdry, mk_image_toCycles_congr X (add_sub_cancel_right i 1), ← X.toCycles_i i (i + 1),
      KZero'.mk_image_comp_mono]
  rw [KZero.mk_eq_kernel_add_image (X.d i (i + 1)), hk, hb, mk_cycles]
  abel

/-- **The Euler formula in `K(A)`.** For a complex `X` of `A` zero outside `[a, b]`,
`Σ (−1)ⁱ [Xⁱ] = Σ (−1)ⁱ [Hⁱ(X)]` in `KZero A`. -/
theorem sum_negOnePow_mk_X_eq {a b : ℤ} (hab : a ≤ b + 1)
    (hX : ∀ i, i < a ∨ b < i → IsZero (X.X i)) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk A (X.X i) =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • KZero.mk A (X.homology i) := by
  have ha : bdry X a = 0 :=
    KZero'.mk_image_eq_zero_of_isZero_src _ (hX (a - 1) (Or.inl (by omega)))
  have hb : bdry X (b + 1) = 0 :=
    KZero'.mk_image_eq_zero_of_isZero_tgt _
      (IsZero.of_mono (X.iCycles (b + 1)) (hX (b + 1) (Or.inr (by omega))))
  rw [Finset.sum_congr rfl fun i _ => by rw [mk_X, smul_add], Finset.sum_add_distrib, sum_Icc_negOnePow_add (bdry X) a b (by omega), ha, hb, smul_zero,
    smul_zero, add_zero, add_zero]

/-- **The Euler formula** (view 3, item 5). Let `χ` be an additive function on the abelian
category `A` with values in an abelian group `G`: `χ(X₂) = χ(X₁) + χ(X₃)` for every short exact
sequence `0 → X₁ → X₂ → X₃ → 0`. For every complex `X` of `A` zero outside `[a, b]`,
`Σ (−1)ⁱ χ(Xⁱ) = Σ (−1)ⁱ χ(Hⁱ(X))`. -/
theorem sum_negOnePow_eq_sum_negOnePow_homology {G : Type*} [AddCommGroup G] (χ : A → G)
    (hχ : ∀ S : ShortComplex A, S.ShortExact → χ S.X₂ = χ S.X₁ + χ S.X₃) {a b : ℤ}
    (hab : a ≤ b + 1) (hX : ∀ i, i < a ∨ b < i → IsZero (X.X i)) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • χ (X.X i) =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • χ (X.homology i) := by
  have := congrArg (KZero.lift χ hχ) (sum_negOnePow_mk_X_eq X hab hX)
  simpa only [map_sum, map_zsmul, KZero.lift_mk] using this

/-- An exact complex zero outside `[a, b]` has alternating sum `0` for every additive `χ`
(the example `0 → K → K² → K → 0` of the notes, `1 − 2 + 1 = 0`). -/
theorem sum_negOnePow_eq_zero_of_exact {G : Type*} [AddCommGroup G] (χ : A → G)
    (hχ : ∀ S : ShortComplex A, S.ShortExact → χ S.X₂ = χ S.X₁ + χ S.X₃) {a b : ℤ}
    (hab : a ≤ b + 1) (hX : ∀ i, i < a ∨ b < i → IsZero (X.X i))
    (hexact : ∀ i, IsZero (X.homology i)) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • χ (X.X i) = 0 := by
  have h0 : ∀ i, χ (X.homology i) = 0 := fun i => by
    have := KZero.lift_mk χ hχ (X.homology i)
    rw [KZero.mk_eq_zero_of_isZero (hexact i), map_zero] at this
    exact this.symm
  rw [sum_negOnePow_eq_sum_negOnePow_homology X χ hχ hab hX]
  simp [h0]

end Grothendieck.IhesSGA6_2_3Euler

#print axioms Grothendieck.IhesSGA6_2_3Euler.sum_negOnePow_mk_X_eq
#print axioms Grothendieck.IhesSGA6_2_3Euler.sum_negOnePow_eq_sum_negOnePow_homology
#print axioms Grothendieck.IhesSGA6_2_3Euler.sum_negOnePow_eq_zero_of_exact
