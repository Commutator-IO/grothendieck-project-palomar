module

public import Mathlib
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.Polynomial.Basis

@[expose] public section


/-!
# Folder 153: integer-valued polynomials, co-operations, analyseurs

The modernised reading `transcripts/153/153.modern.tex` (manuscript page 3)
fixes a pair of commutative rings `k₀ ⊂ K₀` and
`Ω = Int(k₀) = {F ∈ K₀[T] | F(λ) ∈ k₀ for all λ ∈ k₀}`, and states:

> **Lemme.** Si `M` est un `k₀`-module libre, l'ensemble des
> `F ∈ K₀[T] ⊗_{k₀} M` tels que `F(x) ∈ M` pour tout `x ∈ k₀` s'identifie à
> `Ω ⊗_{k₀} M` — coordonnée par coordonnée dans une base de `M`.

Here `F(x)` is the image of `F` under `ev_x ⊗ id : K₀[T] ⊗ M → K₀ ⊗ M`, and
"`F(x) ∈ M`" means that it lies in the image of `M → K₀ ⊗ M`, `m ↦ 1 ⊗ m`.
"S'identifie à" is read as: the canonical map `Ω ⊗ M → K₀[T] ⊗ M` is injective
(`lemme_injective`) and its image is exactly that set (`lemme_range`). The
reading's "coordinate by coordinate" is `lemme_coordonnees`: in a basis of `M`,
`F` satisfies the condition iff each of its coordinates lies in `Ω`.

What the formalisation found. The Lemme holds as stated, and one hypothesis
is not used: that `k₀ → K₀` is an inclusion. The proof works for any
`k₀`-algebra `K₀`, `Int(k₀)` being then the polynomials sending `k₀` into the
image of `k₀`. Freeness of `M` is used twice, as the reading says it is: for
the injectivity (a free module is flat, `Module.Flat.of_free`) and for the
coordinates. (The reading's footnote on the co-operations — that
`K₀[X] ⊗_{k₀} K₀[Y] = K₀[X,Y]` needs `K₀ ⊗_{k₀} K₀ = K₀` — concerns the next
paragraph; the co-operations are formalised below without it.)

## The rest of the folder

* Page 3: `Ω` is stable under composition (`comp_mem_Omega`); for `K₀ = S⁻¹k₀` and
  `Ω` free, `Φ : Ω ⊗ Ω → K₀[X, Y]`, `G ⊗ H ↦ G(X) H(Y)`, is injective
  (`Phi_injective`) with image the polynomials taking values in `k₀` on `k₀ × k₀`
  (`mem_range_Phi_iff`), so `F(X + Y)` and `F(XY)` have unique preimages
  (`coaddition_existsUnique`, `comultiplication_existsUnique`), and the rules
  `F ∘ (P + Q) = ∑ (Gᵢ ∘ P)(Hᵢ ∘ Q)`, `F ∘ (PQ) = ∑ (Jₐ ∘ P)(Kₐ ∘ Q)` hold for any
  representative (`comp_add_eq`, `comp_mul_eq`). What the proof uses of `K₀` is
  that `K₀ ⊗_{k₀} Ω → K₀[T]` be injective (`..._of_injective`); it is always
  surjective (`omegaBaseChange_surjective`), and injective for `K₀` a localisation
  (`omegaBaseChange_injective`) and for `K₀` flat over `k₀` with `K₀ ⊗ K₀ = K₀`
  (`omegaBaseChange_injective_of_flat`). Whether `K₀ ⊗ K₀ = K₀` alone suffices is
  left open.
* Page 2: Pólya's basis of `Int(ℤ)` by forward differences (`polya`, `polyaBasis`),
  Vandermonde in `ℚ[X, Y]` from mathlib's `Ring.add_choose_eq` (`vandermonde`), and
  the co-operations of `Int(ℤ)` (`coaddition_binom`, `comultiplication_binom`).
* Page 5: for a composition satisfying 1) and 2) (`Composition`), the constants
  form a sub-pseudo-ring, `F ∘ 0` is a constant, `Ω⁰` is an ideal and
  `Ω = Ω₀ ⊕ Ω⁰` (`Composition.isCompl_constants_zeroPart`); 3) is not used.
* Page 7: `(Appl(A, A))₀ ≃ A` (`applConstantsEquiv`); `Appl(A, A)` fails 3a) for an
  infinite nonzero commutative ring (`appl_not_coaddition`); the constants of `k[T]`
  are `k` (`mem_constants_poly`); `T^q - T` kills every constant over `𝔽_q`
  (`poly_toAppl_not_injective`), while over an infinite domain, and for `Int(ℤ)`,
  `Ω → Ω_{Ω₀}` is injective (`poly_toAppl_injective`, `eq_of_comp_intCast`);
  `∑_{m ≥ 1} T^m` has no finite co-addition in `k[[T]]⁺`, stated on coefficients
  (`geom_not_finite_coaddition`, from `pascal_det`).
-/

namespace Grothendieck.Folder153

open Polynomial TensorProduct

section Coordonnees

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R M)

/-- Coordinates of `N ⊗ M` in a basis `b` of `M`: `N ⊗ M ≃ ι →₀ N`. -/
noncomputable def coords (N : Type*) [AddCommGroup N] [Module R N] :
    N ⊗[R] M ≃ₗ[R] ι →₀ N :=
  TensorProduct.congr (LinearEquiv.refl R N) b.repr ≪≫ₗ finsuppScalarRight R R N ι

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem coords_tmul (n : N) (m : M) (i : ι) :
    coords b N (n ⊗ₜ m) i = b.repr m i • n := by
  simp [coords]

/-- The coordinates are natural in `N`. -/
theorem coords_rTensor (f : N →ₗ[R] P) (t : N ⊗[R] M) :
    coords b P (f.rTensor M t) = Finsupp.mapRange f f.map_zero (coords b N t) := by
  induction t using TensorProduct.inductionOn with
  | tmul n m => ext i; simp [coords_tmul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, Finsupp.mapRange_add f.map_add]

/-- An element of `P ⊗ M` comes from `N ⊗ M` iff each coordinate comes from `N`. -/
theorem mem_range_rTensor (f : N →ₗ[R] P) (t : P ⊗[R] M) :
    t ∈ LinearMap.range (f.rTensor M) ↔ ∀ i, coords b P t i ∈ LinearMap.range f := by
  constructor
  · rintro ⟨s, rfl⟩ i
    rw [coords_rTensor, Finsupp.mapRange_apply]
    exact ⟨_, rfl⟩
  · intro h
    choose g hg using h
    let s : ι →₀ N := ∑ i ∈ (coords b P t).support, Finsupp.single i (g i)
    refine ⟨(coords b N).symm s, (coords b P).injective ?_⟩
    rw [coords_rTensor, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finsupp.mapRange_apply, Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hj
    · exact hg j
    · exact (map_zero f).trans (Finsupp.notMem_support_iff.mp hj).symm

theorem coords_tmul_basis (n : N) (j : ι) : coords b N (n ⊗ₜ b j) = Finsupp.single j n := by
  ext i
  rw [coords_tmul, b.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- Every `t ∈ N ⊗ M` is `∑ⱼ tⱼ ⊗ bⱼ`, its coordinates against the basis. -/
theorem eq_sum_coords (t : N ⊗[R] M) : t = (coords b N t).sum fun j n => n ⊗ₜ b j := by
  apply (coords b N).injective
  rw [map_finsuppSum]
  simp only [coords_tmul_basis]
  exact (Finsupp.sum_single _).symm

end Coordonnees

variable {k₀ K₀ : Type*} [CommRing k₀] [CommRing K₀] [Algebra k₀ K₀]

/-- Evaluation at `x ∈ k₀`, as a `k₀`-linear map `K₀[T] → K₀`. -/
noncomputable def ev (x : k₀) : K₀[X] →ₗ[k₀] K₀ :=
  (Polynomial.leval (algebraMap k₀ K₀ x)).restrictScalars k₀

theorem ev_apply (x : k₀) (F : K₀[X]) : ev x F = F.eval (algebraMap k₀ K₀ x) := rfl

variable (k₀ K₀) in
/-- `Ω = Int(k₀)`: the polynomials of `K₀[T]` taking values in `k₀` on `k₀`. -/
noncomputable def Omega : Subalgebra k₀ K₀[X] where
  carrier := {F | ∀ x : k₀, F.eval (algebraMap k₀ K₀ x) ∈ (algebraMap k₀ K₀).range}
  mul_mem' {F G} hF hG x := by rw [eval_mul]; exact mul_mem (hF x) (hG x)
  add_mem' {F G} hF hG x := by rw [eval_add]; exact add_mem (hF x) (hG x)
  algebraMap_mem' c x := by
    rw [Polynomial.algebraMap_apply, eval_C]; exact ⟨c, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module k₀ M]

variable (K₀ M) in
/-- The set of the Lemme: the `F ∈ K₀[T] ⊗ M` such that `F(x) ∈ M` for every
`x ∈ k₀`, i.e. `(ev_x ⊗ id) F` lies in the image of `m ↦ 1 ⊗ m`. -/
def valeursDansM : Set (K₀[X] ⊗[k₀] M) :=
  {F | ∀ x : k₀, (ev x).rTensor M F ∈ LinearMap.range (TensorProduct.mk k₀ K₀ M 1)}

/-- The image of `m ↦ 1 ⊗ m` is the image of `k₀ ⊗ M → K₀ ⊗ M`. -/
theorem range_mk_one :
    LinearMap.range (TensorProduct.mk k₀ K₀ M 1) =
      LinearMap.range ((Algebra.linearMap k₀ K₀).rTensor M) := by
  have : TensorProduct.mk k₀ K₀ M 1 =
      (Algebra.linearMap k₀ K₀).rTensor M ∘ₗ (TensorProduct.lid k₀ M).symm.toLinearMap := by
    ext m; simp
  rw [this, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- **Lemme, coordinate by coordinate.** In a basis `b` of `M`, `F ∈ K₀[T] ⊗ M`
takes values in `M` on `k₀` iff each of its coordinates lies in `Ω = Int(k₀)`. -/
theorem lemme_coordonnees {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k₀ M) (F : K₀[X] ⊗[k₀] M) :
    F ∈ valeursDansM K₀ M ↔ ∀ i, coords b K₀[X] F i ∈ Omega k₀ K₀ := by
  simp only [valeursDansM, Set.mem_ofPred_eq, range_mk_one, mem_range_rTensor b,
    coords_rTensor, Finsupp.mapRange_apply, ev_apply]
  exact ⟨fun h i x => h x i, fun h x i => h i x⟩

/-- **Lemme (1).** For `M` free, `Ω ⊗ M → K₀[T] ⊗ M` is injective. -/
theorem lemme_injective [Module.Free k₀ M] :
    Function.Injective ((Omega k₀ K₀).val.toLinearMap.rTensor M) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- **Lemme (2).** For `M` free, the image of `Ω ⊗ M → K₀[T] ⊗ M` is exactly the
set of `F` with `F(x) ∈ M` for every `x ∈ k₀`. -/
theorem lemme_range [Module.Free k₀ M] :
    (LinearMap.range ((Omega k₀ K₀).val.toLinearMap.rTensor M) : Set (K₀[X] ⊗[k₀] M)) =
      valeursDansM K₀ M := by
  classical
  let b := Module.Free.chooseBasis k₀ M
  ext F
  rw [SetLike.mem_coe, mem_range_rTensor b, lemme_coordonnees b]
  exact forall_congr' fun i => ⟨fun ⟨G, hG⟩ => hG ▸ G.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

/-! ### `Ω = Int(k₀)` is stable under composition (pages 3 and 9) -/

theorem mem_Omega {F : K₀[X]} :
    F ∈ Omega k₀ K₀ ↔ ∀ x : k₀, F.eval (algebraMap k₀ K₀ x) ∈ (algebraMap k₀ K₀).range :=
  Iff.rfl

theorem comp_mem_Omega {F G : K₀[X]} (hF : F ∈ Omega k₀ K₀) (hG : G ∈ Omega k₀ K₀) :
    F.comp G ∈ Omega k₀ K₀ := fun x => by
  obtain ⟨y, hy⟩ := hG x
  rw [eval_comp, ← hy]
  exact hF y

/-! ### The co-operations of page 3

`K₀[X, Y]` is `K₀[X][X]` (Lean's `K₀[X][X]`): the outer variable, written `X`,
plays the reading's `X`, the inner one, `C X`, its `Y`. -/

/-- `Δₐ F = F(X + Y)`. -/
noncomputable def coadd (F : K₀[X]) : K₀[X][X] :=
  F.eval₂ ((C : K₀[X] →+* K₀[X][X]).comp C) (X + C X)

/-- `Δₘ F = F(XY)`. -/
noncomputable def comul (F : K₀[X]) : K₀[X][X] :=
  F.eval₂ ((C : K₀[X] →+* K₀[X][X]).comp C) (X * C X)

theorem eval_eval_coadd (F : K₀[X]) (a b : K₀) :
    ((coadd F).eval (C a)).eval b = F.eval (a + b) := by
  have h : (evalRingHom b).comp ((evalRingHom (C a)).comp ((C : K₀[X] →+* K₀[X][X]).comp C)) =
      RingHom.id K₀ := RingHom.ext fun c => by simp
  unfold coadd
  rw [← coe_evalRingHom (C a), hom_eval₂, ← coe_evalRingHom b, hom_eval₂, h, eval₂_id]
  simp

theorem eval_eval_comul (F : K₀[X]) (a b : K₀) :
    ((comul F).eval (C a)).eval b = F.eval (a * b) := by
  have h : (evalRingHom b).comp ((evalRingHom (C a)).comp ((C : K₀[X] →+* K₀[X][X]).comp C)) =
      RingHom.id K₀ := RingHom.ext fun c => by simp
  unfold comul
  rw [← coe_evalRingHom (C a), hom_eval₂, ← coe_evalRingHom b, hom_eval₂, h, eval₂_id]
  simp

variable (k₀ K₀) in
/-- `Φ : Ω ⊗ Ω → K₀[X, Y]`, `G ⊗ H ↦ G(X) H(Y)`. -/
noncomputable def Phi : Omega k₀ K₀ ⊗[k₀] Omega k₀ K₀ →ₗ[k₀] K₀[X][X] :=
  TensorProduct.lift <| LinearMap.mk₂ k₀
    (fun G H : Omega k₀ K₀ => (G : K₀[X]).map C * C (H : K₀[X]))
    (fun G G' H => by simp [Polynomial.map_add, add_mul])
    (fun c G H => by
      change (c • (G : K₀[X])).map C * C (H : K₀[X]) = _
      simp only [Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.map_mul, map_C,
        mul_assoc])
    (fun G H H' => by simp [mul_add])
    (fun c G H => by
      change (G : K₀[X]).map C * C (c • (H : K₀[X])) = _
      simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
      ring)

theorem Phi_tmul (G H : Omega k₀ K₀) :
    Phi k₀ K₀ (G ⊗ₜ H) = (G : K₀[X]).map C * C (H : K₀[X]) := by
  simp [Phi]

/-- Evaluation `X ↦ P`, `Y ↦ Q`. -/
noncomputable def evPQ (P Q : K₀[X]) : K₀[X][X] →+* K₀[X] :=
  eval₂RingHom (compRingHom Q) P

theorem evPQ_tmul (P Q G H : K₀[X]) : evPQ P Q (G.map C * C H) = G.comp P * H.comp Q := by
  have hC : (compRingHom Q).comp (C : K₀ →+* K₀[X]) = C := RingHom.ext fun a => by simp
  simp only [evPQ, map_mul, coe_eval₂RingHom, eval₂_map, hC, eval₂_C, coe_compRingHom_apply]
  rfl

theorem evPQ_CC (P Q : K₀[X]) :
    (evPQ P Q).comp ((C : K₀[X] →+* K₀[X][X]).comp C) = C :=
  RingHom.ext fun a => by simp [evPQ]

theorem evPQ_coadd (F P Q : K₀[X]) : evPQ P Q (coadd F) = F.comp (P + Q) := by
  have hx : evPQ P Q (X + C X) = P + Q := by simp [evPQ]
  rw [coadd, hom_eval₂, evPQ_CC, hx]
  rfl

theorem evPQ_comul (F P Q : K₀[X]) : evPQ P Q (comul F) = F.comp (P * Q) := by
  have hx : evPQ P Q (X * C X) = P * Q := by
    simp only [evPQ, coe_eval₂RingHom, eval₂_mul, eval₂_X, eval₂_C, coe_compRingHom_apply, X_comp]
  rw [comul, hom_eval₂, evPQ_CC, hx]
  rfl

/-- **Page 3, the rule `F ∘ (P + Q) = ∑ (Gᵢ ∘ P)(Hᵢ ∘ Q)`.** Whenever `∑ Gᵢ ⊗ Hᵢ`
represents `F(X + Y)`, composition with a sum follows. -/
theorem comp_add_eq {ι : Type*} (s : Finset ι) (G H : ι → Omega k₀ K₀) (F : K₀[X])
    (h : Phi k₀ K₀ (∑ i ∈ s, G i ⊗ₜ H i) = coadd F) (P Q : K₀[X]) :
    F.comp (P + Q) = ∑ i ∈ s, (G i : K₀[X]).comp P * (H i : K₀[X]).comp Q := by
  rw [← evPQ_coadd, ← h, map_sum, map_sum]
  simp only [Phi_tmul, evPQ_tmul]

/-- **Page 3, the rule `F ∘ (PQ) = ∑ (Jₐ ∘ P)(Kₐ ∘ Q)`.** -/
theorem comp_mul_eq {ι : Type*} (s : Finset ι) (J K : ι → Omega k₀ K₀) (F : K₀[X])
    (h : Phi k₀ K₀ (∑ i ∈ s, J i ⊗ₜ K i) = comul F) (P Q : K₀[X]) :
    F.comp (P * Q) = ∑ i ∈ s, (J i : K₀[X]).comp P * (K i : K₀[X]).comp Q := by
  rw [← evPQ_comul, ← h, map_sum, map_sum]
  simp only [Phi_tmul, evPQ_tmul]

theorem eval_eval_Phi_tmul (G H : K₀[X]) (a b : K₀) :
    ((G.map C * C H).eval (C a)).eval b = G.eval a * H.eval b := by
  simp [eval_map, eval₂_at_apply]

/-- The image of `Φ` takes values in `k₀` on `k₀ × k₀`. -/
theorem values_of_mem_range_Phi {P : K₀[X][X]} (hP : P ∈ LinearMap.range (Phi k₀ K₀))
    (x y : k₀) :
    (P.eval (C (algebraMap k₀ K₀ x))).eval (algebraMap k₀ K₀ y) ∈ (algebraMap k₀ K₀).range := by
  obtain ⟨t, rfl⟩ := hP
  induction t using TensorProduct.inductionOn with
  | tmul G H =>
    rw [Phi_tmul, eval_eval_Phi_tmul]
    exact mul_mem (mem_Omega.mp G.2 x) (mem_Omega.mp H.2 y)
  | add t t' ht ht' =>
    rw [map_add, eval_add, eval_add]
    exact add_mem ht ht'

/-! ### The co-operations for any `k₀ → K₀` with `K₀ ⊗_{k₀} Ω ↪ K₀[T]`

The proof of page 3 uses one property of the pair: a `k₀`-basis of `Ω` stays a
basis of `K₀[T]` over `K₀`, i.e. `K₀ ⊗_{k₀} Ω → K₀[T]` is bijective. It is always
surjective, since `k₀[T] ⊂ Ω` (`omegaBaseChange_surjective`); injectivity is the
hypothesis. It holds for `K₀` a localisation of `k₀` (`omegaBaseChange_injective`)
and, more generally, for `K₀` flat over `k₀` with `K₀ ⊗_{k₀} K₀ = K₀`
(`omegaBaseChange_injective_of_flat`). -/

variable (k₀ K₀) in
/-- `K₀ ⊗_{k₀} Ω → K₀[T]`, `a ⊗ F ↦ a F`. -/
noncomputable def omegaBaseChange : K₀ ⊗[k₀] Omega k₀ K₀ →ₗ[K₀] K₀[X] :=
  LinearMap.liftBaseChange K₀ (Omega k₀ K₀).val.toLinearMap

theorem omegaBaseChange_tmul (a : K₀) (F : Omega k₀ K₀) :
    omegaBaseChange k₀ K₀ (a ⊗ₜ F) = a • (F : K₀[X]) := by
  simp [omegaBaseChange]

/-- In a basis `e` of `Ω`, `K₀ ⊗ Ω → K₀[T]` sends `∑ aⱼ ⊗ eⱼ` to `∑ aⱼ eⱼ`. -/
theorem omegaBaseChange_eq_sum {I : Type*} (e : Module.Basis I k₀ (Omega k₀ K₀))
    (t : K₀ ⊗[k₀] Omega k₀ K₀) :
    omegaBaseChange k₀ K₀ t = ((e.baseChange K₀).repr t).sum fun j c => c • (e j : K₀[X]) := by
  conv_lhs => rw [← (e.baseChange K₀).linearCombination_repr t]
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [map_smul, Module.Basis.baseChange_apply, omegaBaseChange_tmul, one_smul]

theorem X_pow_mem_Omega (n : ℕ) : (X ^ n : K₀[X]) ∈ Omega k₀ K₀ :=
  mem_Omega.mpr fun x => ⟨x ^ n, by simp⟩

/-- `K₀ ⊗_{k₀} Ω → K₀[T]` is always surjective: `k₀[T] ⊂ Ω`. -/
theorem omegaBaseChange_surjective : Function.Surjective (omegaBaseChange k₀ K₀) := by
  intro p
  change p ∈ LinearMap.range (omegaBaseChange k₀ K₀)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact add_mem hp hq
  | monomial n a =>
    exact ⟨a ⊗ₜ ⟨X ^ n, X_pow_mem_Omega n⟩, by
      rw [omegaBaseChange_tmul, ← C_mul_X_pow_eq_monomial, smul_eq_C_mul]⟩

/-- A `k₀`-basis of `Ω` spans `K₀[T]` over `K₀`, for any `k₀`-algebra `K₀`. -/
theorem exists_sum_smul_basis {I : Type*} (e : Module.Basis I k₀ (Omega k₀ K₀)) (p : K₀[X]) :
    ∃ a : I →₀ K₀, (a.sum fun j c => c • (e j : K₀[X])) = p := by
  obtain ⟨t, rfl⟩ := omegaBaseChange_surjective (k₀ := k₀) p
  exact ⟨(e.baseChange K₀).repr t, (omegaBaseChange_eq_sum e t).symm⟩

/-- When `K₀ ⊗_{k₀} Ω → K₀[T]` is injective, a `k₀`-basis of `Ω` stays linearly
independent over `K₀`. -/
theorem sum_smul_basis_eq_zero_of_injective (hK : Function.Injective (omegaBaseChange k₀ K₀))
    {I : Type*} (e : Module.Basis I k₀ (Omega k₀ K₀)) (a : I →₀ K₀)
    (h : (a.sum fun j c => c • (e j : K₀[X])) = 0) : a = 0 := by
  have ht : omegaBaseChange k₀ K₀ ((e.baseChange K₀).repr.symm a) = 0 := by
    rw [omegaBaseChange_eq_sum e, LinearEquiv.apply_symm_apply, h]
  exact (e.baseChange K₀).repr.symm.map_eq_zero_iff.mp
    ((injective_iff_map_eq_zero _).mp hK _ ht)

/-- **`K₀` flat over `k₀` with `K₀ ⊗_{k₀} K₀ = K₀`** (multiplication injective, i.e.
`K₀[X] ⊗_{k₀} K₀[Y] = K₀[X, Y]`): then `K₀ ⊗_{k₀} Ω → K₀[T]` is injective. -/
theorem omegaBaseChange_injective_of_flat [Module.Flat k₀ K₀]
    (hmul : Function.Injective (LinearMap.mul' k₀ K₀)) :
    Function.Injective (omegaBaseChange k₀ K₀) := by
  set g : K₀ ⊗[k₀] K₀[X] →ₗ[k₀] K₀[X] :=
    (LinearMap.liftBaseChange K₀ ((LinearMap.id : K₀[X] →ₗ[K₀] K₀[X]).restrictScalars k₀)).restrictScalars k₀
  have hfac : ∀ t, omegaBaseChange k₀ K₀ t =
      g (LinearMap.lTensor K₀ (Omega k₀ K₀).val.toLinearMap t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a F => simp [g, omegaBaseChange_tmul]
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
  set E : K₀[X] ≃ₗ[k₀] ℕ →₀ K₀ := (Polynomial.basisMonomials K₀).repr.restrictScalars k₀
  have hE : ∀ p n, E p n = p.coeff n := fun p n => rfl
  have hc : ∀ (t : K₀ ⊗[k₀] K₀[X]) n,
      LinearMap.mul' k₀ K₀ (finsuppRight k₀ k₀ K₀ K₀ ℕ (LinearMap.lTensor K₀ E.toLinearMap t) n) =
        (g t).coeff n := by
    intro t n
    induction t using TensorProduct.inductionOn with
    | tmul a p => simp [g, hE, finsuppRight_apply_tmul_apply]
    | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, coeff_add, ht, ht']
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
    have h0 : finsuppRight k₀ k₀ K₀ K₀ ℕ (LinearMap.lTensor K₀ E.toLinearMap t) = 0 := by
      ext n
      apply hmul
      rw [hc, ht, Finsupp.coe_zero, Pi.zero_apply, map_zero, coeff_zero]
    rw [LinearEquiv.map_eq_zero_iff] at h0
    exact (LinearEquiv.lTensor K₀ E).map_eq_zero_iff.mp h0
  intro t t' h
  rw [hfac, hfac] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective (hg h)

theorem exists_decomp {I : Type*} (e : Module.Basis I k₀ (Omega k₀ K₀)) (P : K₀[X][X]) :
    ∃ g : I →₀ K₀[X], P = g.sum fun j G => G.map C * C (e j : K₀[X]) := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨g, rfl⟩ := hP
    obtain ⟨g', rfl⟩ := hQ
    exact ⟨g + g', (Finsupp.sum_add_index' (fun j => by simp)
      (fun j G G' => by simp [Polynomial.map_add, add_mul])).symm⟩
  | monomial n p =>
    obtain ⟨a, ha⟩ := exists_sum_smul_basis e p
    refine ⟨a.mapRange (fun c => C c * X ^ n) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (fun j => by simp), ← ha, ← C_mul_X_pow_eq_monomial]
    simp only [Finsupp.sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_eq_C_mul, map_mul, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]
    ring

/-- **Two-variable form of the Lemme.** When `K₀ ⊗_{k₀} Ω → K₀[T]` is injective
and `Ω` is free, a
polynomial of `K₀[X, Y]` lies in the image of `Ω ⊗ Ω` iff it takes values in `k₀`
on `k₀ × k₀`. -/
theorem mem_range_Phi_iff_of_injective [Module.Free k₀ (Omega k₀ K₀)]
    (hK : Function.Injective (omegaBaseChange k₀ K₀)) (P : K₀[X][X]) :
    P ∈ LinearMap.range (Phi k₀ K₀) ↔ ∀ x y : k₀,
      (P.eval (C (algebraMap k₀ K₀ x))).eval (algebraMap k₀ K₀ y) ∈ (algebraMap k₀ K₀).range := by
  classical
  refine ⟨values_of_mem_range_Phi, fun hP => ?_⟩
  set e := Module.Free.chooseBasis k₀ (Omega k₀ K₀)
  obtain ⟨g, rfl⟩ := exists_decomp e P
  have hg : ∀ j, g j ∈ Omega k₀ K₀ := fun j x => by
    set a := algebraMap k₀ K₀ x
    have hQ : (g.sum fun j G => G.map C * C (e j : K₀[X])).eval (C a) =
        g.sum fun j G => G.eval a • (e j : K₀[X]) := by
      simp [Finsupp.sum, eval_finsetSum, eval_map, eval₂_at_apply, smul_eq_C_mul]
    have hQΩ : (g.sum fun j G => G.eval a • (e j : K₀[X])) ∈ Omega k₀ K₀ :=
      mem_Omega.mpr fun y => by rw [← hQ]; exact hP x y
    obtain ⟨β, hβ⟩ : ∃ β : _ →₀ k₀,
        (β.sum fun j c => c • (e j : K₀[X])) = g.sum fun j G => G.eval a • (e j : K₀[X]) := by
      refine ⟨e.repr ⟨_, hQΩ⟩, ?_⟩
      have := congrArg Subtype.val (e.linearCombination_repr ⟨_, hQΩ⟩)
      rw [Finsupp.linearCombination_apply] at this
      simpa [Finsupp.sum] using this
    have h0 := sum_smul_basis_eq_zero_of_injective hK e
      (g.mapRange (fun G => G.eval a) (eval_zero) - β.mapRange (algebraMap k₀ K₀) (map_zero _)) (by
        rw [Finsupp.sum_sub_index (fun j c c' => sub_smul c c' _),
          Finsupp.sum_mapRange_index (h := fun j c => c • (e j : K₀[X])) (fun j => zero_smul _ _),
          Finsupp.sum_mapRange_index (h := fun j c => c • (e j : K₀[X])) (fun j => zero_smul _ _),
          sub_eq_zero]
        simp only [algebraMap_smul]
        exact hβ.symm)
    have := DFunLike.congr_fun h0 j
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, Finsupp.coe_zero,
      Pi.zero_apply, sub_eq_zero] at this
    exact ⟨β j, this.symm⟩
  refine ⟨∑ j ∈ g.support, (⟨g j, hg j⟩ : Omega k₀ K₀) ⊗ₜ e j, ?_⟩
  simp [map_sum, Phi_tmul, Finsupp.sum]

/-- **Uniqueness.** When `K₀ ⊗_{k₀} Ω → K₀[T]` is injective and `Ω` is free, `Φ : Ω ⊗ Ω → K₀[X, Y]` is injective. -/
theorem Phi_injective_of_injective [Module.Free k₀ (Omega k₀ K₀)]
    (hK : Function.Injective (omegaBaseChange k₀ K₀)) : Function.Injective (Phi k₀ K₀) := by
  classical
  set e := Module.Free.chooseBasis k₀ (Omega k₀ K₀)
  have hz : ∀ m, ((0 : Omega k₀ K₀) : K₀[X]).coeff m = 0 := coeff_zero
  have hΦ : ∀ t, Phi k₀ K₀ t =
      (coords e (Omega k₀ K₀) t).sum fun j H => (H : K₀[X]).map C * C (e j : K₀[X]) := by
    intro t
    conv_lhs => rw [eq_sum_coords e t]
    rw [map_finsuppSum]
    simp only [Phi_tmul]
  have hcoeff : ∀ t m, (Phi k₀ K₀ t).coeff m =
      ((coords e (Omega k₀ K₀) t).mapRange (fun H : Omega k₀ K₀ => (H : K₀[X]).coeff m)
        (hz m)).sum fun j c => c • (e j : K₀[X]) := by
    intro t m
    rw [hΦ, Finsupp.sum_mapRange_index (h := fun j c => c • (e j : K₀[X]))
      (fun j => zero_smul _ _)]
    simp [Finsupp.sum, finsetSum_coeff, coeff_mul_C, coeff_map, smul_eq_C_mul]
  intro t t' h
  apply (coords e (Omega k₀ K₀)).injective
  ext j : 1
  apply Subtype.ext
  ext m
  have h0 := sum_smul_basis_eq_zero_of_injective hK e
    (((coords e _ t).mapRange (fun H : Omega k₀ K₀ => (H : K₀[X]).coeff m) (hz m)) -
      ((coords e _ t').mapRange (fun H : Omega k₀ K₀ => (H : K₀[X]).coeff m) (hz m))) (by
    rw [Finsupp.sum_sub_index (fun j c c' => sub_smul c c' _), ← hcoeff, ← hcoeff, h, sub_self])
  simpa [sub_eq_zero, Finsupp.mapRange_apply] using DFunLike.congr_fun h0 j

/-- **The co-addition is well defined (page 3), for any `k₀ → K₀` with
`K₀ ⊗_{k₀} Ω ↪ K₀[T]`.** For `F ∈ Ω`, `F(X + Y)` is the image of exactly one
element of `Ω ⊗ Ω`. -/
theorem coaddition_existsUnique_of_injective [Module.Free k₀ (Omega k₀ K₀)]
    (hK : Function.Injective (omegaBaseChange k₀ K₀)) {F : K₀[X]}
    (hF : F ∈ Omega k₀ K₀) : ∃! t, Phi k₀ K₀ t = coadd F := by
  obtain ⟨t, ht⟩ := (mem_range_Phi_iff_of_injective hK (coadd F)).mpr fun x y => by
    rw [eval_eval_coadd, ← map_add]; exact mem_Omega.mp hF (x + y)
  exact ⟨t, ht, fun t' ht' => Phi_injective_of_injective hK (ht'.trans ht.symm)⟩

/-- **The co-multiplication is well defined (page 3), same hypothesis.** -/
theorem comultiplication_existsUnique_of_injective [Module.Free k₀ (Omega k₀ K₀)]
    (hK : Function.Injective (omegaBaseChange k₀ K₀)) {F : K₀[X]}
    (hF : F ∈ Omega k₀ K₀) : ∃! t, Phi k₀ K₀ t = comul F := by
  obtain ⟨t, ht⟩ := (mem_range_Phi_iff_of_injective hK (comul F)).mpr fun x y => by
    rw [eval_eval_comul, ← map_mul]; exact mem_Omega.mp hF (x * y)
  exact ⟨t, ht, fun t' ht' => Phi_injective_of_injective hK (ht'.trans ht.symm)⟩

section Localisation

variable (S : Submonoid k₀) [IsLocalization S K₀]
include S

/-- When `K₀ = S⁻¹k₀`, a `k₀`-basis of `Ω` stays linearly independent over `K₀`. -/
theorem sum_smul_basis_eq_zero {I : Type*} (e : Module.Basis I k₀ (Omega k₀ K₀)) (a : I →₀ K₀)
    (h : (a.sum fun j c => c • (e j : K₀[X])) = 0) : a = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset S (a.support.image a)
  have hb' : ∀ j, ∃ d : k₀, algebraMap k₀ K₀ d = (b : k₀) • a j := by
    intro j
    by_cases hj : j ∈ a.support
    · exact hb (a j) (Finset.mem_image_of_mem a hj)
    · rw [Finsupp.notMem_support_iff.mp hj, smul_zero]
      exact ⟨0, map_zero _⟩
  choose d hd using hb'
  have hu : IsUnit (algebraMap k₀ K₀ b) := IsLocalization.map_units K₀ b
  have hsum : ∑ j ∈ a.support, d j • e j = 0 := by
    apply Subtype.val_injective
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    calc ∑ j ∈ a.support, ((d j • e j : Omega k₀ K₀) : K₀[X])
        = ∑ j ∈ a.support, algebraMap k₀ K₀ b • (a j • (e j : K₀[X])) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [SetLike.val_smul, ← algebraMap_smul K₀ (d j), hd, smul_assoc, algebraMap_smul]
      _ = algebraMap k₀ K₀ b • (a.sum fun j c => c • (e j : K₀[X])) := by
          rw [Finsupp.sum, Finset.smul_sum]
      _ = 0 := by rw [h, smul_zero]
  ext j
  by_cases hj : j ∈ a.support
  · have h1 := linearIndependent_iff'.mp e.linearIndependent _ _ hsum j hj
    have h2 := hd j
    rw [h1, map_zero, Algebra.smul_def] at h2
    exact hu.mul_right_eq_zero.mp h2.symm
  · exact Finsupp.notMem_support_iff.mp hj

/-- When `K₀ = S⁻¹k₀` and `Ω` is free, `K₀ ⊗_{k₀} Ω → K₀[T]` is injective. -/
theorem omegaBaseChange_injective [Module.Free k₀ (Omega k₀ K₀)] :
    Function.Injective (omegaBaseChange k₀ K₀) := by
  set e := Module.Free.chooseBasis k₀ (Omega k₀ K₀)
  refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
  have h0 := sum_smul_basis_eq_zero S e ((e.baseChange K₀).repr t) (by
    rw [← omegaBaseChange_eq_sum e, ht])
  exact (e.baseChange K₀).repr.map_eq_zero_iff.mp h0

/-- **Two-variable form of the Lemme.** For `K₀ = S⁻¹k₀` and `Ω` free, a
polynomial of `K₀[X, Y]` lies in the image of `Ω ⊗ Ω` iff it takes values in `k₀`
on `k₀ × k₀`. -/
theorem mem_range_Phi_iff [Module.Free k₀ (Omega k₀ K₀)] (P : K₀[X][X]) :
    P ∈ LinearMap.range (Phi k₀ K₀) ↔ ∀ x y : k₀,
      (P.eval (C (algebraMap k₀ K₀ x))).eval (algebraMap k₀ K₀ y) ∈ (algebraMap k₀ K₀).range :=
  mem_range_Phi_iff_of_injective (omegaBaseChange_injective S) P

/-- **Uniqueness.** For `K₀ = S⁻¹k₀` and `Ω` free, `Φ : Ω ⊗ Ω → K₀[X, Y]` is injective. -/
theorem Phi_injective [Module.Free k₀ (Omega k₀ K₀)] : Function.Injective (Phi k₀ K₀) :=
  Phi_injective_of_injective (omegaBaseChange_injective S)

/-- **The co-addition is well defined (page 3).** For `K₀ = S⁻¹k₀`, `Ω` free and
`F ∈ Ω`, `F(X + Y)` is the image of exactly one element of `Ω ⊗ Ω`. -/
theorem coaddition_existsUnique [Module.Free k₀ (Omega k₀ K₀)] {F : K₀[X]}
    (hF : F ∈ Omega k₀ K₀) : ∃! t, Phi k₀ K₀ t = coadd F :=
  coaddition_existsUnique_of_injective (omegaBaseChange_injective S) hF

/-- **The co-multiplication is well defined (page 3).** -/
theorem comultiplication_existsUnique [Module.Free k₀ (Omega k₀ K₀)] {F : K₀[X]}
    (hF : F ∈ Omega k₀ K₀) : ∃! t, Phi k₀ K₀ t = comul F :=
  comultiplication_existsUnique_of_injective (omegaBaseChange_injective S) hF

end Localisation

/-! ### Pólya and Vandermonde (page 2): `Int(ℤ) = ⊕ ℤ binom(T, n)` -/

/-- `Fₙ = binom(T, n) ∈ ℚ[T]`. -/
noncomputable def binom (n : ℕ) : ℚ[X] := Ring.choose (X : ℚ[X]) n

theorem binom_eval (a : ℚ) (n : ℕ) : (binom n).eval a = Ring.choose a n := by
  simpa [binom] using Ring.map_choose (evalRingHom a) (X : ℚ[X]) n

theorem binom_eval_nat (m n : ℕ) : (binom n).eval (m : ℚ) = (m.choose n : ℚ) := by
  rw [binom_eval, Ring.choose_natCast]

theorem binom_mem (n : ℕ) : binom n ∈ Omega ℤ ℚ :=
  mem_Omega.mpr fun x => ⟨Ring.choose x n, by
    rw [binom_eval]; exact Ring.map_choose (algebraMap ℤ ℚ) x n⟩

theorem binom_linearIndependent : LinearIndependent ℤ binom := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hval : ∀ m : ℕ, (∑ k ∈ s, g k * (m.choose k : ℤ)) = 0 := by
    intro m
    have := congrArg (Polynomial.eval (m : ℚ)) hs
    simp only [eval_finsetSum, eval_smul, eval_zero, binom_eval_nat] at this
    simp only [zsmul_eq_mul] at this
    exact_mod_cast this
  have hf : (fun m : ℕ => ∑ k ∈ s, g k * (m.choose k : ℤ)) =
      ∑ k ∈ s, g k • (fun m : ℕ => (m.choose k : ℤ)) := by
    funext m; simp [Finset.sum_apply]
  have h0 : (fwdDiff 1)^[i] (fun m : ℕ => ∑ k ∈ s, g k * (m.choose k : ℤ)) 0 = 0 := by
    rw [show (fun m : ℕ => ∑ k ∈ s, g k * (m.choose k : ℤ)) = 0 from funext hval]
    simp [fwdDiff_iter_eq_sum_shift]
  rw [hf, fwdDiff_iter_finsetSum, Finset.sum_apply] at h0
  simp only [fwdDiff_iter_const_smul, Pi.smul_apply, fwdDiff_iter_choose_zero, smul_eq_mul,
    mul_ite, mul_one, mul_zero] at h0
  rwa [Finset.sum_ite_eq, ite_eq_left hi] at h0

/-- **Pólya (1919).** A polynomial of `ℚ[T]` taking integer values on `ℤ` is an
integer combination of the `binom(T, k)`, `k ≤ deg P`. -/
theorem polya {P : ℚ[X]} (hP : P ∈ Omega ℤ ℚ) :
    ∃ c : ℕ → ℤ, P = ∑ k ∈ Finset.range (P.natDegree + 1), (c k : ℚ) • binom k := by
  have hf : ∀ m : ℕ, ∃ z : ℤ, (z : ℚ) = P.eval (m : ℚ) := fun m => by
    obtain ⟨z, hz⟩ := mem_Omega.mp hP m
    exact ⟨z, by simpa using hz⟩
  choose f hf using hf
  refine ⟨fun k => (fwdDiff 1)^[k] f 0, ?_⟩
  have hcast : ∀ k, (((fwdDiff 1)^[k] f 0 : ℤ) : ℚ) = (fwdDiff 1)^[k] P.eval 0 := by
    intro k
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    push_cast
    simp [hf, zsmul_eq_mul]
  have hzero : ∀ k, P.natDegree < k → (fwdDiff 1)^[k] f 0 = 0 := fun k hk => by
    simpa [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hk] using hcast k
  have hN : ∀ m : ℕ, f m = ∑ k ∈ Finset.range (m + 1), m.choose k • (fwdDiff 1)^[k] f 0 :=
    fun m => by simpa using shift_eq_sum_fwdDiff_iter 1 f m 0
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℚ)))
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_smul, binom_eval_nat, smul_eq_mul]
  rw [← hf m, hN m]
  push_cast [nsmul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m + 1 ≤ m + P.natDegree + 1)) ?_,
    Finset.sum_subset (Finset.range_mono (by omega : P.natDegree + 1 ≤ m + P.natDegree + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by ring
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [hzero k (by omega)]
    simp
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- **Pólya's basis**: `Int(ℤ)` is the free `ℤ`-module with basis `binom(T, n)`. -/
noncomputable def polyaBasis : Module.Basis ℕ ℤ (Omega ℤ ℚ) :=
  Module.Basis.mk (v := fun n => (⟨binom n, binom_mem n⟩ : Omega ℤ ℚ))
    (LinearIndependent.of_comp (Omega ℤ ℚ).val.toLinearMap binom_linearIndependent)
    (fun P _ => by
      obtain ⟨c, hc⟩ := polya P.2
      have : P = ∑ k ∈ Finset.range ((P : ℚ[X]).natDegree + 1),
          c k • (⟨binom k, binom_mem k⟩ : Omega ℤ ℚ) := by
        refine Subtype.ext (hc.trans ?_)
        simp [Int.cast_smul_eq_zsmul]
      rw [this]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem polyaBasis_apply (n : ℕ) : (polyaBasis n : ℚ[X]) = binom n := by
  simp [polyaBasis]

instance : Module.Free ℤ (Omega ℤ ℚ) := Module.Free.of_basis polyaBasis

/-- **Vandermonde**, as an identity in `ℚ[X, Y]`:
`binom(X + Y, m) = ∑_{i + j = m} binom(X, i) binom(Y, j)`. -/
theorem vandermonde (m : ℕ) :
    coadd (binom m) = ∑ ij ∈ Finset.antidiagonal m, (binom ij.1).map C * C (binom ij.2) := by
  have h1 : coadd (binom m) = Ring.choose (X + C X : ℚ[X][X]) m := by
    simpa [coadd, binom] using
      Ring.map_choose (eval₂RingHom ((C : ℚ[X] →+* ℚ[X][X]).comp C) (X + C X)) (X : ℚ[X]) m
  rw [h1, Ring.add_choose_eq m (Commute.all _ _)]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have h2 : (binom ij.1).map C = Ring.choose (X : ℚ[X][X]) ij.1 := by
    simpa [binom] using Ring.map_choose (mapRingHom (C : ℚ →+* ℚ[X])) (X : ℚ[X]) ij.1
  have h3 : C (binom ij.2) = Ring.choose (C X : ℚ[X][X]) ij.2 := by
    simpa [binom] using Ring.map_choose (C : ℚ[X] →+* ℚ[X][X]) (X : ℚ[X]) ij.2
  rw [h2, h3]

/-- **The co-addition of `Int(ℤ)`** is `Fₘ ↦ ∑_{i+j=m} Fᵢ ⊗ Fⱼ`, and it is the only
element of `Int(ℤ) ⊗ Int(ℤ)` representing `Fₘ(X + Y)`. -/
theorem coaddition_binom (m : ℕ) (t : Omega ℤ ℚ ⊗[ℤ] Omega ℤ ℚ) :
    Phi ℤ ℚ t = coadd (binom m) ↔
      t = ∑ ij ∈ Finset.antidiagonal m, polyaBasis ij.1 ⊗ₜ polyaBasis ij.2 := by
  have h : Phi ℤ ℚ (∑ ij ∈ Finset.antidiagonal m, polyaBasis ij.1 ⊗ₜ polyaBasis ij.2) =
      coadd (binom m) := by
    rw [vandermonde, map_sum]
    simp only [Phi_tmul, polyaBasis_apply]
  exact ⟨fun ht => Phi_injective (nonZeroDivisors ℤ) (ht.trans h.symm), fun ht => ht ▸ h⟩

/-- **The co-multiplication of `Int(ℤ)`**: `Fₘ(XY) = ∑ δᵢⱼᵐ Fᵢ(X) Fⱼ(Y)` for a
unique element of `Int(ℤ) ⊗ Int(ℤ)`, i.e. unique integers `δᵢⱼᵐ`. -/
theorem comultiplication_binom (m : ℕ) : ∃! t, Phi ℤ ℚ t = comul (binom m) :=
  comultiplication_existsUnique (nonZeroDivisors ℤ) (binom_mem m)

/-- On `Int(ℤ)` the map to `Appl(ℤ, ℤ)` is injective: a polynomial of `ℚ[T]` is
determined by its values on `ℤ`. -/
theorem eq_of_comp_intCast {F G : ℚ[X]} (h : ∀ n : ℤ, F.comp (C (n : ℚ)) = G.comp (C (n : ℚ))) :
    F = G := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective
    (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ)))
  rintro _ ⟨n, rfl⟩
  have h' := h n
  rw [comp_C, comp_C] at h'
  exact C_injective h'

/-! ### Analyseurs (page 5): constants and `Ω = Ω₀ ⊕ Ω⁰` -/

/-- The composition part of the axioms 1) and 2) of page 5, on a pseudo-ring `Ω`:
`∘` associative with unit `T`, and `F ↦ F ∘ G` a morphism of pseudo-rings. The
axioms 3) are not needed below. -/
structure Composition (Ω : Type*) [NonUnitalCommRing Ω] where
  comp : Ω → Ω → Ω
  T : Ω
  comp_assoc : ∀ F G H, comp (comp F G) H = comp F (comp G H)
  T_comp : ∀ F, comp T F = F
  comp_T : ∀ F, comp F T = F
  add_comp : ∀ F F' G, comp (F + F') G = comp F G + comp F' G
  mul_comp : ∀ F F' G, comp (F * F') G = comp F G * comp F' G

namespace Composition

variable {Ω : Type*} [NonUnitalCommRing Ω] (c : Composition Ω)

/-- `F ↦ F ∘ G` as an additive map. -/
def rightComp (G : Ω) : Ω →+ Ω := AddMonoidHom.mk' (fun F => c.comp F G) fun F F' => c.add_comp F F' G

theorem zero_comp (G : Ω) : c.comp 0 G = 0 := (c.rightComp G).map_zero
theorem neg_comp (F G : Ω) : c.comp (-F) G = -c.comp F G := (c.rightComp G).map_neg F
theorem sub_comp (F F' G : Ω) : c.comp (F - F') G = c.comp F G - c.comp F' G :=
  (c.rightComp G).map_sub F F'

/-- `Ω₀`, the constants: `λ ∘ F = λ` for every `F`. -/
def constants : NonUnitalSubring Ω where
  carrier := {l | ∀ F, c.comp l F = l}
  add_mem' {a b} ha hb F := by rw [c.add_comp, ha F, hb F]
  zero_mem' F := c.zero_comp F
  mul_mem' {a b} ha hb F := by rw [c.mul_comp, ha F, hb F]
  neg_mem' {a} ha F := by rw [c.neg_comp, ha F]

theorem mem_constants {l : Ω} : l ∈ c.constants ↔ ∀ F, c.comp l F = l := Iff.rfl

/-- `Ω⁰ = {F | F ∘ 0 = 0}`. -/
def zeroPart : AddSubgroup Ω where
  carrier := {F | c.comp F 0 = 0}
  add_mem' {a b} (ha : c.comp a 0 = 0) (hb : c.comp b 0 = 0) :=
    show c.comp (a + b) 0 = 0 by rw [c.add_comp, ha, hb, add_zero]
  zero_mem' := c.zero_comp 0
  neg_mem' {a} (ha : c.comp a 0 = 0) := show c.comp (-a) 0 = 0 by rw [c.neg_comp, ha, neg_zero]

theorem mem_zeroPart {F : Ω} : F ∈ c.zeroPart ↔ c.comp F 0 = 0 := Iff.rfl

/-- `Ω⁰` is an ideal. -/
theorem mul_mem_zeroPart (G : Ω) {F : Ω} (hF : F ∈ c.zeroPart) : G * F ∈ c.zeroPart := by
  rw [mem_zeroPart, c.mul_comp, c.mem_zeroPart.mp hF, mul_zero]

/-- `F ∘ λ` is a constant when `λ` is (the action of `Ω` on `Ω₀`). -/
theorem comp_mem_constants (F : Ω) {l : Ω} (hl : l ∈ c.constants) : c.comp F l ∈ c.constants :=
  fun G => by rw [c.comp_assoc, c.mem_constants.mp hl G]

/-- **N.B. of page 5**: `F ∘ 0` is a constant. -/
theorem comp_zero_mem_constants (F : Ω) : c.comp F 0 ∈ c.constants :=
  c.comp_mem_constants F (zero_mem _)

theorem eq_zero_of_mem_constants_of_mem_zeroPart {l : Ω} (hl : l ∈ c.constants)
    (h0 : l ∈ c.zeroPart) : l = 0 := by
  rw [← c.mem_constants.mp hl 0]; exact h0

theorem sub_comp_zero_mem_zeroPart (F : Ω) : F - c.comp F 0 ∈ c.zeroPart := by
  rw [mem_zeroPart, c.sub_comp, c.mem_constants.mp (c.comp_zero_mem_constants F) 0, sub_self]

/-- **`Ω = Ω₀ ⊕ Ω⁰` (page 5)**, as abelian groups, through `F = F(0) + (F - F(0))`. -/
theorem isCompl_constants_zeroPart : IsCompl c.constants.toAddSubgroup c.zeroPart :=
  ⟨AddSubgroup.disjoint_def.mpr fun hl h0 => c.eq_zero_of_mem_constants_of_mem_zeroPart hl h0,
    codisjoint_iff_le_sup.mpr fun F _ => AddSubgroup.mem_sup.mpr ⟨c.comp F 0,
      c.comp_zero_mem_constants F, F - c.comp F 0, c.sub_comp_zero_mem_zeroPart F, add_sub_cancel _ _⟩⟩

/-- `Ω → Appl(Ω₀, Ω₀)`, `F ↦ (λ ↦ F ∘ λ)` (page 7). -/
def toAppl (F : Ω) : c.constants → c.constants := fun l => ⟨c.comp F l, c.comp_mem_constants F l.2⟩

theorem toAppl_add (F G : Ω) : c.toAppl (F + G) = c.toAppl F + c.toAppl G :=
  funext fun l => Subtype.ext (c.add_comp F G l)

theorem toAppl_mul (F G : Ω) : c.toAppl (F * G) = c.toAppl F * c.toAppl G :=
  funext fun l => Subtype.ext (c.mul_comp F G l)

theorem toAppl_comp (F G : Ω) : c.toAppl (c.comp F G) = c.toAppl F ∘ c.toAppl G :=
  funext fun l => Subtype.ext (c.comp_assoc F G l)

theorem toAppl_T : c.toAppl c.T = id := funext fun l => Subtype.ext (c.T_comp l)

/-- On the constants, `F ↦ (λ ↦ F ∘ λ)` is the identity: `λ` goes to the constant map `λ`. -/
theorem toAppl_of_mem_constants {l : Ω} (hl : l ∈ c.constants) :
    c.toAppl l = fun _ => ⟨l, hl⟩ :=
  funext fun m => Subtype.ext (c.mem_constants.mp hl m)

end Composition

/-! ### The examples of page 7 -/

/-- `Ω_A = Appl(A, A)` with the pointwise laws and composition of maps. -/
def appl (A : Type*) [NonUnitalCommRing A] : Composition (A → A) where
  comp F G := F ∘ G
  T := id
  comp_assoc _ _ _ := rfl
  T_comp _ := rfl
  comp_T _ := rfl
  add_comp _ _ _ := rfl
  mul_comp _ _ _ := rfl

theorem mem_constants_appl {A : Type*} [NonUnitalCommRing A] (l : A → A) :
    l ∈ (appl A).constants ↔ ∃ a, l = fun _ => a :=
  ⟨fun hl => ⟨l 0, funext fun x => (congr_fun (hl fun _ => 0) x).symm⟩, by
    rintro ⟨a, rfl⟩ F
    rfl⟩

/-- `(Ω_A)₀ ≃ A`. -/
def applConstantsEquiv (A : Type*) [NonUnitalCommRing A] : (appl A).constants ≃+* A where
  toFun l := l.1 0
  invFun a := ⟨fun _ => a, (mem_constants_appl _).mpr ⟨a, rfl⟩⟩
  left_inv l := Subtype.ext <| funext fun x => (congr_fun (l.2 fun _ => x) 0).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **`Appl(A, A)` does not satisfy 3a)** for `A` an infinite nonzero commutative ring:
the indicator of `0` has no finite co-addition. -/
theorem appl_not_coaddition (A : Type*) [CommRing A] [Nontrivial A] [Infinite A]
    [DecidableEq A] :
    ¬ ∃ (n : ℕ) (F' F'' : Fin n → A → A), ∀ G' G'' : A → A,
      (appl A).comp (fun x => if x = 0 then 1 else 0) (G' + G'') =
        ∑ i, (appl A).comp (F' i) G' * (appl A).comp (F'' i) G'' := by
  rintro ⟨n, F', F'', h⟩
  have key : ∀ x y : A, (if x + y = 0 then (1 : A) else 0) = ∑ i, F' i x * F'' i y := by
    intro x y
    have := congr_fun (h (fun _ => x) (fun _ => y)) 0
    simpa [appl, Finset.sum_apply] using this
  let a : Fin (n + 1) → A := fun k => Infinite.natEmbedding A k
  have ha : Function.Injective a := (Infinite.natEmbedding A).injective.comp Fin.val_injective
  let U : Matrix (Fin (n + 1)) (Fin n) A := Matrix.of fun j i => F' i (a j)
  let V : Matrix (Fin n) (Fin (n + 1)) A := Matrix.of fun i k => F'' i (-a k)
  have hUV : U * V = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [U, V, Matrix.of_apply]
    rw [← key]
    simp only [← sub_eq_add_neg, sub_eq_zero, ha.eq_iff]
  have h1 := Matrix.rank_mul_le_left U V
  rw [hUV, Matrix.rank_one, Fintype.card_fin] at h1
  have h2 := Matrix.rank_le_width U
  omega

/-- The polynomial analyseur `k[T]` (page 7). -/
noncomputable def poly (k : Type*) [CommRing k] : Composition k[X] where
  comp F G := F.comp G
  T := X
  comp_assoc F G H := Polynomial.comp_assoc F G H
  T_comp _ := X_comp
  comp_T _ := comp_X
  add_comp _ _ _ := Polynomial.add_comp
  mul_comp F F' G := Polynomial.mul_comp F F' G

/-- The constants of `k[T]` are `k`. -/
theorem mem_constants_poly {k : Type*} [CommRing k] (l : k[X]) :
    l ∈ (poly k).constants ↔ ∃ a, l = C a :=
  ⟨fun hl => ⟨l.eval 0, (hl (C 0)).symm.trans comp_C⟩, by
    rintro ⟨a, rfl⟩ F
    exact C_comp⟩

/-- **`Ω → Ω_{Ω₀}` is not injective (page 7)**: for `k` a finite field with `q`
elements, `T^q - T ≠ 0` acts as zero on every constant of `k[T]`. -/
theorem poly_toAppl_not_injective (k : Type*) [Field k] [Fintype k] :
    (X ^ Fintype.card k - X : k[X]) ≠ 0 ∧
      ∀ l ∈ (poly k).constants, (poly k).comp (X ^ Fintype.card k - X) l = 0 := by
  refine ⟨FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card, fun l hl => ?_⟩
  obtain ⟨a, rfl⟩ := (mem_constants_poly l).mp hl
  simp [poly, comp_C, FiniteField.pow_card]

/-- For `k` an infinite domain, `k[T] → Ω_{Ω₀}` is injective. -/
theorem poly_toAppl_injective (k : Type*) [CommRing k] [IsDomain k] [Infinite k] (F G : k[X])
    (h : ∀ l ∈ (poly k).constants, (poly k).comp F l = (poly k).comp G l) : F = G :=
  Polynomial.funext fun r => by
    simpa [poly, comp_C] using h (C r) ((mem_constants_poly _).mpr ⟨r, rfl⟩)

/-! ### `k[[T]]⁺` and 3a): the Pascal matrix has infinite rank -/

theorem choose_add_eq_sum (p q : ℕ) :
    (p + q).choose p = ∑ k ∈ Finset.range (p + 1), p.choose k * q.choose k := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => p.choose i * q.choose j),
    ← Finset.sum_range_reflect (fun k => p.choose k * q.choose k)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  show _ = p.choose (p + 1 - 1 - j) * q.choose (p + 1 - 1 - j)
  rw [show p + 1 - 1 - j = p - j by omega, Nat.choose_symm hj]

/-- The Pascal matrix `(binom(p + q, p))_{p, q < N}` has determinant `1`. -/
theorem pascal_det (k : Type*) [CommRing k] (N : ℕ) :
    (Matrix.of fun p q : Fin N => (((p : ℕ) + q).choose p : k)).det = 1 := by
  let L : Matrix (Fin N) (Fin N) k := Matrix.of fun p j => ((p : ℕ).choose j : k)
  have hP : (Matrix.of fun p q : Fin N => (((p : ℕ) + q).choose p : k)) = L * L.transpose := by
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, L]
    rw [choose_add_eq_sum, Nat.cast_sum,
      Fin.sum_univ_eq_sum_range (fun j => ((p : ℕ).choose j : k) * ((q : ℕ).choose j : k)) N]
    push_cast
    refine Finset.sum_subset (Finset.range_mono p.isLt) ?_
    · intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have hU : L.transpose.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [L]
    · intro i j hij
      simp [L, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
  rw [hP, Matrix.det_mul, ← Matrix.det_transpose L, hU, mul_one]

/-- **`k[[T]]⁺` does not satisfy 3a) (page 7).** The coefficients of
`F(X + Y) = ∑_{m ≥ 1} (X + Y)^m` (`F = ∑_{m ≥ 1} T^m`) are `binom(p + q, p)` off
`(0, 0)` and `0` at `(0, 0)`; they are not those of a finite sum `∑ᵢ aᵢ(X) bᵢ(Y)`,
whose coefficients are `∑ᵢ aᵢ,ₚ bᵢ,q`. -/
theorem geom_not_finite_coaddition (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ)
    (a b : Fin n → ℕ → k) :
    ¬ ∀ p q : ℕ, (if p = 0 ∧ q = 0 then 0 else ((p + q).choose p : k)) = ∑ i, a i p * b i q := by
  intro h
  let U : Matrix (Fin (n + 2)) (Option (Fin n)) k :=
    Matrix.of fun p i => i.elim (if (p : ℕ) = 0 then 1 else 0) (fun i => a i p)
  let V : Matrix (Option (Fin n)) (Fin (n + 2)) k :=
    Matrix.of fun i q => i.elim (if (q : ℕ) = 0 then 1 else 0) (fun i => b i q)
  have hUV : (Matrix.of fun p q : Fin (n + 2) => (((p : ℕ) + q).choose p : k)) = U * V := by
    ext p q
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.of_apply, U, V, Option.elim]
    rw [← h]
    by_cases hp : (p : ℕ) = 0 <;> by_cases hq : (q : ℕ) = 0 <;> simp [hp, hq]
  have hunit : IsUnit (Matrix.of fun p q : Fin (n + 2) => (((p : ℕ) + q).choose p : k)) := by
    rw [Matrix.isUnit_iff_isUnit_det, pascal_det]
    exact isUnit_one
  have h1 := Matrix.rank_of_isUnit _ hunit
  have h2 := (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  rw [← hUV, h1] at h2
  simp at h2

end Grothendieck.Folder153
