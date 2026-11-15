module

public import Mathlib
public import Grothendieck.Folder11
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalExpansion

@[expose] public section


/-!
# Folder 11 (pages 33, 37, 41): push-forwards into a graded algebra with a diagonal class

`Grothendieck/Folder11.lean` proves the equivalence of pages 37 and 41 (special simplicial
bivariant algebras ≃ Poincaré algebras) in the commutative case only, and leaves out the graded
case with Koszul signs and p. 41's full faithfulness of `A ↦ (A(pt), Δ)`, whose axioms on `Δ`
the page does not write. The step of the commutative proof that carries full faithfulness is
page 33's: into a Poincaré algebra, the push-forward of a morphism `(f_*, f^*)` is the adjoint
of its pull-back (`Folder11.Simplicial.adj`, `adj_unique`), so a morphism is determined by its
pull-back and every pull-back has one.

This file proves that step in the graded case, with the signs, for an algebra whose duality is
given by a diagonal class `Δ` rather than assumed. The vendored AxiomMath/Stacks file
`StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/DiagonalExpansion.lean` (the algebra
of the proofs of Stacks Lemma 0FIJ and Remark 0FIK) packages, in
`Stacks.WeilCohomology.DiagonalExpansion.DiagonalData`, a `ℤ`-graded graded-commutative
algebra `A` with `A ⊗ A ≅ B` by Künneth, a class `Δ = κ(∑ e_t ⊗ f_t) ∈ B^n`, `n` even, with
`Δ · p₁ a = Δ · p₂ a`, and a gauge `λ` vanishing outside degree `n` with `∑ λ(f_t) e_t = 1`.
These two conditions on `Δ` are candidate axioms for the page's `Δ`; from them the library
proves that `λ(y x)` is a perfect pairing in complementary degrees
(`isPerfPair_tracePairing`) and that `λ` is the only gauge so normalised (`trace_unique`).

**What is proved**, for `hD : DiagonalData 𝒜 ℬ p₁ p₂ n Δ λ l`, any `F`-algebra `E` (no grading
needed) with a linear form `κ_E`, and any algebra map `h : A → E` (the pull-back `f^*`):
* `trace_mul_decompose`, `eq_zero_of_forall_trace_mul`: `λ(y x)` is nondegenerate on the whole
  of `A`, not only between homogeneous pieces;
* `push`, `trace_mul_push`: the push-forward `h_* x = ∑_t (-1)^{a_t} κ_E(h(e_t) x) f_t`, with
  `e_t ∈ A^{a_t}`, satisfies `λ(y · h_* x) = κ_E(h(y) · x)` for all `y`; the sign
  `(-1)^{a_t}` is the Koszul sign that the commutative case does not see;
* `push_proj`, `push_gauge`: it satisfies the projection formula `h_*(h(y) x) = y h_*(x)` and
  `λ ∘ h_* = κ_E`, so `(h_*, h)` is a morphism of gauged algebras of page 33;
* `push_unique` (**a morphism into `A` is determined by its pull-back**): any linear
  `f : E → A` with the projection formula and `λ ∘ f = κ_E` is `h_*`;
* `gauge_unique`: the gauge of `A` is determined by `Δ` (Remark 0FIK, from `trace_unique`).

Not formalised: the graded simplicial bivariant algebras themselves (tensor powers of graded
algebras with Koszul signs, the Künneth isomorphisms `A(I) ⊗ A(pt) ≅ A(I ⊔ pt)`), hence the
graded equivalence of pages 37 and 41, and p. 41's full faithfulness of `A ↦ (A(pt), Δ)`
as a functor: the axioms above are offered for its `Δ`, not read on the page.
-/

namespace Grothendieck.Folder11.GradedPoincare

open DirectSum Stacks.WeilCohomology.DiagonalExpansion

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  {𝒜 : ℤ → Submodule F A} [GradedAlgebra 𝒜] {ℬ : ℤ → Submodule F B}
  {p₁ p₂ : A →ₐ[F] B} {n : ℤ} {η : B} {lam : A →ₗ[F] F} {l : List (ℤ × A × A)}
  {E : Type*} [Ring E] [Algebra F E]

/-- Against `y ∈ A^j`, the trace only sees the component of degree `n - j`. -/
theorem trace_mul_decompose (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {j : ℤ} {y : A}
    (hy : y ∈ 𝒜 j) (z : A) : lam (y * z) = lam (y * (decompose 𝒜 z (n - j) : A)) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 z]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_eq_single (n - j) (fun i _ hi => ?_) (fun h => ?_)
  · exact hD.trace_eq_zero (j + i) (by omega) _
      (SetLike.GradedMul.mul_mem hy (decompose 𝒜 z i).2)
  · rw [DFinsupp.notMem_support_iff.1 h]
    simp

/-- **Nondegeneracy on the whole algebra**: if `λ(y z) = 0` for all `y`, then `z = 0`. -/
theorem eq_zero_of_forall_trace_mul (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {z : A}
    (h : ∀ y, lam (y * z) = 0) : z = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Finset.sum_eq_zero fun i _ => ?_
  refine eq_zero_of_trace_mul hD (i := i) (j := n - i) (by omega) (decompose 𝒜 z i).2
    fun y hy => ?_
  have := trace_mul_decompose hD hy z
  rw [show n - (n - i) = i by omega] at this
  rw [← this, h]

/-- Two elements with the same pairings against all of `A` are equal. -/
theorem eq_of_forall_trace_mul (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {z z' : A}
    (h : ∀ y, lam (y * z) = lam (y * z')) : z = z' :=
  sub_eq_zero.1 (eq_zero_of_forall_trace_mul hD fun y => by rw [mul_sub, map_sub, h, sub_self])

/-- The sign `(-1)^a` in `F`. -/
def sgn (a : ℤ) : F := ((Int.negOnePow a : ℤ) : F)

variable (l) in
/-- The push-forward along `h : A → E` into `A`, read off the diagonal class:
`h_* x = ∑_t (-1)^{a_t} κ_E(h(e_t) x) f_t`. -/
def push (κE : E →ₗ[F] F) (h : A →ₐ[F] E) : E →ₗ[F] A where
  toFun x := (l.map fun t => (sgn t.1 * κE (h t.2.1 * x)) • t.2.2).sum
  map_add' x x' := by
    simp only [mul_add, map_add, add_smul, List.sum_map_add]
  map_smul' c x := by
    simp only [mul_smul_comm, map_smul, smul_eq_mul, RingHom.id_apply, List.smul_sum,
      List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, smul_smul]
    ring_nf

theorem push_apply (κE : E →ₗ[F] F) (h : A →ₐ[F] E) (x : E) :
    push l κE h x = (l.map fun t => (sgn t.1 * κE (h t.2.1 * x)) • t.2.2).sum := rfl

omit [GradedAlgebra 𝒜] in
/-- The Koszul sign: for `y ∈ A^j` and `f ∈ A^{n - j}`, `n` even,
`(-1)^j λ(y f) = λ(f y)`. -/
theorem sgn_mul_trace (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {j : ℤ} {y f : A}
    (hy : y ∈ 𝒜 j) (hf : f ∈ 𝒜 (n - j)) : sgn j * lam (y * f) = lam (f * y) := by
  rw [hD.graded_comm_left _ _ _ _ hy hf, map_zsmul, zsmul_eq_mul, ← mul_assoc, sgn,
    ← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add]
  have hev : Even (j + j * (n - j)) := by
    obtain ⟨m, hm⟩ := hD.even
    have h2 : Even (j * (j - 1)) := Int.even_mul_pred_self j
    obtain ⟨r, hr⟩ := h2
    exact ⟨j * m - r, by rw [hm] at *; linear_combination (-1 : ℤ) * hr⟩
  rw [Int.negOnePow_even _ hev]
  simp

/-- **The push-forward is adjoint to the pull-back**: `λ(y · h_* x) = κ_E(h(y) · x)`. -/
theorem trace_mul_push (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) (κE : E →ₗ[F] F)
    (h : A →ₐ[F] E) (x : E) (y : A) : lam (y * push l κE h x) = κE (h y * x) := by
  induction y using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add y y' hy hy' => rw [add_mul, map_add, hy, hy', map_add, add_mul, map_add]
  | @homogeneous j y =>
    obtain ⟨y, hy⟩ := y
    change lam (y * push l κE h x) = κE (h y * x)
    have lhs : lam (y * push l κE h x) =
        (l.map fun t => sgn t.1 * κE (h t.2.1 * x) * lam (y * t.2.2)).sum := by
      rw [push_apply, ← List.sum_map_mul_left, map_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, mul_smul_comm, map_smul, smul_eq_mul]
    have rhs : κE (h y * x) = (l.map fun t => lam (t.2.2 * y) * κE (h t.2.1 * x)).sum := by
      conv_lhs => rw [← sum_trace_mul_smul hD y]
      rw [map_list_sum, List.map_map, ← List.sum_map_mul_right, map_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, map_smul, smul_mul_assoc, smul_eq_mul]
    rw [lhs, rhs]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨he, hf⟩ := hD.homogeneous t ht
    by_cases htj : t.1 = j
    · rw [htj] at hf ⊢
      rw [← sgn_mul_trace hD hy hf]
      ring
    · rw [hD.trace_eq_zero (j + (n - t.1)) (by omega) _ (SetLike.GradedMul.mul_mem hy hf),
        hD.trace_eq_zero (n - t.1 + j) (by omega) _ (SetLike.GradedMul.mul_mem hf hy)]
      ring

/-- The projection formula `h_*(h(y) x) = y h_*(x)`. -/
theorem push_proj (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) (κE : E →ₗ[F] F) (h : A →ₐ[F] E)
    (y : A) (x : E) : push l κE h (h y * x) = y * push l κE h x :=
  eq_of_forall_trace_mul hD fun z => by
    rw [trace_mul_push hD, ← mul_assoc, ← map_mul, ← mul_assoc, trace_mul_push hD]

/-- `λ ∘ h_* = κ_E`. -/
theorem push_gauge (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) (κE : E →ₗ[F] F) (h : A →ₐ[F] E)
    (x : E) : lam (push l κE h x) = κE x := by
  simpa using trace_mul_push hD κE h x 1

/-- **A morphism of gauged algebras into `A` is determined by its pull-back.** Any linear
`f : E → A` with the projection formula and `λ ∘ f = κ_E` is the push-forward `h_*`. -/
theorem push_unique (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) (κE : E →ₗ[F] F) (h : A →ₐ[F] E)
    (f : E →ₗ[F] A) (proj : ∀ y x, f (h y * x) = y * f x) (gauge : ∀ x, lam (f x) = κE x) :
    f = push l κE h :=
  LinearMap.ext fun x => eq_of_forall_trace_mul hD fun y => by
    rw [trace_mul_push hD, ← proj, gauge]

/-- **The gauge is determined by the diagonal class** (Remark 0FIK): a linear form vanishing
outside degree `n` and normalised by `∑ λ'(f_t) e_t = 1` is `λ`. -/
theorem gauge_unique (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {lam' : A →ₗ[F] F}
    (h0 : ∀ i, i ≠ n → ∀ x ∈ 𝒜 i, lam' x = 0)
    (h1 : (l.map fun t => lam' t.2.2 • t.2.1).sum = 1) : lam' = lam :=
  trace_unique hD h0 h1

end Grothendieck.Folder11.GradedPoincare
