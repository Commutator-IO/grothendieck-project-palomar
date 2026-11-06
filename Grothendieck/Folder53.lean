module

public import Mathlib

@[expose] public section


/-!
# Folder 53, page 21: a cancellative algebraic monoid is a group

Page 21 of folder 53 opens with a « Rectification »: an affine monoid of finite type over a
field embeds as a closed submonoid of `M_n`, not of `GL_n`, « car on peut montrer que si `G`
est un monoïde de prés. finie sur un anneau `k`, tel que les translations à g (à dr.) sont
[illisible] [illisible] — p.ex. s'il ∃ mon. `G → G'`, `G'` un groupe — alors `G` est un objet
gr.-pr. » (transcription `transcripts/53/batch-02.fr.tex`, with « sont », « mon. » and
« gr.-pr. » uncertain). The modernised reading `transcripts/53/53.modern.tex` supplies
« monomorphismes » for the illegible words and the proof by Ax–Grothendieck; both are the
edition's reconstruction, not the page's. The statement over an algebraically closed field is
classical (Putcha, *Linear algebraic monoids*, 1988; Brion's survey, 2014).

This file proves the case of `K`-points, `K` algebraically closed, by the route the reading
proposes: a left translation is an injective polynomial self-map of a Zariski-closed set,
hence surjective by Ax–Grothendieck (`MvPolynomial.ax_grothendieck_zeroLocus`).

What is modelled. A *monoid of `K`-points with a polynomial law* is a monoid `M` with an
injective map `φ : M → (ι → K)` (`ι` finite) whose image is the zero locus of an ideal of
`K[X_i]`, and polynomials `m i` in two sets of variables with `φ (x * y) = law m (φ x) (φ y)`.
* `law`, `translation`, `eval_translation`: the law and its left translations as polynomials;
* `isUnit_of_isLeftCancelMul`: in such a monoid, if left multiplications are injective, every
  element is a unit (only left cancellation is used);
* `inv_mem_of_isClosed`: a submonoid of `GL_n(K)` which is closed in `GL_n` — cut out by
  polynomials in the entries and in `det⁻¹` — is a subgroup (the special case on page 21:
  a closed submonoid of `GL_n` is a group, the reason for `M_n`).

Not formalised: monoid schemes over a ring, scheme-theoretic monomorphisms, finite
presentation (the page's generality), and the embedding into `M_n` of page 30.
-/

open MvPolynomial

namespace Grothendieck.Folder53

variable {K ι : Type*} [Field K]

/-- The polynomial law: `law m a v i = m i (a, v)`, the variables `inl j` for `a`, `inr j`
for `v`. -/
noncomputable def law (m : ι → MvPolynomial (ι ⊕ ι) K) (a v : ι → K) : ι → K :=
  fun i => eval (Sum.elim a v) (m i)

/-- The left translation `v ↦ law m a v`, as polynomials in `v`. -/
noncomputable def translation (m : ι → MvPolynomial (ι ⊕ ι) K) (a : ι → K) :
    ι → MvPolynomial ι K :=
  fun i => bind₁ (Sum.elim (fun j => C (a j)) X) (m i)

theorem eval_translation (m : ι → MvPolynomial (ι ⊕ ι) K) (a : ι → K) :
    (fun v i => eval v (translation m a i)) = law m a := by
  funext v i
  simp only [translation, law, eval, eval₂Hom_bind₁]
  congr 2
  funext j
  cases j <;> simp

variable [IsAlgClosed K] [Finite ι]

/-- A monoid of `K`-points of an affine variety with a polynomial law, whose left translations
are injective, is a group (the reading of folder 53, page 21, over an algebraically closed
field). -/
theorem isUnit_of_isLeftCancelMul {M : Type*} [Monoid M] [IsLeftCancelMul M]
    (φ : M → ι → K) (hφ : Function.Injective φ) (I : Ideal (MvPolynomial ι K))
    (hI : Set.range φ = zeroLocus K I) (m : ι → MvPolynomial (ι ⊕ ι) K)
    (hm : ∀ x y, φ (x * y) = law m (φ x) (φ y)) (x : M) : IsUnit x := by
  have key := ax_grothendieck_zeroLocus I (translation m (φ x))
  rw [eval_translation, ← hI] at key
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := key (by rintro _ ⟨y, rfl⟩; exact ⟨x * y, hm x y⟩)
    (by rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ h; rw [← hm, ← hm] at h; rw [mul_left_cancel (hφ h)])
    ⟨1, rfl⟩
  have hxy : x * y = 1 := hφ (by rw [hm, hy])
  exact ⟨⟨x, y, hxy, mul_left_cancel (a := x) (by rw [← mul_assoc, hxy, one_mul, mul_one])⟩, rfl⟩

/-- The determinant of the generic matrix `(X (some (i, j)))`. -/
noncomputable def detPoly (n : ℕ) : MvPolynomial (Option (Fin n × Fin n)) K :=
  (Matrix.of fun i j => X (some (i, j))).det

/-- Coordinates on `GL_n(K)`: the entries and `det⁻¹`. -/
def glCoords {n : ℕ} (g : GL (Fin n) K) : Option (Fin n × Fin n) → K
  | none => (g⁻¹ : GL (Fin n) K).val.det
  | some ij => g.val ij.1 ij.2

/-- The matrix with entries `v (some (i, j))`. -/
def entries {n : ℕ} (v : Option (Fin n × Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => v (some (i, j))

omit [IsAlgClosed K] in
theorem eval_detPoly {n : ℕ} (v : Option (Fin n × Fin n) → K) :
    eval v (detPoly n) = (entries v).det := by
  rw [detPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [entries]

/-- Matrix multiplication on the coordinates `(A, t)`, `t = det A⁻¹`: `(A, t)(B, s) = (AB, ts)`. -/
noncomputable def glLaw (n : ℕ) :
    Option (Fin n × Fin n) → MvPolynomial (Option (Fin n × Fin n) ⊕ Option (Fin n × Fin n)) K
  | none => X (Sum.inl none) * X (Sum.inr none)
  | some (i, j) => ∑ k, X (Sum.inl (some (i, k))) * X (Sum.inr (some (k, j)))

/-- A submonoid of `GL_n(K)`, `K` algebraically closed, which is Zariski-closed in `GL_n`
(cut out by polynomials in the entries and `det⁻¹`) is a subgroup: the special case of
page 21 of folder 53 behind the rectification `GL_n ↦ M_n`. -/
theorem inv_mem_of_isClosed {n : ℕ} (S : Submonoid (GL (Fin n) K))
    (J : Ideal (MvPolynomial (Option (Fin n × Fin n)) K))
    (hS : ∀ g, g ∈ S ↔ glCoords g ∈ zeroLocus K J) {g : GL (Fin n) K} (hg : g ∈ S) :
    g⁻¹ ∈ S := by
  have hinj : Function.Injective fun x : S => glCoords x.1 := fun x y h =>
    Subtype.ext <| Units.ext <| Matrix.ext fun i j => congrFun h (some (i, j))
  have hrange : Set.range (fun x : S => glCoords x.1) =
      zeroLocus K (J ⊔ Ideal.span {X none * detPoly n - 1}) := by
    ext v
    simp only [Set.mem_range, mem_zeroLocus_iff, Submodule.mem_sup, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, rfl⟩ p ⟨a, ha, _, ⟨c, rfl⟩, rfl⟩
      have h1 : eval (glCoords x.1) a = 0 := by simpa using mem_zeroLocus_iff.1 ((hS x).1 x.2) a ha
      simp only [aeval_eq_eval, map_add, h1, map_mul, map_sub, eval_X, glCoords,
        Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', eval_detPoly, entries,
        map_one, zero_add, mul_eq_zero]
      exact .inl (sub_eq_zero.2 (inv_mul_cancel₀ (Matrix.isUnits_det_units x.1).ne_zero))
    · intro hv
      have hdet : v none * (entries v).det = 1 := by
        simpa [eval_detPoly, sub_eq_zero] using hv _ ⟨0, zero_mem _, _, dvd_rfl, zero_add _⟩
      let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (entries v)
        (right_ne_zero_of_mul_eq_one hdet)
      have hc : glCoords g = v := by
        ext (_ | ⟨i, j⟩)
        · simp [glCoords, g, Matrix.coe_units_inv, eq_inv_of_mul_eq_one_left hdet]
        · rfl
      exact ⟨⟨g, (hS g).2 (hc ▸ fun p hp => hv p ⟨p, hp, 0, dvd_zero _, add_zero p⟩)⟩, hc⟩
  have hm (x y : S) : glCoords (x * y).1 = law (glLaw n) (glCoords x.1) (glCoords y.1) := by
    ext (_ | ⟨i, j⟩)
    · simp [glCoords, law, glLaw, mul_comm]
    · simp [glCoords, law, glLaw, Matrix.mul_apply]
  obtain ⟨u, hu⟩ := isUnit_of_isLeftCancelMul _ hinj _ hrange _ hm ⟨g, hg⟩
  have h1 := congrArg Subtype.val u.mul_inv
  simp only [Submonoid.coe_mul, hu, Submonoid.coe_one] at h1
  rw [inv_eq_of_mul_eq_one_right h1]
  exact (↑u⁻¹ : S).2

end Grothendieck.Folder53

/-!
# Folder 53, page 9: the criterion of geometric irreducibility (the Galois argument)

Page 9 (« Rectificatif sur critère d'irréductibilité géom. », `transcripts/53/53.modern.tex`):
let `X` be an irreducible `k`-scheme (the hypothesis is the edition's) and `f : Z → X` with
a) `Z` geometrically irreducible, b) `f(Z)` not contained in the locus of points through which
several irreducible components of `X_k̄` pass. Then `X` is geometrically irreducible. The proof:
for `k'/k` finite Galois, a component `X'ᵢ` of `X' = X_{k'}` containing the irreducible
`G`-stable set `f'(Z')` is fixed by `G = Gal(k'/k)` by b), hence is the inverse image of
`p(X'ᵢ) = X`, so `X' = X'ᵢ`; radicial extensions do not change the topology.

What is proved.
* `irreducibleSpace_of_stable`, `irreducibleSpace_of_map`: the Galois step, for any closed
  generalizing map `p : X' → X` of sober spaces, `X` irreducible, with a group acting on `X'`
  by homeomorphisms transitively on the fibres of `p`. The page's « `p(X'ᵢ) = X` since `p` is
  open and closed » is done by lifting the generic point of `X` (flatness: `p` generalizing).
* `isPrime_span_sumSq_real`, `not_irreducibleSpace_complex`: the page's counterexample when b)
  is dropped: `ℝ[x,y]/(x² + y²)` is a domain (via `x ↦ t`, `y ↦ i t` into `ℂ[t]`), while
  `Spec ℂ[x,y]/(x² + y²)` is not irreducible: `(x + iy)(x - iy) = x² + y²` and neither factor
  is nilpotent (evaluate at `(1, ∓i)`). `Z = Spec ℝ` maps to the origin, where both lines meet.

Not formalised: the scheme-level statement with Mathlib's
`AlgebraicGeometry.GeometricallyIrreducible` (the action of `Gal(k'/k)` on `X_{k'}` and its
transitivity on fibres, the reduction from all fields `K ⊇ k` to finite Galois extensions of
`k`, and the radicial step), the identification of `ℂ ⊗_ℝ ℝ[x,y]/(x² + y²)` with
`ℂ[x,y]/(x² + y²)`, and the sufficient condition by a geometrically normal point of `X_red`.
-/

open Pointwise

namespace Grothendieck.Folder53

section GaloisStep

variable {X' X G : Type*} [TopologicalSpace X'] [TopologicalSpace X] [Group G] [MulAction G X']
  [ContinuousConstSMul G X']

/-- A homeomorphism `x ↦ g • x` permutes the irreducible components. -/
theorem smul_mem_irreducibleComponents {C : Set X'} (hC : C ∈ irreducibleComponents X') (g : G) :
    g • C ∈ irreducibleComponents X' := by
  have key : ∀ (h : G) {C : Set X'}, C ∈ irreducibleComponents X' →
      ∀ D, IsIrreducible D → h • C ⊆ D → D ⊆ h • C := by
    intro h C hC D hD hCD
    have h1 : IsIrreducible (h⁻¹ • D) := by
      rw [← Set.image_smul]; exact hD.image _ (continuous_const_smul _).continuousOn
    have h2 : C ⊆ h⁻¹ • D := by
      intro x hx
      exact Set.mem_smul_set.2 ⟨h • x, hCD (Set.smul_mem_smul_set hx), by simp⟩
    have h3 := hC.2 h1 h2
    intro y hy
    exact Set.mem_smul_set.2 ⟨h⁻¹ • y, h3 (Set.smul_mem_smul_set hy), by simp⟩
  refine ⟨?_, fun D hD hle => key g hC D hD hle⟩
  rw [← Set.image_smul]; exact hC.1.image _ (continuous_const_smul _).continuousOn


/-- The Galois argument of folder 53, page 9, in topological form. Let `p : X' → X` be closed and
generalizing (as `X_{k'} → X` is, finite and flat, for `k'/k` finite), with `X` irreducible,
`X'` and `X` sober, and let a group `G` act on `X'` by homeomorphisms, transitively on the
fibres of `p` (as `Gal(k'/k)` does). If an irreducible `G`-stable set `S` (the image of `Z_{k'}`)
contains a point `s` through which only one irreducible component of `X'` passes, then `X'` is
irreducible. -/
theorem irreducibleSpace_of_stable [QuasiSober X'] [QuasiSober X] [IrreducibleSpace X]
    (p : X' → X) (hpc : IsClosedMap p) (hpg : GeneralizingMap p)
    (horb : ∀ x y, p x = p y → ∃ g : G, g • x = y)
    {S : Set X'} (hS : IsIrreducible S) (hSG : ∀ g : G, g • S ⊆ S) {s : X'} (hs : s ∈ S)
    (huniq : ∀ C ∈ irreducibleComponents X', ∀ D ∈ irreducibleComponents X',
      s ∈ C → s ∈ D → C = D) :
    IrreducibleSpace X' := by
  obtain ⟨C, hC, hSC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible S hS
  -- every Galois conjugate of `C` passes through `s`, hence equals `C`
  have hstab : ∀ g : G, g • C = C := by
    intro g
    refine huniq _ (smul_mem_irreducibleComponents hC g) _ hC ?_ (hSC hs)
    exact Set.mem_smul_set.2 ⟨g⁻¹ • s, hSC (hSG g⁻¹ (Set.smul_mem_smul_set hs)), by simp⟩
  -- so `C` is saturated for `p`
  have hsat : ∀ x y, x ∈ C → p x = p y → y ∈ C := by
    intro x y hx hxy
    obtain ⟨g, rfl⟩ := horb x y hxy
    rw [← hstab g]; exact Set.smul_mem_smul_set hx
  -- `p (C)` contains the generic point of `X`
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨c, hc⟩ := QuasiSober.sober hC.1 hCc
  obtain ⟨η, hη⟩ := QuasiSober.sober (IrreducibleSpace.isIrreducible_univ X) isClosed_univ
  obtain ⟨x, hxc, rfl⟩ := hpg (hη.specializes (Set.mem_univ (p c)))
  have hxC : x ∈ C := by
    have h2 : C ⊆ closure {x} := by
      rw [← hc.def]; exact closure_minimal (Set.singleton_subset_iff.2
        (specializes_iff_mem_closure.1 hxc)) isClosed_closure
    exact hC.2 isIrreducible_singleton.closure h2 (subset_closure rfl)
  have himg : p '' C = Set.univ := by
    have := (hpc C hCc).closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨x, hxC, rfl⟩)
    rw [hη.def] at this
    exact Set.univ_subset_iff.1 this
  have hCuniv : C = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz, hzy⟩ : p y ∈ p '' C := himg ▸ Set.mem_univ _
    exact hsat z y hz hzy
  rw [irreducibleSpace_def]; exact (hCuniv ▸ hC.1 : IsIrreducible (Set.univ : Set X'))

/-- The same, with `S` the image of an irreducible space `Z'` (the base change `Z_{k'}` of a
geometrically irreducible `Z`), stable under `G`, and one point `f' z` of the image lying on a
single irreducible component: the form of hypotheses a) and b) of page 9. -/
theorem irreducibleSpace_of_map [QuasiSober X'] [QuasiSober X] [IrreducibleSpace X]
    {Z' : Type*} [TopologicalSpace Z'] [IrreducibleSpace Z'] (p : X' → X) (hpc : IsClosedMap p)
    (hpg : GeneralizingMap p) (horb : ∀ x y, p x = p y → ∃ g : G, g • x = y)
    (f' : Z' → X') (hf' : Continuous f') (hG : ∀ (g : G) z, ∃ z', f' z' = g • f' z) (z : Z')
    (huniq : ∀ C ∈ irreducibleComponents X', ∀ D ∈ irreducibleComponents X',
      f' z ∈ C → f' z ∈ D → C = D) :
    IrreducibleSpace X' := by
  refine irreducibleSpace_of_stable p hpc hpg horb
    ((IrreducibleSpace.isIrreducible_univ Z').image f' hf'.continuousOn) ?_
    (s := f' z) ⟨z, trivial, rfl⟩ huniq
  rintro g _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
  exact (hG g w).imp fun _ h => ⟨trivial, h⟩


end GaloisStep

section Counterexample

open Complex
open scoped Polynomial

/-- `x² + y²` in `R[x][y]`: the inner variable is `x = C X`, the outer one `y = X`. -/
noncomputable def sumSq (R : Type*) [CommRing R] : R[X][X] :=
  Polynomial.X ^ 2 + Polynomial.C (Polynomial.X ^ 2)

/-- `x ↦ t`, `y ↦ i t`: `ℝ[x][y] → ℂ[t]`, which kills `x² + y²`. -/
noncomputable def toLines : ℝ[X][X] →+* ℂ[X] :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom (algebraMap ℝ ℂ))
    (Polynomial.C I * Polynomial.X)

/-- `toLines` kills `x² + y²`. -/
theorem toLines_sumSq : toLines (sumSq ℝ) = 0 := by
  rw [sumSq, toLines, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_C, mul_pow, ← Polynomial.C_pow, I_sq]
  simp

/-- `toLines` followed by `t ↦ t₀`, `t₀` real, is evaluation at `(t₀, i t₀)`. -/
theorem eval_toLines (t : ℝ) (f : ℝ[X][X]) :
    (toLines f).eval (t : ℂ) =
      f.eval₂ ((algebraMap ℝ ℂ).comp (Polynomial.evalRingHom t)) (I * t) := by
  have : (Polynomial.evalRingHom (t : ℂ)).comp toLines =
      Polynomial.eval₂RingHom ((algebraMap ℝ ℂ).comp (Polynomial.evalRingHom t)) (I * t) := by
    apply Polynomial.ringHom_ext
    · intro a; simpa [toLines, Polynomial.eval_map_algebraMap] using
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) t a
    · simp [toLines]
  exact congrArg (fun φ : ℝ[X][X] →+* ℂ => φ f) this

/-- `x² + y²` is monic in `y`. -/
theorem monic_sumSq (R : Type*) [CommRing R] [Nontrivial R] : (sumSq R).Monic :=
  Polynomial.monic_X_pow_add_C _ two_ne_zero

/-- The kernel of `x ↦ t, y ↦ i t` is exactly `(x² + y²)`: divide by `y² + x²`, monic in `y`;
the remainder `a(x) + b(x) y` goes to `a(t) + i t b(t)`, zero only if `a = b = 0`. -/
theorem ker_toLines : RingHom.ker toLines = Ideal.span {sumSq ℝ} := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    set r := f %ₘ sumSq ℝ with hr
    have hdeg : r.degree ≤ 1 := Order.le_of_lt_succ
      ((Polynomial.degree_modByMonic_lt f (monic_sumSq ℝ)).trans_eq
        (Polynomial.degree_X_pow_add_C two_pos _))
    have hrf : toLines r = 0 := by
      rwa [← Polynomial.modByMonic_add_div f (sumSq ℝ), map_add, map_mul, toLines_sumSq,
        zero_mul, add_zero] at hf
    have hreq := Polynomial.eq_X_add_C_of_degree_le_one hdeg
    have hev : ∀ t : ℝ, (r.coeff 0).eval t = 0 ∧ t * (r.coeff 1).eval t = 0 := by
      intro t
      have := congrArg (Polynomial.eval (t : ℂ)) hrf
      rw [eval_toLines, hreq] at this
      simp [Complex.ext_iff] at this
      exact ⟨this.1, mul_eq_zero.2 this.2.symm⟩
    have h0 : r.coeff 0 = 0 := Polynomial.funext fun t => by simpa using (hev t).1
    have h1 : Polynomial.X * r.coeff 1 = 0 := Polynomial.funext fun t => by simpa using (hev t).2
    have h1' : r.coeff 1 = 0 := (mul_eq_zero.1 h1).resolve_left Polynomial.X_ne_zero
    rw [Ideal.mem_span_singleton]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (monic_sumSq ℝ)).1 (by rw [← hr, hreq, h0, h1']; simp)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact toLines_sumSq

/-- `ℝ[x, y] / (x² + y²)` is a domain: `X = Spec ℝ[x,y]/(x² + y²)` is irreducible. -/
theorem isPrime_span_sumSq_real : (Ideal.span {sumSq ℝ}).IsPrime :=
  ker_toLines ▸ RingHom.ker_isPrime toLines

/-- Evaluation at `(x, y) = (a, b)` of `ℂ[x][y]`. -/
noncomputable def evalAt (a b : ℂ) : ℂ[X][X] →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom a) b

/-- Evaluation at a point of the cone `x² + y² = 0` kills `x² + y²`. -/
theorem evalAt_sumSq {a b : ℂ} (h : b ^ 2 + a ^ 2 = 0) : evalAt a b (sumSq ℂ) = 0 := by
  rw [evalAt, sumSq, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C]
  simpa using h

/-- Over `ℂ`, `x² + y² = (x + iy)(x - iy)` and neither factor is nilpotent modulo `x² + y²`:
`Spec ℂ[x,y]/(x² + y²)`, the base change of `X` to `ℂ`, is not irreducible. -/
theorem not_irreducibleSpace_complex :
    ¬ IrreducibleSpace (PrimeSpectrum (ℂ[X][X] ⧸ Ideal.span {sumSq ℂ})) := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  intro hprime
  set q := Ideal.span {sumSq ℂ}
  have hnil : ∀ a b : ℂ, b ^ 2 + a ^ 2 = 0 → ∀ u : ℂ[X][X],
      Ideal.Quotient.mk q u ∈ nilradical _ → evalAt a b u = 0 := by
    intro a b hab u hu
    let e : ℂ[X][X] ⧸ q →+* ℂ := Ideal.Quotient.lift q (evalAt a b) fun v hv => by
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hv
      rw [map_mul, evalAt_sumSq hab, mul_zero]
    obtain ⟨n, hn⟩ := hu
    have := congrArg e hn
    rw [map_pow, map_zero] at this
    simpa [e] using pow_eq_zero_iff'.mp this |>.1
  -- `x + iy` and `x - iy`, with `x = C X` and `y = X`
  have hprod :
      Ideal.Quotient.mk q
          (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C I) * Polynomial.X) *
        Ideal.Quotient.mk q
          (Polynomial.C Polynomial.X - Polynomial.C (Polynomial.C I) * Polynomial.X)
      ∈ nilradical _ := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.2 ?_]
    · exact zero_mem _
    · refine Ideal.mem_span_singleton.2 ⟨1, ?_⟩
      have hI : (Polynomial.C (Polynomial.C I) ^ 2 : ℂ[X][X]) = -1 := by
        rw [← Polynomial.C_pow, ← Polynomial.C_pow, I_sq]; simp
      simp only [sumSq, mul_one, Polynomial.C_pow]
      linear_combination (-(Polynomial.X : ℂ[X][X]) ^ 2) * hI
  rcases hprime.mem_or_mem hprod with h | h
  · have := hnil 1 (-I) (by simp) _ h
    norm_num [evalAt] at this
  · have := hnil 1 I (by simp) _ h
    norm_num [evalAt] at this

end Counterexample

end Grothendieck.Folder53

/-!
# Folder 53, page 9: the counterexample at scheme level

The base change `ℂ ⊗_ℝ ℝ[x,y]/(x² + y²)` is identified with `ℂ[x,y]/(x² + y²)`
(`baseChangeEquiv`: `ℂ ⊗_ℝ ℝ[x][y] ≅ ℂ[x][y]`, then `tensorQuotientEquiv`), and the
counterexample is stated with Mathlib's schemes: `Spec ℝ[x,y]/(x² + y²)` is integral
(`isIntegral_spec_sumSq`) but not geometrically irreducible over `ℝ`
(`not_geometricallyIrreducible_sumSq`, both in
`isIntegral_and_not_geometricallyIrreducible_sumSq`): its fibre over `Spec ℂ` is
`Spec ℂ[x,y]/(x² + y²)` (`pullbackSpecIso`), the two lines `x = ± i y`.
-/

namespace Grothendieck.Folder53

section SchemeCounterexample

open Polynomial TensorProduct Algebra.TensorProduct AlgebraicGeometry CategoryTheory

/-- `ℂ ⊗_ℝ ℝ[x][y] → ℂ[x][y]`, `z ⊗ f ↦ z f`. -/
noncomputable def baseChangeHom : ℂ ⊗[ℝ] ℝ[X][X] →ₐ[ℂ] ℂ[X][X] :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ ℂ[X][X])
    (mapAlgHom (mapAlgHom (Algebra.ofId ℝ ℂ))) fun _ _ => Commute.all _ _

/-- `ℂ[x][y] → ℂ ⊗_ℝ ℝ[x][y]`, `x ↦ 1 ⊗ x`, `y ↦ 1 ⊗ y`. -/
noncomputable def baseChangeInv : ℂ[X][X] →ₐ[ℂ] ℂ ⊗[ℝ] ℝ[X][X] :=
  Polynomial.eval₂AlgHom
    (Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℝ] (Polynomial.C Polynomial.X : ℝ[X][X])))
    ((1 : ℂ) ⊗ₜ[ℝ] (Polynomial.X : ℝ[X][X]))
    fun _ => by exact mul_comm (_ : ℂ ⊗[ℝ] ℝ[X][X]) _

theorem baseChangeInv_X :
    baseChangeInv Polynomial.X = (1 : ℂ) ⊗ₜ[ℝ] (Polynomial.X : ℝ[X][X]) :=
  Polynomial.eval₂_X _ _

theorem baseChangeInv_C_X :
    baseChangeInv (Polynomial.C Polynomial.X) =
      (1 : ℂ) ⊗ₜ[ℝ] (Polynomial.C Polynomial.X : ℝ[X][X]) :=
  (Polynomial.eval₂_C _ _).trans (Polynomial.aeval_X _)

theorem baseChangeHom_tmul (z : ℂ) (f : ℝ[X][X]) :
    baseChangeHom (z ⊗ₜ[ℝ] f) =
      Polynomial.C (Polynomial.C z) * f.map (Polynomial.mapRingHom (algebraMap ℝ ℂ)) :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- `ℂ ⊗_ℝ ℝ[x][y] ≅ ℂ[x][y]` as `ℂ`-algebras. -/
noncomputable def baseChangeEquiv : ℂ ⊗[ℝ] ℝ[X][X] ≃ₐ[ℂ] ℂ[X][X] :=
  AlgEquiv.ofAlgHom baseChangeHom baseChangeInv
    (by
      refine Polynomial.algHom_ext' (Polynomial.algHom_ext ?_) ?_ <;>
        simp [baseChangeInv_C_X, baseChangeInv_X, baseChangeHom_tmul])
    (by
      refine Algebra.TensorProduct.ext (by ext)
        (Polynomial.algHom_ext' (Polynomial.algHom_ext ?_) ?_) <;>
        simp [baseChangeInv_C_X, baseChangeInv_X, baseChangeHom_tmul])

theorem baseChangeEquiv_tmul_sumSq : baseChangeEquiv ((1 : ℂ) ⊗ₜ[ℝ] sumSq ℝ) = sumSq ℂ := by
  simp [baseChangeEquiv, baseChangeHom, sumSq]

/-- `ℝ[x,y]/(x² + y²)`, as a named type (a `def`, so that `ℂ ⊗[ℝ] SumSqRing` elaborates with
the module structure coming from the algebra). -/
def SumSqRing : Type := ℝ[X][X] ⧸ Ideal.span {sumSq ℝ}

noncomputable instance : CommRing SumSqRing := Ideal.Quotient.commRing _

noncomputable instance : Algebra ℝ SumSqRing := Ideal.Quotient.algebra _

instance : IsDomain SumSqRing :=
  haveI := isPrime_span_sumSq_real
  Ideal.Quotient.isDomain _

/-- `ℂ ⊗_ℝ ℝ[x,y]/(x² + y²) ≅ ℂ[x,y]/(x² + y²)` as `ℂ`-algebras. -/
noncomputable def tensorQuotSumSqEquiv :
    ℂ ⊗[ℝ] SumSqRing ≃ₐ[ℂ] ℂ[X][X] ⧸ Ideal.span {sumSq ℂ} :=
  (tensorQuotientEquiv ℂ ℝ[X][X] ℂ (Ideal.span {sumSq ℝ})).trans <|
    Ideal.quotientEquivAlg _ _ baseChangeEquiv (by
      rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
      simp [baseChangeEquiv_tmul_sumSq])

/-- `X = Spec ℝ[x,y]/(x² + y²)` is integral. -/
theorem isIntegral_spec_sumSq : IsIntegral (Spec (CommRingCat.of SumSqRing)) := inferInstance

/-- `X = Spec ℝ[x,y]/(x² + y²)` is not geometrically irreducible over `ℝ`: its base change to
`ℂ` is `Spec ℂ[x,y]/(x² + y²)`, which is not irreducible. -/
theorem not_geometricallyIrreducible_sumSq :
    ¬ GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap ℝ SumSqRing))) := by
  intro h
  have h1 := pullback_of_geometrically h.geometrically_irreducibleSpace ℂ
    (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))
  rw [(pullbackSpecIso ℝ SumSqRing ℂ).hom.homeomorph.irreducibleSpace_iff] at h1
  exact not_irreducibleSpace_complex ((PrimeSpectrum.homeomorphOfRingEquiv
    ((Algebra.TensorProduct.comm ℝ _ _).trans
      (tensorQuotSumSqEquiv.restrictScalars ℝ)).toRingEquiv).irreducibleSpace_iff.1
    (show IrreducibleSpace (PrimeSpectrum (SumSqRing ⊗[ℝ] ℂ)) from h1))

/-- The counterexample of page 9 with Mathlib's schemes: `Spec ℝ[x,y]/(x² + y²)` is integral
but not geometrically irreducible over `ℝ`. -/
theorem isIntegral_and_not_geometricallyIrreducible_sumSq :
    IsIntegral (Spec (CommRingCat.of SumSqRing)) ∧
      ¬ GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap ℝ SumSqRing))) :=
  ⟨isIntegral_spec_sumSq, not_geometricallyIrreducible_sumSq⟩

end SchemeCounterexample

end Grothendieck.Folder53
