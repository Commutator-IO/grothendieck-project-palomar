module

public import Mathlib

@[expose] public section


/-!
# Folder 29, page 120: the determinant criterion on tame inertia

The modernised reading `transcripts/29/29.modern.tex` (« Comportement fonctoriel des
groupes d'inertie », number 4, page 120) draws, for a morphism of strictly local regular
schemes with normal crossings divisors whose branches are indexed by `C` and `C'`, the
square in which the map on tame inertia is the map

  `N : ∏_{ℓ ≠ p} ℤ_ℓ(1)^C → ∏_{ℓ ≠ p} ℤ_ℓ(1)^{C'}`

of the integer matrix of multiplicities `(n_{c,c'})`, and states the criterion: `N` is an
isomorphism iff `card C = card C'` and the ordinary integer `det N` is `± p^r`, `p` the
characteristic exponent of the residue fields.

This is the criterion of finding `29-inertia-matrix-determinant` of
`src/content/findings.ts`. That the map on inertia is `N` (the Kummer computation of the
page) is not formalised: mathlib has no tame inertia of regular schemes. What is proved is
the criterion itself, for any integer matrix, `ℤ_ℓ(1)` being free of rank one over `ℤ_ℓ`.

* `inertiaMap N ℓ`: the map `ℤ_ℓ^C → ℤ_ℓ^{C'}` of an integer matrix `N` (rows `C'`,
  columns `C`).
* `card_eq_of_bijective`: if it is bijective for one `ℓ`, then `card C = card C'`.
* `bijective_iff_not_dvd_det`: for a square integer matrix, bijective over `ℤ_ℓ` iff
  `ℓ ∤ det`.
* `forall_not_dvd_iff`: an integer is prime to every prime `ℓ ≠ p` iff it is `± p^k`
  (`p` prime, or `p = 1`, the characteristic exponent in characteristic zero).
* `criterion_of_equiv`: once `C'` and `C` are matched by a bijection `e`, `N` is bijective
  over `ℤ_ℓ` for every `ℓ ≠ p` iff `det (N.submatrix id e) = ± p^k`; the choice of `e`
  changes the determinant only by a sign.
* `criterion` (the page's criterion): `N` is bijective over `ℤ_ℓ` for every prime `ℓ ≠ p`
  iff `card C = card C'` and the determinant is `± p^k`.
-/

open Matrix

namespace Folder29

variable {C C' : Type*} [Fintype C] [Fintype C']

/-- The map `ℤ_ℓ^C → ℤ_ℓ^{C'}` of an integer matrix with rows indexed by `C'` and columns
by `C`. -/
noncomputable def inertiaMap (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (C → ℤ_[ℓ]) → (C' → ℤ_[ℓ]) :=
  (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVec

/-- A matrix bijective over `ℤ_ℓ` for one `ℓ` is square. -/
theorem card_eq_of_bijective (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : Function.Bijective (inertiaMap N ℓ)) : Fintype.card C = Fintype.card C' := by
  simpa using (LinearEquiv.ofBijective (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVecLin h).finrank_eq

/-- A square integer matrix is bijective over `ℤ_ℓ` iff `ℓ` does not divide its
determinant. -/
theorem bijective_iff_not_dvd_det [DecidableEq C'] (M : Matrix C' C' ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (inertiaMap M ℓ) ↔ ¬ (ℓ : ℤ) ∣ M.det := by
  rw [not_iff_comm.1 ((PadicInt.not_isUnit_iff (p := ℓ)).trans
    PadicInt.norm_intCast_lt_one_iff), Int.cast_det, ← isUnit_iff_isUnit_det]
  exact ⟨fun h => mulVec_surjective_iff_isUnit.1 h.2,
    fun h => ⟨mulVec_injective_of_isUnit h, mulVec_surjective_iff_isUnit.2 h⟩⟩

/-- An integer is prime to every prime `ℓ ≠ p` iff it is `± p^k`, for `p` prime or
`p = 1`. -/
theorem forall_not_dvd_iff {p : ℕ} (hp : p = 1 ∨ p.Prime) (d : ℤ) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ¬ (ℓ : ℤ) ∣ d) ↔ ∃ k : ℕ, d = p ^ k ∨ d = -(p ^ k : ℤ) := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
    have hd : d ≠ 0 := fun hd => h ℓ hℓ (by omega) (hd ▸ dvd_zero _)
    have hn : d.natAbs = p ^ d.natAbs.primeFactorsList.length := by
      rcases hp with rfl | hp
      · rw [one_pow, Nat.eq_one_iff_not_exists_prime_dvd]
        exact fun q hq hqd => h q hq hq.one_lt.ne' (Int.natCast_dvd.2 hqd)
      · exact Nat.eq_prime_pow_of_unique_prime_dvd (Int.natAbs_ne_zero.2 hd) fun hq hqd =>
          by_contra fun hqp => h _ hq hqp (Int.natCast_dvd.2 hqd)
    generalize d.natAbs.primeFactorsList.length = k at hn
    exact ⟨k, (by exact_mod_cast hn : (d.natAbs : ℤ) = p ^ k) ▸ Int.natAbs_eq d⟩
  · rintro ⟨k, hk⟩ ℓ hℓ hℓp hdvd
    have : ℓ ∣ p ^ k := by
      rcases hk with rfl | rfl <;> simpa [← Int.natCast_dvd_natCast] using hdvd
    rcases hp with rfl | hp
    · exact hℓ.one_lt.ne' (Nat.dvd_one.1 (by simpa using this))
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow this))

/-- Reindexing the columns by a bijection does not change bijectivity. -/
theorem bijective_submatrix_iff (N : Matrix C' C ℤ) (e : C' ≃ C) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (inertiaMap (N.submatrix id e) ℓ) ↔
      Function.Bijective (inertiaMap N ℓ) := by
  have : inertiaMap (N.submatrix id e) ℓ = inertiaMap N ℓ ∘ (· ∘ e.symm) := by
    ext v
    simp [inertiaMap, ← submatrix_map, submatrix_mulVec_equiv]
  rw [this, Function.Bijective.of_comp_iff]
  exact (e.arrowCongr (Equiv.refl ℤ_[ℓ])).bijective

/-- The criterion once `C'` and `C` are matched by `e`. -/
theorem criterion_of_equiv [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ)
    (e : C' ≃ C) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      ∃ k : ℕ, (N.submatrix id e).det = p ^ k ∨
        (N.submatrix id e).det = -(p ^ k : ℤ) := by
  rw [← forall_not_dvd_iff hp]
  refine ⟨fun h ℓ hℓ hℓp => ?_, fun h ℓ _ hℓp => ?_⟩
  · have := Fact.mk hℓ
    exact (bijective_iff_not_dvd_det _ ℓ).1 ((bijective_submatrix_iff N e ℓ).2 (h ℓ hℓp))
  · exact (bijective_submatrix_iff N e ℓ).1
      ((bijective_iff_not_dvd_det _ ℓ).2 (h ℓ Fact.out hℓp))

/-- **The criterion of page 120.** The integer matrix `N` is bijective over `ℤ_ℓ` for every
prime `ℓ ≠ p` iff `card C = card C'` and, the columns being matched with the rows by some
bijection, `det N = ± p^k`. -/
theorem criterion [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      Fintype.card C = Fintype.card C' ∧ ∃ e : C' ≃ C, ∃ k : ℕ,
        (N.submatrix id e).det = p ^ k ∨ (N.submatrix id e).det = -(p ^ k : ℤ) := by
  refine ⟨fun h => ?_, fun ⟨_, e, he⟩ => (criterion_of_equiv hp N e).2 he⟩
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have := Fact.mk hℓ
  have hc := card_eq_of_bijective N ℓ (h ℓ (by omega))
  exact ⟨hc, Fintype.equivOfCardEq hc.symm, (criterion_of_equiv hp N _).1 h⟩

end Folder29

/-!
# Folder 29, pages 212 and 214: the degree as primitive datum

The reading (« Compter les feuillets sans compter de points », pages 212 and 214 of
`transcripts/29/29.modern.tex`) gives, on the inserted sheets « 1 bis » and « 1 ter », six
conditions on classes of « morphisms of degree `n` »: a) stable under base change, b) additive
for finite sums, c) isomorphisms of degree 1, d') every `f : X ⟶ Y` decomposes the base as
`Y = ∐ₙ Yₙ` with `X ×_Y Yₙ ⟶ Yₙ` of degree `n`, d) degree `≥ 1` implies (universal) effective
descent, e) degree `0` implies `X = ∅`, `f` an isomorphism onto a direct summand. The
« Conclusion » of page 214: under these conditions (and (0)–(2): finite limits, monomorphisms
summand inclusions) the notion is uniquely determined, and `f` has degree `n` iff it becomes
`[1, n]` after a morphism of universal effective descent. This is finding
`29-degree-n-as-primitive`.

The class of trivialising morphisms is a parameter `E : MorphismProperty C` (for the page,
the universal effective descent morphisms, which mathlib does not define); of `E` we use only
that it contains identities and is stable under composition (direct sense), and that every
pullback of a member is an epimorphism (converse). The category is finitary extensive (finite
sums disjoint and universal) with pullbacks, and every monomorphism has a complement (the
page's (2)).

* `DegreeAxioms E`: the six conditions, b) as the nullary and binary sums.
* `atMost_ne`, `degree_not_unique`: **the uniqueness is false as read.** From any degree `D`,
  `D.atMost` (degree `n` := `D`-degree `k` for some `1 ≤ k ≤ n`, or `k = n = 0`) satisfies the
  six conditions too; in finite sets (`FintypeCat`, `E` the surjections) the fibre-cardinality
  degree `standard` and `standard.atMost` differ, `𝟙 PUnit` having degree 1 and 2 in the latter.
  The page's step « donc par additivité, `X'₁ ⟶ Y'` est de degré `n - 1` » is a cancellation
  that the six conditions do not give.
* `DegreeAxioms.UniqueDegree`: the missing condition, a morphism of two different degrees
  has an empty base.
* `deg_imp_triv`: with it, the page's induction through the diagonal: degree `n` implies
  `Triv E n` (trivialised by a member of `E` into `n` copies of the base, `IsTrivial`).
* `triv_imp_deg`: the converse, which the page does not write, for any degree `D` with unique
  degrees, whatever its own descent class, once members of `E` are universal epimorphisms.
* `deg_iff_triv`, `unique` (the Conclusion, repaired): two degrees with unique degrees agree.
-/

namespace Folder29.Degree

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- `p : P ⟶ B` is the constant object `[1, n]_B`: `P ≅ B ⊔ (B ⊔ (⋯ ⊔ ∅))` over `B`,
each summand mapping to `B` by the identity. -/
inductive IsTrivial : ℕ → ∀ {P B : C}, (P ⟶ B) → Prop
  | zero {P B : C} (p : P ⟶ B) : Nonempty (IsInitial P) → IsTrivial 0 p
  | succ {n : ℕ} {P Q B : C} (p : P ⟶ B) (q : Q ⟶ B) (i : B ⟶ P) (j : Q ⟶ P) :
      i ≫ p = 𝟙 B → j ≫ p = q → Nonempty (IsColimit (BinaryCofan.mk i j)) →
      IsTrivial n q → IsTrivial (n + 1) p

/-- `f` becomes `[1, n]` after base change along some member of `E`. -/
def Triv (E : MorphismProperty C) (n : ℕ) : MorphismProperty C := fun X Y f =>
  ∃ (Y' : C) (g : Y' ⟶ Y), E g ∧ ∃ (P : C) (fst : P ⟶ X) (snd : P ⟶ Y'),
    IsPullback fst snd f g ∧ IsTrivial n snd

/-- Conditions a) to e) of page 212 on classes `deg n` of morphisms of degree `n`; additivity
b) for finite sums is stated for the empty and the binary sums, d') with `ℕ`-indexed
coproducts. -/
structure DegreeAxioms (E : MorphismProperty C) where
  deg : ℕ → MorphismProperty C
  baseChange {n : ℕ} {P X Y Y' : C} {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} :
    IsPullback fst snd f g → deg n f → deg n snd
  addZero {X Y : C} (f : X ⟶ Y) : Nonempty (IsInitial X) → deg 0 f
  add {m n : ℕ} {X₁ X₂ X Y : C} {i₁ : X₁ ⟶ X} {i₂ : X₂ ⟶ X} (f : X ⟶ Y) :
    Nonempty (IsColimit (BinaryCofan.mk i₁ i₂)) → deg m (i₁ ≫ f) → deg n (i₂ ≫ f) →
      deg (m + n) f
  iso {X Y : C} (f : X ⟶ Y) [IsIso f] : deg 1 f
  decomp {X Y : C} (f : X ⟶ Y) : ∃ (Yk : ℕ → C) (ι : ∀ k, Yk k ⟶ Y),
    Nonempty (IsColimit (Cofan.mk Y ι)) ∧ ∀ k, ∃ (P : C) (fst : P ⟶ X) (snd : P ⟶ Yk k),
      IsPullback fst snd f (ι k) ∧ deg k snd
  descent {n : ℕ} {X Y : C} (f : X ⟶ Y) : deg (n + 1) f → E f
  empty {X Y : C} (f : X ⟶ Y) : deg 0 f → Nonempty (IsInitial X)
  emptySummand {X Y : C} (f : X ⟶ Y) : deg 0 f →
    ∃ (Z : C) (c : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk f c))

variable {E : MorphismProperty C}

/-- The condition the page's argument uses and does not state: a morphism of two different
degrees has an empty (initial) base. -/
def DegreeAxioms.UniqueDegree (D : DegreeAxioms E) : Prop :=
  ∀ {m n : ℕ} {X Y : C} (f : X ⟶ Y), D.deg m f → D.deg n f → m ≠ n → Nonempty (IsInitial Y)

/-- In a coproduct `Y = ∐ⱼ Yⱼ` whose summands other than `Yₖ` are initial, `Yₖ ⟶ Y` is an
isomorphism. -/
lemma isIso_ι_of_isInitial {Y : C} {Yk : ℕ → C} {ι : ∀ k, Yk k ⟶ Y}
    (hc : IsColimit (Cofan.mk Y ι)) (k : ℕ) (h : ∀ j, j ≠ k → Nonempty (IsInitial (Yk j))) :
    IsIso (ι k) := by
  classical
  let φ : ∀ j, Yk j ⟶ Yk k := fun j =>
    if hj : j = k then eqToHom (by rw [hj]) else (h j hj).some.to _
  have hφ : φ k = 𝟙 _ := by simp [φ]
  refine ⟨Cofan.IsColimit.desc hc φ, ?_, ?_⟩
  · simpa [hφ] using Cofan.IsColimit.fac hc φ k
  · refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    rw [← Category.assoc]
    erw [Cofan.IsColimit.fac hc φ j]
    refine Eq.trans ?_ (Category.comp_id _).symm
    change φ j ≫ ι k = ι j
    by_cases hj : j = k
    · subst hj; rw [hφ, Category.id_comp]
    · exact (h j hj).some.hom_ext _ _

/-- Degree descends along an isomorphism of bases. -/
lemma deg_of_isIso {n : ℕ} (D : DegreeAxioms E) {P X Y Y' : C} {fst : P ⟶ X} {snd : P ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback fst snd f g) [IsIso g] (h : D.deg n snd) :
    D.deg n f := by
  have := sq.isIso_fst_of_isIso
  refine D.baseChange (fst := inv fst) (g := inv g) ?_ h
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [IsIso.inv_comp_eq, ← Category.assoc, sq.w, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- In an extensive category, the target of an epimorphism with initial source is initial. -/
lemma isInitial_of_epi [FinitaryExtensive C] {X Y : C} (hX : IsInitial X) (f : X ⟶ Y) [Epi f] :
    Nonempty (IsInitial Y) := by
  have hpb := FinitaryExtensive.isPullback_initial_to_binaryCofan (coprodIsCoprod Y Y)
  have heq : (coprod.inl : Y ⟶ Y ⨿ Y) = coprod.inr := by
    rw [← cancel_epi f]; exact hX.hom_ext _ _
  exact ⟨IsInitial.ofStrict (hpb.lift (𝟙 Y) (𝟙 Y) (by simpa using heq)) initialIsInitial⟩

/-- If `X' = X ⊔ Z` over `X` (the first summand a section of `q`), the pullback of `q` along
`h : W ⟶ X` is `W ⊔ (Z ×_X W)` over `W`. -/
lemma split [FinitaryExtensive C] {X X' Z W P P0 : C} {Δ : X ⟶ X'} {c : Z ⟶ X'}
    (hc : IsColimit (BinaryCofan.mk Δ c)) {q : X' ⟶ X} (hΔ : Δ ≫ q = 𝟙 X) {h : W ⟶ X}
    {fst₁ : P ⟶ Z} {snd₁ : P ⟶ W} (sq₁ : IsPullback fst₁ snd₁ (c ≫ q) h)
    {fst₀ : P0 ⟶ X'} {snd₀ : P0 ⟶ W} (sq₀ : IsPullback fst₀ snd₀ q h) :
    ∃ (j₀ : W ⟶ P0) (j₁ : P ⟶ P0), j₀ ≫ snd₀ = 𝟙 W ∧ j₁ ≫ snd₀ = snd₁ ∧
      Nonempty (IsColimit (BinaryCofan.mk j₀ j₁)) := by
  let j₀ := sq₀.lift (h ≫ Δ) (𝟙 W) (by simp [hΔ])
  let j₁ := sq₀.lift (fst₁ ≫ c) snd₁ (by rw [Category.assoc, sq₁.w])
  have e₀ : j₀ ≫ snd₀ = 𝟙 W := sq₀.lift_snd _ _ _
  have e₁ : j₁ ≫ snd₀ = snd₁ := sq₀.lift_snd _ _ _
  refine ⟨j₀, j₁, e₀, e₁, ?_⟩
  refine ((BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hc)
    (BinaryCofan.mk j₀ j₁) h fst₁ fst₀ (sq₀.lift_fst _ _ _).symm
    (sq₀.lift_fst _ _ _).symm).2 ⟨?_, ?_⟩
  · refine (IsPullback.of_bot (h₁₁ := h) (v₁₁ := j₀) ?_ (sq₀.lift_fst _ _ _).symm sq₀).flip
    rw [e₀, hΔ]
    exact IsPullback.id_vert h
  · refine (IsPullback.of_bot (h₁₁ := fst₁) (v₁₁ := j₁) ?_ (sq₀.lift_fst _ _ _).symm sq₀).flip
    rw [e₁]
    exact sq₁


/-- The cancellation of page 214 (« donc par additivité »): if `X' = X ⊔ Z` over `X` has degree
`k + 1`, then `Z ⟶ X` has degree `k`. It needs `UniqueDegree`. -/
lemma cancel [HasPullbacks C] [FinitaryExtensive C] (D : DegreeAxioms E) (hu : D.UniqueDegree)
    {k : ℕ} {X X' Z : C} {Δ : X ⟶ X'} {c : Z ⟶ X'} (hc : IsColimit (BinaryCofan.mk Δ c))
    {q : X' ⟶ X} (hΔ : Δ ≫ q = 𝟙 X) (hq : D.deg (k + 1) q) : D.deg k (c ≫ q) := by
  obtain ⟨Xj, ι, ⟨hcof⟩, hpb⟩ := D.decomp (c ≫ q)
  have hinit : ∀ j, j ≠ k → Nonempty (IsInitial (Xj j)) := by
    intro j hj
    obtain ⟨P, fst₁, snd₁, sq₁, hdeg⟩ := hpb j
    have sq₀ := IsPullback.of_hasPullback q (ι j)
    obtain ⟨j₀, j₁, e₀, e₁, hcol⟩ := split hc hΔ sq₁ sq₀
    have h1 : D.deg (1 + j) (pullback.snd q (ι j)) :=
      D.add _ hcol (by rw [e₀]; exact D.iso _) (by rw [e₁]; exact hdeg)
    exact hu _ h1 (D.baseChange sq₀ hq) (by omega)
  have := isIso_ι_of_isInitial hcof k hinit
  obtain ⟨P, fst, snd, sq, hdeg⟩ := hpb k
  exact deg_of_isIso D sq hdeg

/-- **Page 214, the induction.** A morphism of degree `n` becomes `[1, n]` after base change
along a member of `E`: for `n > 0`, pull back along `f` itself; the diagonal splits
`X ×_Y X = X ⊔ X'₁`, `X'₁ ⟶ X` has degree `n - 1`, and the trivialising morphism is the
composite. -/
theorem deg_imp_triv [HasPullbacks C] [FinitaryExtensive C] [E.ContainsIdentities]
    [E.IsStableUnderComposition]
    (hmono : ∀ {A B : C} (m : A ⟶ B) [Mono m],
      ∃ (Z : C) (c : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk m c)))
    (D : DegreeAxioms E) (hu : D.UniqueDegree) (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (hf : D.deg n f) : Triv E n f := by
  induction n generalizing X Y with
  | zero =>
    exact ⟨Y, 𝟙 Y, E.id_mem Y, X, 𝟙 X, f, IsPullback.id_horiz f,
      IsTrivial.zero f (D.empty f hf)⟩
  | succ k ih =>
    have hE := D.descent f hf
    have sq := IsPullback.of_hasPullback f f
    have hq : D.deg (k + 1) (pullback.snd f f) := D.baseChange sq hf
    obtain ⟨Z, c, ⟨hc⟩⟩ := hmono (pullback.diagonal f)
    have hr := cancel D hu hc (pullback.diagonal_snd f) hq
    obtain ⟨W, h, hEh, P, fst₁, snd₁, sq₁, htriv⟩ := ih _ hr
    have sq₀ := IsPullback.of_hasPullback (pullback.snd f f) h
    obtain ⟨j₀, j₁, e₀, e₁, hcol⟩ := split hc (pullback.diagonal_snd f) sq₁ sq₀
    exact ⟨W, h ≫ f, E.comp_mem _ _ hEh hE, _, _, _, sq₀.paste_horiz sq,
      IsTrivial.succ _ snd₁ j₀ j₁ e₀ e₁ hcol htriv⟩

/-- `[1, n]_B ⟶ B` has degree `n`, by b) and c). -/
lemma deg_of_isTrivial (D : DegreeAxioms E) {n : ℕ} {P B : C} {p : P ⟶ B}
    (h : IsTrivial n p) : D.deg n p := by
  induction h with
  | zero p hP => exact D.addZero p hP
  | succ p q i j hi hj hc _ ih =>
    rw [Nat.add_comm]
    exact D.add p hc (by rw [hi]; exact D.iso _) (by rw [hj]; exact ih)

/-- **The converse**, not on the page: a morphism trivialised into `n` sheets by a universal
epimorphism has degree `n`, for any degree with unique degrees. -/
theorem triv_imp_deg [HasPullbacks C] [FinitaryExtensive C] {E' : MorphismProperty C}
    (hE : ∀ {A B Y' Y : C} {a : A ⟶ Y'} {b : A ⟶ B} {g : Y' ⟶ Y} {k : B ⟶ Y},
      E g → IsPullback a b g k → Epi b)
    (D : DegreeAxioms E') (hu : D.UniqueDegree) {n : ℕ} {X Y : C} {f : X ⟶ Y}
    (hf : Triv E n f) : D.deg n f := by
  obtain ⟨Y', g, hg, P, fst, snd, sq, ht⟩ := hf
  have hsnd := deg_of_isTrivial D ht
  obtain ⟨Yk, ι, ⟨hcof⟩, hpb⟩ := D.decomp f
  have hinit : ∀ k, k ≠ n → Nonempty (IsInitial (Yk k)) := by
    intro k hk
    obtain ⟨Q, fq, sqk, hsq, hdeg⟩ := hpb k
    have hR := IsPullback.of_hasPullback g (ι k)
    have := hE hg hR
    have hS := IsPullback.of_hasPullback snd (pullback.fst g (ι k))
    have big := hS.paste_horiz sq
    rw [hR.w] at big
    have hw : (pullback.fst snd (pullback.fst g (ι k)) ≫ fst) ≫ f =
        (pullback.snd snd (pullback.fst g (ι k)) ≫ pullback.snd g (ι k)) ≫ ι k :=
      big.w.trans (Category.assoc _ _ _).symm
    have left : IsPullback (hsq.lift _ _ hw) (pullback.snd snd (pullback.fst g (ι k)))
        sqk (pullback.snd g (ι k)) := by
      refine IsPullback.of_right ?_ (hsq.lift_snd _ _ _) hsq
      rw [hsq.lift_fst]
      exact big
    obtain ⟨hRi⟩ := hu _ (D.baseChange left hdeg) (D.baseChange hS hsnd) hk
    exact isInitial_of_epi hRi (pullback.snd g (ι k))
  have := isIso_ι_of_isInitial hcof n hinit
  obtain ⟨Q, fq, sqn, hsq, hdeg⟩ := hpb n
  exact deg_of_isIso D hsq hdeg


/-- **The Conclusion of page 214, repaired**: degree `n` iff trivialised into `n` sheets by a
member of `E`. -/
theorem deg_iff_triv [HasPullbacks C] [FinitaryExtensive C] [E.ContainsIdentities]
    [E.IsStableUnderComposition]
    (hmono : ∀ {A B : C} (m : A ⟶ B) [Mono m],
      ∃ (Z : C) (c : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk m c)))
    (hE : ∀ {A B Y' Y : C} {a : A ⟶ Y'} {b : A ⟶ B} {g : Y' ⟶ Y} {k : B ⟶ Y},
      E g → IsPullback a b g k → Epi b)
    (D : DegreeAxioms E) (hu : D.UniqueDegree) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    D.deg n f ↔ Triv E n f :=
  ⟨deg_imp_triv hmono D hu n f, triv_imp_deg hE D hu⟩

/-- **Uniqueness**, with `UniqueDegree`: two such degrees coincide. -/
theorem unique [HasPullbacks C] [FinitaryExtensive C] [E.ContainsIdentities]
    [E.IsStableUnderComposition]
    (hmono : ∀ {A B : C} (m : A ⟶ B) [Mono m],
      ∃ (Z : C) (c : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk m c)))
    (hE : ∀ {A B Y' Y : C} {a : A ⟶ Y'} {b : A ⟶ B} {g : Y' ⟶ Y} {k : B ⟶ Y},
      E g → IsPullback a b g k → Epi b)
    (D D' : DegreeAxioms E) (hu : D.UniqueDegree) (hu' : D'.UniqueDegree) : D.deg = D'.deg := by
  funext n X Y f
  exact propext ((deg_iff_triv hmono hE D hu n f).trans (deg_iff_triv hmono hE D' hu' n f).symm)

/-- From a degree `D`, the classes « `D`-degree `k` with `1 ≤ k ≤ n` » (and `D`-degree `0` for
`n = 0`) satisfy the six conditions again. -/
def DegreeAxioms.atMost (D : DegreeAxioms E) : DegreeAxioms E where
  deg n := fun _ _ f => ∃ k ≤ n, (k = 0 ↔ n = 0) ∧ D.deg k f
  baseChange sq := fun ⟨k, hk, hk0, h⟩ => ⟨k, hk, hk0, D.baseChange sq h⟩
  addZero f h := ⟨0, le_rfl, Iff.rfl, D.addZero f h⟩
  add f hc := fun ⟨k₁, h₁, h₁0, d₁⟩ ⟨k₂, h₂, h₂0, d₂⟩ =>
    ⟨k₁ + k₂, by omega, by omega, D.add f hc d₁ d₂⟩
  iso f _ := ⟨1, le_rfl, Iff.rfl, D.iso f⟩
  decomp f := by
    obtain ⟨Yk, ι, hc, h⟩ := D.decomp f
    exact ⟨Yk, ι, hc, fun k => let ⟨P, a, b, sq, d⟩ := h k; ⟨P, a, b, sq, k, le_rfl, Iff.rfl, d⟩⟩
  descent f := fun ⟨k, _, hk0, h⟩ => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact D.descent f h
  empty f := fun ⟨k, hk, _, h⟩ => D.empty f (by obtain rfl : k = 0 := (by omega); exact h)
  emptySummand f := fun ⟨k, hk, _, h⟩ =>
    D.emptySummand f (by obtain rfl : k = 0 := (by omega); exact h)

/-- If `D` has unique degrees and some object is not initial, `D.atMost` is a different degree:
the identity of that object has `D.atMost`-degree 1 and 2. -/
theorem atMost_ne (D : DegreeAxioms E) (hu : D.UniqueDegree) (Y : C)
    (hY : IsEmpty (IsInitial Y)) : D.deg ≠ D.atMost.deg := by
  intro h
  have h2 : D.atMost.deg 2 (𝟙 Y) := ⟨1, by omega, by omega, D.iso _⟩
  exact hY.false (hu _ (D.iso (𝟙 Y)) (h ▸ h2) (by omega)).some

end Folder29.Degree

namespace Folder29.Degree.Finite

open CategoryTheory Limits FintypeCat

/-- The surjections, the universal effective descent morphisms of finite sets. -/
def surj : MorphismProperty FintypeCat.{0} := fun _ _ f => Function.Surjective f

/-- Degree `n` in finite sets: every fibre has `n` elements. -/
def deg (n : ℕ) : MorphismProperty FintypeCat.{0} := fun X Y f =>
  ∀ y : Y, Nat.card {x : X // f x = y} = n

/-- An initial finite set is empty. -/
lemma isEmpty_of_isInitial {X : FintypeCat.{0}} (h : IsInitial X) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := ConcreteCategory.congr_hom
    (h.hom_ext (homMk fun _ => true : X ⟶ FintypeCat.of Bool) (homMk fun _ => false)) x
  exact Bool.noConfusion (this : true = false)

/-- An empty finite set is initial. -/
noncomputable def isInitialOfIsEmpty {X : FintypeCat.{0}} (h : IsEmpty X) : IsInitial X :=
  IsInitial.ofUniqueHom (fun _ => homMk fun x => isEmptyElim x)
    (fun _ _ => by ext x; exact isEmptyElim x)

/-- Fibres are preserved by base change. -/
lemma card_baseChange {P X Y Y' : FintypeCat.{0}} {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback fst snd f g) (y' : Y') :
    Nat.card {p : P // snd p = y'} = Nat.card {x : X // f x = g y'} := by
  have := (Types.isPullback_iff _ _ _ _).1 (sq.map (forget FintypeCat))
  simp at this
  obtain ⟨-, hinj, hex⟩ := this
  have hw : ∀ p, f (fst p) = g (snd p) := fun p => by
    simpa using ConcreteCategory.congr_hom sq.w p
  refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨fst p.1, by rw [hw, p.2]⟩) ⟨?_, ?_⟩)
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (hinj p p' h (hp.trans hp'.symm))
  · rintro ⟨x, hx⟩
    obtain ⟨p, h1, h2⟩ := hex x y' hx
    exact ⟨⟨p, h2⟩, Subtype.ext h1⟩

/-- Fibres add over a binary sum. -/
lemma card_add {X₁ X₂ X Y : FintypeCat.{0}} {i₁ : X₁ ⟶ X} {i₂ : X₂ ⟶ X}
    (hc : IsColimit (BinaryCofan.mk i₁ i₂)) (f : X ⟶ Y) (y : Y) :
    Nat.card {x : X // f x = y} =
      Nat.card {a : X₁ // (i₁ ≫ f) a = y} + Nat.card {b : X₂ // (i₂ ≫ f) b = y} := by
  have := (Types.binaryCofan_isColimit_iff _).1
    ⟨(isColimitMapCoconeBinaryCofanEquiv (forget _) i₁ i₂) (isColimitOfPreserves (forget _) hc)⟩
  simp at this
  obtain ⟨h₁, h₂, hcompl⟩ := this
  rw [← Nat.card_sum]
  refine (Nat.card_congr (Equiv.ofBijective
    (Sum.elim (fun a => ⟨i₁ a.1, by simpa using a.2⟩) (fun b => ⟨i₂ b.1, by simpa using b.2⟩))
    ⟨?_, ?_⟩)).symm
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩) (⟨a', ha'⟩ | ⟨b', hb'⟩) h <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg _ (Subtype.ext (h₁ h))
    · exact (Set.disjoint_left.1 hcompl.disjoint ⟨a, rfl⟩ ⟨b', h.symm⟩).elim
    · exact (Set.disjoint_left.1 hcompl.disjoint ⟨a', rfl⟩ ⟨b, h⟩).elim
    · exact congrArg _ (Subtype.ext (h₂ h))
  · rintro ⟨x, hx⟩
    have : x ∈ Set.range i₁ ⊔ Set.range i₂ := hcompl.sup_eq_top ▸ Set.mem_univ x
    rcases this with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨Sum.inl ⟨a, by simpa using hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨b, by simpa using hx⟩, rfl⟩


/-- The decomposition `Y = ∐ₖ Yₖ` by fibre cardinality. -/
abbrev piece {X Y : FintypeCat.{0}} (f : X ⟶ Y) (k : ℕ) : FintypeCat.{0} :=
  FintypeCat.of {y : Y // Nat.card {x : X // f x = y} = k}

/-- `Y` is the sum of the `Yₖ`. -/
noncomputable def pieceCofanIsColimit {X Y : FintypeCat.{0}} (f : X ⟶ Y) :
    IsColimit (Cofan.mk Y fun k => (homMk Subtype.val : piece f k ⟶ Y)) :=
  Cofan.IsColimit.mk _ (fun t => homMk fun y => t.inj (Nat.card {x : X // f x = y}) ⟨y, rfl⟩)
    (fun t k => by ext ⟨y, hy⟩; subst hy; rfl)
    (fun t m hm => by
      ext y; exact ConcreteCategory.congr_hom (hm (Nat.card {x : X // f x = y})) ⟨y, rfl⟩)

/-- The part of `X` over `Yₖ`. -/
abbrev pieceTotal {X Y : FintypeCat.{0}} (f : X ⟶ Y) (k : ℕ) : FintypeCat.{0} :=
  FintypeCat.of {x : X // Nat.card {x' : X // f x' = f x} = k}

/-- The inclusion of `X ×_Y Yₖ` in `X`. -/
def pieceFst {X Y : FintypeCat.{0}} (f : X ⟶ Y) (k : ℕ) : pieceTotal f k ⟶ X :=
  homMk fun (x : {x : X // Nat.card {x' : X // f x' = f x} = k}) => x.1

/-- The projection `X ×_Y Yₖ ⟶ Yₖ`. -/
def pieceSnd {X Y : FintypeCat.{0}} (f : X ⟶ Y) (k : ℕ) : pieceTotal f k ⟶ piece f k :=
  homMk fun (x : {x : X // Nat.card {x' : X // f x' = f x} = k}) => ⟨f x.1, x.2⟩

/-- `X ×_Y Yₖ` is the pullback. -/
lemma piece_isPullback {X Y : FintypeCat.{0}} (f : X ⟶ Y) (k : ℕ) :
    IsPullback (pieceFst f k) (pieceSnd f k) f (homMk Subtype.val) := by
  have w : pieceFst f k ≫ f = pieceSnd f k ≫ homMk Subtype.val := by ext; rfl
  apply IsPullback.of_map (forget FintypeCat) w
  rw [Types.isPullback_iff]
  refine ⟨by rw [← Functor.map_comp, w, Functor.map_comp], fun a b h => Subtype.ext h.1, ?_⟩
  rintro x ⟨y, hy⟩ h
  change f x = y at h
  exact ⟨⟨x, by rw [h]; exact hy⟩, rfl, Subtype.ext h⟩

/-- A map of degree 0 has empty source. -/
lemma isEmpty_of_deg_zero {X Y : FintypeCat.{0}} {f : X ⟶ Y} (h : deg 0 f) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := h (f x)
  have : Nonempty {x' : X // f x' = f x} := ⟨⟨x, rfl⟩⟩
  have : 0 < Nat.card {x' : X // f x' = f x} := Nat.card_pos
  omega

/-- The standard degree on finite sets: every fibre has `n` elements. -/
noncomputable def standard : DegreeAxioms surj where
  deg := deg
  baseChange sq h y' := (card_baseChange sq y').trans (h _)
  addZero f h y := by
    have := isEmpty_of_isInitial h.some
    simp
  add f hc h₁ h₂ y := by rw [card_add hc.some f y, h₁ y, h₂ y]
  iso f _ y := by
    obtain ⟨hi, hs⟩ := ConcreteCategory.bijective_of_isIso f
    obtain ⟨x, hx⟩ := hs y
    exact Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext (hi (a.2.trans b.2.symm))⟩, ⟨⟨x, hx⟩⟩⟩
  decomp f := ⟨piece f, fun k => homMk Subtype.val, ⟨pieceCofanIsColimit f⟩, fun k =>
    ⟨_, _, _, piece_isPullback f k, fun ⟨y, hy⟩ => by
      refine (Nat.card_congr ?_).trans hy
      exact
        { toFun := fun p => ⟨p.1.1, congrArg Subtype.val p.2⟩
          invFun := fun x => ⟨⟨x.1, by rw [x.2]; exact hy⟩, Subtype.ext x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }⟩⟩
  descent f h y := by
    have : Nonempty {x // f x = y} := (Nat.card_pos_iff.1 (by rw [h y]; omega)).1
    exact ⟨this.some.1, this.some.2⟩
  empty f h := ⟨isInitialOfIsEmpty (isEmpty_of_deg_zero h)⟩
  emptySummand f h := by
    have := isEmpty_of_deg_zero h
    refine ⟨_, 𝟙 _, ⟨BinaryCofan.IsColimit.mk _ (fun _ g => g) (fun _ _ => ?_)
      (fun _ _ => Category.id_comp _) (fun _ _ m _ h₂ => by simpa using h₂)⟩⟩
    ext x; exact isEmptyElim x

/-- The standard degree has unique degrees. -/
theorem standard_uniqueDegree : standard.UniqueDegree := by
  intro m n X Y f hm hn hmn
  refine ⟨isInitialOfIsEmpty ⟨fun y => hmn ?_⟩⟩
  exact (hm y).symm.trans (hn y)

/-- A point is not initial. -/
theorem not_isInitial_punit : IsEmpty (IsInitial (FintypeCat.of PUnit.{1})) :=
  ⟨fun h => (isEmpty_of_isInitial h).false PUnit.unit⟩

/-- **The page's six conditions do not determine the degree**: in finite sets, with the
surjections as descent morphisms, the fibre-cardinality degree and its `atMost` both satisfy
them and differ. -/
theorem degree_not_unique : ∃ D₁ D₂ : DegreeAxioms surj, D₁.deg ≠ D₂.deg :=
  ⟨standard, standard.atMost,
    atMost_ne standard standard_uniqueDegree _ not_isInitial_punit⟩

end Folder29.Degree.Finite

/-!
## Finite sets satisfy conditions (0)–(2)

`FintypeCat` (universe 0) with the surjections as descent class satisfies all hypotheses of
`Folder29.Degree.deg_iff_triv`: it is essentially small (0), has finite limits (1), every
monomorphism is the inclusion of a direct summand (2), and it is finitary extensive; pullbacks
of surjections are epimorphisms. Hence `Finite.deg_iff_triv` and `Finite.unique`: a degree with
(u) is the fibre cardinality, and `Finite.not_uniqueDegree_atMost`: the counterexample
`standard.atMost` survives (0)–(2) and fails (u).
-/

namespace Folder29.Degree.Finite

open CategoryTheory Limits FintypeCat

/-- Finite sets are finitary extensive (finite sums disjoint and universal). -/
instance : FinitaryExtensive FintypeCat.{0} :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (forget FintypeCat)

/-- Condition (2) for finite sets: every monomorphism is the inclusion of a direct summand,
its complement being the rest of the target. -/
theorem mono_complement {A B : FintypeCat.{0}} (m : A ⟶ B) [Mono m] :
    ∃ (Z : FintypeCat.{0}) (c : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk m c)) := by
  have hm : Function.Injective m := (mono_iff_injective ((forget FintypeCat).map m)).1
    inferInstance
  refine ⟨FintypeCat.of {b : B // b ∉ Set.range m}, homMk Subtype.val, ⟨isColimitOfReflects
    (forget _) ((isColimitMapCoconeBinaryCofanEquiv _ _ _).symm
      ((Types.binaryCofan_isColimit_iff _).2 ?_).some)⟩⟩
  refine ⟨hm, Subtype.val_injective, ?_⟩
  change IsCompl (Set.range m) (Set.range (Subtype.val : {b // b ∉ Set.range m} → B))
  rw [Subtype.range_coe_subtype]
  exact isCompl_compl

/-- Condition (0) for finite sets: the isomorphism classes form a small set. -/
theorem essentiallySmall : EssentiallySmall.{0} FintypeCat.{0} :=
  EssentiallySmall.mk' FintypeCat.Skeleton.equivalence.symm

/-- Conditions (0)–(2) of page 212 hold in finite sets: essentially small, finite limits,
every monomorphism the inclusion of a direct summand. -/
theorem conditions :
    EssentiallySmall.{0} FintypeCat.{0} ∧ HasFiniteLimits FintypeCat.{0} ∧
      ∀ {A B : FintypeCat.{0}} (m : A ⟶ B) [Mono m],
        ∃ (Z : FintypeCat.{0}) (c : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk m c)) :=
  ⟨essentiallySmall, inferInstance, mono_complement⟩

instance : surj.ContainsIdentities := ⟨fun _ => Function.surjective_id⟩

instance : surj.IsStableUnderComposition := ⟨fun _ _ hf hg => hg.comp hf⟩

/-- Pullbacks of surjections are epimorphisms (indeed surjections). -/
theorem surj_pullback_epi {A B Y' Y : FintypeCat.{0}} {a : A ⟶ Y'} {b : A ⟶ B} {g : Y' ⟶ Y}
    {k : B ⟶ Y} (hg : surj g) (sq : IsPullback a b g k) : Epi b := by
  have := (Types.isPullback_iff _ _ _ _).1 (sq.map (forget FintypeCat))
  simp at this
  refine (forget _).epi_of_epi_map ((epi_iff_surjective _).2 fun β => ?_)
  obtain ⟨y', hy'⟩ := hg (k β)
  obtain ⟨p, -, hp⟩ := this.2.2 y' β hy'
  exact ⟨p, hp⟩

/-- **The Conclusion of page 214 in finite sets**: with (u), a degree for the surjections is
the fibre cardinality, and degree `n` means trivialised into `n` sheets by a surjection. -/
theorem deg_iff_triv (n : ℕ) {X Y : FintypeCat.{0}} (f : X ⟶ Y) : deg n f ↔ Triv surj n f :=
  Degree.deg_iff_triv mono_complement surj_pullback_epi standard standard_uniqueDegree n f

/-- Uniqueness in finite sets: a degree for the surjections with (u) is the fibre cardinality. -/
theorem unique (D : DegreeAxioms surj) (hu : D.UniqueDegree) : D.deg = deg :=
  Degree.unique mono_complement surj_pullback_epi D standard hu standard_uniqueDegree

/-- Under (0)–(2) the counterexample `standard.atMost` survives, and it fails (u). -/
theorem not_uniqueDegree_atMost : ¬ standard.atMost.UniqueDegree := fun h =>
  atMost_ne standard standard_uniqueDegree _ not_isInitial_punit (unique _ h).symm

end Folder29.Degree.Finite
