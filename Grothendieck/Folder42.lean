module

public import Mathlib
public import Grothendieck.Upstream.NoetherianIsOpenOfStableUnderGeneralization

@[expose] public section


/-!
# Folder 42: Lemme 1, the proposition of page 3, Lemme 2, Corollaire 1

The modernised reading `transcripts/42/42.modern.tex` (manuscript pages 3–5)
states:

> **Proposition (page 3).** Let `X` be a locally Noetherian sober space and `F` a
> sheaf on `X` such that (H): for every `x` there is a nonempty open `U` of
> `closure {x}` on which every generization map `F_y → F_x` is injective. Then
> `Γ(X, F) → lim_x F_x` (coherent families of germs) is bijective.
>
> **Lemme 1.** For a coherent family `(ξ_x)` and a section `s ∈ F(U)`, the locus
> `{x ∈ U : s_x = ξ_x}` is open.
>
> **Lemme 2.** Let `A` be a Noetherian ring and `𝔭` a prime ideal of `A`. Then
> 1. there exists `f ∈ A - 𝔭` such that `A_f → A_𝔭` is injective;
> 2. if moreover `A → A_𝔭` is already injective, then `A_𝔮 → A_𝔭` is injective
>    for every prime ideal `𝔮 ⊇ 𝔭`.
>
> **Corollaire 1.** For `X` locally Noetherian, `Γ(X, 𝒪_X) ≅ lim_x 𝒪_{X,x}`.

All are proved here, Corollaire 1 for `X = Spec A` with `A` Noetherian (the
affine case, to which the reading reduces it). What this certifies is that the
reading holds together, not that it is what the page says (issue #26): that is
for a reader with the leaf in front of them.

What the proofs make plain. The step « constructible and stable under
generization, hence open » is used only in the form proved here as
`isOpen_of_stableUnderGeneralization`: a set stable under generization that
contains, with each point `x`, a nonempty open of `closure {x}`, is open in a
Noetherian sober space. Lemme 2 (2) does not use the Noetherian hypothesis.
Lemme 2 (1) uses it only to make the kernel of `A → A_𝔭` finitely generated —
which is where the reading's footnote bears: the kernel is the set of elements
killed by *some* element outside `𝔭`, not by every one. Corollaire 1 needs, from
Lemme 2, only that one `f ∉ 𝔭` kills that kernel.
-/

namespace Grothendieck.Folder42

open IsLocalization TopologicalSpace

variable {A : Type*} [CommRing A]

/-- A map out of a localisation `S = M⁻¹A`, induced by `g : A → P`, is injective
as soon as everything `g` kills is already killed in `S`. -/
theorem lift_injective {M : Submonoid A} {S : Type*} [CommRing S] [Algebra A S]
    [IsLocalization M S] {P : Type*} [CommRing P] {g : A →+* P}
    (hg : ∀ y : M, IsUnit (g y)) (h : ∀ x, g x = 0 → algebraMap A S x = 0) :
    Function.Injective (IsLocalization.lift (S := S) hg) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M z
  have hgx : g x = 0 := by
    have := congrArg (IsLocalization.lift (S := S) hg) e
    rw [map_mul, hz, zero_mul, IsLocalization.lift_eq] at this
    exact this.symm
  rw [h x hgx] at e
  exact (IsLocalization.map_units S s).mul_left_eq_zero.mp e

variable (p : Ideal A) [p.IsPrime]

/-- The map `A_f → A_𝔭`, for `f ∉ 𝔭`. -/
noncomputable def awayToAtPrime (f : A) (hf : f ∉ p) :
    Localization.Away f →+* Localization.AtPrime p :=
  IsLocalization.lift (M := Submonoid.powers f)
    (fun y => IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y, (Submonoid.powers_le.2 (show f ∈ p.primeCompl from hf)) y.2⟩)

/-- The map `A_𝔮 → A_𝔭`, for primes `𝔭 ⊆ 𝔮`. -/
noncomputable def atPrimeToAtPrime (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    Localization.AtPrime q →+* Localization.AtPrime p :=
  IsLocalization.lift (M := q.primeCompl)
    (fun y => IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y, fun h => y.2 (hpq h)⟩)

/-- The kernel of `A → A_𝔭`, for `A` Noetherian, is killed by one element outside `𝔭`. -/
theorem exists_mul_eq_zero_of_ker [IsNoetherianRing A] :
    ∃ f ∉ p, ∀ y, algebraMap A (Localization.AtPrime p) y = 0 → f * y = 0 := by
  classical
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian
    (RingHom.ker (algebraMap A (Localization.AtPrime p))) : Submodule.FG _)
  have kill : ∀ x ∈ t, ∃ s : p.primeCompl, (s : A) * x = 0 := fun x hx => by
    have : x ∈ RingHom.ker (algebraMap A (Localization.AtPrime p)) :=
      ht ▸ Submodule.subset_span hx
    exact (IsLocalization.map_eq_zero_iff p.primeCompl _ x).1 this
  choose! s hs using kill
  let f : A := ∏ x ∈ t, (s x : A)
  have hf : f ∈ p.primeCompl := Submonoid.prod_mem _ fun x _ => (s x).2
  have hspan : ∀ y ∈ Submodule.span A (t : Set A), f * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun x => (s x : A)) hx
      show (∏ x ∈ t, (s x : A)) * x = 0
      rw [hc, mul_comm (s x : A) c, mul_assoc, hs x hx, mul_zero]
    | zero => exact mul_zero f
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  exact ⟨f, hf, fun y hy => hspan y (ht.symm ▸ hy)⟩

/-- **Lemme 2 (1).** Over a Noetherian ring, some `f ∉ 𝔭` makes `A_f → A_𝔭`
injective. -/
theorem lemme2_1 [IsNoetherianRing A] :
    ∃ (f : A) (hf : f ∉ p), Function.Injective (awayToAtPrime p f hf) := by
  obtain ⟨f, hf, hJ⟩ := exists_mul_eq_zero_of_ker p
  refine ⟨f, hf, lift_injective _ fun y hy => ?_⟩
  exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ y).2
    ⟨⟨f, Submonoid.mem_powers f⟩, hJ y hy⟩

/-- **Lemme 2 (2).** If `A → A_𝔭` is injective, so is `A_𝔮 → A_𝔭` for every
prime `𝔮 ⊇ 𝔭`. No Noetherian hypothesis is needed. -/
theorem lemme2_2 (hinj : Function.Injective (algebraMap A (Localization.AtPrime p)))
    (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    Function.Injective (atPrimeToAtPrime p q hpq) :=
  lift_injective _ fun x hx => by
    rw [hinj (hx.trans (map_zero _).symm), map_zero]


section Topology

variable {X : Type*} [TopologicalSpace X]

/-- **The topological step of Lemme 1 (page 3).** In a Noetherian sober space, a set `E` stable
under generization that contains, with each of its points `x`, a nonempty open of `closure {x}`
(equivalently `W ∩ closure {x}` for an open `W ∋ x`), is open. Noetherian induction on the closed
sets in which `Eᶜ` is dense. -/
theorem isOpen_of_stableUnderGeneralization [NoetherianSpace X] [QuasiSober X] {E : Set X}
    (hgen : StableUnderGeneralization E)
    (hloc : ∀ x ∈ E, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E :=
  TopologicalSpace.NoetherianSpace.isOpen_of_stableUnderGeneralization hgen hloc

end Topology

/-- `A_𝔮 → A_𝔭` is the identity on `A`. -/
theorem atPrimeToAtPrime_algebraMap (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) (x : A) :
    atPrimeToAtPrime p q hpq (algebraMap A _ x) = algebraMap A _ x :=
  IsLocalization.lift_eq _ x

/-- If `f` kills the kernel of `A → A_𝔭`, then `A_𝔮 → A_𝔭` is injective for every prime
`𝔮 ⊇ 𝔭` with `f ∉ 𝔮`: the injectivity condition (H) on the open `D(f) ∩ V(𝔭)` of `V(𝔭)`. -/
theorem atPrimeToAtPrime_injective_of_mul_eq_zero {f : A}
    (hf : ∀ y, algebraMap A (Localization.AtPrime p) y = 0 → f * y = 0)
    (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) (hfq : f ∉ q) :
    Function.Injective (atPrimeToAtPrime p q hpq) :=
  lift_injective _ fun y hy =>
    (IsLocalization.map_eq_zero_iff q.primeCompl _ y).2 ⟨⟨f, hfq⟩, hf y hy⟩

/-- The map `(A_f)_𝔔 → A_𝔭`, for `f ∉ 𝔭` and a prime `𝔔` of `A_f` whose trace on `A` contains
`𝔭`: the page's form of Lemme 2 (2). -/
noncomputable def awayAtPrimeToAtPrime (f : A) (hf : f ∉ p) (Q : Ideal (Localization.Away f))
    [Q.IsPrime] (hQ : p ≤ Q.comap (algebraMap A _)) :
    Localization.AtPrime Q →+* Localization.AtPrime p :=
  IsLocalization.lift (M := Q.primeCompl) (g := awayToAtPrime p f hf) fun y => by
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, e⟩ :=
      IsLocalization.surj (Submonoid.powers f) (y : Localization.Away f)
    have hfn : IsUnit (algebraMap A (Localization.Away f) (f ^ n)) :=
      IsLocalization.map_units _ (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    have ha : a ∉ p := fun ha => by
      have h1 : algebraMap A (Localization.Away f) a ∈ Q := hQ ha
      rw [← e] at h1
      rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
      · exact y.2 h2
      · exact Ideal.IsPrime.ne_top inferInstance (Ideal.eq_top_of_isUnit_mem Q h2 hfn)
    have hu : IsUnit (awayToAtPrime p f hf y *
        awayToAtPrime p f hf (algebraMap A _ (f ^ n))) := by
      rw [← map_mul, e]
      unfold awayToAtPrime
      rw [IsLocalization.lift_eq]
      exact IsLocalization.map_units (Localization.AtPrime p) (⟨a, ha⟩ : p.primeCompl)
    exact isUnit_of_mul_isUnit_left hu

/-- **Lemme 2 (2), in the page's form.** If `A_f → A_𝔭` is injective, so is `(A_f)_𝔔 → A_𝔭`
for every prime `𝔔` of `A_f` above a prime containing `𝔭`. -/
theorem lemme2_2_away (f : A) (hf : f ∉ p) (hinj : Function.Injective (awayToAtPrime p f hf))
    (Q : Ideal (Localization.Away f)) [Q.IsPrime] (hQ : p ≤ Q.comap (algebraMap A _)) :
    Function.Injective (awayAtPrimeToAtPrime p f hf Q hQ) :=
  lift_injective _ fun x hx => by
    rw [hinj (hx.trans (map_zero _).symm), map_zero]

/-- Lemme 2 (1) and (2) together, as page 5 uses them: some `f ∉ 𝔭` makes every
`(A_f)_𝔔 → A_𝔭` injective. -/
theorem lemme2_page [IsNoetherianRing A] :
    ∃ (f : A) (hf : f ∉ p), ∀ (Q : Ideal (Localization.Away f)) [Q.IsPrime]
      (hQ : p ≤ Q.comap (algebraMap A _)),
      Function.Injective (awayAtPrimeToAtPrime p f hf Q hQ) := by
  obtain ⟨f, hf, hinj⟩ := lemme2_1 p
  exact ⟨f, hf, fun Q _ hQ => lemme2_2_away p f hf hinj Q hQ⟩

omit p in
/-- A *coherent family* of germs of the structure sheaf of `Spec A`: one element `ξ 𝔭 ∈ A_𝔭`
for each prime, such that `ξ 𝔮 ↦ ξ 𝔭` under `A_𝔮 → A_𝔭` whenever `𝔭 ⊆ 𝔮`, i.e. whenever `𝔭` is a
generization of `𝔮`. These families form `lim_x 𝒪_{X,x}` along the specialization order. -/
def IsCoherent (ξ : ∀ P : PrimeSpectrum A, Localization.AtPrime P.asIdeal) : Prop :=
  ∀ (P Q : PrimeSpectrum A) (h : P.asIdeal ≤ Q.asIdeal),
    atPrimeToAtPrime P.asIdeal Q.asIdeal h (ξ Q) = ξ P

omit p in
/-- The germs of an element of `A` form a coherent family. -/
theorem isCoherent_algebraMap (a : A) :
    IsCoherent (fun P : PrimeSpectrum A => algebraMap A (Localization.AtPrime P.asIdeal) a) :=
  fun P Q h => atPrimeToAtPrime_algebraMap P.asIdeal Q.asIdeal h a

omit p in
/-- **Lemme 1 (page 3), for the structure sheaf of `Spec A`, `A` Noetherian.** For a coherent
family `ξ` and a fraction `a / s`, the locus `{𝔭 ∈ D(s) : ξ 𝔭 = a / s}` is open. -/
theorem lemme1 [IsNoetherianRing A] {ξ : ∀ P : PrimeSpectrum A, Localization.AtPrime P.asIdeal}
    (hξ : IsCoherent ξ) (a s : A) :
    IsOpen {P : PrimeSpectrum A | s ∉ P.asIdeal ∧
      ξ P * algebraMap A _ s = algebraMap A _ a} := by
  apply isOpen_of_stableUnderGeneralization
  · intro Q P hPQ hQ
    have h : P.asIdeal ≤ Q.asIdeal := (PrimeSpectrum.le_iff_specializes P Q).2 hPQ
    refine ⟨fun hs => hQ.1 (h hs), ?_⟩
    have := congrArg (atPrimeToAtPrime P.asIdeal Q.asIdeal h) hQ.2
    rwa [map_mul, hξ P Q h, atPrimeToAtPrime_algebraMap, atPrimeToAtPrime_algebraMap] at this
  · intro P hP
    obtain ⟨f, hf, hkill⟩ := exists_mul_eq_zero_of_ker P.asIdeal
    refine ⟨(PrimeSpectrum.basicOpen f : Set _) ∩ PrimeSpectrum.basicOpen s,
      (PrimeSpectrum.basicOpen f).isOpen.inter (PrimeSpectrum.basicOpen s).isOpen,
      ⟨hf, hP.1⟩, ?_⟩
    rintro Q ⟨⟨hfQ, hsQ⟩, hQP⟩
    have h : P.asIdeal ≤ Q.asIdeal :=
      (PrimeSpectrum.le_iff_specializes P Q).2 (specializes_iff_mem_closure.2 hQP)
    refine ⟨hsQ, atPrimeToAtPrime_injective_of_mul_eq_zero P.asIdeal hkill Q.asIdeal h hfQ ?_⟩
    rw [map_mul, hξ P Q h, atPrimeToAtPrime_algebraMap, atPrimeToAtPrime_algebraMap]
    exact hP.2

section
open AlgebraicGeometry StructureSheaf

omit p in
/-- **Corollaire 1 (page 4).** For `A` Noetherian, `A = Γ(Spec A, 𝒪)` is the limit of the local
rings `A_𝔭` along specialization: `a ↦ (a/1)_𝔭` is a bijection onto the coherent families.
Injectivity holds for every ring; surjectivity is Lemme 1 plus mathlib's description of the
structure sheaf as the sheaf of locally-fraction families. -/
theorem corollaire1 [IsNoetherianRing A] :
    Function.Bijective (fun a : A =>
      (⟨fun P : PrimeSpectrum A => algebraMap A (Localization.AtPrime P.asIdeal) a,
        isCoherent_algebraMap a⟩ : {ξ // IsCoherent ξ})) := by
  constructor
  · intro a b hab
    refine (toOpenₗ_top_bijective (R := A) (M := A)).1 (Subtype.ext (funext fun x => ?_))
    have h := congrFun (congrArg Subtype.val hab) x.1
    simp only [← Localization.mk_one_eq_algebraMap] at h
    exact h
  · rintro ⟨ξ, hξ⟩
    obtain ⟨a, ha⟩ := (toOpenₗ_top_bijective (R := A) (M := A)).2 ⟨fun x => ξ x.1, fun x => by
      have : (x.1 : PrimeSpectrum A).asIdeal.IsPrime := (x.1 : PrimeSpectrum A).isPrime
      obtain ⟨⟨a, ⟨s, hs⟩⟩, e⟩ :=
        IsLocalization.surj (x.1 : PrimeSpectrum A).asIdeal.primeCompl (ξ x.1)
      refine ⟨⟨_, lemme1 hξ a s⟩, ⟨hs, e⟩, CategoryTheory.homOfLE le_top, a, s, fun y => ⟨y.2.1, ?_⟩⟩
      show ξ y.1 = Localization.mk a ⟨s, y.2.1⟩
      rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
      exact y.2.2⟩
    refine ⟨a, Subtype.ext (funext fun P => ?_)⟩
    have h := congrArg (fun t => t.1 ⟨P, trivial⟩) ha
    simp only at h
    show algebraMap A _ a = ξ P
    rw [← h, toOpenₗ_eq_const, ← Localization.mk_one_eq_algebraMap]
    rfl

end


section Sheaves

open CategoryTheory Opposite

universe u

variable {X : TopCat.{u}} (F : TopCat.Sheaf (Type u) X)

/-- A *coherent family of germs* of `F`: `ξ x ∈ F_x` for each `x`, with `ρ_{yx} (ξ y) = ξ x`
whenever `x ⤳ y` (`y` a specialization of `x`). -/
def IsCoherentGerms (ξ : ∀ x : X, ToType (F.presheaf.stalk x)) : Prop :=
  ∀ ⦃x y : X⦄ (h : x ⤳ y), F.presheaf.stalkSpecializes h (ξ y) = ξ x

/-- **Condition (H) (page 3).** Every point `x` has an open `W ∋ x` such that the generization
maps `F_y → F_x` are injective for `y ∈ W ∩ closure {x}` — i.e. on a nonempty open of
`closure {x}`. -/
def ConditionH : Prop :=
  ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ y ∈ (W : Set X) ∩ closure {x}, ∀ h : x ⤳ y,
    Function.Injective (fun t => F.presheaf.stalkSpecializes h t)

/-- **Lemme 1 (page 3).** Under (H), on a Noetherian sober space, the locus where a section
agrees with a coherent family of germs is open. -/
theorem lemme1_faisceau [NoetherianSpace X] [QuasiSober X] (hH : ConditionH F)
    {ξ : ∀ x : X, ToType (F.presheaf.stalk x)} (hξ : IsCoherentGerms F ξ)
    (U : Opens X) (s : ToType (F.1.obj (op U))) :
    IsOpen {x : X | ∃ hx : x ∈ U, F.presheaf.germ U x hx s = ξ x} := by
  apply isOpen_of_stableUnderGeneralization
  · rintro x y h ⟨hx, e⟩
    refine ⟨h.mem_open U.isOpen hx, ?_⟩
    rw [← hξ h, ← e, TopCat.Presheaf.germ_stalkSpecializes_apply]
  · rintro x ⟨hx, e⟩
    obtain ⟨W, hxW, hinj⟩ := hH x
    refine ⟨(W : Set X) ∩ U, W.isOpen.inter U.isOpen, ⟨hxW, hx⟩, ?_⟩
    rintro y ⟨⟨hyW, hyU⟩, hyx⟩
    have h : x ⤳ y := specializes_iff_mem_closure.2 hyx
    refine ⟨hyU, hinj y ⟨hyW, hyx⟩ h ?_⟩
    simp only
    rw [hξ h, TopCat.Presheaf.germ_stalkSpecializes_apply, e]

/-- **Proposition (page 3).** On a Noetherian sober space, under (H), a global section is the
same thing as a coherent family of germs. -/
theorem proposition [NoetherianSpace X] [QuasiSober X] (hH : ConditionH F) :
    Function.Bijective (fun s : ToType (F.1.obj (op ⊤)) =>
      (⟨fun x => F.presheaf.germ ⊤ x trivial s, fun _ _ h =>
        F.presheaf.germ_stalkSpecializes_apply (U := ⊤) (hy := trivial) h s⟩ :
        {ξ // IsCoherentGerms F ξ})) := by
  constructor
  · exact fun s t hst => TopCat.Presheaf.section_ext F ⊤ s t fun x _ =>
      congrFun (congrArg Subtype.val hst) x
  · rintro ⟨ξ, hξ⟩
    choose U hxU s hs using fun x => F.presheaf.exists_germ_eq (ξ x)
    let V : X → Opens X := fun x =>
      ⟨{y | ∃ hy : y ∈ U x, F.presheaf.germ (U x) y hy (s x) = ξ y},
        lemme1_faisceau F hH hξ (U x) (s x)⟩
    have hVU : ∀ x, V x ≤ U x := fun x y hy => hy.1
    let sf : ∀ x, ToType (F.1.obj (op (V x))) := fun x => F.1.map (homOfLE (hVU x)).op (s x)
    have hgerm : ∀ x y (hy : y ∈ V x), F.presheaf.germ (V x) y hy (sf x) = ξ y :=
      fun x y hy => (F.presheaf.germ_res_apply _ y hy _).trans hy.2
    have hcompat : TopCat.Presheaf.IsCompatible F.1 V sf := by
      intro x y
      apply TopCat.Presheaf.section_ext F
      intro z hz
      refine ((F.presheaf.germ_res_apply ((V x).infLELeft (V y)) z hz (sf x)).trans ?_).trans
        (F.presheaf.germ_res_apply ((V x).infLERight (V y)) z hz (sf y)).symm
      exact (hgerm x z _).trans (hgerm y z _).symm
    obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top)
      (fun z _ => Opens.mem_iSup.2 ⟨z, hxU z, hs z⟩) sf hcompat
    refine ⟨g, Subtype.ext (funext fun x => ?_)⟩
    show F.presheaf.germ ⊤ x trivial g = ξ x
    rw [← hgerm x x ⟨hxU x, hs x⟩, ← hg x, TopCat.Presheaf.germ_res_apply]

end Sheaves
end Grothendieck.Folder42

/-!
# Folder 42, pages 1, 2, 5 and 6: réseaux of local rings, Corollaire 3

The modernised reading states (Corollaire 3, the theorem of page 2 with the edition's
hypothesis « `Y` séparé »):

> Let `S` be locally Noetherian, `X` and `Y` locally of finite type over `S`, `Y` separated over
> `S`. Then `Hom_S(X, Y) → Hom_{p(S)}(p(X), p(Y))` is bijective.

Proved here as `Reseau.toReseau_bijective` (for `X` locally Noetherian, `Y` locally of finite
type and separated over an arbitrary `S`) and `Reseau.corollaire3` (the page's hypotheses).

What the proof makes plain. Injectivity (`toReseau_injective`) needs only `X` locally
Noetherian: neither separatedness nor finite type of `Y` is used, since the réseau datum at `x`
fixes the composite `Spec 𝒪_{X,x} → Y`, and two morphisms agreeing there agree near `x`.
Separatedness enters at one place, Lemme 3, in the form `ext_of_injective_of_isSeparated`: two
`S`-morphisms `Spec 𝒪_{X,x''} → Y` that agree after `Spec 𝒪_{X,x} → Spec 𝒪_{X,x''}`, an
injective ring map, are equal. Lemme 1 is used for the locus where a spread-out morphism agrees
with the réseau homomorphism (`isOpen_matches`), on a locally Noetherian scheme rather than a
Noetherian space. Finite type of `Y` enters only through Mathlib's spreading out
(`spread_out_of_isGermInjective'`), the limit theorem of EGA IV the reading cites.
-/

namespace Grothendieck.Folder42.Reseau

open AlgebraicGeometry CategoryTheory Limits Topology TopologicalSpace

universe u

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- The topological step of Lemme 1, for a quasi-sober space covered by Noetherian opens (such
as a locally Noetherian scheme): it reduces to `isOpen_of_stableUnderGeneralization` on each
Noetherian open. -/
theorem isOpen_of_stableUnderGeneralization_of_locally [QuasiSober T]
    (hT : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ NoetherianSpace U) {E : Set T}
    (hgen : StableUnderGeneralization E)
    (hloc : ∀ x ∈ E, ∃ W : Set T, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hU⟩ := hT x
  have : QuasiSober U := U.isOpenEmbedding'.quasiSober
  have hE' : IsOpen (Subtype.val ⁻¹' E : Set U) := by
    refine isOpen_of_stableUnderGeneralization ?_ ?_
    · exact fun a b hab hb => hgen ((subtype_specializes_iff _ _).1 hab) hb
    · intro y hy
      obtain ⟨W, hW, hyW, hWE⟩ := hloc y hy
      refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hyW, ?_⟩
      rintro z ⟨hzW, hzc⟩
      refine hWE ⟨hzW, ?_⟩
      rw [← specializes_iff_mem_closure] at hzc ⊢
      exact (subtype_specializes_iff _ _).1 hzc
  exact ⟨_, Set.image_preimage_subset _ _, U.isOpen.isOpenMap_subtype_val _ hE', ⟨x, hxU⟩, hx, rfl⟩

end Topology

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- **A homomorphism of réseaux of local rings `p(X) → p(Y)` over `p(S)` (page 1).** An
application of the specialisation orders, increasing (`x ⤳ x'`, « `x'` specialises `x` »,
gives `φ x ⤳ φ x'`), lying over `S`, with a local homomorphism `𝒪_{Y,φ(x)} → 𝒪_{X,x}` at each
point, compatible with the generisation maps, and compatible with the structure maps to the
local rings of `S`. The localisation axiom of a réseau is a property of `p(X)` and `p(Y)`, which
come from schemes, so it is not a field here. -/
structure ReseauHom where
  toFun : X → Y
  mono : ∀ {x x' : X}, x ⤳ x' → toFun x ⤳ toFun x'
  liesOver : ∀ x, sX x = sY (toFun x)
  stalk : ∀ x, Y.presheaf.stalk (toFun x) ⟶ X.presheaf.stalk x
  isLocalHom : ∀ x, IsLocalHom (stalk x).hom
  compat : ∀ {x x' : X} (h : x ⤳ x'),
    stalk x' ≫ X.presheaf.stalkSpecializes h = Y.presheaf.stalkSpecializes (mono h) ≫ stalk x
  overStalk : ∀ x, sY.stalkMap (toFun x) ≫ stalk x =
    S.presheaf.stalkSpecializes (Inseparable.of_eq (liesOver x)).specializes ≫ sX.stalkMap x

attribute [instance] ReseauHom.isLocalHom

variable {sX sY}

namespace ReseauHom

/-- The `S`-morphism `Spec 𝒪_{X,x} → Y` that `Φ` gives at `x`: `Spec` of the local homomorphism,
followed by `Spec 𝒪_{Y,φ(x)} → Y`. -/
noncomputable def germ (Φ : ReseauHom sX sY) (x : X) : Spec (X.presheaf.stalk x) ⟶ Y :=
  Spec.map (Φ.stalk x) ≫ Y.fromSpecStalk (Φ.toFun x)

/-- The germs of `Φ` are compatible with generisation. -/
theorem germ_specializes (Φ : ReseauHom sX sY) {x x' : X} (h : x ⤳ x') :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ Φ.germ x' = Φ.germ x := by
  rw [germ, ← Spec.map_comp_assoc, Φ.compat h, Spec.map_comp_assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, germ]

/-- The germs of `Φ` are `S`-morphisms. -/
theorem germ_comp (Φ : ReseauHom sX sY) (x : X) :
    Φ.germ x ≫ sY = X.fromSpecStalk x ≫ sX := by
  rw [germ, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
    Φ.overStalk, Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

set_option backward.isDefEq.respectTransparency false in
/-- The germ at `x` sends the closed point to `φ(x)`. -/
theorem germ_closedPoint (Φ : ReseauHom sX sY) (x : X) :
    Φ.germ x (IsLocalRing.closedPoint (X.presheaf.stalk x)) = Φ.toFun x := by
  rw [germ, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- A réseau homomorphism is determined by its germs: the point is the image of the closed point,
and `Spec 𝒪_{Y,y} → Y` is a monomorphism. -/
theorem ext_of_germ {Φ Ψ : ReseauHom sX sY} (h : ∀ x, Φ.germ x = Ψ.germ x) : Φ = Ψ := by
  have hfun : Φ.toFun = Ψ.toFun := funext fun x => by
    rw [← germ_closedPoint, h, germ_closedPoint]
  cases Φ with | mk f _ _ α _ _ _ => cases Ψ with | mk g _ _ β _ _ _ =>
  dsimp only at hfun
  subst hfun
  have : α = β := funext fun x => by
    have hx := h x
    simp only [germ] at hx
    exact Spec.map_injective ((cancel_mono _).1 hx)
  subst this
  rfl

end ReseauHom

/-- The réseau homomorphism of an `S`-morphism. -/
noncomputable def toReseau (f : X ⟶ Y) (hf : f ≫ sY = sX) : ReseauHom sX sY where
  toFun := f
  mono h := f.base.hom.map_specializes h
  liesOver x := by rw [← hf]; rfl
  stalk x := f.stalkMap x
  isLocalHom x := inferInstance
  compat h := (f.stalkSpecializes_stalkMap _ _ h).symm
  overStalk x := by
    subst hf
    rw [Scheme.Hom.stalkMap_comp]
    simp

/-- The germ of `p(f)` at `x` is `Spec 𝒪_{X,x} → X → Y`. -/
theorem toReseau_germ (f : X ⟶ Y) (hf : f ≫ sY = sX) (x : X) :
    (toReseau f hf).germ x = X.fromSpecStalk x ≫ f :=
  Scheme.SpecMap_stalkMap_fromSpecStalk f


/-- Two morphisms out of a locally Noetherian scheme that agree on every `Spec 𝒪_{W,w}` are
equal. -/
theorem eq_of_fromSpecStalk_comp {W : Scheme.{u}} [IsLocallyNoetherian W] {a b : W ⟶ Y}
    (h : ∀ w, W.fromSpecStalk w ≫ a = W.fromSpecStalk w ≫ b) : a = b :=
  Scheme.hom_ext_of_forall a b fun w => spread_out_unique_of_isGermInjective' a b (h w)

/-- **Injectivity (Corollaire 2).** Two `S`-morphisms with the same réseau homomorphism are equal,
for `X` locally Noetherian; neither separatedness nor finite type of `Y` is needed: the data at
`x` already fix the germ of the morphism at `x`. -/
theorem toReseau_injective [IsLocallyNoetherian X] {f g : X ⟶ Y} (hf : f ≫ sY = sX)
    (hg : g ≫ sY = sX) (h : toReseau f hf = toReseau g hg) : f = g :=
  eq_of_fromSpecStalk_comp fun x => by
    rw [← toReseau_germ f hf, ← toReseau_germ g hg, h]

/-- In a scheme, `𝒪_{W,w''} → 𝒪_{W,w}` is injective for `w ⤳ w''` in an affine open on which
the germ at `w` is injective. -/
theorem stalkSpecializes_injective {W : Scheme.{u}} {w w'' : W} (hw : w ⤳ w'') (U : W.Opens)
    (hU : IsAffineOpen U) (hwU : w ∈ U) (hw''U : w'' ∈ U)
    (hinj : Function.Injective (W.presheaf.germ U w hwU)) :
    Function.Injective (W.presheaf.stalkSpecializes hw) := by
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨w'', hw''U⟩ : U)
  have := hU.isLocalization_stalk ⟨w'', hw''U⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨w'', hw''U⟩).asIdeal.primeCompl z
  have ha : W.presheaf.germ U w hwU a = 0 := by
    have h1 := congrArg (W.presheaf.stalkSpecializes hw) e
    rw [map_mul, hz, zero_mul] at h1
    have h2 : W.presheaf.stalkSpecializes hw (algebraMap Γ(W, U) _ a) =
        W.presheaf.germ U w hwU a :=
      TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf hw''U hw a
    rw [← h2, ← h1]
  rw [hinj (ha.trans (map_zero _).symm), map_zero] at e
  exact (IsLocalization.map_units _ s).mul_left_eq_zero.mp e

/-- Two `Z`-morphisms `Spec R → Y`, `Y` separated over `Z`, that agree after `Spec T → Spec R`
for an injective `R → T`, are equal: their equaliser is a closed subscheme through which a
scheme-theoretically dense morphism factors. -/
theorem ext_of_injective_of_isSeparated {Z : Scheme.{u}} {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (hφ : Function.Injective φ) {a b : Spec R ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (hab : Spec.map φ ≫ a = Spec.map φ ≫ b) : a = b := by
  let X' : Over Z := Over.mk (a ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (Spec.map φ ≫ a ≫ s)
  let a' : X' ⟶ Y' := Over.homMk a
  let b' : X' ⟶ Y' := Over.homMk b (by simp [X', Y', h])
  let ι' : U' ⟶ X' := Over.homMk (Spec.map φ)
  have : IsSeparated Y'.hom := ‹_›
  have hfac : (equalizer.lift ι' (by ext1; exact hab)).left ≫ (equalizer.ι a' b').left =
      Spec.map φ := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (Spec.map φ).ker = ⊥ := by
    rw [Scheme.ker_of_isAffine, ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
      ← map_bot (Scheme.IdealSheafData.equivOfIsAffine).symm]
    congr 1
    rw [← RingHom.injective_iff_ker_eq_bot]
    have := Scheme.ΓSpecIso_naturality φ
    have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso T).inv := by
      rw [← reassoc_of% this, Iso.hom_inv_id, Category.comp_id]
    rw [e]
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso T).inv).1.comp hφ).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
  have : IsIso (equalizer.ι a' b').left := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, eq_bot_iff, ← hker, ← hfac]
    exact Scheme.Hom.le_ker_comp _ _
  rw [← cancel_epi (equalizer.ι a' b').left]
  congrm $(equalizer.condition a' b').left


namespace ReseauHom

variable (Φ : ReseauHom sX sY)

/-- `h : W → Y` agrees with `Φ` at `w`, along `ι : W → X`. -/
def Matches {W : Scheme.{u}} (ι : W ⟶ X) (h : W ⟶ Y) (w : W) : Prop :=
  W.fromSpecStalk w ≫ h = Spec.map (ι.stalkMap w) ≫ Φ.germ (ι w)

/-- Agreement with `Φ` is preserved by precomposition. -/
theorem matches_comp {W W' : Scheme.{u}} {ι : W ⟶ X} {h : W ⟶ Y} (k : W' ⟶ W) {j : W' ⟶ X}
    (hj : k ≫ ι = j) (w' : W') (H : Φ.Matches ι h (k w')) : Φ.Matches j (k ≫ h) w' := by
  subst hj
  unfold Matches at *
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, H, Scheme.Hom.stalkMap_comp]
  exact (Spec.map_comp_assoc _ _ _).symm

/-- Generisation, read along `ι`. -/
theorem germ_along_specializes {W : Scheme.{u}} (ι : W ⟶ X) {w w'' : W} (hw : w ⤳ w'') :
    Spec.map (W.presheaf.stalkSpecializes hw) ≫ Spec.map (ι.stalkMap w'') ≫ Φ.germ (ι w'') =
      Spec.map (ι.stalkMap w) ≫ Φ.germ (ι w) := by
  rw [← Spec.map_comp_assoc, ← ι.stalkSpecializes_stalkMap, Spec.map_comp_assoc,
    Φ.germ_specializes]

/-- The heart of the argument (Lemme 1 and Lemme 3): the locus where `h` agrees with `Φ` is
open, for `W` locally Noetherian and `Y` separated over `S`. -/
theorem isOpen_matches [IsSeparated sY] {W : Scheme.{u}} [IsLocallyNoetherian W] {ι : W ⟶ X}
    {h : W ⟶ Y} (hh : h ≫ sY = ι ≫ sX) : IsOpen {w | Φ.Matches ι h w} := by
  apply isOpen_of_stableUnderGeneralization_of_locally
  · intro w
    obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
    have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨U, hwU, noetherianSpace_of_isAffineOpen U hU⟩
  · intro a b hab hb
    change Φ.Matches ι h b
    change Φ.Matches ι h a at hb
    unfold Matches at *
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hab, Category.assoc, hb,
      germ_along_specializes]
  · intro w hw
    obtain ⟨U, hwU, hU, hinj⟩ := W.exists_germ_injective w
    refine ⟨U, U.isOpen, hwU, ?_⟩
    rintro w'' ⟨hw''U, hc⟩
    have hsp : w ⤳ w'' := specializes_iff_mem_closure.2 hc
    apply ext_of_injective_of_isSeparated (W.presheaf.stalkSpecializes hsp)
      (stalkSpecializes_injective hsp U hU hwU hw''U hinj) sY
    · simp only [Category.assoc, hh, Φ.germ_comp, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    · rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, germ_along_specializes]
      exact hw

end ReseauHom

set_option backward.isDefEq.respectTransparency false in
/-- `Spec 𝒪_{U,x} → Spec 𝒪_{X,x} → U` is the canonical map. -/
theorem SpecMap_stalkMap_fromSpecStalkOfMem (U : X.Opens) (x : X) (hx : x ∈ U) :
    Spec.map (U.ι.stalkMap ⟨x, hx⟩) ≫ U.fromSpecStalkOfMem x hx =
      U.toScheme.fromSpecStalk ⟨x, hx⟩ := by
  simp only [Scheme.Opens.fromSpecStalkOfMem, Spec.map_inv, IsIso.hom_inv_id_assoc]

/-- `Spec` of the stalk map of an open immersion is an epimorphism (an isomorphism). -/
theorem epi_SpecMap_stalkMap {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k] (a : A) :
    Epi (Spec.map (k.stalkMap a)) :=
  inferInstance

/-- **Surjectivity (Corollaire 3).** Every réseau homomorphism over `p(S)` comes from an
`S`-morphism, for `X` locally Noetherian and `Y` locally of finite type and separated over `S`.
Each germ spreads out to a neighbourhood (EGA IV's limit theorem, Mathlib's
`spread_out_of_isGermInjective'`); the locus where the spread-out morphism agrees with `Φ` is open
(`isOpen_matches`); on these loci the morphisms glue by injectivity. -/
theorem toReseau_surjective [IsLocallyNoetherian X] [LocallyOfFiniteType sY] [IsSeparated sY]
    (Φ : ReseauHom sX sY) : ∃ (f : X ⟶ Y) (hf : f ≫ sY = sX), toReseau f hf = Φ := by
  choose U hxU f hf1 hf2 using fun x =>
    spread_out_of_isGermInjective' sX sY (Φ.germ x) (Φ.germ_comp x)
  have hx : ∀ x, Φ.Matches (U x).ι (f x) ⟨x, hxU x⟩ := by
    intro x
    unfold ReseauHom.Matches
    change _ = _ ≫ Φ.germ x
    rw [hf1 x]
    have e := congrArg (· ≫ f x) (SpecMap_stalkMap_fromSpecStalkOfMem (U x) x (hxU x))
    simp only at e
    exact e.symm
  let V : ∀ x, (U x).toScheme.Opens := fun x =>
    ⟨{w | Φ.Matches (U x).ι (f x) w}, Φ.isOpen_matches (hf2 x)⟩
  let 𝒰 : X.OpenCover :=
    { I₀ := X, X x := (V x).toScheme, f x := (V x).ι ≫ (U x).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨x, ⟨⟨x, hxU x⟩, hx x⟩, rfl⟩, inferInstance⟩ }
  let g : ∀ x, (V x).toScheme ⟶ Y := fun x => (V x).ι ≫ f x
  have hmatch : ∀ x (v : V x), Φ.Matches ((V x).ι ≫ (U x).ι) (g x) v :=
    fun x v => Φ.matches_comp (V x).ι rfl v v.2
  have hglue : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ g x = pullback.snd _ _ ≫ g y := by
    intro x y
    have : IsLocallyNoetherian (pullback (𝒰.f x) (𝒰.f y)) :=
      isLocallyNoetherian_of_isOpenImmersion (pullback.fst _ _ ≫ 𝒰.f x)
    exact eq_of_fromSpecStalk_comp fun p => (Φ.matches_comp (pullback.fst _ _) rfl p (hmatch x _)).trans
      (Φ.matches_comp (pullback.snd _ _) pullback.condition.symm p (hmatch y _)).symm
  let F := 𝒰.glueMorphisms g hglue
  have hF : ∀ x, 𝒰.f x ≫ F = g x := 𝒰.ι_glueMorphisms g hglue
  have hFS : F ≫ sY = sX := 𝒰.hom_ext _ _ fun x => by
    rw [← Category.assoc, hF]
    simp only [g, Category.assoc, hf2]
    rfl
  refine ⟨F, hFS, ReseauHom.ext_of_germ fun z => ?_⟩
  rw [toReseau_germ]
  let v : (V z).toScheme := ⟨⟨z, hxU z⟩, hx z⟩
  have h1 := hmatch z v
  unfold ReseauHom.Matches at h1
  have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk_assoc ((V z).ι ≫ (U z).ι) (x := v) F
  rw [hF z] at h2
  have := epi_SpecMap_stalkMap ((V z).ι ≫ (U z).ι) v
  exact this.left_cancellation _ _ (h2.trans h1)

/-- **Corollaire 3, the theorem of page 2 in the edition's form.** For `X` locally Noetherian and
`Y` locally of finite type and separated over `S`, `f ↦ p(f)` is a bijection from the
`S`-morphisms `X → Y` onto the homomorphisms of réseaux of local rings `p(X) → p(Y)` over
`p(S)`. -/
theorem toReseau_bijective [IsLocallyNoetherian X] [LocallyOfFiniteType sY] [IsSeparated sY] :
    Function.Bijective (fun f : {f : X ⟶ Y // f ≫ sY = sX} => toReseau f.1 f.2) :=
  ⟨fun f g h => Subtype.ext (toReseau_injective f.2 g.2 h),
    fun Φ => let ⟨f, hf, e⟩ := toReseau_surjective Φ; ⟨⟨f, hf⟩, e⟩⟩

/-- **Corollaire 3 with the page's hypotheses** (`S` locally Noetherian, `X` and `Y` locally of
finite type over `S`) and the edition's (`Y` separated over `S`). -/
theorem corollaire3 [IsLocallyNoetherian S] [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    [IsSeparated sY] :
    Function.Bijective (fun f : {f : X ⟶ Y // f ≫ sY = sX} => toReseau f.1 f.2) :=
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  toReseau_bijective

end Grothendieck.Folder42.Reseau

/-!
# Folder 42, page 5: Lemme 3 in the page's form

The modernised reading states:

> **Lemme 3.** Suppose `Y` *separated* over `S`. Then `F : U ↦ Hom_S(U, Y)` satisfies (H).

Proved here as `Reseau.lemme3`, for `X` locally Noetherian and `Y` separated over an arbitrary
`S`: `homSheaf` is the sheaf `F` (`isSheaf_homPresheaf`, morphisms glue), `ConditionH` is the
condition (H) of page 3, and the open of `closure {x}` is any affine open around `x` on which the
germ map at `x` is injective. The page's « plus précisément » is
`stalkSpecializes_homSheaf_injective`: `F_y → F_x` is injective whenever `𝒪_{X,y} → 𝒪_{X,x}` is,
which is the case for `X = Spec A`, `A → A_𝔭` injective and `𝔮 ⊇ 𝔭` by Lemme 2 (2). With the
proposition of page 3, it gives Corollaire 2 for `X` Noetherian (`Reseau.corollaire2`).

What the proof makes plain. A germ of `F` at `x` is determined by the composite
`Spec 𝒪_{X,x} → Y` (`germ_homSheaf_eq_iff`), which uses only `X` locally Noetherian; the
injectivity is then `ext_of_injective_of_isSeparated`, the only use of separatedness.
-/

namespace Grothendieck.Folder42.Reseau

open AlgebraicGeometry CategoryTheory Limits Topology TopologicalSpace Opposite

universe u

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- The presheaf `U ↦ Hom_S(U, Y)` on `X`. -/
noncomputable def homPresheaf : TopCat.Presheaf (Type u) X.toTopCat where
  obj U := {f : (unop U : X.Opens).toScheme ⟶ Y // f ≫ sY = (unop U : X.Opens).ι ≫ sX}
  map i := ↾fun f => ⟨X.homOfLE i.unop.le ≫ f.1, by simp [f.2]⟩
  map_id U := by ext f; simp [Scheme.homOfLE_rfl]
  map_comp i j := by ext f; simp [Scheme.homOfLE_homOfLE_assoc]

variable {sX sY}

theorem homPresheaf_map_val {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) (f : (homPresheaf sX sY).obj U) :
    ((homPresheaf sX sY).map i f).1 = X.homOfLE i.unop.le ≫ f.1 := rfl

/-- **The sheaf of `S`-morphisms (page 5).** `U ↦ Hom_S(U, Y)` is a sheaf: morphisms glue. -/
theorem isSheaf_homPresheaf : (homPresheaf sX sY).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι (U : ι → X.Opens) sf hsf => ?_
  let 𝒰 : (iSup U).toScheme.OpenCover :=
    { I₀ := ι, X i := (U i).toScheme, f i := X.homOfLE (le_iSup U i),
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, inferInstance⟩
        obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
        exact ⟨i, ⟨x.1, hi⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩ }
  have hglue i j : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (sf i).1 = pullback.snd _ _ ≫ (sf j).1 := by
    refine (cancel_epi (isPullback_opens_inf_le (le_iSup U i) (le_iSup U j)).isoPullback.hom).mp ?_
    simpa only [𝒰, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc,
      homPresheaf_map_val]
      using congrArg Subtype.val (hsf i j)
  refine ⟨⟨𝒰.glueMorphisms (fun i => (sf i).1) hglue, ?_⟩, fun i => ?_, fun s hs => ?_⟩
  · exact 𝒰.hom_ext _ _ fun i => by simp [𝒰.ι_glueMorphisms_assoc, (sf i).2, 𝒰]
  · apply Subtype.ext
    change X.homOfLE _ ≫ 𝒰.glueMorphisms (fun i => (sf i).1) hglue = (sf i).1
    exact 𝒰.ι_glueMorphisms _ _ i
  · exact Subtype.ext (𝒰.hom_ext _ _ fun i => by
      rw [𝒰.ι_glueMorphisms, ← hs i, homPresheaf_map_val])

variable (sX sY) in
/-- The sheaf `F : U ↦ Hom_S(U, Y)` of page 5. -/
noncomputable def homSheaf : TopCat.Sheaf (Type u) X.toTopCat :=
  ⟨homPresheaf sX sY, isSheaf_homPresheaf⟩

@[reassoc]
theorem fromSpecStalkOfMem_homOfLE {U V : X.Opens} (h : U ≤ V) (x : X) (hx : x ∈ U) :
    U.fromSpecStalkOfMem x hx ≫ X.homOfLE h = V.fromSpecStalkOfMem x (h hx) := by
  simp [← cancel_mono V.ι]

@[reassoc]
theorem SpecMap_stalkSpecializes_fromSpecStalkOfMem {U : X.Opens} {x y : X} (h : x ⤳ y)
    (hy : y ∈ U) : Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hy =
      U.fromSpecStalkOfMem x (h.mem_open U.isOpen hy) := by
  simp [← cancel_mono U.ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- Two morphisms `U → Y` that agree on `Spec 𝒪_{X,x}` agree near `x`. -/
theorem exists_homOfLE_eq [IsLocallyNoetherian X] {U : X.Opens} {x : X} (hx : x ∈ U)
    {a b : U.toScheme ⟶ Y} (h : U.fromSpecStalkOfMem x hx ≫ a = U.fromSpecStalkOfMem x hx ≫ b) :
    ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ X.homOfLE hW ≫ a = X.homOfLE hW ≫ b := by
  have := isLocallyNoetherian_of_isOpenImmersion U.ι
  have key : ∀ w : (U : Scheme.{u}), U.toScheme.fromSpecStalk w ≫ a =
      U.toScheme.fromSpecStalk w ≫ b → ∃ V : U.toScheme.Opens, w ∈ V ∧ V.ι ≫ a = V.ι ≫ b :=
    fun w h => spread_out_unique_of_isGermInjective' a b h
  obtain ⟨V, hV, e⟩ := key ⟨x, hx⟩ (by
    rw [← SpecMap_stalkMap_fromSpecStalkOfMem]
    exact (Category.assoc _ _ _).trans ((congrArg (Spec.map _ ≫ ·) h).trans
      (Category.assoc _ _ _).symm))
  refine ⟨U.ι ''ᵁ V, U.ι_image_le V, by exact ⟨_, hV, rfl⟩, ?_⟩
  rw [← Scheme.Opens.isoImage_ι_inv_ι, Category.assoc, Category.assoc, e]

/-- Germs of `F` at `x` are equal iff the morphisms agree on `Spec 𝒪_{X,x}`. -/
theorem germ_homSheaf_eq_iff [IsLocallyNoetherian X] {U V : X.Opens} {x : X} (hU : x ∈ U)
    (hV : x ∈ V) (a : (homPresheaf sX sY).obj (op U)) (b : (homPresheaf sX sY).obj (op V)) :
    (homPresheaf sX sY).germ U x hU a = (homPresheaf sX sY).germ V x hV b ↔
      U.fromSpecStalkOfMem x hU ≫ a.1 = V.fromSpecStalkOfMem x hV ≫ b.1 := by
  constructor
  · intro h
    obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (homPresheaf sX sY) x hU hV a b h
    have e' : X.homOfLE iU.le ≫ a.1 = X.homOfLE iV.le ≫ b.1 := congrArg Subtype.val e
    rw [← fromSpecStalkOfMem_homOfLE iU.le x hW, ← fromSpecStalkOfMem_homOfLE iV.le x hW,
      Category.assoc, Category.assoc, e']
  · intro h
    have hUV : x ∈ U ⊓ V := ⟨hU, hV⟩
    have h' : (U ⊓ V).fromSpecStalkOfMem x hUV ≫ X.homOfLE inf_le_left ≫ a.1 =
        (U ⊓ V).fromSpecStalkOfMem x hUV ≫ X.homOfLE inf_le_right ≫ b.1 := by
      simpa only [fromSpecStalkOfMem_homOfLE_assoc] using h
    obtain ⟨W, hW, hxW, e⟩ := exists_homOfLE_eq hUV h'
    rw [← (homPresheaf sX sY).germ_res_apply (homOfLE (hW.trans inf_le_left)) x hxW a,
      ← (homPresheaf sX sY).germ_res_apply (homOfLE (hW.trans inf_le_right)) x hxW b]
    congr 1
    apply Subtype.ext
    simp only [Scheme.homOfLE_homOfLE_assoc] at e
    exact e

/-- **Lemme 3, local form, on the sheaf.** If `𝒪_{X,y} → 𝒪_{X,x}` is injective, so is `F_y → F_x`,
for `Y` separated over `S`. -/
theorem stalkSpecializes_homSheaf_injective [IsLocallyNoetherian X] [IsSeparated sY] {x y : X}
    (h : x ⤳ y) (hinj : Function.Injective (X.presheaf.stalkSpecializes h)) :
    Function.Injective ((homPresheaf sX sY).stalkSpecializes h) := by
  intro s t hst
  obtain ⟨U, hU, a, rfl⟩ := (homPresheaf sX sY).exists_germ_eq s
  obtain ⟨V, hV, b, rfl⟩ := (homPresheaf sX sY).exists_germ_eq t
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    germ_homSheaf_eq_iff] at hst
  rw [germ_homSheaf_eq_iff]
  apply ext_of_injective_of_isSeparated _ hinj sY
  · simp [a.2, b.2]
  · rw [SpecMap_stalkSpecializes_fromSpecStalkOfMem_assoc,
      SpecMap_stalkSpecializes_fromSpecStalkOfMem_assoc]
    exact hst

/-- **Lemme 3 (page 5), in the page's form.** For `X` locally Noetherian and `Y` separated over
`S`, the sheaf `F : U ↦ Hom_S(U, Y)` satisfies (H). -/
theorem lemme3 [IsLocallyNoetherian X] [IsSeparated sY] : ConditionH (homSheaf sX sY) := by
  intro x
  obtain ⟨U, hxU, hU, hinj⟩ := X.exists_germ_injective x
  exact ⟨U, hxU, fun y ⟨hyU, _⟩ h =>
    stalkSpecializes_homSheaf_injective h (stalkSpecializes_injective h U hU hxU hyU hinj)⟩

/-- **Corollaire 2 (page 5), through the proposition of page 3.** For `X` Noetherian and `Y`
separated over `S`, an `S`-morphism `X → Y` is the same thing
as a coherent family of germs of `F`. -/
theorem corollaire2 [IsNoetherian X] [IsSeparated sY] :
    Function.Bijective (fun s : ToType ((homSheaf sX sY).1.obj (op ⊤)) =>
      (⟨fun x => (homSheaf sX sY).presheaf.germ ⊤ x trivial s, fun _ _ h =>
        (homSheaf sX sY).presheaf.germ_stalkSpecializes_apply (U := ⊤) (hy := trivial) h s⟩ :
        {ξ // IsCoherentGerms (homSheaf sX sY) ξ})) :=
  have : NoetherianSpace X.toTopCat := inferInstanceAs (NoetherianSpace X)
  have : QuasiSober X.toTopCat := inferInstanceAs (QuasiSober X)
  proposition _ lemme3

end Grothendieck.Folder42.Reseau
