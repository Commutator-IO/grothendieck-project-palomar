module

public import Mathlib
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section


/-!
# Folder 158, Proposition 1 (§5.1)

The modernised reading `transcripts/158/158.modern.tex`, §5.1 (manuscript
pages 44–46), states:

> **Proposition 1.** Soit `M` un monoïde *fini* dont le groupe enveloppant est
> trivial et qui est pseudo-cofiltrant. Alors il existe `p ∈ M` tel que
> `up = p` pour tout `u ∈ M` — en particulier `p² = p` — et `M` est cofiltrant.

It is proved here as the reading states it, with no hypothesis added. The
proof follows the reading's three steps:

1. (`etape1`) pseudo-cofilteringness and finiteness give a `p` lying in every
   principal right ideal `uM`;
2. `M` acts on itself by left multiplication, and `E₀ = pM` is contained in
   `u(E₀) = upM` for every `u`; since `E₀` is finite, the inclusion is an
   equality, so each `u` permutes `E₀`;
3. the resulting monoid morphism `M → Perm(E₀)` lands in a group, hence is
   trivial, which gives `up = p`.

What the formalisation shows. The finiteness the reading's footnote flags —
used silently on the leaf to turn `E₀ ⊆ u(E₀)` into `E₀ = u(E₀)` — is exactly
where the proof needs it: `Set.eq_of_subset_of_ncard_le` requires the finiteness
of `u(E₀)`, and `Finite.surjective_iff_bijective` (a surjection of `E₀` onto
itself is a permutation) requires that of `E₀`. Nothing else in the argument
uses finiteness except step 1, where it turns "any two `uM` meet" into "all
of them meet". No hypothesis turned out to be superfluous: without
pseudo-cofilteringness the monoid `{1, a, b}` with `a, b` left zeros
(`xy = x` for `x ≠ 1`) is finite with trivial group completion but has no such
`p`; without finiteness the reading's own §6 (`Ep(E)`, `E` infinite) is the
counterexample (not formalised here).

Conventions. "Pseudo-cofiltrant" is the reading's footnote definition,
`∀ u v, ∃ u' v', u u' = v v'`; "cofiltrant" adds the equalising clause on the
same side, `∀ u v, ∃ w, u w = v w`, which is the side the proof produces.
"Trivial group completion" is stated as: every monoid morphism from `M` to a
group is trivial. The groups quantified over are those in `M`'s universe; the
group completion of `M` lives there, so this is the same condition, and taking
fewer groups only weakens the hypothesis.

What the formalisation found. The Proposition holds as stated, but the
reading's modern gloss on it does not. The gloss says `p` « engendre un idéal
à gauche minimal réduit à un zéro à gauche : c'est le noyau de Rees du monoïde
fini, dont la trivialité du groupe enveloppant force qu'il soit ponctuel ».
`Mp = {p}` is indeed a minimal left ideal; but the kernel (minimal two-sided
ideal) is `MpM = pM`, which need not be a point, and `p` is neither unique nor
a two-sided zero: `contre_noyau_non_ponctuel` exhibits a three-element monoid
satisfying every hypothesis whose kernel has two elements. (Also, `u p = p` for
all `u` makes `p` what semigroup theory usually calls a *right* zero.) mathlib
has no structure theory of finite semigroups (kernels, completely simple
semigroups), so the proof is self-contained.
## Monoids with a minimal element (pages 21 to 41), finding `158-minimal-monoid-cofiltered`

A right `M`-set is `RSet M`; its category of elements has the elements as objects and
`m : x·m → x` as arrows. A functor from it to a group `G` is a cocycle
`c(x, mn) = c(x, m) c(x·m, n)`; `SimplyConnected` says every such cocycle, for every group
`G` in `M`'s universe, is a coboundary `g(x) g(x·m)⁻¹` — for a connected category this is
`π₁ = 1` (the equivalence with the fundamental group is not formalised). `ψ` is minimal if
`ψ ∈ uM` for every `u`.

* `cofiltrant_iff_simplyConnected`: a monoid with a minimal element is cofiltered iff every
  connected right `M`-set has a simply connected category of elements.
* `simplyConnected_of_cofiltrant`: the direction from cofiltered, for any monoid.
* `quotPsi_not_simplyConnected` (pp. 21–33, with `φ = ψ` as in the Corollaire of p. 33):
  if the powers of `ψ` are distinct, the relative degree `q − p` of `ψ^p u = ψ^q v` is a
  `ℤ`-valued cocycle on `M/R_ψ`, of degree `1` on the endomorphism `ψ` of the class of `1`.
* `cofiltrant_iff_rhoMin` (pp. 35–41): if `ψ^r = ψ^s`, `r ≠ s`, a power `e` of `ψ` is a
  minimal idempotent; left multiplication permutes the minimal elements `eM`, and `M` is
  cofiltered iff this representation `M → Perm(eM)` is trivial — otherwise the point fails.

What the formalisation found: the statement holds, and the Corollaire's dichotomy
works with `φ = ψ`: hypotheses (B), (C), (D) of pp. 22–30 reduce to « the powers of `ψ`
are distinct », (D) holding for `φ = ψ` by itself. The degree needs no
least object and no presentation of `π₁` (Proposition 1, p. 19): `ψ^p u = ψ^q u` forces
`p = q` for every `u` because `uM ∋ ψ`. In the other case, that the minimal elements form
`eM`, stable under left multiplication, is what makes `M → Perm(eM)` well defined, the step
p. 41 leaves under its illegible words. The `H¹(−, ℚ)` variant of p. 39 is not formalised.
## Finite categories (pages 50 to 53), finding `158-finite-category-cofiltered`

A presheaf is `Psh X`, with the same cocycle form of « simply connected »; (H), `HypH X`,
says every connected presheaf has a simply connected category of elements.

* `common_ancestor` (the doubling lemma, any category): under (H), two elements of a
  connected presheaf have a common ancestor — otherwise `F` glued to itself along the two
  disjoint subpresheaves they generate is connected and carries a `ℤ`-cocycle that is not a
  coboundary.
* `cone_objs_of_H`, `square_of_H`: (H) with `X` connected gives cones over pairs of objects
  (terminal presheaf) and squares over cospans (representables) — the step « (H) ⇒
  pseudo-cofiltrant » that p. 53 asserts without argument, for any category.
* `isCofiltered_of_H`: a finite, non-empty, connected category satisfying (H) is cofiltered
  (Mathlib's `IsCofiltered`). Proof as on pp. 50–52: an object `e` mapping to every object, a
  minimal idempotent `p` of `End e` (Proposition 1's step 1), the local system
  `L(z) = Hom(e, z) p` on the least objects (bijective transitions by counting), constant by
  (H), which gives `p c f = p c g`.
* `discrete_counterexample`: the discrete category on two objects satisfies (H) and is not
  cofiltered.

What the formalisation found: as read (« a finite category X such that every connected
presheaf… ») the statement is false for disconnected `X`; with `X` connected, as the page
must intend, it holds, and the unargued step holds for every small category.
-/

namespace Grothendieck.Folder158

universe u

/-- **Pseudo-cofiltrant** (the reading's footnote, from manuscript p. 55):
`∀ u, v`, `∃ u', v'` with `u u' = v v'` — any two principal right ideals meet. -/
def PseudoCofiltrant (M : Type u) [Monoid M] : Prop :=
  ∀ u v : M, ∃ u' v' : M, u * u' = v * v'

/-- **Cofiltrant**: pseudo-cofiltrant, and any two parallel arrows (here, any
two elements) are equalised further on: `∀ u, v`, `∃ w` with `u w = v w`. -/
def Cofiltrant (M : Type u) [Monoid M] : Prop :=
  PseudoCofiltrant M ∧ ∀ u v : M, ∃ w : M, u * w = v * w

/-- **Groupe enveloppant trivial**: every monoid morphism from `M` to a group is
trivial (the universal property of the group completion, for groups in `M`'s
universe, where the group completion lives). -/
def GroupeEnveloppantTrivial (M : Type u) [Monoid M] : Prop :=
  ∀ (G : Type u) [Group G] (f : M →* G), f = 1

variable {M : Type u} [Monoid M]

/-- **Step 1.** In a finite pseudo-cofiltering monoid, some `p` lies in every
principal right ideal: for every `u` there is `v` with `p = u v`. -/
theorem etape1 [Finite M] (h : PseudoCofiltrant M) :
    ∃ p : M, ∀ u : M, ∃ v : M, p = u * v := by
  classical
  have key : ∀ s : Finset M, ∃ p : M, ∀ u ∈ s, ∃ v : M, p = u * v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a s _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨p', v', e⟩ := h p a
      refine ⟨p * p', (Finset.forall_mem_insert _ _ _).2 ⟨⟨v', e⟩, fun u hu => ?_⟩⟩
      obtain ⟨v, hv⟩ := hp u hu
      exact ⟨v * p', by rw [hv, mul_assoc]⟩
  have := Fintype.ofFinite M
  exact (key Finset.univ).imp fun p hp u => hp u (Finset.mem_univ u)

/-- **Proposition 1.** Let `M` be a finite pseudo-cofiltering monoid with
trivial group completion. Then there is `p ∈ M` with `u p = p` for every
`u ∈ M`; in particular `p² = p`, and `M` is cofiltering. -/
theorem proposition1 [Finite M] (hpc : PseudoCofiltrant M)
    (hG : GroupeEnveloppantTrivial M) :
    ∃ p : M, (∀ u : M, u * p = p) ∧ p * p = p ∧ Cofiltrant M := by
  obtain ⟨p, hp⟩ := etape1 hpc
  -- `E₀ = pM`, the image of `p` in the regular representation.
  let E₀ : Set M := Set.range (p * ·)
  -- `E₀ ⊆ u(E₀)`, because `p ∈ upM`.
  have hsub : ∀ u : M, E₀ ⊆ (u * ·) '' E₀ := by
    rintro u x ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := hp (u * p)
    refine ⟨p * (v * y), ⟨v * y, rfl⟩, ?_⟩
    change u * (p * (v * y)) = p * y
    rw [← mul_assoc, ← mul_assoc, ← hv]
  -- Finiteness of `E₀` turns the inclusion into an equality.
  have heq : ∀ u : M, (u * ·) '' E₀ = E₀ := fun u =>
    (Set.eq_of_subset_of_ncard_le (hsub u) (Set.ncard_image_le (Set.toFinite _))
      (Set.toFinite _)).symm
  -- So each `u` maps `E₀` onto itself, bijectively since `E₀` is finite.
  let f : M → E₀ → E₀ := fun u x =>
    ⟨u * x, (heq u).subset ⟨x, x.2, rfl⟩⟩
  have hbij : ∀ u : M, Function.Bijective (f u) := fun u =>
    Finite.surjective_iff_bijective.1 fun y => by
      obtain ⟨x, hx, e⟩ : (y : M) ∈ (u * ·) '' E₀ := (heq u).symm.subset y.2
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  -- The restriction `u ↦ u|E₀` is a morphism into the group `Perm E₀` …
  let φ : M →* Equiv.Perm E₀ :=
    { toFun := fun u => Equiv.ofBijective (f u) (hbij u)
      map_one' := by ext x; simp [f]
      map_mul' := fun a b => by ext x; simp [f, mul_assoc] }
  -- … hence trivial, which gives `u p = p`.
  have hup : ∀ u : M, u * p = p := fun u => by
    simpa [φ, f] using congrArg (fun σ : Equiv.Perm E₀ => (σ ⟨p, 1, mul_one p⟩ : M))
      (DFunLike.congr_fun (hG _ φ) u)
  exact ⟨p, hup, hup p, hpc, fun u v => ⟨p, by rw [hup u, hup v]⟩⟩

/-! ### The modern gloss: the kernel need not be a point

The reading glosses Proposition 1 as: « `p` est un idempotent qui engendre un
idéal à gauche minimal réduit à un zéro à gauche : c'est le noyau de Rees du
monoïde fini, dont la trivialité du groupe enveloppant force qu'il soit
ponctuel ». The first half is right (`Mp = {p}` is a minimal left ideal, and
`p` absorbs whatever multiplies it on the left, i.e. `p` is what semigroup
theory usually calls a *right* zero). The second half is false: the kernel
(the minimal two-sided ideal) is `MpM = pM`, which need not be a point, and
`p` is neither unique nor a two-sided zero.

The counterexample is the smallest one: two right zeros `a`, `b`
(`xa = a`, `xb = b` for all `x`) with an identity adjoined. -/

/-- The monoid `{1, a, b}` with `x a = a` and `x b = b` for every `x`. -/
inductive Contre
  | un
  | a
  | b
  deriving DecidableEq

instance : Fintype Contre :=
  ⟨{.un, .a, .b}, fun x => by cases x <;> decide⟩

instance : Monoid Contre where
  mul x y := match y with
    | .un => x
    | .a => .a
    | .b => .b
  one := .un
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl

/-- `{1, a, b}` is pseudo-cofiltering: `u a = v a` for all `u, v`. -/
theorem contre_pseudoCofiltrant : PseudoCofiltrant Contre := fun u v =>
  ⟨.a, .a, by cases u <;> cases v <;> rfl⟩

/-- `{1, a, b}` has trivial group completion: `a = b a` forces `b ↦ 1`, and
`b = a b` forces `a ↦ 1`. -/
theorem contre_groupeEnveloppantTrivial : GroupeEnveloppantTrivial Contre := by
  intro G _ f
  have hb : f .b = 1 := mul_right_cancel ((f.map_mul .b .a).symm.trans (one_mul (f .a)).symm)
  have ha : f .a = 1 := mul_right_cancel ((f.map_mul .a .b).symm.trans (one_mul (f .b)).symm)
  ext x
  cases x
  exacts [f.map_one, ha, hb]

/-- The kernel of a monoid: the intersection of its principal two-sided ideals
`MxM` (equivalently of all its non-empty two-sided ideals; for a finite monoid
it is the minimal ideal, the Suschkewitsch–Rees kernel). -/
def noyau (M : Type u) [Monoid M] : Set M :=
  ⋂ x : M, {y | ∃ s t : M, y = s * x * t}

/-- **The gloss fails.** `{1, a, b}` satisfies the hypotheses of Proposition 1,
yet two distinct elements `a ≠ b` both satisfy `u p = p` for all `u`, neither
is a two-sided zero (`a b = b`), and the kernel is `{a, b}`, not a point. -/
theorem contre_noyau_non_ponctuel :
    PseudoCofiltrant Contre ∧ GroupeEnveloppantTrivial Contre ∧
      (∀ u : Contre, u * .a = .a) ∧ (∀ u : Contre, u * .b = .b) ∧
      Contre.a ≠ Contre.b ∧ Contre.a * Contre.b ≠ Contre.a ∧
      noyau Contre = {Contre.a, Contre.b} := by
  refine ⟨contre_pseudoCofiltrant, contre_groupeEnveloppantTrivial,
    fun u => by cases u <;> rfl, fun u => by cases u <;> rfl, by decide, by decide, ?_⟩
  ext y
  simp only [noyau, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  revert y
  decide

/-! ## Monoids with a minimal element (pages 21 to 41), finding `158-minimal-monoid-cofiltered`

A right `M`-set `X` is a presheaf on `B_M`; its category of elements `B_M/X` has the
elements of `X` as objects and `m : x·m → x` as arrows. A functor `B_M/X → B G`, `G` a
group, is a cocycle `c : X × M → G`, `c(x, 1) = 1`, `c(x, mn) = c(x, m) c(x·m, n)`; it is
isomorphic to the trivial functor iff `c(x, m) = g(x) g(x·m)⁻¹` for some `g`. For a
connected category, « every such functor is trivial, for every group `G` » is
`π₁ = 1`; this is the form of « simply connected » used here. -/

/-- A right `M`-set. -/
structure RSet (M : Type u) [Monoid M] where
  /-- The underlying type. -/
  carrier : Type u
  /-- The action `x·m`. -/
  act : carrier → M → carrier
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x m n, act x (m * n) = act (act x m) n

namespace RSet

/-- `X` is connected: non-empty, and any two elements are joined by a zigzag of arrows. -/
def Connected (X : RSet M) : Prop :=
  Nonempty X.carrier ∧ ∀ x y, Relation.EqvGen (fun a b => ∃ m, X.act a m = b) x y

/-- The category of elements of `X` is simply connected: every functor from it to a
group `G`, i.e. every cocycle, is a coboundary. -/
def SimplyConnected (X : RSet M) : Prop :=
  ∀ (G : Type u) [Group G] (c : X.carrier → M → G), (∀ x, c x 1 = 1) →
    (∀ x m n, c x (m * n) = c x m * c (X.act x m) n) →
      ∃ g : X.carrier → G, ∀ x m, c x m = g x * (g (X.act x m))⁻¹

end RSet

/-- `ψ` is minimal: it lies in every principal right ideal `uM`. -/
def Minimal (ψ : M) : Prop := ∀ u : M, ∃ t : M, u * t = ψ

/-! ### Cofiltered implies simply connected -/

/-- Over a cofiltered monoid, the category of elements of a connected `M`-set is simply
connected. -/
theorem simplyConnected_of_cofiltrant (hM : Cofiltrant M) (X : RSet M) (hX : X.Connected) :
    X.SimplyConnected := by
  intro G _ c c1 cmul
  obtain ⟨⟨x₀⟩, hconn⟩ := hX
  -- any two elements have a common descendant
  have common : ∀ x y, ∃ a b, X.act x a = X.act y b := by
    intro x y
    induction hconn x y with
    | rel a b h =>
      obtain ⟨m, rfl⟩ := h
      exact ⟨m, 1, by rw [X.act_one]⟩
    | refl a => exact ⟨1, 1, rfl⟩
    | symm a b _ ih =>
      obtain ⟨p, q, e⟩ := ih
      exact ⟨q, p, e.symm⟩
    | trans a b d _ _ ih₁ ih₂ =>
      obtain ⟨p, q, e₁⟩ := ih₁
      obtain ⟨r, s, e₂⟩ := ih₂
      obtain ⟨q', r', e⟩ := hM.1 q r
      refine ⟨p * q', s * r', ?_⟩
      rw [X.act_mul, e₁, ← X.act_mul, e, X.act_mul, e₂, ← X.act_mul]
  -- parallel arrows have the same value
  have par : ∀ x m n, X.act x m = X.act x n → c x m = c x n := by
    intro x m n h
    obtain ⟨w, hw⟩ := hM.2 m n
    have e := cmul x m w
    rw [hw, cmul x n w, h] at e
    exact (mul_right_cancel e).symm
  -- path independence
  have indep : ∀ x a b a₂ b₂, X.act x a = X.act x₀ b → X.act x a₂ = X.act x₀ b₂ →
      c x a * (c x₀ b)⁻¹ = c x a₂ * (c x₀ b₂)⁻¹ := by
    intro x a b a₂ b₂ h h₂
    obtain ⟨a', a₂', e⟩ := hM.1 a a₂
    have k₀ : c x₀ (b * a') = c x₀ (b₂ * a₂') := par _ _ _ (by
      rw [X.act_mul, X.act_mul, ← h, ← h₂, ← X.act_mul, ← X.act_mul, e])
    have k : c x (a * a') = c x (a₂ * a₂') := by rw [e]
    rw [cmul, cmul, ← h, ← h₂] at k₀
    rw [cmul, cmul] at k
    calc c x a * (c x₀ b)⁻¹ = c x a * c (X.act x a) a' * (c x₀ b * c (X.act x a) a')⁻¹ := by
          group
      _ = c x a₂ * c (X.act x a₂) a₂' * (c x₀ b₂ * c (X.act x a₂) a₂')⁻¹ := by rw [k, k₀]
      _ = c x a₂ * (c x₀ b₂)⁻¹ := by group
  choose a b hab using fun x => common x x₀
  refine ⟨fun x => c x (a x) * (c x₀ (b x))⁻¹, fun x m => ?_⟩
  have e := indep x (a x) (b x) (m * a (X.act x m)) (b (X.act x m)) (hab x)
    (by rw [X.act_mul, hab])
  beta_reduce
  rw [e, cmul]
  group

/-! ### The point: a monoid with a minimal idempotent -/

/-- The point, as a right `M`-set. -/
def RSet.point (M : Type u) [Monoid M] : RSet M where
  carrier := PUnit
  act _ _ := PUnit.unit
  act_one _ := rfl
  act_mul _ _ _ := rfl

/-- The category of elements of the point is `B_M`: a non-trivial morphism from `M` to a
group makes it not simply connected. -/
theorem point_not_simplyConnected {G : Type u} [Group G] (ρ : M →* G) (hρ : ρ ≠ 1) :
    ¬ (RSet.point M).SimplyConnected := by
  intro h
  obtain ⟨g, hg⟩ := h G (fun _ m => ρ m) (fun _ => ρ.map_one) (fun _ m n => ρ.map_mul m n)
  refine hρ (MonoidHom.ext fun m => ?_)
  have := hg PUnit.unit m
  change ρ m = g PUnit.unit * (g PUnit.unit)⁻¹ at this
  rw [this, mul_inv_cancel, MonoidHom.one_apply]

/-- The right multiples of a minimal element are minimal. -/
theorem Minimal.mul {ψ : M} (h : Minimal ψ) (m : M) : Minimal (ψ * m) := fun u => by
  obtain ⟨t, ht⟩ := h u
  exact ⟨t * m, by rw [← mul_assoc, ht]⟩

/-- The left multiples of a minimal element `λ` stay in `λM`. -/
theorem Minimal.left_mul {l : M} (h : Minimal l) (u : M) : ∃ j, u * l = l * j := by
  obtain ⟨k, hk⟩ := h (u * l)
  obtain ⟨j, hj⟩ := h (l * k)
  exact ⟨j, by rw [← hj, ← mul_assoc, ← mul_assoc, hk, hj]⟩

section Idempotent

variable {e : M} (he : Minimal e) (hee : e * e = e)
include he hee

/-- `eM`, the minimal elements when `e` is a minimal idempotent. -/
abbrev Emin (e : M) := {x : M // e * x = x}

theorem emin_mul (u : M) (x : Emin e) : e * (u * x) = u * x := by
  obtain ⟨j, hj⟩ := he.left_mul u
  calc e * (u * x) = e * (u * (e * x)) := by rw [x.2]
    _ = e * (e * j * x) := by rw [← mul_assoc u, hj]
    _ = e * j * x := by rw [← mul_assoc, ← mul_assoc, hee]
    _ = u * x := by rw [← hj, mul_assoc, x.2]

/-- Left multiplication by `u` is a bijection of `eM`: `x ↦ e k₂ x` is its inverse, where
`u e k = e` and `e k e k₂ = e`. -/
theorem emin_bijective (u : M) :
    Function.Bijective (fun x : Emin e => (⟨u * x, emin_mul he hee u x⟩ : Emin e)) := by
  obtain ⟨k, hk⟩ := he (u * e)
  obtain ⟨k₂, hk₂⟩ := he (e * k * e)
  have hfg : ∀ y : M, e * y = y → u * (e * k * y) = y := fun y hy => by
    rw [← mul_assoc, ← mul_assoc, hk, hy]
  have hgh : ∀ y : M, e * y = y → e * k * (e * k₂ * y) = y := fun y hy => by
    rw [← mul_assoc, ← mul_assoc, hk₂, hy]
  have hE : ∀ (a y : M), e * (e * a * y) = e * a * y := fun a y => by
    rw [← mul_assoc, ← mul_assoc, hee]
  have hfh : ∀ x : M, e * x = x → u * x = e * k₂ * x := fun x hx => by
    conv_lhs => rw [← hgh x hx]
    exact hfg _ (hE k₂ x)
  constructor
  · intro x y hxy
    have h : u * (x : M) = u * y := congrArg Subtype.val hxy
    rw [hfh x x.2, hfh y y.2] at h
    apply Subtype.ext
    rw [← hgh x x.2, ← hgh y y.2, h]
  · intro y
    exact ⟨⟨e * k * y, hE k y⟩, Subtype.ext (hfg y y.2)⟩

/-- The representation of `M` on its minimal elements `eM`, a morphism to a group. -/
noncomputable def rhoMin : M →* Equiv.Perm (Emin e) where
  toFun u := Equiv.ofBijective _ (emin_bijective he hee u)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [mul_assoc]

/-- With a minimal idempotent, `M` is cofiltered iff its representation on `eM` is trivial;
otherwise the point has a category of elements that is not simply connected. -/
theorem cofiltrant_iff_rhoMin : Cofiltrant M ↔ rhoMin he hee = 1 := by
  constructor
  · intro hM
    ext u x
    obtain ⟨w, hw⟩ := hM.2 u 1
    obtain ⟨t, ht⟩ := (show Minimal (x : M) by rw [← x.2]; exact he.mul _) w
    change u * (x : M) = x
    rw [← ht, ← mul_assoc, hw, one_mul]
  · intro h
    have hu : ∀ u : M, u * e = e := fun u => by
      simpa [rhoMin] using congrArg (fun σ : Equiv.Perm (Emin e) => ((σ ⟨e, hee⟩ : Emin e) : M))
        (DFunLike.congr_fun h u)
    refine ⟨fun u v => ?_, fun u v => ⟨e, by rw [hu, hu]⟩⟩
    obtain ⟨t, ht⟩ := he u
    obtain ⟨t', ht'⟩ := he v
    exact ⟨t, t', by rw [ht, ht']⟩

end Idempotent

/-- Two equal powers `ψ^r = ψ^s`, `r < s`, give an idempotent power `ψ^n`, `n ≥ 1`. -/
theorem exists_idem_pow {ψ : M} {r s : ℕ} (hrs : r < s) (h : ψ ^ r = ψ ^ s) :
    ∃ n, 1 ≤ n ∧ ψ ^ n * ψ ^ n = ψ ^ n := by
  have step : ∀ m, r ≤ m → ψ ^ (m + (s - r)) = ψ ^ m := fun m hm => by
    rw [show m + (s - r) = (m - r) + s by omega, pow_add, ← h, ← pow_add,
      Nat.sub_add_cancel hm]
  have iter : ∀ j m, r ≤ m → ψ ^ (m + j * (s - r)) = ψ ^ m := by
    intro j
    induction j with
    | zero => intro m _; simp
    | succ j ih =>
      intro m hm
      rw [show m + (j + 1) * (s - r) = (m + j * (s - r)) + (s - r) by
        rw [Nat.succ_mul, Nat.add_assoc],
        step _ (by omega), ih m hm]
  have hpos : 0 < s - r := by omega
  refine ⟨(r + 1) * (s - r), Nat.mul_pos (Nat.succ_pos r) hpos, ?_⟩
  rw [← pow_add, iter (r + 1) _ ((Nat.le_succ r).trans (Nat.le_mul_of_pos_right _ hpos))]

/-! ### The quotient `M/R_ψ` (pages 21 to 33) -/

/-- `u R_ψ v` iff `ψ^p u = ψ^q v` for some `p, q`. -/
def psiSetoid (ψ : M) : Setoid M where
  r u v := ∃ p q : ℕ, ψ ^ p * u = ψ ^ q * v
  iseqv := by
    refine ⟨fun u => ⟨0, 0, rfl⟩, fun ⟨p, q, h⟩ => ⟨q, p, h.symm⟩, ?_⟩
    rintro u v w ⟨p, q, h⟩ ⟨p', q', h'⟩
    refine ⟨p' + p, q + q', ?_⟩
    calc ψ ^ (p' + p) * u = ψ ^ p' * (ψ ^ p * u) := by rw [pow_add, mul_assoc]
      _ = ψ ^ q * (ψ ^ p' * v) := by
          rw [h, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, add_comm]
      _ = ψ ^ (q + q') * w := by rw [h', ← mul_assoc, ← pow_add]

/-- The right `M`-set `F = M/R_ψ`. -/
def quotPsi (ψ : M) : RSet M where
  carrier := Quotient (psiSetoid ψ)
  act x m := Quotient.map (· * m) (fun _ _ hab => by
    obtain ⟨p, q, h⟩ := hab
    exact ⟨p, q, by rw [← mul_assoc, h, mul_assoc]⟩) x
  act_one x := Quotient.inductionOn x fun _ => by simp [Quotient.map_mk]
  act_mul x m n := Quotient.inductionOn x fun _ => by simp [Quotient.map_mk, mul_assoc]

theorem quotPsi_act_mk (ψ u m : M) :
    (quotPsi ψ).act (Quotient.mk _ u) m = Quotient.mk (psiSetoid ψ) (u * m) := rfl

/-- `M/R_ψ` is connected: every class is joined to the class of `1`. -/
theorem quotPsi_connected (ψ : M) : (quotPsi ψ).Connected := by
  have h1 : ∀ x : (quotPsi ψ).carrier, Relation.EqvGen
      (fun a b => ∃ m, (quotPsi ψ).act a m = b) (Quotient.mk _ 1) x :=
    fun x => Quotient.inductionOn x fun u =>
      Relation.EqvGen.rel _ _ ⟨u, by rw [quotPsi_act_mk, one_mul]⟩
  exact ⟨⟨Quotient.mk _ 1⟩, fun x y => (h1 x).symm _ _ |>.trans _ _ _ (h1 y)⟩

section Degree

variable {ψ : M} (hψ : Minimal ψ) (hinf : ∀ r s : ℕ, ψ ^ r = ψ ^ s → r = s)
include hψ hinf

/-- For every `u`, `k ↦ ψ^k u` is injective (with `ut = ψ`, `ψ^p u = ψ^q u` gives
`ψ^{p+1} = ψ^{q+1}`). -/
theorem pow_mul_inj {u : M} {p q : ℕ} (h : ψ ^ p * u = ψ ^ q * u) : p = q := by
  obtain ⟨t, ht⟩ := hψ u
  have := congrArg (· * t) h
  simp only [mul_assoc, ht, ← pow_succ] at this
  exact Nat.succ_injective (hinf _ _ this)

omit hψ hinf in
open Classical in
/-- The relative degree `q − p` of `u R_ψ v`, `ψ^p u = ψ^q v`. -/
noncomputable def deg (ψ u v : M) : ℤ :=
  if h : ∃ p q : ℕ, ψ ^ p * u = ψ ^ q * v then (h.choose_spec.choose : ℤ) - h.choose else 0

theorem deg_eq {u v : M} {p q : ℕ} (h : ψ ^ p * u = ψ ^ q * v) : deg ψ u v = q - p := by
  unfold deg
  split_ifs with hex
  swap
  · exact absurd ⟨p, q, h⟩ hex
  have h₀ := hex.choose_spec.choose_spec
  set p₀ := hex.choose
  set q₀ := hex.choose_spec.choose
  have e : ψ ^ (p₀ + q) * v = ψ ^ (p + q₀) * v := by
    calc ψ ^ (p₀ + q) * v = ψ ^ p₀ * (ψ ^ p * u) := by rw [h, ← mul_assoc, pow_add]
      _ = ψ ^ p * (ψ ^ p₀ * u) := by rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, add_comm]
      _ = ψ ^ (p + q₀) * v := by rw [h₀, ← mul_assoc, pow_add]
  have := pow_mul_inj hψ hinf e
  omega

theorem deg_add {u v w : M} (h₁ : (psiSetoid ψ).r u v) (h₂ : (psiSetoid ψ).r v w) :
    deg ψ u w = deg ψ u v + deg ψ v w := by
  obtain ⟨p, q, h⟩ := h₁
  obtain ⟨p', q', h'⟩ := h₂
  have h'' : ψ ^ (p' + p) * u = ψ ^ (q + q') * w := by
    calc ψ ^ (p' + p) * u = ψ ^ p' * (ψ ^ p * u) := by rw [pow_add, mul_assoc]
      _ = ψ ^ q * (ψ ^ p' * v) := by
          rw [h, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, add_comm]
      _ = ψ ^ (q + q') * w := by rw [h', ← mul_assoc, ← pow_add]
  rw [deg_eq hψ hinf h, deg_eq hψ hinf h', deg_eq hψ hinf h'']
  push_cast; ring

theorem deg_mul {u v : M} (h : (psiSetoid ψ).r u v) (m : M) :
    deg ψ (u * m) (v * m) = deg ψ u v := by
  obtain ⟨p, q, h⟩ := h
  rw [deg_eq hψ hinf h, deg_eq hψ hinf (p := p) (q := q) (by rw [← mul_assoc, h, mul_assoc])]

omit hψ hinf in
theorem rel_mul {u v : M} (h : (psiSetoid ψ).r u v) (m : M) : (psiSetoid ψ).r (u * m) (v * m) := by
  obtain ⟨p, q, h⟩ := h
  exact ⟨p, q, by rw [← mul_assoc, h, mul_assoc]⟩

omit hψ hinf in
theorem out_rel (x : Quotient (psiSetoid ψ)) (m : M) :
    (psiSetoid ψ).r (x.out * m) ((quotPsi ψ).act x m).out := by
  apply Quotient.exact
  have e : (quotPsi ψ).act x m = Quotient.mk _ (x.out * m) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  exact e.symm.trans (Quotient.out_eq (s := psiSetoid ψ) ((quotPsi ψ).act x m)).symm

/-- **Pages 21 to 33, the degree.** If `ψ` is minimal and its powers are distinct, the
category of elements of `M/R_ψ` is not simply connected: the relative degree is a cocycle
with values in `ℤ`, and the endomorphism `ψ` of the class of `1 = ψ` has degree `1`. -/
theorem quotPsi_not_simplyConnected : ¬ (quotPsi ψ).SimplyConnected := by
  intro hS
  let c : (quotPsi ψ).carrier → M → Multiplicative (ULift.{u} ℤ) := fun x m =>
    Multiplicative.ofAdd (ULift.up (deg ψ (x.out * m) ((quotPsi ψ).act x m).out))
  have c1 : ∀ x, c x 1 = 1 := fun x => by
    simp only [c, mul_one, (quotPsi ψ).act_one]
    rw [deg_eq hψ hinf (p := 0) (q := 0) rfl]
    rfl
  have cmul : ∀ x m n, c x (m * n) = c x m * c ((quotPsi ψ).act x m) n := fun x m n => by
    have r₁ := out_rel x m
    have r₂ := out_rel ((quotPsi ψ).act x m) n
    have key : deg ψ (x.out * (m * n)) ((quotPsi ψ).act x (m * n)).out =
        deg ψ (x.out * m) ((quotPsi ψ).act x m).out +
          deg ψ (((quotPsi ψ).act x m).out * n) ((quotPsi ψ).act ((quotPsi ψ).act x m) n).out := by
      rw [(quotPsi ψ).act_mul, ← mul_assoc, deg_add hψ hinf (rel_mul r₁ n) r₂, deg_mul hψ hinf r₁]
    simp only [c, key]
    rfl
  obtain ⟨g, hg⟩ := hS _ c c1 cmul
  -- the endomorphism `ψ` of the class of `1`
  set x : (quotPsi ψ).carrier := Quotient.mk _ 1
  have hx : (quotPsi ψ).act x ψ = x := Quotient.sound ⟨0, 1, by simp⟩
  have h1 := hg x ψ
  rw [hx, mul_inv_cancel] at h1
  have h0 : deg ψ (x.out * ψ) x.out = 0 := by
    have := congrArg (fun z : Multiplicative (ULift.{u} ℤ) => (Multiplicative.toAdd z).down) h1
    simpa [c, hx] using this
  obtain ⟨p, q, hpq⟩ : (psiSetoid ψ).r x.out 1 := Quotient.exact (Quotient.out_eq x)
  have e : ψ ^ p * (x.out * ψ) = ψ ^ (p + 1) * x.out := by
    rw [← mul_assoc, hpq, mul_one, pow_succ', mul_assoc, hpq, mul_one, ← pow_succ, ← pow_succ']
  rw [deg_eq hψ hinf e] at h0
  push_cast at h0
  omega

end Degree

/-- The point is connected. -/
theorem point_connected : (RSet.point M).Connected :=
  ⟨⟨PUnit.unit⟩, fun _ _ => Relation.EqvGen.refl _⟩

/-- **Pages 21 to 41, the Corollaire of page 39 in its simply connected form.** Let `M` be
a monoid with a minimal element `ψ` (`ψ ∈ uM` for every `u`). If every connected right
`M`-set has a simply connected category of elements, then `M` is cofiltered. Otherwise
the folder's witness fails: `M/R_ψ` when the powers of `ψ` are distinct
(`quotPsi_not_simplyConnected`), the point when some power `e` of `ψ` is idempotent, the
image of `M` in the permutations of its minimal elements `eM` being then a non-trivial
group (`cofiltrant_iff_rhoMin`). -/
theorem cofiltrant_of_simplyConnected {ψ : M} (hψ : Minimal ψ)
    (h : ∀ X : RSet M, X.Connected → X.SimplyConnected) : Cofiltrant M := by
  by_cases hinf : ∀ r s : ℕ, ψ ^ r = ψ ^ s → r = s
  · exact absurd (h _ (quotPsi_connected ψ)) (quotPsi_not_simplyConnected hψ hinf)
  push Not at hinf
  obtain ⟨r, s, hrs, hne⟩ := hinf
  obtain ⟨n, hn, hidem⟩ : ∃ n, 1 ≤ n ∧ ψ ^ n * ψ ^ n = ψ ^ n := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact exists_idem_pow hlt hrs
    · exact exists_idem_pow hlt hrs.symm
  have he : Minimal (ψ ^ n) := by
    rw [show n = 1 + (n - 1) by omega, pow_add, pow_one]
    exact hψ.mul _
  rw [cofiltrant_iff_rhoMin he hidem]
  by_contra hρ
  exact point_not_simplyConnected _ hρ (h _ point_connected)

/-- **The equivalence.** For a monoid with a minimal element, `M` is cofiltered if and only
if every connected right `M`-set has a simply connected category of elements. -/
theorem cofiltrant_iff_simplyConnected {ψ : M} (hψ : Minimal ψ) :
    Cofiltrant M ↔ ∀ X : RSet M, X.Connected → X.SimplyConnected :=
  ⟨simplyConnected_of_cofiltrant, cofiltrant_of_simplyConnected hψ⟩

open CategoryTheory

/-! ## Finite categories (pages 50 to 53), finding `158-finite-category-cofiltered` -/

universe v w

/-- A presheaf on `X`: `map k : F z → F z'` for `k : z' ⟶ z`. Its category of elements has
the pairs `(z, t)` as objects and `k : (z', F k t) → (z, t)` as arrows. -/
structure Psh (X : Type w) [Category.{v} X] where
  /-- The value at an object. -/
  obj : X → Type v
  /-- The restriction along an arrow. -/
  map : ∀ {z z' : X}, (z' ⟶ z) → obj z → obj z'
  map_id : ∀ z t, map (𝟙 z) t = t
  map_comp : ∀ {z z' z'' : X} (k' : z'' ⟶ z') (k : z' ⟶ z) t, map (k' ≫ k) t = map k' (map k t)

namespace Psh

variable {X : Type w} [Category.{v} X]

/-- The category of elements of `F` is connected. -/
def Connected (F : Psh X) : Prop :=
  Nonempty (Σ z, F.obj z) ∧ ∀ a b : Σ z, F.obj z,
    Relation.EqvGen (fun a b : Σ z, F.obj z => ∃ k : b.1 ⟶ a.1, b.2 = F.map k a.2) a b

/-- The category of elements of `F` is simply connected: every functor from it to a group,
i.e. every cocycle, is a coboundary. -/
def SimplyConnected (F : Psh X) : Prop :=
  ∀ (G : Type v) [Group G] (c : ∀ {z z' : X}, (z' ⟶ z) → F.obj z → G),
    (∀ z t, c (𝟙 z) t = 1) →
    (∀ {z z' z'' : X} (k' : z'' ⟶ z') (k : z' ⟶ z) t,
      c (k' ≫ k) t = c k t * c k' (F.map k t)) →
    ∃ g : ∀ z, F.obj z → G, ∀ {z z' : X} (k : z' ⟶ z) t, c k t = g z t * (g z' (F.map k t))⁻¹

/-- The terminal presheaf; its category of elements is `X`. -/
def terminal (X : Type w) [Category.{v} X] : Psh X where
  obj _ := PUnit
  map _ _ := PUnit.unit
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

/-- The representable presheaf `Hom(−, c)`. -/
def yo {X : Type w} [Category.{v} X] (c : X) : Psh X where
  obj z := z ⟶ c
  map k f := k ≫ f
  map_id _ _ := Category.id_comp _
  map_comp _ _ _ := Category.assoc _ _ _

theorem yo_connected (c : X) : (yo c).Connected := by
  have h : ∀ a : Σ z, (yo c).obj z, Relation.EqvGen
      (fun a b : Σ z, (yo c).obj z => ∃ k : b.1 ⟶ a.1, b.2 = (yo c).map k a.2) ⟨c, 𝟙 c⟩ a :=
    fun a => Relation.EqvGen.rel _ _ ⟨a.2, (Category.comp_id _).symm⟩
  exact ⟨⟨⟨c, 𝟙 c⟩⟩, fun a b => ((h a).symm _ _).trans _ _ _ (h b)⟩

end Psh

/-- Hypothesis (H): every connected presheaf has a simply connected category of elements. -/
def HypH (X : Type w) [Category.{v} X] : Prop :=
  ∀ F : Psh X, F.Connected → F.SimplyConnected

/-- A predicate that respects a relation in both directions respects its equivalence
closure. -/
theorem eqvGen_iff {α : Type*} {r : α → α → Prop} {Q : α → Prop}
    (h : ∀ a b, r a b → (Q a ↔ Q b)) {a b : α} (hab : Relation.EqvGen r a b) : Q a ↔ Q b := by
  induction hab with
  | rel a b hr => exact h a b hr
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Doubling

variable {X : Type w} [Category.{v} X]

open Classical in
/-- **The doubling lemma.** Under (H), any two elements `ξ`, `η` of a connected presheaf
have a common ancestor. Otherwise the subpresheaves `T₁`, `T₂` they generate are disjoint,
the presheaf `F ⊔_{T₁ ⊔ T₂} F` (two copies of `F` glued along `T₁ ⊔ T₂`) is connected, and
counting the arrows from `T₁` into the second copy is a `ℤ`-valued cocycle that is not a
coboundary. -/
theorem common_ancestor (H : HypH X) (F : Psh X) (hF : F.Connected) {a b : X}
    (ξ : F.obj a) (η : F.obj b) :
    ∃ (w : X) (u : w ⟶ a) (u' : w ⟶ b), F.map u ξ = F.map u' η := by
  by_contra hdis
  push Not at hdis
  -- the subpresheaves generated by `ξ` and `η`
  let T₁ : ∀ z, F.obj z → Prop := fun z t => ∃ u : z ⟶ a, t = F.map u ξ
  let T₂ : ∀ z, F.obj z → Prop := fun z t => ∃ u : z ⟶ b, t = F.map u η
  have T₁map : ∀ {z z'} (k : z' ⟶ z) t, T₁ z t → T₁ z' (F.map k t) := by
    rintro z z' k t ⟨u, rfl⟩; exact ⟨k ≫ u, (F.map_comp k u ξ).symm⟩
  have T₂map : ∀ {z z'} (k : z' ⟶ z) t, T₂ z t → T₂ z' (F.map k t) := by
    rintro z z' k t ⟨u, rfl⟩; exact ⟨k ≫ u, (F.map_comp k u η).symm⟩
  have disj : ∀ z t, T₁ z t → T₂ z t → False := by
    rintro z t ⟨u, rfl⟩ ⟨u', hu'⟩; exact hdis z u u' hu'
  let T : ∀ z, F.obj z → Prop := fun z t => T₁ z t ∨ T₂ z t
  have Tmap : ∀ {z z'} (k : z' ⟶ z) t, T z t → T z' (F.map k t) := fun k t h =>
    h.imp (T₁map k t) (T₂map k t)
  -- the doubled presheaf
  let D : Psh X :=
    { obj := fun z => {q : F.obj z × Bool // T z q.1 → q.2 = false}
      map := fun {z z'} k q => ⟨(F.map k q.1.1, if T z' (F.map k q.1.1) then false else q.1.2),
        fun h => by simp [h]⟩
      map_id := fun z q => by
        refine Subtype.ext (Prod.ext (F.map_id _ _) ?_)
        simp only [F.map_id]
        by_cases h : T z q.1.1
        · simp [h, q.2 h]
        · simp [h]
      map_comp := fun k' k q => by
        refine Subtype.ext (Prod.ext (F.map_comp _ _ _) ?_)
        simp only [F.map_comp]
        by_cases h'' : T _ (F.map k' (F.map k q.1.1))
        · simp [h'']
        · have h' : ¬ T _ (F.map k q.1.1) := fun h => h'' (Tmap k' _ h)
          simp [h'', h'] }
  have Dpos : ∀ {z z'} (k : z' ⟶ z) (t : F.obj z) (bb : Bool) (hv : T z t → bb = false),
      T z' (F.map k t) → D.map k ⟨(t, bb), hv⟩ = ⟨(F.map k t, false), fun _ => rfl⟩ :=
    fun k t bb hv h => Subtype.ext (Prod.ext rfl (by simp [D, h]))
  have Dneg : ∀ {z z'} (k : z' ⟶ z) (t : F.obj z) (bb : Bool) (hv : T z t → bb = false)
      (h : ¬ T z' (F.map k t)), D.map k ⟨(t, bb), hv⟩ = ⟨(F.map k t, bb), fun h' => absurd h' h⟩ :=
    fun k t bb hv h => Subtype.ext (Prod.ext rfl (by simp [D, h]))
  have Tξ : T a ξ := Or.inl ⟨𝟙 a, (F.map_id _ _).symm⟩
  have Tη : T₂ b η := ⟨𝟙 b, (F.map_id _ _).symm⟩
  -- `D` is connected
  let base : Σ z, D.obj z := ⟨a, ⟨(ξ, false), fun _ => rfl⟩⟩
  let RD := fun x y : Σ z, D.obj z => ∃ k : y.1 ⟶ x.1, y.2 = D.map k x.2
  let P : (Σ z, F.obj z) → Prop := fun s => ∀ (bb : Bool) (hv : T s.1 s.2 → bb = false),
    Relation.EqvGen RD ⟨s.1, ⟨(s.2, bb), hv⟩⟩ base
  have Pinv : ∀ s s', (fun x y : Σ z, F.obj z => ∃ k : y.1 ⟶ x.1, y.2 = F.map k x.2) s s' →
      (P s ↔ P s') := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ ⟨k, hk⟩
    simp only at k hk
    subst hk
    constructor
    · intro hP bb' hv'
      by_cases hT' : T z' (F.map k t)
      · obtain rfl := hv' hT'
        refine (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨k, ?_⟩)).trans _ _ _
          (hP false fun _ => rfl)
        exact (Dpos k t false (fun _ => rfl) hT').symm
      · have hT : ¬ T z t := fun h => hT' (Tmap k t h)
        refine (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨k, ?_⟩)).trans _ _ _
          (hP bb' fun h => absurd h hT)
        exact (Dneg k t bb' _ hT').symm
    · intro hP' bb hv
      exact (Relation.EqvGen.rel _ _ ⟨k, rfl⟩).trans _ _ _
        (hP' (D.map k ⟨(t, bb), hv⟩).1.2 (D.map k ⟨(t, bb), hv⟩).2)
  have Pall : ∀ s, P s := fun s => by
    refine (eqvGen_iff Pinv (hF.2 ⟨a, ξ⟩ s)).1 ?_
    intro bb hv
    obtain rfl := hv Tξ
    exact Relation.EqvGen.refl _
  have hD : D.Connected := by
    refine ⟨⟨base⟩, fun x y => ?_⟩
    have hx := Pall ⟨x.1, x.2.1.1⟩ x.2.1.2 x.2.2
    have hy := Pall ⟨y.1, y.2.1.1⟩ y.2.1.2 y.2.2
    exact hx.trans _ _ _ (hy.symm _ _)
  -- the cocycle
  let ind : ∀ {z z' : X}, (z' ⟶ z) → D.obj z → ℤ := fun {z z'} k q =>
    if q.1.2 = true ∧ T₁ z' (F.map k q.1.1) then 1 else 0
  have ind_id : ∀ z (q : D.obj z), ind (𝟙 z) q = 0 := by
    intro z q
    simp only [ind, F.map_id]
    split_ifs with h
    · rw [q.2 (Or.inl h.2)] at h
      exact absurd h.1 Bool.false_ne_true
    · rfl
  have ind_comp : ∀ {z z' z'' : X} (k' : z'' ⟶ z') (k : z' ⟶ z) (q : D.obj z),
      ind (k' ≫ k) q = ind k q + ind k' (D.map k q) := by
    intro z z' z'' k' k q
    obtain ⟨⟨t, bb⟩, hv⟩ := q
    by_cases hT' : T z' (F.map k t)
    · rw [Dpos k t bb hv hT']
      have e : T₁ z'' (F.map (k' ≫ k) t) ↔ T₁ z' (F.map k t) := by
        refine ⟨fun h => hT'.resolve_right fun h₂ => disj _ _ h ?_, fun h => ?_⟩
        · rw [F.map_comp]; exact T₂map k' _ h₂
        · rw [F.map_comp]; exact T₁map k' _ h
      simp [ind, e]
    · rw [Dneg k t bb hv hT']
      have h₁ : ¬ T₁ z' (F.map k t) := fun h => hT' (Or.inl h)
      simp [ind, F.map_comp, h₁]
  let c : ∀ {z z' : X}, (z' ⟶ z) → D.obj z → Multiplicative (ULift.{v} ℤ) :=
    fun k q => Multiplicative.ofAdd (ULift.up (ind k q))
  obtain ⟨g, hg⟩ := H D hD _ c (fun z q => by simp only [c, ind_id]; rfl)
    (fun k' k q => by simp only [c, ind_comp]; rfl)
  let gz : ∀ z, D.obj z → ℤ := fun z q => (Multiplicative.toAdd (g z q)).down
  have key : ∀ {z z' : X} (k : z' ⟶ z) (q : D.obj z), ind k q = gz z q - gz z' (D.map k q) := by
    intro z z' k q
    have := congrArg (fun m : Multiplicative (ULift.{v} ℤ) => (Multiplicative.toAdd m).down)
      (hg k q)
    simpa [c, gz, sub_eq_add_neg] using this
  -- the difference between the two copies, off `T`
  let vt : ∀ z (t : F.obj z), ¬ T z t → Bool → D.obj z := fun z t hT bb =>
    ⟨(t, bb), fun h => absurd h hT⟩
  let hh : ∀ z (t : F.obj z), ¬ T z t → ℤ := fun z t hT =>
    gz z (vt z t hT true) - gz z (vt z t hT false)
  have R1 : ∀ {z z' : X} (k : z' ⟶ z) (t : F.obj z) (hT : ¬ T z t)
      (h' : ¬ T z' (F.map k t)), hh z t hT = hh z' (F.map k t) h' := by
    intro z z' k t hT h'
    have k1 := key k (vt z t hT true)
    have k0 := key k (vt z t hT false)
    rw [Dneg k t _ _ h'] at k1 k0
    have n1 : ¬ T₁ z' (F.map k t) := fun h => h' (Or.inl h)
    simp only [ind, vt, n1, and_false, ite_false] at k1 k0
    simp only [hh, vt]
    omega
  have R2 : ∀ {z z' : X} (k : z' ⟶ z) (t : F.obj z) (hT : ¬ T z t)
      (h' : T₁ z' (F.map k t)), hh z t hT = 1 := by
    intro z z' k t hT h'
    have k1 := key k (vt z t hT true)
    have k0 := key k (vt z t hT false)
    rw [Dpos k t _ _ (Or.inl h')] at k1 k0
    simp only [ind, vt, h', and_true, ite_true, Bool.false_eq_true, ite_false] at k1 k0
    simp only [hh, vt]
    omega
  have R3 : ∀ {z z' : X} (k : z' ⟶ z) (t : F.obj z) (hT : ¬ T z t)
      (h' : T₂ z' (F.map k t)), hh z t hT = 0 := by
    intro z z' k t hT h'
    have k1 := key k (vt z t hT true)
    have k0 := key k (vt z t hT false)
    rw [Dpos k t _ _ (Or.inr h')] at k1 k0
    have n1 : ¬ T₁ z' (F.map k t) := fun h => disj _ _ h h'
    simp only [ind, vt, n1, and_false, ite_false] at k1 k0
    simp only [hh, vt]
    omega
  -- propagate « in `T₁`, or off `T` with difference `1` » along `F`
  let Q : (Σ z, F.obj z) → Prop := fun s => T₁ s.1 s.2 ∨ ∃ hT : ¬ T s.1 s.2, hh s.1 s.2 hT = 1
  have Qinv : ∀ s s', (fun x y : Σ z, F.obj z => ∃ k : y.1 ⟶ x.1, y.2 = F.map k x.2) s s' →
      (Q s ↔ Q s') := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ ⟨k, hk⟩
    simp only at k hk
    subst hk
    constructor
    · rintro (h | ⟨hT, h⟩)
      · exact Or.inl (T₁map k t h)
      · by_cases h₁ : T₁ z' (F.map k t)
        · exact Or.inl h₁
        by_cases h₂ : T₂ z' (F.map k t)
        · exact absurd (h.symm.trans (R3 k t hT h₂)) one_ne_zero
        have h' : ¬ T z' (F.map k t) := fun h => h.elim h₁ h₂
        exact Or.inr ⟨h', (R1 k t hT h').symm.trans h⟩
    · rintro (h | ⟨hT', h⟩)
      · by_cases hT : T z t
        · exact Or.inl (hT.resolve_right fun h₂ => disj _ _ h (T₂map k t h₂))
        · exact Or.inr ⟨hT, R2 k t hT h⟩
      · have hT : ¬ T z t := fun h => hT' (Tmap k t h)
        exact Or.inr ⟨hT, (R1 k t hT hT').trans h⟩
  have hQ := (eqvGen_iff Qinv (hF.2 ⟨a, ξ⟩ ⟨b, η⟩)).1 (Or.inl ⟨𝟙 a, (F.map_id _ _).symm⟩)
  rcases hQ with h | ⟨hT, -⟩
  · exact disj _ _ h Tη
  · exact hT (Or.inr Tη)

/-- **The step « (H) ⇒ pseudo-cofiltrant » of page 53**, for any category: (H) and `X`
connected give cones over pairs of objects… -/
theorem cone_objs_of_H (H : HypH X) (hX : (Psh.terminal X).Connected) (x y : X) :
    ∃ (w : X) (_ : w ⟶ x), Nonempty (w ⟶ y) := by
  obtain ⟨w, u, u', -⟩ := common_ancestor H _ hX (a := x) (b := y) PUnit.unit PUnit.unit
  exact ⟨w, u, ⟨u'⟩⟩

/-- … and (H) alone gives squares over cospans. -/
theorem square_of_H (H : HypH X) {x y c : X} (u : x ⟶ c) (v : y ⟶ c) :
    ∃ (w : X) (u' : w ⟶ x) (v' : w ⟶ y), u' ≫ u = v' ≫ v :=
  common_ancestor H (Psh.yo c) (Psh.yo_connected c) u v

end Doubling

section Finite

variable {X : Type v} [SmallCategory X] [FinCategory X]

/-- A finite category with cones over pairs has an object mapping to every object. -/
theorem exists_least (hne : Nonempty X)
    (hc : ∀ x y : X, ∃ (w : X) (_ : w ⟶ x), Nonempty (w ⟶ y)) :
    ∃ e : X, ∀ z : X, Nonempty (e ⟶ z) := by
  classical
  have key : ∀ s : Finset X, ∃ e : X, ∀ z ∈ s, Nonempty (e ⟶ z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨hne.some, by simp⟩
    | insert a s _ ih =>
      obtain ⟨e, he⟩ := ih
      obtain ⟨w, u, ⟨v⟩⟩ := hc e a
      refine ⟨w, (Finset.forall_mem_insert _ _ _).2 ⟨⟨v⟩, fun z hz => ?_⟩⟩
      obtain ⟨k⟩ := he z hz
      exact ⟨u ≫ k⟩
  obtain ⟨e, he⟩ := key Finset.univ
  exact ⟨e, fun z => he z (Finset.mem_univ z)⟩

/-- In the monoid `End e` of an object mapping to every object, (H) gives a minimal
idempotent `p` (finite and pseudo-cofiltered, as in Proposition 1). -/
theorem exists_minimal_idem (H : HypH X) {e : X} (he : ∀ z : X, Nonempty (e ⟶ z)) :
    ∃ p : End e, p * p = p ∧ Minimal p := by
  have hpc : PseudoCofiltrant (End e) := fun u v => by
    obtain ⟨w, a, b, hab⟩ := square_of_H H u.asHom v.asHom
    obtain ⟨j⟩ := he w
    exact ⟨End.of (j ≫ a), End.of (j ≫ b), End.ext (by simp [hab])⟩
  have : Finite (End e) := Finite.of_equiv _ End.homEquiv.symm
  obtain ⟨ψ, hψ⟩ := etape1 hpc
  have hmin : Minimal ψ := fun u => (hψ u).imp fun _ h => h.symm
  obtain ⟨r, s, hne, hrs⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => ψ ^ n)
  obtain ⟨n, hn, hidem⟩ : ∃ n, 1 ≤ n ∧ ψ ^ n * ψ ^ n = ψ ^ n := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact exists_idem_pow hlt hrs
    · exact exists_idem_pow hlt hrs.symm
  refine ⟨ψ ^ n, hidem, ?_⟩
  rw [show n = 1 + (n - 1) by omega, pow_add, pow_one]
  exact hmin.mul _

/-- **Pages 50 to 53, for a connected finite category.** If `X` is finite, non-empty and
connected, and every connected presheaf on `X` has a simply connected category of elements,
then `X` is cofiltered. The equalising arrow is `p ≫ c` with `c : e ⟶ x`, `e` mapping to
every object and `p` a minimal idempotent of `End e`: the local system
`L(z) = Hom(e, z) p` on the least objects is constant by (H), which forces `p c f = p c g`. -/
theorem isCofiltered_of_H (H : HypH X) (hX : (Psh.terminal X).Connected) : IsCofiltered X := by
  classical
  have hne : Nonempty X := ⟨hX.1.some.1⟩
  obtain ⟨e, he⟩ := exists_least hne (cone_objs_of_H H hX)
  obtain ⟨p, hidem, hmin⟩ := exists_minimal_idem H he
  have hpp : p.asHom ≫ p.asHom = p.asHom := by simpa using congrArg End.asHom hidem
  -- the local system `L(z) = Hom(e, z) p`
  let L : X → Type v := fun z => {f : e ⟶ z // p.asHom ≫ f = f}
  let Lmap : ∀ {z z' : X}, (z ⟶ z') → L z → L z' := fun k ℓ =>
    ⟨ℓ.1 ≫ k, by rw [← Category.assoc, ℓ.2]⟩
  have Lsurj : ∀ {z z' : X} (k : z ⟶ z'), Function.Surjective (Lmap k) := by
    intro z z' k f'
    obtain ⟨w, a, b, hab⟩ := square_of_H H k f'.1
    obtain ⟨j⟩ := he w
    obtain ⟨θ, hθ⟩ := hmin (End.of (j ≫ b))
    have hθ' : θ.asHom ≫ j ≫ b = p.asHom := by simpa using congrArg End.asHom hθ
    refine ⟨⟨p.asHom ≫ θ.asHom ≫ j ≫ a, by rw [← Category.assoc, hpp]⟩, Subtype.ext ?_⟩
    change (p.asHom ≫ θ.asHom ≫ j ≫ a) ≫ k = f'.1
    calc (p.asHom ≫ θ.asHom ≫ j ≫ a) ≫ k = p.asHom ≫ θ.asHom ≫ j ≫ (a ≫ k) := by
          simp only [Category.assoc]
      _ = p.asHom ≫ (θ.asHom ≫ j ≫ b) ≫ f'.1 := by rw [hab]; simp only [Category.assoc]
      _ = f'.1 := by rw [hθ', ← Category.assoc, hpp, f'.2]
  -- the least objects, where `L` is a local system
  let X₀ : X → Prop := fun z => ∀ w, Nonempty (z ⟶ w)
  have Lbij : ∀ {z z' : X}, X₀ z → X₀ z' → ∀ k : z ⟶ z', Function.Bijective (Lmap k) := by
    intro z z' hz hz' k
    obtain ⟨r⟩ := hz' z
    have h₁ := Nat.card_le_card_of_surjective _ (Lsurj k)
    have h₂ := Nat.card_le_card_of_surjective _ (Lsurj r)
    exact (Lsurj k).bijective_of_nat_card_le (le_antisymm h₁ h₂).ge
  have he₀ : X₀ e := he
  let Lequiv : ∀ {z z' : X}, (z ⟶ z') → X₀ z → X₀ z' → (L z ≃ L z') := fun k hz hz' =>
    Equiv.ofBijective _ (Lbij hz hz' k)
  -- the presheaf of least objects: its category of elements is the full subcategory `X₀`
  let S₀ : Psh X :=
    { obj := fun z => {_u : PUnit.{v+1} // X₀ z}
      map := fun k q => ⟨PUnit.unit, fun w => (q.2 w).map (k ≫ ·)⟩
      map_id := fun _ _ => rfl
      map_comp := fun _ _ _ => rfl }
  have hS₀ : S₀.Connected := by
    let base : Σ z, S₀.obj z := ⟨e, ⟨PUnit.unit, he₀⟩⟩
    have hb : ∀ x : Σ z, S₀.obj z, Relation.EqvGen
        (fun a b : Σ z, S₀.obj z => ∃ k : b.1 ⟶ a.1, b.2 = S₀.map k a.2) base x := fun x => by
      obtain ⟨k⟩ := x.2.2 e
      exact Relation.EqvGen.rel _ _ ⟨k, Subsingleton.elim _ _⟩
    exact ⟨⟨base⟩, fun x y => ((hb x).symm _ _).trans _ _ _ (hb y)⟩
  -- trivialise `L` on `X₀` with (H)
  let jz : ∀ z, e ⟶ z := fun z => (he z).some
  let β : ∀ z, X₀ z → (L z ≃ L e) := fun z hz => (Lequiv (jz z) he₀ hz).symm
  let c : ∀ {z z' : X}, (z' ⟶ z) → S₀.obj z → Equiv.Perm (L e) := fun {z z'} k q =>
    ((β z' (S₀.map k q).2).symm.trans (Lequiv k (S₀.map k q).2 q.2)).trans (β z q.2)
  have Lid : ∀ {z} (ℓ : L z), Lmap (𝟙 z) ℓ = ℓ := fun ℓ => Subtype.ext (Category.comp_id _)
  have Lcomp : ∀ {z z' z''} (k' : z'' ⟶ z') (k : z' ⟶ z) (ℓ : L z''),
      Lmap (k' ≫ k) ℓ = Lmap k (Lmap k' ℓ) := fun _ _ ℓ =>
    Subtype.ext (Category.assoc _ _ _).symm
  obtain ⟨g, hg⟩ := H S₀ hS₀ (Equiv.Perm (L e)) c
    (fun z q => Equiv.ext fun ℓ => by
      simp only [c, Equiv.trans_apply, Lequiv, Equiv.ofBijective_apply, Lid,
        Equiv.apply_symm_apply, Equiv.Perm.one_apply])
    (fun k' k q => Equiv.ext fun ℓ => by
      simp only [c, Equiv.trans_apply, Lequiv, Equiv.ofBijective_apply, Lcomp,
        Equiv.Perm.mul_apply, Equiv.symm_apply_apply])
  let ψE : ∀ z, X₀ z → (L z ≃ L e) := fun z hz => (β z hz).trans (g z ⟨PUnit.unit, hz⟩)⁻¹
  have ψinv : ∀ {z z' : X} (k : z' ⟶ z) (hz : X₀ z) (hz' : X₀ z') (ℓ : L z'),
      ψE z hz (Lmap k ℓ) = ψE z' hz' ℓ := by
    intro z z' k hz hz' ℓ
    have h := congrArg (fun σ : Equiv.Perm (L e) => σ (β z' hz' ℓ)) (hg k ⟨PUnit.unit, hz⟩)
    simp only [c, Equiv.trans_apply, Lequiv, Equiv.ofBijective_apply, Equiv.symm_apply_apply,
      Equiv.Perm.mul_apply] at h
    simp only [ψE, Equiv.trans_apply]
    rw [h]
    exact Equiv.symm_apply_apply _ _
  -- evaluation: `Φ(z, u)(s) = ψE⁻¹(s) ≫ u` depends only on the class of `(z, u)` over `y`
  have Φinv : ∀ {y z z' : X} (k : z' ⟶ z) (hz : X₀ z) (hz' : X₀ z') (u : z ⟶ y) (s : L e),
      ((ψE z' hz').symm s).1 ≫ k ≫ u = ((ψE z hz).symm s).1 ≫ u := by
    intro y z z' k hz hz' u s
    have h : (ψE z hz).symm s = Lmap k ((ψE z' hz').symm s) := by
      rw [Equiv.symm_apply_eq, ψinv k hz hz', Equiv.apply_symm_apply]
    rw [h, ← Category.assoc]
  have equal : ∀ {x y : X} (f g : x ⟶ y), ∃ (w : X) (h : w ⟶ x), h ≫ f = h ≫ g := by
    intro x y f g
    obtain ⟨c₀⟩ := he x
    obtain ⟨w, a, b, hab⟩ := square_of_H H (c₀ ≫ f) (c₀ ≫ g)
    obtain ⟨j⟩ := he w
    let s := ψE e he₀ ⟨p.asHom, hpp⟩
    have key : ((ψE e he₀).symm s).1 ≫ c₀ ≫ f = ((ψE e he₀).symm s).1 ≫ c₀ ≫ g := by
      rw [← Φinv (j ≫ a) he₀ he₀ (c₀ ≫ f) s, ← Φinv (j ≫ b) he₀ he₀ (c₀ ≫ g) s]
      simp only [Category.assoc, hab]
    simp only [s, Equiv.symm_apply_apply] at key
    exact ⟨e, p.asHom ≫ c₀, by simpa only [Category.assoc] using key⟩
  exact
    { cone_objs := fun x y => by
        obtain ⟨w, u, ⟨v⟩⟩ := cone_objs_of_H H hX x y
        exact ⟨w, u, v, trivial⟩
      cone_maps := fun _ _ f g => equal f g
      nonempty := hne }

/-- **The statement as read fails without connectedness.** The discrete category on two
objects is finite, every presheaf on it (connected or not) has a simply connected category
of elements, and it is not cofiltered. -/
theorem discrete_counterexample :
    HypH (Discrete Bool) ∧ ¬ (Psh.terminal (Discrete Bool)).Connected ∧
      ¬ IsCofiltered (Discrete Bool) := by
  refine ⟨fun F _ G _ c c1 _ => ⟨fun _ _ => 1, fun {z z'} k t => ?_⟩, fun h => ?_, fun h => ?_⟩
  · obtain rfl : z' = z := Discrete.ext (Discrete.eq_of_hom k)
    obtain rfl : k = 𝟙 _ := Subsingleton.elim _ _
    rw [c1]; simp
  · have hQ := (eqvGen_iff (Q := fun s : Σ z, (Psh.terminal (Discrete Bool)).obj z =>
      s.1.as = true) (fun a b ⟨k, _⟩ => by simp only [Discrete.eq_of_hom k])
      (h.2 ⟨⟨true⟩, PUnit.unit⟩ ⟨⟨false⟩, PUnit.unit⟩)).1 rfl
    simp at hQ
  · obtain ⟨w, u, v, -⟩ := h.cone_objs ⟨true⟩ ⟨false⟩
    have := (Discrete.eq_of_hom u).symm.trans (Discrete.eq_of_hom v)
    simp at this

end Finite

end Grothendieck.Folder158
