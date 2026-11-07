module

public import Mathlib
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.Group
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Grothendieck.Upstream.SemilocalStableRange

@[expose] public section


/-!
# Folder 79: coset graphs with homotheties, and the polyhedra `P_{M,i}` of `(Z/n)²`

The modernised reading `transcripts/79/79.modern.tex` (« Homogénéité, et
traduction en théorie des groupes », pages 238 to 269; « Le commutant de
`SL(M)` et de `SL(M)'` », pages 92 to 95; « Un sommet est-il déterminé par son
étoile ? », pages 275 to 280; « Orientation et connexité », pages 17 to 20;
« Lire `Z'_Λ` sur les étoiles » and « Le fait mirifique », pages 96 to 101 and
136 to 140; « Points antipodiques et homothéties », pages 178 to 189) is the source of the findings `79-homothety-groups-as-subgroups`,
`79-commutant-octahedral-exception`, `79-vertex-determined-by-star`,
`79-semilocal-diameter-three`, `79-star-polygon-twist` and
`79-homothety-distance-three` of
`src/content/findings.ts`. Proving them says only that the claims hold as
stated (or as corrected below); whether they stand in the literature is a
separate question.

What is formalised:

* **(88)–(89), pages 242 to 247.** For a group `H`, a subgroup `U₀` and
  `σ ∈ H` with `σ² ∈ U₀` and `U₀ ∩ σU₀σ⁻¹ = 1` (the coset graph `H/U₀`, with
  origin arc `(U₀, σU₀)`, on whose arcs `H` is simply transitive),
  `homothetyEquiv` is a bijection between groups `Z` of homotheties
  (`IsHomothetyGroup`: permutations commuting with `H`, sending each arc
  `(s, t)` to an arc `(λs, λ⁻¹t)`, faithful in the sense of (72)) and
  subgroups `T ⊂ H` (`IsTorus`) that `σ` inverts, that normalise `U₀`, and with
  `U₀ × T × U₁ → H` injective. Both directions are proved, including the one
  that is partly illegible on page 247. `IsHomothetyGroup.comm`: commutativity
  of `Z` follows from the other conditions, without simple transitivity (the
  margin « [ ] résulte des autres »). No faithfulness of `H` on `H/U₀` is used.
* **Pages 92 to 95, over any commutative ring `R`.** `commutant`: a map of
  `M*/±1` (`Vtx R`) commuting with `SL(2, R)` is a scalar `c ∈ R*`, or, if
  `2R ⊂ {0, 2}` (`Exceptional R`), a scalar times `σ`, `σ(ẋ) = (x + 2y)˙` for
  `x ∧ y = 1`. Conversely (`scal_act`, `sigma_act`) these commute with
  `SL(2, R)`; `sigma_sigma`, `sigma_scal` and `sigma_ne_scal` (if `2 ≠ 0`, `σ`
  is no scalar and has no fixed point) give the direct product
  `R*/±1 × {1, σ}`; `scal_eq_scal_iff` says the scalars act through `R*/±1`.
  `exceptional_zmod_iff`: over `Z/n`, `2R = {0, 2} ≠ {0}` iff `n = 4`, hence
  `commutant_zmod`; `zmod4_non_neighbours`: for `Z/4`, `σ(ẋ)` is the one vertex
  other than `ẋ` not adjacent to it, the antipode of the octahedron.
* **Pages 275 to 279.** `same_star_iff`, over any commutative ring: `x'` has the
  neighbours of `x` type by type iff `x' = ± x`, or `2R ⊂ {0, 2}` and
  `x' = ± (x + 2y)`. The semi-local hypothesis of the page is not needed.
  `matA_mulVec`, `matA_det`, `matA_sq`: in the exceptional case `σ` is induced
  by the matrix with rows `(1, 2)` and `(2, -1)`, of determinant `-1` and
  square `1`.
* **Pages 19 and 20.** `exists_isUnit_mul_add` (stable range one of a semi-local
  ring, the fact the page cites as known) and `semilocal_dist_three`: over a ring
  with finitely many maximal ideals, any two vertices of `SP_M` are joined by a
  path `x, z₁, z₂, y` with `x ∧ z₁ = z₁ ∧ z₂ = z₂ ∧ y = e`; `local_dist_three` and
  `zmod_dist_three` (`n ≥ 1`) are the cases of a local ring and of `Z/n`.
* **Pages 96 to 101 and 136 to 140, in the model.** `twist_edge` (`A_{T_μ}` of
  `P_{M, i}` is `P_{M, μi}`), `twist_star` (the star of `ẋ` is, as a set, the
  star of `μẋ` after the twist), `star_line`, `triangle_face` (formula (178), page 67),
  `link_polygon` (the star `k ↦ y + kx` carries the polygon `k ~ k ± μ` in
  `P_{M, μi}`), `twist_index` (`λ_{Γ, s} = ± μ`, no exponent).
* **Page 188, (32) a″).** In the coset graph (`σ² ∈ U₀`), for an
  `H`-equivariant permutation `λ ≠ 1`: `homothety_fixed` (no fixed point),
  `homothety_adj` (if `λx` is a neighbour of `x`, it is the only one),
  `homothety_common_nbr` (a common neighbour of `x` and `λx` forces equal
  stars), hence `homothety_dist_ge_three`: if `x` has two neighbours and no
  other vertex has its star, `λx` is at distance at least `3` from `x`. The
  double-cone lemma of page 275 (equal stars only for the octahedron) is not
  formalised; in the model it is replaced by `same_star_iff`. In the model
  (`Adj`, edges of type `± e` on `M*/±1`), over any commutative ring:
  `commutant_dist` (a map `λ ≠ 1` commuting with `SL(2, R)` fixes no vertex,
  moves none to a neighbour, and moves one, equivalently all, to distance `2`
  iff `R` is exceptional and `λ = σ`), `sigma_common_nbr`; over a semi-local
  ring `commutant_dist_three` (distance exactly `3` for `λ ≠ 1, σ`), and over
  `Z/n`, `n ≥ 2`, `zmod_scal_dist_three` (units `μ ≠ ± 1`).
-/

namespace Grothendieck.Folder79

/-! ## Homothety groups as subgroups (pages 242 to 247) -/

section Homothety

open MulAction

variable {H : Type*} [Group H] (U₀ : Subgroup H) (σ : H)

/-- The origin `s₀ = U₀` of the coset graph. -/
def s₀ : H ⧸ U₀ := QuotientGroup.mk 1

/-- The other end `t₀ = σ U₀` of the origin arc. -/
def t₀ : H ⧸ U₀ := QuotientGroup.mk σ

variable {U₀ σ}

theorem smul_s₀ (h : H) : h • s₀ U₀ = QuotientGroup.mk h := by
  simp [s₀]

theorem smul_t₀ (h : H) : h • t₀ U₀ σ = QuotientGroup.mk (h * σ) := by
  simp [t₀]

theorem smul_s₀_eq_iff (g : H) : g • s₀ U₀ = s₀ U₀ ↔ g ∈ U₀ := by
  rw [smul_s₀, s₀, QuotientGroup.eq]; simp

theorem smul_t₀_eq_iff (g : H) : g • t₀ U₀ σ = t₀ U₀ σ ↔ σ⁻¹ * g * σ ∈ U₀ := by
  rw [smul_t₀, t₀, QuotientGroup.eq, ← U₀.inv_mem_iff]; simp [mul_assoc]

/-- `s ⟶ t` is an arc of the coset graph: the image of the origin arc
`(s₀, t₀)` under an element of `H`. -/
def IsArc (s t : H ⧸ U₀) : Prop := ∃ h : H, h • s₀ U₀ = s ∧ h • t₀ U₀ σ = t

variable (U₀ σ) in
/-- A group `Z` of homotheties (pages 241 to 243): permutations of `S = H/U₀`
commuting with `H`, such that `(s, t)` an arc implies `(λ s, λ⁻¹ t)` an arc
(condition (70 b) as corrected by the reading), and acting faithfully in the
sense of (72). Commutativity is not assumed: `IsHomothetyGroup.comm` derives it. -/
structure IsHomothetyGroup (Z : Subgroup (Equiv.Perm (H ⧸ U₀))) : Prop where
  commute : ∀ l ∈ Z, ∀ (h : H) (x : H ⧸ U₀), l (h • x) = h • l x
  homothety : ∀ l ∈ Z, ∀ s t, IsArc (σ := σ) s t → IsArc (σ := σ) (l s) (l⁻¹ t)
  faithful : ∀ l ∈ Z, ∀ u : H, u • s₀ U₀ = s₀ U₀ → u • t₀ U₀ σ = l (t₀ U₀ σ) → l = 1

variable (U₀ σ) in
/-- The conditions of (89) on a subgroup `T ⊂ H`: `σ` inverts `T` (hence
normalises it), `T` normalises `U₀`, and `U₀ × T × U₁ → H` is injective,
with `U₁ = σ U₀ σ⁻¹ = {b | σ⁻¹ b σ ∈ U₀}`. -/
structure IsTorus (T : Subgroup H) : Prop where
  inverts : ∀ t ∈ T, σ * t * σ⁻¹ = t⁻¹
  normalises : ∀ t ∈ T, ∀ u ∈ U₀, t * u * t⁻¹ ∈ U₀
  injective : ∀ a ∈ U₀, ∀ a' ∈ U₀, ∀ t ∈ T, ∀ t' ∈ T, ∀ b b' : H,
    σ⁻¹ * b * σ ∈ U₀ → σ⁻¹ * b' * σ ∈ U₀ → a * t * b = a' * t' * b' →
    a = a' ∧ t = t' ∧ b = b'

/-- An `H`-equivariant map of `H/U₀` is determined by the image of `s₀`. -/
theorem equivariant_ext {l l' : Equiv.Perm (H ⧸ U₀)}
    (hl : ∀ (h : H) x, l (h • x) = h • l x) (hl' : ∀ (h : H) x, l' (h • x) = h • l' x)
    (h0 : l (s₀ U₀) = l' (s₀ U₀)) : l = l' := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rw [← smul_s₀, hl, hl', h0]

theorem inv_commute {l : Equiv.Perm (H ⧸ U₀)} (hl : ∀ (h : H) x, l (h • x) = h • l x)
    (h : H) (x : H ⧸ U₀) : l⁻¹ (h • x) = h • l⁻¹ x := by
  apply l.injective
  rw [hl]; simp

variable (hz : ∀ u ∈ U₀, σ⁻¹ * u * σ ∈ U₀ → u = 1)
include hz

/-- Simple transitivity on arcs (79): two elements of `H` that agree on `s₀`
and `t₀` are equal. -/
theorem eq_of_agree {u v : H} (hs : u • s₀ U₀ = v • s₀ U₀)
    (ht : u • t₀ U₀ σ = v • t₀ U₀ σ) : u = v := by
  have h1 : (v⁻¹ * u) • s₀ U₀ = s₀ U₀ := by rw [mul_smul, hs, inv_smul_smul]
  have h2 : (v⁻¹ * u) • t₀ U₀ σ = t₀ U₀ σ := by rw [mul_smul, ht, inv_smul_smul]
  rw [smul_s₀_eq_iff] at h1
  rw [smul_t₀_eq_iff] at h2
  exact (inv_mul_eq_one.mp (hz _ h1 h2)).symm

theorem sigma_sq (hσ : σ * σ ∈ U₀) : σ * σ = 1 :=
  hz _ hσ (by simpa [mul_assoc] using hσ)

variable {Z : Subgroup (Equiv.Perm (H ⧸ U₀))}

omit hz in
theorem IsHomothetyGroup.base (hZ : IsHomothetyGroup U₀ σ Z) {l} (hl : l ∈ Z) :
    ∃ u : H, u • s₀ U₀ = l (s₀ U₀) ∧ u • t₀ U₀ σ = l⁻¹ (t₀ U₀ σ) := by
  obtain ⟨u, hu⟩ := hZ.homothety l hl _ _ ⟨1, rfl, rfl⟩
  exact ⟨u, by simpa using hu⟩

omit hz in
theorem eq_inv_of_smul {l : Equiv.Perm (H ⧸ U₀)} (hl : ∀ (h : H) x, l (h • x) = h • l x)
    {u : H} {x : H ⧸ U₀} (h : u • x = l x) : u⁻¹ • x = l⁻¹ x := by
  apply l.injective
  rw [hl, ← h]; simp

omit hz in
/-- Commutativity of `Z` follows from the other conditions: the bracket
`[T_H / 𝔷_H commutatif]` of (88), which the margin of page 247 says
« résulte des autres ». -/
theorem IsHomothetyGroup.comm (hZ : IsHomothetyGroup U₀ σ Z) {a b} (ha : a ∈ Z)
    (hb : b ∈ Z) : a * b = b * a := by
  obtain ⟨u, hu1, hu2⟩ := hZ.base ha
  obtain ⟨v, hv1, hv2⟩ := hZ.base hb
  obtain ⟨w, hw1, hw2⟩ := hZ.base (Z.mul_mem hb ha)
  have cb := hZ.commute b hb
  have cbi := inv_commute cb
  have cba := hZ.commute _ (Z.mul_mem hb ha)
  have hw1' := eq_inv_of_smul cba hw1
  have hw2' : w⁻¹ • t₀ U₀ σ = (b * a) (t₀ U₀ σ) := by
    simpa using eq_inv_of_smul (inv_commute cba) hw2
  set c := b⁻¹ * a⁻¹ * b * a with hc
  have hcZ : c ∈ Z := Z.mul_mem (Z.mul_mem (Z.mul_mem (Z.inv_mem hb) (Z.inv_mem ha)) hb) ha
  have key := hZ.faithful c hcZ (w⁻¹ * (u * v)) ?_ ?_
  · calc a * b = a * b * c := by rw [key, mul_one]
      _ = b * a := by rw [hc]; group
  · rw [mul_smul, mul_smul, hv1, ← cb, hu1]
    have : b (a (s₀ U₀)) = (b * a) (s₀ U₀) := rfl
    rw [this, ← hw1, inv_smul_smul]
  · rw [mul_smul, mul_smul, hv2, ← cbi, hu2]
    have hab : b⁻¹ (a⁻¹ (t₀ U₀ σ)) = (b⁻¹ * a⁻¹) (t₀ U₀ σ) := rfl
    have cc := hZ.commute _ (Z.mul_mem (Z.inv_mem hb) (Z.inv_mem ha))
    rw [hab, ← cc, hw2']
    simp [hc, Equiv.Perm.mul_apply]

/-- The subgroup `T_H` of page 245 attached to a homothety group `Z`:
the `u ∈ H` with `u s₀ = λ s₀` and `u t₀ = λ⁻¹ t₀` for some `λ ∈ Z`. -/
def torusOf (hZ : IsHomothetyGroup U₀ σ Z) : Subgroup H where
  carrier := {u | ∃ l ∈ Z, u • s₀ U₀ = l (s₀ U₀) ∧ u • t₀ U₀ σ = l⁻¹ (t₀ U₀ σ)}
  one_mem' := ⟨1, Z.one_mem, by simp, by simp⟩
  mul_mem' := by
    rintro u v ⟨a, ha, hu1, hu2⟩ ⟨b, hb, hv1, hv2⟩
    refine ⟨b * a, Z.mul_mem hb ha, ?_, ?_⟩
    · show (u * v) • _ = _
      rw [mul_smul, hv1, ← hZ.commute b hb, hu1]; rfl
    · show (u * v) • _ = _
      rw [mul_smul, hv2, ← inv_commute (hZ.commute b hb), hu2, ← hZ.comm ha hb]
      simp [Equiv.Perm.mul_apply]
  inv_mem' := by
    rintro u ⟨a, ha, hu1, hu2⟩
    refine ⟨a⁻¹, Z.inv_mem ha, eq_inv_of_smul (hZ.commute a ha) hu1, ?_⟩
    simpa using eq_inv_of_smul (inv_commute (hZ.commute a ha)) hu2

/-- The homotheties attached to a subgroup `T ⊂ H`: the `H`-equivariant
permutations `λ` with `λ s₀ = t s₀` for some `t ∈ T`, that is `h U₀ ↦ h t U₀`. -/
def homothetiesOf (T : Subgroup H) : Subgroup (Equiv.Perm (H ⧸ U₀)) where
  carrier := {l | (∀ (h : H) x, l (h • x) = h • l x) ∧ ∃ t ∈ T, l (s₀ U₀) = t • s₀ U₀}
  one_mem' := ⟨fun _ _ => rfl, 1, T.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ca, t, ht, hat⟩ ⟨cb, t', ht', hbt⟩
    refine ⟨fun h x => by simp [Equiv.Perm.mul_apply, ca, cb], t' * t, T.mul_mem ht' ht, ?_⟩
    simp only [Equiv.Perm.mul_apply, hbt, ca, hat, mul_smul]
  inv_mem' := by
    rintro a ⟨ca, t, ht, hat⟩
    refine ⟨inv_commute ca, t⁻¹, T.inv_mem ht, ?_⟩
    apply a.injective
    rw [ca]; simp [hat]

omit hz in
theorem sigma_smul_s₀ : σ • s₀ U₀ = t₀ U₀ σ := by simp [s₀, t₀]

omit hz in
theorem sigma_smul_t₀ (h1 : σ * σ = 1) : σ • t₀ U₀ σ = s₀ U₀ := by
  rw [← sigma_smul_s₀, ← mul_smul, h1, one_smul]

omit hz in
/-- If `λ` is equivariant with `λ s₀ = t s₀` and `σ t⁻¹ = t σ`, then
`λ⁻¹ t₀ = t t₀`: the arc `(λ s₀, λ⁻¹ t₀)` is `t (s₀, t₀)`. -/
theorem inv_t₀ {l : Equiv.Perm (H ⧸ U₀)} (c : ∀ (h : H) x, l (h • x) = h • l x) {t : H}
    (hlt : l (s₀ U₀) = t • s₀ U₀) (hst : σ * t⁻¹ = t * σ) :
    l⁻¹ (t₀ U₀ σ) = t • t₀ U₀ σ := by
  rw [← sigma_smul_s₀, inv_commute c, ← eq_inv_of_smul c hlt.symm, ← mul_smul, hst,
    mul_smul, sigma_smul_s₀]

omit hz in
theorem sigma_inv_comm {T : Subgroup H} (hT : IsTorus U₀ σ T) {t : H} (ht : t ∈ T) :
    σ * t⁻¹ = t * σ := by
  simpa using mul_inv_eq_iff_eq_mul.mp (hT.inverts _ (T.inv_mem ht))

/-- The conditions of (89) hold for `T_H`. -/
theorem isTorus_torusOf (hσ : σ * σ ∈ U₀) (hZ : IsHomothetyGroup U₀ σ Z) :
    IsTorus U₀ σ (torusOf hZ) := by
  have hσ1 := sigma_sq hz hσ
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_left hσ1
  refine ⟨?_, ?_, ?_⟩
  · rintro t ⟨l, hl, h1, h2⟩
    have c := hZ.commute l hl
    apply eq_of_agree hz
    · rw [hσi, mul_smul, mul_smul, sigma_smul_s₀, h2, ← inv_commute c, sigma_smul_t₀ hσ1,
        eq_inv_of_smul c h1]
    · rw [hσi, mul_smul, mul_smul, sigma_smul_t₀ hσ1, h1, ← c, sigma_smul_s₀]
      simpa using (eq_inv_of_smul (inv_commute c) h2).symm
  · rintro t ⟨l, hl, h1, h2⟩ u hu
    have c := hZ.commute l hl
    rw [← smul_s₀_eq_iff, mul_smul, mul_smul, eq_inv_of_smul c h1, ← inv_commute c,
      (smul_s₀_eq_iff u).2 hu, ← inv_commute c, h1]
    simp
  · intro a ha a' ha' t ht t' ht' b b' hb hb' heq
    set c' := t'⁻¹ * (a'⁻¹ * a) * t'⁻¹⁻¹ with hc'
    have hc'U : c' ∈ U₀ := by
      obtain ⟨l, hl, h1, h2⟩ := (torusOf hZ).inv_mem ht'
      rw [hc', ← smul_s₀_eq_iff, mul_smul, mul_smul, eq_inv_of_smul (hZ.commute l hl) h1,
        ← inv_commute (hZ.commute l hl), (smul_s₀_eq_iff _).2 (U₀.mul_mem (U₀.inv_mem ha') ha),
        ← inv_commute (hZ.commute l hl), h1]
      simp
    set r := t'⁻¹ * t with hr
    have hrT : r ∈ torusOf hZ := (torusOf hZ).mul_mem ((torusOf hZ).inv_mem ht') ht
    set d := b * b'⁻¹ with hd
    have hdU : σ⁻¹ * d * σ ∈ U₀ := by simpa [hd, mul_assoc] using U₀.mul_mem hb (U₀.inv_mem hb')
    have hcrd : c' * r * d = 1 := by
      have e : c' * r * d = t'⁻¹ * a'⁻¹ * (a * t * b) * b'⁻¹ := by
        simp only [hc', hr, hd]; group
      rw [e, heq]; group
    obtain ⟨l, hl, r1, r2⟩ := hrT
    have hdr : d = r⁻¹ * c'⁻¹ := by
      calc d = (c' * r)⁻¹ * (c' * r * d) := by group
        _ = r⁻¹ * c'⁻¹ := by rw [hcrd]; group
    have ht0 : d • t₀ U₀ σ = t₀ U₀ σ := (smul_t₀_eq_iff d).2 hdU
    have hc0 : c'⁻¹ • t₀ U₀ σ = l⁻¹⁻¹⁻¹ (t₀ U₀ σ) := by
      rw [hdr, mul_smul] at ht0
      have := congrArg (r • ·) ht0
      simp only [smul_inv_smul] at this
      rw [this, r2]; simp
    have hl1 := hZ.faithful l⁻¹ (Z.inv_mem hl) c'⁻¹
      ((smul_s₀_eq_iff _).2 (U₀.inv_mem hc'U)) (by simpa using hc0)
    have hl1' : l = 1 := inv_eq_one.mp hl1
    have hr1 : r = 1 := eq_of_agree hz (by rw [r1, hl1']; simp) (by rw [r2, hl1']; simp)
    have htt : t = t' := (inv_mul_eq_one.mp hr1).symm
    have hcd : c' * d = 1 := by simpa [hr1] using hcrd
    have hd1 : d = 1 :=
      hz d (by rw [eq_inv_of_mul_eq_one_right hcd]; exact U₀.inv_mem hc'U) hdU
    have hc1 : c' = 1 := by simpa [hd1] using hcd
    refine ⟨?_, htt, ?_⟩
    · calc a = a' * (t' * c' * t'⁻¹) := by rw [hc']; group
        _ = a' := by rw [hc1]; group
    · exact mul_inv_eq_one.mp hd1

/-- The permutation `h U₀ ↦ h t U₀`, for `t` normalising `U₀`. -/
def rightMulFun (t : H) (ht : ∀ u ∈ U₀, t⁻¹ * u * t ∈ U₀) : H ⧸ U₀ → H ⧸ U₀ :=
  Quotient.map' (· * t) (fun x y hxy => by
    rw [QuotientGroup.leftRel_apply] at *
    simpa [mul_assoc] using ht _ hxy)

omit hz in
theorem rightMulFun_mk (t : H) (ht : ∀ u ∈ U₀, t⁻¹ * u * t ∈ U₀) (h : H) :
    rightMulFun t ht (QuotientGroup.mk h) = QuotientGroup.mk (h * t) := rfl

/-- `h U₀ ↦ h t U₀` as a permutation. -/
def rightMul (t : H) (h1 : ∀ u ∈ U₀, t⁻¹ * u * t ∈ U₀) (h2 : ∀ u ∈ U₀, t * u * t⁻¹ ∈ U₀) :
    Equiv.Perm (H ⧸ U₀) where
  toFun := rightMulFun t h1
  invFun := rightMulFun t⁻¹ (by simpa using h2)
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g => simp [rightMulFun_mk]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g => simp [rightMulFun_mk]

/-- Conversely, a subgroup `T` with the conditions of (89) gives a group of
homotheties: the converse direction of (88), partly illegible on page 247. -/
theorem isHomothetyGroup_homothetiesOf (hσ : σ * σ ∈ U₀) {T : Subgroup H}
    (hT : IsTorus U₀ σ T) : IsHomothetyGroup U₀ σ (homothetiesOf T) := by
  have hσ1 := sigma_sq hz hσ
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_left hσ1
  refine ⟨fun l hl => hl.1, ?_, ?_⟩
  · rintro l ⟨c, t, ht, hlt⟩ _ _ ⟨h, rfl, rfl⟩
    refine ⟨h * t, ?_, ?_⟩
    · rw [mul_smul, ← hlt, c]
    · rw [mul_smul, inv_commute c, inv_t₀ c hlt (sigma_inv_comm hT ht)]
  · rintro l ⟨c, t, ht, hlt⟩ u hu0 hut
    have hu : u ∈ U₀ := (smul_s₀_eq_iff u).1 hu0
    rw [← sigma_smul_s₀, c, hlt, ← mul_smul, ← mul_smul, smul_s₀, smul_s₀, QuotientGroup.eq] at hut
    -- `hut : (u * σ)⁻¹ * (σ * t) ∈ U₀`
    set a := t⁻¹ * (σ⁻¹ * u * σ) with ha
    have haU : a ∈ U₀ := by simpa [ha, mul_assoc] using U₀.inv_mem hut
    have hb : σ⁻¹ * (σ⁻¹ * u * σ) * σ ∈ U₀ := by
      rw [hσi, show σ * (σ * u * σ) * σ = (σ * σ) * u * (σ * σ) by group, hσ1]; simpa using hu
    have key := hT.injective (t * a * t⁻¹) (hT.normalises t ht a haU) 1 U₀.one_mem t ht 1
      T.one_mem 1 (σ⁻¹ * u * σ) (by simp) hb (by simp [ha, mul_assoc])
    apply equivariant_ext c (fun _ _ => rfl)
    rw [hlt, key.2.1]; simp

omit hz in
/-- `Z ↦ T_H ↦ Z` is the identity. -/
theorem homothetiesOf_torusOf (hZ : IsHomothetyGroup U₀ σ Z) :
    homothetiesOf (torusOf hZ) = Z := by
  ext l
  constructor
  · rintro ⟨c, t, ⟨m, hm, h1, _⟩, hlt⟩
    exact equivariant_ext c (hZ.commute m hm) (by rw [hlt, h1]) ▸ hm
  · intro hl
    obtain ⟨u, h1, h2⟩ := hZ.base hl
    exact ⟨hZ.commute l hl, u, ⟨l, hl, h1, h2⟩, h1.symm⟩

/-- `T ↦ Z ↦ T_H` is the identity. -/
theorem torusOf_homothetiesOf (hσ : σ * σ ∈ U₀) {T : Subgroup H} (hT : IsTorus U₀ σ T) :
    torusOf (isHomothetyGroup_homothetiesOf hz hσ hT) = T := by
  ext u
  constructor
  · rintro ⟨l, ⟨c, t, ht, hlt⟩, h1, h2⟩
    have : u = t := eq_of_agree hz (by rw [h1, hlt])
      (by rw [h2, inv_t₀ c hlt (sigma_inv_comm hT ht)])
    exact this ▸ ht
  · intro hu
    have h1 : ∀ v ∈ U₀, u⁻¹ * v * u ∈ U₀ := fun v hv => by
      simpa using hT.normalises _ (T.inv_mem hu) v hv
    have h2 : ∀ v ∈ U₀, u * v * u⁻¹ ∈ U₀ := hT.normalises u hu
    set l := rightMul u h1 h2
    have c : ∀ (h : H) x, l (h • x) = h • l x := fun h x => by
      induction x using QuotientGroup.induction_on with
      | H g => simp [l, rightMul, rightMulFun_mk, mul_assoc]
    have hlt : l (s₀ U₀) = u • s₀ U₀ := by simp [l, rightMul, s₀, rightMulFun_mk]
    exact ⟨l, ⟨c, u, hu, hlt⟩, hlt.symm, (inv_t₀ c hlt (sigma_inv_comm hT hu)).symm⟩

/-- **(88)–(89), pages 245 to 247.** For the coset graph of `(H, U₀, σ)` with
`H` simply transitive on arcs (`U₀ ∩ σ U₀ σ⁻¹ = 1`, and `σ² ∈ U₀`), groups of
homotheties correspond bijectively to subgroups `T ⊂ H` that `σ` inverts,
that normalise `U₀`, and for which `U₀ × T × U₁ → H` is injective. -/
def homothetyEquiv (hσ : σ * σ ∈ U₀) :
    {Z : Subgroup (Equiv.Perm (H ⧸ U₀)) // IsHomothetyGroup U₀ σ Z} ≃
      {T : Subgroup H // IsTorus U₀ σ T} where
  toFun Z := ⟨torusOf Z.2, isTorus_torusOf hz hσ Z.2⟩
  invFun T := ⟨homothetiesOf T.1, isHomothetyGroup_homothetiesOf hz hσ T.2⟩
  left_inv Z := Subtype.ext (homothetiesOf_torusOf Z.2)
  right_inv T := Subtype.ext (torusOf_homothetiesOf hz hσ T.2)

end Homothety

/-! ## The distance from a vertex to its image under a homothety (pages 187 and 188) -/

section HomothetyDistance

variable {H : Type*} [Group H] {U₀ : Subgroup H} {σ : H}

/-- Arcs are carried to arcs by `H`. -/
theorem IsArc.smul {s t : H ⧸ U₀} (h : IsArc (σ := σ) s t) (g : H) :
    IsArc (σ := σ) (g • s) (g • t) := by
  obtain ⟨k, rfl, rfl⟩ := h
  exact ⟨g * k, mul_smul _ _ _, mul_smul _ _ _⟩

/-- With `σ² ∈ U₀`, the graph is undirected: `σ` exchanges `s₀` and `t₀`. -/
theorem IsArc.symm (hσ : σ * σ ∈ U₀) {s t : H ⧸ U₀} (h : IsArc (σ := σ) s t) :
    IsArc (σ := σ) t s := by
  obtain ⟨k, rfl, rfl⟩ := h
  refine ⟨k * σ, by rw [mul_smul, sigma_smul_s₀], ?_⟩
  rw [← sigma_smul_s₀, ← mul_smul, mul_assoc, mul_smul, (smul_s₀_eq_iff _).2 hσ]

/-- The stabiliser of `s` is transitive on the neighbours of `s`: this is
regularity, `H` being transitive on arcs. -/
theorem IsArc.stab_trans {s t t' : H ⧸ U₀} (h : IsArc (σ := σ) s t)
    (h' : IsArc (σ := σ) s t') : ∃ g : H, g • s = s ∧ g • t = t' := by
  obtain ⟨k, rfl, rfl⟩ := h
  obtain ⟨k', hk, rfl⟩ := h'
  refine ⟨k' * k⁻¹, ?_, ?_⟩
  · rw [mul_smul, inv_smul_smul, hk]
  · rw [mul_smul, inv_smul_smul]

variable {l : Equiv.Perm (H ⧸ U₀)}

/-- Distance `0`: an `H`-equivariant permutation with a fixed point is the
identity. -/
theorem homothety_fixed (hl : ∀ (h : H) x, l (h • x) = h • l x) {x : H ⧸ U₀}
    (hx : l x = x) : l = 1 := by
  apply equivariant_ext hl (fun _ _ => rfl)
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [← smul_s₀, hl] at hx
    simpa using congrArg (g⁻¹ • ·) hx

/-- Distance `1` (page 188, « puisque stabilisateurs »): if `λ x` is a
neighbour of `x`, the stabiliser of `x` fixes `λ x` and is transitive on the
neighbours of `x`, so `λ x` is the only neighbour of `x`. -/
theorem homothety_adj (hl : ∀ (h : H) x, l (h • x) = h • l x) {x t : H ⧸ U₀}
    (h : IsArc (σ := σ) x (l x)) (ht : IsArc (σ := σ) x t) : t = l x := by
  obtain ⟨g, hg, rfl⟩ := h.stab_trans ht
  rw [← hl, hg]

/-- Distance `2` (page 188): if `x` and `λ x` have a common neighbour, they
have the same neighbours. -/
theorem homothety_common_nbr (hσ : σ * σ ∈ U₀) (hl : ∀ (h : H) x, l (h • x) = h • l x)
    {x t : H ⧸ U₀} (h1 : IsArc (σ := σ) x t) (h2 : IsArc (σ := σ) t (l x)) (t' : H ⧸ U₀) :
    IsArc (σ := σ) x t' ↔ IsArc (σ := σ) (l x) t' := by
  constructor
  · intro h'
    obtain ⟨g, hg, rfl⟩ := h1.stab_trans h'
    have := h2.smul g
    rw [← hl, hg] at this
    exact this.symm hσ
  · intro h'
    obtain ⟨g, hg, rfl⟩ := (h2.symm hσ).stab_trans h'
    have hgx : g • x = x := l.injective (by rw [hl, hg])
    have := h1.smul g
    rwa [hgx] at this

/-- **Page 188, (32) a″).** Let `λ ≠ 1` be an `H`-equivariant permutation of
the vertices of the coset graph (`σ² ∈ U₀`), and `x` a vertex with at least two
neighbours that no other vertex has as its neighbours. Then `λ x` is neither `x`,
nor a neighbour of `x`, nor at distance `2` from `x`. If `λ x` is at distance at
most `3` from `x`, the distance is therefore `3`. The same holds for `λ⁻¹`. -/
theorem homothety_dist_ge_three (hσ : σ * σ ∈ U₀) (hl : ∀ (h : H) x, l (h • x) = h • l x)
    (hl1 : l ≠ 1) {x : H ⧸ U₀}
    (hstar : ∃ t t', IsArc (σ := σ) x t ∧ IsArc (σ := σ) x t' ∧ t ≠ t')
    (hsep : ∀ y, (∀ t, IsArc (σ := σ) x t ↔ IsArc (σ := σ) y t) → y = x) :
    l x ≠ x ∧ ¬ IsArc (σ := σ) x (l x) ∧ ¬ ∃ t, IsArc (σ := σ) x t ∧ IsArc (σ := σ) t (l x) := by
  have hne : l x ≠ x := fun e => hl1 (homothety_fixed hl e)
  refine ⟨hne, fun h => ?_, fun ⟨t, h1, h2⟩ => hne (hsep _ (homothety_common_nbr hσ hl h1 h2))⟩
  obtain ⟨t, t', ht, ht', hne'⟩ := hstar
  exact hne' ((homothety_adj hl h ht).trans (homothety_adj hl h ht').symm)

end HomothetyDistance

/-! ## Rank two: unimodular vectors modulo sign -/

section RankTwo

open Matrix

variable {R : Type*} [CommRing R]

/-- `x ∧ y` in the basis of `R²`. -/
def det2 (x y : Fin 2 → R) : R := x 0 * y 1 - x 1 * y 0

theorem det2_swap (x y : Fin 2 → R) : det2 y x = -det2 x y := by unfold det2; ring

omit [CommRing R] in
theorem vec_ext {x y : Fin 2 → R} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i; fin_cases i <;> assumption

theorem mulVec_apply2 (M : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) (i : Fin 2) :
    (M *ᵥ x) i = M i 0 * x 0 + M i 1 * x 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det2_mulVec (M : Matrix (Fin 2) (Fin 2) R) (x y : Fin 2 → R) :
    det2 (M *ᵥ x) (M *ᵥ y) = M.det * det2 x y := by
  simp only [det2, mulVec_apply2, Matrix.det_fin_two]; ring

/-- Coordinates in a basis `(x, y)` with `x ∧ y = 1`:
`z = (z ∧ y) x + (x ∧ z) y`. -/
theorem decomp {x y : Fin 2 → R} (h : det2 x y = 1) (z : Fin 2 → R) :
    z = det2 z y • x + det2 x z • y := by
  unfold det2 at h
  apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, det2]
  · linear_combination (-(z 0)) * h
  · linear_combination (-(z 1)) * h

/-- `x ∈ M*`: `x` is the first vector of a basis of `R²`. -/
def Unimod (x : Fin 2 → R) : Prop := ∃ y, det2 x y = 1

theorem unimod_of_isUnit {x z : Fin 2 → R} (h : IsUnit (det2 x z)) : Unimod x := by
  obtain ⟨u, hu⟩ := h
  refine ⟨(↑u⁻¹ : R) • z, ?_⟩
  have : det2 x ((↑u⁻¹ : R) • z) = ↑u⁻¹ * det2 x z := by
    simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, ← hu]; simp

variable (R) in
/-- The relation `x = ± y` on `M*`. -/
def pmSetoid : Setoid {x : Fin 2 → R // Unimod x} where
  r x y := x.1 = y.1 ∨ x.1 = -y.1
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (by rw [h, neg_neg])),
    fun h1 h2 => by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> simp⟩

variable (R) in
/-- `S_M = M*/±1`, the vertices. -/
def Vtx := Quotient (pmSetoid R)

/-- The vertex of a vector `x` with `x ∧ y = 1`. -/
def vtx {x y : Fin 2 → R} (h : det2 x y = 1) : Vtx R := Quotient.mk _ ⟨x, y, h⟩

theorem vtx_eq_iff {x y x' y' : Fin 2 → R} (h : det2 x y = 1) (h' : det2 x' y' = 1) :
    vtx h = vtx h' ↔ x = x' ∨ x = -x' :=
  ⟨fun e => Quotient.exact e, fun e => Quotient.sound e⟩

theorem Vtx.ind {P : Vtx R → Prop} (H : ∀ (x y : Fin 2 → R) (h : det2 x y = 1), P (vtx h))
    (v : Vtx R) : P v := by
  induction v using Quotient.inductionOn with
  | h x => obtain ⟨x, y, h⟩ := x; exact H x y h

/-- The action of `SL(2, R)` on `S_M`. -/
def act (g : Matrix.SpecialLinearGroup (Fin 2) R) : Vtx R → Vtx R :=
  Quotient.map (fun x => ⟨g.1 *ᵥ x.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨g.1 *ᵥ y, by rw [det2_mulVec, g.2, hy, one_mul]⟩⟩)
    (fun x y h => h.elim (fun h => Or.inl (by simp [h]))
      (fun h => Or.inr (by simp [h, Matrix.mulVec_neg])))

theorem act_vtx (g : Matrix.SpecialLinearGroup (Fin 2) R) {x y : Fin 2 → R}
    (h : det2 x y = 1) :
    act g (vtx h) = vtx (show det2 (g.1 *ᵥ x) (g.1 *ᵥ y) = 1 by
      rw [det2_mulVec, g.2, h, one_mul]) := rfl

theorem det2_smul_left (c : R) (x y : Fin 2 → R) : det2 (c • x) y = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_smul_right (c : R) (x y : Fin 2 → R) : det2 x (c • y) = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_add_left (x x' y : Fin 2 → R) : det2 (x + x') y = det2 x y + det2 x' y := by
  simp only [det2, Pi.add_apply]; ring

theorem det2_add_right (x y y' : Fin 2 → R) : det2 x (y + y') = det2 x y + det2 x y' := by
  simp only [det2, Pi.add_apply]; ring

theorem det2_self (x : Fin 2 → R) : det2 x x = 0 := by unfold det2; ring

theorem det2_neg_left (x y : Fin 2 → R) : det2 (-x) y = -det2 x y := by
  simp only [det2, Pi.neg_apply]; ring

theorem det2_neg_right (x y : Fin 2 → R) : det2 x (-y) = -det2 x y := by
  simp only [det2, Pi.neg_apply]; ring

theorem det2_scal (c : Rˣ) {x y : Fin 2 → R} (h : det2 x y = 1) :
    det2 ((c : R) • x) ((↑c⁻¹ : R) • y) = 1 := by
  rw [det2_smul_left, det2_smul_right, h]; simp

/-- The scalar `c ∈ R*`, acting on `S_M`. -/
def scal (c : Rˣ) : Vtx R → Vtx R :=
  Quotient.map (fun x => ⟨(c : R) • x.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨(↑c⁻¹ : R) • y, det2_scal c hy⟩⟩)
    (fun x y h => h.elim (fun h => Or.inl (by simp [h]))
      (fun h => Or.inr (by simp [h])))

theorem scal_vtx (c : Rˣ) {x y : Fin 2 → R} (h : det2 x y = 1) :
    scal c (vtx h) = vtx (det2_scal c h) := rfl

/-- The scalars commute with `SL(2, R)`. -/
theorem scal_act (c : Rˣ) (g : Matrix.SpecialLinearGroup (Fin 2) R) (v : Vtx R) :
    scal c (act g v) = act g (scal c v) := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [act_vtx, scal_vtx, scal_vtx, act_vtx, vtx_eq_iff]
    left; rw [Matrix.mulVec_smul]

/-- `c` and `c'` act alike on `S_M` iff `c = ± c'`: the scalars act through
`R*/±1`, faithfully. -/
theorem scal_eq_scal_iff (c c' : Rˣ) : scal (R := R) c = scal c' ↔ c = c' ∨ c = -c' := by
  constructor
  · intro h
    have h1 : det2 (![1, 0] : Fin 2 → R) ![0, 1] = 1 := by simp [det2]
    have := congrFun h (vtx h1)
    rw [scal_vtx, scal_vtx, vtx_eq_iff] at this
    rcases this with h | h
    · left; ext; simpa using congrFun h 0
    · right; ext; simpa using congrFun h 0
  · rintro (h | h) <;> funext v <;> induction v using Vtx.ind with
    | H x y hxy =>
      rw [scal_vtx, scal_vtx, vtx_eq_iff]
      first | (left; rw [h]; done) | (right; rw [h]; simp)

/-! ### The exceptional rings: `2R = {0, 2}` -/

/-- The ideal `2R` is contained in `{0, 2}`. With `2 ≠ 0` this is `2R = {0, 2} ≠ {0}`. -/
def Exceptional (R : Type*) [CommRing R] : Prop := ∀ s : R, 2 * s = 0 ∨ 2 * s = 2

theorem Exceptional.four (hR : Exceptional R) : (4 : R) = 0 := by
  rcases hR 2 with h | h
  · linear_combination h
  · linear_combination 2 * h

theorem Exceptional.two_mul_unit (hR : Exceptional R) {c : R} (hc : IsUnit c) : 2 * c = 2 := by
  obtain ⟨u, rfl⟩ := hc
  rcases hR u with h | h
  · have : (2 : R) = 0 := by simpa [mul_assoc] using congrArg (· * (↑u⁻¹ : R)) h
    rw [h, this]
  · exact h

theorem Exceptional.neg_two (hR : Exceptional R) : (-2 : R) = 2 := by
  linear_combination -hR.four

/-- On `Z/n`, `2R = {0, 2} ≠ {0}` holds only for `n = 4`. -/
theorem exceptional_zmod_iff (n : ℕ) :
    (Exceptional (ZMod n) ∧ (2 : ZMod n) ≠ 0) ↔ n = 4 := by
  constructor
  · rintro ⟨hR, h2⟩
    have h4 := hR.four
    have : (4 : ZMod n) = ((4 : ℕ) : ZMod n) := by norm_num
    rw [this, ZMod.natCast_eq_zero_iff] at h4
    have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) h4
    interval_cases n <;> simp_all <;> revert h2 <;> decide
  · rintro rfl
    refine ⟨fun s => ?_, by decide⟩
    fin_cases s <;> decide

/-- Independence of the partner: if `2R ⊂ {0, 2}`, `x ∧ y = 1`, `x' ∧ y' = 1`
and `x' = ± x`, then `x' + 2 y' = ± (x + 2 y)`. -/
theorem Exceptional.sigma_rel (hR : Exceptional R) {x y x' y' : Fin 2 → R}
    (h : det2 x y = 1) (h' : det2 x' y' = 1) (hx : x' = x ∨ x' = -x) :
    x' + (2 : R) • y' = x + (2 : R) • y ∨ x' + (2 : R) • y' = -(x + (2 : R) • y) := by
  have h4 := hR.four
  -- write `y'` in the basis `(x, y)`
  have hd := decomp h y'
  rcases hx with hx | hx <;> rw [hx] at h' ⊢
  · have hb : det2 x y' = 1 := h'
    rw [hb, one_smul] at hd
    rcases hR (det2 y' y) with h2 | h2
    · left; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (x i) * h2
    · right; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2 + (x i + y i) * h4
  · have hb : det2 x y' = -1 := by rw [← neg_neg x, det2_neg_left, h']
    rw [hb] at hd
    rcases hR (det2 y' y) with h2 | h2
    · right; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2
    · left; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2 - (y i) * h4

theorem det2_sigma {x y : Fin 2 → R} (h : det2 x y = 1) : det2 (x + (2 : R) • y) y = 1 := by
  rw [det2_add_left, det2_smul_left, det2_self, h]; ring

/-- The extra element `σ` of the commutant (pages 94 and 95), for `2R ⊂ {0, 2}`:
`ẋ ↦ (x + 2y)˙` for any `y` with `x ∧ y = 1`. In the basis `(e₁, e₂)` it sends
`ė₁` to the class of `(1, 2)`, the image of `e₁` by the matrix with rows
`(1, 0)` and `(2, 1)`. -/
noncomputable def sigma (hR : Exceptional R) : Vtx R → Vtx R :=
  Quotient.lift (fun x => vtx (det2_sigma x.2.choose_spec))
    (fun x x' hx => (vtx_eq_iff _ _).2 (hR.sigma_rel x'.2.choose_spec x.2.choose_spec hx))

theorem sigma_vtx (hR : Exceptional R) {x y : Fin 2 → R} (h : det2 x y = 1) :
    sigma hR (vtx h) = vtx (det2_sigma h) :=
  Quotient.sound (hR.sigma_rel h (⟨x, y, h⟩ : {x : Fin 2 → R // Unimod x}).2.choose_spec
    (Or.inl rfl))

theorem sigma_act (hR : Exceptional R) (g : Matrix.SpecialLinearGroup (Fin 2) R) (v : Vtx R) :
    sigma hR (act g v) = act g (sigma hR v) := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [act_vtx, sigma_vtx, sigma_vtx, act_vtx, vtx_eq_iff]
    left; rw [Matrix.mulVec_add, Matrix.mulVec_smul]

/-- `σ² = 1`. -/
theorem sigma_sigma (hR : Exceptional R) (v : Vtx R) : sigma hR (sigma hR v) = v := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [sigma_vtx, sigma_vtx, vtx_eq_iff]
    left; ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y i) * hR.four

/-- `σ` commutes with the scalars: the commutant is a direct product. -/
theorem sigma_scal (hR : Exceptional R) (c : Rˣ) (v : Vtx R) :
    sigma hR (scal c v) = scal c (sigma hR v) := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [scal_vtx, sigma_vtx, sigma_vtx, scal_vtx, vtx_eq_iff]
    left; ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hR.two_mul_unit (Units.isUnit c⁻¹)
    have h2 := hR.two_mul_unit (Units.isUnit c)
    linear_combination (y i) * h1 - (y i) * h2

theorem scal_one (v : Vtx R) : scal 1 v = v := by
  induction v using Vtx.ind with
  | H x y h => rw [scal_vtx, vtx_eq_iff]; left; simp

/-- If `2 ≠ 0`, `σ` is no scalar; in particular (`c = 1`) it has no fixed point. -/
theorem sigma_ne_scal (hR : Exceptional R) (h2 : (2 : R) ≠ 0) (c : Rˣ) (v : Vtx R) :
    sigma hR v ≠ scal c v := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [sigma_vtx, scal_vtx, Ne, vtx_eq_iff]
    rintro (e | e) <;> apply h2 <;>
      simpa [det2_add_right, det2_smul_right, det2_neg_right, det2_self, h] using congrArg (det2 x) e

/-- The ring computation of pages 93 to 95: a unimodular `(p, q)` whose class
is fixed by every `(1, t; 0, 1)` modulo `± 1`. -/
theorem stab_lemma {p q r s : R} (hdet : p * s - q * r = 1)
    (H : ∀ t : R, p = p + t * q ∨ (p = -(p + t * q) ∧ q = -q)) :
    (q = 0 ∧ IsUnit p) ∨ (Exceptional R ∧ q = 2 ∧ 2 * p = 2 ∧ IsUnit p) := by
  rcases H 1 with h1 | ⟨h1, -⟩
  · have hq : q = 0 := by linear_combination -h1
    left
    refine ⟨hq, IsUnit.of_mul_eq_one s ?_⟩
    rw [hq] at hdet; simpa using hdet
  · have hq : q = -2 * p := by linear_combination h1
    have hpp : p * (s + 2 * r) = 1 := by linear_combination hdet + r * h1
    have key : ∀ a : R, 2 * a = 0 ∨ 2 * a = 2 * p := by
      intro a
      have htq : (a * (s + 2 * r)) * q = -2 * a := by
        rw [hq]; linear_combination (-2 * a) * hpp
      rcases H (a * (s + 2 * r)) with e | ⟨e, -⟩
      · left; linear_combination e + htq
      · right; linear_combination htq - e
    have h2p : 2 * p = 2 := by
      rcases key 1 with e | e
      · have : (2 : R) = 0 := by simpa using e
        rw [this, zero_mul]
      · simpa using e.symm
    have hR : Exceptional R := fun a => (key a).imp id (fun e => e.trans h2p)
    right
    refine ⟨hR, ?_, h2p, IsUnit.of_mul_eq_one _ hpp⟩
    rw [hq]; linear_combination (-1 : R) * h2p - hR.four

theorem det2_e : det2 (![1, 0] : Fin 2 → R) ![0, 1] = 1 := by simp [det2]

/-- The matrix with columns `x` and `y`, in `SL(2, R)` when `x ∧ y = 1`. -/
def cols {x y : Fin 2 → R} (h : det2 x y = 1) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![x 0, y 0; x 1, y 1], by
    rw [Matrix.det_fin_two_of]; unfold det2 at h; linear_combination h⟩

theorem act_cols {x y : Fin 2 → R} (h : det2 x y = 1) : act (cols h) (vtx det2_e) = vtx h := by
  rw [act_vtx, vtx_eq_iff]; left
  apply vec_ext <;> simp [cols, mulVec_apply2]

theorem cols_mulVec {x y : Fin 2 → R} (h : det2 x y = 1) (w : Fin 2 → R) :
    (cols h).1 *ᵥ w = w 0 • x + w 1 • y := by
  apply vec_ext <;> simp [cols, mulVec_apply2] <;> ring

/-- **Pages 92 to 95, the commutant.** A map of `S_M = M*/±1` to itself that
commutes with `SL(2, R)` is a scalar `c ∈ R*`, or, when `2R ⊂ {0, 2}`, a scalar
times `σ`. No hypothesis on `R`; the map need not be assumed bijective. -/
theorem commutant (f : Vtx R → Vtx R) (hf : ∀ g v, f (act g v) = act g (f v)) :
    (∃ c : Rˣ, f = scal c) ∨ (∃ hR : Exceptional R, ∃ c : Rˣ, f = scal c ∘ sigma hR) := by
  obtain ⟨⟨w, w', hw⟩, hrep⟩ := Quotient.exists_rep (f (vtx (det2_e (R := R))))
  have hfw : f (vtx det2_e) = vtx hw := hrep.symm
  have H : ∀ t : R, w 0 = w 0 + t * w 1 ∨ (w 0 = -(w 0 + t * w 1) ∧ w 1 = -w 1) := by
    intro t
    let N : Matrix.SpecialLinearGroup (Fin 2) R :=
      ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩
    have hN : act N (vtx (det2_e (R := R))) = vtx det2_e := by
      rw [act_vtx, vtx_eq_iff]; left
      apply vec_ext <;> simp [N, mulVec_apply2]
    have := hf N (vtx det2_e)
    rw [hN, hfw, act_vtx, vtx_eq_iff] at this
    rcases this with e | e
    · left; simpa [N, mulVec_apply2] using congrFun e 0
    · right
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      simp only [N, mulVec_apply2, Pi.neg_apply] at e0 e1
      exact ⟨by simpa using e0, by simpa using e1⟩
  have hdet : w 0 * w' 1 - w 1 * w' 0 = 1 := hw
  have hval : ∀ (x y : Fin 2 → R) (h : det2 x y = 1),
      f (vtx h) = vtx (show det2 (w 0 • x + w 1 • y) ((cols h).1 *ᵥ w') = 1 by
        rw [← cols_mulVec h, det2_mulVec, (cols h).2, hw, one_mul]) := by
    intro x y h
    rw [← act_cols h, hf, hfw, act_vtx, vtx_eq_iff]
    left; exact cols_mulVec h w
  rcases stab_lemma hdet H with ⟨hq, ⟨u, hu⟩⟩ | ⟨hR, hq, h2p, ⟨u, hu⟩⟩
  · left; refine ⟨u, funext fun v => ?_⟩
    induction v using Vtx.ind with
    | H x y h => rw [hval, scal_vtx, vtx_eq_iff]; left; rw [hq, hu]; simp
  · right; refine ⟨hR, u, funext fun v => ?_⟩
    induction v using Vtx.ind with
    | H x y h =>
      rw [hval, Function.comp_apply, sigma_vtx, scal_vtx, vtx_eq_iff]; left
      rw [hq, ← hu]; ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(y i)) * h2p - 2 * (y i) * hu

/-- Converse: the scalars, and `σ` when `2R ⊂ {0, 2}`, commute with `SL(2, R)`;
with `σ² = 1` and `σ c = c σ` the commutant is `R*/±1 × {1, σ}`. -/
theorem commutant_converse (c : Rˣ) (hR : Exceptional R) (g) (v : Vtx R) :
    scal c (act g v) = act g (scal c v) ∧
      (scal c ∘ sigma hR) (act g v) = act g ((scal c ∘ sigma hR) v) := by
  refine ⟨scal_act c g v, ?_⟩
  simp only [Function.comp_apply, sigma_act, scal_act]

theorem sigma_eq_id_of_two (hR : Exceptional R) (h2 : (2 : R) = 0) : sigma hR = id := by
  funext v
  induction v using Vtx.ind with
  | H x y h => rw [sigma_vtx, id, vtx_eq_iff]; left; rw [h2, zero_smul, add_zero]

/-- Outside the exceptional case (`2R = {0, 2} ≠ {0}` fails), the commutant is
the scalars `R*/±1`. -/
theorem commutant_of_not_exceptional (hR : ¬ (Exceptional R ∧ (2 : R) ≠ 0))
    (f : Vtx R → Vtx R) (hf : ∀ g v, f (act g v) = act g (f v)) : ∃ c : Rˣ, f = scal c := by
  rcases commutant f hf with h | ⟨hE, c, hc⟩
  · exact h
  · refine ⟨c, ?_⟩
    have h2 : (2 : R) = 0 := by by_contra h2; exact hR ⟨hE, h2⟩
    rw [hc, sigma_eq_id_of_two hE h2]; rfl

/-- Over `Z/n` with `n ≠ 4`, the commutant of `SL(2, Z/n)` on `M*/±1` is the
group of scalars. -/
theorem commutant_zmod {n : ℕ} (hn : n ≠ 4) (f : Vtx (ZMod n) → Vtx (ZMod n))
    (hf : ∀ g v, f (act g v) = act g (f v)) : ∃ c : (ZMod n)ˣ, f = scal c :=
  commutant_of_not_exceptional (fun h => hn ((exceptional_zmod_iff n).1 h)) f hf

theorem exceptional_zmod_four : Exceptional (ZMod 4) := ((exceptional_zmod_iff 4).2 rfl).1

/-- **Z/4: σ is the antipody of the octahedron.** For `x ∧ y = 1` in `(Z/4)²`,
the vertices `z` not joined to `x` (`x ∧ z` not a unit) are `± x` and
`± (x + 2y)`, so `σ(ẋ)` is the one vertex other than `ẋ` not adjacent to it. -/
theorem zmod4_non_neighbours {x y z w : Fin 2 → ZMod 4} (h : det2 x y = 1)
    (hz : det2 z w = 1) (hn : ¬ IsUnit (det2 x z)) :
    z = x ∨ z = -x ∨ z = x + (2 : ZMod 4) • y ∨ z = -(x + (2 : ZMod 4) • y) := by
  have hd := decomp h z
  set a := det2 z y
  set b := det2 x z
  have hb : b = 0 ∨ b = 2 := by
    have h1 : b ≠ 1 := fun e => hn (e ▸ isUnit_one)
    have h3 : b ≠ 3 := fun e => hn (e ▸ IsUnit.of_mul_eq_one (3 : ZMod 4) (by decide))
    revert h1 h3; generalize b = b'; revert b'; decide
  have hw : a * det2 x w + b * det2 y w = 1 := by
    rw [hd, det2_add_left, det2_smul_left, det2_smul_left] at hz; exact hz
  have ha : a = 1 ∨ a = 3 := by
    revert hb hw; generalize a = a'; generalize b = b'; generalize det2 x w = u
    generalize det2 y w = v; revert a' b' u v; decide
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [hd]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · left; simp
  · right; right; left; simp
  · right; left; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    linear_combination (x i) * h4
  · right; right; right; ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    linear_combination (x i + y i) * h4

/-! ### A vertex and its star (pages 275 to 279) -/

theorem star_aux {α β : R} (H : ∀ s : R, α - s * β = 1 ∨ α - s * β = -1) :
    (α = 1 ∧ β = 0) ∨ (α = -1 ∧ β = 0) ∨
      (Exceptional R ∧ ((α = 1 ∧ β = 2) ∨ (α = -1 ∧ β = -2))) := by
  rcases H 0 with h0 | h0 <;> simp only [zero_mul, sub_zero] at h0
  · rcases H 1 with h1 | h1
    · left; exact ⟨h0, by linear_combination h0 - h1⟩
    · have hβ : β = 2 := by linear_combination h0 - h1
      right; right
      refine ⟨fun s => ?_, Or.inl ⟨h0, hβ⟩⟩
      rcases H s with e | e
      · left; linear_combination h0 - e - s * hβ
      · right; linear_combination h0 - e - s * hβ
  · rcases H 1 with h1 | h1
    · have hβ : β = -2 := by linear_combination h0 - h1
      right; right
      refine ⟨fun s => ?_, Or.inr ⟨h0, hβ⟩⟩
      rcases H s with e | e
      · right; linear_combination e - h0 + s * hβ
      · left; linear_combination e - h0 + s * hβ
    · right; left; exact ⟨h0, by linear_combination h0 - h1⟩

/-- **Pages 276 and 277, over any commutative ring.** Let `x ∧ y = 1`. A
vector `x'` has, type by type, the neighbours of `x` (`x ∧ z` a unit implies
`x' ∧ z = ± x ∧ z`) iff `x' = ± x`, or `2R ⊂ {0, 2}` and `x' = ± (x + 2y)`,
that is `ẋ' = σ(ẋ)`. No semi-local hypothesis is needed. -/
theorem same_star_iff {x y x' : Fin 2 → R} (h : det2 x y = 1) :
    (∀ z, IsUnit (det2 x z) → det2 x' z = det2 x z ∨ det2 x' z = -det2 x z) ↔
      x' = x ∨ x' = -x ∨
        (Exceptional R ∧ (x' = x + (2 : R) • y ∨ x' = -(x + (2 : R) • y))) := by
  constructor
  · intro H
    have hd := decomp h x'
    have H' : ∀ s : R, det2 x' y - s * det2 x x' = 1 ∨ det2 x' y - s * det2 x x' = -1 := by
      intro s
      have hz : det2 x (y + s • x) = 1 := by
        rw [det2_add_right, det2_smul_right, det2_self, h]; ring
      have e : det2 x' (y + s • x) = det2 x' y - s * det2 x x' := by
        rw [det2_add_right, det2_smul_right, det2_swap x' x]; ring
      have := H (y + s • x) (by rw [hz]; exact isUnit_one)
      rw [hz, e] at this; exact this
    rcases star_aux H' with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨hR, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · left; rw [hd, ha, hb]; simp
    · right; left; rw [hd, ha, hb]; simp
    · right; right; refine ⟨hR, Or.inl ?_⟩; rw [hd, ha, hb]; simp
    · right; right; refine ⟨hR, Or.inr ?_⟩; rw [hd, ha, hb]; ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]; ring
  · rintro (rfl | rfl | ⟨hR, rfl | rfl⟩) z hz
    · left; rfl
    · right; rw [det2_neg_left]
    · have e : det2 (x + (2 : R) • y) z = det2 x z - 2 * det2 z y := by
        rw [det2_add_left, det2_smul_left, det2_swap y z]; ring
      rw [e]
      rcases hR (det2 z y) with h2 | h2
      · left; rw [h2, sub_zero]
      · right; rw [h2]; linear_combination hR.two_mul_unit hz
    · have e : det2 (-(x + (2 : R) • y)) z = -(det2 x z - 2 * det2 z y) := by
        rw [det2_neg_left, det2_add_left, det2_smul_left, det2_swap y z]; ring
      rw [e]
      rcases hR (det2 z y) with h2 | h2
      · right; rw [h2, sub_zero]
      · left; rw [h2]; linear_combination -(hR.two_mul_unit hz)

theorem sigma_matrix_aux (hR : Exceptional R) {p q r s : R} (h : p * s - q * r = 1) :
    (2 * q = 2 * r ∧ 2 * p = 2 * q + 2 * s) ∨ (2 * p + 2 * q + 2 * r = 0 ∧ 2 * p = 2 * s) := by
  by_cases hz2 : (2 : R) = 0
  · left; simp [hz2]
  have h2 : (2 * p) * s - (2 * q) * r = 2 := by linear_combination 2 * h
  have h22 : (2 : R) + 2 = 0 := by linear_combination hR.four
  rcases hR p with hp | hp <;> rcases hR q with hq | hq <;> rcases hR r with hr | hr <;>
    rcases hR s with hs | hs <;> simp only [hp, hq, hr, hs, zero_mul, add_zero, zero_add,
      sub_zero, zero_sub, sub_self, h22] at h2 ⊢ <;>
    first
    | exact absurd h2.symm hz2
    | simp

/-- The matrix with rows `(1, 2)` and `(2, -1)`. -/
def matA : Matrix (Fin 2) (Fin 2) R := !![1, 2; 2, -1]

/-- **Pages 277 to 279.** When `2R ⊂ {0, 2}`, `σ` is induced by the matrix
`A` with rows `(1, 2)` and `(2, -1)`: `A x = ± (x + 2y)` whenever `x ∧ y = 1`.
`A` has determinant `-1` and `A² = 1`. -/
theorem matA_mulVec (hR : Exceptional R) {x y : Fin 2 → R} (h : det2 x y = 1) :
    matA *ᵥ x = x + (2 : R) • y ∨ matA *ᵥ x = -(x + (2 : R) • y) := by
  have h' : x 0 * y 1 - x 1 * y 0 = 1 := h
  have h4 := hR.four
  rcases sigma_matrix_aux hR h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    apply vec_ext <;> simp [matA, mulVec_apply2]
    · linear_combination e1
    · linear_combination e2
  · right
    apply vec_ext <;> simp [matA, mulVec_apply2]
    · linear_combination e1
    · linear_combination e2 + (y 1) * h4

theorem matA_det (hR : Exceptional R) : (matA : Matrix (Fin 2) (Fin 2) R).det = -1 := by
  rw [matA, Matrix.det_fin_two_of]; linear_combination -hR.four

theorem matA_sq (hR : Exceptional R) : (matA : Matrix (Fin 2) (Fin 2) R) * matA = 1 := by
  have h4 := hR.four
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matA, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h4

/-! ### Distance at most three over a semi-local ring (pages 19 and 20) -/

/-- Stable range one for a semi-local ring (finitely many maximal ideals):
if `(d, d')` is unimodular, some `a d + d'` is a unit. This is the input that
page 20 cites as known (« on sait que »); it is `IsCoprime.exists_isUnit_add_mul`
(`Upstream/`). -/
theorem exists_isUnit_mul_add [Finite (MaximalSpectrum R)] {d d' a₀ b₀ : R}
    (h : a₀ * d + b₀ * d' = 1) : ∃ a : R, IsUnit (a * d + d') := by
  obtain ⟨a, ha⟩ := IsCoprime.exists_isUnit_add_mul (a := d') (b := d)
    ⟨b₀, a₀, by linear_combination h⟩
  exact ⟨a, by rwa [add_comm]⟩

/-- **Page 20, (47).** Over a semi-local ring, for any gauge `e ∈ R*` and any
two unimodular `x`, `y` of `R²`, there are unimodular `z₁`, `z₂` with
`x ∧ z₁ = z₁ ∧ z₂ = z₂ ∧ y = e`: any two vertices of `SP_M` are at distance
at most `3`. -/
theorem semilocal_dist_three [Finite (MaximalSpectrum R)] (e : Rˣ) {x y : Fin 2 → R}
    (hx : Unimod x) (hy : Unimod y) :
    ∃ z₁ z₂ : Fin 2 → R, Unimod z₁ ∧ Unimod z₂ ∧
      det2 x z₁ = e ∧ det2 z₁ z₂ = e ∧ det2 z₂ y = e := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  have pl : det2 w y' * det2 x y + (-det2 x y') * det2 w y = 1 := by
    have : det2 w y' * det2 x y + (-det2 x y') * det2 w y = det2 x w * det2 y y' := by
      unfold det2; ring
    rw [this, hw, hy', one_mul]
  obtain ⟨a, u, hu⟩ := exists_isUnit_mul_add pl
  set z := a • x + w with hz
  have hxz : det2 x z = 1 := by rw [hz, det2_add_right, det2_smul_right, det2_self, hw]; ring
  have hzy : det2 z y = u := by
    rw [hu, hz, det2_add_left, det2_smul_left]
  set z₁ := (e : R) • z
  have h1 : det2 x z₁ = e := by rw [det2_smul_right, hxz, mul_one]
  have h1y : det2 z₁ y = e * u := by rw [det2_smul_left, hzy]
  set z₂ := (↑u⁻¹ : R) • (z₁ + y)
  have h12 : det2 z₁ z₂ = e := by
    rw [det2_smul_right, det2_add_right, det2_self, zero_add, h1y, mul_left_comm, Units.inv_mul,
      mul_one]
  have h2y : det2 z₂ y = e := by
    rw [det2_smul_left, det2_add_left, det2_self, add_zero, h1y, mul_left_comm, Units.inv_mul,
      mul_one]
  refine ⟨z₁, z₂, unimod_of_isUnit (z := y) ?_, unimod_of_isUnit (z := y) ?_, h1, h12, h2y⟩
  · rw [h1y]; exact (e * u).isUnit
  · rw [h2y]; exact e.isUnit

/-- A local ring is semi-local. -/
theorem finite_maximalSpectrum_of_local [IsLocalRing R] : Finite (MaximalSpectrum R) := by
  have : Subsingleton (MaximalSpectrum R) := ⟨fun a b => MaximalSpectrum.ext
    ((IsLocalRing.eq_maximalIdeal a.isMaximal).trans (IsLocalRing.eq_maximalIdeal b.isMaximal).symm)⟩
  exact Finite.of_subsingleton

/-- The case of a local ring (in particular a field). -/
theorem local_dist_three [IsLocalRing R] (e : Rˣ) {x y : Fin 2 → R}
    (hx : Unimod x) (hy : Unimod y) :
    ∃ z₁ z₂ : Fin 2 → R, Unimod z₁ ∧ Unimod z₂ ∧
      det2 x z₁ = e ∧ det2 z₁ z₂ = e ∧ det2 z₂ y = e :=
  have := finite_maximalSpectrum_of_local (R := R)
  semilocal_dist_three e hx hy

/-- A finite ring is semi-local. -/
theorem finite_maximalSpectrum_of_finite [Finite R] : Finite (MaximalSpectrum R) :=
  Finite.of_injective (fun m : MaximalSpectrum R => (m.asIdeal : Set R))
    (fun _ _ e => MaximalSpectrum.ext (SetLike.coe_injective e))

/-- The case `Λ = Z/n`, `n ≥ 1` (for `n ≥ 5` this is Singerman and Strudwick's
Theorem 11, with equality). -/
theorem zmod_dist_three (n : ℕ) [NeZero n] (e : (ZMod n)ˣ) {x y : Fin 2 → ZMod n}
    (hx : Unimod x) (hy : Unimod y) :
    ∃ z₁ z₂ : Fin 2 → ZMod n, Unimod z₁ ∧ Unimod z₂ ∧
      det2 x z₁ = e ∧ det2 z₁ z₂ = e ∧ det2 z₂ y = e :=
  have := finite_maximalSpectrum_of_finite (R := ZMod n)
  semilocal_dist_three e hx hy

/-! ### The twist of one end, in the model (pages 96 to 101, 136 to 140) -/

theorem pm_mul_cancel {a b : R} (μ : Rˣ) :
    ((μ : R) * a = μ * b ∨ (μ : R) * a = -(μ * b)) ↔ (a = b ∨ a = -b) := by
  constructor
  · rintro (h | h)
    · left; simpa using congrArg ((↑μ⁻¹ : R) * ·) h
    · right; simpa [mul_neg] using congrArg ((↑μ⁻¹ : R) * ·) h
  · rintro (rfl | rfl)
    · left; rfl
    · right; ring

/-- Twisting one end by the scalar `μ` changes the type `± e` of an edge into
`± μ e`: the edge set `A_{T_μ}` of `P_{M, i}` is that of `P_{M, μ i}`. -/
theorem twist_edge (μ : Rˣ) (e : R) (x y : Fin 2 → R) :
    (det2 x ((μ : R) • y) = μ * e ∨ det2 x ((μ : R) • y) = -(μ * e)) ↔
      (det2 x y = e ∨ det2 x y = -e) := by
  rw [det2_smul_right]; exact pm_mul_cancel μ

/-- The star of `ẋ` in `P_{M, i}` (`i = ± e`) is, as a set, the star of
`μ ẋ` in `P_{M, μ i}`: `Et_{A₀}(s) = Et_{A_λ}(λ s)`. -/
theorem twist_star (μ : Rˣ) (e : R) (x z : Fin 2 → R) :
    (det2 ((μ : R) • x) z = μ * e ∨ det2 ((μ : R) • x) z = -(μ * e)) ↔
      (det2 x z = e ∨ det2 x z = -e) := by
  rw [det2_smul_left]; exact pm_mul_cancel μ

/-- The star of `ẋ` in `P_{M, ±e}` is the line `y + R x` (pages 14 to 16). -/
theorem star_line (e : Rˣ) {x y z : Fin 2 → R} (hy : det2 x y = e) (hz : det2 x z = e) :
    z = y + det2 z ((↑e⁻¹ : R) • y) • x := by
  have h1 : det2 x ((↑e⁻¹ : R) • y) = 1 := by rw [det2_smul_right, hy]; simp
  have := decomp h1 z
  rwa [hz, smul_smul, Units.mul_inv, one_smul, add_comm] at this

/-- **Page 67, formula (178): the faces of a type are the triangles of its
edges.** If `x ∧ y = e` is a unit, `x ∧ z = ± e` and `z ∧ y = ± e`, then
`z = ± x ± y`. -/
theorem triangle_face (e : Rˣ) {x y z : Fin 2 → R} (hy : det2 x y = e)
    (hxz : det2 x z = e ∨ det2 x z = -e) (hzy : det2 z y = e ∨ det2 z y = -e) :
    ∃ a b : R, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ z = a • x + b • y := by
  have h1 : det2 x ((↑e⁻¹ : R) • y) = 1 := by rw [det2_smul_right, hy]; simp
  have hd := decomp h1 z
  rw [det2_smul_right, smul_smul] at hd
  refine ⟨↑e⁻¹ * det2 z y, det2 x z * ↑e⁻¹, ?_, ?_, hd⟩
  · rcases hzy with h | h <;> rw [h] <;> simp
  · rcases hxz with h | h <;> rw [h] <;> simp

/-- **The star polygon (pages 138 and 139, To 6), in the model.** Let
`x ∧ y = e` with `e` a unit, so that the star of `ẋ` in `P_{M, ±e}` is
`k ↦ (y + k x)˙`. Two of its points `y + k x`, `y + k' x` are joined by an edge
of type `± μ e` iff `k - k' = ± μ`. For `μ = 1` this is the polygon of the
star in `P_{M, ±e}`; in `P_{M, ±μe}` the same set carries the `μ`-th star
polygon. The exponent is `μ` itself, as the reading computes. -/
theorem link_polygon (e μ : Rˣ) {x y : Fin 2 → R} (hy : det2 x y = e) (k k' : R) :
    (det2 (y + k • x) (y + k' • x) = μ * e ∨ det2 (y + k • x) (y + k' • x) = -(μ * e)) ↔
      (k - k' = μ ∨ k - k' = -μ) := by
  have e1 : det2 (y + k • x) (y + k' • x) = (k - k') * e := by
    simp only [det2_add_left, det2_add_right, det2_smul_left, det2_smul_right, det2_self,
      det2_swap x y, hy]; ring
  rw [e1]
  constructor
  · rintro (h | h)
    · left; simpa using congrArg (· * (↑e⁻¹ : R)) h
    · right; simpa [neg_mul] using congrArg (· * (↑e⁻¹ : R)) h
  · rintro (h | h) <;> rw [h]
    · left; ring
    · right; ring

/-- The scalar `μ` carries the star of `ẋ` in `P_{M, ±e}`, indexed by
`k ↦ y + k x`, onto the star of `ẋ` in `P_{M, ±μe}`, indexed by
`j ↦ μ y + j x` (`x ∧ μ y = μ e`), by `k ↦ μ k`: a translation by `k`
steps becomes a translation by `μ k` steps (`λ_{Γ, s} = ± μ`, page 99). -/
theorem twist_index (μ : R) (x y : Fin 2 → R) (k : R) :
    μ • (y + k • x) = μ • y + (μ * k) • x ∧ det2 x (μ • y) = μ * det2 x y := by
  refine ⟨?_, det2_smul_right μ x y⟩
  rw [smul_add, smul_smul]

/-! ### The distance from a vertex to its image, in the model (pages 187 and 188) -/

variable (R) in
/-- `ẋ` and `ż` are joined by an edge of type `± e` (of `P_{M, ±e}`) when
`x ∧ z = ± e`; for `e = 1` and `R = Z/n` this is the Farey map mod `n`. -/
def Adj (e : R) : Vtx R → Vtx R → Prop :=
  Quotient.lift₂ (fun a b => det2 a.1 b.1 = e ∨ det2 a.1 b.1 = -e) (by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    apply propext
    rcases h₁ with h | h <;> rcases h₂ with h' | h' <;>
      simp only [h, h', det2_neg_left, det2_neg_right, neg_neg, neg_eq_iff_eq_neg] <;>
        tauto)

theorem adj_vtx (e : R) {x y z w : Fin 2 → R} (h : det2 x y = 1) (h' : det2 z w = 1) :
    Adj R e (vtx h) (vtx h') ↔ (det2 x z = e ∨ det2 x z = -e) := Iff.rfl

theorem units_pm_of_mul {c e : Rˣ} (h : (c : R) * e = e ∨ (c : R) * e = -e) :
    c = 1 ∨ c = -1 := by
  rcases h with h | h
  · left; ext; simpa using congrArg (· * (↑e⁻¹ : R)) h
  · right; ext; simpa using congrArg (· * (↑e⁻¹ : R)) h

/-- A scalar `μ ≠ ± 1` moves every vertex: `μ ẋ ≠ ẋ`. -/
theorem scal_ne_self {c : Rˣ} (hc : c ≠ 1 ∧ c ≠ -1) (v : Vtx R) : scal c v ≠ v := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [scal_vtx, Ne, vtx_eq_iff]
    rintro (e | e) <;> have := congrArg (det2 · y) e <;>
      simp only [det2_smul_left, det2_neg_left, h, mul_one] at this
    · exact hc.1 (Units.ext this)
    · exact hc.2 (Units.ext this)

/-- Distance `1` in the model: `μ ẋ` is never adjacent to `ẋ`, since
`x ∧ μ x = 0`. -/
theorem not_adj_scal [Nontrivial R] (e c : Rˣ) (v : Vtx R) : ¬ Adj R e v (scal c v) := by
  induction v using Vtx.ind with
  | H x y h =>
    rw [scal_vtx, adj_vtx, det2_smul_right, det2_self, mul_zero]
    simp [e.ne_zero.symm]

/-- Distance `2` in the model: if `ż` is adjacent to `ẋ` and to `μ ẋ`, then
`μ e = ± e`, so `μ = ± 1`. -/
theorem no_common_nbr_scal (e : Rˣ) {c : Rˣ} (hc : c ≠ 1 ∧ c ≠ -1) (v : Vtx R) :
    ¬ ∃ w, Adj R e v w ∧ Adj R e w (scal c v) := by
  rintro ⟨w, hw1, hw2⟩
  induction v using Vtx.ind with
  | H x y h =>
  induction w using Vtx.ind with
  | H z z' hz =>
    rw [adj_vtx] at hw1
    rw [scal_vtx, adj_vtx, det2_smul_right, det2_swap] at hw2
    have : (c : R) * e = e ∨ (c : R) * e = -e := by
      rcases hw1 with h1 | h1 <;> rw [h1] at hw2 <;> rcases hw2 with h2 | h2
      · right; linear_combination -h2
      · left; linear_combination -h2
      · left; linear_combination h2
      · right; linear_combination h2
    exact (units_pm_of_mul this).elim hc.1 hc.2

/-- The three exclusions for a scalar `μ ≠ ± 1`. -/
theorem scal_dist [Nontrivial R] (e : Rˣ) {c : Rˣ} (hc : c ≠ 1 ∧ c ≠ -1) (v : Vtx R) :
    scal c v ≠ v ∧ ¬ Adj R e v (scal c v) ∧ ¬ ∃ w, Adj R e v w ∧ Adj R e w (scal c v) :=
  ⟨scal_ne_self hc v, not_adj_scal e c v, no_common_nbr_scal e hc v⟩

/-- `σ(ẋ)` and `ẋ` have a common neighbour of each type: `(e y)˙`. -/
theorem sigma_common_nbr (hR : Exceptional R) (e : Rˣ) (v : Vtx R) :
    ∃ w, Adj R e v w ∧ Adj R e w (sigma hR v) := by
  induction v using Vtx.ind with
  | H x y h =>
    have hw : det2 ((e : R) • y) ((↑e⁻¹ : R) • -x) = 1 := by
      rw [det2_smul_left, det2_smul_right, det2_neg_right, det2_swap, h]; simp
    refine ⟨vtx hw, ?_, ?_⟩
    · rw [adj_vtx, det2_smul_right, h, mul_one]; left; rfl
    · rw [sigma_vtx, adj_vtx, det2_smul_left, det2_add_right, det2_smul_right, det2_self,
        det2_swap, h]
      right; ring

theorem scal_eq_id_iff (c : Rˣ) : scal (R := R) c = id ↔ c = 1 ∨ c = -1 := by
  have h1 : scal (R := R) 1 = id := funext scal_one
  rw [← h1, scal_eq_scal_iff]

/-- **Page 188, (32) a″), in the model, over any commutative ring.** Let `λ ≠ 1`
be a map of `M*/±1` commuting with `SL(2, R)` and `e ∈ R*`. For every vertex
`v`: `λ v ≠ v`; `λ v` is not adjacent to `v` in `P_{M, ±e}`; and `v`, `λ v`
have a common neighbour iff `R` is exceptional (`2R ⊂ {0, 2}`) and `λ = σ`, the
octahedral antipody for `Z/4`. -/
theorem commutant_dist [Nontrivial R] (e : Rˣ) (f : Vtx R → Vtx R)
    (hf : ∀ g v, f (act g v) = act g (f v)) (hf1 : f ≠ id) (v : Vtx R) :
    f v ≠ v ∧ ¬ Adj R e v (f v) ∧
      ((∃ w, Adj R e v w ∧ Adj R e w (f v)) ↔ ∃ hR : Exceptional R, f = sigma hR) := by
  have key : f v ≠ v ∧ ¬ Adj R e v (f v) ∧
      ((∃ w, Adj R e v w ∧ Adj R e w (f v)) → ∃ hR : Exceptional R, f = sigma hR) := by
    have hscal : ∀ c : Rˣ, f = scal c → f v ≠ v ∧ ¬ Adj R e v (f v) ∧
        ((∃ w, Adj R e v w ∧ Adj R e w (f v)) → ∃ hR : Exceptional R, f = sigma hR) := by
      rintro c rfl
      have hc : c ≠ 1 ∧ c ≠ -1 := not_or.mp (mt (scal_eq_id_iff c).2 hf1)
      obtain ⟨a, b, d⟩ := scal_dist e hc v
      exact ⟨a, b, fun h => absurd h d⟩
    rcases commutant f hf with ⟨c, hc⟩ | ⟨hR, c, hc⟩
    · exact hscal c hc
    by_cases h2 : (2 : R) = 0
    · exact hscal c (by rw [hc, sigma_eq_id_of_two hR h2]; rfl)
    subst hc
    induction v using Vtx.ind with
    | H x y h =>
    have hfv : (scal c ∘ sigma hR) (vtx h) = vtx (det2_scal c (det2_sigma h)) := by
      rw [Function.comp_apply, sigma_vtx, scal_vtx]
    have h2c := hR.two_mul_unit c.isUnit
    rw [hfv]
    refine ⟨?_, ?_, ?_⟩
    · rw [Ne, vtx_eq_iff]
      rintro (e' | e') <;> apply h2 <;> have := congrArg (det2 x) e' <;>
        simp only [det2_smul_right, det2_add_right, det2_self, det2_neg_right, h] at this
      · linear_combination this - h2c
      · linear_combination this - h2c
    · rw [adj_vtx, det2_smul_right, det2_add_right, det2_smul_right, det2_self, h]
      intro he
      have hu : IsUnit (2 : R) := by
        rw [show (c : R) * (0 + 2 * 1) = 2 by linear_combination h2c] at he
        exact he.elim (fun he => he ▸ e.isUnit) fun he => he ▸ e.isUnit.neg
      exact h2 (hu.mul_left_cancel (by linear_combination hR.four))
    · rintro ⟨w, hw1, hw2⟩
      induction w using Vtx.ind with
      | H z z' hz =>
      rw [adj_vtx] at hw1
      rw [adj_vtx, det2_smul_right, det2_add_right, det2_smul_right, det2_swap x z] at hw2
      have h2e := hR.two_mul_unit e.isUnit
      have hcpm : (c : R) * e = e ∨ (c : R) * e = -e := by
        rcases hR (det2 z y) with hb | hb <;> rw [hb] at hw2 <;>
          rcases hw1 with h1 | h1 <;> rw [h1] at hw2 <;> rcases hw2 with h3 | h3
        · right; linear_combination -h3
        · left; linear_combination -h3
        · left; linear_combination h3
        · right; linear_combination h3
        · left; linear_combination h3 + c * h2e
        · right; linear_combination h3 + c * h2e
        · right; linear_combination -h3 + c * h2e + c * hR.four
        · left; linear_combination -h3 + c * h2e + c * hR.four
      exact ⟨hR, by rw [(scal_eq_id_iff c).2 (units_pm_of_mul hcpm)]; rfl⟩
  exact ⟨key.1, key.2.1, key.2.2, fun ⟨hR, hfs⟩ => hfs ▸ sigma_common_nbr hR e v⟩

/-- Over a semi-local ring, any two vertices are joined in `P_{M, ±e}` by a
path of length `3` (from `semilocal_dist_three`). -/
theorem adj_path_three [Finite (MaximalSpectrum R)] (e : Rˣ) (v v' : Vtx R) :
    ∃ w₁ w₂, Adj R e v w₁ ∧ Adj R e w₁ w₂ ∧ Adj R e w₂ v' := by
  induction v using Vtx.ind with
  | H x y h =>
  induction v' using Vtx.ind with
  | H x' y' h' =>
    obtain ⟨z₁, z₂, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, h1, h2, h3⟩ := semilocal_dist_three e ⟨y, h⟩ ⟨y', h'⟩
    exact ⟨vtx ha₁, vtx ha₂, Or.inl h1, Or.inl h2, Or.inl h3⟩

/-- **The finding in the model, over a semi-local ring.** If `λ ≠ 1` commutes
with `SL(2, R)` and is not `σ`, every vertex `v` is at distance exactly `3`
from `λ v` in `P_{M, ±e}`: `λ v ≠ v`, not adjacent, no common neighbour, and a
path of length `3`. -/
theorem commutant_dist_three [Nontrivial R] [Finite (MaximalSpectrum R)] (e : Rˣ)
    (f : Vtx R → Vtx R) (hf : ∀ g v, f (act g v) = act g (f v)) (hf1 : f ≠ id)
    (hσ : ¬ ∃ hR : Exceptional R, f = sigma hR) (v : Vtx R) :
    f v ≠ v ∧ ¬ Adj R e v (f v) ∧ (¬ ∃ w, Adj R e v w ∧ Adj R e w (f v)) ∧
      ∃ w₁ w₂, Adj R e v w₁ ∧ Adj R e w₁ w₂ ∧ Adj R e w₂ (f v) := by
  obtain ⟨a, b, c⟩ := commutant_dist e f hf hf1 v
  exact ⟨a, b, fun h => hσ (c.1 h), adj_path_three e v (f v)⟩

/-- **The model case of the finding: the Farey map mod `n`.** For `n ≥ 2`, a unit
`μ ≠ ± 1` of `Z/n` and any type `± e`, every vertex is at distance exactly `3`
from its image under `μ` (for `e = 1`: Singerman and Strudwick, Theorem 9). -/
theorem zmod_scal_dist_three {n : ℕ} (hn : 1 < n) (e : (ZMod n)ˣ) {μ : (ZMod n)ˣ}
    (hμ : μ ≠ 1 ∧ μ ≠ -1) (v : Vtx (ZMod n)) :
    scal μ v ≠ v ∧ ¬ Adj (ZMod n) e v (scal μ v) ∧
      (¬ ∃ w, Adj (ZMod n) e v w ∧ Adj (ZMod n) e w (scal μ v)) ∧
      ∃ w₁ w₂, Adj (ZMod n) e v w₁ ∧ Adj (ZMod n) e w₁ w₂ ∧ Adj (ZMod n) e w₂ (scal μ v) := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨hn⟩
  have := finite_maximalSpectrum_of_finite (R := ZMod n)
  obtain ⟨a, b, c⟩ := scal_dist e hμ v
  exact ⟨a, b, c, adj_path_three e v _⟩

end RankTwo

/-! ## The « fait mirifique » and To 6 (pages 136 to 140, 184 to 187)

A polygon structure on a set `E` with `n` elements is the cycle graph of a
bijection `φ : Z/n ≃ E`; its `ν`-th star polygon joins `φ k` and `φ (k ± ν)`.
`(Z/n)*` acts on polygon structures through `(Z/n)*/±1`, faithfully for `n ≥ 3`
(`polygonAction`, `twist_eq_twist_iff`). To 6 is then stated for an abstract
graph (`ToSix`), with its consequences, and checked in the model `P_{M, ±e}`. -/

section StarPolygon

variable {n : ℕ} {E : Type*}

/-- The `ν`-th star polygon of the indexing `φ`: `a ~ b` iff `φ⁻¹ b - φ⁻¹ a = ± ν`. -/
def cyc (φ : ZMod n ≃ E) (ν : ZMod n) (a b : E) : Prop :=
  φ.symm b - φ.symm a = ν ∨ φ.symm b - φ.symm a = -ν

variable (n) in
/-- `P` is a polygon structure: the cycle graph `k ~ k ± 1` of some indexing by `Z/n`. -/
def IsPolygon (P : E → E → Prop) : Prop := ∃ φ : ZMod n ≃ E, P = cyc φ 1

variable (n E) in
/-- `Pol(E)`, the polygon structures on `E`. -/
def Pol := {P : E → E → Prop // IsPolygon n P}

theorem two_ne_zero_of_lt (hn : 2 < n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff 2 n).1 (by exact_mod_cast h))
  omega

theorem pm_one_mul {d x ν : ZMod n} (hd : d = 1 ∨ d = -1) :
    (d * x = ν ∨ d * x = -ν) ↔ (x = ν ∨ x = -ν) := by
  rcases hd with rfl | rfl
  · simp
  · simp only [neg_one_mul, neg_eq_iff_eq_neg, neg_neg]; tauto

/-- An injective map of `Z/n` (`n ≥ 3`) preserving the cycle `k ~ k + 1` is
`k ↦ ± k + c`: the automorphisms of the `n`-gon are dihedral. -/
theorem affine_of_adj (hn : 2 < n) (f : ZMod n → ZMod n) (hinj : Function.Injective f)
    (hf : ∀ a b : ZMod n, b - a = 1 → f b - f a = 1 ∨ f b - f a = -1) :
    ∃ d : ZMod n, (d = 1 ∨ d = -1) ∧ ∀ k, f k = d * k + f 0 := by
  have : NeZero n := ⟨by omega⟩
  have h2 := two_ne_zero_of_lt hn
  obtain ⟨d, hd⟩ : ∃ d, d = f 1 - f 0 := ⟨_, rfl⟩
  have hd1 : d = 1 ∨ d = -1 := hd ▸ hf 0 1 (by ring)
  have key : ∀ m : ℕ, f m = d * m + f 0 ∧ f (m + 1) = d * (m + 1) + f 0 := by
    intro m
    induction m with
    | zero => simp [hd]
    | succ m ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hf ((m : ZMod n) + 1) ((m : ZMod n) + 1 + 1) (by ring)
      have hne : f ((m : ZMod n) + 1 + 1) ≠ f m := fun h' => h2 (by
        have := hinj h'; linear_combination this)
      push_cast
      rcases hd1 with hd1 | hd1 <;> rcases h with h | h
      · linear_combination h + ih.2 - hd1
      · exact absurd (by linear_combination h + ih.2 - ih.1 + hd1) hne
      · exact absurd (by linear_combination h + ih.2 - ih.1 + hd1) hne
      · linear_combination h + ih.2 - hd1
  refine ⟨d, hd1, fun k => ?_⟩
  have := (key k.val).1
  rwa [ZMod.natCast_zmod_val] at this

/-- The `ν`-th star polygon depends only on the polygon, not on its indexing. -/
theorem cyc_congr (hn : 2 < n) {φ ψ : ZMod n ≃ E} (h : cyc φ 1 = cyc ψ 1) (ν : ZMod n) :
    cyc φ ν = cyc ψ ν := by
  obtain ⟨d, hd, hf⟩ := affine_of_adj hn (fun k => ψ.symm (φ k))
    (ψ.symm.injective.comp φ.injective) (fun a b hab => by
      have : cyc φ 1 (φ a) (φ b) := by simp [cyc, hab]
      rw [h] at this; exact this)
  have hx : ∀ x, ψ.symm x = d * φ.symm x + ψ.symm (φ 0) := fun x => by
    simpa using hf (φ.symm x)
  funext a b
  apply propext
  simp only [cyc]
  rw [hx a, hx b, show d * φ.symm b + ψ.symm (φ 0) - (d * φ.symm a + ψ.symm (φ 0)) =
    d * (φ.symm b - φ.symm a) by ring, pm_one_mul hd]

/-- Re-indexing a polygon by `k ↦ ν k`. -/
def reindex (φ : ZMod n ≃ E) (ν : (ZMod n)ˣ) : ZMod n ≃ E := (Units.mulLeft ν).trans φ

theorem cyc_reindex (φ : ZMod n ≃ E) (ν : (ZMod n)ˣ) (μ : ZMod n) :
    cyc (reindex φ ν) μ = cyc φ (ν * μ) := by
  funext a b
  apply propext
  have hs : ∀ x, (reindex φ ν).symm x = ↑ν⁻¹ * φ.symm x := fun x => by
    simp [reindex, Units.mulLeft]
  simp only [cyc, hs, ← mul_sub]
  constructor
  · rintro (h | h)
    · left; rw [← h, ← mul_assoc]; simp
    · right; rw [← mul_neg, ← h, ← mul_assoc]; simp
  · rintro (h | h)
    · left; rw [h, ← mul_assoc]; simp
    · right; rw [h, ← mul_neg, ← mul_assoc]; simp


theorem cyc_neg (φ : ZMod n ≃ E) (ν : ZMod n) : cyc φ (-ν) = cyc φ ν := by
  funext a b; simp only [cyc, neg_neg]; exact propext or_comm

theorem isPolygon_cyc (φ : ZMod n ≃ E) (ν : (ZMod n)ˣ) : IsPolygon n (cyc φ ν) :=
  ⟨reindex φ ν, by rw [cyc_reindex, mul_one]⟩

/-- The `ν`-th star polygon of a polygon structure. -/
noncomputable def twist (ν : (ZMod n)ˣ) (P : Pol n E) : Pol n E :=
  ⟨cyc P.2.choose ν, isPolygon_cyc _ ν⟩

theorem twist_of_eq (hn : 2 < n) (ν : (ZMod n)ˣ) {P : Pol n E} {φ : ZMod n ≃ E}
    (h : P.1 = cyc φ 1) : (twist ν P).1 = cyc φ ν :=
  cyc_congr hn (P.2.choose_spec.symm.trans h) ν

theorem twist_one (hn : 2 < n) (P : Pol n E) : twist 1 P = P :=
  Subtype.ext ((twist_of_eq hn 1 P.2.choose_spec).trans P.2.choose_spec.symm)

theorem twist_twist (hn : 2 < n) (μ ν : (ZMod n)ˣ) (P : Pol n E) :
    twist μ (twist ν P) = twist (ν * μ) P := by
  obtain ⟨φ, hφ⟩ := P.2
  apply Subtype.ext
  have h1 : (twist ν P).1 = cyc (reindex φ ν) 1 := by
    rw [twist_of_eq hn ν hφ, cyc_reindex, mul_one]
  rw [twist_of_eq hn μ h1, twist_of_eq hn _ hφ, cyc_reindex, Units.val_mul]

theorem twist_neg (ν : (ZMod n)ˣ) (P : Pol n E) : twist (-ν) P = twist ν P :=
  Subtype.ext (by simp only [twist, Units.val_neg, cyc_neg])

theorem twist_eq_self_iff (hn : 2 < n) (ν : (ZMod n)ˣ) (P : Pol n E) :
    twist ν P = P ↔ ν = 1 ∨ ν = -1 := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := P.2
    have h1 := congrArg Subtype.val h
    rw [twist_of_eq hn ν hφ, hφ] at h1
    have : cyc φ ν (φ 0) (φ ν) := by simp [cyc]
    rw [h1] at this
    simp only [cyc, Equiv.symm_apply_apply, sub_zero] at this
    rcases this with h | h
    · left; exact Units.ext h
    · right; exact Units.ext (by simp [h])
  · rintro (rfl | rfl)
    · exact twist_one hn P
    · rw [twist_neg, twist_one hn]

theorem twist_eq_twist_iff (hn : 2 < n) (ν ν' : (ZMod n)ˣ) (P : Pol n E) :
    twist ν' P = twist ν P ↔ ν' = ν ∨ ν' = -ν := by
  have key : twist ν' P = twist ν P ↔ twist (ν' * ν⁻¹) P = P := by
    constructor
    · intro h; rw [← twist_twist hn, h, twist_twist hn, mul_inv_cancel, twist_one hn]
    · intro h
      have := congrArg (twist ν) h
      rwa [twist_twist hn, show ν' * ν⁻¹ * ν = ν' by group] at this
  rw [key, twist_eq_self_iff hn]
  constructor
  · rintro (h | h) <;> [left; right] <;> simpa using congrArg (· * ν) h
  · rintro (rfl | rfl) <;> [left; right] <;> simp

/-- **The « fait mirifique » (page 138).** `(Z/n)*` acts on the polygon
structures of `E`, through `(Z/n)*/±1`. -/
noncomputable instance polygonAction [Fact (2 < n)] : MulAction (ZMod n)ˣ (Pol n E) where
  smul := twist
  one_smul := twist_one Fact.out
  mul_smul a b P := by
    change twist (a * b) P = twist a (twist b P)
    rw [twist_twist Fact.out, mul_comm]

/-- The rotation `φ k ↦ φ (k + 1)` of an indexed polygon. -/
def rot (φ : ZMod n ≃ E) : Equiv.Perm E := φ.symm.trans ((Equiv.addRight 1).trans φ)

theorem rot_pow (φ : ZMod n ≃ E) (k : ℕ) (x : E) : (rot φ ^ k) x = φ (φ.symm x + k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp only [rot, Equiv.trans_apply, Equiv.coe_addRight, Equiv.symm_apply_apply]
    push_cast; ring_nf

/-- **Pages 184 to 187.** Two polygon structures on `E` with the same group of
rotations differ by a star twist. -/
theorem exists_twist_of_zpowers_rot (hn : 0 < n) {φ ψ : ZMod n ≃ E}
    (h : Subgroup.zpowers (rot ψ) = Subgroup.zpowers (rot φ)) :
    ∃ ν : (ZMod n)ˣ, cyc ψ 1 = cyc φ ν := by
  have : NeZero n := ⟨by omega⟩
  have : Finite E := Finite.of_equiv _ φ
  have hm : rot ψ ∈ Subgroup.zpowers (rot φ) := h ▸ Subgroup.mem_zpowers _
  rw [← mem_powers_iff_mem_zpowers] at hm
  obtain ⟨m, hm⟩ := hm
  set c := φ.symm (ψ 0)
  have hk : ∀ k : ZMod n, φ.symm (ψ k) = c + m * k := by
    intro k
    have h1 : ψ k = (rot ψ ^ k.val) (ψ 0) := by
      rw [rot_pow]; simp
    rw [h1, ← hm, ← pow_mul, rot_pow]
    simp [c]
  have hx : ∀ x, φ.symm x = c + m * ψ.symm x := fun x => by
    simpa using hk (ψ.symm x)
  obtain ⟨k, hk1⟩ := φ.symm.surjective.comp ψ.surjective (c + 1)
  have hmk : (m : ZMod n) * k = 1 := by
    have := hk k; simp only [Function.comp_apply] at hk1; rw [hk1] at this
    linear_combination -this
  let u : (ZMod n)ˣ := ⟨m, k, hmk, by rw [mul_comm]; exact hmk⟩
  refine ⟨u, ?_⟩
  funext a b
  apply propext
  simp only [cyc, hx]
  rw [show c + m * ψ.symm b - (c + m * ψ.symm a) = m * (ψ.symm b - ψ.symm a) by ring]
  have := pm_mul_cancel (a := ψ.symm b - ψ.symm a) (b := 1) u
  simp only [mul_one] at this
  exact this.symm


theorem rot_reindex_pow (φ : ZMod n ≃ E) (ν : (ZMod n)ˣ) (k : ℕ) (x : E) :
    (rot (reindex φ ν) ^ k) x = φ (φ.symm x + ν * k) := by
  rw [rot_pow]
  simp only [reindex, Units.mulLeft, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, mul_add, ← mul_assoc,
    Units.mul_inv, one_mul]

/-- Conversely, the twists of a polygon structure have its group of rotations:
the polygon structures with a given rotation group form one orbit. -/
theorem zpowers_rot_reindex [NeZero n] (φ : ZMod n ≃ E) (ν : (ZMod n)ˣ) :
    Subgroup.zpowers (rot (reindex φ ν)) = Subgroup.zpowers (rot φ) := by
  have h1 : rot (reindex φ ν) = rot φ ^ (ν : ZMod n).val := by
    ext x
    rw [rot_pow, ← pow_one (rot (reindex φ ν)), rot_reindex_pow]
    simp
  have h2 : rot φ = rot (reindex φ ν) ^ ((ν⁻¹ : (ZMod n)ˣ) : ZMod n).val := by
    ext x
    rw [rot_reindex_pow, ← pow_one (rot φ), rot_pow]
    simp
  apply le_antisymm
  · rw [Subgroup.zpowers_le, h1]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le, h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end StarPolygon

/-! ### To 6, in the abstract (pages 138 to 140) -/

section ToSix

variable {n : ℕ} {S : Type*} (A : S → S → Prop)

/-- The star `Et(s)` of a vertex: its neighbours. -/
def star (s : S) : Set S := {t | A s t}

/-- The graph `B` induced on the star of `s` for `A`. -/
def onStar (B : S → S → Prop) (s : S) : star A s → star A s → Prop := fun a b => B a b

/-- `A_λ`: `u` and `t` are joined when `λ⁻¹ u` and `t` are joined in `A`. The
star of `λ s` for `A_λ` is, as a set, the star of `s` for `A`. -/
def twistGraph (l : Equiv.Perm S) : S → S → Prop := fun u t => A (l⁻¹ u) t

theorem star_twistGraph (l : Equiv.Perm S) (s : S) : star (twistGraph A l) (l s) = star A s := by
  ext t; simp [star, twistGraph]

/-- **To 6.** `A` induces a polygon on every star, and `A_λ` induces on every
star `Et(s) = Et_{A_λ}(λ s)` the `ν`-th star polygon of it. -/
def ToSix (hpol : ∀ s, IsPolygon n (onStar A A s)) (l : Equiv.Perm S) (ν : (ZMod n)ˣ) : Prop :=
  ∀ s, onStar A (twistGraph A l) s = (twist ν (⟨_, hpol s⟩ : Pol n _)).1

variable {A}

/-- Under To 6, `ν` is determined by `λ` up to sign. -/
theorem toSix_unique (hn : 2 < n) {hpol : ∀ s, IsPolygon n (onStar A A s)} [Nonempty S]
    {l : Equiv.Perm S} {ν ν' : (ZMod n)ˣ} (h : ToSix A hpol l ν) (h' : ToSix A hpol l ν') :
    ν' = ν ∨ ν' = -ν := by
  obtain ⟨s⟩ := ‹Nonempty S›
  exact (twist_eq_twist_iff hn ν ν' _).1 (Subtype.ext ((h' s).symm.trans (h s)))

/-- Under To 6, `A_λ` is determined by `ν` (`A_λ = A₀^{(ν)}`), as soon as each of
its edges lies in a triangle. -/
theorem twistGraph_eq_of_toSix (hn : 2 < n) {hpol : ∀ s, IsPolygon n (onStar A A s)}
    {l l' : Equiv.Perm S} {ν ν' : (ZMod n)ˣ} (h : ToSix A hpol l ν) (h' : ToSix A hpol l' ν')
    (hν : ν' = ν ∨ ν' = -ν)
    (hl : ∀ u t, twistGraph A l u t → ∃ w, twistGraph A l w u ∧ twistGraph A l w t)
    (hl' : ∀ u t, twistGraph A l' u t → ∃ w, twistGraph A l' w u ∧ twistGraph A l' w t) :
    twistGraph A l = twistGraph A l' := by
  have tw : ∀ s, twist ν' ⟨_, hpol s⟩ = twist ν ⟨_, hpol s⟩ := fun s =>
    (twist_eq_twist_iff hn ν ν' _).2 hν
  funext u t
  apply propext
  constructor
  · intro e
    obtain ⟨w, hu, ht⟩ := hl u t e
    have := congrFun (congrFun (h (l⁻¹ w)) ⟨u, hu⟩) ⟨t, ht⟩
    have h2 := congrFun (congrFun (h' (l⁻¹ w)) ⟨u, hu⟩) ⟨t, ht⟩
    rw [tw] at h2
    exact (h2.trans this.symm).mpr e
  · intro e
    obtain ⟨w, hu, ht⟩ := hl' u t e
    have := congrFun (congrFun (h (l'⁻¹ w)) ⟨u, hu⟩) ⟨t, ht⟩
    have h2 := congrFun (congrFun (h' (l'⁻¹ w)) ⟨u, hu⟩) ⟨t, ht⟩
    rw [tw] at h2
    exact (this.trans h2.symm).mpr e

/-- **Pages 139 and 140: `Z ↪ Z'_n`, except for the octahedron.** If no two
vertices have the same star (the octahedron excepted, page 275) and the twisted
graphs are triangulated, two homotheties with the same `ν ∈ Z'_n` are equal. -/
theorem eq_of_toSix (hn : 2 < n) {hpol : ∀ s, IsPolygon n (onStar A A s)}
    (hstar : ∀ s s', star A s = star A s' → s = s')
    {l l' : Equiv.Perm S} {ν ν' : (ZMod n)ˣ} (h : ToSix A hpol l ν) (h' : ToSix A hpol l' ν')
    (hν : ν' = ν ∨ ν' = -ν)
    (hl : ∀ u t, twistGraph A l u t → ∃ w, twistGraph A l w u ∧ twistGraph A l w t)
    (hl' : ∀ u t, twistGraph A l' u t → ∃ w, twistGraph A l' w u ∧ twistGraph A l' w t) :
    l = l' :=
  have e := twistGraph_eq_of_toSix hn h h' hν hl hl'
  inv_injective (Equiv.ext fun u => hstar _ _ (Set.ext fun t => by
    simpa [star, twistGraph] using congrFun (congrFun e u) t))


/-- An automorphism `g` of `A` carries the star of `s` onto the star of `g s`. -/
def starEquiv {g : Equiv.Perm S} (hg : ∀ a b, A (g a) (g b) ↔ A a b) (s : S) :
    star A s ≃ star A (g s) :=
  Equiv.subtypeEquiv g (fun a => by simp [star, hg])

theorem onStar_starEquiv {g : Equiv.Perm S} (hg : ∀ a b, A (g a) (g b) ↔ A a b) (s : S)
    {B : S → S → Prop} (hB : ∀ a b, B (g a) (g b) ↔ B a b) (a b : star A (g s)) :
    onStar A B (g s) a b ↔ onStar A B s ((starEquiv hg s).symm a) ((starEquiv hg s).symm b) := by
  obtain ⟨a, rfl⟩ := (starEquiv hg s).surjective a
  obtain ⟨b, rfl⟩ := (starEquiv hg s).surjective b
  simp only [Equiv.symm_apply_apply]
  exact hB a b

/-- **Pages 184 to 187, (29): `ν` does not depend on the vertex.** If an
automorphism `g` of `A` commutes with `λ`, the star twist `ν` that `A_λ`
induces at `s` is the one it induces at `g s`. -/
theorem toSix_at_smul (hn : 2 < n) (hpol : ∀ s, IsPolygon n (onStar A A s))
    {l g : Equiv.Perm S} (hg : ∀ a b, A (g a) (g b) ↔ A a b) (hgl : g * l = l * g)
    {ν : (ZMod n)ˣ} {s : S} (h : onStar A (twistGraph A l) s = (twist ν (⟨_, hpol s⟩ : Pol n _)).1) :
    onStar A (twistGraph A l) (g s) = (twist ν (⟨_, hpol (g s)⟩ : Pol n _)).1 := by
  obtain ⟨φ, hφ⟩ := hpol s
  have hA : onStar A A (g s) = cyc (φ.trans (starEquiv hg s)) 1 := by
    funext a b
    apply propext
    rw [onStar_starEquiv hg s hg, hφ]
    rfl
  have hgl' : ∀ u, l⁻¹ (g u) = g (l⁻¹ u) := fun u => by
    have : l⁻¹ * g = g * l⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hgl, mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg (· u) (congrArg DFunLike.coe this)
  have hB : ∀ a b, twistGraph A l (g a) (g b) ↔ twistGraph A l a b := fun a b => by
    simp only [twistGraph, hgl', hg]
  refine Eq.trans ?_ (twist_of_eq hn ν (P := (⟨_, hpol (g s)⟩ : Pol n _)) hA).symm
  replace h := h.trans (twist_of_eq hn ν hφ)
  funext a b
  apply propext
  rw [onStar_starEquiv hg s hB, h]
  rfl

/-- Hence, if the automorphisms of `A` commuting with `λ` are transitive on the
vertices, To 6 at one vertex gives To 6 everywhere, with the same `ν`. -/
theorem toSix_of_transitive (hn : 2 < n) (hpol : ∀ s, IsPolygon n (onStar A A s))
    {l : Equiv.Perm S}
    (htr : ∀ s s' : S, ∃ g : Equiv.Perm S, (∀ a b, A (g a) (g b) ↔ A a b) ∧ g * l = l * g ∧
      g s = s')
    {ν : (ZMod n)ˣ} {s : S} (h : onStar A (twistGraph A l) s = (twist ν (⟨_, hpol s⟩ : Pol n _)).1) :
    ToSix A hpol l ν := fun s' => by
  obtain ⟨g, hg, hgl, rfl⟩ := htr s s'
  exact toSix_at_smul hn hpol hg hgl h

end ToSix

/-! ### To 6 in the model `P_{M, ±e}` over `Z/n` (pages 136 to 140) -/

section ModelToSix

variable {n : ℕ}

theorem scal_scal {R : Type*} [CommRing R] (c c' : Rˣ) (v : Vtx R) :
    scal c (scal c' v) = scal (c * c') v := by
  induction v using Vtx.ind with
  | H x y h => rw [scal_vtx, scal_vtx, scal_vtx, vtx_eq_iff]; left; rw [smul_smul]; simp

/-- The homothety `T_μ` of `S_M`, as a permutation. -/
def scalPerm {R : Type*} [CommRing R] (μ : Rˣ) : Equiv.Perm (Vtx R) where
  toFun := scal μ
  invFun := scal μ⁻¹
  left_inv v := by simp [scal_scal, scal_one]
  right_inv v := by simp [scal_scal, scal_one]

/-- `A_{T_μ}` of `P_{M, ±e}` is `P_{M, ±μe}`. -/
theorem twistGraph_scal {R : Type*} [CommRing R] (e μ : Rˣ) :
    twistGraph (Adj R e) (scalPerm μ) = Adj R (μ * e) := by
  funext u t
  apply propext
  induction u using Vtx.ind with
  | H x y h =>
  induction t using Vtx.ind with
  | H z w h' =>
    change Adj R e (scal μ⁻¹ (vtx h)) (vtx h') ↔ _
    rw [scal_vtx, adj_vtx, adj_vtx, det2_smul_left]
    have := pm_mul_cancel (a := det2 x z) (b := (μ : R) * e) μ⁻¹
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this

variable (hn : 2 < n) (e : (ZMod n)ˣ) {x y₀ : Fin 2 → ZMod n} (hx : det2 x y₀ = 1)

include hx in
theorem det2_starPt (k : ZMod n) :
    det2 ((e : ZMod n) • y₀ + k • x) (-(↑e⁻¹ : ZMod n) • x) = 1 := by
  simp only [det2_add_left, det2_smul_left, det2_smul_right, det2_self,
    det2_swap x y₀, hx]
  simp

/-- The point `(y + k x)˙` of the star of `ẋ` in `P_{M, ±e}`, `y = e y₀`. -/
def starPt (k : ZMod n) : star (Adj (ZMod n) e) (vtx hx) :=
  ⟨vtx (det2_starPt e hx k), by
    change det2 x _ = _ ∨ _
    left
    simp [det2_add_right, det2_smul_right, det2_self, hx]⟩

include hn in
theorem starPt_bijective : Function.Bijective (starPt e hx) := by
  constructor
  · intro k k' h
    have h := congrArg Subtype.val h
    simp only [starPt, vtx_eq_iff] at h
    rcases h with h | h
    · have := congrArg (det2 · y₀) h
      simp only [det2_add_left, det2_smul_left, det2_self, hx] at this
      simpa using this
    · have := congrArg (det2 x ·) h
      simp only [det2_add_right, det2_smul_right, det2_neg_right, det2_self, hx] at this
      have h2 : (2 : ZMod n) * e = 0 := by linear_combination this
      exact absurd (by simpa using congrArg (· * (↑e⁻¹ : ZMod n)) h2) (two_ne_zero_of_lt hn)
  · rintro ⟨v, hv⟩
    induction v using Vtx.ind with
    | H z w h =>
    have hy : det2 x ((e : ZMod n) • y₀) = e := by rw [det2_smul_right, hx, mul_one]
    rcases hv with hv | hv
    · refine ⟨det2 z ((↑e⁻¹ : ZMod n) • ((e : ZMod n) • y₀)), Subtype.ext ?_⟩
      simp only [starPt, vtx_eq_iff]
      left; exact (star_line e hy hv).symm
    · have hv' : det2 x (-z) = e := by rw [det2_neg_right, hv, neg_neg]
      refine ⟨det2 (-z) ((↑e⁻¹ : ZMod n) • ((e : ZMod n) • y₀)), Subtype.ext ?_⟩
      simp only [starPt, vtx_eq_iff]
      right; exact (star_line e hy hv').symm

/-- The star of `ẋ`, indexed by `Z/n`: `k ↦ (y + k x)˙`. -/
noncomputable def starIndex : ZMod n ≃ star (Adj (ZMod n) e) (vtx hx) :=
  Equiv.ofBijective _ (starPt_bijective hn e hx)

include hn in
/-- On the star of `ẋ`, the edges of type `± μ e` form the `μ`-th star polygon
of the indexing: `(y + k x)˙ ~ (y + k' x)˙` iff `k' - k = ± μ`. -/
theorem onStar_adj (μ : (ZMod n)ˣ) :
    onStar (Adj (ZMod n) e) (Adj (ZMod n) (μ * e)) (vtx hx) = cyc (starIndex hn e hx) μ := by
  funext a b
  obtain ⟨k, rfl⟩ := (starIndex hn e hx).surjective a
  obtain ⟨k', rfl⟩ := (starIndex hn e hx).surjective b
  apply propext
  have hy : det2 x ((e : ZMod n) • y₀) = e := by rw [det2_smul_right, hx, mul_one]
  simp only [cyc, Equiv.symm_apply_apply]
  change Adj (ZMod n) _ (vtx (det2_starPt e hx k)) (vtx (det2_starPt e hx k')) ↔ _
  rw [adj_vtx, link_polygon e μ hy]
  constructor <;> rintro (h | h) <;>
    first | (right; linear_combination -h) | (left; linear_combination -h)

include hn in
/-- Every star of `P_{M, ±e}` over `Z/n` is a polygon. -/
theorem isPolygon_adj (v : Vtx (ZMod n)) :
    IsPolygon n (onStar (Adj (ZMod n) e) (Adj (ZMod n) e) v) := by
  induction v using Vtx.ind with
  | H x y h =>
    exact ⟨starIndex hn e h, by simpa using onStar_adj hn e h 1⟩

/-- **To 6 holds in the model, with `ν = μ` (pages 138 and 139).** Over `Z/n`,
`n ≥ 3`, the homothety `T_μ` of `P_{M, ±e}` satisfies To 6 with `ν = μ`: on each
star, `A_{T_μ}` induces the `μ`-th star polygon of the polygon induced by
`P_{M, ±e}`. So `T_μ ↦ μ` is the map `Z → Z'_n` of page 139. -/
theorem toSix_scal (μ : (ZMod n)ˣ) :
    ToSix (Adj (ZMod n) e) (isPolygon_adj hn e) (scalPerm μ) μ := by
  intro v
  induction v using Vtx.ind with
  | H x y h =>
    rw [twistGraph_scal]
    exact (onStar_adj hn e h μ).trans (twist_of_eq hn μ (by simpa using onStar_adj hn e h 1)).symm

end ModelToSix

end Grothendieck.Folder79

/-! ## The double cone (page 275) and homotheties at distance three (pages 187 and 188)

A *regular triangulated 2-polyhedron* is taken here in the weakest form the
argument uses: a symmetric relation `A` on `S` (the edges), connected, whose
stars all carry a polygon of the same order `n ≥ 3` (`IsPolygon n (onStar A A s)`,
the condition (A2) of the reading, with all vertex orders equal). Every edge then lies
in exactly two triangles, so this contains the triangulated 2-polyhedra of the
folder whose vertices all have order `n`, in particular the regular ones. -/

namespace Grothendieck.Folder79

section DoubleCone

variable {n : ℕ} {S : Type*} {A : S → S → Prop}

/-- In the cycle `k ~ k ± 1` of `Z/n`, `n ≥ 3`, two distinct indices with the
same neighbours are opposite (`j = i + 2`), and then `4 = 0`. -/
theorem cyc_same_nbrs (hn : 2 < n) {i j : ZMod n} (hij : i ≠ j)
    (h : ∀ k : ZMod n, (k - i = 1 ∨ k - i = -1) ↔ (k - j = 1 ∨ k - j = -1)) :
    j = i + 2 ∧ (4 : ZMod n) = 0 := by
  have hj : j = i + 2 := by
    rcases (h (i + 1)).1 (Or.inl (by ring)) with h1 | h1
    · exact absurd (by linear_combination h1) hij
    · linear_combination -h1
  refine ⟨hj, ?_⟩
  subst hj
  rcases (h (i - 1)).1 (Or.inr (by ring)) with h2 | h2
  · linear_combination -h2
  · exact absurd (by linear_combination -h2) (two_ne_zero_of_lt hn)

theorem eq_four_of_four_eq_zero (hn : 2 < n) (h : (4 : ZMod n) = 0) : n = 4 := by
  have h4 := (ZMod.natCast_eq_zero_iff 4 n).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) h4
  interval_cases n <;> omega

/-- Adjacency inside a star, read on a polygon indexing of it. -/
theorem adj_iff_of_pol {s : S} {φ : ZMod n ≃ star A s} (hφ : onStar A A s = cyc φ 1)
    (a b : ZMod n) : A (φ a) (φ b) ↔ (b - a = 1 ∨ b - a = -1) := by
  change onStar A A s (φ a) (φ b) ↔ _
  rw [hφ]; simp [cyc]

/-- No loops: a vertex is not in its own star, since a polygon has none. -/
theorem not_adj_self (hn : 2 < n) (hpol : ∀ s, IsPolygon n (onStar A A s)) (s : S) :
    ¬ A s s := by
  intro h
  obtain ⟨φ, hφ⟩ := hpol s
  have h1 : (1 : ZMod n) ≠ 0 := fun h1 => two_ne_zero_of_lt hn (by
    rw [show (2 : ZMod n) = 1 + 1 by norm_num, h1, add_zero])
  have := (adj_iff_of_pol hφ (φ.symm ⟨s, h⟩) (φ.symm ⟨s, h⟩)).1 (by simpa using h)
  rw [sub_self] at this
  rcases this with h0 | h0
  · exact h1 h0.symm
  · exact h1 (neg_eq_zero.1 h0.symm)

/-- **Page 275, the double cone.** In a connected triangulated 2-polyhedron
whose vertices all have the same order `n ≥ 3`, two distinct vertices `s ≠ s'`
with the same star force `n = 4` and the octahedron: the graph is isomorphic to
`K_{2,2,2}`, the vertices `Fin 3 × Bool` joined when their first coordinates
differ, the pairs `{(i, false), (i, true)}` being the opposite vertices. -/
theorem double_cone (hA : ∀ a b, A a b → A b a) (hn : 2 < n)
    (hpol : ∀ s, IsPolygon n (onStar A A s)) (hconn : ∀ a b, Relation.ReflTransGen A a b)
    {s s' : S} (hss : s ≠ s') (hst : star A s = star A s') :
    n = 4 ∧ ∃ e : S ≃ Fin 3 × Bool, ∀ a b, A a b ↔ (e a).1 ≠ (e b).1 := by
  have mem : ∀ w, A s w ↔ A s' w := fun w => by
    change w ∈ star A s ↔ w ∈ star A s'; rw [hst]
  have nss := not_adj_self hn hpol s
  have ns's' := not_adj_self hn hpol s'
  -- at a vertex `u` of the common star, `s` and `s'` are opposite in the star of `u`
  have key : ∀ u, A s u → ∃ φ : ZMod n ≃ star A u, onStar A A u = cyc φ 1 ∧
      ∃ i : ZMod n, (φ i : S) = s ∧ (φ (i + 2) : S) = s' ∧ (4 : ZMod n) = 0 := by
    intro u hu
    obtain ⟨φ, hφ⟩ := hpol u
    have hsu : A u s := hA _ _ hu
    have hs'u : A u s' := hA _ _ ((mem u).1 hu)
    set i := φ.symm ⟨s, hsu⟩
    set j := φ.symm ⟨s', hs'u⟩
    have hi : (φ i : S) = s := by simp [i]
    have hj : (φ j : S) = s' := by simp [j]
    have hij : i ≠ j := fun e => hss (by rw [← hi, ← hj, e])
    have := cyc_same_nbrs hn hij (fun k => by
      rw [← adj_iff_of_pol hφ, ← adj_iff_of_pol hφ, hi, hj, mem])
    refine ⟨φ, hφ, i, hi, ?_, this.2⟩
    rw [← this.1, hj]
  obtain ⟨φ, hφ⟩ := hpol s
  obtain ⟨-, -, -, -, -, h4⟩ := key _ (φ 0).2
  have hn4 := eq_four_of_four_eq_zero hn h4
  subst hn4
  -- the star of a vertex of the star is `{s, s'}` and two vertices of the star
  have close : ∀ u, A s u → ∀ w, A u w → w = s ∨ w = s' ∨ A s w := by
    intro u hu w hw
    obtain ⟨ψ, hψ, i, hi, hi2, -⟩ := key u hu
    set k := ψ.symm ⟨w, hw⟩
    have hk : (ψ k : S) = w := by simp [k]
    have hd : ∀ d : ZMod 4, d = 0 ∨ d = 2 ∨ d = 1 ∨ d = -1 := by decide
    rcases hd (k - i) with hd | hd | hd | hd
    · left; rw [← hk, ← hi, sub_eq_zero.1 hd]
    · right; left; rw [← hk, ← hi2, ← hd]; ring_nf
    all_goals
      right; right
      rw [← hk, ← hi]
      exact (adj_iff_of_pol hψ _ _).2 (by tauto)
  have all : ∀ w, w = s ∨ w = s' ∨ A s w := by
    intro w
    induction hconn s w with
    | refl => exact Or.inl rfl
    | tail _ hab ih =>
      rename_i a b _
      rcases ih with rfl | rfl | ha
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inr ((mem _).2 hab))
      · exact close a ha b hab
  -- the isomorphism with `K_{2,2,2}`
  let idx : Fin 3 × Bool → ZMod 4 := fun p => ((p.1 : ℕ) + 3 + 2 * (if p.2 then 1 else 0) : ℕ)
  have adjIdx : ∀ a b : Fin 3 × Bool, a.1 ≠ 0 → b.1 ≠ 0 →
      ((idx b - idx a = 1 ∨ idx b - idx a = -1) ↔ a.1 ≠ b.1) := by decide
  have injIdx : ∀ a b : Fin 3 × Bool, a.1 ≠ 0 → b.1 ≠ 0 → idx a = idx b → a = b := by decide
  have surjIdx : ∀ k : ZMod 4, ∃ p : Fin 3 × Bool, p.1 ≠ 0 ∧ idx p = k := by decide
  let g : Fin 3 × Bool → S := fun p =>
    if p.1 = 0 then (if p.2 then s' else s) else (φ (idx p) : S)
  have hE : ∀ k, A s (φ k) := fun k => (φ k).2
  have hE' : ∀ k, A s' (φ k) := fun k => (mem _).1 (φ k).2
  have nss' : ¬ A s s' := fun h => ns's' ((mem _).1 h)
  have ns's : ¬ A s' s := fun h => nss' (hA _ _ h)
  have adj : ∀ a b, A (g a) (g b) ↔ a.1 ≠ b.1 := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    by_cases ha : a1 = 0 <;> by_cases hb : b1 = 0
    · subst ha; subst hb
      cases a2 <;> cases b2 <;> simp [g, nss, ns's', nss', ns's]
    · subst ha
      cases a2 <;> simp [g, hb, Ne.symm hb, hE, hE']
    · subst hb
      cases b2 <;> simp [g, ha, hE, hE', fun h => hA _ _ h]
    · simp only [g, ha, hb, ite_false]
      exact (adj_iff_of_pol hφ _ _).trans (adjIdx (a1, a2) (b1, b2) ha hb)
  have g0f : g (0, false) = s := by simp [g]
  have g0t : g (0, true) = s' := by simp [g]
  have gE : ∀ p : Fin 3 × Bool, p.1 ≠ 0 → g p = φ (idx p) := fun p hp => by simp [g, hp]
  have notE : ∀ p : Fin 3 × Bool, p.1 ≠ 0 → g p ≠ s ∧ g p ≠ s' := fun p hp => by
    rw [gE p hp]
    refine ⟨fun h => nss ?_, fun h => ns's' ?_⟩
    · have := hE (idx p); rwa [h] at this
    · have := hE' (idx p); rwa [h] at this
  have inj : Function.Injective g := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    by_cases ha : a1 = 0 <;> by_cases hb : b1 = 0
    · subst ha; subst hb
      cases a2 <;> cases b2 <;> first | rfl | (rw [g0f, g0t] at h; exact (hss h).elim) |
        (rw [g0t, g0f] at h; exact (hss h.symm).elim)
    · subst ha
      cases a2
      · exact ((notE _ hb).1 (h.symm.trans g0f)).elim
      · exact ((notE _ hb).2 (h.symm.trans g0t)).elim
    · subst hb
      cases b2
      · exact ((notE _ ha).1 (h.trans g0f)).elim
      · exact ((notE _ ha).2 (h.trans g0t)).elim
    · rw [gE _ ha, gE _ hb] at h
      exact injIdx _ _ ha hb (φ.injective (Subtype.ext h))
  have surj : Function.Surjective g := by
    intro w
    rcases all w with rfl | rfl | hw
    · exact ⟨(0, false), by simp [g]⟩
    · exact ⟨(0, true), by simp [g]⟩
    · obtain ⟨p, hp, hpk⟩ := surjIdx (φ.symm ⟨w, hw⟩)
      exact ⟨p, by simp [g, hp, hpk]⟩
  let e := Equiv.ofBijective g ⟨inj, surj⟩
  refine ⟨rfl, e.symm, fun a b => ?_⟩
  rw [← adj, show g (e.symm a) = a from e.apply_symm_apply a,
    show g (e.symm b) = b from e.apply_symm_apply b]

end DoubleCone


section HomothetyOctahedron

variable {n : ℕ} {H : Type*} [Group H] {U₀ : Subgroup H} {σ : H} {l : Equiv.Perm (H ⧸ U₀)}

/-- `H` carries stars to stars: `g • t` is a neighbour of `g • a` iff `t` is one of `a`. -/
theorem isArc_smul_iff (g : H) (a t : H ⧸ U₀) :
    IsArc (U₀ := U₀) (σ := σ) (g • a) (g • t) ↔ IsArc (U₀ := U₀) (σ := σ) a t := by
  refine ⟨fun h => ?_, fun h => h.smul g⟩
  simpa using h.smul g⁻¹

/-- **Pages 187 and 188, (32) a″), with the double cone of page 275.** Let the
coset graph `H/U₀` (`σ² ∈ U₀`) be connected, with every star a polygon of order
`n ≥ 3`: a regular triangulated 2-polyhedron, `H` being transitive on its arcs.
If an `H`-equivariant permutation `λ ≠ 1` moves some vertex `x` to distance at
most `2` (`λ x = x`, or `λ x` a neighbour of `x`, or a common neighbour), then
`n = 4`, the polyhedron is the octahedron, and `λ` is its antipody: for every
vertex `y`, `λ y ≠ y` has the star of `y`. -/
theorem homothety_dist_le_two (hσ : σ * σ ∈ U₀) (hl : ∀ (h : H) x, l (h • x) = h • l x)
    (hl1 : l ≠ 1) (hn : 2 < n)
    (hpol : ∀ s, IsPolygon n (onStar (IsArc (U₀ := U₀) (σ := σ)) (IsArc (U₀ := U₀) (σ := σ)) s))
    (hconn : ∀ a b, Relation.ReflTransGen (IsArc (U₀ := U₀) (σ := σ)) a b) {x : H ⧸ U₀}
    (hx : l x = x ∨ IsArc (U₀ := U₀) (σ := σ) x (l x) ∨
      ∃ t, IsArc (U₀ := U₀) (σ := σ) x t ∧ IsArc (U₀ := U₀) (σ := σ) t (l x)) :
    n = 4 ∧ (∃ e : H ⧸ U₀ ≃ Fin 3 × Bool, ∀ a b, IsArc (U₀ := U₀) (σ := σ) a b ↔ (e a).1 ≠ (e b).1) ∧
      ∀ y, l y ≠ y ∧ star (IsArc (U₀ := U₀) (σ := σ)) (l y) = star (IsArc (U₀ := U₀) (σ := σ)) y := by
  have fixed : ∀ y, l y ≠ y := fun y e => hl1 (homothety_fixed hl e)
  -- the star of `x` has two distinct vertices, so `λ x` is not a neighbour of `x`
  have hadj : ¬ IsArc (U₀ := U₀) (σ := σ) x (l x) := by
    intro h
    obtain ⟨φ, -⟩ := hpol x
    have h01 : (0 : ZMod n) ≠ 1 := fun h01 => two_ne_zero_of_lt hn (by
      rw [show (2 : ZMod n) = 1 + 1 by norm_num, ← h01, add_zero])
    have e0 := homothety_adj hl h (φ 0).2
    have e1 := homothety_adj hl h (φ 1).2
    exact h01 (φ.injective (Subtype.ext (e0.trans e1.symm)))
  obtain ⟨t, h1, h2⟩ : ∃ t, IsArc (U₀ := U₀) (σ := σ) x t ∧ IsArc (U₀ := U₀) (σ := σ) t (l x) := by
    rcases hx with hx | hx | hx
    · exact (fixed x hx).elim
    · exact (hadj hx).elim
    · exact hx
  have hst : star (IsArc (U₀ := U₀) (σ := σ)) x = star (IsArc (U₀ := U₀) (σ := σ)) (l x) :=
    Set.ext fun t' => homothety_common_nbr hσ hl h1 h2 t'
  obtain ⟨h4, e, he⟩ := double_cone (fun a b h => h.symm hσ) hn hpol hconn
    (fixed x).symm hst
  refine ⟨h4, ⟨e, he⟩, fun y => ⟨fixed y, ?_⟩⟩
  -- transport the equality of stars from `x` to `y = g • x`
  obtain ⟨g, rfl⟩ : ∃ g : H, g • x = y := by
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b => exact ⟨b * a⁻¹, by
          rw [← smul_s₀ a, ← smul_s₀ b, smul_smul, inv_mul_cancel_right]⟩
  ext t'
  change IsArc _ _ ↔ IsArc _ _
  rw [hl, ← smul_inv_smul g t', isArc_smul_iff, isArc_smul_iff]
  exact (Set.ext_iff.1 hst _).symm

/-- **Page 188, (32) a″): distance exactly three.** Same setting, outside the
octahedron (`n ≠ 4`): an `H`-equivariant permutation `λ ≠ 1` moves no vertex
to itself, to a neighbour, or to distance `2`. When `λ x` (or `λ⁻¹ x`, which is
equivariant too) is at distance at most `3` from `x`, the distance is `3`. -/
theorem homothety_dist_three (hσ : σ * σ ∈ U₀) (hl : ∀ (h : H) x, l (h • x) = h • l x)
    (hl1 : l ≠ 1) (hn : 2 < n) (h4 : n ≠ 4)
    (hpol : ∀ s, IsPolygon n (onStar (IsArc (U₀ := U₀) (σ := σ)) (IsArc (U₀ := U₀) (σ := σ)) s))
    (hconn : ∀ a b, Relation.ReflTransGen (IsArc (U₀ := U₀) (σ := σ)) a b) (x : H ⧸ U₀) :
    l x ≠ x ∧ ¬ IsArc (U₀ := U₀) (σ := σ) x (l x) ∧
      ¬ ∃ t, IsArc (U₀ := U₀) (σ := σ) x t ∧ IsArc (U₀ := U₀) (σ := σ) t (l x) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    exact h4 (homothety_dist_le_two hσ hl hl1 hn hpol hconn (by tauto)).1

end HomothetyOctahedron

end Grothendieck.Folder79


/-! ## `Z ↪ Z'_n` except for the octahedron (pages 139 and 140, with page 275)

The hypothesis « no two vertices share a star » of `eq_of_toSix` is replaced by
the double cone: in a connected regular triangulated 2-polyhedron of order
`n ≠ 4` it holds, and for `n = 4` the polyhedron is the octahedron. The
exception is real: over `Z/4`, the antipody `σ` and the identity both satisfy
To 6 with `ν = 1`. -/

namespace Grothendieck.Folder79

section ToSixOctahedron

variable {n : ℕ} {S : Type*} {A : S → S → Prop}

/-- In a symmetric graph whose stars are polygons, every edge lies in a triangle. -/
theorem triangulated_of_pol (hA : ∀ a b, A a b → A b a)
    (hpol : ∀ s, IsPolygon n (onStar A A s)) {u t : S} (h : A u t) :
    ∃ w, A w u ∧ A w t := by
  obtain ⟨φ, hφ⟩ := hpol u
  obtain ⟨k, hk⟩ := φ.surjective ⟨t, h⟩
  refine ⟨φ (k + 1), hA _ _ (φ _).2, hA _ _ ?_⟩
  have := (adj_iff_of_pol hφ k (k + 1)).2 (Or.inl (by ring))
  simpa [hk] using this

/-- A permutation preserving every star leaves `A` untwisted: `A_λ = A`. -/
theorem twistGraph_eq_self {l : Equiv.Perm S} (hl : ∀ u, star A (l u) = star A u) :
    twistGraph A l = A := by
  funext u t
  apply propext
  have h := Set.ext_iff.1 (hl (l⁻¹ u)) t
  rw [show l (l⁻¹ u) = u by simp] at h
  exact h.symm

/-- Such a permutation satisfies To 6 with `ν = 1`. -/
theorem toSix_one_of_star_eq (hn : 2 < n) (hpol : ∀ s, IsPolygon n (onStar A A s))
    {l : Equiv.Perm S} (hl : ∀ u, star A (l u) = star A u) : ToSix A hpol l 1 := by
  intro s
  rw [twistGraph_eq_self hl]
  exact (congrArg Subtype.val (twist_one hn ⟨_, hpol s⟩)).symm

/-- **Pages 139 and 140: `Z ↪ Z'_n`, the octahedron excepted.** In a connected
symmetric graph whose stars are polygons of order `n ≥ 3`, `n ≠ 4`, two
permutations satisfying To 6 with the same `ν ∈ Z'_n`, and whose twisted graphs
are triangulated, are equal. -/
theorem eq_of_toSix_of_ne_four (hA : ∀ a b, A a b → A b a) (hn : 2 < n) (h4 : n ≠ 4)
    {hpol : ∀ s, IsPolygon n (onStar A A s)} (hconn : ∀ a b, Relation.ReflTransGen A a b)
    {l l' : Equiv.Perm S} {ν ν' : (ZMod n)ˣ} (h : ToSix A hpol l ν) (h' : ToSix A hpol l' ν')
    (hν : ν' = ν ∨ ν' = -ν)
    (hl : ∀ u t, twistGraph A l u t → ∃ w, twistGraph A l w u ∧ twistGraph A l w t)
    (hl' : ∀ u t, twistGraph A l' u t → ∃ w, twistGraph A l' w u ∧ twistGraph A l' w t) :
    l = l' :=
  eq_of_toSix hn (fun _ _ hst => by_contra fun hss =>
    h4 (double_cone hA hn hpol hconn hss hst).1) h h' hν hl hl'

/-- The same without `n ≠ 4`: two such permutations are equal, or the graph is
the octahedron `K_{2,2,2}`. -/
theorem eq_of_toSix_or_octahedron (hA : ∀ a b, A a b → A b a) (hn : 2 < n)
    {hpol : ∀ s, IsPolygon n (onStar A A s)} (hconn : ∀ a b, Relation.ReflTransGen A a b)
    {l l' : Equiv.Perm S} {ν ν' : (ZMod n)ˣ} (h : ToSix A hpol l ν) (h' : ToSix A hpol l' ν')
    (hν : ν' = ν ∨ ν' = -ν)
    (hl : ∀ u t, twistGraph A l u t → ∃ w, twistGraph A l w u ∧ twistGraph A l w t)
    (hl' : ∀ u t, twistGraph A l' u t → ∃ w, twistGraph A l' w u ∧ twistGraph A l' w t) :
    l = l' ∨ (n = 4 ∧ ∃ e : S ≃ Fin 3 × Bool, ∀ a b, A a b ↔ (e a).1 ≠ (e b).1) := by
  by_cases hstar : ∀ s s', star A s = star A s' → s = s'
  · exact Or.inl (eq_of_toSix hn hstar h h' hν hl hl')
  · push Not at hstar
    obtain ⟨s, s', hst, hss⟩ := hstar
    exact Or.inr (double_cone hA hn hpol hconn hss hst)

end ToSixOctahedron

section OctahedronModel

variable {R : Type*} [CommRing R]

theorem adj_symm_model (e : R) {v t : Vtx R} (h : Adj R e v t) : Adj R e t v := by
  induction v using Vtx.ind with
  | H x y hxy =>
  induction t using Vtx.ind with
  | H z w hz =>
  rw [adj_vtx] at h ⊢
  rw [det2_swap]
  rcases h with h | h <;> rw [h] <;> simp

theorem adj_sigma_of (hR : Exceptional R) (e : Rˣ) {v t : Vtx R} (h : Adj R e v t) :
    Adj R e (sigma hR v) t := by
  induction v using Vtx.ind with
  | H x y hxy =>
  induction t using Vtx.ind with
  | H z w hz =>
  rw [sigma_vtx, adj_vtx]
  rw [adj_vtx] at h
  have hu : IsUnit (det2 x z) := h.elim (fun h => h ▸ e.isUnit) (fun h => h ▸ e.isUnit.neg)
  rcases (same_star_iff hxy).2 (Or.inr (Or.inr ⟨hR, Or.inl rfl⟩)) z hu with h1 | h1 <;>
    rw [h1] <;> rcases h with h | h <;> rw [h] <;> simp

/-- `σ(ẋ)` has the star of `ẋ` in `P_{M, ±e}`. -/
theorem star_sigma (hR : Exceptional R) (e : Rˣ) (v : Vtx R) :
    star (Adj R e) (sigma hR v) = star (Adj R e) v :=
  Set.ext fun t => ⟨fun h => by
    have := adj_sigma_of hR e h; rwa [sigma_sigma] at this, adj_sigma_of hR e⟩

/-- `σ` as a permutation of `M*/±1`. -/
noncomputable def sigmaPerm (hR : Exceptional R) : Equiv.Perm (Vtx R) where
  toFun := sigma hR
  invFun := sigma hR
  left_inv := sigma_sigma hR
  right_inv := sigma_sigma hR

/-- **The octahedral exception of page 139 is real.** Over `Z/4`, in
`P_{M, ±e}` (the octahedron), the antipody `σ` and the identity both satisfy
To 6 with `ν = 1`, both twisted graphs are triangulated, and `σ ≠ 1`: the map
`λ ↦ ν` is not injective. -/
theorem octahedron_toSix (e : (ZMod 4)ˣ) :
    ToSix (Adj (ZMod 4) e) (isPolygon_adj (by norm_num) e) (sigmaPerm exceptional_zmod_four) 1 ∧
      ToSix (Adj (ZMod 4) e) (isPolygon_adj (by norm_num) e) 1 1 ∧
      (∀ u t, twistGraph (Adj (ZMod 4) e) (sigmaPerm exceptional_zmod_four) u t →
        ∃ w, twistGraph (Adj (ZMod 4) e) (sigmaPerm exceptional_zmod_four) w u ∧
          twistGraph (Adj (ZMod 4) e) (sigmaPerm exceptional_zmod_four) w t) ∧
      (∀ u t, twistGraph (Adj (ZMod 4) e) 1 u t →
        ∃ w, twistGraph (Adj (ZMod 4) e) 1 w u ∧ twistGraph (Adj (ZMod 4) e) 1 w t) ∧
      sigmaPerm exceptional_zmod_four ≠ 1 := by
  have hs := star_sigma exceptional_zmod_four e
  have h1 : ∀ u, star (Adj (ZMod 4) e) ((1 : Equiv.Perm (Vtx (ZMod 4))) u) =
      star (Adj (ZMod 4) e) u := fun _ => rfl
  have tri : ∀ u t, Adj (ZMod 4) e u t → ∃ w, Adj (ZMod 4) e w u ∧ Adj (ZMod 4) e w t :=
    fun _ _ h => triangulated_of_pol (fun _ _ => adj_symm_model (e : ZMod 4))
      (isPolygon_adj (by norm_num) e) h
  refine ⟨toSix_one_of_star_eq (by norm_num) _ (l := sigmaPerm exceptional_zmod_four) hs, toSix_one_of_star_eq (by norm_num) _ h1,
    by rw [twistGraph_eq_self hs]; exact tri, by rw [twistGraph_eq_self h1]; exact tri, ?_⟩
  intro h
  apply sigma_ne_scal exceptional_zmod_four (by decide) 1 (vtx det2_e)
  rw [scal_one]
  exact congrArg (fun p : Equiv.Perm (Vtx (ZMod 4)) => p (vtx det2_e)) h

end OctahedronModel

end Grothendieck.Folder79


/-! ## The antipody of the octahedron is a homothety (pages 188 and 275, abstract form)

For a graph isomorphic to the octahedron `K_{2,2,2}` the antipody (each vertex to
the one other vertex not adjacent to it) is defined from the graph alone, so it
commutes with every automorphism; it has the star of each vertex, hence satisfies
the homothety condition (H1), and it is the only permutation `λ ≠ 1` commuting
with `H` that moves a vertex to distance at most `2`. It does not satisfy the
faithfulness (72), so it lies in no group `IsHomothetyGroup`. -/

namespace Grothendieck.Folder79

section OctahedronAntipody

variable {S : Type*} {A : S → S → Prop} (e : S ≃ Fin 3 × Bool)

/-- The antipody of a graph identified with `K_{2,2,2}` by `e`. -/
def octAnti : Equiv.Perm S :=
  e.symm.permCongr <|
    Function.Involutive.toPerm (fun p : Fin 3 × Bool => (p.1, !p.2)) fun _ => by simp

@[simp] theorem octAnti_apply (y : S) : octAnti e y = e.symm ((e y).1, !(e y).2) := rfl

variable {e} (he : ∀ a b, A a b ↔ (e a).1 ≠ (e b).1)
include he

omit he in
theorem octAnti_ne (y : S) : octAnti e y ≠ y := fun h => by
  simpa using congrArg (·.2) (congrArg e h)

/-- The non-neighbours of `y` are `y` and its antipode. -/
theorem not_adj_iff_octAnti {y z : S} : ¬ A y z ↔ z = y ∨ z = octAnti e y := by
  rw [he, not_not, ← e.apply_eq_iff_eq, octAnti_apply, ← e.apply_eq_iff_eq,
    Equiv.apply_symm_apply]
  rcases e z with ⟨a, b⟩; rcases e y with ⟨c, d⟩
  cases b <;> cases d <;> simp [eq_comm]

theorem star_octAnti (y : S) : star A (octAnti e y) = star A y := by
  ext t; change A _ t ↔ A y t; simp [he]

omit he in
theorem octAnti_symm : (octAnti e)⁻¹ = octAnti e :=
  Equiv.ext fun y => (octAnti e).injective (by simp [Equiv.Perm.inv_def])

/-- Condition (H1): `{s, t}` is an edge iff `{λ s, λ⁻¹ t}` is one. -/
theorem octAnti_homothety (s t : S) : A (octAnti e s) ((octAnti e)⁻¹ t) ↔ A s t := by
  rw [octAnti_symm]; simp [he]

/-- The antipode is at distance `2`. -/
theorem octAnti_common_nbr (y : S) : ¬ A y (octAnti e y) ∧ ∃ t, A y t ∧ A t (octAnti e y) :=
  ⟨(not_adj_iff_octAnti he).2 (Or.inr rfl), e.symm ((e y).1 + 1, true), by simp [he]⟩

/-- The antipody commutes with every injective map preserving the graph. -/
theorem octAnti_comm {g : S → S} (hg : ∀ a b, A (g a) (g b) ↔ A a b)
    (hi : Function.Injective g) (y : S) : octAnti e (g y) = g (octAnti e y) :=
  (((not_adj_iff_octAnti he).1 ((hg _ _).not.2 (octAnti_common_nbr he y).1)).resolve_left
    (hi.ne (octAnti_ne y))).symm

/-- A permutation moving every vertex to another vertex with the same star is the
antipody. -/
theorem eq_octAnti {l : Equiv.Perm S} (hl : ∀ y, l y ≠ y ∧ star A (l y) = star A y) :
    l = octAnti e := by
  have hn : ∀ y, ¬ A y y := by simp [he]
  ext y
  refine ((not_adj_iff_octAnti he).1 fun h => hn (l y) ?_).resolve_left (hl y).1
  change l y ∈ star A (l y); rwa [(hl y).2]

end OctahedronAntipody

section OctahedronHomothety

variable {H : Type*} [Group H] {U₀ : Subgroup H} {σ : H} {e : H ⧸ U₀ ≃ Fin 3 × Bool}

/-- **The octahedral exception of page 188 is a homothety, in the abstract setting.**
Let the coset graph `H/U₀` be the octahedron (`σ² ∈ U₀` is not needed). Its
antipody commutes with `H`, satisfies the homothety condition (70 b), is not the identity, has the
star of each vertex (so `A_λ = A`: it is strict), and moves each vertex to
distance `2`. It fails the faithfulness (72), so it lies in no homothety group
`IsHomothetyGroup`. -/
theorem octAnti_isHomothety
    (he : ∀ a b, IsArc (U₀ := U₀) (σ := σ) a b ↔ (e a).1 ≠ (e b).1) :
    (∀ (h : H) x, octAnti e (h • x) = h • octAnti e x) ∧
      (∀ s t, IsArc (σ := σ) s t → IsArc (σ := σ) (octAnti e s) ((octAnti e)⁻¹ t)) ∧
      octAnti e ≠ 1 ∧ twistGraph (IsArc (σ := σ)) (octAnti e) = IsArc (σ := σ) ∧
      (∀ x, ¬ IsArc (σ := σ) x (octAnti e x) ∧
        ∃ t, IsArc (σ := σ) x t ∧ IsArc (σ := σ) t (octAnti e x)) ∧
      (∃ u : H, u • s₀ U₀ = s₀ U₀ ∧ u • t₀ U₀ σ = octAnti e (t₀ U₀ σ)) ∧
      ∀ Z, IsHomothetyGroup U₀ σ Z → octAnti e ∉ Z := by
  have h72 : ∃ u : H, u • s₀ U₀ = s₀ U₀ ∧
      u • t₀ U₀ σ = octAnti e (t₀ U₀ σ) :=
    IsArc.stab_trans ⟨1, one_smul _ _, one_smul _ _⟩
      ((he _ _).2 (by simpa using (he _ _).1 ⟨1, one_smul _ _, one_smul _ _⟩))
  refine ⟨fun h => octAnti_comm he (isArc_smul_iff h) (MulAction.injective h),
    fun s t => (octAnti_homothety he s t).2,
    fun h => octAnti_ne (e := e) (s₀ U₀) (by rw [h]; rfl),
    twistGraph_eq_self (star_octAnti he), octAnti_common_nbr he, h72, fun Z hZ hm => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := h72
  exact octAnti_ne (e := e) (s₀ U₀) (by rw [hZ.faithful _ hm u hu1 hu2]; rfl)

/-- **Page 188, the exception is the antipody.** In a connected coset graph whose
stars are polygons of order `n ≥ 3`, an `H`-equivariant permutation `λ ≠ 1`
moving some vertex to distance at most `2` is the antipody of the octahedron. -/
theorem homothety_dist_le_two_eq {n : ℕ} {l : Equiv.Perm (H ⧸ U₀)} (hσ : σ * σ ∈ U₀)
    (hl : ∀ (h : H) x, l (h • x) = h • l x) (hl1 : l ≠ 1) (hn : 2 < n)
    (hpol : ∀ s, IsPolygon n
      (onStar (IsArc (U₀ := U₀) (σ := σ)) (IsArc (U₀ := U₀) (σ := σ)) s))
    (hconn : ∀ a b, Relation.ReflTransGen (IsArc (U₀ := U₀) (σ := σ)) a b) {x : H ⧸ U₀}
    (hx : l x = x ∨ IsArc (U₀ := U₀) (σ := σ) x (l x) ∨
      ∃ t, IsArc (U₀ := U₀) (σ := σ) x t ∧ IsArc (U₀ := U₀) (σ := σ) t (l x)) :
    ∃ e : H ⧸ U₀ ≃ Fin 3 × Bool,
      (∀ a b, IsArc (U₀ := U₀) (σ := σ) a b ↔ (e a).1 ≠ (e b).1) ∧ l = octAnti e := by
  obtain ⟨-, ⟨e, he⟩, hy⟩ := homothety_dist_le_two hσ hl hl1 hn hpol hconn hx
  exact ⟨e, he, eq_octAnti he hy⟩

end OctahedronHomothety

end Grothendieck.Folder79
