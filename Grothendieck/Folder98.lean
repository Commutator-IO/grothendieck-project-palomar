module

public import Mathlib
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Multiset.Bind
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Algebra.Group.Action.Sum

@[expose] public section


/-!
# Folder 98: the axioms of a theory of norms in the model of G-sets (pages 10–12), and the
# classes of sheaves over the extensions of the base field (pages 28–30)

The modernised reading `transcripts/98/98.modern.tex` (« Une théorie axiomatique des normes »)
gives, in a category with finite sums, a class `𝒩` of morphisms with (i) identities,
(ii) composition, (iii) base change, (iv) sums, (v) the quotients `(X^n_Y)/H`, `H ⊆ 𝔖_n`; a
degree with (i bis) `deg id = 1`, (ii bis) `deg (vu) = deg v · deg u`, (iii bis) invariance under
base change, (iv bis) additivity, (v bis) `deg ((X^n_Y)/H → Y) = card(E^n/H)` for `deg u = r`,
`E = {1, …, r}`; and canonical sections `Can_{X/Y} : Y → Sym^r_Y(X)` with (i ter)
`Can_{X/X} = id`, (ii ter) the transitivity diagram of page 11, (iii ter) base change,
(iv ter) additivity. Example I: `G`-sets, `u` of degree `r` when all its fibres have `r`
elements, `Can_{X/Y}(y)` the class of the « suite de ses éléments rangés dans un ordre
quelconque »; the page says (i)–(v) and (i bis)–(v bis) are « trivialement vérifiées » and that
« on vérifie aussitôt » (i ter)–(iv ter).

What is formalised, for maps of types (the action of `G` only has to be respected, `can_smul`):

* `hasDeg_id`, `hasDeg_comp`, `hasDeg_pullback`, `hasDeg_sum`, `hasDeg_quotPow` — (i)–(v) and
  (i bis)–(v bis): maps with fibres of constant finite cardinality form a class closed under
  identities, composition, base change, sums and quotients `(X^n_Y)/H`, with the degree rules;
  the fibre of `(X^n_Y)/H` over `y` is in bijection with `E^n/H`.
* `Can`, with `Sym^r_Y(X)` as pairs `(y, m)`, `m` a multiset of `r` points of `u⁻¹(y)`, and
  `can_id`, `can_comp`, `can_pullback`, `can_sum` — (i ter)–(iv ter), (ii ter) being the
  diagram of page 11 with `can : Sym^s_Z(Sym^r_Y X) → Sym^s_Z(Sym^r_Z X) → Sym^{rs}_Z X`.
* `can_smul` — `Can` is compatible with the action of a group `G` when `u` is equivariant.
* `kEquiv_equivalence` — Déf. 1 of page 28: `k`-equivalence of sheaves over extensions of `k`
  is an equivalence relation, in a model where `C` is the category of extensions and `Φ K` the
  classes of sheaves on `X ⊗_k K` with base change.
* `kEquiv_map` — page 29: `𝔉(X/k)` is contravariant in `X`.
* `corollaire5_surj`, `corollaire5_iff` — Cor. 5 of page 30: from Prop. 1 and the two
  properties of `K̃`, `𝔉(X/k)` is the quotient of the classes on `X ⊗_k K̃` by `Aut(K̃/k)`.

Not formalised: Example II (finite locally free morphisms of schemes, with the norm of page 2),
Example III (covering spaces and `Φ(E) = X ×^Γ E`), the transitivity of norms of pages 6–8;
for pages 28–30, Prop. 1 itself and the universality and homogeneity of `K̃`, which are
hypotheses.

**What the formalisation finds.** Example I satisfies all the axioms, including (ii ter), which
nothing in the folder verifies for any example: the fibre of `v ∘ u` over `z` is the disjoint
union of the fibres of `u` over the `s` points of the fibre of `v`. The group plays no role
beyond the equivariance of `Can`; (v bis) holds for every `n` and every `H`, with the fibre of
`(X^n_Y)/H` identified with `E^n/H` by any enumeration of the fibre of `u`. For Déf. 1, the
justification of page 28, that two extensions of `k` « peuvent toujours être “dominées” par une
troisième », is not enough for transitivity: the two extensions `K'`, `K''` of `K₂` must be
dominated by a third extension of `K₂`, compatibly with the two embeddings of `K₂`
(`Amalgamation`), as the reading's note says. In Cor. 5, surjectivity uses only the first half
of Prop. 1 and the embedding of the extensions of finite type in `K̃`; injectivity uses both
halves and the homogeneity of `K̃`.

What this certifies is that the reading holds together at this point, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder98

variable {X Y Z : Type*}

/-- `u` has degree `r`: every fibre of `u` is finite with `r` elements (Example I). -/
def HasDeg (u : X → Y) (r : ℕ) : Prop := ∀ y, (u ⁻¹' {y}).Finite ∧ (u ⁻¹' {y}).ncard = r

/-- The fibre of `u` over `y`, as a finset. -/
noncomputable def fib {u : X → Y} {r : ℕ} (hu : HasDeg u r) (y : Y) : Finset X :=
  (hu y).1.toFinset

@[simp] theorem mem_fib {u : X → Y} {r : ℕ} (hu : HasDeg u r) {y : Y} {x : X} :
    x ∈ fib hu y ↔ u x = y := by simp [fib]

theorem card_fib {u : X → Y} {r : ℕ} (hu : HasDeg u r) (y : Y) : (fib hu y).card = r := by
  rw [fib, ← Set.ncard_eq_toFinset_card _ (hu y).1, (hu y).2]

theorem hasDeg_of_finset {u : X → Y} {r : ℕ} (s : Y → Finset X) (hs : ∀ y x, x ∈ s y ↔ u x = y)
    (hc : ∀ y, (s y).card = r) : HasDeg u r := fun y => by
  have : u ⁻¹' {y} = ↑(s y) := by ext x; simp [hs]
  rw [this]
  exact ⟨Finset.finite_toSet _, by rw [Set.ncard_coe_finset, hc]⟩

/-! ### The class `𝒩` and the degree: (i)–(iv), (i bis)–(iv bis) -/

/-- (i), (i bis) -/
theorem hasDeg_id : HasDeg (id : X → X) 1 :=
  hasDeg_of_finset (fun x => {x}) (fun y x => by simp [eq_comm]) fun _ => rfl

/-- (ii), (ii bis): `deg (v ∘ u) = deg v · deg u`. -/
theorem hasDeg_comp {u : X → Y} {v : Y → Z} {r s : ℕ} (hu : HasDeg u r) (hv : HasDeg v s) :
    HasDeg (v ∘ u) (s * r) := by
  classical
  refine hasDeg_of_finset (fun z => (fib hv z).biUnion (fib hu)) (fun z x => by simp) fun z => ?_
  rw [Finset.card_biUnion]
  · simp [card_fib]
  · intro y _ y' _ hyy'
    exact Finset.disjoint_left.2 fun x hx hx' => hyy' (((mem_fib hu).1 hx).symm.trans
      ((mem_fib hu).1 hx'))

/-- The fibre product `X ×_Y Y'`. -/
def Pullback (u : X → Y) {Y' : Type*} (f : Y' → Y) := {p : X × Y' // u p.1 = f p.2}

/-- (iii), (iii bis): the degree is invariant under base change. -/
theorem hasDeg_pullback {u : X → Y} {r : ℕ} (hu : HasDeg u r) {Y' : Type*} (f : Y' → Y) :
    HasDeg (fun p : Pullback u f => p.1.2) r := by
  classical
  refine hasDeg_of_finset (fun y' => (fib hu (f y')).attach.map
    ⟨fun x => ⟨(x.1, y'), (mem_fib hu).1 x.2⟩, fun a b h => Subtype.ext (by
      simpa using congrArg (fun p : Pullback u f => p.1.1) h)⟩) (fun y' p => ?_) fun y' => ?_
  · simp only [Finset.mem_map, Finset.mem_attach, true_and]
    exact ⟨by rintro ⟨x, rfl⟩; rfl, by rintro rfl; exact ⟨⟨p.1.1, (mem_fib hu).2 p.2⟩, rfl⟩⟩
  · simp [card_fib]

/-- (iv), (iv bis): `deg (u₁, u₂) = deg u₁ + deg u₂`. -/
theorem hasDeg_sum {X₁ X₂ : Type*} {u₁ : X₁ → Y} {u₂ : X₂ → Y} {r₁ r₂ : ℕ}
    (h₁ : HasDeg u₁ r₁) (h₂ : HasDeg u₂ r₂) : HasDeg (Sum.elim u₁ u₂) (r₁ + r₂) := by
  classical
  refine hasDeg_of_finset (fun y => (fib h₁ y).disjSum (fib h₂ y)) (fun y x => ?_) fun y => ?_
  · cases x <;> simp
  · simp [card_fib]


/-! ### (v), (v bis): the quotients `(X^n_Y)/H` -/

/-- The `n`-fold fibre product `X^n_Y`, as pairs `(y, t)` with `t : Fin n → u⁻¹(y)`. -/
def FibPow (u : X → Y) (n : ℕ) := {p : Y × (Fin n → X) // ∀ i, u (p.2 i) = p.1}

/-- `H ⊆ 𝔖_n` permuting the factors. -/
def fibPowSetoid (u : X → Y) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) :
    Setoid (FibPow u n) where
  r p q := p.1.1 = q.1.1 ∧ ∃ σ ∈ H, q.1.2 = p.1.2 ∘ σ
  iseqv := ⟨fun p => ⟨rfl, 1, H.one_mem, rfl⟩,
    fun ⟨h1, σ, hσ, h⟩ => ⟨h1.symm, σ⁻¹, H.inv_mem hσ, by rw [h]; ext; simp⟩,
    fun ⟨h1, σ, hσ, h⟩ ⟨h1', τ, hτ, h'⟩ => ⟨h1.trans h1', σ * τ, H.mul_mem hσ hτ,
      by rw [h', h]; rfl⟩⟩

/-- `(X^n_Y)/H`. -/
def QuotPow (u : X → Y) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) :=
  Quotient (fibPowSetoid u H)

/-- Its projection to `Y`. -/
def QuotPow.proj {u : X → Y} {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} :
    QuotPow u H → Y :=
  Quotient.lift (fun p : FibPow u n => p.1.1) fun _ _ h => h.1

/-- `E^n/H` for a set `E`. -/
def powSetoid (E : Type*) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) : Setoid (Fin n → E) where
  r s t := ∃ σ ∈ H, t = s ∘ σ
  iseqv := ⟨fun _ => ⟨1, H.one_mem, rfl⟩,
    fun ⟨σ, hσ, h⟩ => ⟨σ⁻¹, H.inv_mem hσ, by rw [h]; ext; simp⟩,
    fun ⟨σ, hσ, h⟩ ⟨τ, hτ, h'⟩ => ⟨σ * τ, H.mul_mem hσ hτ, by rw [h', h]; rfl⟩⟩

/-- (v), (v bis): if `u` has degree `r`, the projection `(X^n_Y)/H → Y` has degree
`card(E^n/H)`, `E = {1, …, r}`. -/
theorem hasDeg_quotPow {u : X → Y} {r : ℕ} (hu : HasDeg u r) {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) :
    HasDeg (QuotPow.proj : QuotPow u H → Y) (Nat.card (Quotient (powSetoid (Fin r) H))) := by
  classical
  intro y
  -- an enumeration of the fibre
  have hc : Fintype.card (fib hu y) = r := by simp [card_fib]
  let ι : Fin r ≃ fib hu y := (Fintype.equivFinOfCardEq hc).symm
  let g : Quotient (powSetoid (Fin r) H) → (QuotPow.proj : QuotPow u H → Y) ⁻¹' {y} :=
    Quotient.lift (fun s => ⟨Quotient.mk _ ⟨(y, fun i => (ι (s i)).1),
        fun i => (mem_fib hu).1 (ι (s i)).2⟩, rfl⟩)
      (fun s t ⟨σ, hσ, h⟩ => Subtype.ext (Quotient.sound ⟨rfl, σ, hσ, by rw [h]; rfl⟩))
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | h s => ?_
      induction b using Quotient.inductionOn with | h t => ?_
      obtain ⟨-, σ, hσ, h⟩ := Quotient.exact (congrArg Subtype.val hab)
      refine Quotient.sound ⟨σ, hσ, funext fun i => ι.injective (Subtype.ext ?_)⟩
      exact congrFun h i
    · rintro ⟨q, hq⟩
      induction q using Quotient.inductionOn with | h p => ?_
      have hp : p.1.1 = y := hq
      refine ⟨Quotient.mk _ fun i => ι.symm ⟨p.1.2 i, (mem_fib hu).2 ((p.2 i).trans hp)⟩,
        Subtype.ext (Quotient.sound ⟨hp.symm, 1, H.one_mem, ?_⟩)⟩
      ext i; simp
  have hfin : Finite ((QuotPow.proj : QuotPow u H → Y) ⁻¹' {y}) :=
    Finite.of_surjective g hg.2
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofBijective g hg).symm]


/-! ### The canonical sections `Can_{X/Y} : Y → Sym^r_Y(X)`: (i ter)–(iv ter) -/

/-- `Sym^r_Y(X) = (X^r_Y)/𝔖_r`: a point `y` and a multiset of `r` points of `u⁻¹(y)`. -/
def SymY (u : X → Y) (r : ℕ) :=
  Σ y : Y, {m : Multiset X // Multiset.card m = r ∧ ∀ x ∈ m, u x = y}

/-- `Can_{X/Y}(y)`: the class of the `r` points of the fibre, in any order (page 11). -/
noncomputable def Can {u : X → Y} {r : ℕ} (hu : HasDeg u r) (y : Y) : SymY u r :=
  ⟨y, (fib hu y).val, by simp [card_fib], fun x hx => (mem_fib hu).1 hx⟩

theorem SymY.ext {u : X → Y} {r : ℕ} {p q : SymY u r} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) :
    p = q := by
  obtain ⟨y, m, hm⟩ := p
  obtain ⟨y', m', hm'⟩ := q
  simp only at h1 h2
  subst h1 h2
  rfl

/-- `Sym^s` of a morphism over `Z`. -/
def SymY.map {A B : Type*} {a : A → Z} {b : B → Z} {s : ℕ} (f : A → B)
    (hf : ∀ x, b (f x) = a x) (p : SymY a s) : SymY b s :=
  ⟨p.1, p.2.1.map f, by simp [p.2.2.1], fun x hx => by
    obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.1 hx
    rw [hf]; exact p.2.2.2 x' hx'⟩

/-- `can : Sym^r_Y(X) → Sym^r_Z(X)` for `X → Y → Z`. -/
def SymY.push {u : X → Y} (v : Y → Z) {r : ℕ} (p : SymY u r) : SymY (v ∘ u) r :=
  ⟨v p.1, p.2.1, p.2.2.1, fun x hx => by simp [p.2.2.2 x hx]⟩

/-- `can : Sym^s_Z(Sym^r_Z(X)) → Sym^{rs}_Z(X)`, the union of the multisets. -/
def SymY.flatten {w : X → Z} {r s : ℕ} (p : SymY (fun q : SymY w r => q.1) s) :
    SymY w (s * r) :=
  ⟨p.1, p.2.1.bind fun q => q.2.1, by
    rw [Multiset.card_bind, Multiset.map_congr rfl fun q _ => q.2.2.1, Multiset.map_const',
      Multiset.sum_replicate, p.2.2.1, smul_eq_mul],
    fun x hx => by
      obtain ⟨q, hq, hxq⟩ := Multiset.mem_bind.1 hx
      rw [q.2.2.2 x hxq]; exact p.2.2.2 q hq⟩

/-- (i ter): `Can_{X/X} = id`, the fibre of `id` over `x` being `{x}`. -/
theorem can_id (x : X) : (Can hasDeg_id x).2.1 = {x} := by
  change (fib hasDeg_id x).val = {x}
  rw [← Finset.singleton_val]
  congr 1
  ext; simp

/-- (ii ter), the transitivity diagram of page 11: for `X → Y → Z` of degrees `r`, `s`,
`can ∘ can ∘ Sym^s(Can_{X/Y}) ∘ Can_{Y/Z} = Can_{X/Z}`. -/
theorem can_comp {u : X → Y} {v : Y → Z} {r s : ℕ} (hu : HasDeg u r) (hv : HasDeg v s) (z : Z) :
    SymY.flatten (SymY.map (SymY.push v) (fun _ => rfl)
      (SymY.map (Can hu) (fun _ => rfl) (Can hv z))) = Can (hasDeg_comp hu hv) z := by
  refine SymY.ext rfl ?_
  change Multiset.bind (((fib hv z).val.map (Can hu)).map (SymY.push v)) (fun q => q.2.1) =
    (fib (hasDeg_comp hu hv) z).val
  rw [Multiset.map_map, Multiset.bind_map]
  change (fib hv z).val.bind (fun y => (fib hu y).val) = _
  have hnd : ((fib hv z).val.bind fun y => (fib hu y).val).Nodup := by
    refine Multiset.nodup_bind.2 ⟨fun y _ => (fib hu y).nodup, ?_⟩
    refine (fib hv z).nodup.pairwise fun y _ y' _ hyy' => ?_
    exact Multiset.disjoint_left.2 fun hx hx' => hyy' (((mem_fib hu).1 hx).symm.trans
      ((mem_fib hu).1 hx'))
  refine (Multiset.Nodup.ext hnd (fib _ z).nodup).2 fun x => ?_
  · simp only [Multiset.mem_bind, Finset.mem_val, mem_fib, Function.comp_apply]
    exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun h => ⟨u x, h, rfl⟩⟩

/-- (iii ter): `Can` commutes with base change along `f : Y' → Y`. -/
theorem can_pullback {u : X → Y} {r : ℕ} (hu : HasDeg u r) {Y' : Type*} (f : Y' → Y) (y' : Y') :
    (Can (hasDeg_pullback hu f) y').2.1.map (fun p => p.1.1) = (Can hu (f y')).2.1 := by
  change (fib (hasDeg_pullback hu f) y').val.map _ = (fib hu (f y')).val
  have hnd : ((fib (hasDeg_pullback hu f) y').val.map fun p => p.1.1).Nodup := by
    refine (fib _ y').nodup.map_on fun p hp q hq h => Subtype.ext (Prod.ext h ?_)
    exact ((mem_fib _).1 hp).trans ((mem_fib _).1 hq).symm
  refine (Multiset.Nodup.ext hnd (fib _ _).nodup).2 fun x => ?_
  · simp only [Multiset.mem_map, Finset.mem_val, mem_fib]
    exact ⟨fun ⟨p, hp, hx⟩ => hx ▸ p.2.trans (congrArg f hp),
      fun hx => ⟨⟨(x, y'), hx⟩, rfl, rfl⟩⟩

/-- (iv ter): for `X = X₁ ⊔ X₂`, `Can_{X/Y}` is the sum of `Can_{X₁/Y}` and `Can_{X₂/Y}`. -/
theorem can_sum {X₁ X₂ : Type*} {u₁ : X₁ → Y} {u₂ : X₂ → Y} {r₁ r₂ : ℕ}
    (h₁ : HasDeg u₁ r₁) (h₂ : HasDeg u₂ r₂) (y : Y) :
    (Can (hasDeg_sum h₁ h₂) y).2.1 =
      (Can h₁ y).2.1.map Sum.inl + (Can h₂ y).2.1.map Sum.inr := by
  change (fib (hasDeg_sum h₁ h₂) y).val =
    (fib h₁ y).val.map Sum.inl + (fib h₂ y).val.map Sum.inr
  have hnd : ((fib h₁ y).val.map Sum.inl + (fib h₂ y).val.map Sum.inr).Nodup := by
    rw [Multiset.nodup_add]
    refine ⟨(fib h₁ y).nodup.map Sum.inl_injective, (fib h₂ y).nodup.map Sum.inr_injective,
      Multiset.disjoint_left.2 fun ha hb => ?_⟩
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hb
    exact Sum.inr_ne_inl hb
  refine (Multiset.Nodup.ext (fib _ y).nodup hnd).2 fun x => ?_
  cases x <;> simp

/-- `Can` is compatible with the action of `G` (page 11): for `u` equivariant,
`Can(g y) = g · Can(y)`. -/
theorem can_smul {G : Type*} [Group G] [MulAction G X] [MulAction G Y] {u : X → Y} {r : ℕ}
    (hu : HasDeg u r) (hequiv : ∀ (g : G) x, u (g • x) = g • u x) (g : G) (y : Y) :
    (Can hu (g • y)).2.1 = (Can hu y).2.1.map (g • ·) := by
  change (fib hu (g • y)).val = (fib hu y).val.map (g • ·)
  have hinj : Function.Injective (g • · : X → X) := fun a b h => by
    simpa using congrArg (g⁻¹ • ·) h
  refine (Multiset.Nodup.ext (fib _ _).nodup ((fib hu y).nodup.map hinj)).2 fun x => ?_
  simp only [Finset.mem_val, mem_fib, Multiset.mem_map]
  constructor
  · intro hx
    refine ⟨g⁻¹ • x, ?_, by simp⟩
    rw [hequiv, hx, inv_smul_smul]
  · rintro ⟨x', hx', rfl⟩
    rw [hequiv, hx']


/-! ### Pages 28–30: classes of sheaves over the extensions of the base field

Déf. 1 of page 28 calls `F₁` on `X ⊗_k K₁` and `F₂` on `X ⊗_k K₂` `k`-equivalent when there are
an extension `K'` and `k`-embeddings `u_i : K_i → K'` with `F₁ ⊗_{K₁} K' ≃ F₂ ⊗_{K₂} K'`; the
page says it is an equivalence relation « en vertu de la transitivité de l'extension des
scalaires et du fait que deux extensions de `k` peuvent toujours être “dominées” par une
troisième ». Cor. 5 of page 30, for `K̃` algebraically closed of infinite transcendence degree,
puts the classes `𝔉(X/k)` in bijection with the classes of sheaves on `X ⊗_k K̃` modulo
`Aut(K̃/k)`.

The model: a category `C` (the extensions of `k` and their `k`-embeddings), for each `K` a type
`Φ K` (the isomorphism classes of sheaves on `X ⊗_k K`), and base change
`bc u : Φ K → Φ K'`, functorial. -/

section Classes

open CategoryTheory

universe v u w

variable {C : Type u} [Category.{v} C] {Φ : C → Type w}
  {bc : ∀ {K K' : C}, (K ⟶ K') → Φ K → Φ K'}

variable (Φ bc) in
/-- Déf. 1: `(K₁, F₁)` and `(K₂, F₂)` are `k`-equivalent when they become isomorphic over a
common extension `K'`. -/
def KEquiv (p q : Σ K, Φ K) : Prop :=
  ∃ (K' : C) (u₁ : p.1 ⟶ K') (u₂ : q.1 ⟶ K'), bc u₁ p.2 = bc u₂ q.2

variable (C) in
/-- Two extensions `B`, `B'` of `A` are dominated by a third extension of `A`: a common
extension `D` with embeddings that agree on `A` (for fields, a quotient of `B ⊗_A B'` by a
maximal ideal). -/
def Amalgamation : Prop :=
  ∀ ⦃A B B' : C⦄ (f : A ⟶ B) (g : A ⟶ B'), ∃ (D : C) (f' : B ⟶ D) (g' : B' ⟶ D),
    f ≫ f' = g ≫ g'

/-- Déf. 1: `k`-equivalence is an equivalence relation, by the transitivity of base change and
the domination of two extensions of `K₂` by a third extension of `K₂`. -/
theorem kEquiv_equivalence
    (hcomp : ∀ {K K' K''} (f : K ⟶ K') (g : K' ⟶ K'') a, bc (f ≫ g) a = bc g (bc f a))
    (ham : Amalgamation C) : Equivalence (KEquiv Φ bc) where
  refl p := ⟨p.1, 𝟙 _, 𝟙 _, rfl⟩
  symm := fun ⟨K', u₁, u₂, h⟩ => ⟨K', u₂, u₁, h.symm⟩
  trans := by
    rintro p q r ⟨K', u₁, u₂, h⟩ ⟨K'', v₂, v₃, h'⟩
    dsimp only at h h'
    obtain ⟨D, a, b, hab⟩ := ham u₂ v₂
    refine ⟨D, u₁ ≫ a, v₃ ≫ b, ?_⟩
    dsimp only
    rw [hcomp, hcomp, h, ← hcomp, hab, hcomp, h', ← hcomp]

/-- Page 29: `𝔉(X/k)` is contravariant in `X`. A pullback `ρ` of sheaves along `X' → X`,
compatible with base change, preserves `k`-equivalence. -/
theorem kEquiv_map {Ψ : C → Type w} {bc' : ∀ {K K' : C}, (K ⟶ K') → Ψ K → Ψ K'}
    (ρ : ∀ K, Φ K → Ψ K) (hρ : ∀ {K K'} (u : K ⟶ K') a, ρ K' (bc u a) = bc' u (ρ K a))
    {p q : Σ K, Φ K} (h : KEquiv Φ bc p q) : KEquiv Ψ bc' ⟨p.1, ρ _ p.2⟩ ⟨q.1, ρ _ q.2⟩ := by
  obtain ⟨K', u₁, u₂, h⟩ := h
  exact ⟨K', u₁, u₂, by dsimp only at h ⊢; rw [← hρ, ← hρ, h]⟩

/-! Cor. 5. `fg K` says that `K` is of finite type over `k`; `Ω` stands for `K̃`. The
hypotheses are the two halves of Prop. 1, for `X` of finite type (`hdesc`: a sheaf is defined
over a sub-extension of finite type; `hfin`: two equivalent coherent sheaves defined over extensions
of finite type become isomorphic over an extension of finite type), and the two consequences the
reading draws from the page's hypotheses on `K̃`, algebraically closed of infinite
transcendence degree (`huniv`: every extension of finite type embeds in `K̃`; `hhomog`: two
embeddings of an extension of finite type differ by an automorphism of `K̃`). -/

variable {fg : C → Prop} {Ω : C}
  (hid : ∀ K (a : Φ K), bc (𝟙 K) a = a)
  (hcomp : ∀ {K K' K''} (f : K ⟶ K') (g : K' ⟶ K'') a, bc (f ≫ g) a = bc g (bc f a))
  (huniv : ∀ K, fg K → Nonempty (K ⟶ Ω))
  (hhomog : ∀ K, fg K → ∀ f g : K ⟶ Ω, ∃ σ : Ω ≅ Ω, g = f ≫ σ.hom)
  (hdesc : ∀ K (a : Φ K), ∃ (K₀ : C) (j : K₀ ⟶ K) (a₀ : Φ K₀), fg K₀ ∧ bc j a₀ = a)
  (hfin : ∀ p q : Σ K, Φ K, fg p.1 → fg q.1 → KEquiv Φ bc p q →
    ∃ (K' : C) (u₁ : p.1 ⟶ K') (u₂ : q.1 ⟶ K'), fg K' ∧ bc u₁ p.2 = bc u₂ q.2)

include hcomp huniv hdesc in
/-- Cor. 5, surjectivity: every class has a representative on `X ⊗_k K̃`. -/
theorem corollaire5_surj (ham : Amalgamation C) (p : Σ K, Φ K) :
    ∃ x : Φ Ω, KEquiv Φ bc p ⟨Ω, x⟩ := by
  obtain ⟨K, a⟩ := p
  obtain ⟨K₀, j, a₀, hK₀, rfl⟩ := hdesc K a
  obtain ⟨e⟩ := huniv K₀ hK₀
  obtain ⟨D, f, g, hfg⟩ := ham j e
  exact ⟨bc e a₀, D, f, g, by dsimp only; rw [← hcomp, hfg, hcomp]⟩

include hid hcomp huniv hhomog hdesc hfin in
/-- Cor. 5, injectivity: two sheaves on `X ⊗_k K̃` are `k`-equivalent if and only if
`F ≃ σ(G)` for an automorphism `σ` of `K̃`. -/
theorem corollaire5_iff (x y : Φ Ω) :
    KEquiv Φ bc ⟨Ω, x⟩ ⟨Ω, y⟩ ↔ ∃ σ : Ω ≅ Ω, x = bc σ.hom y := by
  constructor
  · rintro ⟨K', u₁, u₂, h⟩
    dsimp only at h
    obtain ⟨K₁, j₁, x₁, hK₁, rfl⟩ := hdesc Ω x
    obtain ⟨K₂, j₂, y₂, hK₂, rfl⟩ := hdesc Ω y
    obtain ⟨K'', w₁, w₂, hK'', hw⟩ := hfin ⟨K₁, x₁⟩ ⟨K₂, y₂⟩ hK₁ hK₂
      ⟨K', j₁ ≫ u₁, j₂ ≫ u₂, by dsimp only; rw [hcomp, hcomp, h]⟩
    dsimp only at hw
    obtain ⟨e⟩ := huniv K'' hK''
    obtain ⟨σ₁, hσ₁⟩ := hhomog K₁ hK₁ (w₁ ≫ e) j₁
    obtain ⟨σ₂, hσ₂⟩ := hhomog K₂ hK₂ (w₂ ≫ e) j₂
    refine ⟨σ₂.symm ≪≫ σ₁, ?_⟩
    rw [hσ₁, hσ₂, Iso.trans_hom, Iso.symm_hom, hcomp, hcomp, hcomp, hcomp, ← hcomp σ₂.hom,
      Iso.hom_inv_id, hid, hw, hcomp]
  · rintro ⟨σ, rfl⟩
    exact ⟨Ω, 𝟙 _, σ.hom, by dsimp only; rw [hid]⟩

end Classes

/-! ### Example III (page 13): coverings and `Φ(E) = X ×^Γ E`

`Γ` acts on a space `X` by homeomorphisms, and every point has a neighbourhood `U` with
`gU ∩ U = ∅` for `g ≠ 1` (the action is free and properly discontinuous in the sense of
covering spaces, the reading of « non ramifié »). `Φ(E)` is the quotient of `X × E` by the
diagonal action, `E` a discrete `Γ`-set. -/

section ExampleIII

open Topology

variable {Γ : Type*} [Group Γ] {X : Type*} [MulAction Γ X]
  {E F : Type*} [MulAction Γ E] [MulAction Γ F]

variable (Γ X) in
/-- `Φ(E) = X ×^Γ E`, the contracted product. -/
abbrev Phi (E : Type*) [MulAction Γ E] := Quotient (MulAction.orbitRel Γ (X × E))

variable (Γ) in
/-- The class of `(x, e)` in `X ×^Γ E`. -/
def Phi.mk (x : X) (e : E) : Phi Γ X E := Quotient.mk _ (x, e)

theorem Phi.mk_eq_mk {x y : X} {e e' : E} :
    Phi.mk Γ x e = Phi.mk Γ y e' ↔ ∃ g : Γ, g • y = x ∧ g • e' = e := by
  simp [Phi.mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Prod.ext_iff]

theorem Phi.mk_smul (g : Γ) (x : X) (e : E) : Phi.mk Γ (g • x) (g • e) = Phi.mk Γ x e :=
  Phi.mk_eq_mk.2 ⟨g, rfl, rfl⟩

@[elab_as_elim]
theorem Phi.ind {P : Phi Γ X E → Prop} (h : ∀ x e, P (Phi.mk Γ x e)) (q : Phi Γ X E) : P q :=
  Quotient.ind (fun p => h p.1 p.2) q

variable (Γ X) in
/-- `Φ(f) : X ×^Γ E → X ×^Γ F` for an equivariant `f : E → F`. -/
def Phi.map (f : E → F) (hf : ∀ (g : Γ) e, f (g • e) = g • f e) : Phi Γ X E → Phi Γ X F :=
  Quotient.map (Prod.map id f) fun _ b ⟨g, h⟩ => ⟨g, h ▸ Prod.ext rfl (hf g b.2).symm⟩

@[simp] theorem Phi.map_mk {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) (x : X) (e : E) :
    Phi.map Γ X f hf (Phi.mk Γ x e) = Phi.mk Γ x (f e) := rfl

/-- The points of `Φ(E)` over `[x, e']` are the `[x, i]`, `f i = e'`. -/
theorem Phi.map_eq_mk {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) (x : X) (e' : F)
    (p : Phi Γ X E) : Phi.map Γ X f hf p = Phi.mk Γ x e' ↔ ∃ i, f i = e' ∧ Phi.mk Γ x i = p := by
  induction p using Phi.ind with | h y e => ?_
  refine ⟨fun h => ?_, by rintro ⟨i, rfl, h⟩; rw [← h]; rfl⟩
  obtain ⟨g, rfl, hg⟩ := Phi.mk_eq_mk.1 h.symm
  exact ⟨g • e, by rw [hf, hg], Phi.mk_smul g y e⟩

/-- For a free action, `i ↦ [x, i]` is injective. -/
theorem Phi.mk_injective (hfree : ∀ (g : Γ) (x : X), g • x = x → g = 1) (x : X) :
    Function.Injective (Phi.mk Γ x : E → Phi Γ X E) := fun i j h => by
  obtain ⟨g, hg, rfl⟩ := Phi.mk_eq_mk.1 h
  rw [hfree g x hg, one_smul]

/-- Example III, the hypothesis of page 13 (« on suppose que `Φ` transforme les morphismes de
degré `r` en morphismes de degré `r` »): for a free action, `Φ` preserves degrees. -/
theorem hasDeg_phi (hfree : ∀ (g : Γ) (x : X), g • x = x → g = 1) {f : E → F}
    (hf : ∀ (g : Γ) e, f (g • e) = g • f e) {r : ℕ} (hr : HasDeg f r) :
    HasDeg (Phi.map Γ X f hf) r := by
  classical
  refine hasDeg_of_finset (fun q => (fib hr q.out.2).image (Phi.mk Γ q.out.1)) (fun q p => ?_)
    fun q => (Finset.card_image_of_injective _ (Phi.mk_injective hfree _)).trans (card_fib ..)
  conv_rhs => rw [← q.out_eq]
  simp only [Finset.mem_image, mem_fib]
  exact (Phi.map_eq_mk hf _ _ p).symm

/-- `Φ` commutes with finite sums: `X ×^Γ (E ⊔ F) ≃ (X ×^Γ E) ⊔ (X ×^Γ F)`. -/
def Phi.sumEquiv : Phi Γ X (E ⊕ F) ≃ Phi Γ X E ⊕ Phi Γ X F where
  toFun := Quotient.lift (fun p => p.2.elim (.inl <| Phi.mk Γ p.1 ·) (.inr <| Phi.mk Γ p.1 ·))
    fun _ b ⟨g, h⟩ => by subst h; obtain ⟨x, e | e⟩ := b <;> exact congrArg _ (Phi.mk_smul ..)
  invFun := Sum.elim (Phi.map Γ X Sum.inl fun _ _ => rfl) (Phi.map Γ X Sum.inr fun _ _ => rfl)
  left_inv := Phi.ind fun x e => by cases e <;> rfl
  right_inv := by rintro (q | q) <;> induction q using Phi.ind <;> rfl

/-! The page goes on: `Φ` takes canonical morphisms to canonical morphisms, and breaks off.
`Sym^r_F(E)` is a `Γ`-set, `Can_{E/F}` is equivariant (`can_smul`), and `Φ(Can_{E/F})`, followed
by the comparison `X ×^Γ Sym^r_F(E) → Sym^r_{Φ F}(Φ E)`, is `Can_{Φ E/Φ F}`. -/

/-- `Sym^r_F(E)` is a `Γ`-set when `f` is equivariant. -/
@[reducible] def SymY.mulAction {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) (r : ℕ) :
    MulAction Γ (SymY f r) where
  smul g p := ⟨g • p.1, p.2.1.map (g • ·), by simp [p.2.2.1], fun x hx => by
    obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.1 hx
    rw [hf, p.2.2.2 x' hx']⟩
  one_smul p := SymY.ext (one_smul ..) (by
    change Multiset.map (fun x => (1 : Γ) • x) p.2.1 = p.2.1; simp)
  mul_smul g h p := SymY.ext (mul_smul ..) (by
    change Multiset.map (fun x => (g * h) • x) p.2.1 = (p.2.1.map (h • ·)).map (g • ·)
    simp [mul_smul])

/-- `Can_{E/F}` is equivariant. -/
theorem can_smul' {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) {r : ℕ} (hr : HasDeg f r)
    (g : Γ) (y : F) : letI := SymY.mulAction hf r; Can hr (g • y) = g • Can hr y :=
  SymY.ext rfl (can_smul hr hf g y)

/-- The comparison `X ×^Γ Sym^r_F(E) → Sym^r_{Φ F}(Φ E)`, `[x, (e', m)] ↦ ([x, e'], [x, m])`. -/
def Phi.symComp {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) (r : ℕ) :
    letI := SymY.mulAction hf r; Phi Γ X (SymY f r) → SymY (Phi.map Γ X f hf) r :=
  letI := SymY.mulAction hf r
  Quotient.lift (fun p => ⟨Phi.mk Γ p.1 p.2.1, p.2.2.1.map (Phi.mk Γ p.1), by simp [p.2.2.2.1],
      fun _ h => by
        obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 h
        rw [Phi.map_mk, p.2.2.2.2 i hi]⟩)
    fun a b ⟨g, h⟩ => by
      subst h
      refine SymY.ext (Phi.mk_smul ..) ?_
      change (b.2.2.1.map (g • ·)).map (Phi.mk Γ (g • b.1)) = b.2.2.1.map (Phi.mk Γ b.1)
      simp [Phi.mk_smul]

/-- Example III, the claim on which page 13 breaks off: `Φ` takes `Can_{E/F}` to
`Can_{Φ E/Φ F}`, through the comparison `Phi.symComp`. -/
theorem phi_can (hfree : ∀ (g : Γ) (x : X), g • x = x → g = 1) {f : E → F}
    (hf : ∀ (g : Γ) e, f (g • e) = g • f e) {r : ℕ} (hr : HasDeg f r) (q : Phi Γ X F) :
    letI := SymY.mulAction hf r
    Phi.symComp hf r (Phi.map Γ X (Can hr) (can_smul' hf hr) q) =
      Can (hasDeg_phi hfree hf hr) q := by
  induction q using Phi.ind with | h x e' => ?_
  refine SymY.ext rfl ?_
  change (fib hr e').val.map (Phi.mk Γ x) = (fib (hasDeg_phi hfree hf hr) _).val
  refine (Multiset.Nodup.ext ((fib hr e').nodup.map (Phi.mk_injective hfree x))
    (fib _ _).nodup).2 fun p => ?_
  simp only [Multiset.mem_map, Finset.mem_val, mem_fib, Phi.map_eq_mk]

/-- For a free action the comparison is bijective: `X ×^Γ Sym^r_F(E) ≅ Sym^r_{Φ F}(Φ E)`. -/
theorem Phi.symComp_bijective (hfree : ∀ (g : Γ) (x : X), g • x = x → g = 1) {f : E → F}
    (hf : ∀ (g : Γ) e, f (g • e) = g • f e) (r : ℕ) :
    letI := SymY.mulAction hf r; Function.Bijective (Phi.symComp (X := X) hf r) := by
  let := SymY.mulAction hf r
  constructor
  · intro a b hab
    induction a using Phi.ind with | h x p => ?_
    induction b using Phi.ind with | h y p' => ?_
    obtain ⟨e', m, hm⟩ := p
    obtain ⟨e'', n, hn⟩ := p'
    have h2 : m.map (Phi.mk Γ x) = n.map (Phi.mk Γ y) := congrArg (fun s => s.2.1) hab
    obtain ⟨g, hgx, hge⟩ := Phi.mk_eq_mk.1 (congrArg Sigma.fst hab)
    refine Phi.mk_eq_mk.2 ⟨g, hgx, SymY.ext hge (Multiset.map_injective (Phi.mk_injective hfree x) ?_)⟩
    change g • y = x at hgx
    change (n.map (g • ·)).map _ = _
    rw [h2, ← hgx]
    simp [Phi.mk_smul]
  · rintro ⟨q, M, hM, hMq⟩
    obtain ⟨⟨x, e'⟩, rfl⟩ := Quotient.mk_surjective q
    have hpt p (hp : p ∈ M) : ∃ i, f i = e' ∧ Phi.mk Γ x i = p :=
      (Phi.map_eq_mk hf x e' p).1 (hMq p hp)
    refine ⟨Phi.mk Γ x ⟨e', M.pmap (fun _ h => Classical.choose h) hpt, by simpa using hM,
      fun i hi => ?_⟩, SymY.ext rfl ?_⟩
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_pmap.1 hi
      exact (Classical.choose_spec (hpt p hp)).1
    · change (M.pmap _ hpt).map (Phi.mk Γ x) = M
      rw [Multiset.map_pmap]
      exact (Multiset.pmap_congr M fun p hp _ _ => (Classical.choose_spec (hpt p hp)).2).trans
        ((Multiset.pmap_eq_map _ id M hpt).trans M.map_id)

section Topology

variable [TopologicalSpace X] [ContinuousConstSMul Γ X] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace F] [DiscreteTopology F]

omit [ContinuousConstSMul Γ X] [DiscreteTopology E] in
theorem Phi.continuous_mk (e : E) : Continuous (Phi.mk Γ · e : X → Phi Γ X E) :=
  continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)

/-- `x ↦ [x, e]` is open, the quotient by a group action being open. -/
theorem Phi.isOpenMap_mk (e : E) : IsOpenMap (Phi.mk Γ · e : X → Phi Γ X E) := by
  have : ContinuousConstSMul Γ E := ⟨fun _ => continuous_of_discreteTopology⟩
  refine (isOpenMap_quotient_mk'_mul (Γ := Γ) (T := X × E)).comp fun U hU => ?_
  convert hU.prod (isOpen_discrete {e}) using 1
  ext ⟨x, e'⟩
  simp [eq_comm, and_comm]

omit [ContinuousConstSMul Γ X] [DiscreteTopology F] in
theorem Phi.continuous_map {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) :
    Continuous (Phi.map Γ X f hf) :=
  (continuous_id.prodMap continuous_of_discreteTopology).quotient_map' _

/-- Example III: for `Γ` acting on `X` with every point having a neighbourhood disjoint from its
translates, `Φ` takes every equivariant map of discrete `Γ`-sets to a covering map; by
`hasDeg_phi`, one with `r` sheets when the map has degree `r`. -/
theorem isCoveringMap_phi
    (hdisj : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : Γ, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) : IsCoveringMap (Phi.map Γ X f hf) := by
  intro q
  induction q using Phi.ind with | h x e' => ?_
  obtain ⟨U₀, hU₀, hd₀⟩ := hdisj x
  have hU : IsOpen (interior U₀) := isOpen_interior
  have hxU : x ∈ interior U₀ := mem_interior_iff_mem_nhds.2 hU₀
  have hd : ∀ (g : Γ), ∀ y ∈ interior U₀, ∀ z ∈ interior U₀, g • z = y → g = 1 :=
    fun g y hy z hz h => hd₀ g ⟨y, ⟨z, interior_subset hz, h⟩, interior_subset hy⟩
  have hV : IsOpen ((Phi.mk Γ · e' : X → Phi Γ X F) '' interior U₀) :=
    Phi.isOpenMap_mk e' _ hU
  let W (i : f ⁻¹' {e'}) := (Phi.mk Γ · i.1 : X → Phi Γ X E) '' interior U₀
  have hexh : Phi.map Γ X f hf ⁻¹' ((Phi.mk Γ · e') '' interior U₀) ⊆ ⋃ i, W i := by
    rintro p ⟨y, hy, hp⟩
    obtain ⟨i, hi, rfl⟩ := (Phi.map_eq_mk hf y e' p).1 hp.symm
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, y, hy, rfl⟩
  rcases isEmpty_or_nonempty (f ⁻¹' {e'}) with hE | hne
  · refine (IsEvenlyCovered.of_preimage_eq_empty Empty (hV.mem_nhds ⟨x, hxU, rfl⟩)
      (Set.eq_empty_of_subset_empty (hexh.trans (by simp)))).to_isEvenlyCovered_preimage
  have : Nonempty (Phi Γ X F → Phi Γ X E) := ⟨fun _ => Phi.mk Γ x hne.some.1⟩
  refine (IsEvenlyCovered.of_trivialization (t := hV.trivializationDiscrete W _
    (fun i S hS => ⟨fun h => ?_, fun h => ?_⟩) (fun i => ?_) (fun i => ?_) (fun i j hij => ?_) hexh)
    ⟨x, hxU, rfl⟩).to_isEvenlyCovered_preimage
  · exact (h.preimage (Phi.continuous_map hf)).inter (Phi.isOpenMap_mk i.1 _ hU)
  · have : S = (Phi.mk Γ · e') '' (interior U₀ ∩ (Phi.mk Γ · i.1) ⁻¹'
        (Phi.map Γ X f hf ⁻¹' S ∩ W i)) := by
      ext w
      refine ⟨fun hw => ?_, ?_⟩
      · obtain ⟨y, hy, rfl⟩ := hS hw
        refine ⟨y, ⟨hy, ?_, y, hy, rfl⟩, rfl⟩
        change Phi.mk Γ y (f i.1) ∈ S
        rwa [show f i.1 = e' from i.2]
      · rintro ⟨y, ⟨-, hy, -⟩, rfl⟩
        change Phi.mk Γ y (f i.1) ∈ S at hy
        rwa [show f i.1 = e' from i.2] at hy
    rw [this]
    exact Phi.isOpenMap_mk e' _ (hU.inter (h.preimage (Phi.continuous_mk i.1)))
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
    obtain ⟨g, hg, -⟩ := Phi.mk_eq_mk.1 (h : Phi.mk Γ y (f i.1) = Phi.mk Γ z (f i.1))
    rw [hd g y hy z hz hg, one_smul] at hg
    exact congrArg (Phi.mk Γ · i.1) hg.symm
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, congrArg (Phi.mk Γ y) i.2⟩
  · refine Set.disjoint_left.2 fun _ ⟨y, hy, h1⟩ ⟨z, hz, h2⟩ => hij ?_
    obtain ⟨g, hg, h⟩ := Phi.mk_eq_mk.1 (h2.trans h1.symm)
    rw [hd g z hz y hy hg, one_smul] at h
    exact Subtype.ext h

end Topology

end ExampleIII

end Grothendieck.Folder98
