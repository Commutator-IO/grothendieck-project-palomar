module

public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
# Folder 74: generalised cubic complexes around a triangle (pages 92–103, 116)

Finding `74-gq2t-latin-square-reduction` of `src/content/findings.ts`, from the
modernised reading `transcripts/74/74.modern.tex`, sections 19–21.

A graph `G` satisfies **axiom 1** if every edge lies in a unique triangle, and
**axiom 2** if every vertex off a triangle is adjacent to a vertex of it. Fix a
triangle `t₀ = {t 0, t 1, t 2}`. For `α : Fin 3`, `Ẽ_α` (`Et α`) is the set of
vertices off `t₀` adjacent to `t α`. The file proves:

* (pp. 93–99, Props 1–5) the third vertex of the vertical triangle on
  `{t α, s}` is a fixed-point-free involution `σ_α` of `Ẽ_α`; a vertex of `Ẽ_β`,
  `β ≠ α`, is adjacent to exactly one of `s, σ_α s`; an edge between `Ẽ_α` and
  `Ẽ_β` lies in a unique upper triangle `x ∈ Γ̃` (`UT`), which meets each `Ẽ_α`
  once; `Γ̃` is stable under `σ = ∏ σ_α`.
* (pp. 101–102) with `E_α = Ẽ_α/σ_α` and `Γ = Γ̃/σ`, the map
  `Γ → E_α × E_β` is bijective for `α ≠ β` (`latin`): `Γ` is a Latin square;
  for each `α`, `Γ̃` is the pull-back of the double cover `Ẽ_α → E_α` along
  `Γ → E_α` (`pullback`), whence a transitive system of isomorphisms between
  the three pull-backs over `Γ` (`transition`, `transition_trans`); the counts
  `|Ẽ_α| = 2|E_α|`, `|Γ̃| = 2|Γ|`, `|Γ| = |E_α| |E_β|`, and `E_β ≃ E_γ` as soon
  as `Ẽ_α` is nonempty (Cor. of p. 99).
* (pp. 96–100, the Scholie) the graph is isomorphic to the graph built on
  `t₀ ⊔ ∐ Ẽ_α` from its data (`Config.scholieIso`), and these data satisfy (*)
  (injectivity of the pair projections), `β_Γ̃` (exactly one point of each orbit
  of `σ_α` is linked to a given point of `Ẽ_β`) and (Ka) (`scholie_forward`).
  Conversely, for data satisfying `β_Γ̃` and (Ka), the graph built from them
  satisfies axioms 1 and 2 (`Scholie.scholie_converse`) and its upper triangles
  are the elements of `T` (`Scholie.upper_triangle`); under (*) and `β_Γ̃`, axiom
  1 holds if and only if (Ka) does (`Scholie.axiom1_iff_ka`).
* (pp. 101–103, problems I and II) a Latin square `Γ → E_α` with three double
  covers `Ẽ_α → E_α` and a set `Γ̃` identified with each pull-back gives data
  satisfying (*) and `β_Γ̃` (`LatinCover.star`, `LatinCover.beta`), hence, under
  (Ka), a graph satisfying axioms 1 and 2 (`LatinCover.converse`); a graph gives
  such a Latin square with its covers (`Config.latinCover`).
* (necessity of (Ka)) a Latin square of order 2 with trivial double covers
  satisfies (*) and `β_Γ̃` but not (Ka), and its graph violates axiom 1
  (`ka_needed`). The sentence of page 97, that data satisfying (*) give a graph
  satisfying axiom 1, needs the marginal condition.
* (p. 116) for a group `G`, the maps `(x, y, z) ↦ (x, a⁻¹z⁻¹, a⁻¹y⁻¹)` preserve
  `xyz = 1` for every `a` if and only if every element has order dividing 2
  (`p116`), and then `G` is commutative (`p116_comm`).
* (the count used by folder 69) for permutations `f, g, h` of a commutative group,
  `f x + g y = h (x + y)` for all `x, y` if and only if they are a common additive
  automorphism followed by translations by `c_f`, `c_g`, `c_f + c_g`
  (`autotopism_iff`); the Klein group has 6 automorphisms (`card_klein_addAut`) and
  its table 96 autotopisms (`card_klein_autotopisms`, cross-checked by enumeration in
  `card_klein_autotopisms_decide`). With two lifts and the 6 permutations of a
  triangle this gives the 1152 of folder 69; the lift is not formalised.

The forward direction uses axiom 2 only for `t₀` and for the vertical
triangles, and does not use axiom 3 (the `Ẽ_α` nonempty), which serves only for
the counts. (Ka) in triangle form (`Ka`) implies (*), and under (*) it is
equivalent to the shape of the margin of page 96 with the conclusion
`(s_α) ∈ Γ̃` (`Scholie.ka_iff`).

The axiom (Ka) is only partly legible on the leaf; `Ka` and `KaPage` are
reconstructions, the forms under which the Scholie becomes an equivalence. What this certifies is
that the reading holds together, not that it is what the page says (issue
#26).
-/

namespace Grothendieck.Folder74

noncomputable section

open Function

/-! ## Three indices -/

/-- The third element of `Fin 3`, for two distinct ones. -/
def third (α β : Fin 3) : Fin 3 := -(α + β)

theorem third_spec : ∀ α β : Fin 3, α ≠ β →
    third α β ≠ α ∧ third α β ≠ β ∧ ∀ δ, δ = α ∨ δ = β ∨ δ = third α β := by
  decide

theorem fin3_cases (α β γ : Fin 3) (hab : α ≠ β) (hac : α ≠ γ) (hbc : β ≠ γ) :
    ∀ δ, δ = α ∨ δ = β ∨ δ = γ := by
  revert α β γ; decide

/-! ## The axioms (page 92) -/

section Axioms
variable {V : Type*} (G : SimpleGraph V)

/-- Axiom 1: every edge lies in a unique triangle. -/
def Axiom1 : Prop := ∀ x y, G.Adj x y → ∃! z, G.Adj x z ∧ G.Adj y z

/-- Axiom 2: a vertex off a triangle is adjacent to one of its vertices. -/
def Axiom2 : Prop := ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
  ∀ s, s ≠ a → s ≠ b → s ≠ c → G.Adj s a ∨ G.Adj s b ∨ G.Adj s c

end Axioms

/-! ## Quotient by an involution, and Latin squares -/

section Involution
variable {X : Type*} (f : X → X) (hf : ∀ x, f (f x) = x)

/-- The orbits of an involution. -/
def invSetoid : Setoid X where
  r x y := y = x ∨ y = f x
  iseqv := by
    refine ⟨fun x => Or.inl rfl, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (hf x).symm
    · rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (hf x)

theorem inv_mk_eq_iff (x y : X) :
    Quotient.mk (invSetoid f hf) x = Quotient.mk (invSetoid f hf) y ↔ y = x ∨ y = f x :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem inv_mk_f (x : X) :
    Quotient.mk (invSetoid f hf) (f x) = Quotient.mk (invSetoid f hf) x :=
  (inv_mk_eq_iff f hf _ _).2 (Or.inr (hf x).symm)

/-- A set with a fixed-point-free involution is a double cover of its quotient:
`X ≃ X/f × Bool`. -/
noncomputable def invEquiv (hne : ∀ x, f x ≠ x) : X ≃ Quotient (invSetoid f hf) × Bool := by
  classical
  refine Equiv.ofBijective
    (fun x => (Quotient.mk _ x, decide (x = (Quotient.mk (invSetoid f hf) x).out))) ⟨?_, ?_⟩
  · intro x y h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1] at h2
    generalize hr : (Quotient.mk (invSetoid f hf) y).out = r at h2
    have e : Quotient.mk (invSetoid f hf) r = Quotient.mk _ y := hr ▸ Quotient.out_eq _
    have hx := (inv_mk_eq_iff f hf r x).1 (e.trans h1.symm)
    have hy := (inv_mk_eq_iff f hf r y).1 e
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | rfl | simp [hne] at h2
  · rintro ⟨q, b⟩
    obtain ⟨r, rfl⟩ := Quotient.exists_rep q
    set r' := (Quotient.mk (invSetoid f hf) r).out
    have hr : Quotient.mk (invSetoid f hf) r' = Quotient.mk _ r := Quotient.out_eq _
    cases b
    · refine ⟨f r', ?_⟩
      simp only [inv_mk_f, hr, Prod.mk.injEq, true_and, decide_eq_false_iff_not]
      exact hne r'
    · refine ⟨r', ?_⟩
      simp [hr, r']

theorem card_eq_two_mul (hne : ∀ x, f x ≠ x) :
    Nat.card X = 2 * Nat.card (Quotient (invSetoid f hf)) := by
  rw [Nat.card_congr (invEquiv f hf hne), Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, mul_comm]

end Involution

/-- In a Latin square, a row is a bijection between the other two coordinates. -/
theorem row_bijective {Γ A B D : Type*} (f : Γ → A) (g : Γ → B) (h : Γ → D)
    (hfg : Bijective fun x => (f x, g x)) (hfh : Bijective fun x => (f x, h x)) (a : A) :
    Bijective fun b => h ((Equiv.ofBijective _ hfg).symm (a, b)) := by
  have key : ∀ b, f ((Equiv.ofBijective _ hfg).symm (a, b)) = a ∧
      g ((Equiv.ofBijective _ hfg).symm (a, b)) = b := fun b => by
    simpa only [Equiv.ofBijective_apply, Prod.mk.injEq] using
      (Equiv.ofBijective _ hfg).apply_symm_apply (a, b)
  refine ⟨fun b₁ b₂ e => ?_, fun d => ?_⟩
  · have hx : (Equiv.ofBijective _ hfg).symm (a, b₁) = (Equiv.ofBijective _ hfg).symm (a, b₂) :=
      hfh.1 (by simp only [Prod.mk.injEq]; exact ⟨(key b₁).1.trans (key b₂).1.symm, e⟩)
    rw [← (key b₁).2, ← (key b₂).2, hx]
  · obtain ⟨x, hx⟩ := hfh.2 (a, d)
    simp only [Prod.mk.injEq] at hx
    refine ⟨g x, ?_⟩
    have : (Equiv.ofBijective _ hfg).symm (a, g x) = x := by
      rw [Equiv.symm_apply_eq]; simp [hx.1]
    simp only [this, hx.2]

/-- A graph satisfying axioms 1 and 2, with a chosen triangle `t₀`. -/
structure Config (V : Type*) where
  G : SimpleGraph V
  t : Fin 3 → V
  ht : ∀ α β, α ≠ β → G.Adj (t α) (t β)
  ax1 : Axiom1 G
  ax2 : Axiom2 G

namespace Config

variable {V : Type*} (C : Config V)

theorem eq_of_adj {x y z w : V} (h : C.G.Adj x y) (hz : C.G.Adj x z) (hz' : C.G.Adj y z)
    (hw : C.G.Adj x w) (hw' : C.G.Adj y w) : z = w :=
  (C.ax1 x y h).unique ⟨hz, hz'⟩ ⟨hw, hw'⟩

theorem t_injective : Injective C.t := by
  intro α β h
  by_contra hne
  exact C.G.loopless.irrefl _ (h ▸ C.ht α β hne)

/-- A vertex off `t₀` is adjacent to at most one vertex of `t₀`. -/
theorem off_unique {s : V} (hs : s ∉ Set.range C.t) {α β : Fin 3}
    (ha : C.G.Adj s (C.t α)) (hb : C.G.Adj s (C.t β)) : α = β := by
  by_contra hne
  obtain ⟨h1, h2, -⟩ := third_spec α β hne
  have := C.eq_of_adj (C.ht α β hne) ha.symm hb.symm (C.ht α _ (Ne.symm h1))
    (C.ht β _ (Ne.symm h2))
  exact hs ⟨_, this.symm⟩

/-- Page 92, (1): a vertex off `t₀` is adjacent to a vertex of `t₀`. -/
theorem off_exists {s : V} (hs : s ∉ Set.range C.t) : ∃ α, C.G.Adj s (C.t α) := by
  have hne : ∀ α, s ≠ C.t α := fun α h => hs ⟨α, h.symm⟩
  rcases C.ax2 _ _ _ (C.ht 0 1 (by decide)) (C.ht 1 2 (by decide)) (C.ht 0 2 (by decide))
    s (hne 0) (hne 1) (hne 2) with h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

/-- `Ẽ_α`: the vertices off `t₀` adjacent to `t α`. -/
abbrev Et (α : Fin 3) : Type _ := {s : V // s ∉ Set.range C.t ∧ C.G.Adj s (C.t α)}

/-- The third vertex of the triangle on the vertical edge `{t α, s}`. -/
noncomputable def apex {α : Fin 3} (s : C.Et α) : V :=
  (C.ax1 _ _ s.2.2.symm).exists.choose

theorem apex_spec {α : Fin 3} (s : C.Et α) :
    C.G.Adj (C.t α) (C.apex s) ∧ C.G.Adj s.1 (C.apex s) :=
  (C.ax1 _ _ s.2.2.symm).exists.choose_spec

theorem apex_mem {α : Fin 3} (s : C.Et α) :
    C.apex s ∉ Set.range C.t ∧ C.G.Adj (C.apex s) (C.t α) := by
  refine ⟨?_, (C.apex_spec s).1.symm⟩
  rintro ⟨β, hβ⟩
  obtain ⟨h1, h2⟩ := C.apex_spec s
  rw [← hβ] at h1 h2
  exact h1.ne (congrArg C.t (C.off_unique s.2.1 s.2.2 h2))

/-- Page 93, Prop. 1: the involution `σ_α` of `Ẽ_α`. -/
noncomputable def sig {α : Fin 3} (s : C.Et α) : C.Et α := ⟨C.apex s, C.apex_mem s⟩

theorem adj_sig {α : Fin 3} (s : C.Et α) : C.G.Adj s.1 (C.sig s).1 := (C.apex_spec s).2

/-- The only vertex adjacent to `t α` and to `s ∈ Ẽ_α` is `σ_α s`. -/
theorem sig_unique {α : Fin 3} (s : C.Et α) {z : V} (h1 : C.G.Adj (C.t α) z)
    (h2 : C.G.Adj s.1 z) : z = (C.sig s).1 :=
  C.eq_of_adj s.2.2.symm h1 h2 (C.apex_spec s).1 (C.apex_spec s).2

theorem sig_sig {α : Fin 3} (s : C.Et α) : C.sig (C.sig s) = s :=
  Subtype.ext (C.sig_unique (C.sig s) s.2.2.symm (C.adj_sig s).symm).symm

theorem sig_ne {α : Fin 3} (s : C.Et α) : C.sig s ≠ s := fun h =>
  (C.adj_sig s).ne (congrArg Subtype.val h).symm

theorem et_disjoint {α β : Fin 3} (s : C.Et α) (u : C.Et β) (h : s.1 = u.1) : α = β :=
  C.off_unique s.2.1 s.2.2 (h ▸ u.2.2)

/-- Page 94, Prop. 2. -/
theorem prop2 {α β : Fin 3} (s : C.Et α) (u : C.Et β) :
    ¬ (C.G.Adj u.1 s.1 ∧ C.G.Adj u.1 (C.sig s).1) := by
  rintro ⟨h1, h2⟩
  have := C.eq_of_adj (C.adj_sig s) h1.symm h2.symm s.2.2 (C.apex_spec s).1.symm
  exact u.2.1 ⟨α, this.symm⟩

/-- Page 98, Prop. 5: a point of `Ẽ_β` is adjacent to `s` or to `σ_α s`. -/
theorem prop5 {α β : Fin 3} (hab : α ≠ β) (s : C.Et α) (u : C.Et β) :
    C.G.Adj u.1 s.1 ∨ C.G.Adj u.1 (C.sig s).1 := by
  have n1 : u.1 ≠ C.t α := fun h => u.2.1 ⟨α, h.symm⟩
  have n2 : u.1 ≠ s.1 := fun h => hab (C.et_disjoint s u h.symm)
  have n3 : u.1 ≠ (C.sig s).1 := fun h => hab (C.et_disjoint (C.sig s) u h.symm)
  rcases C.ax2 _ _ _ s.2.2.symm (C.adj_sig s) (C.apex_spec s).1 u.1 n1 n2 n3 with h | h | h
  exacts [absurd (C.off_unique u.2.1 u.2.2 h) (Ne.symm hab), Or.inl h, Or.inr h]

/-- Props 2 and 5: exactly one of `s, σ_α s` is adjacent to `u ∈ Ẽ_β`. -/
theorem adj_sig_iff {α β : Fin 3} (hab : α ≠ β) (s : C.Et α) (u : C.Et β) :
    C.G.Adj u.1 (C.sig s).1 ↔ ¬ C.G.Adj u.1 s.1 :=
  ⟨fun h h' => C.prop2 s u ⟨h', h⟩, fun h => (C.prop5 hab s u).resolve_left h⟩

/-- Page 98, first corollary: if `s, u` are adjacent, so are `σ s, σ u`. -/
theorem adj_sig_sig {α β : Fin 3} (hab : α ≠ β) {s : C.Et α} {u : C.Et β}
    (h : C.G.Adj s.1 u.1) : C.G.Adj (C.sig s).1 (C.sig u).1 := by
  have h1 : ¬ C.G.Adj (C.sig u).1 s.1 := by
    intro h'; exact C.prop2 u s ⟨h, h'.symm⟩
  exact ((C.adj_sig_iff hab s (C.sig u)).2 h1).symm

/-- Page 95, Prop. 3: the third vertex of a triangle on a transverse edge lies in
the third `Ẽ`. -/
theorem prop3 {α β : Fin 3} (hab : α ≠ β) (s : C.Et α) (u : C.Et β)
    (hsu : C.G.Adj s.1 u.1) {z : V} (hs : C.G.Adj s.1 z) (hu : C.G.Adj u.1 z) :
    z ∉ Set.range C.t ∧ C.G.Adj z (C.t (third α β)) := by
  obtain ⟨-, -, h3⟩ := third_spec α β hab
  have zoff : z ∉ Set.range C.t := by
    rintro ⟨δ, rfl⟩
    exact hab ((C.off_unique s.2.1 s.2.2 hs).trans (C.off_unique u.2.1 hu u.2.2))
  refine ⟨zoff, ?_⟩
  obtain ⟨δ, hδ⟩ := C.off_exists zoff
  rcases h3 δ with rfl | rfl | rfl
  · have hz : z = (C.sig s).1 := C.sig_unique s hδ.symm hs
    exact absurd ⟨hsu.symm, hz ▸ hu⟩ (C.prop2 s u)
  · have hz : z = (C.sig u).1 := C.sig_unique u hδ.symm hu
    exact absurd ⟨hsu, hz ▸ hs⟩ (C.prop2 u s)
  · exact hδ

/-! ## Upper triangles (pages 94–98) -/

/-- `Γ̃`: the upper triangles, as triples `x α ∈ Ẽ_α` that are pairwise adjacent. -/
abbrev UT : Type _ := {x : Fin 3 → V // (∀ α, x α ∉ Set.range C.t ∧ C.G.Adj (x α) (C.t α)) ∧
    ∀ α β, α ≠ β → C.G.Adj (x α) (x β)}

/-- The vertex of an upper triangle in `Ẽ_α`. -/
def pr (x : C.UT) (α : Fin 3) : C.Et α := ⟨x.1 α, x.2.1 α⟩

/-- Page 95, Props 3 and 4 (image): a transverse edge lies in an upper triangle. -/
theorem ut_exists {α β : Fin 3} (hab : α ≠ β) (s : C.Et α) (u : C.Et β)
    (hsu : C.G.Adj s.1 u.1) : ∃ x : C.UT, x.1 α = s.1 ∧ x.1 β = u.1 := by
  classical
  obtain ⟨z, hzs, hzu⟩ := (C.ax1 _ _ hsu).exists
  obtain ⟨zoff, hz⟩ := C.prop3 hab s u hsu hzs hzu
  obtain ⟨h1, h2, h3⟩ := third_spec α β hab
  let x : Fin 3 → V := fun δ => if δ = α then s.1 else if δ = β then u.1 else z
  have xa : x α = s.1 := by simp [x]
  have xb : x β = u.1 := by simp [x, Ne.symm hab]
  have xc : x (third α β) = z := by simp [x, h1, h2]
  refine ⟨⟨x, fun δ => ?_, fun δ ε hδε => ?_⟩, xa, xb⟩
  · rcases h3 δ with rfl | rfl | rfl
    · rw [xa]; exact s.2
    · rw [xb]; exact u.2
    · rw [xc]; exact ⟨zoff, hz⟩
  · rcases h3 δ with rfl | rfl | rfl <;> rcases h3 ε with rfl | rfl | rfl <;>
      simp only [xa, xb, xc] <;> first
        | exact absurd rfl hδε | exact hsu | exact hsu.symm | exact hzs | exact hzs.symm
        | exact hzu | exact hzu.symm

/-- Page 96, Prop. 4 (injectivity): an upper triangle is determined by two of its
vertices. -/
theorem ut_unique {α β : Fin 3} (hab : α ≠ β) {x y : C.UT} (ha : x.1 α = y.1 α)
    (hb : x.1 β = y.1 β) : x = y := by
  obtain ⟨h1, h2, h3⟩ := third_spec α β hab
  have hc : x.1 (third α β) = y.1 (third α β) := by
    refine C.eq_of_adj (x.2.2 α β hab) (x.2.2 _ _ (Ne.symm h1)) (x.2.2 _ _ (Ne.symm h2)) ?_ ?_
    · rw [ha]; exact y.2.2 _ _ (Ne.symm h1)
    · rw [hb]; exact y.2.2 _ _ (Ne.symm h2)
  apply Subtype.ext; funext δ
  rcases h3 δ with rfl | rfl | rfl
  exacts [ha, hb, hc]

/-- Page 98, second corollary: `Γ̃` is stable under `σ = ∏ σ_α`. -/
noncomputable def sigUT (x : C.UT) : C.UT :=
  ⟨fun α => (C.sig (C.pr x α)).1, fun α => (C.sig (C.pr x α)).2,
    fun α β h => C.adj_sig_sig h (x.2.2 α β h)⟩

theorem pr_sigUT (x : C.UT) (α : Fin 3) : C.pr (C.sigUT x) α = C.sig (C.pr x α) := rfl

theorem sigUT_sigUT (x : C.UT) : C.sigUT (C.sigUT x) = x :=
  Subtype.ext <| funext fun α => congrArg Subtype.val (C.sig_sig (C.pr x α))

theorem sigUT_ne (x : C.UT) : C.sigUT x ≠ x := fun h =>
  C.sig_ne (C.pr x 0) (by rw [← pr_sigUT, h])

/-- An upper triangle is determined by one vertex and the orbit of a second. -/
theorem ut_eq_of {α β : Fin 3} (hab : α ≠ β) {x y : C.UT} (ha : C.pr y α = C.pr x α)
    (hb : C.pr y β = C.pr x β ∨ C.pr y β = C.sig (C.pr x β)) : y = x := by
  rcases hb with hb | hb
  · exact C.ut_unique hab (congrArg Subtype.val ha) (congrArg Subtype.val hb)
  · exfalso
    have h := y.2.2 α β hab
    have e1 : y.1 α = x.1 α := congrArg Subtype.val ha
    have e2 : y.1 β = (C.sig (C.pr x β)).1 := congrArg Subtype.val hb
    rw [e1, e2] at h
    exact C.prop2 (C.pr x β) (C.pr x α) ⟨(x.2.2 α β hab), h⟩

/-! ## The Latin square and the double covers (pages 101–102) -/

/-- `E_α = Ẽ_α / σ_α`. -/
abbrev E (α : Fin 3) : Type _ := Quotient (invSetoid (C.sig (α := α)) C.sig_sig)

/-- `Γ = Γ̃ / σ`. -/
abbrev Gam : Type _ := Quotient (invSetoid C.sigUT C.sigUT_sigUT)

/-- The class of `s ∈ Ẽ_α` in `E_α`. -/
def mkE {α : Fin 3} (s : C.Et α) : C.E α := Quotient.mk _ s

/-- The class of `x ∈ Γ̃` in `Γ`. -/
def mkG (x : C.UT) : C.Gam := Quotient.mk _ x

/-- The three quotient maps `φ_α : Γ → E_α`. -/
def phi (α : Fin 3) : C.Gam → C.E α :=
  Quotient.lift (fun x => C.mkE (C.pr x α)) (by
    intro x y h
    rcases h with rfl | rfl
    · rfl
    · exact (inv_mk_f _ _ _).symm)

theorem phi_mkG (α : Fin 3) (x : C.UT) : C.phi α (C.mkG x) = C.mkE (C.pr x α) := rfl

/-- Page 102, axiom `β_Γ`: for `α ≠ β`, `Γ → E_α × E_β` is bijective. `Γ` is a
Latin square on the three `E_α`. -/
theorem latin {α β : Fin 3} (hab : α ≠ β) :
    Bijective fun g : C.Gam => (C.phi α g, C.phi β g) := by
  refine ⟨fun g h e => ?_, fun p => ?_⟩
  · induction g using Quotient.ind with | _ x => ?_
    induction h using Quotient.ind with | _ y => ?_
    simp only [Prod.mk.injEq] at e
    obtain ⟨ea, eb⟩ := e
    have ha := (inv_mk_eq_iff _ _ _ _).1 ea
    have hb := (inv_mk_eq_iff _ _ _ _).1 eb
    rcases ha with ha | ha
    · rw [C.ut_eq_of hab ha hb]
    · have hb' : C.pr (C.sigUT y) β = C.pr x β ∨
          C.pr (C.sigUT y) β = C.sig (C.pr x β) := by
        rw [pr_sigUT]
        rcases hb with hb | hb
        · right; rw [hb]
        · left; rw [hb, sig_sig]
      have := C.ut_eq_of hab (x := x) (y := C.sigUT y) (by rw [pr_sigUT, ha, sig_sig]) hb'
      rw [← this]
      exact inv_mk_f _ _ _
  · obtain ⟨e, f⟩ := p
    induction e using Quotient.ind with | _ s => ?_
    induction f using Quotient.ind with | _ u => ?_
    rcases C.prop5 hab s u with h | h
    · obtain ⟨x, xa, xb⟩ := C.ut_exists hab s u h.symm
      refine ⟨C.mkG x, ?_⟩
      have ha : C.pr x α = s := Subtype.ext xa
      have hb : C.pr x β = u := Subtype.ext xb
      simp only [phi_mkG, ha, hb]
      rfl
    · obtain ⟨x, xa, xb⟩ := C.ut_exists hab (C.sig s) u h.symm
      refine ⟨C.mkG x, ?_⟩
      have ha : C.pr x α = C.sig s := Subtype.ext xa
      have hb : C.pr x β = u := Subtype.ext xb
      simp only [phi_mkG, ha, hb, mkE, inv_mk_f]

/-- The pull-back of the double cover `Ẽ_α → E_α` along `φ_α : Γ → E_α`. -/
abbrev PB (α : Fin 3) : Type _ := {p : C.Gam × C.Et α // C.phi α p.1 = C.mkE p.2}

/-- Page 101: `Γ̃` is the pull-back of `Ẽ_α → E_α` along `Γ → E_α`, for each `α`. -/
noncomputable def pullback (α : Fin 3) : C.UT ≃ C.PB α :=
  Equiv.ofBijective (fun x => ⟨(C.mkG x, C.pr x α), rfl⟩) <| by
    refine ⟨fun x y e => ?_, fun ⟨⟨g, s⟩, h⟩ => ?_⟩
    · have e1 : C.mkG x = C.mkG y := congrArg (fun p : C.PB α => p.1.1) e
      have e2 : C.pr x α = C.pr y α := congrArg (fun p : C.PB α => p.1.2) e
      rcases (inv_mk_eq_iff _ _ x y).1 e1 with h | h
      · exact h.symm
      · exfalso; apply C.sig_ne (C.pr x α)
        rw [← pr_sigUT, ← h, e2]
    · obtain ⟨x, rfl⟩ := Quotient.exists_rep g
      rcases (inv_mk_eq_iff _ _ (C.pr x α) s).1 h with h' | h'
      · exact ⟨x, Subtype.ext (Prod.ext rfl h'.symm)⟩
      · exact ⟨C.sigUT x, Subtype.ext (Prod.ext (inv_mk_f _ _ _) ((C.pr_sigUT x α).trans h'.symm))⟩

/-- Page 102: the isomorphisms between the pull-backs of the three double covers. -/
noncomputable def transition (α β : Fin 3) : C.PB α ≃ C.PB β :=
  (C.pullback α).symm.trans (C.pullback β)

/-- They are isomorphisms over `Γ`. -/
theorem transition_over (α β : Fin 3) (p : C.PB α) : (C.transition α β p).1.1 = p.1.1 := by
  obtain ⟨x, rfl⟩ := (C.pullback α).surjective p
  simp only [transition, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- And they form a transitive system. -/
theorem transition_trans (α β γ : Fin 3) :
    (C.transition α β).trans (C.transition β γ) = C.transition α γ :=
  Equiv.ext fun p => by simp [transition]

theorem transition_self (α : Fin 3) : C.transition α α = Equiv.refl _ :=
  Equiv.ext fun p => by simp [transition]

/-! ## Counts (pages 99 and 104) -/

theorem card_Et (α : Fin 3) : Nat.card (C.Et α) = 2 * Nat.card (C.E α) :=
  card_eq_two_mul _ _ C.sig_ne

theorem card_UT : Nat.card C.UT = 2 * Nat.card C.Gam :=
  card_eq_two_mul _ _ C.sigUT_ne

theorem card_Gam {α β : Fin 3} (hab : α ≠ β) :
    Nat.card C.Gam = Nat.card (C.E α) * Nat.card (C.E β) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (C.latin hab)), Nat.card_prod]

/-- Page 99, corollary: if `Ẽ_α` is nonempty, `E_β` and `E_γ` are in bijection
(and so are `Ẽ_β` and `Ẽ_γ`). -/
theorem E_equiv {α β γ : Fin 3} (hab : α ≠ β) (hac : α ≠ γ) (s : C.Et α) :
    Nonempty (C.E β ≃ C.E γ) :=
  ⟨Equiv.ofBijective _ (row_bijective (C.phi α) (C.phi β) (C.phi γ) (C.latin hab)
    (C.latin hac) (C.mkE s))⟩

end Config

/-! ## The Scholie and its converse (pages 96–100) -/

universe u

theorem fin3_succ : ∀ δ : Fin 3, δ + 1 ≠ δ ∧ δ + 2 ≠ δ ∧ δ + 1 ≠ δ + 2 := by decide

/-- The points of `∐ Ẽ_α`. -/
abbrev Pt (X : Fin 3 → Type u) : Type u := Σ α, X α

/-- The data of the Scholie of page 96 on three sets `Ẽ_α = X α`: fixed-point-free
involutions `σ_α`, and a set `T ⊆ ∏ Ẽ_α` of triples (the upper triangles). -/
structure Scholie (X : Fin 3 → Type u) where
  σ : ∀ α, X α → X α
  σσ : ∀ α s, σ α (σ α s) = s
  σne : ∀ α s, σ α s ≠ s
  T : Set (∀ α, X α)

namespace Scholie

variable {X : Fin 3 → Type u} (D : Scholie X)

/-- The involution `σ` on `∐ Ẽ_α`. -/
def sg (p : Pt X) : Pt X := ⟨p.1, D.σ p.1 p.2⟩

/-- Two points of distinct `Ẽ`'s are linked when a triple of `T` contains both. -/
def Lk (p q : Pt X) : Prop := p.1 ≠ q.1 ∧ ∃ τ ∈ D.T, τ p.1 = p.2 ∧ τ q.1 = q.2

/-- Condition (*): the projections of `T` on two factors are injective. -/
def Star : Prop :=
  ∀ τ ∈ D.T, ∀ ρ ∈ D.T, ∀ α β, α ≠ β → τ α = ρ α → τ β = ρ β → τ = ρ

/-- Condition `β_Γ̃` (page 101, with Prop. 5 of page 98): of the two points of an
orbit of `σ_α`, exactly one is linked to a given point of `Ẽ_β`, `β ≠ α`. -/
def Beta : Prop := ∀ p q : Pt X, p.1 ≠ q.1 → (D.Lk (D.sg p) q ↔ ¬ D.Lk p q)

/-- Condition (***) = (Ka) of the margin of page 96, in the form used here: three
triples `τ, ρ₁, ρ₂ ∈ T` through the pairs `(s_α, s_β)`, `(s_α, s_γ)`, `(s_β, s_γ)`
of one family `(s_α, s_β, s_γ)` coincide. -/
def Ka : Prop :=
  ∀ α β γ : Fin 3, α ≠ β → α ≠ γ → β ≠ γ → ∀ τ ∈ D.T, ∀ ρ₁ ∈ D.T, ∀ ρ₂ ∈ D.T,
    τ α = ρ₁ α → τ β = ρ₂ β → ρ₁ γ = ρ₂ γ → τ = ρ₁

/-- (Ka) in the shape of the margin of page 96: a family `(s_α)` and triples
`(t_α)` of `T` with `s_β = φ_β(t_α)` for `α ≠ β`; the conclusion, illegible on
the leaf, is taken to be `(s_α) ∈ T`. -/
def KaPage : Prop :=
  ∀ (s : ∀ α, X α) (t : Fin 3 → ∀ α, X α), (∀ α, t α ∈ D.T) →
    (∀ α β, α ≠ β → t α β = s β) → s ∈ D.T

theorem Ka.star {D : Scholie X} (hK : D.Ka) : D.Star := by
  intro τ hτ ρ hρ α β hab e1 e2
  obtain ⟨n1, n2, -⟩ := third_spec α β hab
  exact hK α (third α β) β (Ne.symm n1) hab n2 τ hτ ρ hρ τ hτ e1 rfl e2.symm

theorem Ka.kaPage {D : Scholie X} (hK : D.Ka) : D.KaPage := by
  intro s t ht hs
  have e := hK 0 1 2 (by decide) (by decide) (by decide) (t 2) (ht 2) (t 1) (ht 1) (t 0) (ht 0)
    ((hs 2 0 (by decide)).trans (hs 1 0 (by decide)).symm)
    ((hs 2 1 (by decide)).trans (hs 0 1 (by decide)).symm)
    ((hs 1 2 (by decide)).trans (hs 0 2 (by decide)).symm)
  have : s = t 2 := by
    funext δ
    fin_cases δ
    exacts [(hs 2 0 (by decide)).symm, (hs 2 1 (by decide)).symm,
      by rw [e]; exact (hs 1 2 (by decide)).symm]
  rw [this]; exact ht 2

theorem ka_of_kaPage (hS : D.Star) (hP : D.KaPage) : D.Ka := by
  classical
  intro α β γ hab hac hbc τ hτ ρ₁ hρ₁ ρ₂ hρ₂ e1 e2 e3
  let s : ∀ δ, X δ := Function.update τ γ (ρ₁ γ)
  have sα : s α = τ α := Function.update_of_ne hac _ _
  have sβ : s β = τ β := Function.update_of_ne hbc _ _
  have sγ : s γ = ρ₁ γ := Function.update_self _ _ _
  let t : Fin 3 → ∀ δ, X δ := fun δ => if δ = γ then τ else if δ = β then ρ₁ else ρ₂
  have tγ : t γ = τ := by simp [t]
  have tβ : t β = ρ₁ := by simp [t, hbc]
  have tα : t α = ρ₂ := by simp [t, hac, hab]
  have ht : ∀ δ, t δ ∈ D.T := by
    intro δ
    rcases fin3_cases α β γ hab hac hbc δ with h | h | h <;> rw [h]
    · rw [tα]; exact hρ₂
    · rw [tβ]; exact hρ₁
    · rw [tγ]; exact hτ
  have hst : ∀ ε δ, ε ≠ δ → t ε δ = s δ := by
    intro ε δ hεδ
    rcases fin3_cases α β γ hab hac hbc ε with hε | hε | hε <;>
      rcases fin3_cases α β γ hab hac hbc δ with hδ | hδ | hδ
    all_goals first
      | exact absurd (hε.trans hδ.symm) hεδ
      | rw [hε, hδ]
    all_goals first
      | (rw [tα, sβ]; exact e2.symm)
      | (rw [tα, sγ]; exact e3.symm)
      | (rw [tβ, sα]; exact e1.symm)
      | (rw [tβ, sγ])
      | (rw [tγ, sα])
      | (rw [tγ, sβ])
  have hs : s ∈ D.T := hP s t ht hst
  have hsτ : s = τ := hS s hs τ hτ α β hab sα sβ
  have hγ : τ γ = ρ₁ γ := by rw [← hsτ]; exact sγ
  exact hS τ hτ ρ₁ hρ₁ α γ hac e1 hγ

/-- Under (*), the two forms of (Ka) agree; and (Ka) implies (*). -/
theorem ka_iff : D.Ka ↔ D.Star ∧ D.KaPage :=
  ⟨fun h => ⟨h.star, h.kaPage⟩, fun h => D.ka_of_kaPage h.1 h.2⟩

theorem sg_sg (p : Pt X) : D.sg (D.sg p) = p := by
  obtain ⟨α, s⟩ := p; simp [sg, D.σσ]

theorem sg_ne (p : Pt X) : D.sg p ≠ p := by
  obtain ⟨α, s⟩ := p
  intro h
  simp only [sg, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact D.σne α s h

theorem Lk_symm {p q : Pt X} (h : D.Lk p q) : D.Lk q p := by
  obtain ⟨hne, τ, hτ, h1, h2⟩ := h
  exact ⟨Ne.symm hne, τ, hτ, h2, h1⟩

theorem Lk_irrefl (p : Pt X) : ¬ D.Lk p p := fun h => h.1 rfl

/-- The vertex of a triple `τ` in `Ẽ_α`. -/
def vx (τ : ∀ α, X α) (α : Fin 3) : Pt X := ⟨α, τ α⟩

theorem eq_vx {τ : ∀ α, X α} {p : Pt X} (h : τ p.1 = p.2) : p = vx τ p.1 := by
  obtain ⟨α, s⟩ := p
  exact (congrArg (Sigma.mk α) h).symm

theorem Lk_vx {τ : ∀ α, X α} (hτ : τ ∈ D.T) {α β : Fin 3} (h : α ≠ β) :
    D.Lk (vx τ α) (vx τ β) := ⟨h, τ, hτ, rfl, rfl⟩

/-- Adjacency on `t₀ ⊔ ∐ Ẽ_α` (Scholie, 2°) α)–δ)). -/
def Adj : Fin 3 ⊕ Pt X → Fin 3 ⊕ Pt X → Prop
  | .inl α, .inl β => α ≠ β
  | .inl α, .inr p => p.1 = α
  | .inr p, .inl α => p.1 = α
  | .inr p, .inr q => q = D.sg p ∨ D.Lk p q

/-- The graph of the Scholie, on `t₀ ⊔ ∐ Ẽ_α`. -/
def graph : SimpleGraph (Fin 3 ⊕ Pt X) where
  Adj := D.Adj
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [Adj] at h ⊢
    · exact Ne.symm h
    · exact h
    · exact h
    · rcases h with rfl | h
      · exact Or.inl (D.sg_sg _).symm
      · exact Or.inr (D.Lk_symm h)⟩
  loopless := ⟨fun a h => by
    cases a <;> simp only [Adj] at h
    · exact h rfl
    · rcases h with h | h
      · exact D.sg_ne _ h.symm
      · exact D.Lk_irrefl _ h⟩

@[simp] theorem adj_inl_inl (α β : Fin 3) :
    D.graph.Adj (.inl α) (.inl β) ↔ α ≠ β := Iff.rfl
@[simp] theorem adj_inl_inr (α : Fin 3) (p : Pt X) :
    D.graph.Adj (.inl α) (.inr p) ↔ p.1 = α := Iff.rfl
@[simp] theorem adj_inr_inl (α : Fin 3) (p : Pt X) :
    D.graph.Adj (.inr p) (.inl α) ↔ p.1 = α := Iff.rfl
@[simp] theorem adj_inr_inr (p q : Pt X) :
    D.graph.Adj (.inr p) (.inr q) ↔ q = D.sg p ∨ D.Lk p q := Iff.rfl

/-- `t₀` is a triangle of the graph. -/
theorem base_triangle : ∀ α β : Fin 3, α ≠ β → D.graph.Adj (.inl α) (.inl β) :=
  fun _ _ h => h

/-- Under `β_Γ̃`, no point is adjacent to both points of an orbit of `σ`. -/
theorem not_adj_orbit (hB : D.Beta) (p r : Pt X)
    (h1 : D.graph.Adj (.inr p) (.inr r)) (h2 : D.graph.Adj (.inr (D.sg p)) (.inr r)) :
    False := by
  simp only [adj_inr_inr, D.sg_sg] at h1 h2
  rcases h1 with rfl | h1 <;> rcases h2 with h2 | h2
  · exact D.sg_ne p h2
  · exact D.Lk_irrefl _ h2
  · subst h2; exact D.Lk_irrefl _ h1
  · exact (hB p r h1.1).1 h2 h1

theorem same_fibre (p r : Pt X) (h : p.1 = r.1) (hadj : D.graph.Adj (.inr p) (.inr r)) :
    r = D.sg p := by
  rcases hadj with h' | h'
  · exact h'
  · exact absurd h h'.1

/-- Under `β_Γ̃` and (Ka), the apex of a transverse edge is the third vertex of
its triple. -/
theorem apex_transverse (hB : D.Beta) (hK : D.Ka) {τ : ∀ α, X α}
    (hτ : τ ∈ D.T) {α β : Fin 3} (hab : α ≠ β) {r : Pt X}
    (h1 : D.graph.Adj (.inr (vx τ α)) (.inr r)) (h2 : D.graph.Adj (.inr (vx τ β)) (.inr r)) :
    r = vx τ (third α β) := by
  obtain ⟨n1, n2, h3⟩ := third_spec α β hab
  have hl : D.Lk (vx τ α) (vx τ β) := D.Lk_vx hτ hab
  simp only [adj_inr_inr] at h1 h2
  rcases h1 with rfl | h1
  · rcases h2 with h2 | h2
    · exact absurd (congrArg Sigma.fst h2) hab
    · exact ((hB _ _ hab).1 (D.Lk_symm h2) hl).elim
  rcases h2 with rfl | h2
  · exact ((hB _ _ (Ne.symm hab)).1 (D.Lk_symm h1) (D.Lk_symm hl)).elim
  obtain ⟨e1, ρ₁, hρ₁, a1, b1⟩ := h1
  obtain ⟨e2, ρ₂, hρ₂, a2, b2⟩ := h2
  obtain ⟨γ, w⟩ := r
  have e1' : α ≠ γ := e1
  have e2' : β ≠ γ := e2
  have a1' : ρ₁ α = τ α := a1
  have b1' : ρ₁ γ = w := b1
  have a2' : ρ₂ β = τ β := a2
  have b2' : ρ₂ γ = w := b2
  have hγ : γ = third α β := by
    rcases h3 γ with h | h | h
    · exact absurd h.symm e1'
    · exact absurd h.symm e2'
    · exact h
  subst hγ
  have e := hK α β (third α β) hab (Ne.symm n1) (Ne.symm n2) τ hτ ρ₁ hρ₁ ρ₂ hρ₂ a1'.symm
    a2'.symm (b1'.trans b2'.symm)
  rw [← e] at b1'
  exact (congrArg (Sigma.mk (third α β)) b1').symm

/-- Page 97: under `β_Γ̃` and (Ka), the upper triangles of the graph are the
triples of `T`. -/
theorem upper_triangle (hB : D.Beta) (hK : D.Ka) {p q r : Pt X}
    (hpq : D.graph.Adj (.inr p) (.inr q)) (hqr : D.graph.Adj (.inr q) (.inr r))
    (hpr : D.graph.Adj (.inr p) (.inr r)) :
    ∃ τ ∈ D.T, p.1 ≠ q.1 ∧ p = vx τ p.1 ∧ q = vx τ q.1 ∧ r = vx τ (third p.1 q.1) := by
  rcases (D.adj_inr_inr p q).1 hpq with rfl | hl
  · exact (D.not_adj_orbit hB p r hpr hqr).elim
  obtain ⟨hne, τ, hτ, e1, e2⟩ := hl
  have hp := eq_vx e1
  have hq := eq_vx e2
  refine ⟨τ, hτ, hne, hp, hq, ?_⟩
  have hpr' : D.graph.Adj (.inr (vx τ p.1)) (.inr r) := by rw [← hp]; exact hpr
  have hqr' : D.graph.Adj (.inr (vx τ q.1)) (.inr r) := by rw [← hq]; exact hqr
  exact D.apex_transverse hB hK hτ hne hpr' hqr'

theorem ax1_inl_inr (α : Fin 3) (q : Pt X) (h : q.1 = α) :
    ∃! z, D.graph.Adj (.inl α) z ∧ D.graph.Adj (.inr q) z := by
  refine ⟨.inr (D.sg q), ⟨h, Or.inl rfl⟩, ?_⟩
  rintro (δ | r) ⟨h1, h2⟩
  · simp only [adj_inl_inl, adj_inr_inl] at h1 h2
    exact absurd (h.symm.trans h2) h1
  · simp only [adj_inl_inr, adj_inr_inr] at h1 h2
    rcases h2 with rfl | h2
    · rfl
    · exact absurd (h.trans h1.symm) h2.1

/-- Scholie, converse: under `β_Γ̃` and (Ka), the graph satisfies axiom 1. -/
theorem axiom1 (hB : D.Beta) (hK : D.Ka) : Axiom1 D.graph := by
  have symm1 : ∀ x y, (∃! z, D.graph.Adj x z ∧ D.graph.Adj y z) →
      ∃! z, D.graph.Adj y z ∧ D.graph.Adj x z :=
    fun x y h => by simpa only [and_comm] using h
  intro x y hxy
  rcases x with α | p <;> rcases y with β | q
  · obtain ⟨n1, n2, h3⟩ := third_spec α β hxy
    refine ⟨.inl (third α β), ⟨Ne.symm n1, Ne.symm n2⟩, ?_⟩
    rintro (δ | r) ⟨h1, h2⟩
    · simp only [adj_inl_inl] at h1 h2
      rcases h3 δ with rfl | rfl | rfl
      · exact absurd rfl h1
      · exact absurd rfl h2
      · rfl
    · simp only [adj_inl_inr] at h1 h2
      exact absurd (h1.symm.trans h2) hxy
  · exact D.ax1_inl_inr α q hxy
  · exact symm1 _ _ (D.ax1_inl_inr β p hxy)
  · simp only [adj_inr_inr] at hxy
    rcases hxy with rfl | hl
    · refine ⟨.inl p.1, ⟨rfl, rfl⟩, ?_⟩
      rintro (δ | r) ⟨h1, h2⟩
      · simp only [adj_inr_inl] at h1; rw [h1]
      · exact (D.not_adj_orbit hB p r h1 h2).elim
    · obtain ⟨α, s⟩ := p
      obtain ⟨β, u⟩ := q
      obtain ⟨hne, τ, hτ, e1, e2⟩ := hl
      have hne' : α ≠ β := hne
      have e1' : τ α = s := e1
      have e2' : τ β = u := e2
      subst e1' e2'
      obtain ⟨n1, n2, -⟩ := third_spec α β hne'
      refine ⟨.inr (vx τ (third α β)),
        ⟨Or.inr (D.Lk_vx hτ (Ne.symm n1)), Or.inr (D.Lk_vx hτ (Ne.symm n2))⟩, ?_⟩
      rintro (δ | r) ⟨h1, h2⟩
      · exact absurd ((show α = δ from h1).trans (show β = δ from h2).symm) hne'
      · rw [D.apex_transverse hB hK hτ hne' h1 h2]

theorem ax2_vertical (hB : D.Beta) (q : Pt X) (v : Fin 3 ⊕ Pt X) (h1 : v ≠ .inl q.1) :
    D.graph.Adj v (.inl q.1) ∨ D.graph.Adj v (.inr q) ∨ D.graph.Adj v (.inr (D.sg q)) := by
  rcases v with δ | w
  · exact Or.inl (fun h => h1 (by rw [h]))
  · by_cases hw : w.1 = q.1
    · exact Or.inl hw
    · by_cases hl : D.Lk q w
      · exact Or.inr (Or.inl (Or.inr (D.Lk_symm hl)))
      · exact Or.inr (Or.inr (Or.inr (D.Lk_symm ((hB q w (Ne.symm hw)).2 hl))))

/-- Page 100, Prop. 6: axiom 2 for an upper triangle. -/
theorem ax2_upper (hB : D.Beta) (hK : D.Ka) {τ : ∀ α, X α} (hτ : τ ∈ D.T)
    (v : Fin 3 ⊕ Pt X) : ∃ ε, D.graph.Adj v (.inr (vx τ ε)) := by
  rcases v with δ | ⟨δ, w⟩
  · exact ⟨δ, rfl⟩
  · by_cases hw' : w = D.σ δ (τ δ)
    · refine ⟨δ, Or.inl ?_⟩
      change (⟨δ, τ δ⟩ : Pt X) = ⟨δ, D.σ δ w⟩
      rw [hw', D.σσ]
    · by_contra hcon'
      have hcon := not_exists.mp hcon'
      obtain ⟨n1, n2, n3⟩ := fin3_succ δ
      have l1 : ¬ D.Lk ⟨δ, w⟩ (vx τ (δ + 1)) := fun h => hcon _ (Or.inr h)
      have l2 : ¬ D.Lk ⟨δ, w⟩ (vx τ (δ + 2)) := fun h => hcon _ (Or.inr h)
      obtain ⟨-, ρ₁, hρ₁, a1, b1⟩ := (hB ⟨δ, w⟩ (vx τ (δ + 1)) (Ne.symm n1)).2 l1
      obtain ⟨-, ρ₂, hρ₂, a2, b2⟩ := (hB ⟨δ, w⟩ (vx τ (δ + 2)) (Ne.symm n2)).2 l2
      have a1' : ρ₁ δ = D.σ δ w := a1
      have b1' : ρ₁ (δ + 1) = τ (δ + 1) := b1
      have a2' : ρ₂ δ = D.σ δ w := a2
      have b2' : ρ₂ (δ + 2) = τ (δ + 2) := b2
      have e := hK (δ + 1) (δ + 2) δ n3 n1 n2 τ hτ ρ₁ hρ₁ ρ₂ hρ₂ b1'.symm b2'.symm
        (a1'.trans a2'.symm)
      apply hw'
      rw [e, a1', D.σσ]

/-- Scholie, converse: under `β_Γ̃` and (Ka), the graph satisfies axiom 2. -/
theorem axiom2 (hB : D.Beta) (hK : D.Ka) : Axiom2 D.graph := by
  intro a b c hab hbc hac v va vb vc
  rcases a with α | p <;> rcases b with β | q <;> rcases c with γ | r
  · rcases v with δ | w
    · rcases fin3_cases α β γ hab hac hbc δ with rfl | rfl | rfl
      · exact absurd rfl va
      · exact absurd rfl vb
      · exact absurd rfl vc
    · rcases fin3_cases α β γ hab hac hbc w.1 with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact absurd ((show r.1 = α from hac).symm.trans (show r.1 = β from hbc)) hab
  · exact absurd ((show q.1 = α from hab).symm.trans (show q.1 = γ from hbc)) hac
  · obtain rfl := D.same_fibre q r ((show q.1 = α from hab).trans (show r.1 = α from hac).symm) hbc
    have hab' : q.1 = α := hab
    subst hab'
    exact D.ax2_vertical hB q v va
  · exact absurd ((show p.1 = β from hab).symm.trans (show p.1 = γ from hac)) hbc
  · obtain rfl := D.same_fibre p r ((show p.1 = β from hab).trans (show r.1 = β from hbc).symm) hac
    have hab' : p.1 = β := hab
    subst hab'
    rcases D.ax2_vertical hB p v vb with h | h | h
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
  · obtain rfl := D.same_fibre p q ((show p.1 = γ from hac).trans (show q.1 = γ from hbc).symm) hab
    have hac' : p.1 = γ := hac
    subst hac'
    rcases D.ax2_vertical hB p v vc with h | h | h
    exacts [Or.inr (Or.inr h), Or.inl h, Or.inr (Or.inl h)]
  · obtain ⟨τ, hτ, hne, hp, hq, hr⟩ := D.upper_triangle hB hK hab hbc hac
    obtain ⟨-, -, h3⟩ := third_spec p.1 q.1 hne
    obtain ⟨ε, hε⟩ := D.ax2_upper hB hK hτ v
    rcases h3 ε with rfl | rfl | rfl
    · rw [← hp] at hε; exact Or.inl hε
    · rw [← hq] at hε; exact Or.inr (Or.inl hε)
    · rw [← hr] at hε; exact Or.inr (Or.inr hε)

/-- Axiom 1 forces (Ka): in the graph of the Scholie, under (*). -/
theorem ka_of_axiom1 (hS : D.Star) (h1 : Axiom1 D.graph) : D.Ka := by
  intro α β γ hab hac hbc τ hτ ρ₁ hρ₁ ρ₂ hρ₂ e1 e2 e3
  have hadj : D.graph.Adj (.inr (vx τ α)) (.inr (vx τ β)) := Or.inr (D.Lk_vx hτ hab)
  have u1 : D.graph.Adj (.inr (vx τ α)) (.inr (vx τ γ)) := Or.inr (D.Lk_vx hτ hac)
  have u2 : D.graph.Adj (.inr (vx τ β)) (.inr (vx τ γ)) := Or.inr (D.Lk_vx hτ hbc)
  have w1 : D.graph.Adj (.inr (vx τ α)) (.inr (vx ρ₁ γ)) :=
    Or.inr ⟨hac, ρ₁, hρ₁, e1.symm, rfl⟩
  have w2 : D.graph.Adj (.inr (vx τ β)) (.inr (vx ρ₁ γ)) :=
    Or.inr ⟨hbc, ρ₂, hρ₂, e2.symm, e3.symm⟩
  have e := (h1 _ _ hadj).unique ⟨u1, u2⟩ ⟨w1, w2⟩
  exact hS τ hτ ρ₁ hρ₁ α γ hac e1
    (by simpa only [Sum.inr.injEq, vx, Sigma.mk.inj_iff, heq_eq_eq, true_and] using e)

/-- Under (*) and `β_Γ̃`, the graph satisfies axiom 1 if and only if (Ka) holds;
it then satisfies axiom 2. -/
theorem axiom1_iff_ka (hS : D.Star) (hB : D.Beta) : Axiom1 D.graph ↔ D.Ka :=
  ⟨D.ka_of_axiom1 hS, D.axiom1 hB⟩

theorem scholie_converse (hB : D.Beta) (hK : D.Ka) : Axiom1 D.graph ∧ Axiom2 D.graph :=
  ⟨D.axiom1 hB hK, D.axiom2 hB hK⟩

end Scholie

/-! ## Problems I and II (pages 101–103) -/

/-- The data of page 102 on three sets `Ẽ_α = X α`: a set `Γ` with three
quotients `φ_α : Γ → E_α`, double covers `p_α : Ẽ_α → E_α` whose fibres are the
orbits of `σ_α`, and a set `Γ̃` over `Γ` identified with the pull-back of each
`p_α` along `φ_α` (these identifications give the transitive system of
isomorphisms between the three pull-backs). The Latin property `β_Γ` is the field
`latin`. -/
structure LatinCover (X : Fin 3 → Type u) where
  Γ : Type u
  E : Fin 3 → Type u
  φ : ∀ α, Γ → E α
  latin : ∀ α β, α ≠ β → Bijective fun g => (φ α g, φ β g)
  σ : ∀ α, X α → X α
  σσ : ∀ α s, σ α (σ α s) = s
  σne : ∀ α s, σ α s ≠ s
  p : ∀ α, X α → E α
  fibre : ∀ α s s', p α s = p α s' ↔ s' = s ∨ s' = σ α s
  Γt : Type u
  q : Γt → Γ
  ψ : ∀ α, Γt → X α
  lies_over : ∀ α x, p α (ψ α x) = φ α (q x)
  pb_inj : ∀ α x y, q x = q y → ψ α x = ψ α y → x = y
  pb_surj : ∀ α g s, φ α g = p α s → ∃ x, q x = g ∧ ψ α x = s

namespace LatinCover

variable {X : Fin 3 → Type u} (L : LatinCover X)

/-- The Scholie data of a Latin square with its double covers: `T` is the image
of `Γ̃` in `∏ Ẽ_α`. -/
def toScholie : Scholie X where
  σ := L.σ
  σσ := L.σσ
  σne := L.σne
  T := Set.range fun x α => L.ψ α x

theorem q_eq {α β : Fin 3} (hab : α ≠ β) {x y : L.Γt} (h1 : L.ψ α x = L.ψ α y)
    (h2 : L.ψ β x = L.ψ β y) : L.q x = L.q y := by
  have e1 : L.φ α (L.q x) = L.φ α (L.q y) := by rw [← L.lies_over, ← L.lies_over, h1]
  have e2 : L.φ β (L.q x) = L.φ β (L.q y) := by rw [← L.lies_over, ← L.lies_over, h2]
  exact (L.latin α β hab).1 (Prod.ext e1 e2)

/-- Condition (*) holds for the data of a Latin square with double covers. -/
theorem star : L.toScholie.Star := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ α β hab e1 e2
  have e1' : L.ψ α x = L.ψ α y := e1
  have e2' : L.ψ β x = L.ψ β y := e2
  rw [L.pb_inj α x y (L.q_eq hab e1' e2') e1']

theorem lk_iff {α β : Fin 3} (s : X α) (u : X β) :
    L.toScholie.Lk ⟨α, s⟩ ⟨β, u⟩ ↔ α ≠ β ∧ ∃ x, L.ψ α x = s ∧ L.ψ β x = u := by
  constructor
  · rintro ⟨h, _, ⟨x, rfl⟩, h1, h2⟩; exact ⟨h, x, h1, h2⟩
  · rintro ⟨h, x, h1, h2⟩; exact ⟨h, _, ⟨x, rfl⟩, h1, h2⟩

/-- Page 102: `β_Γ` gives `β_Γ̃`. -/
theorem beta : L.toScholie.Beta := by
  rintro ⟨α, s⟩ ⟨β, u⟩ hab
  have hab' : α ≠ β := hab
  -- the point of `Γ̃` over the cell `(p_α s, p_β u)` with `ψ_β = u`
  have key : ∀ x y : L.Γt, L.ψ β x = u → L.ψ β y = u → L.p α (L.ψ α x) = L.p α s →
      L.p α (L.ψ α y) = L.p α s → x = y := by
    intro x y hx hy px py
    have e1 : L.φ α (L.q x) = L.φ α (L.q y) := by rw [← L.lies_over, ← L.lies_over, px, py]
    have e2 : L.φ β (L.q x) = L.φ β (L.q y) := by rw [← L.lies_over, ← L.lies_over, hx, hy]
    exact L.pb_inj β x y ((L.latin α β hab').1 (Prod.ext e1 e2)) (hx.trans hy.symm)
  change L.toScholie.Lk ⟨α, L.σ α s⟩ ⟨β, u⟩ ↔ ¬ L.toScholie.Lk ⟨α, s⟩ ⟨β, u⟩
  rw [L.lk_iff, L.lk_iff]
  constructor
  · rintro ⟨-, x, hx1, hx2⟩ ⟨-, y, hy1, hy2⟩
    have px : L.p α (L.ψ α x) = L.p α s := by
      rw [hx1]; exact ((L.fibre α s (L.σ α s)).2 (Or.inr rfl)).symm
    have py : L.p α (L.ψ α y) = L.p α s := by rw [hy1]
    have := key x y hx2 hy2 px py
    subst this
    exact L.σne α s (hx1.symm.trans hy1)
  · intro h
    obtain ⟨g, hg⟩ := (L.latin α β hab').2 (L.p α s, L.p β u)
    simp only [Prod.mk.injEq] at hg
    obtain ⟨x, hxg, hxu⟩ := L.pb_surj β g u hg.2
    have hpx : L.p α s = L.p α (L.ψ α x) := by rw [L.lies_over, hxg, hg.1]
    rcases (L.fibre α s _).1 hpx with h' | h'
    · exact absurd ⟨hab', x, h', hxu⟩ h
    · exact ⟨hab', x, h', hxu⟩

/-- Problems I and II, converse: a Latin square with three double covers and the
identifications of their pull-backs, subject to (Ka), gives a graph satisfying
axioms 1 and 2. -/
theorem converse (hK : L.toScholie.Ka) :
    Axiom1 L.toScholie.graph ∧ Axiom2 L.toScholie.graph :=
  L.toScholie.scholie_converse L.beta hK

/-- And (Ka) is necessary for axiom 1. -/
theorem axiom1_iff_ka : Axiom1 L.toScholie.graph ↔ L.toScholie.Ka :=
  L.toScholie.axiom1_iff_ka L.star L.beta

end LatinCover

/-! ## The forward direction, packaged, and the round trip -/

namespace Config

variable {V : Type*} (C : Config V)

/-- The Latin square, double covers and pull-back identifications of a graph. -/
def latinCover : LatinCover C.Et where
  Γ := C.Gam
  E := C.E
  φ := C.phi
  latin := fun _ _ h => C.latin h
  σ := fun _ => C.sig
  σσ := fun _ => C.sig_sig
  σne := fun _ => C.sig_ne
  p := fun _ => C.mkE
  fibre := fun _ s s' => inv_mk_eq_iff _ _ s s'
  Γt := C.UT
  q := C.mkG
  ψ := fun α x => C.pr x α
  lies_over := fun _ _ => rfl
  pb_inj := fun α x y h1 h2 => (C.pullback α).injective (Subtype.ext (Prod.ext h1 h2))
  pb_surj := fun α g s h => by
    obtain ⟨x, hx⟩ := (C.pullback α).surjective ⟨(g, s), h⟩
    exact ⟨x, congrArg (fun p : C.PB α => p.1.1) hx, congrArg (fun p : C.PB α => p.1.2) hx⟩

/-- The Scholie data of a graph. -/
abbrev scholie : Scholie C.Et := C.latinCover.toScholie

theorem scholie_lk {α β : Fin 3} (hab : α ≠ β) (s : C.Et α) (u : C.Et β) :
    C.scholie.Lk ⟨α, s⟩ ⟨β, u⟩ ↔ C.G.Adj s.1 u.1 := by
  rw [LatinCover.lk_iff]
  constructor
  · rintro ⟨-, x, h1, h2⟩
    have h1' : C.pr x α = s := h1
    have h2' : C.pr x β = u := h2
    rw [← h1', ← h2']
    exact x.2.2 α β hab
  · intro h
    obtain ⟨x, xa, xb⟩ := C.ut_exists hab s u h
    exact ⟨hab, x, Subtype.ext xa, Subtype.ext xb⟩

/-- The triples of a graph satisfy (Ka). -/
theorem scholie_ka : C.scholie.Ka := by
  rintro α β γ hab hac hbc _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ e1 e2 e3
  have h1 : x.1 α = y.1 α := congrArg Subtype.val e1
  have h2 : x.1 β = z.1 β := congrArg Subtype.val e2
  have h3 : y.1 γ = z.1 γ := congrArg Subtype.val e3
  have hc : x.1 γ = y.1 γ := by
    refine C.eq_of_adj (x.2.2 α β hab) (x.2.2 α γ hac) (x.2.2 β γ hbc) ?_ ?_
    · rw [h1]; exact y.2.2 α γ hac
    · rw [h2, h3]; exact z.2.2 β γ hbc
  rw [C.ut_unique hac h1 hc]

/-- Pages 96–102, forward: the data of a graph satisfy (*), `β_Γ̃` and (Ka). -/
theorem scholie_forward : C.scholie.Star ∧ C.scholie.Beta ∧ C.scholie.Ka :=
  ⟨C.latinCover.star, C.latinCover.beta, C.scholie_ka⟩

/-- The map `t₀ ⊔ ∐ Ẽ_α → S` of page 92, (1). -/
def toV : Fin 3 ⊕ Pt C.Et → V
  | .inl α => C.t α
  | .inr p => p.2.1

theorem toV_injective : Injective C.toV := by
  rintro (α | ⟨α, s⟩) (β | ⟨β, u⟩) h <;> simp only [toV] at h
  · rw [C.t_injective h]
  · exact (u.2.1 ⟨α, h⟩).elim
  · exact (s.2.1 ⟨β, h.symm⟩).elim
  · have hab : α = β := C.et_disjoint s u h
    subst hab
    rw [Subtype.ext h]

theorem toV_surjective : Surjective C.toV := by
  intro v
  by_cases hv : v ∈ Set.range C.t
  · obtain ⟨α, rfl⟩ := hv
    exact ⟨.inl α, rfl⟩
  · obtain ⟨α, hα⟩ := C.off_exists hv
    exact ⟨.inr ⟨α, ⟨v, hv, hα⟩⟩, rfl⟩

theorem toV_adj (a b : Fin 3 ⊕ Pt C.Et) :
    C.G.Adj (C.toV a) (C.toV b) ↔ C.scholie.graph.Adj a b := by
  rcases a with α | ⟨α, s⟩ <;> rcases b with β | ⟨β, u⟩
  · simp only [toV, Scholie.adj_inl_inl]
    exact ⟨fun h e => h.ne (congrArg C.t e), C.ht α β⟩
  · simp only [toV, Scholie.adj_inl_inr]
    exact ⟨fun h => C.off_unique u.2.1 u.2.2 h.symm, fun h => by subst h; exact u.2.2.symm⟩
  · simp only [toV, Scholie.adj_inr_inl]
    exact ⟨fun h => C.off_unique s.2.1 s.2.2 h, fun h => by subst h; exact s.2.2⟩
  · simp only [toV, Scholie.adj_inr_inr]
    by_cases hab : α = β
    · subst hab
      have hl : ¬ C.scholie.Lk ⟨α, s⟩ ⟨α, u⟩ := fun h => h.1 rfl
      simp only [hl, or_false]
      change _ ↔ (⟨α, u⟩ : Pt C.Et) = ⟨α, C.sig s⟩
      rw [Sigma.mk.inj_iff]
      simp only [heq_eq_eq, true_and]
      exact ⟨fun h => Subtype.ext (C.sig_unique s u.2.2.symm h),
        fun h => by rw [h]; exact C.adj_sig s⟩
    · have hs : ¬ (⟨β, u⟩ : Pt C.Et) = C.scholie.sg ⟨α, s⟩ :=
        fun h => hab (congrArg Sigma.fst h).symm
      simp only [hs, false_or]
      exact (C.scholie_lk hab s u).symm

/-- Page 96, Scholie: the graph is isomorphic to the graph built from its data. -/
def scholieIso : C.scholie.graph ≃g C.G :=
  { Equiv.ofBijective C.toV ⟨C.toV_injective, C.toV_surjective⟩ with
    map_rel_iff' := fun {a b} => C.toV_adj a b }

end Config

/-! ## (Ka) is needed: a Latin square of order 2 with trivial double covers -/

/-- `Ẽ_α = E_α × {0, 1}` with `E_α = ℤ/2`, both written with `Bool`. -/
abbrev X2 : Fin 3 → Type := fun _ => Bool × Bool

/-- The triples over the table `w = u + v` of `ℤ/2` (`xor` on `Bool`), on one
sheet `e`. -/
def tri (a : Bool × Bool × Bool) : Fin 3 → Bool × Bool :=
  ![(a.1, a.2.2), (a.2.1, a.2.2), (xor a.1 a.2.1, a.2.2)]

/-- The Scholie data: `σ` exchanges the sheets. -/
def ex : Scholie X2 where
  σ := fun _ s => (s.1, !s.2)
  σσ := by decide
  σne := by decide
  T := Set.range tri

theorem ex_star_aux : ∀ (a b : Bool × Bool × Bool) (α β : Fin 3), α ≠ β →
    tri a α = tri b α → tri a β = tri b β → a = b := by
  decide +kernel

theorem ex_beta_aux : ∀ (α β : Fin 3) (s u : Bool × Bool), α ≠ β →
    ((α ≠ β ∧ ∃ a, tri a α = (s.1, !s.2) ∧ tri a β = u) ↔
      ¬ (α ≠ β ∧ ∃ a, tri a α = s ∧ tri a β = u)) := by
  decide +kernel

theorem ex_lk {α β : Fin 3} (s u : Bool × Bool) :
    ex.Lk ⟨α, s⟩ ⟨β, u⟩ ↔ α ≠ β ∧ ∃ a, tri a α = s ∧ tri a β = u := by
  constructor
  · rintro ⟨h, _, ⟨a, rfl⟩, h1, h2⟩; exact ⟨h, a, h1, h2⟩
  · rintro ⟨h, a, h1, h2⟩; exact ⟨h, _, ⟨a, rfl⟩, h1, h2⟩

/-- The data of a Latin square of order 2 with trivial double covers satisfy (*)
and `β_Γ̃`, but not (Ka), and their graph violates axiom 1: the edge
`{(0,0) ∈ Ẽ_a, (0,0) ∈ Ẽ_b}` lies in the two triangles closed by `(0,0)` and by
`(1,0) ∈ Ẽ_c`. -/
theorem ka_needed : ex.Star ∧ ex.Beta ∧ ¬ ex.Ka ∧ ¬ Axiom1 ex.graph := by
  have hS : ex.Star := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ α β h h1 h2
    rw [ex_star_aux a b α β h h1 h2]
  have hB : ex.Beta := by
    rintro ⟨α, s⟩ ⟨β, u⟩ h
    change ex.Lk ⟨α, (s.1, !s.2)⟩ ⟨β, u⟩ ↔ ¬ ex.Lk ⟨α, s⟩ ⟨β, u⟩
    rw [ex_lk, ex_lk]
    exact ex_beta_aux α β s u h
  have hK : ¬ ex.Ka := by
    intro h
    have := h 0 1 2 (by decide) (by decide) (by decide) (tri (false, false, false)) ⟨_, rfl⟩
      (tri (false, true, false)) ⟨_, rfl⟩ (tri (true, false, false)) ⟨_, rfl⟩
      (by decide) (by decide) (by decide)
    exact absurd this (by decide)
  exact ⟨hS, hB, hK, fun h => hK (ex.ka_of_axiom1 hS h)⟩

/-! ## Page 116: the group is an elementary abelian 2-group -/

/-- If every element of `G` has order dividing 2, `G` is commutative (page 116). -/
theorem p116_comm {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) (g k : G) :
    g * k = k * g := by
  have hinv : ∀ g : G, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
  calc g * k = (g * k)⁻¹ := (hinv _).symm
    _ = k⁻¹ * g⁻¹ := mul_inv_rev g k
    _ = k * g := by rw [hinv, hinv]

/-- Page 116: on the relation `xyz = 1` of a group `G`, the maps
`φ_a : (x, y, z) ↦ (x, a⁻¹z⁻¹, a⁻¹y⁻¹)` all preserve the relation if and only if
every element of `G` has order dividing 2. -/
theorem p116 {G : Type*} [Group G] :
    (∀ a x y z : G, x * y * z = 1 → x * (a⁻¹ * z⁻¹) * (a⁻¹ * y⁻¹) = 1) ↔
      ∀ g : G, g * g = 1 := by
  constructor
  · intro h g
    simpa using h g⁻¹ 1 1 1 (by simp)
  · intro h a x y z hxyz
    have hinv : ∀ g : G, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
    have comm := p116_comm h
    rw [hinv, hinv, hinv]
    rw [show x * (a * z) * (a * y) = x * (a * (z * a) * y) by group, comm z a,
      show x * (a * (a * z) * y) = x * ((a * a) * z * y) by group, h a, one_mul, comm z y,
      ← mul_assoc, hxyz]


/-! ## The autotopisms of the Klein table

An autotopism of the Cayley table of an additive group `A` is a triple `(f, g, h)`
of permutations with `f x + g y = h (x + y)`. For the Klein group they number
`96 = 6 · 4 · 4`; this is the count behind the stabiliser of a triangle in the
graph of the 27 lines (folder 69: `96 · 2 · 6 = 1152`), whose lift is not
formalised here. -/

section Klein

variable {A : Type*} [AddCommGroup A]

/-- For an autotopism `(f, g, h)`, the normalised `x ↦ f x - f 0` is additive. -/
def normAdd (f g h : A ≃ A) (H : ∀ x y, f x + g y = h (x + y)) : A ≃+ A :=
  { f.trans (Equiv.subRight (f 0)) with
    map_add' := fun x y => by
      simp only [Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.subRight_apply]
      have a : f (x + y) = h (x + y) - g 0 := eq_sub_of_add_eq (by simpa using H (x + y) 0)
      have b : g y = h y - f 0 := eq_sub_of_add_eq' (by simpa using H 0 y)
      have c : f y = h y - g 0 := eq_sub_of_add_eq (by simpa using H y 0)
      rw [a, ← H x y, b, c]
      abel }

/-- Autotopisms of the table of a commutative group: `(f, g, h)` is one if and only if
`f`, `g`, `h` are a common additive automorphism `φ` followed by translations by
`c_f`, `c_g` and `c_f + c_g`. Setting `y = 0` and `x = 0` shows that the normalised
`f - f 0`, `g - g 0`, `h - f 0 - g 0` coincide; additivity follows. -/
theorem autotopism_iff (f g h : A ≃ A) :
    (∀ x y, f x + g y = h (x + y)) ↔ ∃ φ : A ≃+ A, ∃ cf cg : A,
      (∀ x, f x = φ x + cf) ∧ (∀ y, g y = φ y + cg) ∧ (∀ z, h z = φ z + cf + cg) := by
  constructor
  · intro H
    refine ⟨normAdd f g h H, f 0, g 0, fun x => ?_, fun y => ?_, fun z => ?_⟩
    · change f x = f x - f 0 + f 0
      abel
    · change g y = f y - f 0 + g 0
      have h1 : f 0 + g y = h y := by simpa using H 0 y
      have h2 : f y + g 0 = h y := by simpa using H y 0
      rw [eq_sub_of_add_eq' h1, ← h2]
      abel
    · change h z = f z - f 0 + f 0 + g 0
      rw [← show f z + g 0 = h z by simpa using H z 0]
      abel
  · rintro ⟨φ, cf, cg, hf, hg, hh⟩ x y
    rw [hf, hg, hh, map_add]
    abel

/-- The autotopisms of the table of `A`. -/
abbrev Autotopisms (A : Type*) [AddCommGroup A] : Type _ :=
  {t : Equiv.Perm A × Equiv.Perm A × Equiv.Perm A // ∀ x y, t.1 x + t.2.1 y = t.2.2 (x + y)}

/-- The autotopisms of `A` are parametrised by `(φ, c_f, c_g)`. -/
def autotopismEquiv (A : Type*) [AddCommGroup A] : (A ≃+ A) × A × A ≃ Autotopisms A where
  toFun p := ⟨(p.1.toEquiv.trans (Equiv.addRight p.2.1),
      p.1.toEquiv.trans (Equiv.addRight p.2.2),
      p.1.toEquiv.trans (Equiv.addRight (p.2.1 + p.2.2))), fun x y => by
    simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      Equiv.coe_addRight, map_add]
    abel⟩
  invFun t := (normAdd t.1.1 t.1.2.1 t.1.2.2 t.2, t.1.1 0, t.1.2.1 0)
  left_inv p := by
    obtain ⟨φ, a, b⟩ := p
    refine Prod.ext (AddEquiv.ext fun x => ?_) (Prod.ext ?_ ?_) <;> simp [normAdd]
  right_inv t := by
    obtain ⟨⟨f, g, h⟩, H⟩ := t
    have hg : ∀ y, f y - f 0 + g 0 = g y := fun y => by
      have h1 : f 0 + g y = h y := by simpa using H 0 y
      have h2 : f y + g 0 = h y := by simpa using H y 0
      rw [eq_sub_of_add_eq' h1, ← h2]
      abel
    have hh : ∀ z, f z - f 0 + (f 0 + g 0) = h z := fun z => by
      rw [← show f z + g 0 = h z by simpa using H z 0]
      abel
    refine Subtype.ext (Prod.ext (Equiv.ext fun x => ?_) (Prod.ext (Equiv.ext fun y => ?_)
      (Equiv.ext fun z => ?_)))
    · change f x - f 0 + f 0 = f x
      abel
    · exact hg y
    · exact hh z

/-- The Klein group. -/
abbrev Klein : Type := ZMod 2 × ZMod 2

/-- The characterisation for the Klein group. -/
theorem klein_autotopism_iff (f g h : Klein ≃ Klein) :
    (∀ x y, f x + g y = h (x + y)) ↔ ∃ φ : Klein ≃+ Klein, ∃ cf cg : Klein,
      (∀ x, f x = φ x + cf) ∧ (∀ y, g y = φ y + cg) ∧ (∀ z, h z = φ z + cf + cg) :=
  autotopism_iff f g h

/-- Additive automorphisms as additive permutations. -/
def kleinAddEquiv :
    (Klein ≃+ Klein) ≃ {e : Equiv.Perm Klein // ∀ x y, e (x + y) = e x + e y} where
  toFun φ := ⟨φ.toEquiv, φ.map_add⟩
  invFun e := { e.1 with map_add' := e.2 }
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Klein ≃+ Klein) := Fintype.ofEquiv _ kleinAddEquiv.symm

/-- The Klein group has six additive automorphisms (`GL₂(𝔽₂) ≅ S₃`). -/
theorem card_klein_addAut : Fintype.card (Klein ≃+ Klein) = 6 := by
  rw [Fintype.card_congr kleinAddEquiv]
  decide +kernel

/-- The Cayley table of the Klein group has `96 = 6 · 4 · 4` autotopisms. -/
theorem card_klein_autotopisms : Fintype.card (Autotopisms Klein) = 96 := by
  rw [← Fintype.card_congr (autotopismEquiv Klein), Fintype.card_prod, Fintype.card_prod,
    card_klein_addAut]
  rfl

/-- The same count by enumeration of the `24³` triples of permutations. -/
theorem card_klein_autotopisms_decide :
    (Finset.univ.filter fun t : Equiv.Perm Klein × Equiv.Perm Klein × Equiv.Perm Klein =>
      ∀ x y, t.1 x + t.2.1 y = t.2.2 (x + y)).card = 96 := by
  decide +kernel

end Klein

end

end Grothendieck.Folder74
