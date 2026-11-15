module

public import Mathlib
public import Mathlib.Order.Lattice
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.Basic

@[expose] public section


/-!
# Folder 156-9, pages 107–110: transposes, the orthomodular law, and two finite spatios

The modernised reading `transcripts/156-9/156-9.modern.tex` (chapter IX of *Vers une géométrie
des formes*, July 1986) calls a *spatios* a complete lattice `Σ` with an order-reversing
involution `∁`; two elements are *disjoint*, `x |o| y`, when `x ≤ ∁ y`. A *disposition* is a set
`E` with a symmetric relation `|o|`, and its supports — the parts equal to the orthogonal of their
orthogonal — form a spatios (page 79). A map `α : Σ → Σ'` has a *transpose* `β : Σ' → Σ` when
`α x |o| y ↔ x |o| β y` for all `x, y`.

Page 107 asks:

> Si α_* et β_* commutent à ∁ (…), [est-ce] un iso. de spatios, inverses l'un de l'autre ?

Page 108 states Lemme 1: for `b ≤ c`, some `b*` disjoint from `b` has `b ∨ b* = c` iff
`b ∨ (∁ b ∧ c) = c`, and `∁ b ∧ c` is the largest such `b*`. The corollary of page 108 asks this
for every pair `b ≤ c` — the orthomodular law — and page 110 asks whether it always holds
(« J'en doute fort ! »), whether it holds when `Σ` is finite (« J'en doute également »), and
whether, when it holds, `Σ` must be a Boolean algebra.

Proved here:

* `lemme1`, `lemme1_max`: Lemme 1 of page 108, in any lattice with an antitone map `∁`.
* `transpose_inverse`: the answer to the question of page 107 is yes. If `β` is a transpose of
  `α` and both commute with `∁`, then `α ∘ β = id` and `β ∘ α = id`. Only the order and an
  order-reversing involution on each side are used.
* `O6`: the disposition on four points `0 - 1 - 2 - 3` (a path, `x |o| y` iff `x, y` are
  neighbours). `o6_supports`: its supports are `∅, {1}, {2}, {0, 2}, {1, 3}, E` (the hexagon);
  `o6_spatios`: the orthogonal is an involution on them, reverses inclusion, and `S ∩ S^⊥ = ∅`;
  `o6_not_orthomodular`: `{1} ⊆ {1, 3}` and `{1} ∨ ({1}^⊥ ∧ {1, 3}) = {1}`.
* `MO2`: the disposition on four points where `0 |o| 1` and `2 |o| 3` only. `mo2_supports`:
  its supports are `∅, {0}, {1}, {2}, {3}, E`; `mo2_spatios` as above; `mo2_orthomodular`: the
  orthomodular law holds for every pair of supports; `mo2_not_distrib`:
  `{0} ∧ ({2} ∨ {3}) = {0}` while `({0} ∧ {2}) ∨ ({0} ∧ {3}) = ∅`.

**What the formalisation finds.** Both doubts of page 110 are right, and the third question has
a negative answer: a spatios with six elements, the spatios of a four-point disposition, is not
orthomodular, and another, also of a four-point disposition, is orthomodular without being
distributive, hence without being a Boolean algebra. The non-orthomodular one is the hexagon
already met in folder 156-4 (`Grothendieck.Folder156_4.hexagon_saturated`): the path `a - b - c - d`
of that model's disjoint pairs is the disposition `O6` here. The answer to page 107 is the
edition's; it needs neither the Sup nor any Boolean hypothesis.
-/

namespace Grothendieck.Folder156_9

section Lemme1

variable {S : Type*} [Lattice S] (cpl : S → S)

/-- Disjunction in a spatios: `x |o| y` when `x ≤ ∁ y`. -/
def Disj (x y : S) : Prop := x ≤ cpl y

/-- **Lemme 1 (page 108).** For `b ≤ c`, there is `b*` disjoint from `b` with `b ∨ b* = c` if and
only if `b ∨ (∁ b ∧ c) = c`. -/
theorem lemme1 {b c : S} (hbc : b ≤ c) :
    (∃ e, Disj cpl e b ∧ b ⊔ e = c) ↔ b ⊔ (cpl b ⊓ c) = c := by
  constructor
  · rintro ⟨e, he, rfl⟩
    refine le_antisymm (sup_le le_sup_left inf_le_right) (sup_le_sup_left ?_ b)
    exact le_inf he le_sup_right
  · intro h
    exact ⟨cpl b ⊓ c, inf_le_left, h⟩

/-- **Lemme 1, end (page 108).** Every such `b*` lies under `b*₀ = ∁ b ∧ c`. -/
theorem lemme1_max {b c e : S} (he : Disj cpl e b) (hc : b ⊔ e = c) : e ≤ cpl b ⊓ c :=
  le_inf he (hc ▸ le_sup_right)

end Lemme1

section Transpose

variable {S S' : Type*} [PartialOrder S] [PartialOrder S'] {cpl : S → S} {cpl' : S' → S'}

/-- **Page 107, the question answered.** Let `∁, ∁'` be order-reversing involutions, and `β` a
transpose of `α`: `α x ≤ ∁' y ↔ x ≤ ∁ (β y)`. If `α` and `β` both commute with the
complements, they are inverse to each other. -/
theorem transpose_inverse (hcc : ∀ x, cpl (cpl x) = x) (hcc' : ∀ y, cpl' (cpl' y) = y)
    (hanti : ∀ {x y}, x ≤ y → cpl y ≤ cpl x) (hanti' : ∀ {x y}, x ≤ y → cpl' y ≤ cpl' x)
    {α : S → S'} {β : S' → S} (htr : ∀ x y, α x ≤ cpl' y ↔ x ≤ cpl (β y))
    (hα : ∀ x, α (cpl x) = cpl' (α x)) (hβ : ∀ y, β (cpl' y) = cpl (β y)) :
    (∀ y, α (β y) = y) ∧ ∀ x, β (α x) = x := by
  -- `α` is left adjoint to `β`.
  have gc : ∀ x y, α x ≤ y ↔ x ≤ β y := fun x y => by
    have := htr x (cpl' y)
    rwa [hcc', hβ, hcc] at this
  -- reversing the order through the involutions
  have rev : ∀ {x y : S'}, cpl' x ≤ cpl' y → y ≤ x := fun h => by
    simpa [hcc'] using hanti' h
  have rev' : ∀ {x y : S}, cpl x ≤ cpl y → y ≤ x := fun h => by
    simpa [hcc] using hanti h
  refine ⟨fun y => le_antisymm ((gc _ _).2 le_rfl) ?_, fun x => le_antisymm ?_ ((gc _ _).1 le_rfl)⟩
  · have h := (gc (β (cpl' y)) (cpl' y)).2 le_rfl
    rw [hβ, hα] at h
    exact rev h
  · have h := (gc (cpl x) (α (cpl x))).1 le_rfl
    rw [hα, hβ] at h
    exact rev' h

end Transpose

section Finite

/-- The orthogonal of a part of a disposition on four points. -/
def perp (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] (A : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter fun x => ∀ y ∈ A, r x y

/-- The support of a part: the orthogonal of its orthogonal. -/
def supp (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] (A : Finset (Fin 4)) : Finset (Fin 4) :=
  perp r (perp r A)

/-- The spatios structure on the supports: the orthogonal of a support is a support, is an
involution on supports, reverses inclusion, and meets it in `∅`. -/
def IsSpatios (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] : Prop :=
  ∀ A B : Finset (Fin 4), supp r A = A → supp r B = B →
    supp r (perp r A) = perp r A ∧ perp r (perp r A) = A ∧
      (A ⊆ B → perp r B ⊆ perp r A) ∧ A ∩ perp r A = ∅

/-- The orthomodular law on the supports, join being the support of the union:
`b ⊆ c → b ∨ (b^⊥ ∧ c) = c`. -/
def IsOrthomodular (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] : Prop :=
  ∀ b c : Finset (Fin 4), supp r b = b → supp r c = c → b ⊆ c →
    supp r (b ∪ (perp r b ∩ c)) = c

instance (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] : Decidable (IsSpatios r) :=
  inferInstanceAs (Decidable (∀ _ _, _))

instance (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] : Decidable (IsOrthomodular r) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- The hexagon's disposition: the path `0 - 1 - 2 - 3`. -/
def O6 (x y : Fin 4) : Prop := x.val + 1 = y.val ∨ y.val + 1 = x.val

/-- The disposition of `MO2`: `0 |o| 1` and `2 |o| 3`, and nothing else. -/
def MO2 (x y : Fin 4) : Prop := x.val / 2 = y.val / 2 ∧ x ≠ y

instance : DecidableRel O6 := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel MO2 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The supports of `O6` are `∅, {1}, {2}, {0, 2}, {1, 3}, E`: six elements, the hexagon. -/
theorem o6_supports :
    Finset.univ.filter (fun A : Finset (Fin 4) => supp O6 A = A) =
      {∅, {1}, {2}, {0, 2}, {1, 3}, Finset.univ} := by
  decide

theorem o6_spatios : IsSpatios O6 := by decide

/-- **The hexagon is not orthomodular**: `{1} ⊆ {1, 3}`, but `{1}^⊥ ∩ {1, 3} = ∅`, so
`{1} ∨ ({1}^⊥ ∧ {1, 3}) = {1}`. -/
theorem o6_not_orthomodular :
    ({1} : Finset (Fin 4)) ⊆ {1, 3} ∧ supp O6 {1} = {1} ∧ supp O6 {1, 3} = {1, 3} ∧
      supp O6 ({1} ∪ (perp O6 {1} ∩ {1, 3})) = {1} ∧ ¬ IsOrthomodular O6 := by
  decide

/-- The supports of `MO2` are `∅, {0}, {1}, {2}, {3}, E`. -/
theorem mo2_supports :
    Finset.univ.filter (fun A : Finset (Fin 4) => supp MO2 A = A) =
      {∅, {0}, {1}, {2}, {3}, Finset.univ} := by
  decide

theorem mo2_spatios : IsSpatios MO2 := by decide

/-- **`MO2` is orthomodular.** -/
theorem mo2_orthomodular : IsOrthomodular MO2 := by decide

/-- **`MO2` is not distributive, hence not a Boolean algebra**: `{0} ∧ ({2} ∨ {3}) = {0}`,
while `({0} ∧ {2}) ∨ ({0} ∧ {3}) = ∅`. -/
theorem mo2_not_distrib :
    ({0} : Finset (Fin 4)) ∩ supp MO2 ({2} ∪ {3}) = {0} ∧
      supp MO2 (({0} : Finset (Fin 4)) ∩ {2} ∪ {0} ∩ {3}) = ∅ := by
  decide

end Finite

end Grothendieck.Folder156_9
