module

public import Mathlib

@[expose] public section


/-!
# Folder 156-3, betweenness read on the cuts of a tronçon (pages 11–15)

The modernised reading `transcripts/156-3/156-3.modern.tex` (chapter III of
*Vers une géométrie des formes*, « Réseaux via découpages ») defines on page 8 a
*tronçon ordonné*: a poset, locally directed downwards (a) and upwards (a′),
directed both ways (b), dense (c), with more than one element (d). The
0-spheres are the comparable pairs `ε = {a, b}`, `a < b`; the moderate
complement `C(ε)` is the set of elements comparable to both and distinct from
both, and its pieces are `L_{<a}`, `]a, b[`, `L_{>b}` (pages 8 and 14).

The finding `156-3-betweenness-from-cuts` (`src/content/findings.ts`) states
that comparability together with, for each comparable pair, the unlabelled
partition of `C(ε)` into its pieces determines the strict betweenness relation,
hence the order up to reversal: in a 3-chain `J`, the middle element is the
unique one for which the pieces of `C(ε)` and `C(ε′)` containing the third
element, `ε, ε′` the two pairs through it, are disjoint. Proved here:

* `piece_above`, `piece_below`, `piece_between` — the three pieces computed on
  page 15 (`X_{a,b} = L_{>b}`, `X_{b,c} = L_{<b}`, `X_{c,a} = ]a, c[`);
* `middle_iff` — page 15: in a 3-chain, `q` is strictly between `p` and `r`
  iff the two pieces attached to the pairs through `q` are disjoint;
* `btw_transport` — hence a bijection preserving comparability and the
  partitions preserves strict betweenness;
* `le_iff_readLe`, `order_eq_or_dual` — pages 11–13: on a poset directed both
  ways, strict betweenness and comparability determine the order up to
  reversal;
* `order_of_cuts` — the finding's statement for tronçons: a bijection between
  tronçons preserving comparability and the partitions of the `C(ε)` is an
  order isomorphism or an order anti-isomorphism;
* `cmp_alone_insufficient` — comparability alone does not suffice, already on
  the tronçon `ℚ`;
* `btwLe_iff`, `btwLe_reading_fails` — the non-strict betweenness of page 11.

What the proof makes plain. Only density (c) and directedness (b) are used:
the local conditions a), a′) and d) play no part. Density serves twice — to
make the two other intersections non-empty on page 15 — and directedness only
in the lemma of pages 11–13. The non-strict relation `R̄(a, b, c)` is
`R(a, b, c)` or (`b ∈ {a, c}` and `a, c` comparable): the reading's « `R(a, b, c)`
or `b ∈ {a, c}` » fails for `a, c` incomparable, which the lemma never meets
since it is applied with `x < y`. What this certifies is that the reading holds
together, not that it is what the page says (issue #26), and not that the
statement is new: the finding stays open as a literature question.
-/

namespace Grothendieck.Folder156_3

open Set

section Defs

variable {α : Type*} [PartialOrder α]

/-- `x` and `y` are comparable. -/
def Cmp (x y : α) : Prop := x ≤ y ∨ y ≤ x

/-- Strict betweenness `𝓡(a, b, c)`: `a < b < c` or `a > b > c` (page 11). -/
def Btw (a b c : α) : Prop := (a < b ∧ b < c) ∨ (c < b ∧ b < a)

/-- Non-strict betweenness `𝓡̄(a, b, c)`: `a ≤ b ≤ c` or `a ≥ b ≥ c` (page 11). -/
def BtwLe (a b c : α) : Prop := (a ≤ b ∧ b ≤ c) ∨ (c ≤ b ∧ b ≤ a)

/-- `t ∈ C({a, b})`: `t ∉ {a, b}` and `{a, b, t}` is a chain (page 14). -/
def InC (a b t : α) : Prop := t ≠ a ∧ t ≠ b ∧ Cmp t a ∧ Cmp t b

/-- `s` and `t` lie in the same piece of `C({a, b})`: both below `a` and `b`,
both strictly between them, or both above them (pages 8 and 14). The relation
is symmetric in `a, b`, so it depends only on the pair. -/
def SamePiece (a b s t : α) : Prop :=
  (s < a ∧ s < b ∧ t < a ∧ t < b) ∨ (Btw a s b ∧ Btw a t b) ∨ (a < s ∧ b < s ∧ a < t ∧ b < t)

/-- `X_ε`, for `ε = {a, b}`: the piece of `C(ε)` containing `t` (page 15). -/
def piece (a b t : α) : Set α := {s | InC a b s ∧ SamePiece a b s t}

/-- A tronçon ordonné (page 8). -/
structure Troncon (α : Type*) [PartialOrder α] : Prop where
  /-- a) `L_{>a}` is directed downwards. -/
  dir_down : ∀ a x y : α, a < x → a < y → ∃ z, a < z ∧ z ≤ x ∧ z ≤ y
  /-- a′) `L_{<a}` is directed upwards. -/
  dir_up : ∀ a x y : α, x < a → y < a → ∃ z, x ≤ z ∧ y ≤ z ∧ z < a
  /-- b) `L` is directed downwards … -/
  low : ∀ x y : α, ∃ z, z ≤ x ∧ z ≤ y
  /-- … and upwards. -/
  high : ∀ x y : α, ∃ z, x ≤ z ∧ y ≤ z
  /-- c) `L` is dense (« divisible »). -/
  dense : ∀ x y : α, x < y → ∃ z, x < z ∧ z < y
  /-- d) `card L > 1`. -/
  card : ∃ x y : α, x ≠ y

end Defs

section Pieces

variable {α : Type*} [PartialOrder α] {a b s t : α}

theorem btw_comm : Btw a s b ↔ Btw b s a := by
  unfold Btw; exact or_comm

theorem samePiece_comm : SamePiece a b s t ↔ SamePiece b a s t := by
  unfold SamePiece
  rw [btw_comm (a := a) (s := s) (b := b), btw_comm (a := a) (s := t) (b := b)]
  tauto

theorem piece_comm (a b t : α) : piece a b t = piece b a t := by
  ext s
  simp only [piece, InC, mem_ofPred_eq]
  rw [samePiece_comm]
  tauto

/-- Page 15: for `a < b < t`, the piece of `C({a, b})` containing `t` is `L_{>b}`. -/
theorem piece_above (hab : a < b) (hbt : b < t) : piece a b t = {s | b < s} := by
  ext s
  constructor
  · rintro ⟨-, h | h | h⟩
    · exact absurd h.2.2.1 (lt_asymm (hab.trans hbt))
    · rcases h.2 with ⟨-, htb⟩ | ⟨-, hta⟩
      · exact absurd htb (lt_asymm hbt)
      · exact absurd hta (lt_asymm (hab.trans hbt))
    · exact h.2.1
  · intro hs
    have hs : b < s := hs
    exact ⟨⟨(hab.trans hs).ne', hs.ne', Or.inr (hab.trans hs).le, Or.inr hs.le⟩,
      Or.inr (Or.inr ⟨hab.trans hs, hs, hab.trans hbt, hbt⟩)⟩

/-- Page 15: for `t < a < b`, the piece of `C({a, b})` containing `t` is `L_{<a}`. -/
theorem piece_below (hab : a < b) (hta : t < a) : piece a b t = {s | s < a} := by
  ext s
  constructor
  · rintro ⟨-, h | h | h⟩
    · exact h.1
    · rcases h.2 with ⟨hat, -⟩ | ⟨hbt, -⟩
      · exact absurd hat (lt_asymm hta)
      · exact absurd hbt (lt_asymm (hta.trans hab))
    · exact absurd h.2.2.1 (lt_asymm hta)
  · intro hs
    have hs : s < a := hs
    exact ⟨⟨hs.ne, (hs.trans hab).ne, Or.inl hs.le, Or.inl (hs.trans hab).le⟩,
      Or.inl ⟨hs, hs.trans hab, hta, hta.trans hab⟩⟩

/-- Page 15: for `a < t < b`, the piece of `C({a, b})` containing `t` is `]a, b[`. -/
theorem piece_between (hat : a < t) (htb : t < b) : piece a b t = Ioo a b := by
  ext s
  constructor
  · rintro ⟨-, h | h | h⟩
    · exact absurd h.2.2.1 (lt_asymm hat)
    · rcases h.1 with h1 | ⟨hbs, hsa⟩
      · exact h1
      · exact absurd (hbs.trans hsa) (lt_asymm (hat.trans htb))
    · exact absurd h.2.2.2 (lt_asymm htb)
  · rintro ⟨has, hsb⟩
    exact ⟨⟨has.ne', hsb.ne, Or.inr has.le, Or.inl hsb.le⟩,
      Or.inr (Or.inl ⟨Or.inl ⟨has, hsb⟩, Or.inl ⟨hat, htb⟩⟩)⟩

/-- **Page 15.** In a 3-chain `{p, q, r}` of a dense poset, `q` is strictly
between `p` and `r` iff the piece of `C({p, q})` containing `r` and the piece of
`C({q, r})` containing `p` are disjoint. -/
theorem middle_iff (hd : ∀ x y : α, x < y → ∃ z, x < z ∧ z < y) {p q r : α}
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (cpq : Cmp p q) (cqr : Cmp q r)
    (cpr : Cmp p r) : Btw p q r ↔ Disjoint (piece p q r) (piece q r p) := by
  have lt_or : ∀ {x y : α}, x ≠ y → Cmp x y → x < y ∨ y < x := fun hxy c =>
    c.elim (fun h => Or.inl (lt_of_le_of_ne h hxy)) fun h => Or.inr (lt_of_le_of_ne h hxy.symm)
  have nd : ∀ {X Y : Set α} {x : α}, x ∈ X → x ∈ Y → ¬ Disjoint X Y := fun hX hY hd =>
    Set.disjoint_left.1 hd hX hY
  rcases lt_or hpq cpq with h1 | h1 <;> rcases lt_or hqr cqr with h2 | h2 <;>
    rcases lt_or hpr cpr with h3 | h3
  · -- p < q < r
    rw [piece_above h1 h2, piece_below h2 h1]
    refine ⟨fun _ => Set.disjoint_left.2 fun s hs hs' => lt_asymm (hs : q < s) hs', fun _ =>
      Or.inl ⟨h1, h2⟩⟩
  · exact absurd (h1.trans h2) (lt_asymm h3)
  · -- p < r < q
    rw [piece_between h3 h2, piece_comm q r, piece_below h2 h3]
    obtain ⟨s, hps, hsr⟩ := hd p r h3
    refine ⟨fun hb => ?_, fun hdis => absurd hdis (nd ⟨hps, hsr.trans h2⟩ (hsr : s < r))⟩
    rcases hb with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h (lt_asymm h2)
    · exact absurd h (lt_asymm h1)
  · -- r < p < q
    rw [piece_below h1 h3, piece_comm q r, piece_between h3 h1]
    obtain ⟨s, hrs, hsp⟩ := hd r p h3
    refine ⟨fun hb => ?_, fun hdis => absurd hdis (nd (hsp : s < p) ⟨hrs, hsp.trans h1⟩)⟩
    rcases hb with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h (lt_asymm h2)
    · exact absurd h (lt_asymm h1)
  · -- q < p < r
    rw [piece_comm p q, piece_above h1 h3, piece_between h1 h3]
    obtain ⟨s, hps, hsr⟩ := hd p r h3
    refine ⟨fun hb => ?_, fun hdis => absurd hdis (nd (hps : p < s) ⟨h1.trans hps, hsr⟩)⟩
    rcases hb with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (lt_asymm h1)
    · exact absurd h (lt_asymm h2)
  · -- q < r < p
    rw [piece_comm p q, piece_between h2 h3, piece_above h2 h3]
    obtain ⟨s, hrs, hsp⟩ := hd r p h3
    refine ⟨fun hb => ?_, fun hdis => absurd hdis (nd ⟨h2.trans hrs, hsp⟩ (hrs : r < s))⟩
    rcases hb with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (lt_asymm h1)
    · exact absurd h (lt_asymm h2)
  · exact absurd (h2.trans h1) (lt_asymm h3)
  · -- r < q < p
    rw [piece_comm p q, piece_below h1 h2, piece_comm q r, piece_above h2 h1]
    refine ⟨fun _ => Set.disjoint_left.2 fun s hs hs' => lt_asymm (hs : s < q) hs', fun _ =>
      Or.inr ⟨h2, h1⟩⟩

end Pieces

section Transport

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- The data of page 14 preserved by a bijection `e`: comparability, and for each
comparable pair `ε` the partition of `C(ε)` into its pieces. -/
structure PreservesCuts (e : α ≃ β) : Prop where
  cmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y
  piece : ∀ a b, a ≠ b → Cmp a b → ∀ s t, InC a b s → InC a b t →
    (SamePiece (e a) (e b) (e s) (e t) ↔ SamePiece a b s t)

theorem inC_transport {e : α ≃ β} (hcmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y) (a b t : α) :
    InC (e a) (e b) (e t) ↔ InC a b t := by
  simp only [InC, hcmp, ne_eq, e.injective.eq_iff]

theorem chain_of_btw {a b c : α} (h : Btw a b c) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Cmp a b ∧ Cmp b c ∧ Cmp a c := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1.ne, h2.ne, (h1.trans h2).ne, Or.inl h1.le, Or.inl h2.le, Or.inl (h1.trans h2).le⟩
  · exact ⟨h2.ne', h1.ne', (h1.trans h2).ne', Or.inr h2.le, Or.inr h1.le,
      Or.inr (h1.trans h2).le⟩

theorem preimage_piece {e : α ≃ β} (he : PreservesCuts e) {a b t : α} (hab : a ≠ b)
    (cab : Cmp a b) (ht : InC a b t) : e ⁻¹' piece (e a) (e b) (e t) = piece a b t := by
  ext s
  simp only [mem_preimage, piece, mem_ofPred_eq, inC_transport he.cmp]
  exact and_congr_right fun hs => he.piece a b hab cab s t hs ht

omit [PartialOrder α] [PartialOrder β] in
theorem disjoint_preimage_equiv (e : α ≃ β) (X Y : Set β) :
    Disjoint (e ⁻¹' X) (e ⁻¹' Y) ↔ Disjoint X Y := by
  refine ⟨fun h => ?_, fun h => h.preimage e⟩
  simpa using h.preimage e.symm

/-- **Pages 14–15.** A bijection between dense posets that preserves
comparability and the partitions of the `C(ε)` preserves strict betweenness. -/
theorem btw_transport (hdα : ∀ x y : α, x < y → ∃ z, x < z ∧ z < y)
    (hdβ : ∀ x y : β, x < y → ∃ z, x < z ∧ z < y) {e : α ≃ β} (he : PreservesCuts e)
    (p q r : α) : Btw (e p) (e q) (e r) ↔ Btw p q r := by
  by_cases hc : p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ Cmp p q ∧ Cmp q r ∧ Cmp p r
  · obtain ⟨hpq, hqr, hpr, cpq, cqr, cpr⟩ := hc
    rw [middle_iff hdα hpq hqr hpr cpq cqr cpr,
      middle_iff hdβ (e.injective.ne hpq) (e.injective.ne hqr) (e.injective.ne hpr)
        ((he.cmp _ _).2 cpq) ((he.cmp _ _).2 cqr) ((he.cmp _ _).2 cpr),
      ← disjoint_preimage_equiv e,
      preimage_piece he hpq cpq ⟨hpr.symm, hqr.symm, Or.symm cpr, Or.symm cqr⟩,
      preimage_piece he hqr cqr ⟨hpq, hpr, cpq, cpr⟩]
  · refine iff_of_false (fun h => hc ?_) fun h => hc (chain_of_btw h)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := chain_of_btw h
    exact ⟨e.injective.ne_iff.1 h1, e.injective.ne_iff.1 h2, e.injective.ne_iff.1 h3,
      (he.cmp _ _).1 h4, (he.cmp _ _).1 h5, (he.cmp _ _).1 h6⟩

end Transport

section Order

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- Page 11, with the exact condition: `𝓡̄(a, b, c)` iff `𝓡(a, b, c)`, or
`b ∈ {a, c}` with `a, c` comparable. -/
theorem btwLe_iff (a b c : α) : BtwLe a b c ↔ Btw a b c ∨ ((b = a ∨ b = c) ∧ Cmp a c) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · by_cases e1 : b = a
      · exact Or.inr ⟨Or.inl e1, Or.inl (h1.trans h2)⟩
      by_cases e2 : b = c
      · exact Or.inr ⟨Or.inr e2, Or.inl (h1.trans h2)⟩
      exact Or.inl (Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm e1), lt_of_le_of_ne h2 e2⟩)
    · by_cases e1 : b = a
      · exact Or.inr ⟨Or.inl e1, Or.inr (h1.trans h2)⟩
      by_cases e2 : b = c
      · exact Or.inr ⟨Or.inr e2, Or.inr (h1.trans h2)⟩
      exact Or.inl (Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm e2), lt_of_le_of_ne h2 e1⟩)
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨rfl | rfl, h | h⟩)
    · exact Or.inl ⟨h1.le, h2.le⟩
    · exact Or.inr ⟨h1.le, h2.le⟩
    · exact Or.inl ⟨le_rfl, h⟩
    · exact Or.inr ⟨h, le_rfl⟩
    · exact Or.inl ⟨h, le_rfl⟩
    · exact Or.inr ⟨le_rfl, h⟩

/-- The reading's form « `𝓡̄(a, b, c)` iff `𝓡(a, b, c)` or `b ∈ {a, c}` » fails
for incomparable `a, c`: here `b = a` and `𝓡̄(a, a, c)` is false. -/
theorem btwLe_reading_fails : ¬ BtwLe ((0 : ℕ), (1 : ℕ)) (0, 1) (1, 0) := by
  simp [BtwLe, Prod.le_def]

/-- The order read on betweenness from a pair `a < b` (pages 11–13): `u ≤ v`
iff there are `x ∈ L_{≤a}` and `y ∈ L_{≥b}` with `u, v` between `x` and `y`
and `u` between `x` and `v`. -/
def ReadLe (a b u v : α) : Prop :=
  ∃ x y, (x = a ∨ Btw b a x) ∧ (y = b ∨ Btw a b y) ∧ BtwLe x u y ∧ BtwLe x v y ∧ BtwLe x u v

/-- **Pages 11–13.** On a poset directed both ways (condition b), the order is
read on betweenness from any pair `a < b`. -/
theorem le_iff_readLe (low : ∀ x y : α, ∃ z, z ≤ x ∧ z ≤ y)
    (high : ∀ x y : α, ∃ z, x ≤ z ∧ y ≤ z) {a b : α} (hab : a < b) (u v : α) :
    u ≤ v ↔ ReadLe a b u v := by
  constructor
  · intro huv
    obtain ⟨x, hxu, hxa⟩ := low u a
    obtain ⟨y, hvy, hby⟩ := high v b
    exact ⟨x, y, hxa.eq_or_lt.imp id fun e => Or.inr ⟨e, hab⟩,
      hby.eq_or_lt.imp Eq.symm fun e => Or.inl ⟨hab, e⟩, Or.inl ⟨hxu, huv.trans hvy⟩,
      Or.inl ⟨hxu.trans huv, hvy⟩, Or.inl ⟨hxu, huv⟩⟩
  · rintro ⟨x, y, hx, hy, h1, h2, h3⟩
    have hxa : x ≤ a := by
      rcases hx with rfl | ⟨h, -⟩ | ⟨h, -⟩
      · exact le_rfl
      · exact absurd h (lt_asymm hab)
      · exact h.le
    have hby : b ≤ y := by
      rcases hy with rfl | ⟨-, h⟩ | ⟨-, h⟩
      · exact le_rfl
      · exact h.le
      · exact absurd h (lt_asymm hab)
    have hxy : x < y := hxa.trans_lt (hab.trans_le hby)
    have mid : ∀ w, BtwLe x w y → x ≤ w := fun w hw => by
      rcases hw with ⟨h, -⟩ | ⟨h, h'⟩
      · exact h
      · exact absurd (h.trans h') (not_le_of_gt hxy)
    rcases h3 with ⟨-, h⟩ | ⟨-, hux⟩
    · exact h
    · exact (le_antisymm hux (mid u h1)).trans_le (mid v h2)

theorem btwLe_transport {e : α ≃ β} (hcmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y)
    (hbtw : ∀ x y z, Btw (e x) (e y) (e z) ↔ Btw x y z) (a b c : α) :
    BtwLe (e a) (e b) (e c) ↔ BtwLe a b c := by
  rw [btwLe_iff, btwLe_iff, hbtw, hcmp, e.injective.eq_iff, e.injective.eq_iff]

theorem readLe_transport {e : α ≃ β} (hcmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y)
    (hbtw : ∀ x y z, Btw (e x) (e y) (e z) ↔ Btw x y z) (a b u v : α) :
    ReadLe (e a) (e b) (e u) (e v) ↔ ReadLe a b u v := by
  simp only [ReadLe, e.surjective.exists, btwLe_transport hcmp hbtw, hbtw, e.injective.eq_iff]

/-- The case of `order_eq_or_dual` where `e` keeps the orientation of one
strict pair. -/
theorem iso_of_lt (lowα : ∀ x y : α, ∃ z, z ≤ x ∧ z ≤ y)
    (highα : ∀ x y : α, ∃ z, x ≤ z ∧ y ≤ z) (lowβ : ∀ x y : β, ∃ z, z ≤ x ∧ z ≤ y)
    (highβ : ∀ x y : β, ∃ z, x ≤ z ∧ y ≤ z) {e : α ≃ β}
    (hcmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y)
    (hbtw : ∀ x y z, Btw (e x) (e y) (e z) ↔ Btw x y z) {a b : α} (hab : a < b)
    (heab : e a < e b) (x y : α) : e x ≤ e y ↔ x ≤ y := by
  rw [le_iff_readLe lowβ highβ heab, le_iff_readLe lowα highα hab,
    readLe_transport hcmp hbtw]

/-- **Pages 11–13.** On posets directed both ways, a bijection preserving
comparability and strict betweenness is an order isomorphism or an order
anti-isomorphism: betweenness determines the order up to reversal. -/
theorem order_eq_or_dual (lowα : ∀ x y : α, ∃ z, z ≤ x ∧ z ≤ y)
    (highα : ∀ x y : α, ∃ z, x ≤ z ∧ y ≤ z) (lowβ : ∀ x y : β, ∃ z, z ≤ x ∧ z ≤ y)
    (highβ : ∀ x y : β, ∃ z, x ≤ z ∧ y ≤ z) (e : α ≃ β)
    (hcmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y)
    (hbtw : ∀ x y z, Btw (e x) (e y) (e z) ↔ Btw x y z) :
    (∀ x y, e x ≤ e y ↔ x ≤ y) ∨ (∀ x y, e y ≤ e x ↔ x ≤ y) := by
  by_cases hex : ∃ a b : α, a < b
  · obtain ⟨a, b, hab⟩ := hex
    rcases (hcmp a b).2 (Or.inl hab.le) with h | h
    · exact Or.inl (iso_of_lt lowα highα lowβ highβ hcmp hbtw hab
        (lt_of_le_of_ne h (e.injective.ne hab.ne)))
    · -- reverse `β`
      let e' : α ≃ βᵒᵈ := e.trans OrderDual.toDual
      have hcmp' : ∀ x y, Cmp (e' x) (e' y) ↔ Cmp x y := fun x y => by
        rw [← hcmp]; exact or_comm
      have hbtw' : ∀ x y z, Btw (e' x) (e' y) (e' z) ↔ Btw x y z := fun x y z => by
        rw [← hbtw]; unfold Btw; simp only [e', Equiv.trans_apply, OrderDual.toDual_lt_toDual]
        tauto
      have := iso_of_lt (β := βᵒᵈ) lowα highα (fun x y => highβ x y)
        (fun x y => lowβ x y) hcmp' hbtw' hab
        (show e' a < e' b from (lt_of_le_of_ne h (e.injective.ne hab.ne') : e b < e a))
      exact Or.inr fun x y => by simpa [e'] using this x y
  · simp only [not_exists] at hex
    have eq_of_le : ∀ {x y : α}, x ≤ y → x = y := fun h => h.eq_of_not_lt (hex _ _)
    exact Or.inl fun x y => ⟨fun h => ((hcmp x y).1 (Or.inl h)).elim id fun h' => (eq_of_le h').ge,
      fun h => eq_of_le h ▸ le_rfl⟩

/-- **The finding, pages 11–15.** A bijection between tronçons ordonnés that
preserves comparability and, for every comparable pair `ε`, the partition of
`C(ε)` into its pieces, is an order isomorphism or an order anti-isomorphism.
Only conditions b) and c) of page 8 are used. -/
theorem order_of_cuts (hα : Troncon α) (hβ : Troncon β) {e : α ≃ β}
    (he : PreservesCuts e) :
    (∀ x y, e x ≤ e y ↔ x ≤ y) ∨ (∀ x y, e y ≤ e x ↔ x ≤ y) :=
  order_eq_or_dual hα.low hα.high hβ.low hβ.high e he.cmp
    (btw_transport hα.dense hβ.dense he)

/-- `ℚ` is a tronçon (an « intervalle »). -/
theorem troncon_rat : Troncon ℚ where
  dir_down a x y hx hy := ⟨min x y, lt_min hx hy, min_le_left _ _, min_le_right _ _⟩
  dir_up a x y hx hy := ⟨max x y, le_max_left _ _, le_max_right _ _, max_lt hx hy⟩
  low x y := ⟨min x y, min_le_left _ _, min_le_right _ _⟩
  high x y := ⟨max x y, le_max_left _ _, le_max_right _ _⟩
  dense x y h := exists_between h
  card := ⟨0, 1, by norm_num⟩

/-- Comparability alone does not determine the order up to reversal, already
for the totally ordered tronçon `ℚ`: the transposition of `0` and `1` preserves
comparability and is neither increasing nor decreasing. -/
theorem cmp_alone_insufficient :
    ∃ e : ℚ ≃ ℚ, (∀ x y, Cmp (e x) (e y) ↔ Cmp x y) ∧
      ¬ ((∀ x y, e x ≤ e y ↔ x ≤ y) ∨ (∀ x y, e y ≤ e x ↔ x ≤ y)) := by
  refine ⟨Equiv.swap 0 1, fun x y => ⟨fun _ => le_total x y, fun _ => le_total _ _⟩, ?_⟩
  rintro (h | h)
  · have := h 0 1
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at this
    norm_num at this
  · have := h 1 2
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by norm_num) (by norm_num)]
      at this
    norm_num at this

end Order

end Grothendieck.Folder156_3
