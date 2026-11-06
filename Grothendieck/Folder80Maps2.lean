module

public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section


/-!
# Folder 80, pages 20, 24, 28: the bigon-free dichotomy, in combinatorial maps

Finding `80-bigon-free-five-line-dichotomy`. Page 24 (boxed, announced on page 20):

> Tout arrangement sans bigones … est soit du type `II_4`, soit contient un des types
> `I′_{3,2}`, `II_5`, `III_6`.

with `II′_{3,2}` the reading's name for the page's `I′_{3,2}` (a pencil of three and a pencil
of two, without the line joining their centres).

**The incidence core** (`dichotomy`). Lines `L`, points `P`, a relation `on`; two distinct lines
meet in exactly one point (`meet`), every point is on at least two lines (`two`: the points are
the vertices). *Bigon-free* (`BigonFree`) means that every line carries at least three
vertices: no bigonal line (exactly two) and no monogon (one, the pencils, where every face is a
bigon). If moreover some vertex is a *simple crossing* (exactly two lines through it), the
arrangement is `II_4` or contains `II_5`, `II′_{3,2}` or `III_6`.

**The maps** (`PseudolineMap`). Page 60: « une carte, topologique ou combinatoire, dont la
surface sous-jacente est un plan projectif réel », vertices of even order `≥ 4`, lines got by
going straight, two lines meeting once, each line passing once through each of its vertices.
A combinatorial map of a possibly non-orientable surface is a generalised map (`GMap`): a
finite set of flags with three fixed-point-free involutions `a0, a1, a2`, `a0 a2` a
fixed-point-free involution; vertices, edges, faces are the classes of `⟨a1, a2⟩`, `⟨a0, a2⟩`,
`⟨a0, a1⟩`, and `χ = V − E + F`. A pseudoline map adds a labelling of the flags by lines,
constant on edges, such that each line through a vertex has there exactly the four flags of
two edge-ends (`pass`), each line is connected (`conn`), every vertex is on two lines (`two`),
two lines meet at exactly one vertex (`meet`), and `χ = 1` (`euler`). Going straight is not
used: the axioms are weaker than the page's, so the theorem is stronger.

* `melchior`: a bigon-free pseudoline map has a simple crossing (Melchior's inequality
  `Σ (3 − ν(v)) ≥ 3`, from `χ = 1`, `E = Σ ν(v)` and `2E ≥ 3F`; the faces have at least three
  sides because the skeleton has no loop and no multiple edge, `face_six`);
* `map_dichotomy`: **the page's boxed statement**, for every bigon-free pseudoline map.

The proof is the one of the problems paper (§ Pseudoline arrangements): Melchior gives a simple
crossing, hence four lines in general position (`exists_gp4`); a further line through none or
one of their six vertices gives `II_5` or `II′_{3,2}`, otherwise it is a diagonal (`diag_of`);
two diagonals of different pairs give `III_6` (`iii6_of`), two of the same pair are equal
(`diag_unique`), and a lone diagonal is bigonal (`not_bigonFree`). Not formalised: the
numbering lemma of page 28, and the passage from a topological arrangement to its map.
-/

namespace Grothendieck.Folder80Maps2

section Core

variable {P L : Type*} (on : P → L → Prop)

/-- Three lines are concurrent. -/
def C (a b c : L) : Prop := ∃ p, on p a ∧ on p b ∧ on p c

/-- Four lines in general position: distinct, no three concurrent. -/
def GP4 (a b c d : L) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ¬C on a b c ∧ ¬C on a b d ∧ ¬C on a c d ∧ ¬C on b c d

/-- Five lines in general position: distinct, no three concurrent. -/
def GP5 (a b c d e : L) : Prop :=
  GP4 on a b c d ∧ a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e ∧
    ¬C on a b e ∧ ¬C on a c e ∧ ¬C on a d e ∧ ¬C on b c e ∧ ¬C on b d e ∧ ¬C on c d e

/-- Every line carries at least three vertices. -/
def BigonFree : Prop := ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- `II_4`: the arrangement is four lines in general position. -/
def IsII4 : Prop := ∃ a b c d, GP4 on a b c d ∧ ∀ m, m = a ∨ m = b ∨ m = c ∨ m = d

/-- `II_5`: five lines in general position. -/
def HasII5 : Prop := ∃ a b c d e, GP5 on a b c d e

/-- `II′_{3,2}`: `a, b, c` through `p`, `d, e` not through `p`, and their meeting point on none
of `a, b, c` (so it is the only concurrent triple of the five, and no line joins the two
centres). -/
def HasII32 : Prop :=
  ∃ a b c d e : L, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ ∃ p, on p a ∧ on p b ∧ on p c ∧ ¬on p d ∧
    ¬on p e ∧ ∀ q, on q d → on q e → ¬on q a ∧ ¬on q b ∧ ¬on q c

/-- No line of the arrangement passes through `p`, `q` and `r`. -/
def NC (p q r : P) : Prop := ∀ m, on p m → on q m → ¬on r m

/-- Some line of the arrangement passes through `p` and `q`. -/
def J (p q : P) : Prop := ∃ m, on p m ∧ on q m

/-- `III_6`, the complete quadrangle: four points, no three on a line, pairwise joined. -/
def HasIII6 : Prop :=
  ∃ p q r s : P, J on p q ∧ J on p r ∧ J on p s ∧ J on q r ∧ J on q s ∧ J on r s ∧
    NC on p q r ∧ NC on p q s ∧ NC on p r s ∧ NC on q r s

variable {on}
variable (meet : ∀ a b : L, a ≠ b → ∃! p, on p a ∧ on p b)
include meet

/-- Two lines through two distinct points are equal. -/
theorem eq_of_two {a b : L} {p q : P} (hp : on p a) (hp' : on p b) (hq : on q a)
    (hq' : on q b) (hpq : p ≠ q) : a = b :=
  by_contra fun h => hpq ((meet a b h).unique ⟨hp, hp'⟩ ⟨hq, hq'⟩)

omit meet in
/-- A point on `a, b` and a point on `a, c` differ, unless `a, b, c` are concurrent. -/
theorem ne_of_nc {a b c : L} {p q : P} (h : ¬C on a b c) (hp : on p b) (hq : on q a)
    (hq' : on q c) : p ≠ q := by
  rintro rfl; exact h ⟨p, hq, hp, hq'⟩

omit meet in
theorem C.swap12 {a b c : L} : C on a b c → C on b a c := fun ⟨p, h1, h2, h3⟩ => ⟨p, h2, h1, h3⟩

omit meet in
theorem C.swap23 {a b c : L} : C on a b c → C on a c b := fun ⟨p, h1, h2, h3⟩ => ⟨p, h1, h3, h2⟩

omit meet in
theorem GP4.swap12 {a b c d : L} (h : GP4 on a b c d) : GP4 on b a c d :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  ⟨Ne.symm h1, h4, h5, h2, h3, h6, fun h => h7 h.swap12, fun h => h8 h.swap12, h10, h9⟩

omit meet in
theorem GP4.swap23 {a b c d : L} (h : GP4 on a b c d) : GP4 on a c b d :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  ⟨h2, h1, h3, Ne.symm h4, h6, h5, fun h => h7 h.swap23, h9, h8,
    fun h => h10 h.swap12⟩

omit meet in
theorem GP4.swap34 {a b c d : L} (h : GP4 on a b c d) : GP4 on a b d c :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  ⟨h1, h3, h2, h5, h4, Ne.symm h6, h8, h7, fun h => h9 h.swap23, fun h => h10 h.swap23⟩

/-- Step 1: from a simple crossing, four lines in general position. -/
theorem quad_of {a b c d : L} {p qc qd rc rd : P} (hab : a ≠ b) (hpa : on p a) (hpb : on p b)
    (hc : ¬on p c) (hd : ¬on p d) (h1 : on qc a) (h2 : on qc c) (h3 : on qd a) (h4 : on qd d)
    (hq : qc ≠ qd) (h5 : on rc b) (h6 : on rc c) (h7 : on rd b) (h8 : on rd d) (hr : rc ≠ rd) :
    GP4 on a b c d := by
  have hac : a ≠ c := fun h => hc (h ▸ hpa)
  have had : a ≠ d := fun h => hd (h ▸ hpa)
  have hbc : b ≠ c := fun h => hc (h ▸ hpb)
  have hbd : b ≠ d := fun h => hd (h ▸ hpb)
  refine ⟨hab, hac, had, hbc, hbd, by rintro rfl; exact hc (eq_of_two meet h1 h2 h3 h4 hq ▸ hpa),
    ?_, ?_, ?_, ?_⟩ <;> rintro ⟨x, hx1, hx2, hx3⟩
  · exact hc ((meet a b hab).unique ⟨hx1, hx2⟩ ⟨hpa, hpb⟩ ▸ hx3)
  · exact hd ((meet a b hab).unique ⟨hx1, hx2⟩ ⟨hpa, hpb⟩ ▸ hx3)
  · exact hq (((meet a c hac).unique ⟨h1, h2⟩ ⟨hx1, hx2⟩).trans
      ((meet a d had).unique ⟨hx1, hx3⟩ ⟨h3, h4⟩))
  · exact hr (((meet b c hbc).unique ⟨h5, h6⟩ ⟨hx1, hx2⟩).trans
      ((meet b d hbd).unique ⟨hx1, hx3⟩ ⟨h7, h8⟩))

omit meet in
/-- A line with three vertices has two vertices other than a given point. -/
theorem two_off (hbf : BigonFree on) (l : L) (p : P) :
    ∃ s t, on s l ∧ on t l ∧ s ≠ t ∧ s ≠ p ∧ t ≠ p := by
  obtain ⟨q, r, u, hq, hr, hu, hqr, hqu, hru⟩ := hbf l
  by_cases h1 : q = p
  · subst h1; exact ⟨r, u, hr, hu, hru, Ne.symm hqr, Ne.symm hqu⟩
  by_cases h2 : r = p
  · subst h2; exact ⟨q, u, hq, hu, hqu, h1, Ne.symm hru⟩
  exact ⟨q, r, hq, hr, hqr, h1, h2⟩

/-- Step 1: a simple crossing `p = a ∩ b` of a bigon-free arrangement gives four lines in
general position. -/
theorem exists_gp4 (two : ∀ p l, on p l → ∃ m, m ≠ l ∧ on p m) (hbf : BigonFree on) {p : P}
    {a b : L} (hab : a ≠ b) (hpa : on p a) (hpb : on p b) (honly : ∀ c, on p c → c = a ∨ c = b) :
    ∃ x y z w, GP4 on x y z w := by
  have off : ∀ {e}, e ≠ a → e ≠ b → ¬on p e := fun hea heb hpe => (honly _ hpe).elim hea heb
  have nab : ∀ {s}, on s a → on s b → s = p := fun h1 h2 =>
    (meet a b hab).unique ⟨h1, h2⟩ ⟨hpa, hpb⟩
  obtain ⟨s1, s2, hs1, hs2, hs12, hs1p, hs2p⟩ := two_off hbf b p
  obtain ⟨e1, he1b, hse1⟩ := two s1 b hs1
  obtain ⟨e2, he2b, hse2⟩ := two s2 b hs2
  have he1a : e1 ≠ a := by rintro rfl; exact hs1p (nab hse1 hs1)
  have he2a : e2 ≠ a := by rintro rfl; exact hs2p (nab hse2 hs2)
  have hp1 := off he1a he1b
  have hp2 := off he2a he2b
  obtain ⟨q1, ⟨hq1a, hq1e⟩, -⟩ := meet a e1 he1a.symm
  obtain ⟨q2, ⟨hq2a, hq2e⟩, -⟩ := meet a e2 he2a.symm
  by_cases hq : q1 = q2
  · subst hq
    obtain ⟨u, v, hu, hv, huv, hup, hvp⟩ := two_off hbf a p
    obtain ⟨q3, hq3, hq13, hq3p⟩ : ∃ q3, on q3 a ∧ q1 ≠ q3 ∧ q3 ≠ p := by
      by_cases h : q1 = u
      · exact ⟨v, hv, h ▸ huv, hvp⟩
      · exact ⟨u, hu, h, hup⟩
    obtain ⟨d, hda, hq3d⟩ := two q3 a hq3
    have hdb : d ≠ b := by rintro rfl; exact hq3p (nab hq3 hq3d)
    have hpd := off hda hdb
    obtain ⟨t, ⟨htb, htd⟩, -⟩ := meet b d hdb.symm
    by_cases ht : s1 = t
    · subst ht
      exact ⟨a, b, e2, d, quad_of meet hab hpa hpb hp2 hpd hq1a hq2e hq3 hq3d hq13 hs2 hse2 htb
        htd (Ne.symm hs12)⟩
    · exact ⟨a, b, e1, d, quad_of meet hab hpa hpb hp1 hpd hq1a hq1e hq3 hq3d hq13 hs1 hse1 htb
        htd ht⟩
  · exact ⟨a, b, e1, e2, quad_of meet hab hpa hpb hp1 hp2 hq1a hq1e hq2a hq2e hq hs1 hse1 hs2
      hse2 hs12⟩

omit meet in
/-- A line through one vertex `a ∩ b` of a quadrilateral and not through the opposite vertex
`c ∩ d` gives a `II′_{3,2}`. -/
theorem ii32_of {a b c d l : L} (g : GP4 on a b c d) (h : C on a b l) (h' : ¬C on c d l)
    (hla : l ≠ a) (hlb : l ≠ b) : HasII32 on := by
  obtain ⟨hab, -, -, -, -, hcd, habc, habd, hacd, hbcd⟩ := g
  obtain ⟨p, hpa, hpb, hpl⟩ := h
  exact ⟨a, b, l, c, d, hab, hla.symm, hlb.symm, hcd, p, hpa, hpb, hpl,
    fun hc => habc ⟨p, hpa, hpb, hc⟩, fun hd => habd ⟨p, hpa, hpb, hd⟩, fun q hc hd =>
      ⟨fun ha => hacd ⟨q, ha, hc, hd⟩, fun hb => hbcd ⟨q, hb, hc, hd⟩,
        fun hl => h' ⟨q, hc, hd, hl⟩⟩⟩

omit meet in
/-- Step 2: with no `II_5` and no `II′_{3,2}`, a fifth line is a diagonal of the
quadrilateral: it passes through two opposite vertices. -/
theorem diag_of {a b c d l : L} (g : GP4 on a b c d) (ha : l ≠ a) (hb : l ≠ b) (hc : l ≠ c)
    (hd : l ≠ d) (n5 : ¬HasII5 on) (n32 : ¬HasII32 on) :
    (C on a b l ∧ C on c d l) ∨ (C on a c l ∧ C on b d l) ∨ (C on a d l ∧ C on b c l) := by
  have key : ∀ {a b c d : L}, GP4 on a b c d → l ≠ a → l ≠ b → C on a b l → C on c d l :=
    fun g ha hb h => by_contra fun h' => n32 (ii32_of g h h' ha hb)
  have g2 := g.swap23
  have g3 := g.swap34.swap23
  have g4 := g.swap12.swap23
  have g5 := g.swap23.swap12.swap34.swap23
  have g6 := g.swap12.swap23.swap34.swap23.swap34
  by_contra h
  simp only [not_or, not_and] at h
  exact n5 ⟨a, b, c, d, l, g, ha.symm, hb.symm, hc.symm, hd.symm,
    fun h1 => h.1 h1 (key g ha hb h1), fun h1 => h.2.1 h1 (key g2 ha hc h1),
    fun h1 => h.2.2 h1 (key g3 ha hd h1), fun h1 => h.2.2 (key g4 hb hc h1) h1,
    fun h1 => h.2.1 (key g6 hb hd h1) h1, fun h1 => h.1 (key g5 hc hd h1) h1⟩

/-- Two diagonals through the same opposite pair are equal. -/
theorem diag_unique {a b c d l l' : L} (g : GP4 on a b c d) (h1 : C on a b l) (h2 : C on c d l)
    (h3 : C on a b l') (h4 : C on c d l') : l = l' := by
  obtain ⟨hab, -, -, -, -, hcd, habc, -, -, -⟩ := g
  obtain ⟨r, hra, hrb, hrl⟩ := h1
  obtain ⟨r', hrc, hrd, hrl'⟩ := h2
  obtain ⟨s, hsa, hsb, hsl⟩ := h3
  obtain ⟨s', hsc, hsd, hsl'⟩ := h4
  obtain rfl := (meet a b hab).unique ⟨hsa, hsb⟩ ⟨hra, hrb⟩
  obtain rfl := (meet c d hcd).unique ⟨hsc, hsd⟩ ⟨hrc, hrd⟩
  exact eq_of_two meet hrl hsl hrl' hsl' (by rintro rfl; exact habc ⟨s, hsa, hsb, hsc⟩)

/-- Two diagonals through different opposite pairs give a complete quadrangle. -/
theorem iii6_of {a b c d l l' : L} (g : GP4 on a b c d) (h1 : C on a b l) (h2 : C on c d l)
    (h3 : C on a c l') (h4 : C on b d l') : HasIII6 on := by
  obtain ⟨-, -, -, -, -, -, habc, habd, hacd, hbcd⟩ := g
  obtain ⟨r1, h1a, h1b, h1l⟩ := h1
  obtain ⟨r2, h2c, h2d, h2l⟩ := h2
  obtain ⟨r3, h3a, h3c, h3l⟩ := h3
  obtain ⟨r4, h4b, h4d, h4l⟩ := h4
  refine ⟨r1, r2, r3, r4, ⟨l, h1l, h2l⟩, ⟨a, h1a, h3a⟩, ⟨b, h1b, h4b⟩, ⟨c, h2c, h3c⟩,
    ⟨d, h2d, h4d⟩, ⟨l', h3l, h4l⟩, fun m h1m h2m h3m => ?_, fun m h1m h2m h4m => ?_,
    fun m h1m h3m h4m => ?_, fun m h2m h3m h4m => ?_⟩
  · obtain rfl := eq_of_two meet h1m h1a h3m h3a (ne_of_nc habc h1b h3a h3c)
    exact hacd ⟨r2, h2m, h2c, h2d⟩
  · obtain rfl := eq_of_two meet h1m h1b h4m h4b fun h => habd ⟨r1, h1a, h1b, h ▸ h4d⟩
    exact hbcd ⟨r2, h2m, h2c, h2d⟩
  · obtain rfl := eq_of_two meet h1m h1a h3m h3a (ne_of_nc habc h1b h3a h3c)
    exact habd ⟨r4, h4m, h4b, h4d⟩
  · obtain rfl := eq_of_two meet h2m h2c h3m h3c fun h => hacd ⟨r2, h ▸ h3a, h2c, h2d⟩
    exact hbcd ⟨r4, h4b, h4m, h4d⟩

/-- A single diagonal, with nothing else outside the quadrilateral, is bigonal. -/
theorem not_bigonFree {a b c d l : L} (two : ∀ p l, on p l → ∃ m, m ≠ l ∧ on p m)
    (hbf : BigonFree on) (g : GP4 on a b c d) (h1 : C on a b l) (h2 : C on c d l)
    (hall : ∀ m, m = a ∨ m = b ∨ m = c ∨ m = d ∨ m = l) : False := by
  obtain ⟨r1, h1a, h1b, h1l⟩ := h1
  obtain ⟨r2, h2c, h2d, h2l⟩ := h2
  have key : ∀ x, on x l → x = r1 ∨ x = r2 := fun x hx => by
    obtain ⟨m, hml, hxm⟩ := two x l hx
    rcases hall m with rfl | rfl | rfl | rfl | rfl
    · exact .inl ((meet _ _ hml).unique ⟨hxm, hx⟩ ⟨h1a, h1l⟩)
    · exact .inl ((meet _ _ hml).unique ⟨hxm, hx⟩ ⟨h1b, h1l⟩)
    · exact .inr ((meet _ _ hml).unique ⟨hxm, hx⟩ ⟨h2c, h2l⟩)
    · exact .inr ((meet _ _ hml).unique ⟨hxm, hx⟩ ⟨h2d, h2l⟩)
    · exact absurd rfl hml
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := hbf l
  rcases key p hp with rfl | rfl <;> rcases key q hq with rfl | rfl <;>
    rcases key r hr with rfl | rfl <;> simp_all

/-- **The dichotomy** (incidence form): a bigon-free arrangement with a simple crossing is
`II_4` or contains `II_5`, `II′_{3,2}` or `III_6`. -/
theorem dichotomy (two : ∀ p l, on p l → ∃ m, m ≠ l ∧ on p m) (hbf : BigonFree on)
    (hsc : ∃ p a b, a ≠ b ∧ on p a ∧ on p b ∧ ∀ c, on p c → c = a ∨ c = b) :
    IsII4 on ∨ HasII5 on ∨ HasII32 on ∨ HasIII6 on := by
  obtain ⟨p, a, b, hab, hpa, hpb, honly⟩ := hsc
  obtain ⟨x, y, z, w, g⟩ := exists_gp4 meet two hbf hab hpa hpb honly
  by_contra! ⟨n4, n5, n32, n6⟩
  have cls := fun l (h1 : l ≠ x) h2 h3 h4 => diag_of g h1 h2 h3 h4 n5 n32
  obtain ⟨δ, h1, h2, h3, h4⟩ : ∃ δ, δ ≠ x ∧ δ ≠ y ∧ δ ≠ z ∧ δ ≠ w := by
    by_contra! h
    exact n4 ⟨x, y, z, w, g, fun m => by tauto⟩
  have g2 := g.swap23
  have g3 := g.swap34.swap23
  have hall : ∀ m, m = x ∨ m = y ∨ m = z ∨ m = w ∨ m = δ := fun m => by
    by_contra! ⟨k1, k2, k3, k4, k5⟩
    rcases cls δ h1 h2 h3 h4 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rcases cls m k1 k2 k3 k4 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact k5 (diag_unique meet g f1 f2 e1 e2)
    · exact n6 (iii6_of meet g e1 e2 f1 f2)
    · exact n6 (iii6_of meet g.swap34 e1 e2.swap12 f1 f2)
    · exact n6 (iii6_of meet g f1 f2 e1 e2)
    · exact k5 (diag_unique meet g2 f1 f2 e1 e2)
    · exact n6 (iii6_of meet g2.swap34 e1 e2.swap12 f1 f2.swap12)
    · exact n6 (iii6_of meet g.swap34 f1 f2.swap12 e1 e2)
    · exact n6 (iii6_of meet g2.swap34 f1 f2.swap12 e1 e2.swap12)
    · exact k5 (diag_unique meet g3 f1 f2 e1 e2)
  rcases cls δ h1 h2 h3 h4 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact not_bigonFree meet two hbf g e1 e2 hall
  · exact not_bigonFree meet two hbf g2 e1 e2 fun m => by have := hall m; tauto
  · exact not_bigonFree meet two hbf g3 e1 e2 fun m => by have := hall m; tauto

end Core

section Maps

open Relation

/-- A set invariant under the generators of an equivalence closure is invariant under it. -/
theorem eqvGen_iff {α : Type*} {r : α → α → Prop} (S : α → Prop) (h : ∀ x y, r x y → (S x ↔ S y))
    {a b : α} (hab : EqvGen r a b) : S a ↔ S b := by
  induction hab with
  | rel x y h' => exact h x y h'
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ i1 i2 => exact i1.trans i2

/-- A generalised map (a combinatorial map of a possibly non-orientable surface): flags with
three fixed-point-free involutions, `a0` and `a2` commuting with `a0 a2` fixed-point-free. -/
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d

namespace GMap

variable {D : Type*} (M : GMap D)

/-- Vertices are the classes of `⟨a1, a2⟩`. -/
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x
/-- Edges are the classes of `⟨a0, a2⟩`. -/
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x
/-- Faces are the classes of `⟨a0, a1⟩`. -/
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x

/-- The vertex of a flag. -/
def vtx (d : D) : M.Vtx := Quot.mk _ d
/-- The edge of a flag. -/
def edge (d : D) : M.Edge := Quot.mk _ d
/-- The face of a flag. -/
def face (d : D) : M.Face := Quot.mk _ d

instance [Finite D] : Finite M.Vtx := Quot.finite _
instance [Finite D] : Finite M.Edge := Quot.finite _
instance [Finite D] : Finite M.Face := Quot.finite _

/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face

variable {M}

@[simp] theorem vtx_a1 (d : D) : M.vtx (M.a1 d) = M.vtx d := (Quot.sound (.inl rfl)).symm
@[simp] theorem vtx_a2 (d : D) : M.vtx (M.a2 d) = M.vtx d := (Quot.sound (.inr rfl)).symm
@[simp] theorem edge_a0 (d : D) : M.edge (M.a0 d) = M.edge d := (Quot.sound (.inl rfl)).symm
@[simp] theorem edge_a2 (d : D) : M.edge (M.a2 d) = M.edge d := (Quot.sound (.inr rfl)).symm
@[simp] theorem face_a0 (d : D) : M.face (M.a0 d) = M.face d := (Quot.sound (.inl rfl)).symm
@[simp] theorem face_a1 (d : D) : M.face (M.a1 d) = M.face d := (Quot.sound (.inr rfl)).symm

theorem a0_eq_iff {x y : D} : M.a0 x = y ↔ x = M.a0 y :=
  ⟨fun h => h ▸ (M.a0_a0 x).symm, fun h => h ▸ M.a0_a0 y⟩
theorem a1_eq_iff {x y : D} : M.a1 x = y ↔ x = M.a1 y :=
  ⟨fun h => h ▸ (M.a1_a1 x).symm, fun h => h ▸ M.a1_a1 y⟩
theorem a2_eq_iff {x y : D} : M.a2 x = y ↔ x = M.a2 y :=
  ⟨fun h => h ▸ (M.a2_a2 x).symm, fun h => h ▸ M.a2_a2 y⟩

/-- An edge has exactly the four flags `d, a0 d, a2 d, a0 a2 d`. -/
theorem edge_eq {d e : D} :
    M.edge e = M.edge d ↔ e = d ∨ e = M.a0 d ∨ e = M.a2 d ∨ e = M.a0 (M.a2 d) := by
  constructor
  · intro h
    refine (eqvGen_iff (fun x => x = d ∨ x = M.a0 d ∨ x = M.a2 d ∨ x = M.a0 (M.a2 d)) ?_
      (Quot.eqvGen_exact h)).2 (.inl rfl)
    rintro x y (rfl | rfl)
    · simp only [a0_eq_iff, M.a0_a0]; tauto
    · simp only [a2_eq_iff, ← M.a0_a2, M.a2_a2]; tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem edge_four (d : D) : [d, M.a0 d, M.a2 d, M.a0 (M.a2 d)].Nodup := by
  have := M.a0_ne d; have := M.a2_ne d; have := M.a02_ne d
  have := M.a0_ne (M.a2 d)
  have : M.a0 d ≠ M.a2 d := fun h => M.a02_ne d (by rw [← h, M.a0_a0])
  have : M.a0 d ≠ M.a0 (M.a2 d) := fun h => M.a2_ne d (by
    rw [a0_eq_iff, M.a0_a0] at h; exact h.symm)
  simp_all [eq_comm]

end GMap

open GMap

/-- A combinatorial pseudoline arrangement (page 60): a generalised map with flags labelled by
lines, constant on edges; a line through a vertex has there the four flags of two edge-ends
(it passes once); each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; the surface is a projective plane, `χ = 1`. -/
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1

namespace PseudolineMap

variable {D L : Type*} (X : PseudolineMap D L)

/-- The line `l` passes through the vertex `v`. -/
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l

variable {X}

/-- A line whose flags all sit at two vertices `u, w` is not bigon-free. -/
theorem confined (hbf : BigonFree X.On) {l : L} {u w : X.M.Vtx}
    (H : ∀ e, X.line e = l → X.M.vtx e = u ∨ X.M.vtx e = w) : False := by
  obtain ⟨p, q, r, ⟨d1, rfl, h1⟩, ⟨d2, rfl, h2⟩, ⟨d3, rfl, h3⟩, h12, h13, h23⟩ := hbf l
  rcases H _ h1 with h1 | h1 <;> rcases H _ h2 with h2 | h2 <;> rcases H _ h3 with h3 | h3 <;>
    simp_all

/-- The connected line `l` stays in a set of vertices stable under `a0` along `l`. -/
theorem confine {l : L} (Z : X.M.Vtx → Prop)
    (h : ∀ x, X.line x = l → Z (X.M.vtx x) → Z (X.M.vtx (X.M.a0 x))) {d : D} (hd : X.line d = l)
    (hZ : Z (X.M.vtx d)) {e : D} (he : X.line e = l) : Z (X.M.vtx e) := by
  refine (eqvGen_iff (fun x => X.line x = l → Z (X.M.vtx x)) ?_ (X.conn d e (hd.trans he.symm))).1
    (fun _ => hZ) he
  rintro x y (rfl | ⟨h1, h2⟩)
  · rw [X.line_a0]
    exact ⟨fun h' hx => h _ hx (h' hx), fun h' hx => by
      simpa [X.M.a0_a0] using h _ (by rwa [X.line_a0]) (h' hx)⟩
  · rw [h1, h2]

variable [Fintype D]

open Classical in
/-- The four flags of a line at a vertex. -/
theorem at_four {d x1 x2 x3 x4 : D} (hn : [x1, x2, x3, x4].Nodup)
    (hx : ∀ x ∈ [x1, x2, x3, x4], X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d) {f : D}
    (hf : X.M.vtx f = X.M.vtx d) (hl : X.line f = X.line d) : f ∈ [x1, x2, x3, x4] := by
  have h4 := X.pass d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have hsub : [x1, x2, x3, x4].toFinset ⊆
      Finset.univ.filter fun e => X.M.vtx e = X.M.vtx d ∧ X.line e = X.line d := fun x hx' => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx _ (List.mem_toFinset.1 hx')
  have := Finset.eq_of_subset_of_card_le hsub (by rw [h4, List.toFinset_card_of_nodup hn]; rfl)
  rw [← List.mem_toFinset, this]; simp [hf, hl]

/-- No loop: the two ends of an edge are distinct vertices. -/
theorem noLoop (hbf : BigonFree X.On) (d : D) : X.M.vtx (X.M.a0 d) ≠ X.M.vtx d := by
  intro h
  have hall : ∀ x ∈ [d, X.M.a0 d, X.M.a2 d, X.M.a0 (X.M.a2 d)],
      X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d := by
    simp [h, X.line_a0, X.line_a2, X.M.a0_a2]
  refine confined hbf (l := X.line d) (u := X.M.vtx d) (w := X.M.vtx d) fun e he => .inl ?_
  refine confine (fun t => t = X.M.vtx d) (fun x hx hxv => ?_) rfl rfl he
  have := at_four (edge_four d) hall hxv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> simp [h, X.M.a0_a0, X.M.a0_a2]

/-- No multiple edge: two edges with the same ends are equal. -/
theorem noMulti (hbf : BigonFree X.On) {x y : D} (hv : X.M.vtx x = X.M.vtx y)
    (hw : X.M.vtx (X.M.a0 x) = X.M.vtx (X.M.a0 y)) : X.M.edge x = X.M.edge y := by
  by_contra hne
  by_cases hl : X.line x = X.line y
  · have hd : ∀ {a b}, X.M.edge a = X.M.edge x → X.M.edge b = X.M.edge y → a ≠ b :=
      fun ha hb h => hne (ha.symm.trans (h ▸ hb))
    have n1 : [x, X.M.a2 x, y, X.M.a2 y].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨(X.M.a2_ne x).symm, hd rfl rfl, hd rfl (edge_a2 y)⟩, ⟨hd (edge_a2 x) rfl,
        hd (edge_a2 x) (edge_a2 y)⟩, (X.M.a2_ne y).symm⟩
    have n2 : [X.M.a0 x, X.M.a0 (X.M.a2 x), X.M.a0 y, X.M.a0 (X.M.a2 y)].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      refine ⟨⟨fun h => X.M.a2_ne x ?_, hd (by simp) (by simp), hd (by simp) (by simp)⟩,
        ⟨hd (by simp) (by simp), hd (by simp) (by simp)⟩, fun h => X.M.a2_ne y ?_⟩ <;>
        simpa [X.M.a0_a0] using (congrArg X.M.a0 h).symm
    have h1 : ∀ z ∈ [x, X.M.a2 x, y, X.M.a2 y], X.M.vtx z = X.M.vtx x ∧ X.line z = X.line x := by
      simp [hv, hl, X.line_a2]
    have h2 : ∀ z ∈ [X.M.a0 x, X.M.a0 (X.M.a2 x), X.M.a0 y, X.M.a0 (X.M.a2 y)],
        X.M.vtx z = X.M.vtx (X.M.a0 x) ∧ X.line z = X.line (X.M.a0 x) := by
      simp [hw, hl, X.line_a2, X.line_a0, X.M.a0_a2]
    refine confined hbf (l := X.line x) (u := X.M.vtx x) (w := X.M.vtx (X.M.a0 x)) fun e he => ?_
    refine confine (fun t => t = X.M.vtx x ∨ t = X.M.vtx (X.M.a0 x)) (fun f hf hfv => ?_)
      rfl (.inl rfl) he
    rcases hfv with hfv | hfv
    · have := at_four n1 h1 hfv hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> simp [hw, X.M.a0_a2]
    · have := at_four n2 h2 hfv (by rw [hf, X.line_a0])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> simp [hv, X.M.a0_a0, X.M.a0_a2]
  · obtain ⟨v, -, huniq⟩ := X.meet _ _ hl
    have h1 := huniq (X.M.vtx x) ⟨⟨x, rfl, rfl⟩, ⟨y, hv.symm, rfl⟩⟩
    have h2 := huniq (X.M.vtx (X.M.a0 x)) ⟨⟨_, rfl, X.line_a0 x⟩, ⟨_, hw.symm, X.line_a0 y⟩⟩
    exact noLoop hbf x (h2.trans h1.symm)

omit [Fintype D] in
/-- Every vertex has degree at least two: `a1 d ≠ a2 d`. -/
theorem a1_ne_a2 (d : D) : X.M.a1 d ≠ X.M.a2 d := by
  intro h
  obtain ⟨e, he, hl⟩ := X.two d
  have := (eqvGen_iff (fun z => z = d ∨ z = X.M.a2 d) ?_ (Quot.eqvGen_exact he)).2 (.inl rfl)
  · rcases this with rfl | rfl
    · exact hl rfl
    · exact hl (X.line_a2 _)
  · rintro u w (rfl | rfl)
    · simp only [a1_eq_iff, ← h, X.M.a1_a1]; tauto
    · simp only [a2_eq_iff, X.M.a2_a2]; tauto

theorem edge_a1_ne (hbf : BigonFree X.On) (d : D) : X.M.edge (X.M.a1 d) ≠ X.M.edge d := by
  intro h
  rcases edge_eq.1 h with h | h | h | h
  · exact X.M.a1_ne d h
  · exact noLoop hbf d (by rw [← h, vtx_a1])
  · exact a1_ne_a2 d h
  · exact noLoop hbf (X.M.a2 d) (by rw [← h, vtx_a1, vtx_a2])

open Classical in
/-- Every face has at least three sides: six flags. -/
theorem face_six (hbf : BigonFree X.On) (d : D) :
    6 ≤ (Finset.univ.filter fun e => X.M.face e = X.M.face d).card := by
  have i0 : ∀ {x y : D}, X.M.a0 x = X.M.a0 y → x = y := fun h => by
    simpa [X.M.a0_a0] using congrArg X.M.a0 h
  have i1 : ∀ {x y : D}, X.M.a1 x = X.M.a1 y → x = y := fun h => by
    simpa [X.M.a1_a1] using congrArg X.M.a1 h
  have loop : ∀ z, X.M.a1 z ≠ X.M.a0 z := fun z h => noLoop hbf z (by rw [← h, vtx_a1])
  have multi : X.M.a0 (X.M.a1 d) ≠ X.M.a1 (X.M.a0 d) := fun h =>
    edge_a1_ne hbf d (noMulti hbf (vtx_a1 d) (by rw [h, vtx_a1]))
  have hn : [X.M.a0 (X.M.a1 d), X.M.a1 d, d, X.M.a0 d, X.M.a1 (X.M.a0 d),
      X.M.a0 (X.M.a1 (X.M.a0 d))].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨X.M.a0_ne _, fun h => loop d (a0_eq_iff.1 h), fun h => X.M.a1_ne d (i0 h), multi,
      fun h => (X.M.a0_ne d (i1 (i0 h)).symm)⟩, ⟨X.M.a1_ne d, loop d,
      fun h => X.M.a0_ne d (i1 h).symm, fun h => multi (a0_eq_iff.2 h)⟩, ⟨(X.M.a0_ne d).symm,
      fun h => loop d (a1_eq_iff.2 h), fun h => X.M.a1_ne _ (a0_eq_iff.2 h).symm⟩,
      ⟨(X.M.a1_ne _).symm, fun h => loop d (a1_eq_iff.2 (i0 h))⟩, (X.M.a0_ne _).symm⟩
  have hsub : [X.M.a0 (X.M.a1 d), X.M.a1 d, d, X.M.a0 d, X.M.a1 (X.M.a0 d),
      X.M.a0 (X.M.a1 (X.M.a0 d))].toFinset ⊆ Finset.univ.filter fun e => X.M.face e = X.M.face d :=
    fun x hx => by
      simp only [List.mem_toFinset, List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all
  exact (List.toFinset_card_of_nodup hn).symm.trans_le (Finset.card_le_card hsub)

open Classical in
/-- **Melchior's inequality** gives a simple crossing: from `χ = 1`, `4E = 4 Σ ν(v)` and
`6F ≤ 4E`, `Σ (3 − ν(v)) ≥ 3`, so some vertex is on exactly two lines. -/
theorem melchior (hbf : BigonFree X.On) :
    ∃ v a b, a ≠ b ∧ X.On v a ∧ X.On v b ∧ ∀ c, X.On v c → c = a ∨ c = b := by
  let := Fintype.ofFinite X.M.Vtx
  let := Fintype.ofFinite X.M.Edge
  let := Fintype.ofFinite X.M.Face
  let ν : X.M.Vtx → ℕ := fun v => ((Finset.univ.filter fun e => X.M.vtx e = v).image X.line).card
  have hν : ∀ v c, X.On v c ↔ c ∈ (Finset.univ.filter fun e => X.M.vtx e = v).image X.line :=
    fun v c => by simp [On]
  have hV : Fintype.card D = ∑ v, 4 * ν v := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := X.M.vtx) (t := Finset.univ)
      (by simp)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_eq_sum_card_image X.line, Finset.sum_const_nat (m := 4), mul_comm]
    intro l hl
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hl
    have h4 := X.pass e
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
    rw [Finset.filter_filter, ← h4]
    congr 1; ext a; simp [(Finset.mem_filter.1 he).2]
  have hE : Fintype.card D = 4 * Fintype.card X.M.Edge := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := X.M.edge) (t := Finset.univ)
      (by simp)]
    have : ∀ q, (Finset.univ.filter fun a => X.M.edge a = q).card = 4 := fun q => by
      obtain ⟨d, rfl⟩ : ∃ d, X.M.edge d = q := Quot.exists_rep q
      have h : _ = 4 := List.toFinset_card_of_nodup (edge_four (M := X.M) d)
      rw [← h]
      congr 1; ext e; simpa using edge_eq (M := X.M) (d := d) (e := e)
    simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hF : 6 * Fintype.card X.M.Face ≤ Fintype.card D := by
    rw [← Finset.card_univ (α := D), Finset.card_eq_sum_card_fiberwise (f := X.M.face)
      (t := Finset.univ) (by simp)]
    calc 6 * Fintype.card X.M.Face = ∑ _q : X.M.Face, 6 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun q _ => by
        obtain ⟨d, rfl⟩ : ∃ d, X.M.face d = q := Quot.exists_rep q
        exact face_six hbf d
  have heul := X.euler
  simp only [GMap.euler, Nat.card_eq_fintype_card] at heul
  obtain ⟨v, -, hv⟩ : ∃ v ∈ Finset.univ, ν v < 3 := by
    by_contra! h
    have := Finset.sum_le_sum h
    rw [← Finset.mul_sum] at hV
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    omega
  obtain ⟨d, rfl⟩ : ∃ d, X.M.vtx d = v := Quot.exists_rep v
  obtain ⟨e, he, hl⟩ := X.two d
  have h2 : 1 < ν (X.M.vtx d) := Finset.one_lt_card.2 ⟨_, (hν _ _).1 ⟨d, rfl, rfl⟩, _,
    (hν _ _).1 ⟨e, he, rfl⟩, hl.symm⟩
  obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.1 (show ν (X.M.vtx d) = 2 by omega)
  refine ⟨X.M.vtx d, a, b, hab, (hν _ _).2 (by simp [hab']), (hν _ _).2 (by simp [hab']),
    fun c hc => ?_⟩
  simpa [hab'] using (hν _ _).1 hc

/-- **The page's boxed statement** (pages 20, 24): every bigon-free combinatorial arrangement of
pseudolines in the real projective plane is `II_4` or contains `II_5`, `II′_{3,2}` or
`III_6`. -/
theorem map_dichotomy (hbf : BigonFree X.On) :
    IsII4 X.On ∨ HasII5 X.On ∨ HasII32 X.On ∨ HasIII6 X.On :=
  dichotomy X.meet (fun _ _ ⟨d, hd, hl⟩ => by
    obtain ⟨e, he, hle⟩ := X.two d
    exact ⟨_, hl ▸ hle, e, he.trans hd, rfl⟩) hbf (melchior hbf)

end PseudolineMap

end Maps

end Grothendieck.Folder80Maps2
