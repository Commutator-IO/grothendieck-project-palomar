module

public import Mathlib
public import Grothendieck.Folder80Maps3

@[expose] public section


/-!
# Folder 80, pages 39–54: the sign algebra behind the three-pencil case

Finding `80-skeleton-full-faithfulness`. `Folder80Maps3` proves page 54 for every bigon-free
arrangement in which each triangle has a fourth line through none of its vertices. What it
leaves is the case where every other line passes through a vertex of some triangle: the
arrangement lies in three pencils, the complete quadrangle `III₆` being the first example.

This file closes that case by another route, through chirotopes. A chirotope is written
additively, `χ i j l : ZMod 2` being the sign bit of the triple (`0` for `+`, `1` for `-`),
defined on the *bases*, the triples of pairwise distinct lines with no common point. An
isomorphism of labelled skeleta gives, along each line `i`, the same points in the same cyclic
order up to reversal; by the representation theorem in rank 2 the two contractions at `i` then
differ by a sign `s i` and a reorientation `ε i`:
`χ' (σ i) (σ j) (σ l) = χ i j l + s i + ε i j + ε i l` (`LocallyEquivalent`).

**What is proved.**
* `eq_zero_of_fourth`: if a sign function is, at each line `i`, of the form
  `ψ i j l = δ i j + δ i l`, it vanishes on a triangle that has a fourth line through none of
  its vertices (the four triples of four lines in general position have equal values, and their
  sum is zero).
* `eq_zero`: in a bigon-free incidence structure where two lines meet once, it vanishes on every
  triangle. A triangle `a, b, c` without a fourth line is split at `a` by a line `x` through
  `b ∩ c`, which exists because `a` carries a third vertex; the triangles `a, b, x` and `a, x, c`
  have fourth lines through `a ∩ c` and `a ∩ b`, which exist because `b` and `c` carry third
  vertices.
* `reorientation_of_locallyEquivalent`: **steps 2–4.** If the two chirotopes are locally
  equivalent along every line, `χ' ∘ σ` is the reorientation of `χ` by `s`.
* `const_add_cut`, `locallyEquivalent_of_sameSeparation`: **the rank-2 step.** On a complete
  multipartite graph with at least three parts, a sign function balanced on every 4-cycle is a
  constant plus a cut. Along a line, the 4-cycle sums of `χ` are its separation relation (which
  pair of vertices separates which on the line), so two chirotopes with the same separation
  relation along every line are locally equivalent.
* `reorientation_of_sameSeparation`: **steps 1–4 together.**

**Not formalised.** Folkman–Lawrence, which turns the reorientation into a homeomorphism of the
projective plane, and the fact that on an actual arrangement the separation relation along `i`
is the one the cyclic order of the vertices of `L_i` records.
-/

namespace Grothendieck.Folder80Signs

open Grothendieck.Folder80Maps3 (BigonFree)

variable {P L : Type*} (on : P → L → Prop)

/-- Three pairwise distinct lines without a common point. -/
def Basis (i j l : L) : Prop :=
  i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ¬∃ p, on p i ∧ on p j ∧ on p l

/-- Two distinct lines meet in exactly one point, and every point is on two lines. -/
structure Incidence : Prop where
  meet : ∀ l l' : L, l ≠ l' → ∃ p, on p l ∧ on p l'
  unique : ∀ {l l' : L} {p q : P}, l ≠ l' → on p l → on p l' → on q l → on q l' → p = q
  two : ∀ {p : P} {l : L}, on p l → ∃ l', l' ≠ l ∧ on p l'

variable {on}

/-- A sign function that is, at each line `i`, the coboundary of some `δ i` on the other
lines. -/
def LocalForm (ψ : L → L → L → ZMod 2) : Prop :=
  ∃ δ : L → L → ZMod 2, ∀ i j l, Basis on i j l → ψ i j l = δ i j + δ i l

theorem Basis.swap12 {i j l : L} (h : Basis on i j l) : Basis on j i l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h3, h2, fun ⟨p, a, b, c⟩ => h4 ⟨p, b, a, c⟩⟩

theorem Basis.swap23 {i j l : L} (h : Basis on i j l) : Basis on i l j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h2, h1, h3.symm, fun ⟨p, a, b, c⟩ => h4 ⟨p, a, c, b⟩⟩

/-- A line avoiding a common point of two lines makes a basis with them. -/
theorem basis_of_avoid (hI : Incidence on) {i j m : L} {p : P} (hij : i ≠ j) (pi : on p i)
    (pj : on p j) (hm : ¬on p m) (mi : m ≠ i) (mj : m ≠ j) : Basis on i j m :=
  ⟨hij, mi.symm, mj.symm, fun ⟨_, qi, qj, qm⟩ => hm (hI.unique hij pi pj qi qj ▸ qm)⟩

section Algebra

variable {ψ : L → L → L → ZMod 2}
  (s12 : ∀ i j l, ψ j i l = ψ i j l) (s23 : ∀ i j l, ψ i l j = ψ i j l)
include s12 s23

/-- **Step 3.** Four lines in general position: the triangle `i, j, l` gets the value `0`. The
three relations at `i`, `j` and `l` add up to `ψ i j l`, everything else appearing twice. -/
theorem eq_zero_of_fourth (hψ : LocalForm (on := on) ψ) {i j l m : L} (h : Basis on i j l)
    (hm1 : Basis on i j m) (hm2 : Basis on i l m) (hm3 : Basis on j l m) : ψ i j l = 0 := by
  obtain ⟨δ, hδ⟩ := hψ
  have ei := hδ i j l h
  have ei' := hδ i j m hm1
  have ei'' := hδ i l m hm2
  have ej : ψ i j l = δ j i + δ j l := by rw [← s12]; exact hδ j i l h.swap12
  have ej' : ψ i j m = δ j i + δ j m := by rw [← s12]; exact hδ j i m hm1.swap12
  have ej'' := hδ j l m hm3
  have el : ψ i j l = δ l i + δ l j := by
    rw [← s23 i j l, ← s12 i l j]; exact hδ l i j h.swap23.swap12
  have el' : ψ i l m = δ l i + δ l m := by rw [← s12]; exact hδ l i m hm2.swap12
  have el'' : ψ j l m = δ l j + δ l m := by rw [← s12]; exact hδ l j m hm3.swap12
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination ei + ei' + ei'' + ej + ej' + ej'' + el + el' + el'' +
    (-ψ i j l - ψ i j m - ψ i l m - ψ j l m + δ i j + δ i l + δ i m + δ j i + δ j l + δ j m +
      δ l i + δ l j + δ l m) * two

/-- **Steps 3 and 4.** In a bigon-free incidence structure, a sign function of local form
vanishes on every basis. -/
theorem eq_zero (hI : Incidence on) (hbf : BigonFree on) (hψ : LocalForm (on := on) ψ)
    {a b c : L} (h : Basis on a b c) : ψ a b c = 0 := by
  have key : ∀ {i j l m : L}, Basis on i j l → Basis on i j m → Basis on i l m →
      Basis on j l m → ψ i j l = 0 := fun h1 h2 h3 h4 => eq_zero_of_fourth s12 s23 hψ h1 h2 h3 h4
  have hB := h
  obtain ⟨hab, hac, hbc, hno⟩ := h
  -- a triangle with a fourth line through none of its vertices: step 3
  by_cases hfourth : ∃ m, Basis on a b m ∧ Basis on a c m ∧ Basis on b c m
  · obtain ⟨m, h1, h2, h3⟩ := hfourth
    exact key hB h1 h2 h3
  push Not at hfourth
  obtain ⟨δ, hδ⟩ := hψ
  obtain ⟨P1, P1b, P1c⟩ := hI.meet b c hbc
  obtain ⟨P2, P2a, P2c⟩ := hI.meet a c hac
  obtain ⟨P3, P3a, P3b⟩ := hI.meet a b hab
  -- with no fourth line, every line other than `a, b, c` passes through a vertex
  have through : ∀ m, m ≠ a → m ≠ b → m ≠ c → on P1 m ∨ on P2 m ∨ on P3 m := by
    intro m ma mb mc
    by_contra hcon
    push Not at hcon
    exact hfourth m (basis_of_avoid hI hab P3a P3b hcon.2.2 ma mb)
      (basis_of_avoid hI hac P2a P2c hcon.2.1 ma mc) (basis_of_avoid hI hbc P1b P1c hcon.1 mb mc)
  -- on a line `l`, a vertex other than two given ones
  have third : ∀ (l : L) (u v : P), ∃ q, on q l ∧ q ≠ u ∧ q ≠ v := by
    intro l u v
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := hbf l
    by_cases h1 : p ≠ u ∧ p ≠ v
    · exact ⟨p, hp, h1⟩
    by_cases h2 : q ≠ u ∧ q ≠ v
    · exact ⟨q, hq, h2⟩
    refine ⟨r, hr, ?_, ?_⟩ <;> rintro rfl <;> grind
  -- a second line through a new point `Q` of `a`, `R` of `b`, `S` of `c`
  obtain ⟨Q, Qa, Q2, Q3⟩ := third a P2 P3
  obtain ⟨R, Rb, R1, R3⟩ := third b P1 P3
  obtain ⟨S, Sc, S1, S2⟩ := third c P1 P2
  obtain ⟨x, xa, Qx⟩ := hI.two Qa
  obtain ⟨y, yb, Ry⟩ := hI.two Rb
  obtain ⟨z, zc, Sz⟩ := hI.two Sc
  -- a line meets `a`, `b`, `c` only once
  have xP2 : ¬on P2 x := fun e => Q2 (hI.unique xa.symm Qa Qx P2a e)
  have xP3 : ¬on P3 x := fun e => Q3 (hI.unique xa.symm Qa Qx P3a e)
  have yP1 : ¬on P1 y := fun e => R1 (hI.unique yb.symm Rb Ry P1b e)
  have yP3 : ¬on P3 y := fun e => R3 (hI.unique yb.symm Rb Ry P3b e)
  have zP1 : ¬on P1 z := fun e => S1 (hI.unique zc.symm Sc Sz P1c e)
  have zP2 : ¬on P2 z := fun e => S2 (hI.unique zc.symm Sc Sz P2c e)
  have xb : x ≠ b := fun e => xP3 (e ▸ P3b)
  have xc : x ≠ c := fun e => xP2 (e ▸ P2c)
  have ya : y ≠ a := fun e => yP3 (e ▸ P3a)
  have yc : y ≠ c := fun e => yP1 (e ▸ P1c)
  have za : z ≠ a := fun e => zP2 (e ▸ P2a)
  have zb : z ≠ b := fun e => zP1 (e ▸ P1b)
  -- so `x` passes through `P1`, `y` through `P2`, `z` through `P3`
  have x1 : on P1 x := (through x xa xb xc).resolve_right (not_or.2 ⟨xP2, xP3⟩)
  have y2 : on P2 y := ((through y ya yb yc).resolve_left yP1).resolve_right yP3
  have z3 : on P3 z := ((through z za zb zc).resolve_left zP1).resolve_left zP2
  have yQ : ¬on Q y := fun e => Q2 (hI.unique ya.symm Qa e P2a y2)
  have zQ : ¬on Q z := fun e => Q3 (hI.unique za.symm Qa e P3a z3)
  have xy : y ≠ x := fun e => xP2 (e ▸ y2)
  have xz : z ≠ x := fun e => xP3 (e ▸ z3)
  -- the triangle `a, b, x`, with fourth line `y`
  have Babx := basis_of_avoid hI hab P3a P3b xP3 xa xb
  have h1 : ψ a b x = 0 := key Babx (basis_of_avoid hI hab P3a P3b yP3 ya yb)
    (basis_of_avoid hI xa.symm Qa Qx yQ ya xy) (basis_of_avoid hI xb.symm P1b x1 yP1 yb xy)
  -- the triangle `a, x, c`, with fourth line `z`
  have Baxc := (basis_of_avoid hI hac P2a P2c xP2 xa xc).swap23
  have h2 : ψ a x c = 0 := key Baxc (basis_of_avoid hI xa.symm Qa Qx zQ za xz)
    (basis_of_avoid hI hac P2a P2c zP2 za zc) (basis_of_avoid hI xc x1 P1c zP1 xz zc)
  -- at `a`: `ψ a b c = ψ a b x + ψ a x c`
  have e1 := hδ a b c hB
  have e2 := hδ a b x Babx
  have e3 := hδ a x c Baxc
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination e1 - e2 - e3 + h1 + h2 - δ a x * two

end Algebra

/-- Two chirotopes, as sign bits on the bases, are *locally equivalent* along every line when the
contractions at `i` and at `σ i` differ by a global sign `s i` and a reorientation `ε i`: what an
isomorphism of labelled skeleta gives, by the representation theorem in rank 2. -/
def LocallyEquivalent (χ χ' : L → L → L → ZMod 2) (σ : L → L) : Prop :=
  ∃ s : L → ZMod 2, ∃ ε : L → L → ZMod 2,
    ∀ i j l, Basis on i j l → χ' (σ i) (σ j) (σ l) = χ i j l + s i + ε i j + ε i l

/-- **Steps 2–4.** In a bigon-free incidence structure, two alternating chirotopes that are
locally equivalent along every line differ by a reorientation: `χ' ∘ σ` is `χ` with the lines in
`r` reversed. -/
theorem reorientation_of_locallyEquivalent (hI : Incidence on) (hbf : BigonFree on)
    {χ χ' : L → L → L → ZMod 2} {σ : L → L}
    (a12 : ∀ i j l, χ j i l = χ i j l + 1) (a23 : ∀ i j l, χ i l j = χ i j l + 1)
    (a12' : ∀ i j l, χ' j i l = χ' i j l + 1) (a23' : ∀ i j l, χ' i l j = χ' i j l + 1)
    (H : LocallyEquivalent (on := on) χ χ' σ) :
    ∃ r : L → ZMod 2, ∀ i j l, Basis on i j l →
      χ' (σ i) (σ j) (σ l) = χ i j l + r i + r j + r l := by
  obtain ⟨s, ε, hε⟩ := H
  refine ⟨s, fun i j l h => ?_⟩
  -- step 2: `ψ` is symmetric, and of local form with `δ i j = ε i j + s j`
  set ψ : L → L → L → ZMod 2 := fun i j l => χ' (σ i) (σ j) (σ l) + χ i j l + s i + s j + s l
  have two : (2 : ZMod 2) = 0 := rfl
  have s12 : ∀ i j l, ψ j i l = ψ i j l := fun i j l => by
    simp only [ψ]; rw [a12, a12']; linear_combination two
  have s23 : ∀ i j l, ψ i l j = ψ i j l := fun i j l => by
    simp only [ψ]; rw [a23, a23']; linear_combination two
  have hloc : LocalForm (on := on) ψ := ⟨fun i j => ε i j + s j, fun i j l h => by
    simp only [ψ]; rw [hε i j l h]; linear_combination (χ i j l + s i) * two⟩
  have h0 := eq_zero s12 s23 hI hbf hloc h
  simp only [ψ] at h0
  linear_combination h0 - (χ i j l + s i + s j + s l) * two

section RankTwo

/-! ### The rank-2 step

Along a line `i`, the other lines fall into classes, one per vertex of `i`. A sign function on
pairs of lines in distinct classes is *balanced* when its sum over every 4-cycle of the complete
multipartite graph is `0`. For the product of two chirotopes, this says that the two contractions
at `i` have the same separation relation: `{j, k}` separates `{l, m}` on `i` iff
`χ i j l + χ i j m + χ i k l + χ i k m = 1`, and that is what the cyclic order of the vertices
along `i`, up to reversal, records. -/

variable {V C : Type*} {cls : V → C} {φ : V → V → ZMod 2}

/-- **The rank-2 lemma.** On a complete multipartite graph with at least three parts, a symmetric
sign function balanced on every 4-cycle is a constant plus a cut. -/
theorem const_add_cut (hsym : ∀ j l, φ l j = φ j l)
    (h4 : ∀ j k l m, cls j ≠ cls l → cls j ≠ cls m → cls k ≠ cls l → cls k ≠ cls m →
      φ j l + φ j m + φ k l + φ k m = 0)
    {p q r : V} (hpq : cls p ≠ cls q) (hqr : cls q ≠ cls r) (hpr : cls p ≠ cls r) :
    ∃ (s : ZMod 2) (ε : V → ZMod 2), ∀ j l, cls j ≠ cls l → φ j l = s + ε j + ε l := by
  classical
  -- `s` is the value of the triangle `p, q, r`; `ε` is read from `p`, or from `q` on the class
  -- of `p`
  refine ⟨φ p q + φ q r + φ r p, fun j => if cls j = cls p then φ q j + φ p q
    else φ p j + (φ p q + φ q r + φ r p), ?_⟩
  -- one end in the class of `p`: a 4-cycle through `p` and `q`
  have half : ∀ j l, cls j = cls p → cls l ≠ cls p →
      φ j l = φ q j + φ p q + φ p l := by
    intro j l hj hl
    have e := h4 j p l q (fun e => hl (e.symm.trans hj)) (fun e => hpq (hj.symm.trans e))
      (Ne.symm hl) hpq
    linear_combination (norm := (ring_nf; reduce_mod_char)) e + hsym q j
  intro j l hjl
  by_cases hj : cls j = cls p <;> by_cases hl : cls l = cls p
  · exact absurd (hj.trans hl.symm) hjl
  · simp only [hj, hl, ↓reduceIte]
    linear_combination (norm := (ring_nf; reduce_mod_char)) half j l hj hl
  · simp only [hj, hl, ↓reduceIte]
    linear_combination (norm := (ring_nf; reduce_mod_char)) half l j hl hj + hsym j l
  · simp only [hj, hl, ↓reduceIte]
    -- both ends outside the class of `p`: the triangle `p, j, l` has the value of `p, q, r`
    by_cases hlq : cls l = cls q
    · have hjq : cls j ≠ cls q := fun e => hjl (e.trans hlq.symm)
      have e1 := h4 l q j p (Ne.symm hjl) hl (fun e => hjl (e.symm.trans hlq.symm)) (Ne.symm hpq)
      have e2 := h4 j r q p hjq hj (Ne.symm hqr) (Ne.symm hpr)
      linear_combination (norm := (ring_nf; reduce_mod_char)) e1 + e2 + hsym j l + hsym p l +
        hsym j q + hsym p q + hsym p j + hsym q r
    · have e1 := h4 j q p l hj hjl (Ne.symm hpq) (fun e => hlq e.symm)
      have e2 := h4 l r q p hlq hl (Ne.symm hqr) (Ne.symm hpr)
      linear_combination (norm := (ring_nf; reduce_mod_char)) e1 + e2 + hsym p j + hsym p q +
        hsym q l + hsym p l + hsym q r

end RankTwo

/-- The two chirotopes have the same separation relation along every line: what an isomorphism
of labelled skeleta gives, the cyclic order of the vertices along `i` being kept up to
reversal. -/
def SameSeparation (χ χ' : L → L → L → ZMod 2) (σ : L → L) : Prop :=
  ∀ i j k l m, Basis on i j l → Basis on i j m → Basis on i k l → Basis on i k m →
    χ' (σ i) (σ j) (σ l) + χ' (σ i) (σ j) (σ m) + χ' (σ i) (σ k) (σ l) + χ' (σ i) (σ k) (σ m) =
      χ i j l + χ i j m + χ i k l + χ i k m

/-- **The rank-2 step.** In a bigon-free incidence structure, chirotopes with the same separation
relation along every line are locally equivalent. -/
theorem locallyEquivalent_of_sameSeparation (hI : Incidence on) (hbf : BigonFree on)
    {χ χ' : L → L → L → ZMod 2} {σ : L → L}
    (a23 : ∀ i j l, χ i l j = χ i j l + 1) (a23' : ∀ i j l, χ' i l j = χ' i j l + 1)
    (H : SameSeparation (on := on) χ χ' σ) : LocallyEquivalent (on := on) χ χ' σ := by
  classical
  -- the class of `j` along `i` is the point `i ∩ j`
  let c : L → L → P := fun i j => if h : i ≠ j then Classical.choose (hI.meet i j h)
    else Classical.choice ⟨Classical.choose (hbf i)⟩
  have c_on : ∀ {i j}, i ≠ j → on (c i j) i ∧ on (c i j) j := fun {i j} h => by
    simp only [c, ne_eq, h, not_false_eq_true, ↓reduceDIte]; exact Classical.choose_spec (hI.meet i j h)
  have c_eq : ∀ {i j : L} {p : P}, i ≠ j → on p i → on p j → c i j = p :=
    fun h hi hj => hI.unique h (c_on h).1 (c_on h).2 hi hj
  have basis_iff : ∀ {i j l : L}, i ≠ j → i ≠ l → (Basis on i j l ↔ c i j ≠ c i l) := by
    intro i j l hj hl
    constructor
    · rintro ⟨-, -, -, hno⟩ e
      exact hno ⟨c i j, (c_on hj).1, (c_on hj).2, e ▸ (c_on hl).2⟩
    · intro hne
      refine ⟨hj, hl, fun e => hne (by subst e; rfl), fun ⟨p, pi, pj, pl⟩ => hne ?_⟩
      rw [c_eq hj pi pj, c_eq hl pi pl]
  -- at each line, apply the rank-2 lemma to the other lines
  have local_i : ∀ i, ∃ (s : ZMod 2) (ε : L → ZMod 2), ∀ j l, Basis on i j l →
      χ' (σ i) (σ j) (σ l) = χ i j l + s + ε j + ε l := by
    intro i
    let V := {j : L // i ≠ j}
    let φ : V → V → ZMod 2 := fun j l => χ' (σ i) (σ j) (σ l) + χ i j l
    have hsym : ∀ j l, φ l j = φ j l := fun j l => by
      simp only [φ]; rw [a23 i, a23' (σ i)]
      linear_combination (norm := (ring_nf; reduce_mod_char))
    have h4 : ∀ j k l m : V, c i j ≠ c i l → c i j ≠ c i m → c i k ≠ c i l → c i k ≠ c i m →
        φ j l + φ j m + φ k l + φ k m = 0 := by
      intro j k l m h1 h2 h3 h4
      have e := H i j k l m ((basis_iff j.2 l.2).2 h1) ((basis_iff j.2 m.2).2 h2)
        ((basis_iff k.2 l.2).2 h3) ((basis_iff k.2 m.2).2 h4)
      simp only [φ]
      linear_combination (norm := (ring_nf; reduce_mod_char)) e
    -- three vertices on `i`, and a second line through each
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := hbf i
    obtain ⟨jp, hjp, pjp⟩ := hI.two hp
    obtain ⟨jq, hjq, qjq⟩ := hI.two hq
    obtain ⟨jr, hjr, rjr⟩ := hI.two hr
    have cp := c_eq (Ne.symm hjp) hp pjp
    have cq := c_eq (Ne.symm hjq) hq qjq
    have cr := c_eq (Ne.symm hjr) hr rjr
    obtain ⟨s, ε, hε⟩ := const_add_cut (cls := fun j : V => c i j) hsym h4
      (p := ⟨jp, Ne.symm hjp⟩) (q := ⟨jq, Ne.symm hjq⟩) (r := ⟨jr, Ne.symm hjr⟩)
      (by simp only [cp, cq]; exact hpq) (by simp only [cq, cr]; exact hqr)
      (by simp only [cp, cr]; exact hpr)
    refine ⟨s, fun j => if h : i ≠ j then ε ⟨j, h⟩ else 0, fun j l hB => ?_⟩
    have hj := hB.1; have hl := hB.2.1
    have := hε ⟨j, hj⟩ ⟨l, hl⟩ ((basis_iff hj hl).1 hB)
    simp only [φ, ne_eq, hj, hl, not_false_eq_true, ↓reduceDIte] at this ⊢
    linear_combination (norm := (ring_nf; reduce_mod_char)) this
  choose s ε hε using local_i
  exact ⟨s, ε, hε⟩

/-- **Steps 1–4, from the cyclic orders to the reorientation.** In a bigon-free incidence
structure, two alternating chirotopes with the same separation relation along every line differ
by a reorientation. Only Folkman–Lawrence, from the reorientation to a homeomorphism, and the
reading of the separation relation on an actual arrangement, are left outside. -/
theorem reorientation_of_sameSeparation (hI : Incidence on) (hbf : BigonFree on)
    {χ χ' : L → L → L → ZMod 2} {σ : L → L}
    (a12 : ∀ i j l, χ j i l = χ i j l + 1) (a23 : ∀ i j l, χ i l j = χ i j l + 1)
    (a12' : ∀ i j l, χ' j i l = χ' i j l + 1) (a23' : ∀ i j l, χ' i l j = χ' i j l + 1)
    (H : SameSeparation (on := on) χ χ' σ) :
    ∃ r : L → ZMod 2, ∀ i j l, Basis on i j l →
      χ' (σ i) (σ j) (σ l) = χ i j l + r i + r j + r l :=
  reorientation_of_locallyEquivalent hI hbf a12 a23 a12' a23'
    (locallyEquivalent_of_sameSeparation hI hbf a23 a23' H)

end Grothendieck.Folder80Signs
