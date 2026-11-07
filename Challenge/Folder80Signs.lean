module

public import Challenge.Folder80Maps3

@[expose] public section

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

/-- The two chirotopes have the same separation relation along every line: what an isomorphism
of labelled skeleta gives, the cyclic order of the vertices along `i` being kept up to
reversal. -/
def SameSeparation (χ χ' : L → L → L → ZMod 2) (σ : L → L) : Prop :=
  ∀ i j k l m, Basis on i j l → Basis on i j m → Basis on i k l → Basis on i k m →
    χ' (σ i) (σ j) (σ l) + χ' (σ i) (σ j) (σ m) + χ' (σ i) (σ k) (σ l) + χ' (σ i) (σ k) (σ m) =
      χ i j l + χ i j m + χ i k l + χ i k m

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
      χ' (σ i) (σ j) (σ l) = χ i j l + r i + r j + r l := by
  sorry

end Grothendieck.Folder80Signs
