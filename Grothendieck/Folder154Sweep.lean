module

public import Mathlib

@[expose] public section


/-!
# Folder 154, pages 142, 144, 145: one half-sweep of seven pseudolines, written twice

Finding `154-sweep-142-144-same` (`src/content/findings.ts`).

**What is encoded, and whose it is.**
* The crossings of the wiring diagram at the top right of page 142 are read off the machine redraw
  `transcripts/154/drawings/08-2.tex` (overlay-checked against the scan, not checked by a reader):
  seven strands leave in the order `A … G`, and the dotted crossings are, from the top down,
  `D/E, F/G, D/G, E/G, C/G, B/G, B/C, B/E, C/E, B/D, C/D, B/F, G/A` (`crossings142`).
  The redraw gives them as pairs of strands; the word in adjacent transpositions (`word142`) is
  the edition's translation, and the theorem `pairs_word142` checks that it crosses exactly these
  pairs in this order.
* The ten rows of page 144, from `A B C D E F G` to `G A E D C F B` (`table144`), are the
  transcription's (batch 8), row `9′` read `A G E C D B F` (the parenthesis `(A G)` taken as the two
  letters in that order — the edition's reading).
* The generator word of page 145, `σ₃ σ₄ σ₅ σ₂ σ₆ σ₁ σ₅ σ₃ σ₆ …`, is the transcription's; its ninth
  term `σ₆` is marked uncertain there. The convention that `σᵢ` exchanges the strands in *places*
  `i` and `i + 1` (not the letters) is the reading's.

A state of the sweep is a permutation `st : Perm (Fin 7)`, `st p` being the strand in place `p`
(strands `A = 0, …, G = 6`, places `0, …, 6`); `σᵢ` acts on the right, `st ↦ st * swap (i−1) i`.

**Results.**
* `pairs_word142`, `run_word142`: the redraw's 13 crossings are adjacent transpositions, in this
  order, and end at `G A E D C F B`;
* `table144_eq_states`: the ten rows of page 144 are states of that same sweep, after
  `0, 2, 3, 4, 5, 6, 7, 8, 10, 13` of its crossings — between two rows, the crossings are those of
  the row, made one after the other (`D/E` and `F/G`; `C/E` and `B/D`; `C/D`, `B/F` and `G/A` being
  made at once on the page): the table and the diagram are the same sweep;
* `inv_run_le_length`: any word in the `σᵢ` reaching a permutation has at least as many letters as
  the permutation has inversions (general, by induction: one adjacent transposition changes the
  inversions by at most one, `inv_mul_adjSwap_le`); hence `isReduced_of_inv_eq`;
* `inv_run_word142`, `isReduced_word142`: the 13 crossings are reduced (13 = number of inversions
  of `G A E D C F B`); `uncrossed142`: the pairs never crossed are exactly
  `A/B, A/C, A/D, A/E, A/F, C/F, D/F, E/F` (8 = 21 − 13), each crossed pair crossed once;
* `isReduced_word145_8`, `word145_9_crosses_CF_twice`, `not_isReduced_word145_9`: the first eight
  terms of the word of page 145 are reduced; with the ninth term `σ₆`, read as uncertain, the
  strands `C` and `F` cross a second time (at the third and ninth crossings) and the word is no
  longer reduced: `σ₃ σ₂ σ₁ σ₄ σ₃ σ₆ σ₅` (7 letters) gives the same permutation.

The pairs listed by the finding are as stated; nothing in it needed correcting. Not formalised:
the wiring diagram of page 144 (redraw 08-18), whose wires are not identified with letters.
-/

namespace Grothendieck.Folder154Sweep

open Equiv

/-- The strands, named as on the pages. -/
abbrev A : Fin 7 := 0
abbrev B : Fin 7 := 1
abbrev C : Fin 7 := 2
abbrev D : Fin 7 := 3
abbrev E : Fin 7 := 4
abbrev F : Fin 7 := 5
abbrev G : Fin 7 := 6

/-- The generator `σᵢ` (`1 ≤ i ≤ 6`), the transposition of the places `i − 1` and `i` (places
counted from `0`); any other index gives the identity. -/
def sig (i : ℕ) : Perm (Fin 7) :=
  if h : 1 ≤ i ∧ i < 7 then swap ⟨i - 1, by omega⟩ ⟨i, h.2⟩ else 1

/-- The state reached from `A B C D E F G` by the word `w`, the letters applied left to right. -/
def run (w : List ℕ) : Perm (Fin 7) := (w.map sig).prod

/-- The pairs of strands crossed by the word `w` from the state `st`, in order. -/
def pairs : List ℕ → Perm (Fin 7) → List (Sym2 (Fin 7))
  | [], _ => []
  | i :: w, st => s(st ⟨min (i - 1) 6, by omega⟩, st ⟨min i 6, by omega⟩) :: pairs w (st * sig i)

/-- The row read off a state: the strands in places `0, …, 6`. -/
def row (st : Perm (Fin 7)) : List (Fin 7) := List.ofFn st

/-- The state after the first `k` letters of `w`. -/
def stateAfter (w : List ℕ) (k : ℕ) : Perm (Fin 7) := run (w.take k)

/-- The number of inversions: pairs of places `p < q` whose strands are in the reverse order. -/
def inv {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun x => x.1 < x.2 ∧ σ x.2 < σ x.1)).card

/-- A word is reduced when no word reaching the same permutation is shorter. -/
def IsReduced (w : List ℕ) : Prop := ∀ w' : List ℕ, run w' = run w → w.length ≤ w'.length

/-! ## The general bound: a word has at least as many letters as inversions -/

/-- The adjacent transposition `swap k (k+1)` keeps the order of every pair of places other than
`(k, k+1)`. -/
lemma adjSwap_lt {n : ℕ} (k : ℕ) (hk : k + 1 < n) (p q : Fin n) (hpq : p < q)
    (hne : ¬ ((p : ℕ) = k ∧ (q : ℕ) = k + 1)) :
    swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ p < swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ q := by
  have hpq' : (p : ℕ) < q := hpq
  rw [Fin.lt_def]
  rw [swap_apply_def, swap_apply_def]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

/-- One adjacent transposition adds at most one inversion. -/
theorem inv_mul_adjSwap_le {n : ℕ} (σ : Perm (Fin n)) (k : ℕ) (hk : k + 1 < n) :
    inv (σ * swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) ≤ inv σ + 1 := by
  classical
  set s : Perm (Fin n) := swap ⟨k, by omega⟩ ⟨k + 1, hk⟩ with hs
  set S := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun x => x.1 < x.2 ∧ (σ * s) x.2 < (σ * s) x.1)
  set T := (Finset.univ : Finset (Fin n × Fin n)).filter (fun x => x.1 < x.2 ∧ σ x.2 < σ x.1)
  set e : Fin n × Fin n := (⟨k, by omega⟩, ⟨k + 1, hk⟩)
  have h1 : (S.erase e).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun x => (s x.1, s x.2)) ?_ ?_
    · intro x hx
      have hx' : x ∈ S.erase e := hx
      rw [Finset.mem_erase] at hx'
      obtain ⟨hne, hxS⟩ := hx'
      have hxS' : x.1 < x.2 ∧ (σ * s) x.2 < (σ * s) x.1 := (Finset.mem_filter.1 hxS).2
      show (s x.1, s x.2) ∈ T
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, adjSwap_lt k hk x.1 x.2 hxS'.1 ?_, hxS'.2⟩
      rintro ⟨h1, h2⟩
      exact hne (Prod.ext (Fin.ext h1) (Fin.ext h2))
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (s.injective hxy.1) (s.injective hxy.2)
  have h2 : S.card - 1 ≤ (S.erase e).card := Finset.pred_card_le_card_erase
  show S.card ≤ T.card + 1
  omega

lemma inv_mul_sig_le (σ : Perm (Fin 7)) (i : ℕ) : inv (σ * sig i) ≤ inv σ + 1 := by
  unfold sig
  split_ifs with h
  · have := inv_mul_adjSwap_le σ (i - 1) (by omega)
    have e : (⟨i - 1 + 1, by omega⟩ : Fin 7) = ⟨i, h.2⟩ := Fin.ext (by simp; omega)
    rw [e] at this
    exact this
  · simp

lemma inv_one {n : ℕ} : inv (1 : Perm (Fin n)) = 0 := by
  rw [inv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ h
  exact lt_asymm h.1 h.2

/-- A word reaching `σ` has at least `inv σ` letters (from any start, by induction). -/
theorem inv_mul_prod_le (σ : Perm (Fin 7)) (w : List ℕ) :
    inv (σ * (w.map sig).prod) ≤ inv σ + w.length := by
  induction w generalizing σ with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ← mul_assoc]
    have := ih (σ * sig i)
    have := inv_mul_sig_le σ i
    omega

theorem inv_run_le_length (w : List ℕ) : inv (run w) ≤ w.length := by
  have := inv_mul_prod_le 1 w
  simpa [run, inv_one] using this

/-- A word with as many letters as its permutation has inversions is reduced. -/
theorem isReduced_of_inv_eq {w : List ℕ} (h : inv (run w) = w.length) : IsReduced w :=
  fun w' hw' => h ▸ hw' ▸ inv_run_le_length w'

/-! ## Page 142: the wiring diagram (redraw 08-2) -/

/-- The crossings of the wiring diagram of page 142, from the top down, as read off redraw 08-2. -/
def crossings142 : List (Sym2 (Fin 7)) :=
  [s(D, E), s(F, G), s(D, G), s(E, G), s(C, G), s(B, G), s(B, C), s(B, E), s(C, E), s(B, D),
    s(C, D), s(B, F), s(G, A)]

/-- The same crossings as a word in the `σᵢ` (the edition's translation). -/
def word142 : List ℕ := [4, 6, 5, 4, 3, 2, 3, 4, 3, 5, 4, 6, 1]

/-- Each crossing of the redraw is an adjacent transposition: the word crosses exactly the
redraw's pairs, in the redraw's order. -/
theorem pairs_word142 : pairs word142 1 = crossings142 := by decide

/-- The strands arrive in the order `G A E D C F B`. -/
theorem run_word142 : row (run word142) = [G, A, E, D, C, F, B] := by decide

theorem inv_run_word142 : inv (run word142) = 13 := by decide

theorem isReduced_word142 : IsReduced word142 :=
  isReduced_of_inv_eq (by rw [inv_run_word142]; rfl)

/-- The 8 pairs that the half-sweep leaves uncrossed. -/
def uncrossed142 : List (Sym2 (Fin 7)) :=
  [s(A, B), s(A, C), s(A, D), s(A, E), s(A, F), s(C, F), s(D, F), s(E, F)]

/-- Each crossed pair is crossed once, and a pair of distinct strands is crossed if and only if it
is not one of the 8 pairs `A/B, A/C, A/D, A/E, A/F, C/F, D/F, E/F`. -/
theorem uncrossed142_spec :
    crossings142.Nodup ∧ crossings142.length = 13 ∧ uncrossed142.length = 8 ∧
      ∀ a b : Fin 7, a < b → (s(a, b) ∈ crossings142 ↔ s(a, b) ∉ uncrossed142) := by
  decide

/-! ## Page 144: the table of permutations -/

/-- The ten rows of page 144, from the start `A B C D E F G` (row `1′`) to the end row. -/
def table144 : List (List (Fin 7)) :=
  [[A, B, C, D, E, F, G],
   [A, B, C, E, D, G, F],
   [A, B, C, E, G, D, F],
   [A, B, C, G, E, D, F],
   [A, B, G, C, E, D, F],
   [A, G, B, C, E, D, F],
   [A, G, C, B, E, D, F],
   [A, G, C, E, B, D, F],
   [A, G, E, C, D, B, F],
   [G, A, E, D, C, F, B]]

/-- The rows of page 144 are states of the sweep of page 142, after `0, 2, 3, 4, 5, 6, 7, 8, 10`
and `13` of its crossings: the table is the same sweep, the crossings `D/E, F/G`, then `C/E, B/D`,
then `C/D, B/F, G/A` being made at once. -/
theorem table144_eq_states :
    table144 = [0, 2, 3, 4, 5, 6, 7, 8, 10, 13].map (fun k => row (stateAfter word142 k)) := by
  decide

/-! ## Page 145: the generator word -/

/-- The first eight terms of the word of page 145. -/
def word145_8 : List ℕ := [3, 4, 5, 2, 6, 1, 5, 3]

/-- The first nine terms, the ninth `σ₆` being read as uncertain. -/
def word145_9 : List ℕ := word145_8 ++ [6]

theorem isReduced_word145_8 : IsReduced word145_8 :=
  isReduced_of_inv_eq (by decide)

/-- With the ninth term, `C` and `F` cross a second time (third and ninth crossings). -/
theorem word145_9_crosses_CF_twice :
    (pairs word145_9 1)[2]? = some s(C, F) ∧ (pairs word145_9 1)[8]? = some s(F, C) := by
  decide

/-- The nine terms are not reduced: seven letters give the same permutation. -/
theorem not_isReduced_word145_9 : ¬ IsReduced word145_9 := fun h => by
  have := h [3, 2, 1, 4, 3, 6, 5] (by decide)
  simp [word145_9, word145_8] at this

end Grothendieck.Folder154Sweep
