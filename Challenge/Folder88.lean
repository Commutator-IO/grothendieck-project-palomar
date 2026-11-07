module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Grothendieck.Folder88

open Equiv

section Ordre

variable {W R I : Type*} [Group W] [MulAction W R]

/-- The data of the reading: a `W`-torsor `R` and `φ : R × I → W` with a)
`φ(w r, i) = w φ(r, i) w⁻¹` and `φ(r, i)² = 1`. -/
structure Epinglage (W R I : Type*) [Group W] [MulAction W R] where
  /-- `φ(r, i)`, the simple reflection of index `i` for the base `r`. -/
  φ : R → I → W
  /-- a) `φ(w r, i) = int(w) φ(r, i)`. -/
  equivariant : ∀ (w : W) r i, φ (w • r) i = w * φ r i * w⁻¹
  /-- `φ(r, i)² = 1`. -/
  involution : ∀ r i, φ r i * φ r i = 1
  /-- `W` acts freely on `R`. -/
  libre : ∀ (w : W) (r : R), w • r = r → w = 1
  /-- `W` acts transitively on `R`. -/
  transitif : ∀ r r' : R, ∃ w : W, w • r = r'

variable (E : Epinglage W R I) (n : ℕ)

/-- `Rep'(I) = Bij([1, ℓ], I)`, with `ℓ = n + 2` and `[1, ℓ]` written
`Fin (n + 2)` (position `k` of the reading is `k - 1` here). -/
abbrev Rep' (n : ℕ) (I : Type*) := Fin (n + 2) ≃ I

/-- The position `ℓ`. -/
def dernier : Fin (n + 2) := Fin.last (n + 1)

/-- The position `ℓ - 1`. -/
def avantDernier : Fin (n + 2) := (Fin.last n).castSucc

/-- `τ_{ℓ-1}`, the transposition of `ℓ - 1` and `ℓ`. -/
def τ : Perm (Fin (n + 2)) := swap (avantDernier n) (dernier n)

/-- `σ_{ℓ-2}(r, u) = (r, u ∘ τ_{ℓ-1})`. -/
def sigmaAvant : Perm (R × Rep' n I) :=
  Function.Involutive.toPerm (fun x => (x.1, (τ n).trans x.2)) fun x => by
    ext k <;> simp [τ, swap_apply_self]

@[simp] theorem sigmaAvant_apply (x : R × Rep' n I) :
    sigmaAvant n x = (x.1, (τ n).trans x.2) := rfl

theorem sigmaDernier_aux (r : R) (i : I) :
    E.φ (E.φ r i • r) i • E.φ r i • r = r := by
  rw [E.equivariant, mul_inv_cancel_right, smul_smul, E.involution, one_smul]

/-- `σ_{ℓ-1}(r, u) = (φ(r, u(ℓ)) · r, u)`. -/
def sigmaDernier : Perm (R × Rep' n I) :=
  Function.Involutive.toPerm (fun x => (E.φ x.1 (x.2 (dernier n)) • x.1, x.2)) fun x => by
    simp only [sigmaDernier_aux]

@[simp] theorem sigmaDernier_apply (x : R × Rep' n I) :
    sigmaDernier E n x = (E.φ x.1 (x.2 (dernier n)) • x.1, x.2) := rfl

variable [Fintype I] [DecidableEq I]

/-- `ν`, the lcm of the `n_{ij}`, `i ≠ j`, computed at a base `r₀`. -/
noncomputable def nu (r₀ : R) : ℕ :=
  ((Finset.univ : Finset (I × I)).filter (fun p => p.1 ≠ p.2)).lcm
    fun p => orderOf (E.φ r₀ p.1 * E.φ r₀ p.2)

/-- **Proposition** (page 8). For `ℓ = n + 2 = Card I` and `R` non-empty, the
order of `σ_{ℓ-2} σ_{ℓ-1}` on `R × Rep'(I)` is `2ν`. -/
theorem proposition_ordre (r₀ : R) (e : Rep' n I) :
    orderOf (sigmaAvant n * sigmaDernier E n) = 2 * nu E r₀ := by
  sorry

end Ordre

end Grothendieck.Folder88
