module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder154

/-- The signs read along a line are valid: not all zero, and of the form `a … a (x) −a … −a`
with `a = ±1`, the middle `x` (at position `c`) being `a`, `0` or `−a`: that is
`+ … + (0) − … −` up to reversal, with at most one zero. -/
def ValidSeq {n : ℕ} (s : Fin n → SignType) : Prop :=
  (∃ i, s i ≠ 0) ∧ ∃ a : SignType, a ≠ 0 ∧ ∃ c : ℕ,
    (∀ i : Fin n, (i : ℕ) < c → s i = a) ∧ (∀ i : Fin n, c < (i : ℕ) → s i = -a)

/-- The combinatorial data of an arrangement `Σ`: vertices `V` (one representative cocircuit
for each antipodal pair), lines `L`; line `ℓ` carries the vertices `vert ℓ 0, …` in the order
of its double cover from a base point, `ori ℓ i = ±1` comparing the representative of
`vert ℓ i` with the orientation of `ℓ`. -/
structure Arrangement (V : Type*) (L : Type*) where
  /-- The number of vertices on a line. -/
  len : L → ℕ
  /-- The vertices of a line, in order. -/
  vert : (ℓ : L) → Fin (len ℓ) → V
  vert_injective : ∀ ℓ, Function.Injective (vert ℓ)
  /-- The sign correcting the chosen representative of each vertex along the line. -/
  ori : (ℓ : L) → Fin (len ℓ) → SignType
  ori_ne_zero : ∀ ℓ i, ori ℓ i ≠ 0

/-- `σ` is a specialisation of `τ` (`τ` a generisation of `σ`): `τ = σ` wherever `σ ≠ 0`. -/
def Spec {X : Type*} (σ τ : X → SignType) : Prop := ∀ x, σ x ≠ 0 → τ x = σ x

namespace Arrangement

variable {V L : Type*} (A : Arrangement V L)

/-- The signs of a signature read along the line `ℓ`. -/
def restr (σ : V → SignType) (ℓ : L) : Fin (A.len ℓ) → SignType :=
  fun i => A.ori ℓ i * σ (A.vert ℓ i)

/-- A position of an added pseudoline: a cocircuit signature valid on every line of `Σ`
(Las Vergnas's criterion, with the edition's exclusion of the lines of `Σ` themselves). -/
def IsPosition (σ : V → SignType) : Prop := ∀ ℓ, ValidSeq (A.restr σ ℓ)

variable {A}

/-- The generisations of the position `σ_D`. -/
abbrev Gen (A : Arrangement V L) (σD : V → SignType) :=
  {σ : V → SignType // A.IsPosition σ ∧ Spec σD σ}

end Arrangement

namespace Arrangement

variable {V L : Type*} [Fintype V] {A : Arrangement V L} {σD : V → SignType}

/-- The generisations of `D`: `3^ν`, one for each face of the `ν`-cube, `ν` the number of
vertices through which `D` passes. -/
theorem card_gen (hD : A.IsPosition σD) :
    Nat.card (A.Gen σD) = 3 ^ Fintype.card {v // σD v = 0} := by
  sorry

end Arrangement

end Grothendieck.Folder154
