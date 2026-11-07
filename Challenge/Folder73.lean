module

public import Mathlib

@[expose] public section

namespace Folder73

open Matrix

variable {k : Type*}

section Polygon

variable [Field k] {n : ℕ} [NeZero n]

/-- The multipliers of an `n`-gon given by its sides (page 25, the relation `(∗)`):
`λ_i u_{i-1} - λ_{i+1}(u_i + u_{i+1}) + λ_{i+2} u_{i+2} = 0` for all `i`. -/
def IsMult (u : ZMod n → Fin 2 → k) (l : ZMod n → k) : Prop :=
  ∀ i, l i • u (i - 1) - l (i + 1) • (u i + u (i + 1)) + l (i + 2) • u (i + 2) = 0

end Polygon

section EarArea

variable [Field k] {n : ℕ} [NeZero n]

/-- The space `N(u_*)` of multipliers. -/
def multSpace (u : ZMod n → Fin 2 → k) : Submodule k (ZMod n → k) where
  carrier := {l | IsMult u l}
  add_mem' {a b} ha hb i := by
    have h := congrArg₂ (· + ·) (ha i) (hb i)
    simp only [add_zero] at h
    rw [← h]
    simp only [Pi.add_apply, add_smul]
    abel
  zero_mem' i := by simp
  smul_mem' c a ha i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← smul_sub, ← smul_add, ha i, smul_zero]

variable (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)

include hu

end EarArea

section FourCases

variable [Field k] {n : ℕ} [NeZero n] (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)

include hu

/-- **Page 28, the Théorème: the four cases** (`|k| > n`). -/
theorem four_cases (hk : (n : ℕ∞) < ENat.card k) :
    multSpace u = ⊥ ∨
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧ Module.finrank k (multSpace u) = 1) ∨
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧ Module.finrank k (multSpace u) = 2) ∨
      (multSpace u ≠ ⊥ ∧ (∃ i, ∀ l ∈ multSpace u, l i = 0) ∧
        Module.finrank k (multSpace u) = 1) := by
  sorry

end FourCases

end Folder73
