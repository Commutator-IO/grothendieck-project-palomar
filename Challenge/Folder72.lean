module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder72

universe u

variable {R : Type u} [CommRing R]

variable (n : ℕ) (μ β : ℕ → R)

/-- The coordinate of index `k`, zero beyond `n + 1`. -/
def co (k : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  if h : k < n + 2 then LinearMap.proj (⟨k, h⟩ : Fin (n + 2)) else 0

/-- The basis vector `e_k` (`e₀ = s₀`, `e_{i+1} = aᵢ`). -/
def e (k : ℕ) : Fin (n + 2) → R := fun j => if (j : ℕ) = k then 1 else 0

/-- The form `a'ᵢ`: `⟨a_{i−1}, a'ᵢ⟩ = 1`, `⟨aᵢ, a'ᵢ⟩ = μᵢ`, `⟨a_{i+1}, a'ᵢ⟩ = βᵢ`. -/
def F (i : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  co n i + μ i • co n (i + 1) + β i • co n (i + 2)

/-- The pseudo-reflection `τᵢ = id + a'ᵢ ⊗ aᵢ`. -/
def τ (i : ℕ) : Module.End R (Fin (n + 2) → R) :=
  1 + (F n μ β i).smulRight (e n (i + 1))

variable {n}

/-- `(y_{top−m}, y_{top−m+1})` for the solution of `F_k y = 0` (`k < top`) with
`y_top = 1`, `y_k = 0` for `k > top`. -/
def cc (top : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => (-(μ (top - 1 - m) * (cc top m).1 + β (top - 1 - m) * (cc top m).2), (cc top m).1)

/-- The coordinates of the back-substituted vector with top index `top`. -/
def y (top k : ℕ) : R := if k ≤ top then (cc μ β top (top - k)).1 else 0

variable {μ β}

variable (μ β) in
/-- The vector with coordinates `y top`. -/
def vec (top : ℕ) : Fin (n + 2) → R := fun j => y μ β top j

variable (n μ β)

/-- `c̃`: killed by every `a'ᵢ`, coordinate `1` on `aₙ`. -/
def ct : Fin (n + 2) → R := vec μ β (n + 1)

variable {n μ β}

section Invariant

/-- `Z'ᵢ = H₀ ∩ ⋯ ∩ Hᵢ`. -/
def Zp (n : ℕ) (μ β : ℕ → R) (i : ℕ) : Submodule R (Fin (n + 2) → R) where
  carrier := {x | ∀ k ≤ i, F n μ β k x = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- `Z*ᵢ = Lin(h_{i+1}, …, hₙ) = Lin(e_{i+2}, …, e_{n+1})`. -/
def Zs (n : ℕ) (i : ℕ) : Submodule R (Fin (n + 2) → R) where
  carrier := {x | ∀ k ≤ i + 1, co n k x = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- The hyperplane at infinity `C`, `π = 0`. -/
def Vh (n : ℕ) : Submodule R (Fin (n + 2) → R) := LinearMap.ker (co n 0)

/-- Stability under all the `τᵢ`. -/
def Invariant (n : ℕ) (μ β : ℕ → R) (W : Submodule R (Fin (n + 2) → R)) : Prop :=
  ∀ i ≤ n, ∀ w ∈ W, τ n μ β i w ∈ W

variable {K : Type u} [Field K] {μ' β' : ℕ → K}

/-- **Page 79.** The subspaces stable under all the `τᵢ`. -/
theorem invariant_iff (W : Submodule K (Fin (n + 2) → K)) :
    Invariant n μ' β' W ↔
      W = ⊥ ∨ W = ⊤ ∨ W = K ∙ ct n μ' β' ∨ W = Vh n ∨
        ∃ i < n, β' i = 0 ∧ (W = Zp n μ' β' i ∨ W = Zs n i) := by
  sorry

end Invariant

end Grothendieck.Folder72
