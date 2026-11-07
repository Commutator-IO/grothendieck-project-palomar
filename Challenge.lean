module

public import Mathlib

/-!
# The Challenge: the orders of the tangent line bundles on `M_{0,n}`

The two theorems of `Grothendieck/Folder146.lean` cited by the article « The tangent line at a
marked point on `M_{0,n}/𝔖_{n−1}`, after a table of Grothendieck », in the homogeneous model of
`M_{0,n}(K)`: configurations `v` of `n` vectors of `K²` giving distinct points of `ℙ¹(K)`
(`Conf`), and functions of weight on them. `TrivL K n m` says that `L^{⊗m}`,
`L = L₁ ⊗ ⋯ ⊗ Lₙ`, has an equivariant trivialisation; `TrivLi K k m` says the same for
`Lₙ^{⊗m}`, `n = k + 1`, under the stabiliser of the `n`-th point.

* `trivL_iff`: over a field with a primitive `(n − 1)`-th root of unity, `n ≥ 2`, `TrivL K n m`
  holds iff `(n − 1) ∣ m`.
* `trivLi_iff`: over a field with primitive roots of unity of orders `n − 1` and `n − 2`,
  `n ≥ 3`, `TrivLi K (n − 1) m` holds iff `(n − 1)(n − 2) ∣ m`.

The definitions are copied verbatim from the library under the same names. This file imports
only Mathlib, so that it compiles on its own.
-/

@[expose] public section

namespace Grothendieck.Folder146

variable {K : Type*} [Field K]

/-- The bracket `[v w] = v₁w₂ − v₂w₁`: it vanishes iff `v` and `w` give the same point of
`ℙ¹(K)` (or one of them is zero). -/
def br (v w : K × K) : K := v.1 * w.2 - v.2 * w.1

/-- The linear substitution `(x, y) ↦ (ax + by, cx + dy)`. -/
def lin (a b c d : K) (v : K × K) : K × K := (a * v.1 + b * v.2, c * v.1 + d * v.2)

/-- `n` vectors of `K²` giving `n` distinct points of `ℙ¹(K)`. -/
def Conf {n : ℕ} (v : Fin n → K × K) : Prop := ∀ i j, i ≠ j → br (v i) (v j) ≠ 0

variable (K) in
/-- An equivariant trivialisation of `L^{⊗m}`, `L = L₁ ⊗ ⋯ ⊗ Lₙ`, on `M_{0,n}(K)`. -/
def TrivL (n : ℕ) (m : ℤ) : Prop :=
  ∃ F : (Fin n → K × K) → K, ∀ v, Conf v → F v ≠ 0 ∧
    (∀ t : Fin n → K, (∀ i, t i ≠ 0) → F (fun i => t i • v i) = (∏ i, t i) ^ (2 * m) * F v) ∧
    (∀ a b c d : K, a * d - b * c ≠ 0 →
      F (fun i => lin a b c d (v i)) = (a * d - b * c) ^ (m * n) * F v) ∧
    ∀ σ : Equiv.Perm (Fin n), F (v ∘ σ) = F v

variable (K) in
/-- An equivariant trivialisation of `Lₙ^{⊗m}` on `M_{0,n}(K)`, `n = k + 1`, under the
stabiliser `𝔖_k` of the `n`-th point `p`; `v` are the `k` other points. -/
def TrivLi (k : ℕ) (m : ℤ) : Prop :=
  ∃ F : K × K → (Fin k → K × K) → K, ∀ p v, Conf v → (∀ i, br p (v i) ≠ 0) → F p v ≠ 0 ∧
    (∀ (s : K) (t : Fin k → K), s ≠ 0 → (∀ i, t i ≠ 0) →
      F (s • p) (fun i => t i • v i) = s ^ (2 * m) * F p v) ∧
    (∀ a b c d : K, a * d - b * c ≠ 0 →
      F (lin a b c d p) (fun i => lin a b c d (v i)) = (a * d - b * c) ^ m * F p v) ∧
    ∀ σ : Equiv.Perm (Fin k), F p (v ∘ σ) = F p v

/-- The general formula for `L`: over a field with a primitive `(n − 1)`-th root of unity, `n ≥ 2`,
`L^{⊗m}` is equivariantly trivial on `M_{0,n}` iff `(n − 1) ∣ m` (énoncé de l'édition). -/
theorem trivL_iff {n : ℕ} (hn : 2 ≤ n) {ω : K} (hω : IsPrimitiveRoot ω (n - 1)) (m : ℤ) :
    TrivL K n m ↔ ((n - 1 : ℕ) : ℤ) ∣ m := by
  sorry

/-- The general formula for `L_i`: over a field with primitive roots of unity of orders `n − 1`
and `n − 2`, `n ≥ 3`, `Lₙ^{⊗m}` is equivariantly trivial on `M_{0,n}` under the stabiliser of
the `n`-th point iff `(n − 1)(n − 2) ∣ m` (énoncé de l'édition). -/
theorem trivLi_iff {n : ℕ} (hn : 3 ≤ n) {ω ζ : K} (hω : IsPrimitiveRoot ω (n - 1))
    (hζ : IsPrimitiveRoot ζ (n - 2)) (m : ℤ) :
    TrivLi K (n - 1) m ↔ (((n - 1) * (n - 2) : ℕ) : ℤ) ∣ m := by
  sorry

end Grothendieck.Folder146

end
