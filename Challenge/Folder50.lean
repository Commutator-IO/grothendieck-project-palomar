module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder50

open Polynomial Finset

/-- The frame of pages 6–10 at one object and one class `ξ` with `φ_ξ` a
`ℚ`-isomorphism, transported to `E = End(A)` by `ψ(η) = φ_ξ⁻¹ φ_η`; the star is
the Rosati involution. -/
structure Frame (E N : Type*) [Ring E] [StarRing E] [AddCommGroup N] (r : ℕ) where
  /-- `η ↦ φ_ξ⁻¹ φ_η`. -/
  ψ : N →+ E
  ψ_injective : Function.Injective ψ
  /-- The classes are antisymmetric, so their images are Rosati-symmetric. -/
  star_ψ : ∀ η, star (ψ η) = ψ η
  /-- The pullback `α*η`. -/
  pb : E → N → N
  ψ_pb : ∀ α η, ψ (pb α η) = star α * ψ η * α
  /-- The class `ξ`. -/
  ξ : N
  ψ_ξ : ψ ξ = 1
  /-- The intersection form of (e). -/
  I : MultilinearMap ℤ (fun _ : Fin r => N) ℤ
  /-- The degree of (e) 3). -/
  ν : E → ℤ
  I_pb : ∀ u (v : Fin r → N), I (fun i => pb u (v i)) = ν u * I v
  I_ξ : I (fun _ => ξ) ≠ 0

namespace Frame

variable {E N : Type*} [Ring E] [StarRing E] [AddCommGroup N] {r : ℕ} (F : Frame E N r)

/-- `D_ξ(α, β) = (α + β)*ξ − α*ξ − β*ξ`. -/
def D (α β : E) : N := F.pb (α + β) F.ξ - F.pb α F.ξ - F.pb β F.ξ

/-- `D_ξ(α) = D_ξ(α, 1)`. -/
def Dξ (α : E) : N := F.D α 1

/-- The weight of each summand of `(α + n)*ξ = n²ξ + n D_ξ(α) + α*ξ`. -/
def wt : Fin 3 → ℕ := ![2, 1, 0]

/-- The three summands. -/
def sel (α : E) : Fin 3 → N := ![F.ξ, F.Dξ α, F.pb α F.ξ]

/-- The polynomial `P` with `P(n) = ν(α + n)`, over `ℚ`. -/
noncomputable def charPoly (α : E) : ℚ[X] :=
  C ((F.I fun _ => F.ξ : ℤ) : ℚ)⁻¹ *
    ∑ f : Fin r → Fin 3, C ((F.I fun i => F.sel α (f i) : ℤ) : ℚ) * X ^ (∑ i, wt (f i))

/-- `σᵢ(α)`, the coefficient of `n^{2r − i}` in `ν(α + n)`. -/
noncomputable def σ (i : ℕ) (α : E) : ℚ := (F.charPoly α).coeff (2 * r - i)

/-- `tr(α) = σ₁(α)`. -/
noncomputable def tr (α : E) : ℚ := F.σ 1 α

/-- **The trace formula** (head of page 8), for a symmetric intersection form:
`tr(α) · I(ξ^r) = r · I(ξ^{r−1}, D_ξ(α))`. -/
theorem tr_mul_I {m : ℕ} (F : Frame E N (m + 1))
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → N), F.I (v ∘ σ) = F.I v)
    (α : E) :
    F.tr α * ((F.I fun _ => F.ξ : ℤ) : ℚ) =
      (m + 1) * ((F.I (Function.update (fun _ => F.ξ) 0 (F.Dξ α)) : ℤ) : ℚ) := by
  sorry

end Frame

namespace ModelA

/-- `E = N = ℤ²`, trivial involution, `ξ = (1, 1)`, `ν(u) = u₁² u₂²`, `r = 2`. -/
def F : Frame (ℤ × ℤ) (ℤ × ℤ) 2 where
  ψ := AddMonoidHom.id _
  ψ_injective := Function.injective_id
  star_ψ := fun η => star_trivial η
  pb := fun α η => α * η * α
  ψ_pb := fun α η => by simp [star_trivial]
  ξ := 1
  ψ_ξ := rfl
  I := I
  ν := fun u => u.1 ^ 2 * u.2 ^ 2
  I_pb := fun u v => by simp only [I_apply, Prod.fst_mul, Prod.snd_mul]; ring
  I_ξ := by simp [I_apply]

end ModelA

namespace ModelB

open Quaternion

/-- `E = ℍ[ℤ, 0, 0, 0]` with its conjugation, `N = ℤ`, `ξ = 1`, `α*x = (re α)² x`,
`ν(α) = (re α)²`. -/
def F : Frame ℍ[ℤ, 0, 0, 0] ℤ 1 where
  ψ := ⟨⟨fun x => (x : ℍ[ℤ, 0, 0, 0]), QuaternionAlgebra.coe_zero⟩,
    fun x y => QuaternionAlgebra.coe_add x y⟩
  ψ_injective := QuaternionAlgebra.coe_injective
  star_ψ := fun η => QuaternionAlgebra.star_coe η
  pb := fun u x => u.re ^ 2 * x
  ψ_pb := fun u x => by
    change ((u.re ^ 2 * x : ℤ) : ℍ[ℤ, 0, 0, 0]) = star u * (x : ℍ[ℤ, 0, 0, 0]) * u
    ext <;> simp [sq] <;> ring
  ξ := 1
  ψ_ξ := QuaternionAlgebra.coe_one
  I := I
  ν := fun u => u.re ^ 2
  I_pb := fun u v => by simp [I_apply]
  I_ξ := by simp [I_apply]

end ModelB

end Grothendieck.Folder50
