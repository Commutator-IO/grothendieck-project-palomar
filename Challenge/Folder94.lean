module

public import Mathlib

@[expose] public section

open RingTheory.Sequence Submodule Function

namespace Grothendieck.Folder94

variable {A : Type*} [CommRing A]

open Polynomial

noncomputable section

universe u

section Telescope

variable {R : Type*} [CommRing R] (c : ℕ → R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The transition maps of the telescope `M →c M →c M → ⋯` from stage `i` to stage `j`:
multiplication by `∏_{i < l ≤ j} c l`. -/
def teleMap (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M := (∏ l ∈ Finset.Ioc i j, c l) • LinearMap.id

instance teleMap_directedSystem :
    DirectedSystem (fun _ : ℕ => M) (fun i j h => teleMap c M i j h) where
  map_self i x := by simp [teleMap]
  map_map k j i hij hjk x := by
    simp only [teleMap, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm, Finset.prod_Ioc_consecutive _ hij hjk]

/-- The functor `F(M) = colim(M →c M →c M → ⋯)` of the counterexample. -/
abbrev Tele : Type _ := Module.DirectLimit (fun _ : ℕ => M) (teleMap c M)

variable {c M}

end Telescope

section Plane

variable {k : Type*} [Field k]

/-- `x − a` in `k[x, y]`, written `k[X][X]` with `x` the inner variable. -/
abbrev hx (a : k) : k[X][X] := C (X - C a)

/-- Hence `F` restricted to `A_g`-modules is representable by no finite module, for any
`g ≠ 0`: the case `𝔭 = 0` of Lemma 5 (v) fails. -/
theorem not_representable_away {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0)
    (Q : Type*) [AddCommGroup Q] [Module (Localization.Away g) Q]
    [Module.Finite (Localization.Away g) Q]
    (e : (Q →ₗ[Localization.Away g] Localization.Away g) ≃ₗ[Localization.Away g]
      Tele (fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j))) (Localization.Away g)) :
    False := by
  sorry

end Plane

end

end Grothendieck.Folder94
