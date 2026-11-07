module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder137.Perfect

open CategoryTheory Limits

universe u

noncomputable section

variable (k : Type u) [CommRing k]

/-- The support of the disc `ℂⁿ`: `k` in degrees `n` and `n + 1`, `0` elsewhere. -/
def discS (n m : ℕ) : Submodule k k := if m = n ∨ m = n + 1 then ⊤ else ⊥

lemma mem_discS_of_eq (n m : ℕ) (h : m = n ∨ m = n + 1) (x : k) : x ∈ discS k n m := by
  simp [discS, h]

/-- The differential of the disc, the identity of `k` from degree `n + 1` to degree `n`. -/
def discD (n m : ℕ) : ModuleCat.of k (discS k n (m + 1)) ⟶ ModuleCat.of k (discS k n m) :=
  ModuleCat.ofHom (LinearMap.codRestrict (discS k n m)
    ((if m = n then LinearMap.id else 0) ∘ₗ (discS k n (m + 1)).subtype) (fun x => by
      by_cases h : m = n
      · exact mem_discS_of_eq k n m (Or.inl h) _
      · simp [h]))

@[simp]
lemma discD_apply (n m : ℕ) (x : ModuleCat.of k (discS k n (m + 1))) :
    Subtype.val ((discD k n m).hom x) = if m = n then Subtype.val x else 0 := by
  by_cases h : m = n <;> simp [discD, h]

/-- The disc `ℂⁿ` (p. 39): the chain complex `k → k`, identity, in degrees `n + 1`, `n`. -/
noncomputable abbrev disc (n : ℕ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun m => ModuleCat.of k (discS k n m)) (discD k n) (fun m => by
    ext x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, discD_apply, discD_apply]
    split_ifs <;> first | rfl | omega)

/-- The value in `k` of an element of a component of a disc. -/
def dv {n m : ℕ} (x : (disc k n).X m) : k := (show discS k n m from x).1

variable {k}

variable (k) in
/-- The generator `1` of the disc `ℂⁿ`, in degree `n + 1`. -/
def one (n : ℕ) : (disc k n).X (n + 1) := ⟨1, mem_discS_of_eq k n (n + 1) (Or.inr rfl) 1⟩

/-- Proposition 1 (p. 40), the endomorphisms of a disc: `End(ℂⁿ) = k · id`. -/
lemma disc_endo {n : ℕ} (f : disc k n ⟶ disc k n) :
    f = dv k ((f.f (n + 1)).hom (one k n)) • 𝟙 _ := by
  sorry

end

end Grothendieck.Folder137.Perfect
