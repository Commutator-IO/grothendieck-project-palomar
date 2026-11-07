module

public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs

@[expose] public section

open Polynomial

namespace Grothendieck.Folder43

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- Left composition with `F`: `Σ aᵢ t^{pⁱ} ↦ Σ aᵢᵖ t^{p^{i+1}}`. -/
noncomputable def Fr : (ℕ →₀ R) →+ (ℕ →₀ R) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp
    (Finsupp.mapRange.addMonoidHom (frobenius R p).toAddMonoidHom)

/-- `D = F − 1`, `f ↦ fᵖ − f`. -/
noncomputable def D : (ℕ →₀ R) →+ (ℕ →₀ R) := Fr R p - AddMonoidHom.id _

/-- `c ↦ [c]ᵢ`, the class of `(i, c)` in the perfection. -/
def mkHom (i : ℕ) : R →+ PerfectClosure R p where
  toFun c := PerfectClosure.mk R p (i, c)
  map_zero' := PerfectClosure.mk_zero_right R p i
  map_add' a b := by
    rw [PerfectClosure.mk_add_mk]
    simp only
    rw [← iterate_map_add]
    exact PerfectClosure.R.sound R p i i (a + b) _ rfl

/-- `Φ (a) = Σ [aᵢ]ᵢ`. -/
noncomputable def Φ : (ℕ →₀ R) →+ PerfectClosure R p := Finsupp.liftAddHom (mkHom R p)

/-- **The kernel of `Φ` is the image of `F − 1`.** -/
theorem ker_Φ : (Φ R p).ker = (D R p).range := by
  sorry

end Grothendieck.Folder43
