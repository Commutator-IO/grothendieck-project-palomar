module

public import Mathlib

@[expose] public section

namespace CategoryTheory

namespace Idempotents

open Category Karoubi CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

variable (C D E)

variable {C} in
theorem Karoubi.hom_eq_decompId_i_comp {P Q : Karoubi C} (f : P ⟶ Q) :
    f = P.decompId_i ≫ (toKaroubi C).map f.f ≫ Q.decompId_p := by
  ext
  simp

end Idempotents

end CategoryTheory
