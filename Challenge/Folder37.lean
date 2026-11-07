module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder37

open Polynomial

variable (k : Type*) [Field k]

/-- `B[T]` with `B = k[X₀, X₁, …]`. -/
abbrev P := (MvPolynomial ℕ k)[X]

/-- `Aₙ = B[T]/(T^{n+1})`, a type of its own so that its ring structure has a single
source. -/
def An (n : ℕ) : Type _ := P k ⧸ Ideal.span {(X : P k) ^ (n + 1)}

noncomputable instance (n : ℕ) : CommRing (An k n) :=
  fast_instance% Ideal.Quotient.commRing _

/-- The reduction `B[T] → Aₙ`. -/
noncomputable def mkA (n : ℕ) : P k →+* An k n := Ideal.Quotient.mk _

/-- The generator `XₗTˡ` of `B[T]`. -/
noncomputable def gen (l : ℕ) : P k := C (MvPolynomial.X l) * X ^ l

/-- `Jₙ = (X₀, X₁T, …, XₙTⁿ) ⊂ Aₙ`. -/
noncomputable def Jn (n : ℕ) : Ideal (An k n) :=
  Ideal.span (Set.range fun l : Fin (n + 1) => mkA k n (gen k l))

open TensorProduct in
/-- **The counterexample.** For any commutative ring `A` and any ring maps `A → Aₙ`
(the page's `A = B[[T]]` with its reductions), no finitely presented `A`-module `M`
has `Aₙ ⊗_A M ≅ Mₙ = Aₙ/Jₙ` for every `n`. -/
theorem no_finitePresentation_inducing (A : Type*) [CommRing A] (f : ∀ n, A →+* An k n)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    ¬ ∀ n, letI := (f n).toAlgebra
      Nonempty ((An k n) ⊗[A] M ≃ₗ[An k n] (An k n ⧸ Jn k n)) := by
  sorry

end Grothendieck.Folder37
