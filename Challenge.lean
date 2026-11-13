module

public import Mathlib

/-!
# The Challenge: one headline statement per folder file, for 41 folders

Each section states the headline theorem of one file `Grothendieck/FolderNN.lean` with `sorry`,
together with the definitions its statement depends on, copied from the library under the same
names (docstrings and comments removed). Palomar limits this file, and only this file, to
1,000 lines and 100 KiB, so it compares 41 of the 91 headline theorems; the other 50 are built
and proved in the library but not compared here, and `CHALLENGE.md` lists both. This file
imports only Mathlib, so that it compiles alone.
-/

-- From Challenge/Folder1.lean
@[expose] public section
namespace Grothendieck.Folder1
open Finset Module InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
section SVD
variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
noncomputable def sigma (n m : ℕ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, T.singularValues i
end SVD
open scoped ComplexConjugate
end Grothendieck.Folder1
namespace Grothendieck.Folder1
open Finset Module InnerProductSpace Matrix Polynomial
open scoped MatrixOrder ComplexOrder ComplexConjugate
section SigmaSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
theorem sigma_system (u v : E →ₗ[ℂ] F) (n m : ℕ) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  sorry
end SigmaSystem
end Grothendieck.Folder1
end

-- From Challenge/Folder13.lean
@[expose] public section
open Complex Polynomial
open scoped Pointwise
namespace Grothendieck.Folder13
theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} := by
  sorry
end Grothendieck.Folder13
end

-- From Challenge/Folder22.lean
@[expose] public section
namespace Grothendieck.Folder22
open TensorProduct LinearMap
universe u
variable {A : Type u} [CommRing A]
section SeveralVariablesSmooth
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {σ : Type*} [Finite σ]
  [DecidableEq σ]
theorem not_formallySmooth_mv (i₀ : σ) (h : ¬ Module.Finite K Ω[K⁄R]) :
    ¬ Algebra.FormallySmooth K (MvPowerSeries σ K) := by
  sorry
end SeveralVariablesSmooth
end Grothendieck.Folder22
end

-- From Challenge/Folder29.lean
@[expose] public section
open Matrix
namespace Folder29
variable {C C' : Type*} [Fintype C] [Fintype C']
noncomputable def inertiaMap (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (C → ℤ_[ℓ]) → (C' → ℤ_[ℓ]) :=
  (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVec
theorem criterion [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      Fintype.card C = Fintype.card C' ∧ ∃ e : C' ≃ C, ∃ k : ℕ,
        (N.submatrix id e).det = p ^ k ∨ (N.submatrix id e).det = -(p ^ k : ℤ) := by
  sorry
end Folder29
end

-- From Challenge/Folder37.lean
@[expose] public section
namespace Grothendieck.Folder37
open Polynomial
variable (k : Type*) [Field k]
abbrev P := (MvPolynomial ℕ k)[X]
def An (n : ℕ) : Type _ := P k ⧸ Ideal.span {(X : P k) ^ (n + 1)}
noncomputable instance (n : ℕ) : CommRing (An k n) :=
  fast_instance% Ideal.Quotient.commRing _
noncomputable def mkA (n : ℕ) : P k →+* An k n := Ideal.Quotient.mk _
noncomputable def gen (l : ℕ) : P k := C (MvPolynomial.X l) * X ^ l
noncomputable def Jn (n : ℕ) : Ideal (An k n) :=
  Ideal.span (Set.range fun l : Fin (n + 1) => mkA k n (gen k l))
open TensorProduct in
theorem no_finitePresentation_inducing (A : Type*) [CommRing A] (f : ∀ n, A →+* An k n)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    ¬ ∀ n, letI := (f n).toAlgebra
      Nonempty ((An k n) ⊗[A] M ≃ₗ[An k n] (An k n ⧸ Jn k n)) := by
  sorry
end Grothendieck.Folder37
end

-- From Challenge/Folder39.lean
@[expose] public section
namespace Grothendieck.Folder39.Henselian
open MvPowerSeries
variable {k : Type*} [CommRing k]
structure IsFormalClass (A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)) : Prop where
  X_mem : ∀ n (i : Fin n), X i ∈ A n
  subst_mem : ∀ {n m : ℕ} {φ : MvPowerSeries (Fin n) k} {f : Fin n → MvPowerSeries (Fin m) k},
    φ ∈ A n → (∀ i, f i ∈ A m) → (∀ i, IsNilpotent (constantCoeff (f i))) → subst f φ ∈ A m
  inv_mem : ∀ {n : ℕ} {f g : Fin n → MvPowerSeries (Fin n) k}, (∀ i, f i ∈ A n) →
    (∀ i, IsNilpotent (constantCoeff (f i))) → (∀ i, IsNilpotent (constantCoeff (g i))) →
    (∀ i, subst g (f i) = X i) → (∀ i, subst f (g i) = X i) → ∀ i, g i ∈ A n
variable {A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)}
theorem implicit_mem (hA : IsFormalClass A) {n : ℕ} {P : MvPowerSeries (Fin (n + 1)) k}
    (hP : P ∈ A (n + 1)) (h0 : constantCoeff P = 0)
    (h1 : IsUnit (coeff (Finsupp.single 0 1) P)) {F : MvPowerSeries (Fin n) k}
    (hF0 : constantCoeff F = 0)
    (hF : subst (Fin.cons F X : Fin (n + 1) → MvPowerSeries (Fin n) k) P = 0) : F ∈ A n := by
  sorry
end Grothendieck.Folder39.Henselian
end

-- From Challenge/Folder40.lean
@[expose] public section
namespace Grothendieck.Folder40
open Polynomial IsLocalRing
section PowerSeries
variable {k : Type*} [Field k]
abbrev Cusp (k : Type*) [Field k] (n : ℕ) := AdjoinRoot (X ^ n - C (PowerSeries.X ^ 2 : (PowerSeries k)))
theorem not_isDVR_cusp_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    ¬ ∃ _ : IsDomain (Cusp k n), IsDiscreteValuationRing (Cusp k n) := by
  sorry
end PowerSeries
end Grothendieck.Folder40
end

-- From Challenge/Folder41.lean
@[expose] public section
namespace Grothendieck.Folder41
open Topology
section Topologie
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
def SectionGenerique (f : X → Y) (φ : Y → X) : Prop :=
  ∀ y, f (φ y) = y ∧ ∀ x, f x = y → φ y ⤳ x
variable {f : X → Y} {φ : Y → X} (hφ : SectionGenerique f φ)
include hφ
end Topologie
section Schemas
open AlgebraicGeometry
theorem proposition1 {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (φ : Y → X)
    (hφ : SectionGenerique f φ) :
    List.TFAE [Continuous φ, IsOpenMap f, ∀ y y', y' ⤳ y → φ y' ⤳ φ y, GeneralizingMap f] := by
  sorry
end Schemas
end Grothendieck.Folder41
end

-- From Challenge/Folder46.lean
@[expose] public section
open Finset IsLocalRing
namespace Grothendieck.Folder46
section Cocycles
variable {Γ A : Type*} [Group Γ] [Ring A] [MulSemiringAction Γ A]
def IsCocycle (c : Γ → Aˣ) : Prop :=
  ∀ g h, (c (g * h) : A) = c g * g • (c h : A)
variable [Fintype Γ]
variable {B : Type*} [Ring B] [MulSemiringAction Γ B]
end Cocycles
section LocalRing
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
variable [IsLocalRing O]
variable {Γ B : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ A] [Ring B]
  [MulSemiringAction Γ B]
theorem injective [Module.Finite O A] (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ)
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A)) {c c' : Γ → Aˣ}
    (hc : IsCocycle c) (hc' : IsCocycle c')
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * π (c' g) * g • (v : B)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  sorry
end LocalRing
end Grothendieck.Folder46
end

-- From Challenge/Folder53.lean
@[expose] public section
open MvPolynomial
namespace Grothendieck.Folder53
variable {K ι : Type*} [Field K]
noncomputable def law (m : ι → MvPolynomial (ι ⊕ ι) K) (a v : ι → K) : ι → K :=
  fun i => eval (Sum.elim a v) (m i)
variable [IsAlgClosed K] [Finite ι]
theorem isUnit_of_isLeftCancelMul {M : Type*} [Monoid M] [IsLeftCancelMul M]
    (φ : M → ι → K) (hφ : Function.Injective φ) (I : Ideal (MvPolynomial ι K))
    (hI : Set.range φ = zeroLocus K I) (m : ι → MvPolynomial (ι ⊕ ι) K)
    (hm : ∀ x y, φ (x * y) = law m (φ x) (φ y)) (x : M) : IsUnit x := by
  sorry
end Grothendieck.Folder53
open Pointwise
end

-- From Challenge/Folder62.lean
@[expose] public section
namespace Folder62
variable {K : Type*} [Field K]
def num (t : K) : K := (t + 1) * (2 * t - 1) * (t - 2)
def den (t : K) : K := t * (t - 1)
noncomputable def j (t : K) : K := -(1 / 27) * (num t / den t) ^ 2
theorem j_eq_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    j s = j t ↔ s = t ∨ s = 1 / t ∨ s = 1 - t ∨ s = t / (t - 1) ∨ s = 1 / (1 - t) ∨
      s = (t - 1) / t := by
  sorry
end Folder62
end

-- From Challenge/Folder63.lean
@[expose] public section
open Polynomial
namespace Grothendieck.Folder63
abbrev R := AdjoinRoot (X ^ 2 + X + 1 : ℤ[X])
noncomputable abbrev ζ : R := AdjoinRoot.root _
noncomputable def P : Ideal R[X] := Ideal.span {C 2, X}
noncomputable def α : Fin 4 → R := ![0, 1, ζ, ζ ^ 2]
noncomputable def branch (i : Fin 4) : R[X] := X + 2 * C (α i)
theorem tangents_distinct (i j : Fin 4) (hij : i ≠ j) (a b : R[X])
    (h : a * branch i + b * branch j ∈ P ^ 2) : a ∈ P ∧ b ∈ P := by
  sorry
end Grothendieck.Folder63
end

-- From Challenge/Folder64.lean
@[expose] public section
namespace Grothendieck.Folder64
open Finset
section Field
variable {K : Type*} [Field K] [DecidableEq K]
def quad (i : K) : Finset K := {0, 1, i, -i}
variable {i : K}
theorem fixer_five (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (a : K)
    (h : ∀ z ∈ quad i, a * z + (a - 1) ∈ quad i) : (5 : K) * (a - 1) = 0 := by
  sorry
end Field
end Grothendieck.Folder64
end

-- From Challenge/Folder69.lean
@[expose] public section
namespace Grothendieck.Folder69
open Equiv
def pairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]
def cp (v : Fin 27) : ℕ × ℕ := pairs.getD (v.val - 12) (0, 0)
def meets (u v : Fin 27) : Bool :=
  if u.val < 12 ∧ v.val < 12 then
    (u.val < 6 ∧ 6 ≤ v.val ∧ u.val + 6 ≠ v.val) || (v.val < 6 ∧ 6 ≤ u.val ∧ v.val + 6 ≠ u.val)
  else if u.val < 12 then (cp v).1 = u.val % 6 || (cp v).2 = u.val % 6
  else if v.val < 12 then (cp u).1 = v.val % 6 || (cp u).2 = v.val % 6
  else (cp u).1 ≠ (cp v).1 ∧ (cp u).1 ≠ (cp v).2 ∧ (cp u).2 ≠ (cp v).1 ∧ (cp u).2 ≠ (cp v).2
def C : SimpleGraph (Fin 27) where
  Adj u v := meets u v = true
  symm := ⟨fun u v h =>
    ((show ∀ u v : Fin 27, meets u v = meets v u by decide +kernel) u v).symm.trans h⟩
  loopless := ⟨fun u h => by
    rw [(show ∀ u : Fin 27, meets u u = false by decide +kernel) u] at h
    exact Bool.false_ne_true h⟩
def t : Finset (Fin 27) := {0, 7, 12}
theorem card_aut : Nat.card {f : C ≃g C // ∀ v, f v ∈ t ↔ v ∈ t} = 1152 := by
  sorry
end Grothendieck.Folder69
end

-- From Challenge/Folder70.lean
@[expose] public section
namespace Grothendieck.Folder70
section General
variable {R : Type*} [CommRing R] (α : R)
def iota (p : R × R × R) : R × R × R :=
  ((-1 - α) - p.1, 1 - (-1 - α) - p.2.1, 1 - (-1 - α) - p.2.2)
def vert : Fin 12 → R × R × R :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1 - α, -(-1 - α), 1), (0, -(-1 - α), 1),
    iota α (0, 0, 0), iota α (1, 0, 0), iota α (0, 1, 0), iota α (0, 0, 1),
    iota α (-1 - α, -(-1 - α), 1), iota α (0, -(-1 - α), 1)]
variable {α}
end General
end Grothendieck.Folder70
namespace Grothendieck.Folder70
section Quadric
open Matrix
variable {R : Type*} [CommRing R] {α : R}
@[ext] structure QuadFn (R : Type*) where
  (a b c u v w d e f k : R)
def QuadFn.eval (Q : QuadFn R) (p : R × R × R) : R :=
  Q.a * p.1 ^ 2 + Q.b * p.2.1 ^ 2 + Q.c * p.2.2 ^ 2 + Q.u * (p.2.1 * p.2.2)
    + Q.v * (p.2.2 * p.1) + Q.w * (p.1 * p.2.1) + Q.d * p.1 + Q.e * p.2.1 + Q.f * p.2.2 + Q.k
def QuadFn.smul (r : R) (Q : QuadFn R) : QuadFn R :=
  ⟨r * Q.a, r * Q.b, r * Q.c, r * Q.u, r * Q.v, r * Q.w, r * Q.d, r * Q.e, r * Q.f, r * Q.k⟩
variable (α) in
def qFn : QuadFn R := ⟨1, 1, 1, -α, 1, 1, -1, -1, -1, 0⟩
theorem quadric_unique (h : α ^ 2 + α - 1 = 0) (Q : QuadFn R)
    (hQ : ∀ i : Fin 12, i.val < 9 → Q.eval (vert α i) = 0) : Q = QuadFn.smul Q.a (qFn α) := by
  sorry
end Quadric
end Grothendieck.Folder70
end

-- From Challenge/Folder76.lean
@[expose] public section
namespace Grothendieck.Folder76
open MulAction
variable {G : Type*} [Group G] {n : ℕ}
def gen (σ : Fin (n + 1) → G) (K : Set (Fin (n + 1))) : Subgroup G :=
  Subgroup.closure (σ '' K)
def N (σ : Fin (n + 1) → G) (H : Set (Fin (n + 1))) : Subgroup G := gen σ Hᶜ
lemma gen_mono (σ : Fin (n + 1) → G) {K K' : Set (Fin (n + 1))} (h : K ⊆ K') :
    gen σ K ≤ gen σ K' :=
  Subgroup.closure_mono (Set.image_mono h)
lemma N_anti (σ : Fin (n + 1) → G) {H H' : Set (Fin (n + 1))} (h : H ⊆ H') :
    N σ H' ≤ N σ H :=
  gen_mono σ (Set.compl_subset_compl.mpr h)
variable (σ : Fin (n + 1) → G) (X : Type*) [MulAction G X]
abbrev D (H : Set (Fin (n + 1))) : Type _ := orbitRel.Quotient (N σ H) X
variable {σ X}
def res {H H' : Set (Fin (n + 1))} (h : H ⊆ H') : D σ X H' → D σ X H :=
  Quotient.map' id fun x y hxy => by
    rw [orbitRel_apply] at hxy ⊢
    obtain ⟨g, rfl⟩ := hxy
    exact ⟨⟨g, N_anti σ h g.2⟩, rfl⟩
theorem flag_lemma (hσ : ∀ i j : Fin (n + 1), (i : ℕ) + 2 ≤ j → Commute (σ i) (σ j))
    {H H' : Set (Fin (n + 1))} (i : Fin (n + 1)) (hiH : i ∈ H) (hmax : ∀ j ∈ H, j ≤ i)
    (hiH' : i ∈ H') (hinit : ∀ j ∈ H', ∀ k ∈ H ∩ H', j ≤ k → j ∈ H)
    (a : D σ X H) (b : D σ X H')
    (hab : res Set.inter_subset_left a = res Set.inter_subset_right b) :
    ∃ c : D σ X (H ∪ H'), res Set.subset_union_left c = a ∧
      res Set.subset_union_right c = b := by
  sorry
end Grothendieck.Folder76
end

-- From Challenge/Folder77.lean
@[expose] public section
namespace Grothendieck.Folder77
open MvPolynomial Matrix
def polarOf {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then 2 * y s(i, i) else y s(i, j)
section
open Finset
def fpfInv (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i
end
noncomputable def hafnian (m : ℕ) : MvPolynomial (Sym2 (Fin m)) ℤ :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ Finset.univ.filter (fun i => i < σ i), X s(i, σ i)
theorem disc_even_rank (n : ℕ) :
    ∃ C : MvPolynomial (Sym2 (Fin (2 * n))) ℤ, ∀ {R : Type*} [CommRing R]
      (y : Sym2 (Fin (2 * n)) → R),
        (-1) ^ n * (polarOf y).det = aeval y (hafnian (2 * n)) ^ 2 - 4 * aeval y C := by
  sorry
end Grothendieck.Folder77
end

-- From Challenge/Folder78.lean
@[expose] public section
namespace Grothendieck.Folder78
open Polynomial Polynomial.Chebyshev
section Poly
variable (R : Type*) [CommRing R]
noncomputable def F (n : ℤ) : R[X] :=
  if Even n then S R (n / 2 - 1) else S R (n / 2) + S R (n / 2 - 1)
end Poly
section Map
variable {k : Type*} [CommRing k]
def u (α : k) : Equiv.Perm (k × k) where
  toFun p := (1 - p.2 + α * p.1, p.1)
  invFun p := (p.2, 1 - p.1 + α * p.2)
  left_inv p := Prod.ext rfl (show 1 - (1 - p.2 + α * p.1) + α * p.1 = p.2 by ring)
  right_inv p := Prod.ext (show 1 - (1 - p.1 + α * p.2) + α * p.2 = p.1 by ring) rfl
theorem zpow_eq_one_iff (α : k) (n : ℤ) : u α ^ n = 1 ↔ (F k n).eval α = 0 := by
  sorry
end Map
end Grothendieck.Folder78
end

-- From Challenge/Folder80Maps2.lean
public section
namespace Grothendieck.Folder80Maps2
section Core
variable {P L : Type*} (on : P → L → Prop)
def C (a b c : L) : Prop := ∃ p, on p a ∧ on p b ∧ on p c
def GP4 (a b c d : L) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ¬C on a b c ∧ ¬C on a b d ∧ ¬C on a c d ∧ ¬C on b c d
def GP5 (a b c d e : L) : Prop :=
  GP4 on a b c d ∧ a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e ∧
    ¬C on a b e ∧ ¬C on a c e ∧ ¬C on a d e ∧ ¬C on b c e ∧ ¬C on b d e ∧ ¬C on c d e
def BigonFree : Prop := ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r
def IsII4 : Prop := ∃ a b c d, GP4 on a b c d ∧ ∀ m, m = a ∨ m = b ∨ m = c ∨ m = d
def HasII5 : Prop := ∃ a b c d e, GP5 on a b c d e
def HasII32 : Prop :=
  ∃ a b c d e : L, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ ∃ p, on p a ∧ on p b ∧ on p c ∧ ¬on p d ∧
    ¬on p e ∧ ∀ q, on q d → on q e → ¬on q a ∧ ¬on q b ∧ ¬on q c
def NC (p q r : P) : Prop := ∀ m, on p m → on q m → ¬on r m
def J (p q : P) : Prop := ∃ m, on p m ∧ on q m
def HasIII6 : Prop :=
  ∃ p q r s : P, J on p q ∧ J on p r ∧ J on p s ∧ J on q r ∧ J on q s ∧ J on r s ∧
    NC on p q r ∧ NC on p q s ∧ NC on p r s ∧ NC on q r s
end Core
section Maps
open Relation
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d
namespace GMap
variable {D : Type*} (M : GMap D)
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x
def vtx (d : D) : M.Vtx := Quot.mk _ d
def edge (d : D) : M.Edge := Quot.mk _ d
def face (d : D) : M.Face := Quot.mk _ d
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face
end GMap
open GMap
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1
namespace PseudolineMap
variable {D L : Type*} (X : PseudolineMap D L)
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l
variable {X}
variable [Fintype D]
theorem map_dichotomy (hbf : BigonFree X.On) :
    IsII4 X.On ∨ HasII5 X.On ∨ HasII32 X.On ∨ HasIII6 X.On := by
  sorry
end PseudolineMap
end Maps
end Grothendieck.Folder80Maps2
end

-- From Challenge/Folder89.lean
@[expose] public section
namespace Grothendieck.Folder89
variable {R : Type*} [CommRing R]
def wedge (u v : Fin 2 → R) : R := u 0 * v 1 - u 1 * v 0
theorem fundamental_relation (u v w : Fin 2 → R) (hd : IsUnit (wedge u v)) :
    (wedge u v = wedge v w ∧ wedge v w = wedge w u) ↔ u + v + w = 0 := by
  sorry
end Grothendieck.Folder89
end

-- From Challenge/Folder90.lean
@[expose] public section
open Polynomial TensorProduct
namespace Grothendieck.Folder90
variable (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]
variable {R K}
variable (R K) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
section Components
variable {A : Type*} [CommRing A] (π : A)
theorem iInf_pow_eq_bot_iff [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ := by
  sorry
end Components
end Grothendieck.Folder90
end

-- From Challenge/Folder93.lean
@[expose] public section
open Polynomial
open scoped Ring
namespace Grothendieck.Folder93
variable {R : Type*} [CommRing R]
local notation "D" => Polynomial.hasseDeriv
noncomputable def N (f : R[X]) : R[X] := D 2 f ^ 2 - D 3 f * D 1 f
open CategoryTheory CochainComplex HomComplex
end Grothendieck.Folder93
namespace Grothendieck.Folder93.Alpha
open Polynomial
open scoped Ring
local notation "D" => Polynomial.hasseDeriv
variable {A : Type*} [CommRing A] (p n : ℕ) (α : A)
noncomputable abbrev P : A[X] := X ^ p ^ n - C α
variable {p n α}
variable (p n α)
theorem rigidity_alpha_local [IsLocalRing A] [Fact p.Prime] [CharP A p] (hq : 3 < p ^ n)
    (hC : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : A)) (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P p n α) (D 1 s))) (hN : AdjoinRoot.mk (P p n α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p n α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p n α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p n α) (C c * X + C d)) := by
  sorry
end Grothendieck.Folder93.Alpha
end

-- From Challenge/Folder94.lean
@[expose] public section
open RingTheory.Sequence Submodule Function
namespace Grothendieck.Folder94
variable {A : Type*} [CommRing A]
open Polynomial
noncomputable section
universe u
section Telescope
variable {R : Type*} [CommRing R] (c : ℕ → R) (M : Type*) [AddCommGroup M] [Module R M]
def teleMap (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M := (∏ l ∈ Finset.Ioc i j, c l) • LinearMap.id
abbrev Tele : Type _ := Module.DirectLimit (fun _ : ℕ => M) (teleMap c M)
variable {c M}
end Telescope
section Plane
variable {k : Type*} [Field k]
abbrev hx (a : k) : k[X][X] := C (X - C a)
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
end

-- From Challenge/Folder100.lean
@[expose] public section
namespace Grothendieck.Folder100.Baire
open IsLocalRing PrimeSpectrum
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [IsAdicComplete (maximalIdeal R) R]
theorem exists_finite_subcover_of_countable {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hcov : ∀ x : PrimeSpectrum R, Order.coheight x ≤ 1 → x ∈ ⋃ i, Z i) :
    ∃ s : Finset ι, ⋃ i ∈ s, Z i = Set.univ := by
  sorry
end Grothendieck.Folder100.Baire
end

-- From Challenge/Folder107.lean
@[expose] public section
namespace Grothendieck.Folder107
open CategoryTheory Limits HomotopicalAlgebra
universe v u
variable {C : Type u} [Category.{v} C]
structure RelativeCylinder {X X' : C} (i : X ⟶ X') where
  P : Precylinder X
  P' : Precylinder X'
  iJ : P.I ⟶ P'.I
  w₀ : P.i₀ ≫ iJ = i ≫ P'.i₀
  w₁ : P.i₁ ≫ iJ = i ≫ P'.i₁
attribute [reassoc] RelativeCylinder.w₀ RelativeCylinder.w₁
def IsHomotopy {A Y : C} (P : Precylinder A) (H : P.I ⟶ Y) (f f' : A ⟶ Y) : Prop :=
  P.i₀ ≫ H = f ∧ P.i₁ ≫ H = f'
section ModelCategory
variable [ModelCategory C] {X X' Y Y' : C} {i : X ⟶ X'} (R : RelativeCylinder i)
theorem rectification_modelCategory (p : Y ⟶ Y') [Fibration p]
    [Cofibration (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    [WeakEquivalence (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (φ : X' ⟶ Y) :
    (∃ (φbar : X' ⟶ Y) (K : R.P'.I ⟶ Y),
        i ≫ φbar = g ∧ φbar ≫ p = g' ∧ IsHomotopy R.P' K φ φbar) ↔
      ∃ (k : R.P.I ⟶ Y) (h : R.P'.I ⟶ Y'),
        IsHomotopy R.P k (i ≫ φ) g ∧ IsHomotopy R.P' h (φ ≫ p) g' ∧ k ≫ p = R.iJ ≫ h := by
  sorry
end ModelCategory
end Grothendieck.Folder107
end

-- From Challenge/Folder118.lean
@[expose] public section
namespace Grothendieck.Folder118
open MulAction
variable (G : Type*) [Group G]
def IsWeq {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) : Prop :=
  (∀ y : Y, ∃ (x : X) (g : G), g • f x = y) ∧
  (∀ (x x' : X) (g : G), g • f x = f x' → ∃ h : G, h • x = x') ∧
  (∀ (x : X) (g : G), g • f x = f x → g • x = x)
def Aspherical (X : Type*) [MulAction G X] : Prop :=
  Nonempty X ∧ (∀ x y : X, ∃ g : G, g • x = y) ∧ ∀ (x : X) (g : G), g • x = x → g = 1
variable {G}
def prodHom {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] (f : X →[G] Y) (f' : X' →[G] Y') : X × X' →[G] Y × Y' where
  toFun p := (f p.1, f' p.2)
  map_smul' g p := by simp [map_smul]
theorem answer_page_35 [Nontrivial G] :
    (∀ {X Y X' Y' : Type} [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
      (f : X →[G] Y) (f' : X' →[G] Y'), IsWeq G f → IsWeq G f' → IsWeq G (prodHom f f')) ∧
    ¬ Aspherical G PUnit ∧ ¬ Aspherical G (G × G) := by
  sorry
end Grothendieck.Folder118
end

-- From Challenge/Folder121.lean
@[expose] public section
namespace Grothendieck.Folder121
open Set
variable {X : Type*} [TopologicalSpace X]
def Rare (B Z : Set X) : Prop := ∀ V, IsOpen V → V ∩ Z ⊆ B → V ∩ Z = ∅
structure Tame (F : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F
  closure_mem : ∀ A ∈ F, closure A ∈ F
  dense_open : ∀ A ∈ F, ∃ G, IsOpen G ∧ G ∩ closure A ⊆ A ∧ closure A ⊆ closure (G ∩ closure A)
  dcc : ∀ A : ℕ → Set X, (∀ n, A n ∈ F ∧ IsClosed (A n)) →
    (∀ n, A (n + 1) ⊆ A n ∧ Rare (A (n + 1)) (A n)) → ∃ n, A n = ∅
variable {F : Set (Set X)}
structure IsDecomp (Z : Set X) (P : Finset (Set X)) : Prop where
  nonempty : ∀ c ∈ P, c.Nonempty
  disjoint : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → Disjoint c d
  cover : ⋃ c ∈ P, c = Z
  frontier : ∀ c ∈ P, ∀ d ∈ P, (closure c ∩ d).Nonempty → d ⊆ closure c
  distinct : ∀ c ∈ P, ∀ d ∈ P, closure c = closure d → c = d
def Compat (L P : Finset (Set X)) : Prop := ∀ Y ∈ L, ∀ c ∈ P, c ⊆ Y ∨ Disjoint c Y
def Good (F : Set (Set X)) (L : Finset (Set X)) (Z : Set X) (P : Finset (Set X)) : Prop :=
  IsDecomp Z P ∧ (∀ c ∈ P, c ∈ F) ∧ Compat L P
def Coarser (P Q : Finset (Set X)) : Prop := ∀ q ∈ Q, ∃ p ∈ P, q ⊆ p
theorem page14 (hF : Tame F) (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, Good F L univ P ∧ ∀ Q, Good F L univ Q → Coarser P Q := by
  sorry
end Grothendieck.Folder121
end

-- From Challenge/Folder123Kostant.lean
@[expose] public section
namespace Grothendieck.Folder123Kostant
def dataA (n : ℕ) : ℕ × ℕ × ℕ := ((n + 1).factorial, n + 1, n + 1)
def dataB (n : ℕ) : ℕ × ℕ × ℕ := (2 ^ n * n.factorial, 2 * n, 2)
def dataG2 : ℕ × ℕ × ℕ := (12, 6, 1)
def number (d : ℕ × ℕ × ℕ) : ℕ := d.1 ^ 2 / (d.2.1 * d.2.2 * Nat.totient d.2.1)
theorem small_cases :
    number (dataA 1) = 1 ∧ number (dataA 2) = 2 ∧ number (dataB 2) = 4 ∧ number dataG2 = 12 := by
  sorry
end Grothendieck.Folder123Kostant
end

-- From Challenge/Folder136.lean
@[expose] public section
namespace Grothendieck.Folder136
theorem binomial_constant {A : Type*} [AddCommGroup A] (x : ℕ → A) (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (x j - x i) = 0) :
    ∀ j, N ≤ j → x j = x N := by
  sorry
end Grothendieck.Folder136
open TensorProduct Coalgebra WithConv Polynomial Finset
end

-- From Challenge/Folder145.lean
@[expose] public section
namespace Grothendieck.Folder145
open DihedralGroup
def Compatible (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ m n : ℕ, n ≠ 0 → ∀ h : m ∣ n, ZMod.castHom h (ZMod m) (p n) = p m
def hatPow {G : Type*} [Group G] [Fintype G] (p : ∀ n : ℕ, ZMod n) (x : G) : G :=
  x ^ (p (Fintype.card G)).val
def Rel14 (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (x y z : G),
    z * y * x = 1 → hatPow p z * hatPow p y * hatPow p x = 1
theorem rel14_unit_iff (p : ∀ n : ℕ, ZMod n) (hp : Compatible p)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (p n)) :
    Rel14 p ↔ ∀ n : ℕ, n ≠ 0 → p n = 1 := by
  sorry
end Grothendieck.Folder145
end

-- From Challenge/Folder146.lean
@[expose] public section
namespace Grothendieck.Folder146
variable {K : Type*} [Field K]
def anh : Fin 6 → K → K
  | 0 => fun x => x
  | 1 => fun x => 1 / x
  | 2 => fun x => 1 - x
  | 3 => fun x => x / (x - 1)
  | 4 => fun x => 1 / (1 - x)
  | 5 => fun x => (x - 1) / x
def der : Fin 6 → K → K
  | 0 => fun _ => 1
  | 1 => fun x => -1 / x ^ 2
  | 2 => fun _ => -1
  | 3 => fun x => -1 / (x - 1) ^ 2
  | 4 => fun x => 1 / (1 - x) ^ 2
  | 5 => fun x => 1 / x ^ 2
def U (x : K) : Prop := x ≠ 0 ∧ x ≠ 1
theorem six_dvd (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0)
    (m : ℤ) (h : K → K) (hh : ∀ x, U x → h x ≠ 0)
    (hc : ∀ a x, U x → der a x ^ m = h (anh a x) / h x) : 6 ∣ m := by
  sorry
variable {α : Type*} {n : ℕ} {V : α → Prop} {act : Fin n → α → α} {c : Fin n → α → K}
end Grothendieck.Folder146
end

-- From Challenge/Folder147.lean
@[expose] public section
namespace Grothendieck.Folder147
variable {K : Type*} [Field K] [CharZero K]
theorem class_M11 (L z₂ z₃ : K) :
    (1 / 2) * (L - 2 + z₂ + z₃) + (1 / 4) * (1 - z₂ - z₃) + (1 / 6) * (1 - z₂ - z₃)
        + (1 / 24) * z₂ + (1 / 12) * z₃
      = (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  sorry
end Grothendieck.Folder147
end

-- From Challenge/Folder148.lean
@[expose] public section
open Set Filter Topology
namespace Grothendieck.Folder148
structure Marking (r : ℕ) where
  pt : ℤ → ℝ
  strictMono : StrictMono pt
  periodic : ∀ k, pt (k + r) = pt k + 1
variable {r : ℕ}
end Grothendieck.Folder148
open scoped ContinuousMap
namespace Grothendieck.Folder148
variable {r : ℕ}
def circleGluings (P Q : Marking r) (c : ℤ) : Set C(UnitAddCircle, UnitAddCircle) :=
  {f | Function.Bijective f ∧ (∃ F : ℝ → ℝ, Continuous F ∧ StrictAnti F ∧ ∀ x : ℝ, f x = F x) ∧
    ∀ k, f (P.pt k) = Q.pt (c - k)}
theorem contractibleSpace_circleGluings (P Q : Marking r) (c : ℤ) :
    ContractibleSpace (circleGluings P Q c) := by
  sorry
end Grothendieck.Folder148
end

-- From Challenge/Folder148Chart.lean
@[expose] public section
namespace Grothendieck.Folder148Chart
def orders : List ℕ := [10, 6, 4, 2, 2, 1, 2, 1, 2]
def counts : List ℕ := orders.map (120 / ·)
theorem vertices :
    (counts.take 3).sum = 62 ∧ ((counts.drop 3).take 3).sum = 240 ∧ (counts.drop 6).sum = 240 ∧
      counts.sum = 542 := by
  sorry
end Grothendieck.Folder148Chart
end

-- From Challenge/Folder150.lean
@[expose] public section
open Set
namespace Grothendieck.Folder150
def X : Set ℝ := Icc 0 1
def Y : Set ℝ := {0}
def T : Set ℝ := Icc 0 (1 / 2)
def Tdot : Set ℝ := {1 / 2}
def Xstar : Set ℝ := Icc (1 / 2) 1
def cone (S : Set ℝ) : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Icc 0 1 ×ˢ S)
def IsConic (C : Set ℝ) : Prop := C ⊆ T ∧ C = cone (C ∩ Tdot) ∪ (C ∩ Y)
def IsCompatible (X₁ : Set ℝ) : Prop := IsClosed X₁ ∧ X₁ ⊆ X ∧ IsConic (X₁ ∩ T)
def IsCollarCompatible (X₁ : Set ℝ) : Prop :=
  X₁ ∩ Icc (1 / 2) (3 / 4) = (fun p : ℝ × ℝ => p.1 + p.2 / 4) '' ((X₁ ∩ Tdot) ×ˢ Icc 0 1)
theorem compatible_not_determined :
    IsCompatible {0} ∧ IsCompatible ∅ ∧ IsCollarCompatible {0} ∧ IsCollarCompatible ∅ ∧
      ({0} : Set ℝ) ∩ Xstar = ∅ ∩ Xstar ∧ ({0} : Set ℝ).Nonempty := by
  sorry
end Grothendieck.Folder150
end

-- From Challenge/Folder151.lean
@[expose] public section
open Set Topology
namespace Grothendieck.Folder151
abbrev P := ℝ × ℝ
def axis : Set P := {p | p.2 = 0}
def X0 : Set P := {0}
def X1s : Set P := axis \ X0
def X2s : Set P := axisᶜ
structure Tubes where
  V01bar : Set P
  V12bar : Set P
  V01bar_subset : V01bar ⊆ axis
  X0_subset : X0 ⊆ V01bar
  axis_subset : axis ⊆ V12bar
namespace Tubes
variable (T : Tubes)
def V01 : Set P := T.V01bar \ ∅
def V01s : Set P := T.V01bar \ X0
def V12 : Set P := T.V12bar \ X0
def V12s : Set P := T.V12bar \ axis
def piece : Fin 7 → Set P := ![X0, T.V01, T.V01s, X1s, T.V12, T.V12s, X2s]
@[instance_reducible]
def colimTop : TopologicalSpace P :=
  ⨆ i, TopologicalSpace.coinduced (Subtype.val : T.piece i → P) inferInstance
theorem colimTop_ne : T.colimTop ≠ (inferInstance : TopologicalSpace P) := by
  sorry
end Tubes
end Grothendieck.Folder151
end

-- From Challenge/Folder153.lean
@[expose] public section
namespace Grothendieck.Folder153
open Polynomial TensorProduct
variable {k₀ K₀ : Type*} [CommRing k₀] [CommRing K₀] [Algebra k₀ K₀]
noncomputable def ev (x : k₀) : K₀[X] →ₗ[k₀] K₀ :=
  (Polynomial.leval (algebraMap k₀ K₀ x)).restrictScalars k₀
variable (k₀ K₀) in
noncomputable def Omega : Subalgebra k₀ K₀[X] where
  carrier := {F | ∀ x : k₀, F.eval (algebraMap k₀ K₀ x) ∈ (algebraMap k₀ K₀).range}
  mul_mem' {F G} hF hG x := by rw [eval_mul]; exact mul_mem (hF x) (hG x)
  add_mem' {F G} hF hG x := by rw [eval_add]; exact add_mem (hF x) (hG x)
  algebraMap_mem' c x := by
    rw [Polynomial.algebraMap_apply, eval_C]; exact ⟨c, rfl⟩
variable {M : Type*} [AddCommGroup M] [Module k₀ M]
variable (K₀ M) in
def valeursDansM : Set (K₀[X] ⊗[k₀] M) :=
  {F | ∀ x : k₀, (ev x).rTensor M F ∈ LinearMap.range (TensorProduct.mk k₀ K₀ M 1)}
theorem lemme_range [Module.Free k₀ M] :
    (LinearMap.range ((Omega k₀ K₀).val.toLinearMap.rTensor M) : Set (K₀[X] ⊗[k₀] M)) =
      valeursDansM K₀ M := by
  sorry
end Grothendieck.Folder153
end

-- From Challenge/Folder154.lean
@[expose] public section
namespace Grothendieck.Folder154
def ValidSeq {n : ℕ} (s : Fin n → SignType) : Prop :=
  (∃ i, s i ≠ 0) ∧ ∃ a : SignType, a ≠ 0 ∧ ∃ c : ℕ,
    (∀ i : Fin n, (i : ℕ) < c → s i = a) ∧ (∀ i : Fin n, c < (i : ℕ) → s i = -a)
structure Arrangement (V : Type*) (L : Type*) where
  len : L → ℕ
  vert : (ℓ : L) → Fin (len ℓ) → V
  vert_injective : ∀ ℓ, Function.Injective (vert ℓ)
  ori : (ℓ : L) → Fin (len ℓ) → SignType
  ori_ne_zero : ∀ ℓ i, ori ℓ i ≠ 0
def Spec {X : Type*} (σ τ : X → SignType) : Prop := ∀ x, σ x ≠ 0 → τ x = σ x
namespace Arrangement
variable {V L : Type*} (A : Arrangement V L)
def restr (σ : V → SignType) (ℓ : L) : Fin (A.len ℓ) → SignType :=
  fun i => A.ori ℓ i * σ (A.vert ℓ i)
def IsPosition (σ : V → SignType) : Prop := ∀ ℓ, ValidSeq (A.restr σ ℓ)
variable {A}
abbrev Gen (A : Arrangement V L) (σD : V → SignType) :=
  {σ : V → SignType // A.IsPosition σ ∧ Spec σD σ}
end Arrangement
namespace Arrangement
variable {V L : Type*} [Fintype V] {A : Arrangement V L} {σD : V → SignType}
theorem card_gen (hD : A.IsPosition σD) :
    Nat.card (A.Gen σD) = 3 ^ Fintype.card {v // σD v = 0} := by
  sorry
end Arrangement
end Grothendieck.Folder154
end

-- From Challenge/Folder156_4.lean
@[expose] public section
namespace Grothendieck.Folder156_4
section Hexagon
def below : Fin 7 → Finset (Fin 7) :=
  ![{0}, {1}, {2}, {3}, {0, 1, 4}, {1, 2, 5}, {2, 3, 6}]
def le (x y : Fin 7) : Prop := x ∈ below y
def rel (x y : Fin 7) : Prop := ∃ v, x ∈ below v ∧ y ∈ below v
instance : DecidableRel le := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))
instance : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (∃ _, _))
def disj (x y : Fin 7) : Prop := rel x y ∧ ∀ z, ¬ (le z x ∧ le z y)
instance : DecidableRel disj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
def cosuppH (Φ : Finset (Fin 7)) : Finset (Fin 7) := Finset.univ.filter fun x => ∀ y ∈ Φ, disj x y
def suppH (Φ : Finset (Fin 7)) : Finset (Fin 7) := cosuppH (cosuppH Φ)
theorem hexagon_not_distrib :
    ({1, 3} : Finset (Fin 7)) ∩ suppH ({1} ∪ {2}) = {1, 3} ∧
      suppH (({1, 3} : Finset (Fin 7)) ∩ {1} ∪ {1, 3} ∩ {2}) = {1} := by
  sorry
end Hexagon
end Grothendieck.Folder156_4
end

-- From Challenge/Folder158.lean
@[expose] public section
namespace Grothendieck.Folder158
universe u
def PseudoCofiltrant (M : Type u) [Monoid M] : Prop :=
  ∀ u v : M, ∃ u' v' : M, u * u' = v * v'
def Cofiltrant (M : Type u) [Monoid M] : Prop :=
  PseudoCofiltrant M ∧ ∀ u v : M, ∃ w : M, u * w = v * w
def GroupeEnveloppantTrivial (M : Type u) [Monoid M] : Prop :=
  ∀ (G : Type u) [Group G] (f : M →* G), f = 1
variable {M : Type u} [Monoid M]
theorem proposition1 [Finite M] (hpc : PseudoCofiltrant M)
    (hG : GroupeEnveloppantTrivial M) :
    ∃ p : M, (∀ u : M, u * p = p) ∧ p * p = p ∧ Cofiltrant M := by
  sorry
open CategoryTheory
universe v w
end Grothendieck.Folder158
end

-- From Challenge/Folder160.lean
@[expose] public section
open Matrix Polynomial
namespace Grothendieck.Folder160
variable {R : Type*} [CommRing R] (p : ℕ)
def mooreMat {n : ℕ} (ξ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => ξ j ^ p ^ (i : ℕ)
def moore {n : ℕ} (ξ : Fin n → R) : R := (mooreMat p ξ).det
variable [hp : Fact p.Prime]
noncomputable def D (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  moore p (Fin.cons Polynomial.X fun k => Polynomial.C (MvPolynomial.X k))
noncomputable def P (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  ((D p n).roots.map fun a => Polynomial.X - Polynomial.C a).prod
noncomputable def A (n i : ℕ) : MvPolynomial (Fin n) (ZMod p) := (P p n).coeff (p ^ i)
variable {S : Type*} [CommRing S] [Algebra (ZMod p) S]
theorem A_zero_eval {n : ℕ} (ξ : Fin n → S) :
    MvPolynomial.aeval ξ (A p n 0) = (-1) ^ n * moore p ξ ^ (p - 1) := by
  sorry
variable {K : Type*} [Field K] [Algebra (ZMod p) K]
end Grothendieck.Folder160
end
