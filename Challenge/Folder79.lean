module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.Group
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib

@[expose] public section

namespace Grothendieck.Folder79

section RankTwo

open Matrix

variable {R : Type*} [CommRing R]

/-- `x ∧ y` in the basis of `R²`. -/
def det2 (x y : Fin 2 → R) : R := x 0 * y 1 - x 1 * y 0

omit [CommRing R] in
theorem vec_ext {x y : Fin 2 → R} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i; fin_cases i <;> assumption

theorem mulVec_apply2 (M : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) (i : Fin 2) :
    (M *ᵥ x) i = M i 0 * x 0 + M i 1 * x 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det2_mulVec (M : Matrix (Fin 2) (Fin 2) R) (x y : Fin 2 → R) :
    det2 (M *ᵥ x) (M *ᵥ y) = M.det * det2 x y := by
  simp only [det2, mulVec_apply2, Matrix.det_fin_two]; ring

/-- Coordinates in a basis `(x, y)` with `x ∧ y = 1`:
`z = (z ∧ y) x + (x ∧ z) y`. -/
theorem decomp {x y : Fin 2 → R} (h : det2 x y = 1) (z : Fin 2 → R) :
    z = det2 z y • x + det2 x z • y := by
  unfold det2 at h
  apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, det2]
  · linear_combination (-(z 0)) * h
  · linear_combination (-(z 1)) * h

/-- `x ∈ M*`: `x` is the first vector of a basis of `R²`. -/
def Unimod (x : Fin 2 → R) : Prop := ∃ y, det2 x y = 1

variable (R) in
/-- The relation `x = ± y` on `M*`. -/
def pmSetoid : Setoid {x : Fin 2 → R // Unimod x} where
  r x y := x.1 = y.1 ∨ x.1 = -y.1
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (by rw [h, neg_neg])),
    fun h1 h2 => by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> simp⟩

variable (R) in
/-- `S_M = M*/±1`, the vertices. -/
def Vtx := Quotient (pmSetoid R)

/-- The vertex of a vector `x` with `x ∧ y = 1`. -/
def vtx {x y : Fin 2 → R} (h : det2 x y = 1) : Vtx R := Quotient.mk _ ⟨x, y, h⟩

theorem vtx_eq_iff {x y x' y' : Fin 2 → R} (h : det2 x y = 1) (h' : det2 x' y' = 1) :
    vtx h = vtx h' ↔ x = x' ∨ x = -x' :=
  ⟨fun e => Quotient.exact e, fun e => Quotient.sound e⟩

/-- The action of `SL(2, R)` on `S_M`. -/
def act (g : Matrix.SpecialLinearGroup (Fin 2) R) : Vtx R → Vtx R :=
  Quotient.map (fun x => ⟨g.1 *ᵥ x.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨g.1 *ᵥ y, by rw [det2_mulVec, g.2, hy, one_mul]⟩⟩)
    (fun x y h => h.elim (fun h => Or.inl (by simp [h]))
      (fun h => Or.inr (by simp [h, Matrix.mulVec_neg])))

theorem det2_smul_left (c : R) (x y : Fin 2 → R) : det2 (c • x) y = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_smul_right (c : R) (x y : Fin 2 → R) : det2 x (c • y) = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_add_left (x x' y : Fin 2 → R) : det2 (x + x') y = det2 x y + det2 x' y := by
  simp only [det2, Pi.add_apply]; ring

theorem det2_self (x : Fin 2 → R) : det2 x x = 0 := by unfold det2; ring

theorem det2_neg_left (x y : Fin 2 → R) : det2 (-x) y = -det2 x y := by
  simp only [det2, Pi.neg_apply]; ring

theorem det2_scal (c : Rˣ) {x y : Fin 2 → R} (h : det2 x y = 1) :
    det2 ((c : R) • x) ((↑c⁻¹ : R) • y) = 1 := by
  rw [det2_smul_left, det2_smul_right, h]; simp

/-- The scalar `c ∈ R*`, acting on `S_M`. -/
def scal (c : Rˣ) : Vtx R → Vtx R :=
  Quotient.map (fun x => ⟨(c : R) • x.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨(↑c⁻¹ : R) • y, det2_scal c hy⟩⟩)
    (fun x y h => h.elim (fun h => Or.inl (by simp [h]))
      (fun h => Or.inr (by simp [h])))

/-- The ideal `2R` is contained in `{0, 2}`. With `2 ≠ 0` this is `2R = {0, 2} ≠ {0}`. -/
def Exceptional (R : Type*) [CommRing R] : Prop := ∀ s : R, 2 * s = 0 ∨ 2 * s = 2

theorem Exceptional.four (hR : Exceptional R) : (4 : R) = 0 := by
  rcases hR 2 with h | h
  · linear_combination h
  · linear_combination 2 * h

/-- Independence of the partner: if `2R ⊂ {0, 2}`, `x ∧ y = 1`, `x' ∧ y' = 1`
and `x' = ± x`, then `x' + 2 y' = ± (x + 2 y)`. -/
theorem Exceptional.sigma_rel (hR : Exceptional R) {x y x' y' : Fin 2 → R}
    (h : det2 x y = 1) (h' : det2 x' y' = 1) (hx : x' = x ∨ x' = -x) :
    x' + (2 : R) • y' = x + (2 : R) • y ∨ x' + (2 : R) • y' = -(x + (2 : R) • y) := by
  have h4 := hR.four
  -- write `y'` in the basis `(x, y)`
  have hd := decomp h y'
  rcases hx with hx | hx <;> rw [hx] at h' ⊢
  · have hb : det2 x y' = 1 := h'
    rw [hb, one_smul] at hd
    rcases hR (det2 y' y) with h2 | h2
    · left; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (x i) * h2
    · right; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2 + (x i + y i) * h4
  · have hb : det2 x y' = -1 := by rw [← neg_neg x, det2_neg_left, h']
    rw [hb] at hd
    rcases hR (det2 y' y) with h2 | h2
    · right; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2
    · left; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2 - (y i) * h4

theorem det2_sigma {x y : Fin 2 → R} (h : det2 x y = 1) : det2 (x + (2 : R) • y) y = 1 := by
  rw [det2_add_left, det2_smul_left, det2_self, h]; ring

/-- The extra element `σ` of the commutant (pages 94 and 95), for `2R ⊂ {0, 2}`:
`ẋ ↦ (x + 2y)˙` for any `y` with `x ∧ y = 1`. In the basis `(e₁, e₂)` it sends
`ė₁` to the class of `(1, 2)`, the image of `e₁` by the matrix with rows
`(1, 0)` and `(2, 1)`. -/
noncomputable def sigma (hR : Exceptional R) : Vtx R → Vtx R :=
  Quotient.lift (fun x => vtx (det2_sigma x.2.choose_spec))
    (fun x x' hx => (vtx_eq_iff _ _).2 (hR.sigma_rel x'.2.choose_spec x.2.choose_spec hx))

/-- **Pages 92 to 95, the commutant.** A map of `S_M = M*/±1` to itself that
commutes with `SL(2, R)` is a scalar `c ∈ R*`, or, when `2R ⊂ {0, 2}`, a scalar
times `σ`. No hypothesis on `R`; the map need not be assumed bijective. -/
theorem commutant (f : Vtx R → Vtx R) (hf : ∀ g v, f (act g v) = act g (f v)) :
    (∃ c : Rˣ, f = scal c) ∨ (∃ hR : Exceptional R, ∃ c : Rˣ, f = scal c ∘ sigma hR) := by
  sorry

end RankTwo

end Grothendieck.Folder79
