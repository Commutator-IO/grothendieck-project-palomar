module

public import Mathlib
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

@[expose] public section


/-!
# Folder 63, pages 97–99: the four components of `j = 0` at `p = 2` have distinct tangents

The modernised reading `transcripts/63/63.modern.tex` studies the level-3 moduli space over
`ℤ[1/3, ζ₃]`; page 97 asks whether the four irreducible components of `M′₃ ∩ V(c₄)` (the locus
`j = 0`) have distinct tangents at their common point `a` over `𝔽₄`, and page 99 opens
« … aux composantes irréductibles sont égales », the reading concluding that they share one
tangent. This is finding `63-level3-tangents-at-2`.

In the Hesse model the parameter is `t`, and `c₄` is, up to units, `t(t³ + 8)`
(Artebani–Dolgachev; taken as given here, the Hesse-to-Weierstrass computation is not
formalised). Write `R = ℤ[ζ]` (`AdjoinRoot (X² + X + 1)`), `A = R[t]`, and `P = (2, t)`, the
maximal ideal of the point `a` (`A/P = 𝔽₄`). Proved here:

* `factor`: `t³ + 8 = (t + 2)(t + 2ζ)(t + 2ζ²)`, so `V(c₄)` is the four sections `t = 0, −2,
  −2ζ, −2ζ²`, all through `a` (`branch_mem`);
* `tangents_distinct`: the tangent forms `t, t + 2, t + 2ζ, t + 2ζ²` are pairwise linearly
  independent in `P/P²` over `A/P`: `a f + b g ∈ P²` forces `a, b ∈ P`;
* `involution_transvection`: the Hesse involution `t ↦ (t + 2)/(t − 1)` sends `t` to `t + 2`
  modulo `P²` (`t − 1` is a unit at `P`), and fixes `2`: on `P/P²` it is the transvection
  `(2, t) ↦ (2, t + 2)`, which permutes the four tangent lines — one orbit of size four, not a
  common tangent.

**What the formalisation finds.** The four tangents are pairwise distinct, contrary to the
reading's conclusion. Where its argument breaks is the last item: the splitting `V₁ × V₂` of the
tangent space that page 99 asserts is not stable under the involution. Not formalised: that the
Hesse family is the level-3 moduli space, and the formula for `c₄`.
-/

open Polynomial

namespace Grothendieck.Folder63

/-- `ℤ[ζ]`, `ζ` a primitive cube root of unity. -/
abbrev R := AdjoinRoot (X ^ 2 + X + 1 : ℤ[X])

/-- `ζ`. -/
noncomputable abbrev ζ : R := AdjoinRoot.root _

theorem hζ : ζ ^ 2 + ζ + 1 = 0 := by
  have := AdjoinRoot.eval₂_root (X ^ 2 + X + 1 : ℤ[X])
  simpa using this

theorem ζ_cube : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ

theorem monic : (X ^ 2 + X + 1 : ℤ[X]).Monic := by monicity!

/-- The basis `1, ζ` of `R` over `ℤ`. -/
noncomputable def basis := (AdjoinRoot.powerBasis' monic).basis

/-- `R` is a free `ℤ`-module (basis `1, ζ`), so `2` can be cancelled. -/
theorem two_mul_cancel {x y : R} (h : 2 * x = 2 * y) : x = y := by
  have := Module.Free.of_basis basis
  have h2 : (2 : ℤ) • x = (2 : ℤ) • y := by simpa [two_smul, two_mul] using h
  exact smul_right_injective R (two_ne_zero : (2 : ℤ) ≠ 0) h2

/-- `P = (2, t)`. -/
noncomputable def P : Ideal R[X] := Ideal.span {C 2, X}

/-- The ideal `{h : 2 ∣ h(0)}`. -/
def J₁ : Ideal R[X] where
  carrier := {h | (2 : R) ∣ h.coeff 0}
  add_mem' := fun ha hb => by simpa [coeff_add] using dvd_add ha hb
  zero_mem' := by simp
  smul_mem' := fun c h hh => by
    simpa [mul_coeff_zero] using hh.mul_left (c.coeff 0)

/-- The ideal `{h : 4 ∣ h(0), 2 ∣ h'(0)}`. -/
def J₂ : Ideal R[X] where
  carrier := {h | (4 : R) ∣ h.coeff 0 ∧ (2 : R) ∣ h.coeff 1}
  add_mem' := fun ha hb => by
    simp only [Set.mem_ofPred_eq, coeff_add] at *
    exact ⟨dvd_add ha.1 hb.1, dvd_add ha.2 hb.2⟩
  zero_mem' := by simp
  smul_mem' := fun c h hh => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_coeff_zero] at *
    refine ⟨hh.1.mul_left _, ?_⟩
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h4 : (2 : R) ∣ h.coeff 0 := (dvd_mul_right 2 2).trans (by norm_num at hh ⊢; exact hh.1)
    exact dvd_add (hh.2.mul_left _) (h4.mul_left _)

theorem P_le : P ≤ J₁ := by
  rw [P, Ideal.span_le]
  rintro x (rfl | rfl)
  · show (2 : R) ∣ (C 2 : R[X]).coeff 0; simp
  · show (2 : R) ∣ (X : R[X]).coeff 0; simp

theorem mem_P {h : R[X]} : h ∈ P ↔ (2 : R) ∣ h.coeff 0 := by
  refine ⟨fun hh => P_le hh, fun ⟨c, hc⟩ => ?_⟩
  rw [← X_mul_divX_add h, hc, C_mul]
  exact P.add_mem (P.mul_mem_right _ (Ideal.subset_span (by simp)))
    (P.mul_mem_right _ (Ideal.subset_span (by simp)))

theorem P_sq_le : P ^ 2 ≤ J₂ := by
  rw [show P ^ 2 = P * P from sq P, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨u, hu⟩ := mem_P.1 hx
  obtain ⟨v, hv⟩ := mem_P.1 hy
  refine ⟨⟨u * v, by rw [mul_coeff_zero, hu, hv]; ring⟩, ?_⟩
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact ⟨u * y.coeff 1 + x.coeff 1 * v, by rw [hu, hv]; ring⟩

/-- The four values `0, 1, ζ, ζ²`. -/
noncomputable def α : Fin 4 → R := ![0, 1, ζ, ζ ^ 2]

/-- The four branches `t + 2α` of `V(c₄)` through `a`. -/
noncomputable def branch (i : Fin 4) : R[X] := X + 2 * C (α i)

/-- **`t³ + 8 = (t + 2)(t + 2ζ)(t + 2ζ²)`**, so `c₄ = t(t³ + 8)` is the product of the four
branches. -/
theorem factor : (X : R[X]) * (X ^ 3 + 8) = branch 0 * branch 1 * branch 2 * branch 3 := by
  have hC : (C ζ : R[X]) ^ 2 + C ζ + 1 = 0 := by
    simpa using congrArg C hζ
  simp only [branch, α, Matrix.cons_val, C_0, C_1, map_pow]
  linear_combination (-(X : R[X]) * (2 * X ^ 2 + 4 * C ζ * X + 8 * (C ζ - 1))) * hC

theorem branch_mem (i : Fin 4) : branch i ∈ P := by
  rw [mem_P]
  simp [branch, coeff_X_zero]

theorem coeff_mul_branch (a : R[X]) (c : R) :
    (a * (X + 2 * C c)).coeff 0 = 2 * c * a.coeff 0 ∧
      (a * (X + 2 * C c)).coeff 1 = a.coeff 0 + 2 * c * a.coeff 1 := by
  rw [show (2 : R[X]) * C c = C (2 * c) by rw [map_mul, map_ofNat], mul_add]
  constructor
  · rw [coeff_add, coeff_mul_X_zero, coeff_mul_C]; ring
  · have h1 : (a * X).coeff 1 = a.coeff 0 := coeff_mul_X a 0
    rw [coeff_add, h1, coeff_mul_C]; ring

/-- Two tangent forms `t + 2α`, `t + 2β` with `α − β` a unit modulo `2` are independent in
`P/P²`. -/
theorem indep {α β : R} (hαβ : ∃ ε m : R, (α - β) * ε = 1 + 2 * m) (a b : R[X])
    (h : a * (X + 2 * C α) + b * (X + 2 * C β) ∈ P ^ 2) : a ∈ P ∧ b ∈ P := by
  obtain ⟨h0, h1⟩ := P_sq_le h
  obtain ⟨ha0, ha1⟩ := coeff_mul_branch a α
  obtain ⟨hb0, hb1⟩ := coeff_mul_branch b β
  rw [coeff_add, ha0, hb0] at h0
  rw [coeff_add, ha1, hb1] at h1
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  -- `α a₀ + β b₀ = 2u` and `b₀ = 2w − a₀`
  have hu' : α * a.coeff 0 + β * b.coeff 0 = 2 * u :=
    two_mul_cancel (by linear_combination hu)
  set w := v - α * a.coeff 1 - β * b.coeff 1
  have hb : b.coeff 0 = 2 * w - a.coeff 0 := by linear_combination hv
  obtain ⟨ε, m, hε⟩ := hαβ
  have ha : a.coeff 0 = 2 * (ε * (u - β * w) - m * a.coeff 0) := by
    linear_combination ε * hu' - ε * β * hb - a.coeff 0 * hε
  refine ⟨mem_P.2 ⟨_, ha⟩, mem_P.2 ⟨w - (ε * (u - β * w) - m * a.coeff 0), ?_⟩⟩
  linear_combination hb - ha

theorem unit_mod_two (i j : Fin 4) (hij : i ≠ j) :
    ∃ ε m : R, (α i - α j) * ε = 1 + 2 * m := by
  have h3 := ζ_cube
  fin_cases i <;> fin_cases j <;> simp only [α, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    at hij ⊢
  all_goals first
    | exact absurd rfl hij
    | (refine ⟨-1, 0, ?_⟩; ring1)
    | (refine ⟨1, 0, ?_⟩; ring1)
    | (refine ⟨-ζ ^ 2, 0, ?_⟩; linear_combination h3)
    | (refine ⟨ζ ^ 2, 0, ?_⟩; linear_combination h3)
    | (refine ⟨-ζ, 0, ?_⟩; linear_combination h3)
    | (refine ⟨ζ, 0, ?_⟩; linear_combination h3)
    | (refine ⟨1 - ζ ^ 2, 1, ?_⟩; linear_combination (-1 : R) * hζ + h3)
    | (refine ⟨-(1 - ζ ^ 2), 1, ?_⟩; linear_combination (-1 : R) * hζ + h3)
    | (refine ⟨1 - ζ, 1, ?_⟩; linear_combination (-1 : R) * hζ + h3)
    | (refine ⟨-(1 - ζ), 1, ?_⟩; linear_combination (-1 : R) * hζ + h3)
    | (refine ⟨ζ ^ 2 * (1 - ζ ^ 2), 1, ?_⟩
       linear_combination (-ζ ^ 3) * hζ + (3 + ζ ^ 3) * h3)
    | (refine ⟨-(ζ ^ 2 * (1 - ζ ^ 2)), 1, ?_⟩
       linear_combination (-ζ ^ 3) * hζ + (3 + ζ ^ 3) * h3)

/-- **The four tangents are pairwise distinct**: for `i ≠ j`, `a · branch i + b · branch j ∈ P²`
forces `a, b ∈ P`. -/
theorem tangents_distinct (i j : Fin 4) (hij : i ≠ j) (a b : R[X])
    (h : a * branch i + b * branch j ∈ P ^ 2) : a ∈ P ∧ b ∈ P :=
  indep (unit_mod_two i j hij) a b h

/-- **The Hesse involution is a transvection on `P/P²`**: `σ(t) = (t + 2)/(t − 1)` satisfies
`(t + 2) − (t − 1)(t + 2) ∈ P²`, i.e. `σ(t) ≡ t + 2` modulo `P²` once divided by the unit
`t − 1`, and `σ(t) ∈ P`. -/
theorem involution_transvection :
    (X + 2 : R[X]) - (X - 1) * (X + 2) ∈ P ^ 2 ∧ (X + 2 : R[X]) ∈ P ∧ (X - 1 : R[X]) ∉ P := by
  refine ⟨?_, ?_, ?_⟩
  · have hX : (X : R[X]) ∈ P := Ideal.subset_span (by simp)
    have h2 : (C 2 : R[X]) ∈ P := Ideal.subset_span (by simp)
    have : (X + 2 : R[X]) - (X - 1) * (X + 2) = C 2 * C 2 - X * X := by
      rw [map_ofNat]; ring
    rw [this, show P ^ 2 = P * P from sq P]
    exact Ideal.sub_mem _ (Ideal.mul_mem_mul h2 h2) (Ideal.mul_mem_mul hX hX)
  · rw [mem_P]; simp
  · rw [mem_P]
    simp only [coeff_sub, coeff_X_zero, coeff_one_zero, zero_sub]
    rintro ⟨c, hc⟩
    -- `−1 = 2c` is impossible: compare the coordinates on `1` in the basis `1, ζ`
    have hdim : 0 < (AdjoinRoot.powerBasis' monic).dim := by
      have h2 : (X ^ 2 + X + 1 : ℤ[X]).natDegree = 2 := by compute_degree!
      rw [AdjoinRoot.powerBasis'_dim, h2]; norm_num
    let i0 : Fin (AdjoinRoot.powerBasis' monic).dim := ⟨0, hdim⟩
    have h1 : basis i0 = 1 := by simp [basis, i0, PowerBasis.basis_eq_pow]
    have h2 : (2 : R) * c = (2 : ℤ) • c := by rw [zsmul_eq_mul]; norm_num
    have := congrArg (fun x => basis.repr x i0) hc
    simp only [h2, map_zsmul, map_neg, ← h1, Module.Basis.repr_self] at this
    simp at this
    omega

end Grothendieck.Folder63
