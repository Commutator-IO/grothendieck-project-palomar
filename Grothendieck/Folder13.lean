module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section


/-!
# Folder 13, page 47: the « double niveau » question, and its Tate case

Page 47 of folder 13 (« Groupe de Galois motivique », 1965; transcription
`transcripts/13/batch-03.fr.tex`, modernised reading `transcripts/13/13.modern.tex`, section
« Foncteurs pleinement fidèles ») asks whether, over an algebraic extension of `ℚ`, the functor
`M ↦ (T_DR(M), T_B(M), φ)` is fully faithful: the de Rham–Betti form of what is now called
Grothendieck's period conjecture. With `G` the motivic Galois group and `g ∈ G(ℂ)` placing the
de Rham lattice, `T_DR(M) = g(V_ℚ̄)` inside `V ⊗ ℂ`, the question becomes whether the inclusion
`V^G ⊂ V ∩ g(V̄)` is an equality for every `G`-module `V`. The page reduces to `V` simple and
says of the rank-one case: « c'est une puissance de Tate, et ça marche ».

This file proves the two things the page states and does not argue, in models of the edition's
choosing:

* `invariants_subset_inter_smul` (Grothendieck, page 47, the inclusion « `V^G ⊂ V ∩ g(V̄)` »):
  for a group acting on a set, an element of `B ⊆ Λ` fixed by the whole group lies in
  `B ∩ g • Λ`. Here `B` plays the Betti lattice `V`, `Λ` the space `V̄ = V ⊗ ℚ̄`, and `g • Λ`
  the de Rham lattice. `mem_inter_smul_iff`: `x ∈ B ∩ g • Λ` iff `x ∈ B` and `g⁻¹ • x ∈ Λ`,
  the description of `V ∩ T'(V)` of page 33.
* `tate` (Grothendieck, page 47, « ça marche », forme reconstituée par l'édition): for the
  Tate motive `ℚ(n)`, the Betti line is `ℚ ⊂ ℂ` and the de Rham line is `(2πi)ⁿ ℚ̄`, and the
  motivic Galois group `𝔾_m` acts by the `n`-th power, so `V^G` is `ℚ` for `n = 0` and `0`
  otherwise. The theorem says that `ℚ ∩ (2πi)ⁿ ℚ̄` is exactly that: all of `ℚ` for `n = 0`,
  `{0}` for `n ≠ 0`. The equality `V^G = V ∩ g(V̄)` thus holds in rank one.

**Hypothesis, not proved here.** For `n ≠ 0` the argument needs the transcendence of `π`
(Lindemann, 1882), which Mathlib does not have at the pinned revision (it has the analytic part
of Lindemann–Weierstrass, `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`,
and `irrational_pi`). It is taken as the explicit hypothesis `hπ`. Everything else, that `i`
is algebraic and that `z` is algebraic when a nonzero integer power of it is, is proved.

The identification of `ℚ(n)` with these two lines inside `ℂ`, and of `V^G` with `ℚ` or `0`, is
the edition's model and is not formalised; the page writes neither. The general question of
page 47, for motives that are not of Tate type, is open: it is the period conjecture.
-/

open Complex Polynomial
open scoped Pointwise

namespace Grothendieck.Folder13

/-- Page 33: `x ∈ B ∩ g • Λ` iff `x ∈ B` and `g⁻¹ • x ∈ Λ` (« `V ∩ T'(V)` »). -/
theorem mem_inter_smul_iff {Γ M : Type*} [Group Γ] [MulAction Γ M] (B Λ : Set M) (g : Γ)
    (x : M) : x ∈ B ∩ g • Λ ↔ x ∈ B ∧ g⁻¹ • x ∈ Λ := by
  rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem]

/-- **Grothendieck, page 47** (the inclusion `V^G ⊂ V ∩ g(V̄)`): an element of `B ⊆ Λ` fixed
by every element of the group lies in `B ∩ g • Λ`, for every `g`. -/
theorem invariants_subset_inter_smul {Γ M : Type*} [Group Γ] [MulAction Γ M] {B Λ : Set M}
    (hB : B ⊆ Λ) (g : Γ) : {x | x ∈ B ∧ ∀ h : Γ, h • x = x} ⊆ B ∩ g • Λ := by
  rintro x ⟨hx, hfix⟩
  refine (mem_inter_smul_iff B Λ g x).2 ⟨hx, ?_⟩
  rw [hfix]
  exact hB hx

/-- `i` is algebraic over `ℚ`. -/
theorem isAlgebraic_I : IsAlgebraic ℚ (I : ℂ) := ⟨X ^ 2 + 1, by
  intro h; have := congrArg (fun p => p.coeff 0) h; simp at this, by simp⟩

/-- If a nonzero integer power of `z` is algebraic, so is `z`. -/
theorem isAlgebraic_of_zpow {z : ℂ} {n : ℤ} (hn : n ≠ 0) (h : IsAlgebraic ℚ (z ^ n)) :
    IsAlgebraic ℚ z := by
  rcases Int.natAbs_eq n with hn' | hn'
  · rw [hn', zpow_natCast] at h
    exact h.of_pow (by omega)
  · rw [hn', zpow_neg, zpow_natCast, IsAlgebraic.inv_iff] at h
    exact h.of_pow (by omega)

/-- **Grothendieck, page 47, the Tate case** (« c'est une puissance de Tate, et ça marche »;
forme reconstituée par l'édition). For the Tate motive `ℚ(n)`, the rational numbers lying in
the de Rham line `(2πi)ⁿ ℚ̄` are all of `ℚ` when `n = 0` and only `0` otherwise, which is
`V^G` for the weight-`n` character of `𝔾_m`. Assumes the transcendence of `π` (Lindemann),
not in Mathlib. -/
theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} := by
  split_ifs with hn
  · subst hn
    ext q; simp only [Set.mem_ofPred_eq, zpow_zero, one_mul, Set.mem_univ, iff_true]
    exact ⟨q, isAlgebraic_algebraMap (q : ℚ), rfl⟩
  · ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨α, hα, hq⟩
      by_contra hq0
      have hα0 : α ≠ 0 := by rintro rfl; simp at hq; exact hq0 hq
      have h2 : IsAlgebraic ℚ ((2 * Real.pi * I) ^ n) := by
        have : (2 * Real.pi * I) ^ n = (q : ℂ) * α⁻¹ := by
          rw [hq]; field_simp
        rw [this]
        exact (isAlgebraic_algebraMap (q : ℚ)).mul (IsAlgebraic.inv_iff.mpr hα)
      have h1 := isAlgebraic_of_zpow hn h2
      apply hπ
      have : (Real.pi : ℂ) = (2 * Real.pi * I) * (2 * I)⁻¹ := by
        field_simp
      have h2I : IsAlgebraic ℚ ((2 : ℂ) * I) := by
        simpa using (isAlgebraic_algebraMap (2 : ℚ) (A := ℂ)).mul isAlgebraic_I
      rw [this]
      exact h1.mul (IsAlgebraic.inv_iff.mpr h2I)
    · rintro rfl; exact ⟨0, isAlgebraic_zero, by simp⟩

end Grothendieck.Folder13
