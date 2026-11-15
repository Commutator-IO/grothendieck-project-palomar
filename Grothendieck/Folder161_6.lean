module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


/-!
# Folder 161-6, pages 3–6, 12, 14 and 21: the golden number and the six axes of the icosahedron

The modernised reading `transcripts/161-6/161-6.modern.tex` builds the regular icosahedron
from two orthonormal vectors `u, v` and the angle `θ = 2π/5` (pages 3–10): the equilateral
condition `(1′) cos α = cos θ / (1 − cos θ)`, which has a solution `0 < α < π` exactly when
`θ > π/3` (the page writes `≥`), gives `cos α = 1/√5`. The page-6 verification of the lemma
on the neighbouring cap stops; the reading completes it and reduces it to two identities
(A) `c (1 − cos 2π/5) = cos 2π/5`, (B) `c (1 + cos π/5) = cos π/5`, `c = cos α`, which follow
from the golden equation `η² + η − 1 = 0` for `η = 2 cos(2π/5)`, that pages 14 and 12 derive
in `ℤ[1/5][ζ₅]` from the trace and the norm of `η = ζ + ζ⁻¹`. Page 21 passes to the six
lines through opposite vertices, computes `cos α = γ/(2 − γ) = (2γ + 1)/5 = 1/√5`,
`cos 2α = −3/5`, and boxes `B(x, y)² = (4/5) Q(x) Q(y)` and `B′(x, y)² = (1/5) Q(x) Q(y)`,
`B′ = B/2`, for generators `x, y` of two distinct lines; a margin writes `c² + c − 1 = 0` for
the constant `c = cos′(D_i, D_j) = B(x, y)²/(Q(x)Q(y)) − 2`.

Proved here:

* Golden number. `cos_two_pi_div_five`, `eta_eq_inv_goldenRatio`
  (`2 cos(2π/5) = φ⁻¹ = (√5 − 1)/2`), `eta_golden` (`η² + η − 1 = 0`), and, over any
  commutative ring with `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`, `trace_norm` (pages 14 and 12: `ζ⁵ = 1`,
  `Tr η = N η = −1`, `η² + η − 1 = 0`, `η′ = η² − 2`, `η = η′² − 2`).
* The angle. `exists_alpha_iff`: for `0 < θ ≤ π`, there is `0 < α < π` with
  `cos α = cos θ / (1 − cos θ)` iff `π/3 < θ`; `cos_alpha` (`= 1/√5` at `θ = 2π/5`),
  `identity_A`, `identity_B` (the reading's completion of page 6), `page21_cos_alpha`
  (`γ/(2 − γ) = (2γ + 1)/5` over any field where `γ² + γ − 1 = 0`) and `cos_two_alpha`.
* The six axes. Over any commutative ring with `t² = t + 1`, `axes_equiangular`:
  `5 B′(x_i, x_j)² = Q(x_i) Q(x_j)` for the six axes `(0, 1, ±t)`, `(1, ±t, 0)`, `(±t, 0, 1)`,
  `i ≠ j` — no division, so it holds in `ℤ[φ]`, and in characteristic `5`, where both
  sides vanish (`t = 3`, `Q(x_i) = t + 2 = 0`: the axes are isotropic, as in
  `Folder70.lean`). Over `ℝ`, with `t = φ`: `cos'_axes` (`cos′(D_i, D_j) = −6/5`, page 21) and `margin_false`.
* The twelve vertices, over `ℤ[√5]` in doubled coordinates (`2φ = 1 + √5`): `vert_norm`,
  `d2_values` (three distances: `16`, `24 + 8√5`, `40 + 8√5`), `nbrs_card` (each vertex has
  five neighbours at the minimal distance), `edges_card` (30 edges), `faces_card` (20 faces),
  `vert_neg` (the antipodal map permutes the vertices; it is `−1`, of determinant `−1`,
  `det_neg_one`).
* Rationality (the edition's statement, from the reading's remark on page 21):
  `isSquare_five_of_three_lines`: over any field, three vectors with `Q(x_i) ≠ 0` and
  `5 B′(x_i, x_j)² = Q(x_i) Q(x_j)` pairwise force `5` to be a square; `no_three_rat_lines`:
  so there are no three such lines over `ℚ`.

**What the formalisation finds.** The page-4 condition must be strict: at `θ = π/3` the
only solution is `α = 0`. The margin of page 21 is false as read: `c = −6/5` and
`c² + c − 1 = −19/25`; the golden relation is that of `η`, not of `cos′(D_i, D_j)`. The
equiangularity relation needs no division: `5 B′² = Q Q` holds over `ℤ[t]/(t² − t − 1)`. Its
« localement » needs `√5`: over a field where `5` is not a square, such as `ℚ`, three
mutually equiangular lines with this constant do not exist. That the edge graph has
`120` automorphisms, not the `60` rotations the page writes (pages 8–9), is `card_aut` of
`Folder86.lean`; here `vert_neg` gives the orientation-reversing automorphism `−1`.
-/

namespace Grothendieck.Folder161_6

open Real

/-! ## The golden number (pages 4, 6, 12, 14) -/

theorem sqrt5_sq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_pos : 0 < √5 := Real.sqrt_pos.2 (by norm_num)

theorem sqrt5_lt_three : √5 < 3 := by nlinarith [sqrt5_sq, sqrt5_pos]

theorem cos_two_pi_div_five : cos (2 * π / 5) = (√5 - 1) / 4 := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, cos_two_mul, cos_pi_div_five]
  linear_combination (1 / 8 : ℝ) * sqrt5_sq

/-- `η = 2 cos(2π/5)` is the inverse of the golden ratio, `(√5 − 1)/2`. -/
theorem eta_eq_inv_goldenRatio :
    2 * cos (2 * π / 5) = goldenRatio⁻¹ ∧ 2 * cos (2 * π / 5) = (√5 - 1) / 2 := by
  refine ⟨?_, ?_⟩
  · rw [inv_goldenRatio, goldenConj, cos_two_pi_div_five]; ring
  · rw [cos_two_pi_div_five]; ring

/-- The golden equation of `η = 2 cos(2π/5)`, page 12. -/
theorem eta_golden : (2 * cos (2 * π / 5)) ^ 2 + 2 * cos (2 * π / 5) - 1 = 0 := by
  rw [cos_two_pi_div_five]; linear_combination (1 / 4 : ℝ) * sqrt5_sq

/-- Pages 14 and 12, over any commutative ring in which `ζ` is a root of the fifth
cyclotomic polynomial: `η = ζ + ζ⁴`, `η′ = ζ² + ζ³` have trace and norm `−1`, `η` is a root of
`t² + t − 1`, and squaring permutes the two roots by `t ↦ t² − 2`. -/
theorem trace_norm {A : Type*} [CommRing A] (ζ : A) (h : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    ζ ^ 5 = 1 ∧ (ζ + ζ ^ 4) + (ζ ^ 2 + ζ ^ 3) = -1 ∧ (ζ + ζ ^ 4) * (ζ ^ 2 + ζ ^ 3) = -1 ∧
      (ζ + ζ ^ 4) ^ 2 + (ζ + ζ ^ 4) - 1 = 0 ∧ ζ ^ 2 + ζ ^ 3 = (ζ + ζ ^ 4) ^ 2 - 2 ∧
      ζ + ζ ^ 4 = (ζ ^ 2 + ζ ^ 3) ^ 2 - 2 := by
  have h5 : ζ ^ 5 = 1 := by linear_combination (ζ - 1) * h
  refine ⟨h5, by linear_combination h, by linear_combination (ζ + ζ ^ 2) * h5 + h, ?_, ?_, ?_⟩
  · linear_combination (2 + ζ ^ 3) * h5 + h
  · linear_combination (-(2 + ζ ^ 3)) * h5
  · linear_combination (-(2 + ζ)) * h5

/-! ## The angle `α` (pages 3–6) -/

/-- Page 4, corrected: for `0 < θ ≤ π`, the equilateral condition `(1′)` has a solution
`0 < α < π` iff `θ > π/3` (the page writes `θ ≥ π/3`; at `π/3` only `α = 0` is left). -/
theorem exists_alpha_iff {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π) :
    (∃ α, 0 < α ∧ α < π ∧ cos α = cos θ / (1 - cos θ)) ↔ π / 3 < θ := by
  have hc1 : cos θ < 1 := by
    simpa using cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ h0
  have hd : 0 < 1 - cos θ := by linarith
  constructor
  · rintro ⟨α, hα0, hαπ, hα⟩
    have hca : cos α < 1 := by simpa using cos_lt_cos_of_nonneg_of_le_pi le_rfl hαπ.le hα0
    rw [hα, div_lt_one hd] at hca
    by_contra hθ
    have := cos_le_cos_of_nonneg_of_le_pi h0.le (by linarith [pi_pos]) (not_lt.1 hθ)
    rw [cos_pi_div_three] at this
    linarith
  · intro hθ
    have hc : cos θ < 1 / 2 := by
      rw [← cos_pi_div_three]
      exact cos_lt_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) hπ hθ
    have hm : -1 ≤ cos θ := neg_one_le_cos θ
    have hlt : cos θ / (1 - cos θ) < 1 := by rw [div_lt_one hd]; linarith
    have hgt : -1 < cos θ / (1 - cos θ) := by rw [lt_div_iff₀ hd]; linarith
    exact ⟨arccos (cos θ / (1 - cos θ)), arccos_pos.2 hlt, arccos_lt_pi.2 hgt,
      cos_arccos hgt.le hlt.le⟩

/-- `(2)`: at `θ = 2π/5`, `cos α = cos θ / (1 − cos θ) = 1/√5`. -/
theorem cos_alpha : cos (2 * π / 5) / (1 - cos (2 * π / 5)) = 1 / √5 := by
  rw [cos_two_pi_div_five, div_eq_div_iff (by nlinarith [sqrt5_lt_three]) sqrt5_pos.ne']
  nlinarith [sqrt5_sq]

/-- Identity (A) of the reading's completion of page 6, `c (1 − cos 2π/5) = cos 2π/5`. -/
theorem identity_A : 1 / √5 * (1 - cos (2 * π / 5)) = cos (2 * π / 5) := by
  rw [← cos_alpha, div_mul_cancel₀]
  rw [cos_two_pi_div_five]; nlinarith [sqrt5_lt_three]

/-- Identity (B), `c (1 + cos π/5) = cos π/5`. -/
theorem identity_B : 1 / √5 * (1 + cos (π / 5)) = cos (π / 5) := by
  rw [cos_pi_div_five]
  field_simp
  nlinarith [sqrt5_sq]

/-- Page 21: `cos α = γ/(2 − γ) = (2γ + 1)/5` over any field in which `γ² + γ − 1 = 0` and
`5 ≠ 0` (then `2 − γ ≠ 0`). -/
theorem page21_cos_alpha {K : Type*} [Field K] {γ : K} (hγ : γ ^ 2 + γ - 1 = 0)
    (h5 : (5 : K) ≠ 0) : 2 - γ ≠ 0 ∧ γ / (2 - γ) = (2 * γ + 1) / 5 := by
  have h2 : 2 - γ ≠ 0 := by
    intro h
    have : γ = 2 := by linear_combination -h
    rw [this] at hγ
    exact h5 (by linear_combination hγ)
  refine ⟨h2, ?_⟩
  rw [div_eq_div_iff h2 h5]
  linear_combination (2 : K) * hγ

/-- `cos 2α = 2 cos² α − 1 = −3/5`. -/
theorem cos_two_alpha : 2 * (1 / √5) ^ 2 - 1 = -3 / 5 := by
  rw [div_pow, sqrt5_sq]; norm_num

/-! ## The six axes, over any ring with `t² = t + 1` (page 21) -/

section Axes

variable {R : Type*} [CommRing R]

/-- The bilinear form `B′(x, y) = x · y`. -/
def dot (x y : Fin 3 → R) : R := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- The six axes `(0, 1, ±t)`, `(1, ±t, 0)`, `(±t, 0, 1)` of the icosahedron. -/
def axis (t : R) : Fin 6 → Fin 3 → R :=
  ![![0, 1, t], ![0, 1, -t], ![1, t, 0], ![1, -t, 0], ![t, 0, 1], ![-t, 0, 1]]

theorem axis_norm {t : R} (ht : t ^ 2 = t + 1) (i : Fin 6) :
    dot (axis t i) (axis t i) = t + 2 := by
  fin_cases i <;> simp [dot, axis] <;> linear_combination ht

/-- The six axes are equiangular: `5 B′(x_i, x_j)² = Q(x_i) Q(x_j)` for `i ≠ j`. -/
theorem axes_equiangular {t : R} (ht : t ^ 2 = t + 1) {i j : Fin 6} (hij : i ≠ j) :
    5 * dot (axis t i) (axis t j) ^ 2 = dot (axis t i) (axis t i) * dot (axis t j) (axis t j) := by
  rw [axis_norm ht, axis_norm ht]
  have h4 : t ^ 4 = 3 * t + 2 := by linear_combination (t ^ 2 + t + 2) * ht
  fin_cases i <;> fin_cases j <;> simp [dot, axis] at hij ⊢ <;> ring_nf <;>
    simp only [h4, ht] <;> ring

end Axes

/-- Over `ℝ`, with `t = φ`: `cos′(D_i, D_j) = B(x, y)²/(Q(x)Q(y)) − 2 = −6/5`, `B = 2 B′`. -/
theorem cos'_axes {i j : Fin 6} (hij : i ≠ j) :
    (2 * dot (axis goldenRatio i) (axis goldenRatio j)) ^ 2 /
        (dot (axis goldenRatio i) (axis goldenRatio i) *
          dot (axis goldenRatio j) (axis goldenRatio j)) - 2 = -6 / 5 := by
  have ht : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hQ : dot (axis goldenRatio i) (axis goldenRatio i) *
      dot (axis goldenRatio j) (axis goldenRatio j) ≠ 0 := by
    rw [axis_norm ht, axis_norm ht]; nlinarith [goldenRatio_pos]
  rw [sub_eq_iff_eq_add, div_eq_iff hQ]
  linear_combination (4 / 5 : ℝ) * axes_equiangular ht hij

/-- The margin of page 21 is false as read: `c = −6/5` is not a root of `c² + c − 1`. -/
theorem margin_false : ((-6 / 5 : ℝ)) ^ 2 + (-6 / 5) - 1 = -19 / 25 ∧
    ((-6 / 5 : ℝ)) ^ 2 + (-6 / 5) - 1 ≠ 0 := by norm_num

/-! ## The twelve vertices over `ℤ[√5]`, in doubled coordinates -/

/-- `2φ = 1 + √5`. -/
def g : ℤ√5 := ⟨1, 1⟩

/-- The twelve vertices `±(0, 2, ±2φ)`, `±(2, ±2φ, 0)`, `±(±2φ, 0, 2)`: the doubled axes
and their opposites. -/
def vert : Fin 12 → Fin 3 → ℤ√5 :=
  ![![0, 2, g], ![0, 2, -g], ![2, g, 0], ![2, -g, 0], ![g, 0, 2], ![-g, 0, 2],
    ![0, -2, -g], ![0, -2, g], ![-2, -g, 0], ![-2, g, 0], ![-g, 0, -2], ![g, 0, -2]]

/-- Squared distance. -/
def d2 (x y : Fin 3 → ℤ√5) : ℤ√5 := dot (x - y) (x - y)

/-- The edge relation: squared distance `16`, i.e. distance `2` in the undoubled scale. -/
def Edge (i j : Fin 12) : Prop := d2 (vert i) (vert j) = 16

instance : DecidableRel Edge := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- All twelve vertices are on one sphere, `Q = 10 + 2√5`. -/
theorem vert_norm : ∀ i, dot (vert i) (vert i) = ⟨10, 2⟩ := by decide +kernel

/-- `16` is the minimal distance: every other squared distance between distinct vertices
is `24 + 8√5` (the « ℓ′ » distance) or `40 + 8√5` (the antipode). -/
theorem d2_values : ∀ i j, i ≠ j →
    d2 (vert i) (vert j) = 16 ∨ d2 (vert i) (vert j) = ⟨24, 8⟩ ∨
      d2 (vert i) (vert j) = ⟨40, 8⟩ := by decide +kernel

/-- Each vertex has five neighbours. -/
theorem nbrs_card : ∀ i, (Finset.univ.filter (fun j => Edge i j)).card = 5 := by
  decide +kernel

/-- Thirty edges. -/
theorem edges_card :
    (Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 < p.2 ∧ Edge p.1 p.2)).card = 30 := by
  decide +kernel

/-- Twenty faces: triples pairwise joined by an edge. -/
theorem faces_card :
    (Finset.univ.filter (fun p : Fin 12 × Fin 12 × Fin 12 =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ Edge p.1 p.2.1 ∧ Edge p.1 p.2.2 ∧ Edge p.2.1 p.2.2)).card
      = 20 := by
  decide +kernel

/-- The antipodal map `−1` permutes the vertices (`vert (i + 6) = −vert i`), hence the edges. -/
theorem vert_neg : ∀ i : Fin 12, ∃ j, vert j = -vert i ∧
    ∀ k, (Edge i k ↔ ∃ l, vert l = -vert k ∧ Edge j l) := by decide +kernel

theorem det_neg_one : Matrix.det (-1 : Matrix (Fin 3) (Fin 3) ℝ) = -1 := by
  rw [Matrix.det_neg, Matrix.det_one]; norm_num

/-! ## Rationality (the edition's statement, after the reading's remark on page 21) -/

/-- Over any field, three pairwise equiangular lines with constant `1/5` force `5` to be a
square: `5 B′(x_i, x_j)² = Q(x_i) Q(x_j)` for the three pairs, the `Q(x_i)` nonzero. -/
theorem isSquare_five_of_three_lines {K : Type*} [Field K] {q₁ q₂ q₃ b₁₂ b₁₃ b₂₃ : K}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hq₃ : q₃ ≠ 0)
    (h₁₂ : 5 * b₁₂ ^ 2 = q₁ * q₂) (h₁₃ : 5 * b₁₃ ^ 2 = q₁ * q₃) (h₂₃ : 5 * b₂₃ ^ 2 = q₂ * q₃) :
    IsSquare (5 : K) := by
  have hne : ∀ b : K, 5 * b ^ 2 ≠ 0 → (5 : K) ≠ 0 ∧ b ≠ 0 := fun b hb =>
    ⟨fun h => hb (by rw [h, zero_mul]), fun h => hb (by rw [h]; ring)⟩
  obtain ⟨h5, hb₁₂⟩ := hne b₁₂ (by rw [h₁₂]; exact mul_ne_zero hq₁ hq₂)
  obtain ⟨-, hb₁₃⟩ := hne b₁₃ (by rw [h₁₃]; exact mul_ne_zero hq₁ hq₃)
  obtain ⟨-, hb₂₃⟩ := hne b₂₃ (by rw [h₂₃]; exact mul_ne_zero hq₂ hq₃)
  refine ⟨q₁ * q₂ * q₃ / (5 * b₁₂ * b₁₃ * b₂₃), ?_⟩
  have hb : 5 * b₁₂ * b₁₃ * b₂₃ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨⟨⟨h5, hb₁₂⟩, hb₁₃⟩, hb₂₃⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
  linear_combination (25 * b₁₃ ^ 2 * b₂₃ ^ 2) * h₁₂ + (q₁ * q₂ * 5 * b₂₃ ^ 2) * h₁₃ +
    (q₁ * q₂ * (q₁ * q₃)) * h₂₃

/-- Hence there are no three such lines over `ℚ`: the « localement » of page 21 needs `√5`. -/
theorem no_three_rat_lines (x₁ x₂ x₃ : Fin 3 → ℚ) (hq₁ : dot x₁ x₁ ≠ 0) (hq₂ : dot x₂ x₂ ≠ 0)
    (hq₃ : dot x₃ x₃ ≠ 0) (h₁₂ : 5 * dot x₁ x₂ ^ 2 = dot x₁ x₁ * dot x₂ x₂)
    (h₁₃ : 5 * dot x₁ x₃ ^ 2 = dot x₁ x₁ * dot x₃ x₃)
    (h₂₃ : 5 * dot x₂ x₃ ^ 2 = dot x₂ x₂ * dot x₃ x₃) : False := by
  have h := isSquare_five_of_three_lines hq₁ hq₂ hq₃ h₁₂ h₁₃ h₂₃
  have : ¬ IsSquare ((5 : ℕ) : ℚ) := by
    rw [Rat.isSquare_natCast_iff]
    rintro ⟨r, hr⟩
    have : r ≤ 2 := by nlinarith
    interval_cases r <;> omega
  exact this (by exact_mod_cast h)

end Grothendieck.Folder161_6
