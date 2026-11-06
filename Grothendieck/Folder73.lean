module

public import Mathlib

@[expose] public section


/-!
# Folder 73 (« Polygones », [from 1976]): ear areas of plane polygons

The modernised reading `transcripts/73/73.modern.tex` studies the map sending a plane
`n`-gon, given by its sides `u_i = s_{i+1} - s_i`, to the doubled signed areas of its
« ears », `μ_i = u_{i-1} ∧ u_i`. Three of its statements are proved here; they are findings
`73-quadrilateral-projective-frame` and `73-zero-multiplier-criterion` of
`src/content/findings.ts`, and the reachable part of `73-ear-area-multiplier-classification`
(pages 23–28, at the end of the file). Proving them says only that the claims hold as
stated; whether they stand in the literature is a separate question.

The plane is `k²` (`Fin 2 → k`) with the volume form `a ∧ b = a₀b₁ - a₁b₀`; an affine map
acts on sides through its linear part, a `2 × 2` matrix.

## Pages 5–6: closed quadrilaterals form a projective plane

* `mu_relation`: `μ₀ + μ₂ = μ₁ + μ₃` for a closed quadrilateral, over any commutative ring,
  from `wedge_diag`: `u₀ ∧ u₂ = μ₀ - μ₁ = μ₃ - μ₂` and `u₁ ∧ u₃ = μ₁ - μ₂ = μ₀ - μ₃`. The
  page's second line `u₁ ∧ u₃ = μ₀ - μ₂`, copied by the reading, is false
  (`not_wedge13_eq`); the page's own fourth line has the right value. The six products
  `u_i ∧ u_j` are combinations of the `μ_i` (`wedge_eq_zero_of_mu`), so a quadrilateral not
  contained in a line has some `μ_i ≠ 0`.
* `mu_mulVec`: a linear map `M` multiplies every `μ_i` by `det M`.
* `quad_moduli` (injectivity on affine classes): two closed non-collinear quadrilaterals
  have proportional ear areas if and only if one is the image of the other by an invertible
  linear map; `exists_quad_of_mu` (surjectivity, the page's « épi ? »): every nonzero point
  of the plane `μ₀ + μ₂ = μ₁ + μ₃` is the ear-area vector of a closed quadrilateral.
* `side_eq_zero_iff`, `mu_eq_smul_framePt`: for a closed non-collinear quadrilateral,
  `u_i = 0 ⇔ μ_i = μ_{i+1} = 0`, and then `μ` is a nonzero multiple of the point `p_i`
  (`(0,0,1,1)`, `(1,0,0,1)`, `(1,1,0,0)`, `(0,1,1,0)` for `i = 0, 1, 2, 3`).
* `sum_smul_framePt_eq_zero_iff`, `framePt_three_indep`: the only relation among the
  `p_i` is the alternating one, so any three are independent (a projective frame);
  `frame_canonical`: `k⁴ / k·(1,1,1,1)` is linearly isomorphic to the plane, the class of
  the `i`-th basis vector going to `(-1)ⁱ p_i` — the plane is `P(k^A / k·(1,1,1,1))`. The
  sign is needed: `e_i ↦ p_i` has kernel `k·(1,-1,1,-1)`.

Proved over a field (the identities over any commutative ring); the page's `P²_ℤ`, the
statement over `Spec ℤ` as an isomorphism of schemes, is not formalised.

## Pages 15, 18, 28: the zero-multiplier criterion

For `u : ZMod n → k²` with all `u_i ≠ 0`, the multipliers are the `λ` with
`λ_i u_{i-1} - λ_{i+1}(u_i + u_{i+1}) + λ_{i+2} u_{i+2} = 0` for all `i` (`IsMult`). The
juxtaposition `u·v` of the page is read in `Sym² V`, here `k³` through
`a·b ↦ (a₀b₀, a₀b₁ + a₁b₀, a₁b₁)` (`symProd`).

* `zero_multiplier_criterion`: a multiplier with `λ₀ = 0`, `λ₁ = 1` exists if and only if
  `Σ u_i = 0` and, for `2 ≤ i ≤ n - 1`, either `s_i = s_0` (`u_{0i} = 0`) or the pair of
  directions of `{u_{i-1}, u_i}` is that of `{u_1, u_{0i}}`.
* `symProd_formula`: it then satisfies `λ_i u_{i-1}·u_i = u_1·u_{0i}` for every `i ≥ 1`;
  `mult_eq_zero_iff`: `λ_i = 0 ⇔ s_i = s_0`; `mult_unique`: it is unique.
* `eq_zero_of_consecutive`: a multiplier with two consecutive zero components is zero,
  which justifies the normalisation `λ₁ = 1`.
* `symProd_proportional_iff`: for nonzero vectors of a plane, `c·d ∈ k·(a·b)` if and only if
  `{[a], [b]} = {[c], [d]}` — the factorisation fact the « pair of directions » rests on.
-/

namespace Folder73

open Matrix

variable {k : Type*}

/-- The volume form on `k²`: `a ∧ b = a₀b₁ - a₁b₀`. -/
def wedge [CommRing k] (a b : Fin 2 → k) : k := a 0 * b 1 - a 1 * b 0

section Basic

variable [CommRing k]

theorem wedge_swap (a b : Fin 2 → k) : wedge b a = -wedge a b := by
  unfold wedge; ring

theorem wedge_self (a : Fin 2 → k) : wedge a a = 0 := by
  unfold wedge; ring

/-- Cramer's rule in the plane. -/
theorem cramer (a b x : Fin 2 → k) :
    wedge a b • x = wedge x b • a + wedge a x • b := by
  funext j; fin_cases j <;> simp [wedge] <;> ring

theorem wedge_mulVec (M : Matrix (Fin 2) (Fin 2) k) (a b : Fin 2 → k) :
    wedge (M *ᵥ a) (M *ᵥ b) = M.det * wedge a b := by
  simp [wedge, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

end Basic

/-! ## Quadrilaterals (pages 5–6) -/

section Quadrilateral

variable [CommRing k]

/-- The ear areas of a quadrilateral given by its sides: `μ_i = u_{i-1} ∧ u_i`. -/
def mu (u : Fin 4 → Fin 2 → k) (i : Fin 4) : k := wedge (u (i - 1)) (u i)

/-- A quadrilateral given by its sides is closed when they add up to zero. -/
def Closed (u : Fin 4 → Fin 2 → k) : Prop := ∑ i, u i = 0

theorem mu_zero (u : Fin 4 → Fin 2 → k) : mu u 0 = wedge (u 3) (u 0) := rfl
theorem mu_one (u : Fin 4 → Fin 2 → k) : mu u 1 = wedge (u 0) (u 1) := rfl
theorem mu_two (u : Fin 4 → Fin 2 → k) : mu u 2 = wedge (u 1) (u 2) := rfl
theorem mu_three (u : Fin 4 → Fin 2 → k) : mu u 3 = wedge (u 2) (u 3) := rfl

theorem closed_iff (u : Fin 4 → Fin 2 → k) : Closed u ↔ u 3 = -(u 0 + u 1 + u 2) := by
  unfold Closed
  rw [Fin.sum_univ_four]
  constructor
  · intro h; rw [← sub_eq_zero, sub_neg_eq_add, ← h]; abel
  · intro h; rw [h]; abel

/-- The two diagonal products of a closed quadrilateral (page 5): `u₀ ∧ u₂ = μ₀ - μ₁ =
μ₃ - μ₂` and `u₁ ∧ u₃ = μ₁ - μ₂ = μ₀ - μ₃`. -/
theorem wedge_diag (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    wedge (u 0) (u 2) = mu u 0 - mu u 1 ∧ wedge (u 0) (u 2) = mu u 3 - mu u 2 ∧
      wedge (u 1) (u 3) = mu u 1 - mu u 2 ∧ wedge (u 1) (u 3) = mu u 0 - mu u 3 := by
  rw [closed_iff] at h
  simp only [mu_zero, mu_one, mu_two, mu_three, h, wedge, Pi.neg_apply, Pi.add_apply]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- The second line of the page-5 table, `u₁ ∧ u₃ = μ₀ - μ₂`, copied by the reading, is
false: the square `u = (e₁, e₂, e₂, -e₁ - 2e₂)` has `u₁ ∧ u₃ = 1` and `μ₀ - μ₂ = 2`. The
true value, `μ₁ - μ₂ = μ₀ - μ₃`, is the one the page's fourth line gives for `u₃ ∧ u₁`. -/
theorem not_wedge13_eq :
    ¬ ∀ u : Fin 4 → Fin 2 → ℚ, Closed u → wedge (u 1) (u 3) = mu u 0 - mu u 2 := by
  intro h
  have := h ![![1, 0], ![0, 1], ![0, 1], ![-1, -2]] (by
    rw [closed_iff]; funext j; fin_cases j <;> norm_num)
  norm_num [mu_zero, mu_two, wedge] at this

/-- Page 5: `μ₀ + μ₂ = μ₁ + μ₃`. -/
theorem mu_relation (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    mu u 0 + mu u 2 = mu u 1 + mu u 3 := by
  obtain ⟨h1, h2, -⟩ := wedge_diag u h
  linear_combination h2 - h1

/-- All six products `u_i ∧ u_j` of a closed quadrilateral vanish when its ear areas do:
a closed quadrilateral not contained in a line has a nonzero ear area. -/
theorem wedge_eq_zero_of_mu (u : Fin 4 → Fin 2 → k) (h : Closed u)
    (hμ : ∀ i, mu u i = 0) (i j : Fin 4) : wedge (u i) (u j) = 0 := by
  obtain ⟨h02, -, h13, -⟩ := wedge_diag u h
  obtain ⟨e0, e1, e2, e3⟩ : wedge (u 3) (u 0) = 0 ∧ wedge (u 0) (u 1) = 0 ∧
      wedge (u 1) (u 2) = 0 ∧ wedge (u 2) (u 3) = 0 := ⟨hμ 0, hμ 1, hμ 2, hμ 3⟩
  rw [hμ 0, hμ 1, sub_zero] at h02
  rw [hμ 1, hμ 2, sub_zero] at h13
  have s := fun a b : Fin 4 => wedge_swap (u a) (u b)
  fin_cases i <;> fin_cases j <;>
    simp [wedge_self, e0, e1, e2, e3, h02, h13, s 0 1, s 0 2, s 1 2, s 1 3, s 2 3, s 3 0]

/-- Affine invariance: a linear map multiplies every ear area by its determinant. -/
theorem mu_mulVec (M : Matrix (Fin 2) (Fin 2) k) (u : Fin 4 → Fin 2 → k) (i : Fin 4) :
    mu (fun j => M *ᵥ u j) i = M.det * mu u i :=
  wedge_mulVec M _ _

theorem closed_mulVec (M : Matrix (Fin 2) (Fin 2) k) (u : Fin 4 → Fin 2 → k)
    (h : Closed u) : Closed (fun j => M *ᵥ u j) := by
  unfold Closed at *
  rw [← Matrix.mulVec_sum, h, Matrix.mulVec_zero]

/-- The chart `μ₁ ≠ 0` of page 5: `μ₁ u₂ = -μ₂ u₀ + (μ₃ - μ₂) u₁`. -/
theorem chart (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    mu u 1 • u 2 = -mu u 2 • u 0 + (mu u 3 - mu u 2) • u 1 := by
  rw [mu_one, cramer, wedge_swap, ← mu_two, (wedge_diag u h).2.1]

/-- Rotating the labels of a quadrilateral. -/
def rot (r : Fin 4) (u : Fin 4 → Fin 2 → k) : Fin 4 → Fin 2 → k := fun j => u (j + r)

theorem mu_rot (r : Fin 4) (u : Fin 4 → Fin 2 → k) (j : Fin 4) :
    mu (rot r u) j = mu u (j + r) := by
  simp only [mu, rot, sub_add_eq_add_sub]

theorem closed_rot (r : Fin 4) (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    Closed (rot r u) :=
  (Equiv.sum_comp (Equiv.addRight r) u).trans h

end Quadrilateral

section QuadField

variable [Field k]

/-- Injectivity in the chart `μ₁ ≠ 0`. -/
theorem exists_matrix_of_mu_one (u u' : Fin 4 → Fin 2 → k) (hu : Closed u) (hu' : Closed u')
    (c : k) (hc : c ≠ 0) (hμ : ∀ i, mu u' i = c * mu u i) (h1 : mu u 1 ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) k, M.det = c ∧ ∀ i, u' i = M *ᵥ u i := by
  set m := mu u 1 with hm
  let M : Matrix (Fin 2) (Fin 2) k := m⁻¹ •
    !![u' 0 0 * u 1 1 - u' 1 0 * u 0 1, -(u' 0 0 * u 1 0) + u' 1 0 * u 0 0;
       u' 0 1 * u 1 1 - u' 1 1 * u 0 1, -(u' 0 1 * u 1 0) + u' 1 1 * u 0 0]
  have hm' : m = u 0 0 * u 1 1 - u 0 1 * u 1 0 := by rw [hm, mu_one]; rfl
  obtain ⟨e0, e1⟩ : M *ᵥ u 0 = u' 0 ∧ M *ᵥ u 1 = u' 1 := by
    constructor <;> funext r <;> fin_cases r <;>
      · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        rw [hm']; ring
  -- u'₂ from the chart of u'
  have e2 : M *ᵥ u 2 = u' 2 := by
    have c1 := chart u hu
    have c2 := chart u' hu'
    rw [hμ 1, hμ 2, hμ 3, ← hm] at c2
    have : m • (M *ᵥ u 2) = m • u' 2 := by
      rw [← Matrix.mulVec_smul, c1, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, e0, e1]
      apply smul_right_injective _ hc
      simp only [smul_add, smul_smul] at c2 ⊢
      rw [c2]; congr 1 <;> congr 1 <;> ring
    exact smul_right_injective _ h1 this
  have e3 : M *ᵥ u 3 = u' 3 := by
    rw [(closed_iff u).1 hu, (closed_iff u').1 hu', Matrix.mulVec_neg, Matrix.mulVec_add,
      Matrix.mulVec_add, e0, e1, e2]
  have hfun : (fun j => M *ᵥ u j) = u' := by
    funext j; fin_cases j <;> assumption
  refine ⟨M, ?_, fun i => (congrFun hfun i).symm⟩
  have := mu_mulVec M u 1
  rw [hfun, hμ 1, ← hm] at this
  exact (mul_right_cancel₀ h1 this).symm

/-- Injectivity on affine classes (page 5, « mono »): closed quadrilaterals with
proportional ear areas, the first not contained in a line, differ by a linear map of
determinant the ratio. -/
theorem exists_matrix_of_mu (u u' : Fin 4 → Fin 2 → k) (hu : Closed u) (hu' : Closed u')
    (c : k) (hc : c ≠ 0) (hμ : ∀ i, mu u' i = c * mu u i) (hne : ∃ i, mu u i ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) k, M.det = c ∧ ∀ i, u' i = M *ᵥ u i := by
  obtain ⟨i, hi⟩ := hne
  set r : Fin 4 := i - 1
  have h1 : mu (rot r u) 1 ≠ 0 := by
    rw [mu_rot]; convert hi using 2; simp [r]
  obtain ⟨M, hM, hM'⟩ := exists_matrix_of_mu_one (rot r u) (rot r u') (closed_rot r u hu)
    (closed_rot r u' hu') c hc (fun j => by rw [mu_rot, mu_rot, hμ]) h1
  exact ⟨M, hM, fun j => by simpa [rot] using hM' (j - r)⟩

/-- Pages 5–6, the bijection on affine classes: two closed quadrilaterals not contained in
a line have proportional ear areas exactly when one is the image of the other by an
invertible linear map. -/
theorem quad_moduli (u u' : Fin 4 → Fin 2 → k) (hu : Closed u) (hu' : Closed u')
    (hne : ∃ i, mu u i ≠ 0) :
    (∃ M : Matrix (Fin 2) (Fin 2) k, M.det ≠ 0 ∧ ∀ i, u' i = M *ᵥ u i) ↔
      ∃ c : k, c ≠ 0 ∧ ∀ i, mu u' i = c * mu u i := by
  constructor
  · rintro ⟨M, hM, hM'⟩
    refine ⟨M.det, hM, fun i => ?_⟩
    rw [show u' = fun j => M *ᵥ u j from funext hM', mu_mulVec]
  · rintro ⟨c, hc, hμ⟩
    obtain ⟨M, hM, hM'⟩ := exists_matrix_of_mu u u' hu hu' c hc hμ hne
    exact ⟨M, hM ▸ hc, hM'⟩

/-- Surjectivity in the chart `m₁ ≠ 0`. -/
theorem exists_quad_of_mu_one (m : Fin 4 → k) (hrel : m 0 + m 2 = m 1 + m 3) (h1 : m 1 ≠ 0) :
    ∃ u : Fin 4 → Fin 2 → k, Closed u ∧ mu u = m := by
  let u0 : Fin 2 → k := ![m 1, 0]
  let u1 : Fin 2 → k := ![0, 1]
  let u2 : Fin 2 → k := ![-m 2, (m 3 - m 2) / m 1]
  refine ⟨![u0, u1, u2, -(u0 + u1 + u2)], ?_, ?_⟩
  · rw [closed_iff]; rfl
  · funext i
    fin_cases i
    · show wedge _ _ = _
      simp [wedge, u0, u1, u2]
      field_simp
      first | linear_combination hrel | linear_combination -hrel
    · show wedge _ _ = _
      simp [wedge, u0, u1]
    · show wedge _ _ = _
      simp [wedge, u1, u2]
    · show wedge _ _ = _
      simp [wedge, u0, u1, u2]
      field_simp
      ring

/-- Page 5, « épi ? »: every nonzero point of the plane `μ₀ + μ₂ = μ₁ + μ₃` is the
ear-area vector of a closed quadrilateral. -/
theorem exists_quad_of_mu (m : Fin 4 → k) (hrel : m 0 + m 2 = m 1 + m 3) (hm : m ≠ 0) :
    ∃ u : Fin 4 → Fin 2 → k, Closed u ∧ mu u = m := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := Function.ne_iff.mp hm
  have hA : ∀ i : Fin 4, 1 + (i - 1) = i := by decide
  have hrot : ∀ r : Fin 4, m (0 + r) + m (2 + r) = m (1 + r) + m (3 + r) := fun r => by
    fin_cases r <;> simp <;> first | linear_combination hrel | linear_combination -hrel
  set r : Fin 4 := i - 1
  have h1 : m (1 + r) ≠ 0 := by rw [show (1 : Fin 4) + r = i by simp only [r]; exact hA i]; exact hi
  obtain ⟨u, hu, hmu⟩ := exists_quad_of_mu_one (fun j => m (j + r)) (hrot r) h1
  refine ⟨rot (-r) u, closed_rot _ u hu, funext fun j => ?_⟩
  rw [mu_rot, hmu]
  simp

/-- A side is zero exactly when the two ears containing it are flat (page 5, boxed for
`u₂`), for a closed quadrilateral not contained in a line. -/
theorem side_eq_zero_iff (u : Fin 4 → Fin 2 → k) (hu : Closed u) (hne : ∃ j, mu u j ≠ 0)
    (i : Fin 4) : u i = 0 ↔ mu u i = 0 ∧ mu u (i + 1) = 0 := by
  constructor
  · intro h
    simp only [mu, h, add_sub_cancel_right]
    constructor <;> simp [wedge]
  · rintro ⟨h0, h1⟩
    by_contra hi
    obtain ⟨j, hj⟩ := hne
    have hA : ∀ i : Fin 4, 1 + (i - 1) = i := by decide
    have hB : ∀ i : Fin 4, 2 + (i - 1) = i + 1 := by decide
    -- rotate so that `i` becomes `1`
    set r : Fin 4 := i - 1
    set v := rot r u
    have hv : Closed v := closed_rot r u hu
    have hv1 : v 1 ≠ 0 := by
      simp only [v, rot]; rw [show (1 : Fin 4) + r = i by simp only [r]; exact hA i]; exact hi
    have e1 : wedge (v 0) (v 1) = 0 := by
      rw [← mu_one, mu_rot, show (1 : Fin 4) + r = i by simp only [r]; exact hA i]; exact h0
    have e2 : wedge (v 1) (v 2) = 0 := by
      rw [← mu_two, mu_rot, show (2 : Fin 4) + r = i + 1 by simp only [r]; exact hB i]; exact h1
    -- Plücker: `(v₀ ∧ v₁) v₂ + (v₁ ∧ v₂) v₀ + (v₂ ∧ v₀) v₁ = 0`
    have e02 : wedge (v 0) (v 2) = 0 := by
      have hc := cramer (v 0) (v 1) (v 2)
      rw [e1, wedge_swap (v 1) (v 2), e2, neg_zero, zero_smul, zero_smul, zero_add, eq_comm,
        smul_eq_zero] at hc
      exact hc.resolve_right hv1
    obtain ⟨d1, d2, -, -⟩ := wedge_diag v hv
    have hall : ∀ l, mu v l = 0 := by
      have m1 : mu v 1 = 0 := e1
      have m2 : mu v 2 = 0 := e2
      have m0 : mu v 0 = 0 := by linear_combination -d1 + e02 + m1
      have m3 : mu v 3 = 0 := by linear_combination -d2 + e02 + m2
      intro l; fin_cases l <;> assumption
    apply hj
    have := hall (j - r)
    rw [mu_rot] at this
    simpa using this

/-- The four degenerate quadrilaterals: `p_i` is the ear-area point of the quadrilateral
whose side `u_i` is a point. -/
def framePt : Fin 4 → Fin 4 → k :=
  ![![0, 0, 1, 1], ![1, 0, 0, 1], ![1, 1, 0, 0], ![0, 1, 1, 0]]

theorem framePt_mem (i : Fin 4) :
    framePt (k := k) i 0 + framePt i 2 = framePt i 1 + framePt i 3 := by
  fin_cases i <;> simp [framePt]

/-- A closed quadrilateral with `u_i = 0` has ear areas `μ = μ_{i+2} • p_i`, and
`μ_{i+2} ≠ 0` when it is not contained in a line. -/
theorem mu_eq_smul_framePt (u : Fin 4 → Fin 2 → k) (hu : Closed u) (i : Fin 4)
    (h : u i = 0) : mu u = mu u (i + 2) • framePt i := by
  have hrel := mu_relation u hu
  have z : ∀ a, wedge a (0 : Fin 2 → k) = 0 ∧ wedge 0 a = 0 := fun a => by
    simp [wedge]
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [framePt, mu_zero, mu_one, mu_two, mu_three] at h ⊢ <;>
    simp only [h, z, mu_zero, mu_one, mu_two, mu_three] at hrel ⊢ <;>
    first | linear_combination hrel | linear_combination -hrel

theorem mu_degenerate_ne_zero (u : Fin 4 → Fin 2 → k) (hu : Closed u) (i : Fin 4)
    (h : u i = 0) (hne : ∃ j, mu u j ≠ 0) : mu u (i + 2) ≠ 0 := fun h0 => by
  obtain ⟨j, hj⟩ := hne
  exact hj (by rw [mu_eq_smul_framePt u hu i h, h0, zero_smul, Pi.zero_apply])

/-- The only linear relation among the four degenerate points is the alternating one. -/
theorem sum_smul_framePt_eq_zero_iff (c : Fin 4 → k) :
    ∑ i, c i • framePt i = (0 : Fin 4 → k) ↔
      ∃ t : k, c = t • (![1, -1, 1, -1] : Fin 4 → k) := by
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp [Fin.sum_univ_four, framePt] at h0 h1 h2 h3
    refine ⟨c 0, funext fun i => ?_⟩
    fin_cases i <;> simp
    · linear_combination h3
    · linear_combination h0 - h3
    · linear_combination h2
  · rintro ⟨t, rfl⟩
    funext j; fin_cases j <;> simp [Fin.sum_univ_four, framePt]

/-- Any three of the degenerate points are linearly independent: with the alternating
relation, the four points form a projective frame of the plane. -/
theorem framePt_three_indep (c : Fin 4 → k) (h : ∑ i, c i • framePt i = (0 : Fin 4 → k))
    (i : Fin 4)
    (hi : c i = 0) : c = 0 := by
  obtain ⟨t, rfl⟩ := (sum_smul_framePt_eq_zero_iff c).1 h
  have ht : t = 0 := by
    fin_cases i <;> simpa using hi
  rw [ht, zero_smul]

/-- The plane `μ₀ + μ₂ = μ₁ + μ₃` of `k⁴`. -/
def plane : Submodule k (Fin 4 → k) where
  carrier := {m | m 0 + m 2 = m 1 + m 3}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *; linear_combination ha + hb
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    linear_combination c * ha

/-- The ear areas of a closed quadrilateral lie in `plane`. -/
theorem mu_mem_plane (u : Fin 4 → Fin 2 → k) (hu : Closed u) : mu u ∈ plane :=
  mu_relation u hu

/-- `e_i ↦ (-1)ⁱ p_i`. -/
def frameMap : (Fin 4 → k) →ₗ[k] (Fin 4 → k) where
  toFun c := ![-c 1 + c 2, c 2 - c 3, c 0 - c 3, c 0 - c 1]
  map_add' a b := by funext j; fin_cases j <;> simp <;> ring
  map_smul' t a := by funext j; fin_cases j <;> simp <;> ring

theorem frameMap_single (i : Fin 4) :
    frameMap (Pi.single i 1) = ((-1 : k) ^ (i : ℕ)) • framePt (k := k) i := by
  funext j; fin_cases i <;> fin_cases j <;> norm_num [frameMap, framePt]

theorem frameMap_ker : LinearMap.ker (frameMap (k := k)) = k ∙ (fun _ => (1 : k)) := by
  ext c
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp [frameMap] at h0 h1 h2 h3
    refine ⟨c 0, funext fun i => ?_⟩
    fin_cases i <;> simp
    · linear_combination h3
    · linear_combination h3 - h0
    · linear_combination h2
  · rintro ⟨t, rfl⟩
    funext j; fin_cases j <;> simp [frameMap]

theorem frameMap_range : LinearMap.range (frameMap (k := k)) = plane := by
  ext m
  constructor
  · rintro ⟨c, rfl⟩
    show _ = _
    simp [frameMap]; ring
  · intro hm
    change m 0 + m 2 = m 1 + m 3 at hm
    refine ⟨![m 2, m 2 - m 3, m 2 - m 3 + m 0, m 2 - m 3 + m 0 - m 1], funext fun j => ?_⟩
    fin_cases j <;> simp [frameMap] <;> first | ring1 | linear_combination hm

/-- Page 6, the plane is canonically `P(k^A / k·(1,1,1,1))`: a linear isomorphism
`k⁴ / k·(1,1,1,1) ≃ plane` sending the class of the edge `i` to `(-1)ⁱ p_i`, whose line
is the point of the degenerate quadrilateral `u_i = 0`. -/
theorem frame_canonical :
    ∃ e : ((Fin 4 → k) ⧸ (k ∙ (fun _ => (1 : k)))) ≃ₗ[k] plane,
      ∀ i : Fin 4, (e (Submodule.Quotient.mk (Pi.single i 1))).1 =
        ((-1 : k) ^ (i : ℕ)) • framePt (k := k) i := by
  have hmem : ∀ c, frameMap (k := k) c ∈ plane := fun c => by
    rw [← frameMap_range]; exact LinearMap.mem_range_self _ c
  let f : (Fin 4 → k) →ₗ[k] plane := LinearMap.codRestrict plane frameMap hmem
  have hf : Function.Surjective f := fun ⟨m, hm⟩ =>
    ((frameMap_range (k := k)).ge hm).imp fun c hc => Subtype.ext hc
  have hker : LinearMap.ker f = k ∙ (fun _ => (1 : k)) := by
    rw [LinearMap.ker_codRestrict, frameMap_ker]
  refine ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf),
    fun i => ?_⟩
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact frameMap_single i

end QuadField

/-! ## The zero-multiplier criterion (pages 15, 18, 28) -/

section SymSquare

variable [Field k]

/-- The product `a·b` in the symmetric square `Sym² k²`, in the basis `X², XY, Y²`. -/
def symProd (a b : Fin 2 → k) : Fin 3 → k :=
  ![a 0 * b 0, a 0 * b 1 + a 1 * b 0, a 1 * b 1]

theorem symProd_apply0 (a b : Fin 2 → k) : symProd a b 0 = a 0 * b 0 := rfl
theorem symProd_apply1 (a b : Fin 2 → k) : symProd a b 1 = a 0 * b 1 + a 1 * b 0 := rfl
theorem symProd_apply2 (a b : Fin 2 → k) : symProd a b 2 = a 1 * b 1 := rfl

theorem symProd_comm (a b : Fin 2 → k) : symProd a b = symProd b a := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_add_right (a b c : Fin 2 → k) :
    symProd a (b + c) = symProd a b + symProd a c := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_sub_right (a b c : Fin 2 → k) :
    symProd a (b - c) = symProd a b - symProd a c := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_smul_right (a b : Fin 2 → k) (t : k) :
    symProd a (t • b) = t • symProd a b := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_smul_left (a b : Fin 2 → k) (t : k) :
    symProd (t • a) b = t • symProd a b := by
  rw [symProd_comm, symProd_smul_right, symProd_comm]

theorem symProd_zero_right (a : Fin 2 → k) : symProd a 0 = 0 := by
  funext j; fin_cases j <;> simp [symProd]

/-- `Sym² k²` has no zero divisors among products of vectors. -/
theorem symProd_eq_zero_iff (a b : Fin 2 → k) : symProd a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    have h0 : a 0 * b 0 = 0 := congrFun h 0
    have h1 : a 0 * b 1 + a 1 * b 0 = 0 := congrFun h 1
    have h2 : a 1 * b 1 = 0 := congrFun h 2
    by_cases ha0 : a 0 = 0
    · rw [ha0, zero_mul, zero_add] at h1
      by_cases ha1 : a 1 = 0
      · exact Or.inl (funext fun j => by fin_cases j <;> assumption)
      · right; funext j; fin_cases j
        · exact (mul_eq_zero.1 h1).resolve_left ha1
        · exact (mul_eq_zero.1 h2).resolve_left ha1
    · right
      have hb0 : b 0 = 0 := (mul_eq_zero.1 h0).resolve_left ha0
      rw [hb0, mul_zero, add_zero] at h1
      funext j; fin_cases j
      · exact hb0
      · exact (mul_eq_zero.1 h1).resolve_left ha0
  · rintro (rfl | rfl) <;> funext j <;> fin_cases j <;> simp [symProd]

/-- An element of `Sym² k²` as a quadratic form, evaluated at `x`. -/
def qeval (s : Fin 3 → k) (x : Fin 2 → k) : k :=
  s 0 * x 0 ^ 2 + s 1 * (x 0 * x 1) + s 2 * x 1 ^ 2

theorem qeval_smul (t : k) (s : Fin 3 → k) (x : Fin 2 → k) :
    qeval (t • s) x = t * qeval s x := by
  simp [qeval]; ring

/-- `a·b` evaluated at the vector `x = (c₁, -c₀)` orthogonal to `c` is `(a ∧ c)(b ∧ c)`. -/
theorem qeval_symProd_perp (a b c : Fin 2 → k) :
    qeval (symProd a b) ![c 1, -c 0] = wedge a c * wedge b c := by
  simp [qeval, symProd, wedge]; ring

theorem wedge_eq_zero_comm (a b : Fin 2 → k) : wedge a b = 0 ↔ wedge b a = 0 := by
  rw [wedge_swap, neg_eq_zero]

theorem exists_smul_of_wedge {a c : Fin 2 → k} (ha : a ≠ 0) (h : wedge a c = 0) :
    ∃ α : k, c = α • a := by
  unfold wedge at h
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := fun h1 => ha (funext fun j => by fin_cases j <;> assumption)
    rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
    refine ⟨c 1 / a 1, funext fun j => ?_⟩
    fin_cases j
    · simp [h0]; exact (mul_eq_zero.1 h).resolve_left h1
    · simp; field_simp
  · refine ⟨c 0 / a 0, funext fun j => ?_⟩
    fin_cases j
    · simp; field_simp
    · simp; field_simp; linear_combination h

/-- Page 28, the « pair of directions »: for nonzero vectors of a plane, `c·d` is a
multiple of `a·b` in `Sym² k²` if and only if `{[a], [b]} = {[c], [d]}` as pairs of lines. -/
theorem symProd_proportional_iff {a b c d : Fin 2 → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (∃ t : k, symProd c d = t • symProd a b) ↔
      (wedge a c = 0 ∧ wedge b d = 0) ∨ (wedge a d = 0 ∧ wedge b c = 0) := by
  constructor
  · rintro ⟨t, h⟩
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul, symProd_eq_zero_iff] at h
      exact h.elim hc hd
    have E : ∀ x, qeval (symProd c d) x = t * qeval (symProd a b) x := fun x => by
      rw [h, qeval_smul]
    have A := E ![a 1, -a 0]
    have C := E ![c 1, -c 0]
    have B := E ![b 1, -b 0]
    have D := E ![d 1, -d 0]
    simp only [qeval_symProd_perp, wedge_self, zero_mul, mul_zero, mul_eq_zero,
      zero_eq_mul] at A B C D
    rw [wedge_eq_zero_comm c a, wedge_eq_zero_comm d a] at A
    rw [wedge_eq_zero_comm c b, wedge_eq_zero_comm d b] at B
    rcases C with C | C | C
    · exact absurd C ht
    · -- `a ∧ c = 0`
      by_cases hbd : wedge b d = 0
      · exact Or.inl ⟨C, hbd⟩
      · rcases D with D | D | D
        · exact absurd D ht
        · rcases B with B | B
          · exact Or.inr ⟨D, B⟩
          · exact absurd B hbd
        · exact absurd D hbd
    · -- `b ∧ c = 0`
      rcases A with A | A
      · by_cases hbd : wedge b d = 0
        · exact Or.inl ⟨A, hbd⟩
        · rcases D with D | D | D
          · exact absurd D ht
          · exact Or.inr ⟨D, C⟩
          · exact absurd D hbd
      · exact Or.inr ⟨A, C⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · obtain ⟨α, rfl⟩ := exists_smul_of_wedge ha h1
      obtain ⟨β, rfl⟩ := exists_smul_of_wedge hb h2
      exact ⟨α * β, by rw [symProd_smul_left, symProd_smul_right, smul_smul, mul_comm]⟩
    · obtain ⟨α, rfl⟩ := exists_smul_of_wedge ha h1
      obtain ⟨β, rfl⟩ := exists_smul_of_wedge hb h2
      exact ⟨α * β, by rw [symProd_smul_left, symProd_smul_right, smul_smul, symProd_comm b a, mul_comm]⟩

end SymSquare

section Polygon

variable [Field k] {n : ℕ} [NeZero n]

/-- The multipliers of an `n`-gon given by its sides (page 25, the relation `(∗)`):
`λ_i u_{i-1} - λ_{i+1}(u_i + u_{i+1}) + λ_{i+2} u_{i+2} = 0` for all `i`. -/
def IsMult (u : ZMod n → Fin 2 → k) (l : ZMod n → k) : Prop :=
  ∀ i, l i • u (i - 1) - l (i + 1) • (u i + u (i + 1)) + l (i + 2) • u (i + 2) = 0

/-- `u_{0m} = u_0 + ⋯ + u_{m-1} = s_m - s_0`. -/
def partialSum (u : ZMod n → Fin 2 → k) (m : ℕ) : Fin 2 → k :=
  ∑ j ∈ Finset.range m, u j

/-- The Lagrange form `(L)`: `L_i = λ_i u_{i-1} - λ_{i+1} u_{i+1}`. -/
def lagr (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (i : ZMod n) : Fin 2 → k :=
  l i • u (i - 1) - l (i + 1) • u (i + 1)

omit [NeZero n] in
theorem isMult_iff_lagr (u : ZMod n → Fin 2 → k) (l : ZMod n → k) :
    IsMult u l ↔ ∀ i, lagr u l i = lagr u l (i + 1) := by
  have key : ∀ i, lagr u l i - lagr u l (i + 1) =
      l i • u (i - 1) - l (i + 1) • (u i + u (i + 1)) + l (i + 2) • u (i + 2) := fun i => by
    simp only [lagr, add_sub_cancel_right, add_assoc, one_add_one_eq_two, smul_add]
    abel
  simp only [IsMult, ← key, sub_eq_zero]

theorem sum_range_eq_sum (f : ZMod n → Fin 2 → k) :
    ∑ j ∈ Finset.range n, f j = ∑ i, f i :=
  Finset.sum_nbij' (fun j => (j : ZMod n)) (fun i => i.val) (fun _ _ => Finset.mem_univ _)
    (fun i _ => Finset.mem_range.2 (ZMod.val_lt i))
    (fun _ hj => ZMod.val_cast_of_lt (Finset.mem_range.1 hj)) (fun i _ => ZMod.natCast_zmod_val i)
    fun _ _ => rfl

/-- With `λ₀ = 0` and `λ₁ = 1`, `(∗)` says `L_i = -u₁` for every `i`. -/
theorem isMult_iff_lagr_eq (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h0 : l 0 = 0)
    (h1 : l 1 = 1) : IsMult u l ↔ ∀ i, lagr u l i = -u 1 := by
  have hL0 : lagr u l 0 = -u 1 := by simp [lagr, h0, h1]
  rw [isMult_iff_lagr]
  constructor
  · intro h i
    have : ∀ m : ℕ, lagr u l (m : ZMod n) = lagr u l 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.cast_succ, ← h, ih]
    rw [← ZMod.natCast_zmod_val i, this, hL0]
  · intro h i; rw [h, h]

/-- The identity `(S_{m+1})`: `λ_{m+1} u_m·u_{m+1} = u_1·u_{0,m+1}` in `Sym² V`. -/
def SymId (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (m : ℕ) : Prop :=
  l ((m + 1 : ℕ) : ZMod n) • symProd (u m) (u ((m + 1 : ℕ) : ZMod n)) =
    symProd (u 1) (partialSum u (m + 1))

omit [NeZero n] in
private theorem alg_fwd (A B : k) (x y z u1 P : Fin 2 → k) (hL : A • x - B • z = -u1)
    (hS : A • symProd x y = symProd u1 P) : B • symProd y z = symProd u1 (P + y) := by
  have hz : B • z = A • x + u1 := by
    rw [show B • z = A • x - (A • x - B • z) by abel, hL, sub_neg_eq_add]
  rw [← symProd_smul_right, hz, symProd_add_right, symProd_smul_right, symProd_comm y x, hS,
    symProd_comm y u1, symProd_add_right]

omit [NeZero n] in
private theorem alg_bwd (A B : k) (x y z u1 P : Fin 2 → k) (hy : y ≠ 0)
    (hS : A • symProd x y = symProd u1 P) (hS' : B • symProd y z = symProd u1 (P + y)) :
    A • x - B • z = -u1 := by
  have : symProd y (A • x - B • z + u1) = 0 := by
    rw [symProd_add_right, symProd_sub_right, symProd_smul_right, symProd_smul_right,
      symProd_comm y x, hS, hS', symProd_comm y u1, symProd_add_right]
    abel
  exact eq_neg_of_add_eq_zero_left (((symProd_eq_zero_iff _ _).1 this).resolve_left hy)

omit [NeZero n] in
private theorem lagr_succ (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (m : ℕ) :
    lagr u l ((m + 1 : ℕ) : ZMod n) =
      l ((m + 1 : ℕ) : ZMod n) • u m - l ((m + 2 : ℕ) : ZMod n) • u ((m + 2 : ℕ) : ZMod n) := by
  simp only [lagr]
  push_cast
  rw [add_sub_cancel_right, add_assoc, one_add_one_eq_two]

omit [NeZero n] in
private theorem partialSum_succ (u : ZMod n → Fin 2 → k) (m : ℕ) :
    partialSum u (m + 1) = partialSum u m + u m := Finset.sum_range_succ _ _

omit [NeZero n] in
theorem symId_zero (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h1 : l 1 = 1) :
    SymId u l 0 := by
  simp [SymId, partialSum, h1, symProd_comm]

omit [NeZero n] in
/-- `(L)` at `m + 1` carries `(S_{m+1})` to `(S_{m+2})` (page 28, the edition's proof). -/
theorem symId_succ (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (m : ℕ)
    (hL : lagr u l ((m + 1 : ℕ) : ZMod n) = -u 1) (hS : SymId u l m) : SymId u l (m + 1) := by
  rw [lagr_succ] at hL
  unfold SymId at *
  rw [partialSum_succ u (m + 1)]
  exact alg_fwd _ _ _ _ _ _ _ hL hS

/-- A multiplier with `λ₀ = 0`, `λ₁ = 1` satisfies `(S_i)` for every `i ≥ 1`. -/
theorem symId_of_isMult (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h0 : l 0 = 0)
    (h1 : l 1 = 1) (h : IsMult u l) (m : ℕ) : SymId u l m := by
  rw [isMult_iff_lagr_eq u l h0 h1] at h
  induction m with
  | zero => exact symId_zero u l h1
  | succ m ih => exact symId_succ u l m (h _) ih

/-- Conversely, `(S_i)` for every `i ≥ 1` gives `(∗)`, the sides being nonzero. -/
theorem isMult_of_symId (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0) (l : ZMod n → k)
    (h0 : l 0 = 0) (h1 : l 1 = 1) (hS : ∀ m, SymId u l m) : IsMult u l := by
  refine (isMult_iff_lagr_eq u l h0 h1).2 fun i => ?_
  have hn : 1 ≤ n := NeZero.one_le
  set m := i.val + (n - 1)
  have hi : ((m + 1 : ℕ) : ZMod n) = i := by
    rw [show m + 1 = i.val + n by omega]
    push_cast
    rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  rw [← hi, lagr_succ]
  have h2 := hS (m + 1)
  rw [SymId, partialSum_succ u (m + 1)] at h2
  exact alg_bwd _ _ _ _ _ _ _ (hu _) (hS m) h2

omit [NeZero n] in
private theorem cast_n_add (j : ℕ) : ((n + j : ℕ) : ZMod n) = j := by
  push_cast; rw [ZMod.natCast_self, zero_add]

omit [NeZero n] in
private theorem partialSum_n_add (u : ZMod n → Fin 2 → k) (j : ℕ) :
    partialSum u (n + j) = partialSum u n + partialSum u j := by
  simp only [partialSum, Finset.sum_range_add, cast_n_add]

omit [NeZero n] in
/-- For a closed polygon, `(S_i)` is periodic in `i`. -/
theorem symId_n_add (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (hcl : partialSum u n = 0)
    (m : ℕ) : SymId u l (n + m) ↔ SymId u l m := by
  unfold SymId
  rw [show n + m + 1 = n + (m + 1) by ring, cast_n_add, cast_n_add, partialSum_n_add, hcl,
    zero_add]

/-- **Page 28, the criterion of the special case II.** An `n`-gon with nonzero sides has a
multiplier with `λ₀ = 0` and `λ₁ = 1` if and only if it is closed and, for
`2 ≤ i ≤ n - 1`, either `s_i = s_0` or the pair of directions of `{u_{i-1}, u_i}` is that
of `{u_1, u_{0i}}`. -/
theorem zero_multiplier_criterion (hn : 3 ≤ n) (u : ZMod n → Fin 2 → k)
    (hu : ∀ i, u i ≠ 0) :
    (∃ l : ZMod n → k, l 0 = 0 ∧ l 1 = 1 ∧ IsMult u l) ↔
      (∑ i, u i = 0 ∧ ∀ i : ℕ, 2 ≤ i → i ≤ n - 1 →
        partialSum u i = 0 ∨
          ((wedge (u (i - 1 : ℕ)) (u 1) = 0 ∧ wedge (u i) (partialSum u i) = 0) ∨
            (wedge (u (i - 1 : ℕ)) (partialSum u i) = 0 ∧ wedge (u i) (u 1) = 0))) := by
  rw [← sum_range_eq_sum]
  constructor
  · rintro ⟨l, h0, h1, h⟩
    have hS := symId_of_isMult u l h0 h1 h
    refine ⟨?_, fun i hi2 hin => ?_⟩
    · have := hS (n - 1)
      rw [SymId, show n - 1 + 1 = n by omega, ZMod.natCast_self, h0, zero_smul, eq_comm,
        symProd_eq_zero_iff] at this
      exact this.resolve_left (hu 1)
    · by_cases hP : partialSum u i = 0
      · exact Or.inl hP
      · right
        have := hS (i - 1)
        rw [SymId, show i - 1 + 1 = i by omega] at this
        exact (symProd_proportional_iff (hu _) (hu _) (hu 1) hP).1 ⟨_, this.symm⟩
  · rintro ⟨hcl, hcond⟩
    have hex : ∀ i : ℕ, ∃ t : k, 2 ≤ i → i ≤ n - 1 →
        symProd (u 1) (partialSum u i) = t • symProd (u (i - 1 : ℕ)) (u i) := by
      intro i
      by_cases hi : 2 ≤ i ∧ i ≤ n - 1
      · rcases hcond i hi.1 hi.2 with hP | hpair
        · exact ⟨0, fun _ _ => by rw [hP, symProd_zero_right, zero_smul]⟩
        · by_cases hP : partialSum u i = 0
          · exact ⟨0, fun _ _ => by rw [hP, symProd_zero_right, zero_smul]⟩
          · obtain ⟨t, ht⟩ := (symProd_proportional_iff (hu _) (hu _) (hu 1) hP).2 hpair
            exact ⟨t, fun _ _ => ht⟩
      · exact ⟨0, fun h2 h3 => absurd ⟨h2, h3⟩ hi⟩
    choose f hf using hex
    let l : ZMod n → k := fun j => if j.val = 0 then 0 else if j.val = 1 then 1 else f j.val
    have hval1 : (1 : ZMod n).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    have h0 : l 0 = 0 := by simp [l]
    have h1 : l 1 = 1 := by simp only [l, hval1]; norm_num
    have hcl' : partialSum u n = 0 := hcl
    refine ⟨l, h0, h1, isMult_of_symId u hu l h0 h1 ?_⟩
    have hlt : ∀ m, m < n → SymId u l m := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact symId_zero u l h1
      · by_cases hmn : m + 1 = n
        · unfold SymId
          rw [hmn, ZMod.natCast_self, h0, zero_smul, hcl', symProd_zero_right]
        · have hv : ((m + 1 : ℕ) : ZMod n).val = m + 1 := ZMod.val_cast_of_lt (by omega)
          have hl : l ((m + 1 : ℕ) : ZMod n) = f (m + 1) := by
            simp only [l, hv]
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          have e := hf (m + 1) (by omega) (by omega)
          rw [Nat.add_sub_cancel] at e
          unfold SymId
          rw [hl, ← e]
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < n
      · exact hlt m hm
      · obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
        exact (symId_n_add u l hcl' j).2 (ih j (by omega))

/-- The multiplier is given by `λ_i u_{i-1}·u_i = u_1·u_{0i}` in `Sym² V`, for every
`i ≥ 1` (the page's « on aura λ_i défini par u_1 u_{0i} = λ_i u_i u_{i-1} »). -/
theorem symProd_formula (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h0 : l 0 = 0)
    (h1 : l 1 = 1) (h : IsMult u l) (i : ℕ) (hi : 1 ≤ i) :
    l i • symProd (u (i - 1 : ℕ)) (u i) = symProd (u 1) (partialSum u i) := by
  have := symId_of_isMult u l h0 h1 h (i - 1)
  rwa [SymId, show i - 1 + 1 = i by omega] at this

/-- Page 28: `λ_i = 0` exactly at the vertices `s_i = s_0` (`u_{0i} = 0`). -/
theorem mult_eq_zero_iff (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0) (l : ZMod n → k)
    (h0 : l 0 = 0) (h1 : l 1 = 1) (h : IsMult u l) (i : ℕ) (hi : 1 ≤ i) :
    l i = 0 ↔ partialSum u i = 0 := by
  have hf := symProd_formula u l h0 h1 h i hi
  constructor
  · intro hl
    rw [hl, zero_smul, eq_comm, symProd_eq_zero_iff] at hf
    exact hf.resolve_left (hu 1)
  · intro hP
    rw [hP, symProd_zero_right, smul_eq_zero, symProd_eq_zero_iff] at hf
    exact hf.resolve_right (not_or.2 ⟨hu _, hu _⟩)

/-- The multiplier with `λ₀ = 0`, `λ₁ = 1` is unique. -/
theorem mult_unique (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0) (l l' : ZMod n → k)
    (h0 : l 0 = 0) (h1 : l 1 = 1) (h : IsMult u l) (h0' : l' 0 = 0) (h1' : l' 1 = 1)
    (h' : IsMult u l') : l = l' := by
  funext j
  have hn : 1 ≤ n := NeZero.one_le
  have hj : ((j.val + n : ℕ) : ZMod n) = j := by
    push_cast; rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  have e := symProd_formula u l h0 h1 h (j.val + n) (by omega)
  have e' := symProd_formula u l' h0' h1' h' (j.val + n) (by omega)
  rw [← e'] at e
  have hne : symProd (u ((j.val + n - 1 : ℕ) : ZMod n)) (u ((j.val + n : ℕ) : ZMod n)) ≠ 0 :=
    fun h0 => ((symProd_eq_zero_iff _ _).1 h0).elim (hu _) (hu _)
  have := smul_left_injective k hne e
  rwa [hj] at this

/-- Two consecutive zero components force a multiplier to vanish: hence the normalisation
`λ₁ = 1` once `λ₀ = 0`. -/
theorem eq_zero_of_consecutive (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)
    (l : ZMod n → k) (h : IsMult u l) (i : ZMod n) (h0 : l i = 0) (h1 : l (i + 1) = 0) :
    l = 0 := by
  have step : ∀ m : ℕ, l (i + m) = 0 ∧ l (i + m + 1) = 0 := by
    intro m
    induction m with
    | zero => simpa using ⟨h0, h1⟩
    | succ m ih =>
      have e := h (i + m)
      rw [ih.1, ih.2, zero_smul, zero_smul, sub_zero, zero_add, smul_eq_zero] at e
      have e2 : l (i + m + 2) = 0 := e.resolve_right (hu _)
      push_cast
      refine ⟨by rw [← add_assoc]; exact ih.2, ?_⟩
      rw [← add_assoc, add_assoc (i + m), one_add_one_eq_two]; exact e2
  funext j
  have := (step (j - i).val).1
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

end Polygon

/-! ## Pages 23–28: the multiplier space, its dimension, and the four cases

`multSpace u` is the space `N(u_*)` of the multipliers `λ` of page 25 (`IsMult`).

* `evPair_injective`, `finrank_multSpace_le_two`: for nonzero sides, `λ ↦ (λ_i, λ_{i+1})` is
  injective on `N(u_*)`, so `dim N(u_*) ≤ 2` (page 23).
* `collinear_of_finrank_two`: if `dim N(u_*) = 2`, then `u_i`, `u_{i+1} + u_{i+2}`, `u_{i+3}`
  are collinear for every `i` (pages 23, 26, (a) ⇒ (b)).
* `triangle_of_collinear`: if moreover the `u_i` are not all on one line, `u_{i+3} = u_i` and
  `u_{i+1} + u_{i+2} = -u_i` for every `i`, and `3 ∣ n` (pages 24, 26–27, (b) ⇒ (c) ⇒ (d)).
* `finrank_multSpace_eq_two_iff`: for nonzero sides not all on one line, `dim N(u_*) = 2` iff
  `3 ∣ n`, `u_{i+3} = u_i` and `u₀ + u₁ + u₂ = 0` — a triangle traversed `n/3` times; then
  `N(u_*)` is the plane of the `3`-periodic `λ` with `λ₀ + λ₁ + λ₂ = 0`
  (`isMult_periodic`), and it has an element with no zero component as soon as some
  `ω ≠ 0, -1` exists in `k`, i.e. `|k| ≥ 3` (`exists_mult_ne_zero`).
* `dichotomy`, `finrank_le_one_of_le_hyperplane`, `not_le_hyperplane_of_finrank_two`
  (page 28): if `|k| > n`, either some multiplier has no zero component, or `N(u_*)` lies in
  a coordinate hyperplane `H_i`, and then `dim N(u_*) ≤ 1`; a plane `N(u_*)` lies in no `H_i`.
  The page assumes `k` infinite (`dichotomy_of_infinite`).
-/

section EarArea

variable [Field k] {n : ℕ} [NeZero n]

/-- The space `N(u_*)` of multipliers. -/
def multSpace (u : ZMod n → Fin 2 → k) : Submodule k (ZMod n → k) where
  carrier := {l | IsMult u l}
  add_mem' {a b} ha hb i := by
    have h := congrArg₂ (· + ·) (ha i) (hb i)
    simp only [add_zero] at h
    rw [← h]
    simp only [Pi.add_apply, add_smul]
    abel
  zero_mem' i := by simp
  smul_mem' c a ha i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← smul_sub, ← smul_add, ha i, smul_zero]

omit [NeZero n] in
theorem mem_multSpace (u : ZMod n → Fin 2 → k) (l : ZMod n → k) :
    l ∈ multSpace u ↔ IsMult u l := Iff.rfl

/-- `λ ↦ (λ_i, λ_{i+1})` on `N(u_*)`. -/
def evPair (u : ZMod n → Fin 2 → k) (i : ZMod n) : multSpace u →ₗ[k] (Fin 2 → k) :=
  (LinearMap.pi ![LinearMap.proj i, LinearMap.proj (i + 1)]).comp (multSpace u).subtype

omit [NeZero n] in
theorem evPair_zero (u : ZMod n → Fin 2 → k) (i : ZMod n) (l : multSpace u) :
    evPair u i l 0 = l.1 i := rfl

omit [NeZero n] in
theorem evPair_one (u : ZMod n → Fin 2 → k) (i : ZMod n) (l : multSpace u) :
    evPair u i l 1 = l.1 (i + 1) := rfl

variable (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)
include hu

theorem evPair_injective (i : ZMod n) : Function.Injective (evPair u i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  have h0 : l.1 i = 0 := by rw [← evPair_zero, hl]; rfl
  have h1 : l.1 (i + 1) = 0 := by rw [← evPair_one, hl]; rfl
  exact Subtype.ext (eq_zero_of_consecutive u hu l.1 l.2 i h0 h1)

/-- **Page 23.** `dim N(u_*) ≤ 2`. -/
theorem finrank_multSpace_le_two : Module.finrank k (multSpace u) ≤ 2 := by
  simpa using LinearMap.finrank_le_finrank_of_injective (evPair_injective u hu 0)

theorem evPair_surjective (h2 : Module.finrank k (multSpace u) = 2) (i : ZMod n) :
    Function.Surjective (evPair u i) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [h2])).1
    (evPair_injective u hu i)

/-- **Pages 23 and 26, (a) ⇒ (b).** -/
theorem collinear_of_finrank_two (h2 : Module.finrank k (multSpace u) = 2) (i : ZMod n) :
    wedge (u i) (u (i + 3)) = 0 ∧ wedge (u i) (u (i + 1) + u (i + 2)) = 0 := by
  obtain ⟨l, hl⟩ := evPair_surjective u hu h2 (i + 1) ![1, 0]
  obtain ⟨l', hl'⟩ := evPair_surjective u hu h2 (i + 1) ![0, 1]
  have a0 : l.1 (i + 1) = 1 := by rw [← evPair_zero u (i + 1) l, hl]; rfl
  have a1 : l.1 (i + 1 + 1) = 0 := by rw [← evPair_one u (i + 1) l, hl]; rfl
  have b0 : l'.1 (i + 1) = 0 := by rw [← evPair_zero u (i + 1) l', hl']; rfl
  have b1 : l'.1 (i + 1 + 1) = 1 := by rw [← evPair_one u (i + 1) l', hl']; rfl
  have r1 : i + 1 - 1 = i := by ring
  have r2 : i + 1 + 1 = i + 2 := by ring
  have r3 : i + 1 + 2 = i + 3 := by ring
  have f := (l.2 : IsMult u l.1) (i + 1)
  have f' := (l'.2 : IsMult u l'.1) (i + 1)
  rw [a0, a1, r1, r2, r3] at f
  rw [b0, b1, r1, r2, r3] at f'
  have f0 := congrFun f 0
  have f1 := congrFun f 1
  have g0 := congrFun f' 0
  have g1 := congrFun f' 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at f0 f1 g0 g1
  have w1 : wedge (u i) (u (i + 3)) = 0 := by
    unfold wedge; linear_combination u (i + 3) 1 * f0 - u (i + 3) 0 * f1
  refine ⟨w1, ?_⟩
  unfold wedge at w1 ⊢
  simp only [Pi.add_apply]
  linear_combination (-u i 0) * g1 + u i 1 * g0 + l'.1 (i + 3) * w1

omit hu in
/-- Two vectors with nonzero wedge are linearly independent, in coordinates. -/
theorem indep {a b : Fin 2 → k} (hw : wedge a b ≠ 0) {p q : k} (h0 : p * a 0 + q * b 0 = 0)
    (h1 : p * a 1 + q * b 1 = 0) : p = 0 ∧ q = 0 := by
  unfold wedge at hw
  constructor
  · have : p * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination b 1 * h0 - b 0 * h1
    exact (mul_eq_zero.1 this).resolve_right hw
  · have : q * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination a 0 * h1 - a 1 * h0
    exact (mul_eq_zero.1 this).resolve_right hw

omit hu in
theorem smul_coords {a c : Fin 2 → k} {α : k} (h : c = α • a) (j : Fin 2) : c j = α * a j :=
  congrFun h j

omit hu in
theorem add_coords {a b c : Fin 2 → k} {α : k} (h : a + b = α • c) (j : Fin 2) :
    a j + b j = α * c j :=
  congrFun h j

omit [NeZero n] in
/-- One step of page 24: from an independent pair `u_i, u_{i+1}`. -/
theorem step (hb : ∀ i, wedge (u i) (u (i + 3)) = 0 ∧ wedge (u i) (u (i + 1) + u (i + 2)) = 0)
    (i : ZMod n) (hw : wedge (u i) (u (i + 1)) ≠ 0) :
    wedge (u (i + 1)) (u (i + 2)) ≠ 0 ∧ u (i + 4) = u (i + 1) ∧
      u (i + 2) + u (i + 3) = -u (i + 1) := by
  obtain ⟨β, hβ⟩ := exists_smul_of_wedge (hu i) (hb i).1
  obtain ⟨α, hα⟩ := exists_smul_of_wedge (hu i) (hb i).2
  have h1 := hb (i + 1)
  rw [show i + 1 + 3 = i + 4 by ring, show i + 1 + 1 = i + 2 by ring,
    show i + 1 + 2 = i + 3 by ring] at h1
  obtain ⟨β', hβ'v⟩ := exists_smul_of_wedge (hu (i + 1)) h1.1
  obtain ⟨α', hα'v⟩ := exists_smul_of_wedge (hu (i + 1)) h1.2
  have h2 := (hb (i + 2)).2
  rw [show i + 2 + 1 = i + 3 by ring, show i + 2 + 2 = i + 4 by ring] at h2
  obtain ⟨α'', hα''v⟩ := exists_smul_of_wedge (hu (i + 2)) h2
  have A := smul_coords hβ
  have B := add_coords hα
  have C := smul_coords hβ'v
  have D := add_coords hα'v
  have G := add_coords hα''v
  obtain ⟨p1, q1⟩ := indep hw (p := α + β) (q := -1 - α')
    (by linear_combination D 0 - B 0 - A 0) (by linear_combination D 1 - B 1 - A 1)
  obtain ⟨p2, q2⟩ := indep hw (p := β - α'' * α) (q := β' + α'')
    (by linear_combination G 0 - A 0 - C 0 + α'' * B 0)
    (by linear_combination G 1 - A 1 - C 1 + α'' * B 1)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hu (i + 3) (by rw [hβ, zero_smul])
  have eα'' : α'' = -1 := by
    have : β * (1 + α'') = 0 := by linear_combination p2 + α'' * p1
    linear_combination (mul_eq_zero.1 this).resolve_left hβ0
  have eβ' : β' = 1 := by linear_combination q2 - eα''
  have eα' : α' = -1 := by linear_combination -q1
  refine ⟨?_, by rw [hβ'v, eβ', one_smul], by rw [hα'v, eα', neg_one_smul]⟩
  have : wedge (u (i + 1)) (u (i + 2)) = β * wedge (u i) (u (i + 1)) := by
    unfold wedge
    linear_combination u (i + 1) 0 * B 1 - u (i + 1) 1 * B 0 +
      (u i 1 * u (i + 1) 0 - u i 0 * u (i + 1) 1) * p1
  exact this ▸ mul_ne_zero hβ0 hw

omit hu in
theorem wedge_eq_zero_of_common {a b c : Fin 2 → k} (ha : a ≠ 0) (hb : wedge a b = 0)
    (hc : wedge a c = 0) : wedge b c = 0 := by
  obtain ⟨s, rfl⟩ := exists_smul_of_wedge ha hb
  obtain ⟨t, rfl⟩ := exists_smul_of_wedge ha hc
  unfold wedge
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Not all on one line: some consecutive pair is independent. -/
theorem exists_consecutive (hl : ∃ i j, wedge (u i) (u j) ≠ 0) :
    ∃ i, wedge (u i) (u (i + 1)) ≠ 0 := by
  by_contra h
  push Not at h
  have hm : ∀ m : ℕ, wedge (u 0) (u m) = 0 := by
    intro m
    induction m with
    | zero => simpa using wedge_self (u 0)
    | succ m ih =>
      push_cast
      exact wedge_eq_zero_of_common (hu _) ((wedge_eq_zero_comm _ _).1 ih) (h m)
  have hall : ∀ j, wedge (u 0) (u j) = 0 := fun j => by
    simpa [ZMod.natCast_zmod_val] using hm j.val
  obtain ⟨i, j, hij⟩ := hl
  exact hij (wedge_eq_zero_of_common (hu 0) (hall i) (hall j))

/-- **Pages 24, 26 and 27, (b) ⇒ (c) ⇒ (d).** -/
theorem triangle_of_collinear (hl : ∃ i j, wedge (u i) (u j) ≠ 0)
    (hb : ∀ i, wedge (u i) (u (i + 3)) = 0 ∧ wedge (u i) (u (i + 1) + u (i + 2)) = 0) :
    (∀ i, u (i + 3) = u i ∧ u (i + 1) + u (i + 2) = -u i) ∧ 3 ∣ n := by
  obtain ⟨i₀, h₀⟩ := exists_consecutive u hu hl
  have hind : ∀ m : ℕ, wedge (u (i₀ + m)) (u (i₀ + m + 1)) ≠ 0 := by
    intro m
    induction m with
    | zero => simpa using h₀
    | succ m ih =>
      have := (step u hu hb _ ih).1
      push_cast
      convert this using 3 <;> ring
  have hc : ∀ j, u (j + 3) = u j ∧ u (j + 1) + u (j + 2) = -u j := by
    intro j
    have hw := hind (j - 1 - i₀).val
    rw [ZMod.natCast_zmod_val, add_sub_cancel] at hw
    obtain ⟨-, h4, h23⟩ := step u hu hb (j - 1) hw
    rw [show j - 1 + 4 = j + 3 by ring, sub_add_cancel] at h4
    rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 3 = j + 2 by ring, sub_add_cancel] at h23
    exact ⟨h4, h23⟩
  refine ⟨hc, ?_⟩
  by_contra h3
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  set v := (ZMod.unitOfCoprime 3 hcop)⁻¹
  have hv : (3 : ZMod n) * ((v : ZMod n).val : ZMod n) = 1 := by
    rw [ZMod.natCast_zmod_val]
    have := Units.mul_inv (ZMod.unitOfCoprime 3 hcop)
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  have hper : ∀ (m : ℕ) j, u (j + 3 * m) = u j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro j
      rw [show j + 3 * ((m + 1 : ℕ) : ZMod n) = (j + 3 * m) + 3 by push_cast; ring, (hc _).1, ih]
  have h1 : ∀ j, u (j + 1) = u j := fun j => by rw [← hv, hper]
  have hall : ∀ m : ℕ, u m = u 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => push_cast; rw [h1, ih]
  obtain ⟨i, j, hij⟩ := hl
  apply hij
  rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, hall, hall, wedge_self]

omit hu in
/-- `3`-periodic sequences, as functions of `ZMod 3`. -/
def per (h3 : 3 ∣ n) (f : ZMod 3 → k) : ZMod n → k := fun i => f (ZMod.castHom h3 (ZMod 3) i)

omit hu in
theorem sum_three (f : ZMod 3 → k) (hf : f 0 + f 1 + f 2 = 0) (t : ZMod 3) :
    f t + f (t + 1) + f (t + 2) = 0 := by
  have : t = 0 ∨ t = 1 ∨ t = 2 := by revert t; decide
  rcases this with rfl | rfl | rfl
  · simpa using hf
  · rw [show (1 : ZMod 3) + 1 = 2 by decide, show (1 : ZMod 3) + 2 = 0 by decide]
    linear_combination hf
  · rw [show (2 : ZMod 3) + 1 = 0 by decide, show (2 : ZMod 3) + 2 = 1 by decide]
    linear_combination hf

omit hu in
/-- **Page 27, (d) ⇒ (a).** For a triangle traversed `n/3` times, every `3`-periodic `λ` with
`λ₀ + λ₁ + λ₂ = 0` is a multiplier. -/
theorem isMult_periodic (h3 : 3 ∣ n) (hper : ∀ i, u (i + 3) = u i) (hs : u 0 + u 1 + u 2 = 0)
    (f : ZMod 3 → k) (hf : f 0 + f 1 + f 2 = 0) : IsMult u (per h3 f) := by
  have hS : ∀ m : ℕ, u m + u (m + 1) + u (m + 2) = 0 := by
    intro m
    induction m with
    | zero => simpa [add_assoc] using hs
    | succ m ih =>
      push_cast
      rw [show (m : ZMod n) + 1 + 2 = m + 3 by ring, hper,
        show (m : ZMod n) + 1 + 1 = m + 2 by ring]
      rw [← ih]; abel
  intro i
  have h1 := hS (i - 1).val
  rw [ZMod.natCast_zmod_val, sub_add_cancel, show i - 1 + 2 = i + 1 by ring] at h1
  have h2 : u (i + 2) = u (i - 1) := by rw [show i + 2 = i - 1 + 3 by ring, hper]
  have hpair : u i + u (i + 1) = -u (i - 1) := by
    rw [eq_neg_iff_add_eq_zero, ← h1]; abel
  have hsum := sum_three f hf (ZMod.castHom h3 (ZMod 3) i)
  simp only [per, map_add, map_one, map_ofNat]
  rw [h2, hpair, smul_neg, sub_neg_eq_add, ← add_smul, ← add_smul, hsum, zero_smul]

/-- **Page 25, the Proposition, (a) ⇔ (d).** For nonzero sides not all on one line,
`dim N(u_*) = 2` if and only if the polygon is a triangle traversed `n/3` times. -/
theorem finrank_multSpace_eq_two_iff (hl : ∃ i j, wedge (u i) (u j) ≠ 0) :
    Module.finrank k (multSpace u) = 2 ↔
      3 ∣ n ∧ (∀ i, u (i + 3) = u i) ∧ u 0 + u 1 + u 2 = 0 := by
  constructor
  · intro h2
    obtain ⟨hc, h3⟩ := triangle_of_collinear u hu hl (collinear_of_finrank_two u hu h2)
    refine ⟨h3, fun i => (hc i).1, ?_⟩
    have := (hc 0).2
    rw [zero_add, zero_add] at this
    rw [add_assoc, this, add_neg_cancel]
  · rintro ⟨h3, hper, hs⟩
    have hsurj : Function.Surjective (evPair u 0) := by
      intro v
      refine ⟨⟨per h3 ![v 0, v 1, -v 0 - v 1], isMult_periodic u h3 hper hs _ (by simp)⟩, ?_⟩
      funext j
      fin_cases j
      · change (![v 0, v 1, -v 0 - v 1] : ZMod 3 → k) (ZMod.castHom h3 (ZMod 3) 0) = v 0
        rw [map_zero]; rfl
      · change (![v 0, v 1, -v 0 - v 1] : ZMod 3 → k) (ZMod.castHom h3 (ZMod 3) (0 + 1)) = v 1
        rw [zero_add, map_one]; rfl
    rw [(LinearEquiv.ofBijective (evPair u 0) ⟨evPair_injective u hu 0, hsurj⟩).finrank_eq]
    simp

omit hu in
/-- **Page 27, (d) ⇒ (a)**: a multiplier with no zero component, if some `ω ≠ 0, -1` is in `k`
(that is, `|k| ≥ 3`). -/
theorem exists_mult_ne_zero (h3 : 3 ∣ n) (hper : ∀ i, u (i + 3) = u i)
    (hs : u 0 + u 1 + u 2 = 0) {ω : k} (hω0 : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ l, IsMult u l ∧ ∀ i, l i ≠ 0 := by
  refine ⟨per h3 ![1, ω, -1 - ω], isMult_periodic u h3 hper hs _ (by simp), fun i => ?_⟩
  have : ∀ t : ZMod 3, (![1, ω, -1 - ω] : ZMod 3 → k) t ≠ 0 := by
    intro t
    have : t = 0 ∨ t = 1 ∨ t = 2 := by revert t; decide
    rcases this with rfl | rfl | rfl
    · simp
    · simpa using hω0
    · simp only [Matrix.cons_val]
      exact fun h => hω1 (by linear_combination -h)
  exact this _

/-- A plane `N(u_*)` lies in no coordinate hyperplane. -/
theorem not_le_hyperplane_of_finrank_two (h2 : Module.finrank k (multSpace u) = 2)
    (i : ZMod n) : ∃ l ∈ multSpace u, l i ≠ 0 := by
  obtain ⟨l, hl⟩ := evPair_surjective u hu h2 i ![1, 0]
  refine ⟨l.1, l.2, ?_⟩
  rw [← evPair_zero, hl]
  simp

/-- **Page 28, case II.** If `N(u_*)` lies in a coordinate hyperplane, `dim N(u_*) ≤ 1`. -/
theorem finrank_le_one_of_le_hyperplane (i : ZMod n) (h : ∀ l ∈ multSpace u, l i = 0) :
    Module.finrank k (multSpace u) ≤ 1 := by
  let e : multSpace u →ₗ[k] k := (LinearMap.proj (i + 1)).comp (multSpace u).subtype
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro l hl
    exact Subtype.ext (eq_zero_of_consecutive u hu l.1 l.2 i (h l.1 l.2) hl)
  simpa using LinearMap.finrank_le_finrank_of_injective he

omit hu in
/-- **Page 28, the dichotomy**, for `|k| > n`: either some multiplier has no zero
component, or `N(u_*)` lies in a coordinate hyperplane. -/
theorem dichotomy (hk : (n : ℕ∞) < ENat.card k) :
    (∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∨ ∃ i, ∀ l ∈ multSpace u, l i = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  let p : ZMod n → Submodule k (multSpace u) := fun i =>
    LinearMap.ker ((LinearMap.proj i).comp (multSpace u).subtype)
  have hp : ∀ i, p i ≠ ⊤ := fun i htop => by
    obtain ⟨l, hl, hli⟩ := h2 i
    exact hli (htop ▸ Submodule.mem_top : (⟨l, hl⟩ : multSpace u) ∈ p i)
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p hp
    (by rw [Finset.card_univ, ZMod.card]; exact hk)
  obtain ⟨x, -, hx⟩ := Set.exists_of_ssubset hss
  obtain ⟨i, hi⟩ := h1 x.1 x.2
  exact hx (Set.mem_iUnion₂.2 ⟨i, Finset.mem_univ _, hi⟩)

omit hu in
/-- The page's form: over an infinite field. -/
theorem dichotomy_of_infinite [Infinite k] :
    (∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∨ ∃ i, ∀ l ∈ multSpace u, l i = 0 :=
  dichotomy u (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top n)

end EarArea


/-! ## Page 14: `N(u_*)` is the space of Lagrange multipliers of the ear-area map

* `earArea_add`: `φ(u + v) = φ(u) + dφ_u(v) + φ(v)` for the ear-area map
  `φ(u)_i = u_{i-1} ∧ u_i`, so `dEar u` is its differential (`hasStrictFDerivAt_earArea`
  over `ℝ`).
* `isMult_iff_lagrange`, `isMult_iff_closed`: `λ ∈ N(u_*)` iff
  `Σ λ_i dφ_i = w ∧ Σ dv_i` for some `w` — the page's `Σ λ_i df_i = μ Σ dx_i + ν Σ dy_i` —
  iff `Σ λ_i dφ_i` vanishes on the closed deformations `Σ dv_i = 0`.
* `multSpace_eq_bot_iff`: `N(u_*) = 0` iff `dφ_u` maps the closed deformations onto
  `k^{ℤ/n}`: the case (a) of page 28 is the case where `φ`, restricted to the polygons with
  `Σ u_i` fixed, is a submersion at `u_*`.
-/

section Lagrange

variable [Field k] {n : ℕ}

/-- The ear-area map: `φ(u)_i = u_{i-1} ∧ u_i`. -/
def earArea (u : ZMod n → Fin 2 → k) (i : ZMod n) : k := wedge (u (i - 1)) (u i)

/-- Its differential at `u`: `dφ_u(v)_i = v_{i-1} ∧ u_i + u_{i-1} ∧ v_i`. -/
def dEar (u : ZMod n → Fin 2 → k) : (ZMod n → Fin 2 → k) →ₗ[k] (ZMod n → k) where
  toFun v i := wedge (v (i - 1)) (u i) + wedge (u (i - 1)) (v i)
  map_add' a b := by funext i; simp [wedge]; ring
  map_smul' c a := by funext i; simp [wedge]; ring

/-- `φ` is quadratic, with differential `dEar`. -/
theorem earArea_add (u v : ZMod n → Fin 2 → k) :
    earArea (u + v) = earArea u + dEar u v + earArea v := by
  funext i; simp [earArea, dEar, wedge]; ring

variable [NeZero n]

theorem wedge_sum (w : Fin 2 → k) (v : ZMod n → Fin 2 → k) :
    wedge w (∑ i, v i) = ∑ i, wedge w (v i) := by
  simp [wedge, Finset.mul_sum, Finset.sum_sub_distrib]

/-- Summation by parts: `Σ λ_i dφ_i(v) = Σ L_i ∧ v_i`. -/
theorem sum_mul_dEar (u v : ZMod n → Fin 2 → k) (l : ZMod n → k) :
    ∑ i, l i * dEar u v i = ∑ i, wedge (lagr u l i) (v i) := by
  have e := Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
    fun i => l i * wedge (v (i - 1)) (u i)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at e
  calc ∑ i, l i * dEar u v i
      = ∑ i, l i * wedge (v (i - 1)) (u i) + ∑ i, l i * wedge (u (i - 1)) (v i) := by
        simp [dEar, mul_add, Finset.sum_add_distrib]
    _ = ∑ i, wedge (lagr u l i) (v i) := by
        rw [← e, ← Finset.sum_add_distrib]; congr 1; funext i; simp [lagr, wedge]; ring

theorem lagr_const (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h : IsMult u l) (i : ZMod n) :
    lagr u l i = lagr u l 0 := by
  rw [isMult_iff_lagr] at h
  have : ∀ m : ℕ, lagr u l (m : ZMod n) = lagr u l 0 := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ, ← h, ih]
  rw [← ZMod.natCast_zmod_val i, this]

theorem sum_wedge_single (L : ZMod n → Fin 2 → k) (i : ZMod n) (e : Fin 2 → k) :
    ∑ j, wedge (L j) ((Pi.single i e : ZMod n → Fin 2 → k) j) = wedge (L i) e := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, wedge]) (by simp)]; simp

/-- **Page 14.** `λ ∈ N(u_*)` iff `Σ λ_i dφ_i` vanishes on the closed deformations. -/
theorem isMult_iff_closed (u : ZMod n → Fin 2 → k) (l : ZMod n → k) :
    IsMult u l ↔ ∀ v, ∑ i, v i = 0 → ∑ i, l i * dEar u v i = 0 := by
  refine ⟨fun h v hv => ?_, fun hw => ?_⟩
  · rw [sum_mul_dEar]; simp only [lagr_const u l h, ← wedge_sum, hv]; simp [wedge]
  rw [isMult_iff_lagr]
  intro i
  have key : ∀ e : Fin 2 → k, wedge (lagr u l i) e = wedge (lagr u l (i + 1)) e := fun e => by
    have := hw (Pi.single i e - Pi.single (i + 1) e) (by simp [Finset.sum_sub_distrib])
    have h1 := sum_wedge_single (lagr u l) i e
    have h2 := sum_wedge_single (lagr u l) (i + 1) e
    simp only [sum_mul_dEar, wedge, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at this h1 h2 ⊢
    linear_combination this - h1 + h2
  funext j
  fin_cases j
  · simpa [wedge] using key ![0, 1]
  · simpa [wedge] using key ![1, 0]

/-- **Page 14, the Lagrange form.** `λ ∈ N(u_*)` iff `Σ λ_i dφ_i = w ∧ Σ dv_i` for a
constant vector `w`: the page's `Σ λ_i df_i = μ Σ dx_i + ν Σ dy_i`. -/
theorem isMult_iff_lagrange (u : ZMod n → Fin 2 → k) (l : ZMod n → k) :
    IsMult u l ↔ ∃ w : Fin 2 → k, ∀ v, ∑ i, l i * dEar u v i = wedge w (∑ i, v i) :=
  ⟨fun h => ⟨lagr u l 0, fun v => by rw [sum_mul_dEar, wedge_sum]; simp only [lagr_const u l h]⟩,
    fun ⟨w, hw⟩ => (isMult_iff_closed u l).2 fun v hv => by rw [hw, hv]; simp [wedge]⟩

/-- The closed deformations: `Σ v_i = 0`. -/
def closedDef : Submodule k (ZMod n → Fin 2 → k) where
  carrier := {v | ∑ i, v i = 0}
  add_mem' ha hb := by simp_all [Finset.sum_add_distrib]
  zero_mem' := by simp
  smul_mem' c v hv := by simp_all [← Finset.smul_sum]

/-- **Pages 14 and 28, case (a).** `N(u_*) = 0` iff `dφ_u` maps the closed deformations
onto `k^{ℤ/n}`: `φ`, on the polygons with `Σ u_i` fixed, is a submersion at `u_*`. -/
theorem multSpace_eq_bot_iff (u : ZMod n → Fin 2 → k) :
    multSpace u = ⊥ ↔ closedDef.map (dEar u) = ⊤ := by
  have hf : ∀ (f : Module.Dual k (ZMod n → k)) x, f x = ∑ j, f (Pi.single j 1) * x j :=
    fun f x => by
      conv_lhs => rw [pi_eq_sum_univ x]
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      congr! 3 with j
      funext i; simp [Pi.single_apply, eq_comm]
  rw [Submodule.eq_bot_iff]
  refine ⟨fun h => by_contra fun hW => ?_, fun h l hl => funext fun j => ?_⟩
  · obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hW)
      inferInstance
    have hl := h (fun j => f (Pi.single j 1)) <| (isMult_iff_closed u _).2 fun v hv => by
      rw [← hf, ← Submodule.mem_bot k, ← hfW]
      exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (p := closedDef) hv)
    exact hf0 (LinearMap.ext fun x => by rw [hf]; simp [fun j => congrFun hl j])
  · obtain ⟨v, hv, hvj⟩ := (Submodule.eq_top_iff'.1 h) (Pi.single j 1)
    have := (isMult_iff_closed u l).1 hl v hv
    simpa [hvj, Pi.single_apply] using this

omit [NeZero n] in
/-- The ear-area map is bilinear in two copies of `u`. -/
def earBilin : (ZMod n → Fin 2 → k) →ₗ[k] (ZMod n → Fin 2 → k) →ₗ[k] (ZMod n → k) :=
  LinearMap.mk₂ k (fun a b i => wedge (a (i - 1)) (b i))
    (fun _ _ _ => by funext; simp [wedge]; ring) (fun _ _ _ => by funext; simp [wedge]; ring)
    (fun _ _ _ => by funext; simp [wedge]; ring) (fun _ _ _ => by funext; simp [wedge]; ring)

/-- Over a complete nontrivially normed field, `dEar u` is the strict derivative of the
ear-area map at `u`. -/
theorem hasStrictFDerivAt_earArea {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (u : ZMod n → Fin 2 → 𝕜) :
    HasStrictFDerivAt earArea (dEar u).toContinuousLinearMap u := by
  have h := (earBilin (k := 𝕜) (n := n)).toContinuousBilinearMap.hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_id u) (hasStrictFDerivAt_id u)
  refine HasStrictFDerivAt.congr_fderiv (f := earArea) h (ContinuousLinearMap.ext fun v => ?_)
  funext i; simp [earBilin, dEar, add_comm]

end Lagrange

/-! ## Page 28: the four cases, and the nine-gon of page 18

* `four_cases`: for nonzero sides and `|k| > n`, `N(u_*)` is in one of the four cases of the
  Théorème of page 28 — (a) `N(u_*) = 0`; (b₁) a nowhere-zero multiplier and dimension `1`;
  (b₂) a nowhere-zero multiplier and dimension `2`; (c) `N(u_*) ≠ 0` inside some `H_i`,
  and dimension `1` — and `four_cases_exclusive`: in only one.
* `special_two_span`: in case (c) at `i`, `N(u_*)` is the line of the unique multiplier with
  `λ_i = 0`, `λ_{i+1} = 1`, to which `zero_multiplier_criterion` applies (for `i = 0`).
* `nonagon`: the star nine-gon of page 18 has `N(u_*)` a line, spanned by a multiplier zero
  at `0` and nowhere else, for every value of the parameters allowed by the page.
-/

section FourCases

variable [Field k] {n : ℕ} [NeZero n] (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)
include hu

omit hu in
theorem finrank_ne_zero_of_mem {l : ZMod n → k} (hl : l ∈ multSpace u) (hl0 : l ≠ 0) :
    Module.finrank k (multSpace u) ≠ 0 := fun h =>
  hl0 (by simpa using (Submodule.finrank_eq_zero.1 h ▸ hl : l ∈ (⊥ : Submodule k _)))

/-- **Page 28, the Théorème: the four cases** (`|k| > n`). -/
theorem four_cases (hk : (n : ℕ∞) < ENat.card k) :
    multSpace u = ⊥ ∨
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧ Module.finrank k (multSpace u) = 1) ∨
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧ Module.finrank k (multSpace u) = 2) ∨
      (multSpace u ≠ ⊥ ∧ (∃ i, ∀ l ∈ multSpace u, l i = 0) ∧
        Module.finrank k (multSpace u) = 1) := by
  have h2 := finrank_multSpace_le_two u hu
  rcases dichotomy u hk with ⟨l, hl, hl0⟩ | hH
  · have := finrank_ne_zero_of_mem u hl fun h => hl0 0 (by simp [h])
    right
    interval_cases h : Module.finrank k (multSpace u)
    · exact absurd rfl this
    · exact Or.inl ⟨⟨l, hl, hl0⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨⟨l, hl, hl0⟩, rfl⟩)
  · by_cases hb : multSpace u = ⊥
    · exact Or.inl hb
    obtain ⟨i, hi⟩ := hH
    obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff _).1 hb
    have := finrank_ne_zero_of_mem u hl hl0
    have := finrank_le_one_of_le_hyperplane u hu i hi
    exact Or.inr (Or.inr (Or.inr ⟨hb, ⟨i, hi⟩, by omega⟩))

omit hu [NeZero n] in
/-- The four cases exclude one another: (a) excludes a nowhere-zero multiplier and is
`N(u_*) ≠ 0` negated, (b₁) and (b₂) differ by the dimension, and (b) excludes (c). -/
theorem four_cases_exclusive :
    (multSpace u = ⊥ → ¬ ∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) → ¬ ∃ i, ∀ l ∈ multSpace u, l i = 0) :=
  ⟨fun h ⟨l, hl, hl0⟩ => hl0 0 (by rw [h] at hl; simp [(Submodule.mem_bot k).1 hl]),
    fun ⟨l, hl, hl0⟩ ⟨i, hi⟩ => hl0 i (hi l hl)⟩

/-- **Page 28, case (c).** If `N(u_*) ≠ 0` lies in `H_i`, it is the line spanned by a
multiplier with `λ_i = 0` and `λ_{i+1} = 1`. -/
theorem special_two_span (hb : multSpace u ≠ ⊥) (i : ZMod n)
    (hi : ∀ l ∈ multSpace u, l i = 0) :
    ∃ l ∈ multSpace u, l i = 0 ∧ l (i + 1) = 1 ∧ ∀ l' ∈ multSpace u, ∃ c : k, l' = c • l := by
  obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff _).1 hb
  have h1 : l (i + 1) ≠ 0 := fun h => hl0 (eq_zero_of_consecutive u hu l hl i (hi l hl) h)
  have hm : (l (i + 1))⁻¹ • l ∈ multSpace u := Submodule.smul_mem _ _ hl
  have hne : (⟨_, hm⟩ : multSpace u) ≠ 0 := fun h => by
    have := congrArg (fun x : multSpace u => x.1 (i + 1)) h
    simp [h1] at this
  have hf : Module.finrank k (multSpace u) = 1 :=
    le_antisymm (finrank_le_one_of_le_hyperplane u hu i hi) (Nat.one_le_iff_ne_zero.2
      (finrank_ne_zero_of_mem u hl hl0))
  refine ⟨_, hm, by simp [hi l hl], by simp [h1], fun l' hl' => ?_⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hf ⟨l', hl'⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

end FourCases

section Nonagon

variable [Field k]

/-- The star nine-gon of page 18, by its sides: vertices `s₀ = (0,0)`, `s₁ = (1,0)`,
`s₂ = (1,1)`, `s₃ = (β₁, β₁)`, `s₄ = (β₁, y₄)`, `s₅ = (β₂β₁, β₂y₄)`, `s₆ = (β₂β₁, y₆)`,
`s₇ = (β₃β₂β₁, β₃y₆)`, `s₈ = (β₃β₂β₁, y₈)`, `s₉ = s₀`. The odd sides are parallel to `u₁`,
the even ones lie on lines through `s₀`. -/
def nonagon (b₁ b₂ b₃ y₄ y₆ y₈ : k) : ZMod 9 → Fin 2 → k :=
  ![![1, 0], ![0, 1], ![b₁ - 1, b₁ - 1], ![0, y₄ - b₁], ![(b₂ - 1) * b₁, (b₂ - 1) * y₄],
    ![0, y₆ - b₂ * y₄], ![(b₃ - 1) * (b₂ * b₁), (b₃ - 1) * y₆], ![0, y₈ - b₃ * y₆],
    ![-(b₃ * (b₂ * b₁)), -y₈]]

/-- **Page 18.** For `βⱼ ≠ 0, 1`, `y₄ ≠ β₁`, `y₆ ≠ β₂y₄`, `y₈ ≠ β₃y₆`, the nine-gon's
`N(u_*)` is a line, spanned by a multiplier zero at `0` and nowhere else. -/
theorem nonagon_multSpace {b₁ b₂ b₃ y₄ y₆ y₈ : k} (h₁ : b₁ ≠ 0) (h₁' : b₁ ≠ 1) (h₂ : b₂ ≠ 0)
    (h₂' : b₂ ≠ 1) (h₃ : b₃ ≠ 0) (h₃' : b₃ ≠ 1) (h₄ : y₄ ≠ b₁) (h₆ : y₆ ≠ b₂ * y₄)
    (h₈ : y₈ ≠ b₃ * y₆) :
    ∃ l ∈ multSpace (nonagon b₁ b₂ b₃ y₄ y₆ y₈), l 0 = 0 ∧ (∀ i, i ≠ 0 → l i ≠ 0) ∧
      ∀ l' ∈ multSpace (nonagon b₁ b₂ b₃ y₄ y₆ y₈), ∃ c : k, l' = c • l := by
  set u := nonagon b₁ b₂ b₃ y₄ y₆ y₈
  have hu : ∀ i, u i ≠ 0 := by
    intro i h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    fin_cases i <;> simp [u, nonagon, sub_eq_zero, h₁, h₁', h₂, h₂', h₃, h₃', h₄, h₆, h₈] at e0 e1
  obtain ⟨l, h0, h1, hl⟩ := (zero_multiplier_criterion (by norm_num) u hu).2 ⟨by
    rw [← sum_range_eq_sum]
    funext j; fin_cases j <;> simp [Finset.sum_range_succ, u, nonagon] <;> ring, by
    intro i h2 h8
    interval_cases i
    all_goals refine Or.inr ?_
    all_goals simp only [partialSum, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.reduceSub, u, nonagon, wedge, Pi.add_apply,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    exacts [Or.inl ⟨by ring, by ring⟩, Or.inr ⟨by ring, by ring⟩, Or.inl ⟨by ring, by ring⟩,
      Or.inr ⟨by ring, by ring⟩, Or.inl ⟨by ring, by ring⟩, Or.inr ⟨by ring, by ring⟩,
      Or.inl ⟨by ring, by ring⟩]⟩
  have hl0 : l ≠ 0 := fun h => by simp [h] at h1
  have hf : Module.finrank k (multSpace u) = 1 := by
    have := finrank_multSpace_le_two u hu
    have := finrank_ne_zero_of_mem u hl hl0
    have : Module.finrank k (multSpace u) ≠ 2 := fun h => by
      have := congrFun (((finrank_multSpace_eq_two_iff u hu
        ⟨0, 1, by simp [u, nonagon, wedge]⟩).1 h).2.1 1) 0
      norm_num [u, nonagon, sub_eq_zero, h₁, h₂'] at this
    omega
  refine ⟨l, hl, h0, fun i hi => ?_, fun l' hl' => ?_⟩
  · obtain ⟨m, hm1, hm8, rfl⟩ : ∃ m : ℕ, 1 ≤ m ∧ m ≤ 8 ∧ (m : ZMod 9) = i :=
      ⟨i.val, Nat.pos_of_ne_zero fun h => hi ((ZMod.val_eq_zero i).1 h),
        Nat.le_of_lt_succ (ZMod.val_lt i), ZMod.natCast_zmod_val i⟩
    rw [Ne, mult_eq_zero_iff u hu l h0 h1 hl m hm1]
    intro h
    have e0 := congrFun h 0
    interval_cases m <;> simp [partialSum, Finset.sum_range_succ, u, nonagon] at e0
    all_goals ((try ring_nf at e0); simp [h₁, h₂, h₃] at e0)
  · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _
      (fun h => hl0 (congrArg Subtype.val h) : (⟨l, hl⟩ : multSpace u) ≠ 0)).1 hf ⟨l', hl'⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

end Nonagon
end Folder73
