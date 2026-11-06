module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.FieldTheory.Relrank
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

@[expose] public section


/-!
# Folder 70, pages 74–78 and 89–102: the icosahedron over `ℤ[α]` and modulo 5

The modernised reading `transcripts/70/70.modern.tex` (§ VII, « L'icosaèdre en
coordonnées universelles », pages 73 to 111) writes the regular icosahedron over
`ℤ[α] = ℤ[x]/(x² + x − 1)` by three reflections in the vertex frame
`(s₀, s₁ − s₀, s₂ − s₀, s₃ − s₀)`, with `α' = −1 − α`:

> `σ₀(x, y, z) = (1 − (x + y + z), y, z)`, `σ₁(x, y, z) = (y + α'z, x − α'z, z)`,
> `σ₂(x, y, z) = (x, z, y)`; the twelve vertices `s₀, s₁, s₂, s₃, s'₃ = (α', −α', 1)`,
> `s''₃ = (0, −α', 1)` and their images by `ι(x, y, z) = (α' − x, 1 − α' − y, 1 − α' − z)`
> (pages 74–75, 89–92); the invariant function
> `q = x² + y² + z² − αyz + zx + xy − (x + y + z)` (page 95, (19)) and its quadratic part
> `q₀` (pages 101–102).
>
> **Page 78.** « 6 directions de sommets, 15 d'arêtes, 10 de plans de faces :
> `31 = 5² + 5 + 1` » ; in characteristic 5 the vertex directions are the conic
> `q₀ = 0`, and `125 = 1 + 24 + 60 + 40`, the 24 nonzero isotropic vectors being the
> vertices of « deux icosaèdres ».

This is finding `70-icosahedron-char5-conic` of `src/content/findings.ts`, and the
characteristic-5 case of `70-icosahedron-integral-faithful`. Proving them says only
that the claims hold as stated; whether they stand in the literature is a separate
question.

What is formalised.

* Over any commutative ring `R` with `α² + α − 1 = 0`: `q_vert` (the twelve vertices lie
  on `q = 0`), `sigma0_vert`, `sigma1_vert`, `sigma2_vert` (the three generators
  permute the twelve vertices, by the explicit permutations `perm0`, `perm1`, `perm2`),
  `q0_edge` (the thirty edges, listed in `edge`, have `q₀ = 1`), and `isUnit_z` (the
  nine vertices off the face `(s₀, s₁, s₂)` have a unit `z`-coordinate, page 94), and
  `iota_char_two` (in characteristic 2, `ι` is the translation by `(α', α, α)`).
* Over `𝔽₅`: `alpha_eq_two` (`α = 2` is the only root), `two_centre` (the centre
  `o = (1, 2, 2)`, `2o = (α', 1 − α', 1 − α')`), `centre_fixed`, `vert_isotropic`
  (`q₀(s − o) = 0` at the twelve vertices, equivalently `q(o) = 0`), `isotropic_iff`,
  `isotropic_card` and `twoIcos_injective` (the nonzero isotropic vectors are the
  twelve centred vertices and their doubles, twenty-four in all), `conic_iff` (a point
  of `ℙ²(𝔽₅)` is on the conic `q₀ = 0` iff it is one of the six vertex directions),
  `point_bijective` and `card_proj` (the 6 vertex, 15 edge and 10 face directions are
  the 31 points of `ℙ²(𝔽₅)`), `edgeDir_cover`, `faceDir_cover`, `vertDir_cover` (every
  edge, face, vertex gives one of the chosen directions), `face_orth` (the face
  direction is the barycentre, orthogonal to the face plane for the polar form),
  `edge_tangents` and `face_tangents` (an edge point lies on exactly two tangents of the
  conic, a face point on none), `card_square`, `card_nonsquare` (`60` and `40`).
* Faithfulness in every characteristic (finding `70-icosahedron-integral-faithful`, the
  incidence part), over any nonzero commutative ring with `α² + α − 1 = 0`:
  `vert_injective_any` (twelve distinct vertices), `not_collinear_any` (no three on a
  line), `not_in_face_plane_any` (no vertex in the plane of a face not containing it).
  The proof is the page's « par homogénéité » made explicit: `sigmaOf_vert` and the
  kernel-checked word tables `pairWord`, `faceWord` reduce every case to the lines
  `s₀s₁`, `s₀s''₃`, `s₀ι(s₀)` and the face plane `z = 0`, where a `2 × 2` minor is a unit
  of `ℤ[α]` (`base_line_1`, `base_line_5`, `base_line_6`) and `isUnit_z` applies.
-/

namespace Grothendieck.Folder70

/-! ## The icosahedron over a ring with `α² + α − 1 = 0` -/

section General

variable {R : Type*} [CommRing R] (α : R)

/-- `σ₀` of page 74. -/
def sigma0 (p : R × R × R) : R × R × R := (1 - (p.1 + p.2.1 + p.2.2), p.2.1, p.2.2)

/-- `σ₁` of page 74, with `α' = −1 − α`. -/
def sigma1 (p : R × R × R) : R × R × R :=
  (p.2.1 + (-1 - α) * p.2.2, p.1 - (-1 - α) * p.2.2, p.2.2)

/-- `σ₂` of page 74. -/
def sigma2 (p : R × R × R) : R × R × R := (p.1, p.2.2, p.2.1)

/-- The antipodism `ι` of page 91, (17). -/
def iota (p : R × R × R) : R × R × R :=
  ((-1 - α) - p.1, 1 - (-1 - α) - p.2.1, 1 - (-1 - α) - p.2.2)

/-- The twelve vertices of page 75 in the order `s₀, s₁, s₂, s₃, s'₃, s''₃` and their
antipodes `ι s₀, …, ι s''₃`. -/
def vert : Fin 12 → R × R × R :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1 - α, -(-1 - α), 1), (0, -(-1 - α), 1),
    iota α (0, 0, 0), iota α (1, 0, 0), iota α (0, 1, 0), iota α (0, 0, 1),
    iota α (-1 - α, -(-1 - α), 1), iota α (0, -(-1 - α), 1)]

/-- The invariant function `q` of page 95, (19). -/
def q (p : R × R × R) : R :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - α * p.2.1 * p.2.2 + p.2.2 * p.1 + p.1 * p.2.1
    - (p.1 + p.2.1 + p.2.2)

/-- Its quadratic part `q₀` (pages 75 and 101). -/
def q0 (p : R × R × R) : R :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - α * p.2.1 * p.2.2 + p.2.2 * p.1 + p.1 * p.2.1

/-- The polar form of `q₀`, of matrix `[[2, 1, 1], [1, 2, −α], [1, −α, 2]]`. -/
def polar (u v : R × R × R) : R :=
  2 * u.1 * v.1 + 2 * u.2.1 * v.2.1 + 2 * u.2.2 * v.2.2 - α * (u.2.1 * v.2.2 + u.2.2 * v.2.1)
    + (u.2.2 * v.1 + u.1 * v.2.2) + (u.1 * v.2.1 + u.2.1 * v.1)

/-- The permutations of the vertices induced by `σ₀`, `σ₁`, `σ₂`. -/
def perm0 : Fin 12 → Fin 12 := ![1, 0, 2, 3, 5, 4, 7, 6, 8, 9, 11, 10]
/-- See `perm0`. -/
def perm1 : Fin 12 → Fin 12 := ![0, 2, 1, 4, 3, 5, 6, 8, 7, 10, 9, 11]
/-- See `perm0`. -/
def perm2 : Fin 12 → Fin 12 := ![0, 1, 3, 2, 11, 10, 6, 7, 9, 8, 5, 4]

/-- The thirty edges, as pairs of vertex indices (the pairs at `q₀`-distance `1`
over `ℚ(√5)`). -/
def edge : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 11), (1, 2), (1, 3), (1, 5), (1, 10), (2, 4),
    (2, 5), (2, 9), (3, 8), (3, 10), (3, 11), (4, 7), (4, 9), (4, 11), (5, 6), (5, 9),
    (5, 10), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8), (7, 9), (7, 11), (8, 10), (8, 11)]

/-- The twenty faces, the triangles of edges. -/
def face : Fin 20 → Fin 12 × Fin 12 × Fin 12 :=
  ![(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 3, 11), (0, 4, 11), (1, 2, 5), (1, 3, 10),
    (1, 5, 10), (2, 4, 9), (2, 5, 9), (3, 8, 10), (3, 8, 11), (4, 7, 9), (4, 7, 11),
    (5, 6, 9), (5, 6, 10), (6, 7, 8), (6, 7, 9), (6, 8, 10), (7, 8, 11)]

variable {α}

/-- The twelve vertices lie on the quadric `q = 0` (page 101). -/
theorem q_vert (h : α ^ 2 + α - 1 = 0) (i : Fin 12) : q α (vert α i) = 0 := by
  fin_cases i <;> simp only [q, vert, iota, Fin.reduceFinMk, Matrix.cons_val] <;>
    first | ring1 | linear_combination (-2 - α) * h | linear_combination (-1 - α) * h

theorem sigma0_vert (i : Fin 12) : sigma0 (vert α i) = vert α (perm0 i) := by
  fin_cases i <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [sigma0, vert, iota, perm0] <;> ring1

theorem sigma1_vert (h : α ^ 2 + α - 1 = 0) (i : Fin 12) :
    sigma1 α (vert α i) = vert α (perm1 i) := by
  fin_cases i <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [sigma1, vert, iota, perm1, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val] <;>
    first | ring1 | linear_combination (-1 : R) * h | linear_combination h

theorem sigma2_vert (i : Fin 12) : sigma2 (vert α i) = vert α (perm2 i) := by
  fin_cases i <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [sigma2, vert, iota, perm2] <;> ring1

/-- The thirty edges have `q₀ = 1` (the normalisation of page 75). -/
theorem q0_edge (h : α ^ 2 + α - 1 = 0) (e : Fin 30) :
    q0 α (vert α (edge e).2 - vert α (edge e).1) = 1 := by
  fin_cases e <;> simp only [q0, vert, iota, edge, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
    Prod.fst_sub, Prod.snd_sub] <;>
    first | ring1 | linear_combination (-α) * h | linear_combination (1 + α) * h

/-- Page 94: the nine vertices off the face `(s₀, s₁, s₂)` have a unit `z`-coordinate,
so none lies in its plane `z = 0`, over any base. -/
theorem isUnit_z (h : α ^ 2 + α - 1 = 0) (i : Fin 12) (hi : 3 ≤ i.val) :
    IsUnit (vert α i).2.2 := by
  have u1 : IsUnit (2 + α) := ⟨⟨2 + α, 1 - α, by linear_combination -h, by
    linear_combination -h⟩, rfl⟩
  have u2 : IsUnit (1 + α) := ⟨⟨1 + α, α, by linear_combination h, by
    linear_combination h⟩, rfl⟩
  fin_cases i <;> simp at hi <;> simp [vert, iota] <;> ring_nf <;>
    first | exact u1 | exact u2

/-- Page 91, (17): in characteristic `2` the antipodism is the translation by
`(α', α, α)` (the page reads « `(α', 1, 1)` »). No hypothesis on `α` is needed. -/
theorem iota_char_two (h2 : (2 : R) = 0) (p : R × R × R) :
    iota α p = p + (-1 - α, α, α) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [iota, Prod.fst_add, Prod.snd_add]
  · linear_combination (-p.1) * h2
  · linear_combination (1 - p.2.1) * h2
  · linear_combination (1 - p.2.2) * h2

end General

/-! ## Faithfulness in every characteristic (finding `70-icosahedron-integral-faithful`)

The page's « par homogénéité » (pages 93–94), made explicit: the group generated by the
`σᵢ` permutes the vertices by `perm0`, `perm1`, `perm2`; it carries every pair of distinct
vertices to `(s₀, s₁)`, `(s₀, s''₃)` or `(s₀, ι s₀)` (`pairWord`), and every face, in
order, to `(s₀, s₁, s₂)` (`faceWord`), which the kernel checks on `Fin 12`. The base
cases are a unit `2 × 2` minor of `ℤ[α]`, written as a certificate. -/

section Faithful

variable {R : Type*} [CommRing R] {α : R}

/-- The three vertex permutations. -/
def permOf : Fin 3 → Fin 12 → Fin 12 := ![perm0, perm1, perm2]

/-- The permutation of a word `[k₁, …, kₙ]`: `π_{k₁} ∘ ⋯ ∘ π_{kₙ}`. -/
def app (w : List (Fin 3)) (i : Fin 12) : Fin 12 := w.foldr (fun k i => permOf k i) i

/-- The three generators. -/
def sigmaOf (α : R) : Fin 3 → R × R × R → R × R × R := ![sigma0, sigma1 α, sigma2]

theorem sigmaOf_vert (h : α ^ 2 + α - 1 = 0) (k : Fin 3) (i : Fin 12) :
    sigmaOf α k (vert α i) = vert α (permOf k i) := by
  fin_cases k
  · exact sigma0_vert i
  · exact sigma1_vert h i
  · exact sigma2_vert i

/-- `p` is in the affine plane spanned by `r, u, w` (with these parameters). -/
def InPlane (p r u w : R × R × R) : Prop := ∃ s t : R, p - r = s • (u - r) + t • (w - r)

/-- `p` is on the line through `r` and `u`. -/
def OnLine (p r u : R × R × R) : Prop := ∃ a : R, p - r = a • (u - r)

theorem sigmaOf_plane (k : Fin 3) {p r u w : R × R × R} (H : InPlane p r u w) :
    InPlane (sigmaOf α k p) (sigmaOf α k r) (sigmaOf α k u) (sigmaOf α k w) := by
  obtain ⟨s, t, hst⟩ := H
  simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hst
  obtain ⟨h1, h2, h3⟩ := hst
  refine ⟨s, t, ?_⟩
  fin_cases k <;> simp only [sigmaOf, Fin.reduceFinMk, Matrix.cons_val, sigma0, sigma1, sigma2,
    Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  · exact ⟨by linear_combination -h1 - h2 - h3, by linear_combination h2, by linear_combination h3⟩
  · exact ⟨by linear_combination h2 + (-1 - α) * h3, by linear_combination h1 - (-1 - α) * h3,
      by linear_combination h3⟩
  · exact ⟨by linear_combination h1, by linear_combination h3, by linear_combination h2⟩

theorem sigmaOf_line (k : Fin 3) {p r u : R × R × R} (H : OnLine p r u) :
    OnLine (sigmaOf α k p) (sigmaOf α k r) (sigmaOf α k u) := by
  obtain ⟨a, ha⟩ := H
  obtain ⟨s, t, hst⟩ := sigmaOf_plane (α := α) (p := p) (r := r) (u := u) (w := r) k
    ⟨a, 0, by simp [ha]⟩
  exact ⟨s, by simpa using hst⟩

theorem plane_of_word (h : α ^ 2 + α - 1 = 0) (w : List (Fin 3)) {m a b c : Fin 12}
    (H : InPlane (vert α m) (vert α a) (vert α b) (vert α c)) :
    InPlane (vert α (app w m)) (vert α (app w a)) (vert α (app w b)) (vert α (app w c)) := by
  induction w with
  | nil => exact H
  | cons k w ih =>
    simpa only [sigmaOf_vert h, app, List.foldr_cons] using sigmaOf_plane (α := α) k ih

theorem line_of_word (h : α ^ 2 + α - 1 = 0) (w : List (Fin 3)) {i j k : Fin 12}
    (H : OnLine (vert α k) (vert α i) (vert α j)) :
    OnLine (vert α (app w k)) (vert α (app w i)) (vert α (app w j)) := by
  induction w with
  | nil => exact H
  | cons c w ih =>
    simpa only [sigmaOf_vert h, app, List.foldr_cons] using sigmaOf_line (α := α) c ih

theorem eq_of_word (h : α ^ 2 + α - 1 = 0) (w : List (Fin 3)) {i j : Fin 12}
    (H : vert α i = vert α j) : vert α (app w i) = vert α (app w j) := by
  induction w with
  | nil => exact H
  | cons c w ih =>
    simpa only [sigmaOf_vert h, app, List.foldr_cons] using congrArg (sigmaOf α c) ih

theorem app_injective (w : List (Fin 3)) : Function.Injective (app w) := by
  have hp : ∀ k : Fin 3, Function.Injective (permOf k) := by
    unfold Function.Injective; decide +kernel
  induction w with
  | nil => exact fun _ _ h => h
  | cons c w ih => exact fun x y hxy => ih (hp c hxy)

/-- For `i ≠ j`, a word sending `i` to `s₀` and `j` to `s₁`, `s''₃` or `ι s₀`. -/
def pairWord : Fin 12 → Fin 12 → List (Fin 3) :=
  ![![[], [], [1], [1, 2], [1, 2, 1], [], [], [2, 1, 2, 1], [2, 1, 2], [2, 1], [2], [1, 2, 1, 2]],
    ![[0], [], [1, 0], [1, 2, 0], [0], [1, 2, 1, 0], [2, 1, 2, 1, 0], [0], [2, 1, 2, 0], [2, 1, 0],
      [1, 2, 1, 2, 0], [2, 0]],
    ![[0, 1], [0, 1, 0], [], [0, 1], [1, 2, 0, 1], [1, 2, 0, 1, 0], [2, 1, 2, 0, 1, 0],
      [2, 1, 2, 0, 1], [0, 1], [1, 2, 1, 2, 0, 1], [2, 0, 1, 0], [2, 0, 1]],
    ![[0, 1, 2], [0, 1, 2, 0], [0, 1, 2], [], [2, 0, 1, 2], [2, 0, 1, 2, 0], [2, 1, 2, 0, 1, 2, 0],
      [2, 1, 2, 0, 1, 2], [1, 2, 1, 2, 0, 1, 2], [0, 1, 2], [1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2]],
    ![[0, 1, 2, 1], [0, 1, 2, 1], [0, 1, 2, 0, 1], [2, 0, 1, 2, 1], [], [2, 0, 1, 2, 0, 1],
      [2, 1, 2, 0, 1, 2, 0, 1], [1, 2, 1, 2, 0, 1, 2, 1], [2, 1, 2, 0, 1, 2, 1],
      [1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 1], [1, 2, 0, 1, 2, 1]],
    ![[0, 1, 2, 1, 0], [0, 1, 2, 1, 0], [0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 1, 0],
      [2, 0, 1, 2, 0, 1, 0], [], [1, 2, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 0],
      [2, 1, 2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 1, 0]],
    ![[0, 1, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 1, 2, 0, 1, 2, 1, 0],
      [0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
      [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1, 2, 1, 0], [],
      [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
      [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
      [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0]],
    ![[0, 1, 2, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 0, 1, 2, 0, 1],
      [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 0, 1, 2, 1],
      [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [],
      [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1],
      [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 1, 2, 1]],
    ![[0, 1, 2, 1, 2, 0, 1, 2], [0, 1, 2, 1, 2, 0, 1, 2, 0], [0, 1, 2, 1, 2, 0, 1, 2],
      [0, 1, 2, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0],
      [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [],
      [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0],
      [0, 1, 2, 0, 1, 2, 0, 1, 2]],
    ![[0, 1, 2, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0, 1],
      [0, 1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0],
      [1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [],
      [2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1]],
    ![[0, 1, 2, 1, 2, 0], [0, 1, 2, 1, 2, 0], [0, 1, 2, 1, 2, 1, 0], [0, 1, 2, 0, 1, 2, 0],
      [0, 1, 2, 1, 2, 0], [0, 1, 2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
      [2, 1, 2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0], [2, 0, 1, 2, 0, 1, 2, 1, 0], [],
      [2, 0, 1, 2, 0, 1, 2, 0]],
    ![[0, 1, 2, 1, 2], [0, 1, 2, 1, 2], [0, 1, 2, 1, 2, 1], [0, 1, 2, 0, 1, 2],
      [0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2], [2, 1, 2, 0, 1, 2, 0, 1, 2],
      [1, 2, 0, 1, 2, 0, 1, 2, 1], [1, 2, 0, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 2, 1],
      [2, 0, 1, 2, 0, 1, 2], []]]
/-- A word sending the face `f`, in order, to `(s₀, s₁, s₂)`. -/
def faceWord : Fin 20 → List (Fin 3) :=
  ![[], [2], [2, 1], [2, 1, 2], [2, 1, 2, 1], [2, 1, 0], [2, 1, 2, 0], [2, 1, 2, 1, 0],
    [2, 1, 2, 0, 1], [2, 1, 2, 0, 1, 0], [1, 2, 1, 2, 0, 1, 2, 0], [1, 2, 1, 2, 0, 1, 2],
    [1, 2, 1, 2, 0, 1, 2, 0, 1], [1, 2, 1, 2, 0, 1, 2, 1], [1, 2, 1, 2, 0, 1, 2, 0, 1, 0],
    [1, 2, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1]]

theorem pairWord_spec : ∀ i j : Fin 12, i ≠ j → app (pairWord i j) i = 0 ∧
    (app (pairWord i j) j = 1 ∨ app (pairWord i j) j = 5 ∨ app (pairWord i j) j = 6) := by
  decide +kernel

theorem faceWord_spec : ∀ f : Fin 20, app (faceWord f) (face f).1 = 0 ∧
    app (faceWord f) (face f).2.1 = 1 ∧ app (faceWord f) (face f).2.2 = 2 := by
  decide +kernel

variable [Nontrivial R]

theorem base_line_1 (h : α ^ 2 + α - 1 = 0) (k : Fin 12) (hk0 : k ≠ 0) (hkj : k ≠ 1)
    (a : R) : vert α k ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  apply one_ne_zero (α := R)
  fin_cases k <;> simp only [vert, iota, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  · exact absurd rfl hk0
  · exact absurd rfl hkj
  · linear_combination h2
  · linear_combination h3
  · linear_combination α * h2 - h
  · linear_combination α * h2 - h
  · linear_combination (1 - α) * h2 + h
  · linear_combination (1 - α) * h2 + h
  · linear_combination α * h2 - h
  · linear_combination (1 - α) * h2 + h
  · linear_combination h2
  · linear_combination h2

theorem base_line_5 (h : α ^ 2 + α - 1 = 0) (k : Fin 12) (hk0 : k ≠ 0) (hkj : k ≠ 5)
    (a : R) : vert α k ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  apply one_ne_zero (α := R)
  fin_cases k <;> simp only [vert, iota, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  · exact absurd rfl hk0
  · linear_combination α * (1 + α) * h1 - h
  · linear_combination h2 - (1 + α) * h3
  · linear_combination -α * (h2 - (1 + α) * h3) - h
  · linear_combination (α - 1) * (1 + α) * h1 + α * h
  · exact absurd rfl hkj
  · linear_combination (α - 1) * (1 + α) * h1 + α * h
  · linear_combination (1 - 2 * α) * (1 + α) * h1 - (3 + 2 * α) * h
  · linear_combination (α - 1) * (1 + α) * h1 + α * h
  · linear_combination (α - 1) * (1 + α) * h1 + α * h
  · linear_combination -α * (h2 - (1 + α) * h3) - (1 + α) * h
  · linear_combination (α - 1) * (1 + α) * h1 + α * h

theorem base_line_6 (h : α ^ 2 + α - 1 = 0) (k : Fin 12) (hk0 : k ≠ 0) (hkj : k ≠ 6)
    (a : R) : vert α k ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  apply one_ne_zero (α := R)
  fin_cases k <;> simp only [vert, iota, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  · exact absurd rfl hk0
  · linear_combination (1 - α) * ((2 + α) * h1 + (1 + α) * h2) + h
  · linear_combination α * ((2 + α) * h1 + (1 + α) * h2) - h
  · linear_combination α * ((2 + α) * h1 + (1 + α) * h3) - h
  · linear_combination -α * ((2 + α) * h1 + (1 + α) * h2) - h
  · linear_combination (1 - α) * ((2 + α) * h1 + (1 + α) * h2) + α * h
  · exact absurd rfl hkj
  · linear_combination (α - 1) * ((2 + α) * h1 + (1 + α) * h2) + h
  · linear_combination -α * ((2 + α) * h1 + (1 + α) * h2) - h
  · linear_combination -α * ((2 + α) * h1 + (1 + α) * h3) - h
  · linear_combination α * ((2 + α) * h1 + (1 + α) * h2) - h
  · linear_combination (α - 1) * ((2 + α) * h1 + (1 + α) * h2) + α * h

omit [Nontrivial R] in
theorem vert_zero : vert α 0 = 0 := by simp [vert]

theorem base_line (h : α ^ 2 + α - 1 = 0) {j k : Fin 12} (hj : j = 1 ∨ j = 5 ∨ j = 6)
    (hk0 : k ≠ 0) (hkj : k ≠ j) (a : R) : vert α k ≠ a • vert α j := by
  rcases hj with rfl | rfl | rfl
  · exact base_line_1 h k hk0 hkj a
  · exact base_line_5 h k hk0 hkj a
  · exact base_line_6 h k hk0 hkj a

/-- The twelve vertices are distinct, over any nonzero ring with `α² + α = 1`. -/
theorem vert_injective_any (h : α ^ 2 + α - 1 = 0) : Function.Injective (vert α) := by
  intro i j hij
  by_contra hne
  obtain ⟨h0, hj⟩ := pairWord_spec i j hne
  have e := eq_of_word h (pairWord i j) hij
  rw [h0, vert_zero] at e
  rcases hj with hj | hj | hj <;> rw [hj] at e
  · simp [vert, Prod.ext_iff] at e
  · simp [vert, Prod.ext_iff] at e
  · have e3 := congrArg (fun p => p.2.2) e
    simp only [vert, iota, Matrix.cons_val, Prod.snd_zero] at e3
    exact one_ne_zero (show (1 : R) = 0 by linear_combination (α - 1) * e3 + h)

/-- Page 93, a)–c) « par homogénéité »: no three distinct vertices are collinear, over
any nonzero ring with `α² + α = 1` (over a field, `OnLine` is collinearity). -/
theorem not_collinear_any (h : α ^ 2 + α - 1 = 0) {i j k : Fin 12} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ¬ OnLine (vert α k) (vert α i) (vert α j) := by
  intro H
  obtain ⟨h0, hj⟩ := pairWord_spec i j hij
  obtain ⟨a, ha⟩ := line_of_word h (pairWord i j) H
  rw [h0, vert_zero, sub_zero, sub_zero] at ha
  refine base_line h hj ?_ ?_ a ha
  · rw [← h0]; exact fun h' => hik (app_injective _ h').symm
  · exact fun h' => hjk (app_injective _ h').symm

/-- Page 94 « par homogénéité »: no vertex is in the plane of a face not containing it,
over any nonzero ring with `α² + α = 1`. -/
theorem not_in_face_plane_any (h : α ^ 2 + α - 1 = 0) (f : Fin 20) {m : Fin 12}
    (h1 : m ≠ (face f).1) (h2 : m ≠ (face f).2.1) (h3 : m ≠ (face f).2.2) :
    ¬ InPlane (vert α m) (vert α (face f).1) (vert α (face f).2.1) (vert α (face f).2.2) := by
  intro H
  obtain ⟨e0, e1, e2⟩ := faceWord_spec f
  obtain ⟨s, t, hst⟩ := plane_of_word h (faceWord f) H
  rw [e0, e1, e2] at hst
  have hm : 3 ≤ (app (faceWord f) m).val := by
    have n0 : app (faceWord f) m ≠ 0 := by
      rw [← e0]; exact fun h' => h1 (app_injective _ h')
    have n1 : app (faceWord f) m ≠ 1 := by
      rw [← e1]; exact fun h' => h2 (app_injective _ h')
    have n2 : app (faceWord f) m ≠ 2 := by
      rw [← e2]; exact fun h' => h3 (app_injective _ h')
    revert n0 n1 n2
    generalize app (faceWord f) m = x
    revert x; decide
  have hz := congrArg (fun p => p.2.2) hst
  have z0 : (vert α 0).2.2 = 0 := by simp [vert]
  have z1 : (vert α 1).2.2 = 0 := by simp [vert]
  have z2 : (vert α 2).2.2 = 0 := by simp [vert]
  simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul, z0, z1, z2] at hz
  have hu := isUnit_z h _ hm
  rw [show (vert α (app (faceWord f) m)).2.2 = 0 by linear_combination hz] at hu
  exact not_isUnit_zero hu

end Faithful

/-! ## Modulo 5 -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `𝔽₅³`, the affine space of the reduction. -/
abbrev V5 := ZMod 5 × ZMod 5 × ZMod 5

/-- In `𝔽₅`, `α² + α − 1 = (α − 2)²`: the only root is `2` (page 78). -/
theorem alpha_eq_two (a : ZMod 5) : a ^ 2 + a - 1 = 0 ↔ a = 2 := by
  revert a; decide +kernel

/-- The centre `o = ½(α', 1 − α', 1 − α')` at `α = 2`. -/
def o : V5 := (1, 2, 2)

theorem two_centre : (2 : ZMod 5) • o = ((-1 - 2), 1 - (-1 - 2), 1 - (-1 - 2)) := by
  decide +kernel

theorem centre_fixed :
    sigma0 o = o ∧ sigma1 (2 : ZMod 5) o = o ∧ sigma2 o = o ∧ iota (2 : ZMod 5) o = o := by
  decide +kernel

/-- The centred vertex `s − o`. -/
def cv (i : Fin 12) : V5 := vert (2 : ZMod 5) i - o

/-- Page 78: in characteristic 5 the vertices are isotropic for `q₀` centred at `o`. -/
theorem vert_isotropic (i : Fin 12) : q0 (2 : ZMod 5) (cv i) = 0 := by
  revert i; decide +kernel

/-- `q(o) = 0`: the circumscribed quadric is a cone of vertex `o`. -/
theorem q_centre : q (2 : ZMod 5) o = 0 := by decide +kernel

/-- The nonzero isotropic vectors are the twelve centred vertices and their doubles. -/
theorem isotropic_iff (v : V5) :
    (v ≠ 0 ∧ q0 (2 : ZMod 5) v = 0) ↔ ∃ i, v = cv i ∨ v = (2 : ZMod 5) • cv i := by
  revert v; decide +kernel

/-- « Deux icosaèdres » : the vertices `s − o` and `2(s − o)`. -/
def twoIcos : Fin 12 ⊕ Fin 12 → V5
  | .inl i => cv i
  | .inr i => (2 : ZMod 5) • cv i

theorem twoIcos_injective : Function.Injective twoIcos := by
  unfold Function.Injective; decide +kernel

theorem isotropic_card :
    (Finset.univ.filter fun v : V5 => v ≠ 0 ∧ q0 (2 : ZMod 5) v = 0).card = 24 := by
  decide +kernel

theorem card_square :
    (Finset.univ.filter fun v : V5 => q0 (2 : ZMod 5) v = 1 ∨ q0 (2 : ZMod 5) v = 4).card
      = 60 := by
  decide +kernel

theorem card_nonsquare :
    (Finset.univ.filter fun v : V5 => q0 (2 : ZMod 5) v = 2 ∨ q0 (2 : ZMod 5) v = 3).card
      = 40 := by
  decide +kernel

/-! ### The 31 points of `ℙ²(𝔽₅)` -/

/-- The edge vector of an edge. -/
def ev (e : Fin 30) : V5 := vert (2 : ZMod 5) (edge e).2 - vert (2 : ZMod 5) (edge e).1

/-- The centred barycentre (tripled) of a face. -/
def fv (f : Fin 20) : V5 := cv (face f).1 + cv (face f).2.1 + cv (face f).2.2

/-- One edge for each of the fifteen edge directions. -/
def edgeRep : Fin 15 → Fin 30 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 17]

/-- The representative vectors: six vertex directions `s₀ − o, …, s''₃ − o`, fifteen
edge directions, ten face directions (faces `0, …, 9`). -/
def rep : Fin 6 ⊕ Fin 15 ⊕ Fin 10 → V5
  | .inl i => cv (Fin.castLE (by norm_num) i)
  | .inr (.inl k) => ev (edgeRep k)
  | .inr (.inr k) => fv (Fin.castLE (by norm_num) k)

theorem rep_ne_zero (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : rep x ≠ 0 := by
  revert x; decide +kernel

/-- The point of `ℙ²(𝔽₅)` of a representative. -/
def point (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : Projectivization (ZMod 5) V5 :=
  Projectivization.mk (ZMod 5) (rep x) (rep_ne_zero x)

theorem rep_prop_iff : ∀ x y : Fin 6 ⊕ Fin 15 ⊕ Fin 10,
    (∃ a : ZMod 5, a • rep y = rep x) → x = y := by
  decide +kernel

theorem rep_cover : ∀ v : V5, v ≠ 0 → ∃ x, ∃ a : ZMod 5, a • rep x = v := by
  decide +kernel

/-- Page 78: the 6 + 15 + 10 vertex, edge and face directions are the 31 points of
`ℙ²(𝔽₅)`, each once. -/
theorem point_bijective : Function.Bijective point := by
  refine ⟨fun x y hxy => ?_, fun p => ?_⟩
  · unfold point at hxy
    rw [Projectivization.mk_eq_mk_iff'] at hxy
    exact rep_prop_iff x y hxy
  · obtain ⟨x, a, ha⟩ := rep_cover p.rep p.rep_nonzero
    refine ⟨x, ?_⟩
    rw [← Projectivization.mk_rep p]
    unfold point
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀]; · simp
                   rintro rfl; exact p.rep_nonzero (by rw [← ha, zero_smul])⟩

theorem card_proj : Nat.card (Projectivization (ZMod 5) V5) = 31 := by
  rw [← Nat.card_eq_of_bijective point point_bijective]
  simp

/-- Every vertex direction is one of the six. -/
theorem vertDir_cover :
    ∀ i : Fin 12, ∃ k : Fin 6, ∃ a : ZMod 5, cv i = a • rep (.inl k) := by
  decide +kernel

/-- Each of the thirty edges is along one of the fifteen chosen edge directions. -/
theorem edgeDir_cover :
    ∀ e : Fin 30, ∃ k : Fin 15, ∃ a : ZMod 5, ev e = a • rep (.inr (.inl k)) := by
  decide +kernel

/-- Each of the twenty faces gives one of the ten chosen face directions. -/
theorem faceDir_cover :
    ∀ f : Fin 20, ∃ k : Fin 10, ∃ a : ZMod 5, fv f = a • rep (.inr (.inr k)) := by
  decide +kernel

/-- The face direction is the barycentre, polar-orthogonal to the plane of the face. -/
theorem face_orth : ∀ f : Fin 20,
    polar (2 : ZMod 5) (fv f) (cv (face f).2.1 - cv (face f).1) = 0 ∧
    polar (2 : ZMod 5) (fv f) (cv (face f).2.2 - cv (face f).1) = 0 := by
  decide +kernel

/-- Page 78: a point of `ℙ²(𝔽₅)` lies on the conic `q₀ = 0` iff it is a vertex
direction. -/
theorem conic_iff (v : V5) (hv : v ≠ 0) :
    q0 (2 : ZMod 5) v = 0 ↔ Projectivization.mk (ZMod 5) v hv ∈ Set.range (point ∘ .inl) := by
  have key : ∀ v : V5, v ≠ 0 →
      (q0 (2 : ZMod 5) v = 0 ↔ ∃ k : Fin 6, ∃ a : ZMod 5, a • rep (.inl k) = v) := by
    decide +kernel
  rw [key v hv]
  constructor
  · rintro ⟨k, a, ha⟩
    exact ⟨k, by
      simp only [Function.comp, point]
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨a⁻¹, ?_⟩
      have ha0 : a ≠ 0 := by rintro rfl; exact hv (by rw [← ha, zero_smul])
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩
  · rintro ⟨k, hk⟩
    simp only [Function.comp, point] at hk
    rw [Projectivization.mk_eq_mk_iff'] at hk
    obtain ⟨a, ha⟩ := hk
    have ha0 : a ≠ 0 := by
      rintro rfl; exact rep_ne_zero (.inl k) (by rw [← ha, zero_smul])
    exact ⟨k, a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

/-- The tangent to the conic at the vertex direction `k` passes through `rep x`. -/
def onTangent (k : Fin 6) (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : Prop :=
  polar (2 : ZMod 5) (rep (.inl k)) (rep x) = 0

instance (k : Fin 6) (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : Decidable (onTangent k x) := by
  unfold onTangent; infer_instance

/-- An edge direction lies on exactly two tangents of the conic (an exterior point). -/
theorem edge_tangents :
    ∀ k : Fin 15, (Finset.univ.filter fun j => onTangent j (.inr (.inl k))).card = 2 := by
  decide +kernel

/-- A face direction lies on no tangent of the conic (an interior point). -/
theorem face_tangents :
    ∀ k : Fin 10, (Finset.univ.filter fun j => onTangent j (.inr (.inr k))).card = 0 := by
  decide +kernel

end Grothendieck.Folder70

namespace Grothendieck.Folder70

/-! ## The universal formulae (finding `70-universal-formulae-double-cosines`)

Pages 9–25 of the reading write a regular affine realisation by reflections of
`{p₁, …, pₙ}` in its vertex frame `(s₀, …, s_{n+1})`: in barycentric coordinates,
`σᵢ = id + ℓᵢ ⊗ (s_{i+1} − sᵢ)` with `ℓᵢ = tᵢ − tᵢ₊₁ + (1 + αᵢ)(tᵢ₊₂ + ⋯ + t_{n+1})`
(pages 23–25), and page 67 states, for `n = 2` and without proof,
« `ρ_s^p = id ⇔ F_p(α) = 0` ». Here `usig n α i` is that `σᵢ`, acting linearly on
`ℕ → R` (homogeneous barycentric coordinates; `sum_usig`: the affine space `Σ tⱼ = 1`
is preserved), over any commutative ring and for every `n`.

* `usig_mul_self`, `usig_comm`: the relations of the string Coxeter group,
  `σᵢ² = 1` and `σᵢσⱼ = σⱼσᵢ` for `j ≥ i + 2`, whatever the `αᵢ` (page 19);
  `usig_sv_self`, `usig_sv_succ`, `usig_sv_of_lt`, `usig_sv_of_le`: the table of page 25.
* `rho_apply`, `rho_cubic`: `σₖσₖ₊₁ − 1` has its image in the plane of
  `sₖ₊₁ − sₖ, sₖ₊₂ − sₖ₊₁`, and `(t − 1)(t² − αₖt + 1)` kills `σₖσₖ₊₁`.
* `orderOf_rho_eq_three`, `orderOf_rho_eq_four`, `orderOf_rho_eq_five`: over every
  nonzero commutative ring, `σₖσₖ₊₁` has order exactly `3`, `4`, `5` iff `αₖ = −1`,
  `αₖ = 0`, `αₖ² + αₖ − 1 = 0` — the minimal polynomials of `2cos(2π/p)` for the
  values of `p` that occur in the finite regular polytopes. No field, no `p` invertible.
* `usig_emb`, `ico_orderOf`: the generators of pages 74–75 above are the case
  `n = 2`, `(α₀, α₁) = (−1, α)`; tetrahedron `(−1, −1)`, cube `(0, −1)`, octahedron
  `(−1, 0)` and dodecahedron `(α, −1)` are the other Platonic cases of the same theorems.

Not formalised: the criterion for general `p` (it needs the minimal polynomial of
`2cos(2π/p)`), the passage from the definition of a regular realisation to the normal
form (pages 7–18). -/

section Universal

variable {R : Type*} [CommRing R] (n : ℕ) (α : ℕ → R)

/-- The vertex `s_j` of the frame, in barycentric coordinates `(t₀, …, t_{n+1})`. -/
def sv (j : ℕ) : ℕ → R := Pi.single j 1

/-- The affine form `ℓᵢ = tᵢ − tᵢ₊₁ + (1 + αᵢ)(tᵢ₊₂ + ⋯ + t_{n+1})` of page 23. -/
def ell (i : ℕ) : (ℕ → R) →ₗ[R] R :=
  LinearMap.proj (R := R) (φ := fun _ : ℕ => R) i - LinearMap.proj (i + 1) +
    (1 + α i) • ∑ j ∈ Finset.Ico (i + 2) (n + 2), LinearMap.proj j

/-- The edge vector `s_{i+1} − sᵢ`. -/
def wv (i : ℕ) : ℕ → R := sv (i + 1) - sv i

/-- The universal reflection `σᵢ = id + ℓᵢ ⊗ (s_{i+1} − sᵢ)` of pages 23–25. -/
def usig (i : ℕ) : Module.End R (ℕ → R) := 1 + (ell n α i).smulRight (wv i)

variable {n α}

theorem ell_apply (i : ℕ) (x : ℕ → R) :
    ell n α i x = x i - x (i + 1) + (1 + α i) * ∑ j ∈ Finset.Ico (i + 2) (n + 2), x j := by
  simp [ell]

theorem usig_apply (i : ℕ) (x : ℕ → R) :
    usig n α i x = x + ell n α i x • wv i := by
  simp [usig]

theorem ell_sv (i j : ℕ) : ell n α i (sv j) =
    (if i = j then 1 else 0) - (if i + 1 = j then 1 else 0) +
      (1 + α i) * (if i + 2 ≤ j ∧ j < n + 2 then 1 else 0) := by
  simp [ell_apply, sv, Pi.single_apply]

theorem ell_wv_self (i : ℕ) : ell n α i (wv i) = -2 := by
  simp only [wv, map_sub, ell_sv]; simp; ring

theorem ell_wv_of_le {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n) : ell n α i (wv j) = 0 := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem ell_wv_of_lt {i j : ℕ} (hij : i + 1 < j) : ell n α j (wv i) = 0 := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem usig_wv_self (i : ℕ) : usig n α i (wv i) = -wv i := by
  rw [usig_apply, ell_wv_self]; module

/-- `σᵢ² = 1`, whatever the `αⱼ` (page 19). -/
theorem usig_mul_self (i : ℕ) : usig n α i * usig n α i = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.one_apply, usig_apply (x := x), map_add, map_smul,
    usig_wv_self, usig_apply]
  module

/-- `σᵢ σⱼ = σⱼ σᵢ` for `j ≥ i + 2`, whatever the `αₖ` (page 19). -/
theorem usig_comm {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n) :
    usig n α i * usig n α j = usig n α j * usig n α i := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, usig_apply, map_add, map_smul,
    ell_wv_of_le hij hj, ell_wv_of_lt (show i + 1 < j by omega)]
  module

/-- `σᵢ` preserves `t₀ + ⋯ + t_{n+1}`: it acts on the affine space `Σ tⱼ = 1`. -/
theorem sum_usig (i : ℕ) (hi : i ≤ n) (x : ℕ → R) :
    ∑ j ∈ Finset.range (n + 2), usig n α i x j = ∑ j ∈ Finset.range (n + 2), x j := by
  simp only [usig_apply, wv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, sv, Pi.single_apply,
    smul_eq_mul, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_range, show i + 1 < n + 2 by omega,
    show i < n + 2 by omega]

/-- The table of page 25: `σᵢ sⱼ = sⱼ` for `j < i`. -/
theorem usig_sv_of_lt {i j : ℕ} (h : j < i) : usig n α i (sv j) = sv j := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-- `σᵢ sᵢ = sᵢ₊₁`. -/
theorem usig_sv_self (i : ℕ) : usig n α i (sv i) = sv (i + 1) := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-- `σᵢ sᵢ₊₁ = sᵢ`. -/
theorem usig_sv_succ (i : ℕ) : usig n α i (sv (i + 1)) = sv i := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-- `σᵢ sⱼ = −(1 + αᵢ) sᵢ + (1 + αᵢ) sᵢ₊₁ + sⱼ` for `i + 2 ≤ j ≤ n + 1` (page 25). -/
theorem usig_sv_of_le {i j : ℕ} (h1 : i + 2 ≤ j) (h2 : j ≤ n + 1) :
    usig n α i (sv j) = sv j + (1 + α i) • wv i := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-! ### The rotations `σₖ σₖ₊₁` -/

/-- The rotation `σₖ σₖ₊₁` of the polygon in `f_{k+2}`. -/
def rho (k : ℕ) : Module.End R (ℕ → R) := usig n α k * usig n α (k + 1)

theorem ell_succ_wv (k : ℕ) : ell n α (k + 1) (wv k) = 1 := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem ell_wv_succ {k : ℕ} (hk : k + 1 ≤ n) : ell n α k (wv (k + 1)) = 2 + α k := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem rho_wv {k : ℕ} (hk : k + 1 ≤ n) :
    rho (n := n) (α := α) k (wv k) = (1 + α k) • wv k + wv (k + 1) := by
  rw [rho, Module.End.mul_apply, usig_apply (i := k + 1), ell_succ_wv, one_smul, map_add,
    usig_wv_self, usig_apply, ell_wv_succ hk]
  module

theorem rho_wv_succ {k : ℕ} (hk : k + 1 ≤ n) :
    rho (n := n) (α := α) k (wv (k + 1)) = -((2 + α k) • wv k) - wv (k + 1) := by
  rw [rho, Module.End.mul_apply, usig_wv_self, map_neg, usig_apply, ell_wv_succ hk]
  module

/-- `σₖ σₖ₊₁ − 1` takes its values in the plane of `sₖ₊₁ − sₖ` and `sₖ₊₂ − sₖ₊₁`. -/
theorem rho_apply (k : ℕ) (x : ℕ → R) :
    rho (n := n) (α := α) k x =
      x + ell n α k (usig n α (k + 1) x) • wv k + ell n α (k + 1) x • wv (k + 1) := by
  rw [rho, Module.End.mul_apply, usig_apply (i := k), usig_apply (i := k + 1)]
  module

/-- `f^m x = x + Σ_{j<m} f^j (f x − x)`. -/
theorem pow_apply_eq (f : Module.End R (ℕ → R)) (m : ℕ) (x : ℕ → R) :
    (f ^ m) x = x + ∑ j ∈ Finset.range m, (f ^ j) (f x - x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, show f x = x + (f x - x) by abel, map_add, ih,
      Finset.sum_range_succ]
    abel_nf

/-- A vector of the plane of `sₖ₊₁ − sₖ` and `sₖ₊₂ − sₖ₊₁`. -/
def pl (k : ℕ) (a b : R) : ℕ → R := a • wv k + b • wv (k + 1)

theorem rho_pl {k : ℕ} (hk : k + 1 ≤ n) (a b : R) :
    rho (n := n) (α := α) k (pl k a b) = pl k ((1 + α k) * a - (2 + α k) * b) (a - b) := by
  simp only [pl, map_add, map_smul, rho_wv hk, rho_wv_succ hk]
  module

theorem pl_add (k : ℕ) (a b c d : R) : pl k a b + pl k c d = pl k (a + c) (b + d) := by
  simp only [pl]; module

theorem pl_eq_zero {k : ℕ} {a b : R} (ha : a = 0) (hb : b = 0) : pl k a b = 0 := by
  simp [pl, ha, hb]

theorem rho_pow_eq_one {k : ℕ} (m : ℕ)
    (h : ∀ a b : R, ∑ j ∈ Finset.range m, (rho (n := n) (α := α) k ^ j) (pl k a b) = 0) :
    rho (n := n) (α := α) k ^ m = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [pow_apply_eq, Module.End.one_apply, show rho k x - x = pl k _ _ by
    rw [rho_apply, pl]; abel, h, add_zero]

/-- A vector of the plane `⟨sₖ, sₖ₊₁, sₖ₊₂⟩`. -/
def tri (k : ℕ) (a b c : R) : ℕ → R := a • sv k + b • sv (k + 1) + c • sv (k + 2)

theorem rho_tri {k : ℕ} (hk : k + 1 ≤ n) (a b c : R) :
    rho (n := n) (α := α) k (tri k a b c) =
      tri k (c - (1 + α k) * b) (a + (1 + α k) * b) b := by
  have h0 : rho (n := n) (α := α) k (sv k) = sv (k + 1) := by
    rw [rho, Module.End.mul_apply, usig_sv_of_lt (by omega), usig_sv_self]
  have h1 : rho (n := n) (α := α) k (sv (k + 1)) = sv (k + 2) + (1 + α k) • wv k := by
    rw [rho, Module.End.mul_apply, usig_sv_self, usig_sv_of_le (by omega) (by omega)]
  have h2 : rho (n := n) (α := α) k (sv (k + 2)) = sv k := by
    rw [rho, Module.End.mul_apply, usig_sv_succ, usig_sv_succ]
  simp only [tri, map_add, map_smul, h0, h1, h2, wv]
  module

theorem tri_apply (k : ℕ) (a b c : R) :
    tri k a b c k = a ∧ tri k a b c (k + 1) = b ∧ tri k a b c (k + 2) = c := by
  simp [tri, sv]

/-- `σₖ σₖ₊₁` on `⟨sₖ, sₖ₊₁, sₖ₊₂⟩`, in coordinates. -/
def step (α : ℕ → R) (k : ℕ) (t : R × R × R) : R × R × R :=
  (t.2.2 - (1 + α k) * t.2.1, t.1 + (1 + α k) * t.2.1, t.2.1)

theorem rho_pow_tri {k : ℕ} (hk : k + 1 ≤ n) (m : ℕ) (t : R × R × R) :
    (rho (n := n) (α := α) k ^ m) (tri k t.1 t.2.1 t.2.2) =
      tri k ((step α k)^[m] t).1 ((step α k)^[m] t).2.1 ((step α k)^[m] t).2.2 := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, rho_tri hk, Function.iterate_succ_apply]
    exact ih (step α k t)

/-- If `(σₖ σₖ₊₁)^m = 1`, the orbit of `sₖ` closes after `m` steps. -/
theorem step_pow_of_rho_pow {k : ℕ} (hk : k + 1 ≤ n) {m : ℕ}
    (h : rho (n := n) (α := α) k ^ m = 1) : (step α k)^[m] (1, 0, 0) = (1, 0, 0) := by
  have e := rho_pow_tri (α := α) hk m (1, 0, 0)
  rw [h, Module.End.one_apply] at e
  have h1 := tri_apply k (1 : R) 0 0
  have h2 := tri_apply k ((step α k)^[m] (1, 0, 0)).1 ((step α k)^[m] (1, 0, 0)).2.1
    ((step α k)^[m] (1, 0, 0)).2.2
  rw [← e] at h2
  exact Prod.ext (h2.1.symm.trans h1.1) (Prod.ext (h2.2.1.symm.trans h1.2.1)
    (h2.2.2.symm.trans h1.2.2))

/-- If the orbit of `sₖ` does not close after `m` steps, `(σₖ σₖ₊₁)^m ≠ 1`. -/
theorem rho_pow_ne_one {k : ℕ} (hk : k + 1 ≤ n) {m : ℕ}
    (h : (step α k)^[m] (1, 0, 0) ≠ (1, 0, 0)) : rho (n := n) (α := α) k ^ m ≠ 1 :=
  fun h' => h (step_pow_of_rho_pow hk h')

/-- `(t − 1)(t² − αₖ t + 1)` kills `σₖ σₖ₊₁`, for every `n` and every ring. -/
theorem rho_cubic {k : ℕ} (hk : k + 1 ≤ n) (x : ℕ → R) :
    (rho (n := n) (α := α) k ^ 3) x - (1 + α k) • (rho (n := n) (α := α) k ^ 2) x +
      (1 + α k) • (rho (n := n) (α := α) k ^ 1) x - x = 0 := by
  have hy : rho (n := n) (α := α) k x - x =
      pl k (ell n α k (usig n α (k + 1) x)) (ell n α (k + 1) x) := by
    rw [rho_apply, pl]; abel
  rw [pow_apply_eq _ 3, pow_apply_eq _ 2, pow_apply_eq _ 1, hy]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
    Module.End.mul_apply, Module.End.one_apply, rho_pl hk, zero_add]
  simp only [pl]
  module

theorem orderOf_rho_eq_three [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) :
    orderOf (rho (n := n) (α := α) k) = 3 ↔ α k = -1 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rintro ⟨h, -⟩
    have e := step_pow_of_rho_pow hk h
    simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply,
      Prod.mk.injEq] at e
    linear_combination e.2.2
  · intro h
    refine ⟨rho_pow_eq_one 3 fun a b => ?_, fun m hm h0 => rho_pow_ne_one hk ?_⟩
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
        Module.End.mul_apply, Module.End.one_apply, rho_pl hk, pl_add, zero_add]
      apply pl_eq_zero
      · linear_combination ((1 + α k) * a - (2 + α k) * b) * h
      · linear_combination (a - b) * h
    · obtain rfl | rfl : m = 1 ∨ m = 2 := by omega
      all_goals simp [step, Function.iterate_succ_apply', Prod.ext_iff]

theorem orderOf_rho_eq_four [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) :
    orderOf (rho (n := n) (α := α) k) = 4 ↔ α k = 0 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rintro ⟨h, -⟩
    have e := step_pow_of_rho_pow hk h
    simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply,
      Prod.mk.injEq] at e
    linear_combination α k * e.2.2 - e.2.1
  · intro h
    refine ⟨rho_pow_eq_one 4 fun a b => ?_, fun m hm h0 => rho_pow_ne_one hk ?_⟩
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
        Module.End.mul_apply, Module.End.one_apply, rho_pl hk, pl_add, zero_add]
      apply pl_eq_zero <;> rw [h] <;> ring
    · obtain rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 := by omega
      all_goals
        simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply, ne_eq,
          Prod.mk.injEq]
        intro e
        apply one_ne_zero (α := R)
      · linear_combination -e.1
      · linear_combination e.2.2
      · linear_combination e.2.2 - h

theorem orderOf_rho_eq_five [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) :
    orderOf (rho (n := n) (α := α) k) = 5 ↔ α k ^ 2 + α k - 1 = 0 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rintro ⟨h, -⟩
    have e := step_pow_of_rho_pow hk h
    simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply,
      Prod.mk.injEq] at e
    linear_combination α k * e.2.2 - e.2.1
  · intro h
    refine ⟨rho_pow_eq_one 5 fun a b => ?_, fun m hm h0 => rho_pow_ne_one hk ?_⟩
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
        Module.End.mul_apply, Module.End.one_apply, rho_pl hk, pl_add, zero_add]
      apply pl_eq_zero
      · linear_combination (α k * ((1 + α k) * a - (2 + α k) * b) - a) * h
      · linear_combination (α k * (a - b) - b) * h
    · obtain rfl | rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
      all_goals
        simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply, ne_eq,
          Prod.mk.injEq]
        intro e
        apply one_ne_zero (α := R)
      · linear_combination -e.1
      · linear_combination e.2.2
      · linear_combination e.2.1 - h
      · linear_combination e.2.2 - h

/-! ### The icosahedron of pages 74–75 is the case `(α₀, α₁) = (−1, α)` -/

/-- A point `(x, y, z)` of page 74 in barycentric coordinates `(1 − x − y − z, x, y, z)`. -/
def emb (p : R × R × R) : ℕ → R := fun j =>
  if j = 0 then 1 - p.1 - p.2.1 - p.2.2 else if j = 1 then p.1 else if j = 2 then p.2.1
  else if j = 3 then p.2.2 else 0

/-- The parameters of the icosahedron `{3, 5}`. -/
def icoα (a : R) : ℕ → R := fun i => if i = 0 then -1 else a

theorem usig_emb (a : R) (p : R × R × R) :
    usig 2 (icoα a) 0 (emb p) = emb (sigma0 p) ∧
      usig 2 (icoα a) 1 (emb p) = emb (sigma1 a p) ∧
      usig 2 (icoα a) 2 (emb p) = emb (sigma2 p) := by
  have e0 : Finset.Ico 2 4 = {2, 3} := by decide
  have e1 : Finset.Ico 3 4 = {3} := by decide
  refine ⟨funext fun j => ?_, funext fun j => ?_, funext fun j => ?_⟩ <;>
    rcases j with _ | _ | _ | _ | j <;>
    simp [usig_apply, ell_apply, wv, sv, emb, icoα, sigma0, sigma1, sigma2, e0, e1] <;> ring

/-- The icosahedron's rotations have orders `3` and `5` exactly, over every nonzero ring
with `α² + α − 1 = 0`. -/
theorem ico_orderOf [Nontrivial R] {a : R} (h : a ^ 2 + a - 1 = 0) :
    orderOf (rho (n := 2) (α := icoα a) 0) = 3 ∧ orderOf (rho (n := 2) (α := icoα a) 1) = 5 :=
  ⟨(orderOf_rho_eq_three (by norm_num)).2 (by simp [icoα]),
    (orderOf_rho_eq_five (by norm_num)).2 (by simpa [icoα] using h)⟩

end Universal
end Grothendieck.Folder70

namespace Grothendieck.Folder70

/-! ## The quadric of the icosahedron (pages 101, 102 and 106)

Finding `70-icosahedron-integral-faithful`, the quadric part. Over any commutative ring with
`α² + α − 1 = 0`: `quadric_unique` (a quadratic function vanishing at nine of the vertices
is a multiple of `q`, which is invariant, `q_sigma`, and vanishes at all twelve, `q_vert`),
`halfDisc_q` (`δ'(q₀) = 1`), `det_qMat4` (the homogenised quadric has discriminant
`−α − 3`), `norm_disc` (of norm `5`), `isUnit_det_qMat4_iff` and `qHom_smooth` (smooth
wherever `5` is invertible). In characteristic 5: `qMat4_ker_char_five` (the singular locus
is the centre `(1, 2, 2)`, a cone) and, over a field, `qHom_singular_iff`.
-/

section Quadric

open Matrix

variable {R : Type*} [CommRing R] {α : R}

/-- A quadratic function `a x² + b y² + c z² + u yz + v zx + w xy + d x + e y + f z + k` on
`R³`, by its ten coefficients. -/
@[ext] structure QuadFn (R : Type*) where
  (a b c u v w d e f k : R)

/-- The value of a quadratic function at a point. -/
def QuadFn.eval (Q : QuadFn R) (p : R × R × R) : R :=
  Q.a * p.1 ^ 2 + Q.b * p.2.1 ^ 2 + Q.c * p.2.2 ^ 2 + Q.u * (p.2.1 * p.2.2)
    + Q.v * (p.2.2 * p.1) + Q.w * (p.1 * p.2.1) + Q.d * p.1 + Q.e * p.2.1 + Q.f * p.2.2 + Q.k

/-- A scalar multiple of a quadratic function. -/
def QuadFn.smul (r : R) (Q : QuadFn R) : QuadFn R :=
  ⟨r * Q.a, r * Q.b, r * Q.c, r * Q.u, r * Q.v, r * Q.w, r * Q.d, r * Q.e, r * Q.f, r * Q.k⟩

variable (α) in
/-- The coefficients of the invariant function `q` of pages 95 and 101. -/
def qFn : QuadFn R := ⟨1, 1, 1, -α, 1, 1, -1, -1, -1, 0⟩

theorem eval_qFn (p : R × R × R) : (qFn α).eval p = q α p := by
  simp only [QuadFn.eval, qFn, q]; ring

/-- `q` is invariant under the three generators (page 95), for any `α`. -/
theorem q_sigma (p : R × R × R) :
    q α (sigma0 p) = q α p ∧ q α (sigma1 α p) = q α p ∧ q α (sigma2 p) = q α p := by
  obtain ⟨x, y, z⟩ := p
  refine ⟨?_, ?_, ?_⟩ <;> simp only [q, sigma0, sigma1, sigma2] <;> ring

/-- **Page 101: uniqueness of the quadric.** Over any commutative ring with `α² + α − 1 = 0`,
a quadratic function vanishing at the nine vertices `s₀, s₁, s₂, s₃, s'₃, s''₃, ι s₀, ι s₁,
ι s₂` is `a · q`, `a` its coefficient of `x²`: the `9 × 9` minor of the linear system is
`13α + 21`, a unit of `ℤ[α]` (of inverse `13α − 8`). -/
theorem quadric_unique (h : α ^ 2 + α - 1 = 0) (Q : QuadFn R)
    (hQ : ∀ i : Fin 12, i.val < 9 → Q.eval (vert α i) = 0) : Q = QuadFn.smul Q.a (qFn α) := by
  have h0 := hQ 0 (by decide); have h1 := hQ 1 (by decide); have h2 := hQ 2 (by decide)
  have h3 := hQ 3 (by decide); have h4 := hQ 4 (by decide); have h5 := hQ 5 (by decide)
  have h6 := hQ 6 (by decide); have h7 := hQ 7 (by decide); have h8 := hQ 8 (by decide)
  obtain ⟨a, b, c, u, v, w, d, e, f, k⟩ := Q
  simp only [QuadFn.eval, vert, iota, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp only [QuadFn.smul, qFn, QuadFn.mk.injEq]
  refine ⟨by ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-1) * h1 + (1) * h2 + (1) * h3 + (-1) * h4 + (α) * h7 + (-α) * h8 + (-a - b - u + v + w) * h
  · linear_combination (-α) * h0 + (1) * h2 + (1 - α) * h3 + (-1) * h5 + (α) * h6 + (α - 1) * h7 + (-2*a*α - 3*a - 2*b*α - 4*b - 2*c*α - 5*c + 2*d - 2*e - 2*f - 2*u*α - 5*u + 2*v*α + 4*v + 2*w*α + 4*w) * h
  · linear_combination (1) * h0 + (α) * h1 + (-α - 1) * h2 + (-2*α) * h3 + (α) * h4 + (α) * h5 + (α - 1) * h7 + (1 - α) * h8 + (-a*α - 3*a - 2*b*α - 4*b + d - 2*e - 3*u + 2*v + w*α + 3*w) * h
  · linear_combination (-α) * h0 + (α) * h1 + (1) * h4 + (-1) * h5 + (1) * h6 + (-1) * h7 + (-a + w) * h
  · linear_combination (1) * h0 + (-1) * h1 + (-1) * h4 + (1) * h5 + (-α) * h6 + (α) * h7 + (-a + v) * h
  · linear_combination (-1) * h0 + (1) * h1
  · linear_combination (-1) * h0 + (1) * h1 + (-1) * h3 + (1) * h4 + (-α) * h7 + (α) * h8 + (a + b + u - v - w) * h
  · linear_combination (α - 1) * h0 + (-1) * h2 + (α) * h3 + (1) * h5 + (-α) * h6 + (1 - α) * h7 + (2*a*α + 3*a + 2*b*α + 4*b + 2*c*α + 5*c - 2*d + 2*e + 2*f + 2*u*α + 5*u - 2*v*α - 4*v - 2*w*α - 4*w) * h
  · linear_combination h0

/-- The half-discriminant `δ'` of the ternary form `a x² + b y² + c z² + u yz + v zx + w xy`:
half the determinant of its polar matrix, a polynomial in the coefficients. -/
def QuadFn.halfDisc (Q : QuadFn R) : R :=
  4 * Q.a * Q.b * Q.c + Q.u * Q.v * Q.w - Q.a * Q.u ^ 2 - Q.b * Q.v ^ 2 - Q.c * Q.w ^ 2

/-- The polar matrix of the quadratic part. -/
def QuadFn.polarMat (Q : QuadFn R) : Matrix (Fin 3) (Fin 3) R :=
  !![2 * Q.a, Q.w, Q.v; Q.w, 2 * Q.b, Q.u; Q.v, Q.u, 2 * Q.c]

theorem QuadFn.det_polarMat (Q : QuadFn R) : Q.polarMat.det = 2 * Q.halfDisc := by
  rw [QuadFn.polarMat, Matrix.det_fin_three]; simp [QuadFn.halfDisc]; ring

/-- **Pages 101–102: `δ'(q₀) = 1`** (« merveille ! »), over any commutative ring with
`α² + α − 1 = 0`, characteristic 2 included; the polar matrix
`[[2, 1, 1], [1, 2, −α], [1, −α, 2]]` has determinant `2`. -/
theorem halfDisc_q (h : α ^ 2 + α - 1 = 0) :
    (qFn α).halfDisc = 1 ∧ (qFn α).polarMat.det = 2 := by
  have e : (qFn α).halfDisc = 1 := by
    simp only [QuadFn.halfDisc, qFn]; linear_combination (-1 : R) * h
  exact ⟨e, by rw [QuadFn.det_polarMat, e, mul_one]⟩

variable (α) in
/-- The matrix (22) of page 102: `q` homogenised by a fourth variable `t`,
`Q(x, y, z, t) = q₀(x, y, z) − (x + y + z) t`, polar matrix. Its rows are the partial
derivatives of `Q`. -/
def qMat4 : Matrix (Fin 4) (Fin 4) R :=
  !![2, 1, 1, -1; 1, 2, -α, -1; 1, -α, 2, -1; -1, -1, -1, 0]

variable (α) in
/-- The homogenised quadric `Q(x, y, z, t) = q₀(x, y, z) − (x + y + z) t`. -/
def qHom (v : Fin 4 → R) : R := q0 α (v 0, v 1, v 2) - (v 0 + v 1 + v 2) * v 3

theorem qMat4_mulVec (v : Fin 4 → R) : qMat4 α *ᵥ v =
    ![2 * v 0 + v 1 + v 2 - v 3, v 0 + 2 * v 1 - α * v 2 - v 3,
      v 0 - α * v 1 + 2 * v 2 - v 3, -(v 0 + v 1 + v 2)] := by
  ext i; fin_cases i <;> simp [qMat4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- Euler's identity: `v · (M v) = 2 Q(v)`. -/
theorem dot_qMat4 (v : Fin 4 → R) : v ⬝ᵥ (qMat4 α *ᵥ v) = 2 * qHom α v := by
  rw [qMat4_mulVec]; simp [dotProduct, Fin.sum_univ_four, qHom, q0]; ring

/-- **Page 102: the discriminant is `−α − 3`** (« sauf erreur de calcul » — there is none). -/
theorem det_qMat4 (h : α ^ 2 + α - 1 = 0) : (qMat4 α).det = -α - 3 := by
  rw [qMat4, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  linear_combination h

/-- Its norm is `5`: `(−α − 3)(−α' − 3) = 5` with `α' = −1 − α`. -/
theorem norm_disc (h : α ^ 2 + α - 1 = 0) : (-α - 3) * (-(-1 - α) - 3) = 5 := by
  linear_combination (-1 : R) * h

/-- The discriminant is a unit exactly when `5` is: `(−α − 3)(α − 2) = 5` and
`(−α − 3)² = 5 (α + 2)`. -/
theorem isUnit_det_qMat4_iff (h : α ^ 2 + α - 1 = 0) :
    IsUnit (qMat4 α).det ↔ IsUnit (5 : R) := by
  rw [det_qMat4 h]
  refine ⟨fun hu => isUnit_of_dvd_unit ⟨α + 2, by linear_combination h⟩ (hu.pow 2),
    fun hu => isUnit_of_mul_isUnit_left (y := α - 2) ?_⟩
  convert hu using 1; linear_combination (-1 : R) * h

/-- **Page 102: the quadric is smooth when `5` is invertible.** Over any commutative ring with
`α² + α − 1 = 0` in which `5` is a unit, the only common zero of the four partial derivatives
of `Q` (the rows of `qMat4`) is `0`; characteristic 2 included. -/
theorem qHom_smooth (h : α ^ 2 + α - 1 = 0) (h5 : IsUnit (5 : R)) {v : Fin 4 → R}
    (hv : qMat4 α *ᵥ v = 0) : v = 0 :=
  Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
    ((isUnit_det_qMat4_iff h).2 h5).mem_nonZeroDivisors hv

/-- **Pages 102 and 106: in characteristic 5 the quadric is a cone.** If `5 = 0` and `α = 2`
(the only root over a field of characteristic 5), the singular points are the multiples of
`(1, 2, 2, 1)`, the centre `o = (1, 2, 2)` of the icosahedron, which lies on the quadric. -/
theorem qMat4_ker_char_five (h5 : (5 : R) = 0) (hα : α = 2) (v : Fin 4 → R) :
    qMat4 α *ᵥ v = 0 ↔ v = v 3 • ![1, 2, 2, 1] := by
  subst hα
  rw [qMat4_mulVec]
  constructor
  · intro hv
    have r0 := congrFun hv 0; have r1 := congrFun hv 1
    have r2 := congrFun hv 2; have r3 := congrFun hv 3
    simp at r0 r1 r2 r3
    ext i; fin_cases i <;> simp
    · linear_combination (-2) * r0 - r1 - r2 - 2 * r3 + (v 0 - v 3) * h5
    · linear_combination (-2) * r0 - r1 + (v 0 + v 1 - v 3) * h5
    · linear_combination (-2) * r0 - r2 + (v 0 + v 2 - v 3) * h5
  · intro hv
    rw [hv]; ext i; fin_cases i <;> simp <;>
      first | linear_combination (v 3) * h5 | linear_combination (-v 3) * h5

/-- With `α = 2`, the point `(1, 2, 2, 1)` lies on the quadric, in any ring. -/
theorem qHom_centre : qHom 2 ![(1 : R), 2, 2, 1] = 0 := by
  norm_num [qHom, q0]

/-- **Pages 102 and 106, over a field.** The projective quadric `Q = 0` has a singular point
if and only if the characteristic is `5`. -/
theorem qHom_singular_iff {K : Type*} [Field K] {α : K} (h : α ^ 2 + α - 1 = 0) :
    (∃ v : Fin 4 → K, v ≠ 0 ∧ qHom α v = 0 ∧ qMat4 α *ᵥ v = 0) ↔ (5 : K) = 0 := by
  constructor
  · rintro ⟨v, hv0, -, hv⟩
    by_contra h5
    exact hv0 (qHom_smooth h (Ne.isUnit h5) hv)
  · intro h5
    have hα : α = 2 :=
      sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (by linear_combination h + (1 - α) * h5 :
        (α - 2) ^ 2 = 0))
    subst hα
    refine ⟨![1, 2, 2, 1], fun h0 => one_ne_zero (congrFun h0 0), qHom_centre,
      (qMat4_ker_char_five h5 rfl _).2 (by simp)⟩

end Quadric

end Grothendieck.Folder70

namespace Grothendieck.Folder70

/-! ## The order of the group, and the criterion for every `p`

Finding `70-icosahedron-integral-faithful`, the order of the group: `card_icoPermGroup`
(the permutations of the twelve vertices induced by `σ₀, σ₁, σ₂` form a group of order
`120`, by a kernel-checked table of 120 words closed under left multiplication by the
generators) and `card_icoGroup` (over every nonzero commutative ring with `α² + α − 1 = 0`,
characteristics 2 and 5 included, the group of permutations of `R³` generated by
`σ₀, σ₁, σ₂` has order `120`: it acts faithfully on the vertices, since an affine map
fixing `s₀, s₁, s₂, s₃` is the identity).

Finding `70-universal-formulae-double-cosines`, the criterion for general `p`:
`rho_pow_eq_one_iff` (over any nonzero commutative ring, `(σₖσₖ₊₁)^m = 1` iff
`(t − 1)(t² − αₖt + 1) ∣ t^m − 1`), `recip_minpoly_cos` (`X^d Ψ_p(X + X⁻¹) = Φ_p` for the
minimal polynomial `Ψ_p` of `2cos(2π/p)`, `p ≥ 3`), and `orderOf_rho_eq_iff` (over a field
of characteristic `0`, `σₖσₖ₊₁` has order exactly `p ≥ 3` iff `Ψ_p(αₖ) = 0`).
-/

section Order

/-- The permutation of the vertices induced by `σₖ`, an involution. -/
def genPerm (k : Fin 3) : Equiv.Perm (Fin 12) :=
  ⟨permOf k, permOf k, by revert k; unfold Function.LeftInverse; decide,
    by revert k; unfold Function.RightInverse Function.LeftInverse; decide⟩

/-- The group of vertex permutations generated by `σ₀, σ₁, σ₂`. -/
abbrev icoPermGroup : Subgroup (Equiv.Perm (Fin 12)) := Subgroup.closure (Set.range genPerm)

def word120 : Fin 120 → List (Fin 3) :=
  ![[], [0], [1], [2], [1, 0], [2, 0], [0, 1], [2, 1], [1, 2], [0, 1, 0], [2, 1, 0], [1, 2, 0],
    [2, 0, 1], [1, 2, 1], [0, 1, 2], [2, 1, 2], [2, 0, 1, 0], [1, 2, 1, 0], [0, 1, 2, 0],
    [2, 1, 2, 0], [1, 2, 0, 1], [0, 1, 2, 1], [2, 1, 2, 1], [2, 0, 1, 2], [1, 2, 1, 2],
    [1, 2, 0, 1, 0], [0, 1, 2, 1, 0], [2, 1, 2, 1, 0], [2, 0, 1, 2, 0], [1, 2, 1, 2, 0],
    [0, 1, 2, 0, 1], [2, 1, 2, 0, 1], [2, 0, 1, 2, 1], [1, 2, 1, 2, 1], [1, 2, 0, 1, 2],
    [0, 1, 2, 1, 2], [0, 1, 2, 0, 1, 0], [2, 1, 2, 0, 1, 0], [2, 0, 1, 2, 1, 0], [1, 2, 1, 2, 1, 0],
    [1, 2, 0, 1, 2, 0], [0, 1, 2, 1, 2, 0], [2, 0, 1, 2, 0, 1], [1, 2, 1, 2, 0, 1],
    [1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 1], [0, 1, 2, 0, 1, 2], [2, 1, 2, 0, 1, 2],
    [2, 0, 1, 2, 0, 1, 0], [1, 2, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 1, 2, 1, 0],
    [0, 1, 2, 0, 1, 2, 0], [2, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0, 1],
    [0, 1, 2, 0, 1, 2, 1], [2, 1, 2, 0, 1, 2, 1], [2, 0, 1, 2, 0, 1, 2], [1, 2, 1, 2, 0, 1, 2],
    [1, 2, 0, 1, 2, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1, 0], [0, 1, 2, 0, 1, 2, 1, 0],
    [2, 1, 2, 0, 1, 2, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 1, 2, 0, 1, 2, 0],
    [0, 1, 2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 1], [2, 0, 1, 2, 0, 1, 2, 1],
    [1, 2, 1, 2, 0, 1, 2, 1], [1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 2, 1, 2, 0, 1, 2],
    [0, 1, 2, 0, 1, 2, 0, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 0, 1, 2, 1, 0],
    [1, 2, 1, 2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0], [0, 1, 2, 1, 2, 0, 1, 2, 0],
    [2, 0, 1, 2, 0, 1, 2, 0, 1], [1, 2, 1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 1, 2, 0, 1, 2, 1],
    [0, 1, 2, 1, 2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 1, 2], [2, 1, 2, 0, 1, 2, 0, 1, 2],
    [2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
    [0, 1, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 0, 1, 2, 0, 1, 2, 1],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 1], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0],
    [0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
    [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1],
    [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2],
    [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1],
    [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0]]
def next120 : Fin 3 → Fin 120 → Fin 120 :=
  ![![1, 0, 6, 5, 9, 3, 2, 12, 14, 4, 16, 18, 7, 21, 8, 23, 10, 26, 11, 28, 30, 13, 32, 15, 35, 36,
      17, 38, 19, 41, 20, 42, 22, 45, 46, 24, 25, 48, 27, 51, 52, 29, 31, 55, 56, 33, 34, 58, 37,
      61, 62, 39, 40, 64, 66, 43, 44, 68, 47, 71, 72, 49, 50, 74, 53, 77, 54, 78, 57, 81, 82, 59,
      60, 84, 63, 87, 88, 65, 67, 91, 92, 69, 70, 94, 73, 96, 97, 75, 76, 99, 100, 79, 80, 102, 83,
      104, 85, 86, 106, 89, 90, 108, 93, 109, 95, 111, 98, 112, 101, 103, 115, 105, 107, 117, 116,
      110, 114, 113, 119, 118],
    ![2, 4, 0, 8, 1, 11, 9, 13, 3, 6, 17, 5, 20, 7, 18, 24, 25, 10, 14, 29, 12, 30, 33, 34, 15, 16,
      36, 39, 40, 19, 21, 43, 44, 22, 23, 46, 26, 49, 50, 27, 28, 52, 54, 31, 32, 56, 35, 59, 60,
      37, 38, 62, 41, 65, 42, 66, 45, 69, 70, 47, 48, 72, 51, 75, 76, 53, 55, 79, 80, 57, 58, 82,
      61, 85, 86, 63, 64, 88, 90, 67, 68, 92, 71, 93, 95, 73, 74, 97, 77, 98, 78, 100, 81, 83, 103,
      84, 104, 87, 89, 107, 91, 105, 109, 94, 96, 101, 112, 99, 114, 102, 113, 116, 106, 110, 108,
      118, 111, 119, 115, 117],
    ![3, 5, 7, 0, 10, 1, 12, 2, 15, 16, 4, 19, 6, 22, 23, 8, 9, 27, 28, 11, 31, 32, 13, 14, 33, 37,
      38, 17, 18, 39, 42, 20, 21, 24, 47, 45, 48, 25, 26, 29, 53, 51, 30, 49, 57, 35, 58, 34, 36,
      43, 63, 41, 64, 40, 67, 61, 68, 44, 46, 65, 73, 55, 74, 50, 52, 59, 78, 54, 56, 79, 83, 77,
      84, 60, 62, 85, 89, 71, 66, 69, 93, 91, 94, 70, 72, 75, 98, 96, 99, 76, 101, 81, 102, 80, 82,
      105, 87, 106, 86, 88, 108, 90, 92, 110, 111, 95, 97, 113, 100, 115, 103, 104, 117, 107, 118,
      109, 119, 112, 114, 116]]

/-- The element of word `word120 i`. -/
def elt120 (i : Fin 120) : Equiv.Perm (Fin 12) := ((word120 i).map genPerm).prod

theorem gen_mul_elt120 : ∀ k i, genPerm k * elt120 i = elt120 (next120 k i) := by
  decide +kernel

theorem elt120_injective : Function.Injective elt120 := by
  decide +kernel

theorem genPerm_inv (k : Fin 3) : (genPerm k)⁻¹ = genPerm k := by
  revert k; decide

/-- **The order 120 of the group** (pages 75 and 87, « si nous admettons que `G` est
d'ordre 120 »): the permutations of the twelve vertices generated by `σ₀, σ₁, σ₂` form a
group of order `120`. -/
theorem card_icoPermGroup : Nat.card icoPermGroup = 120 := by
  have hmem (i : Fin 120) : elt120 i ∈ icoPermGroup :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg; exact Subgroup.subset_closure ⟨k, rfl⟩
  rw [← Nat.card_fin 120]
  refine (Nat.card_eq_of_bijective (fun i => (⟨elt120 i, hmem i⟩ : icoPermGroup))
    ⟨fun i j h => elt120_injective (congrArg Subtype.val h), fun ⟨g, hg⟩ => ?_⟩).symm
  obtain ⟨i, hi⟩ : ∃ i, elt120 i = g := by
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, rfl⟩
    | mul_left x hx y _ ih =>
      obtain ⟨⟨k, rfl⟩, ⟨i, rfl⟩⟩ := And.intro hx ih
      exact ⟨next120 k i, (gen_mul_elt120 k i).symm⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨⟨k, rfl⟩, ⟨i, rfl⟩⟩ := And.intro hx ih
      exact ⟨next120 k i, by rw [genPerm_inv, gen_mul_elt120]⟩
  exact ⟨i, Subtype.ext hi⟩

variable {R : Type*} [CommRing R] {α : R}

theorem sigmaOf_sigmaOf (k : Fin 3) (p : R × R × R) : sigmaOf α k (sigmaOf α k p) = p := by
  fin_cases k <;> simp [sigmaOf, sigma0, sigma1, sigma2, Prod.ext_iff]; ring

variable (α) in
/-- `σₖ` as a permutation of `R³`. -/
def sigPerm (k : Fin 3) : Equiv.Perm (R × R × R) :=
  ⟨sigmaOf α k, sigmaOf α k, sigmaOf_sigmaOf k, sigmaOf_sigmaOf k⟩

/-- `g` is affine: determined by its values at `s₀ = 0, s₁, s₂, s₃`. -/
def IsAff (g : R × R × R → R × R × R) : Prop := ∀ p, g p = g 0 + p.1 • (g (1, 0, 0) - g 0) +
  p.2.1 • (g (0, 1, 0) - g 0) + p.2.2 • (g (0, 0, 1) - g 0)

theorem isAff_comp {f g : R × R × R → R × R × R} (hf : IsAff f) (hg : IsAff g) :
    IsAff (f ∘ g) := fun p => by
  simp only [Function.comp]
  rw [hf (g p), hf (g 0), hf (g (1, 0, 0)), hf (g (0, 1, 0)), hf (g (0, 0, 1)), hg p]
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  refine ⟨by ring, by ring, by ring⟩

theorem isAff_sigmaOf (k : Fin 3) : IsAff (sigmaOf α k) := fun p => by
  fin_cases k <;> simp [sigmaOf, sigma0, sigma1, sigma2, Prod.ext_iff] <;> (try constructor) <;>
    ring

/-- **The order 120 of the group** of the icosahedron (pages 75 and 87): over every nonzero
commutative ring with `α² + α − 1 = 0`, characteristics 2 and 5 included, the group of
permutations of `R³` generated by `σ₀, σ₁, σ₂` has order `120`; it acts faithfully on the
twelve vertices. -/
theorem card_icoGroup [Nontrivial R] (h : α ^ 2 + α - 1 = 0) :
    Nat.card (Subgroup.closure (Set.range (sigPerm α))) = 120 := by
  set f₁ := FreeGroup.lift (sigPerm α)
  set f₂ := FreeGroup.lift genPerm
  have key (x : FreeGroup (Fin 3)) :
      (∀ i, f₁ x (vert α i) = vert α (f₂ x i)) ∧ IsAff (f₁ x) := by
    induction x with
    | one => exact ⟨fun i => rfl, fun p => by simp⟩
    | of k => exact ⟨fun i => by simp [f₁, f₂, sigPerm, genPerm, sigmaOf_vert h],
        by simpa [f₁, sigPerm] using isAff_sigmaOf k⟩
    | inv_of k ih => simpa [f₁, f₂, sigPerm, genPerm, Equiv.Perm.inv_def] using ih
    | mul x y hx hy => exact ⟨fun i => by simp [hx.1, hy.1], by
      rw [map_mul, Equiv.Perm.coe_mul]; exact isAff_comp hx.2 hy.2⟩
  have hker : f₁.ker = f₂.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · refine fun h1 => Equiv.ext fun i => vert_injective_any h ?_
      rw [← (key x).1, h1]; rfl
    · refine fun h2 => Equiv.ext fun p => ?_
      have hv (i : Fin 12) : f₁ x (vert α i) = vert α i := by rw [(key x).1, h2]; rfl
      have h0 := hv 0; have h1 := hv 1; have h2 := hv 2; have h3 := hv 3
      simp only [vert, Matrix.cons_val] at h0 h1 h2 h3
      rw [(key x).2 p, show (0 : R × R × R) = (0, 0, 0) from rfl, h0, h1, h2, h3]
      simp
  rw [← FreeGroup.range_lift_eq_closure, ← card_icoPermGroup, icoPermGroup,
    ← FreeGroup.range_lift_eq_closure]
  exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange f₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange f₂))).toEquiv

end Order

section General

open Polynomial

variable {R : Type*} [CommRing R] {n : ℕ} {α : ℕ → R}

/-- The polynomial `(t − 1)(t² − a t + 1)` of `rho_cubic`. -/
noncomputable def chi (a : R) : R[X] := (X - 1) * (X ^ 2 - C a * X + 1)

theorem chi_monic (a : R) : (chi a).Monic := by
  unfold chi; monicity!

theorem aeval_rho_chi {k : ℕ} (hk : k + 1 ≤ n) :
    aeval (rho (n := n) (α := α) k) (chi (α k)) = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [show chi (α k) = X ^ 3 - C (1 + α k) * X ^ 2 + C (1 + α k) * X - 1 by
    simp only [chi, C_add, C_1]; ring]
  simpa [Algebra.algebraMap_eq_smul_one, add_smul] using rho_cubic (n := n) (α := α) hk x

theorem rho_sv {k : ℕ} (hk : k + 1 ≤ n) :
    rho (n := n) (α := α) k (sv k) = sv (k + 1) ∧
      rho (n := n) (α := α) k (sv (k + 1)) = sv (k + 2) + (1 + α k) • wv k :=
  ⟨by rw [rho, Module.End.mul_apply, usig_sv_of_lt (by omega), usig_sv_self],
    by rw [rho, Module.End.mul_apply, usig_sv_self, usig_sv_of_le (by omega) (by omega)]⟩

theorem natDegree_chi [Nontrivial R] (a : R) : (chi a).natDegree = 3 := by
  unfold chi; compute_degree!

/-- `(σₖσₖ₊₁)^m = 1` iff `(t − 1)(t² − αₖ t + 1)` divides `t^m − 1`, over any nonzero
commutative ring: `sₖ` is a cyclic vector. -/
theorem rho_pow_eq_one_iff [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) (m : ℕ) :
    rho (n := n) (α := α) k ^ m = 1 ↔ chi (α k) ∣ X ^ m - 1 := by
  constructor
  · intro h
    rw [← modByMonic_eq_zero_iff_dvd (chi_monic _)]
    have hr : aeval (rho (n := n) (α := α) k) ((X ^ m - 1 : R[X]) %ₘ chi (α k)) = 0 := by
      rw [aeval_modByMonic_eq_self_of_root (p := X ^ m - 1) (aeval_rho_chi (α := α) hk)]
      rw [map_sub, map_one, map_pow, aeval_X, h, sub_self]
    have hdeg : ((X ^ m - 1 : R[X]) %ₘ chi (α k)).natDegree < 3 :=
      natDegree_chi (α k) ▸ natDegree_modByMonic_lt _ (chi_monic _)
        (fun h1 => by simpa [h1] using natDegree_chi (α k))
    generalize (X ^ m - 1 : R[X]) %ₘ chi (α k) = r at hr hdeg ⊢
    have e := LinearMap.congr_fun hr (sv k)
    simp only [aeval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_zero, pow_succ,
      LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, (rho_sv hk).1,
      (rho_sv hk).2, pow_zero, Module.End.one_apply, LinearMap.zero_apply, zero_add] at e
    have e0 := congrFun e k; have e1 := congrFun e (k + 1); have e2 := congrFun e (k + 2)
    simp [sv, wv] at e0 e1 e2
    ext (_ | _ | _ | i)
    · simpa [e2] using e0
    · simpa [e2] using e1
    · simpa using e2
    · simpa using coeff_eq_zero_of_natDegree_lt (by omega : r.natDegree < i + 3)
  · rintro ⟨q, hq⟩
    have := congrArg (aeval (rho (n := n) (α := α) k)) hq
    rwa [map_mul, aeval_rho_chi hk, zero_mul, map_sub, map_one, map_pow, aeval_X,
      sub_eq_zero] at this

theorem sq_eq_one_iff_eq_inv {L : Type*} [Field L] {ζ : L} (hζ : ζ ≠ 0) :
    ζ ^ 2 = 1 ↔ ζ = ζ⁻¹ := by
  rw [sq, mul_eq_one_iff_eq_inv₀ hζ]

/-- Over a field of characteristic `0`, with `a = ζ + ζ⁻¹`: `(t − 1)(t² − a t + 1)` divides
`t^m − 1` (`m ≠ 0`) iff `ζ^m = 1` and `ζ² ≠ 1` (`t^m − 1` has simple roots). -/
theorem chi_dvd_iff {L : Type*} [Field L] [CharZero L] {ζ : L} (hζ : ζ ≠ 0) {m : ℕ}
    (hm : m ≠ 0) : chi (ζ + ζ⁻¹) ∣ X ^ m - 1 ↔ ζ ^ m = 1 ∧ ζ ^ 2 ≠ 1 := by
  have hc : chi (ζ + ζ⁻¹) = ((1 ::ₘ ζ ::ₘ {ζ⁻¹} : Multiset L).map fun a => X - C a).prod := by
    simp only [chi, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_one, C_add]
    have : C ζ * C ζ⁻¹ = (1 : L[X]) := by rw [← C_mul, mul_inv_cancel₀ hζ, C_1]
    linear_combination (1 - X) * this
  have h0 : (X ^ m - 1 : L[X]) ≠ 0 := by simpa using (monic_X_pow_sub_C (1 : L) hm).ne_zero
  have hsep := nodup_roots (X_pow_sub_one_separable_iff.2 (Nat.cast_ne_zero.2 hm) :
    (X ^ m - 1 : L[X]).Separable)
  have hr (a : L) : a ∈ (X ^ m - 1 : L[X]).roots ↔ a ^ m = 1 := by
    simp [mem_roots h0, sub_eq_zero]
  rw [hc, Multiset.prod_X_sub_C_dvd_iff_le_roots h0, Ne, sq_eq_one_iff_eq_inv hζ]
  constructor
  · intro hle
    have hnd := Multiset.nodup_of_le hle hsep
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, not_or] at hnd
    exact ⟨(hr ζ).1 (Multiset.mem_of_le hle (by simp)), hnd.2.1⟩
  · rintro ⟨h1, h2⟩
    have h3 : ζ ≠ 1 := fun h => h2 (by simp [h])
    rw [Multiset.le_iff_subset (by simp [h2, h3, Ne.symm h3, eq_comm (a := (1 : L)),
      inv_eq_one]), Multiset.cons_subset, Multiset.cons_subset, Multiset.singleton_subset]
    exact ⟨(hr 1).2 (one_pow m), (hr ζ).2 h1, (hr _).2 (by rw [inv_pow, h1, inv_one])⟩

/-- `P ↦ X^d P(X + X⁻¹)`, `d = deg P`, as a polynomial. -/
noncomputable def recip {S : Type*} [CommRing S] (P : S[X]) : S[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i) * X ^ (P.natDegree - i) * (X ^ 2 + 1) ^ i

theorem aeval_recip {S L : Type*} [CommRing S] [Field L] [Algebra S L] (P : S[X]) {z : L}
    (hz : z ≠ 0) : aeval z (recip P) = z ^ P.natDegree * aeval (z + z⁻¹) P := by
  rw [recip, map_sum, aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have : z ^ 2 + 1 = z * (z + z⁻¹) := by field_simp
  rw [map_mul, map_mul, map_pow, map_pow, aeval_C, aeval_X, map_add, map_pow, aeval_X, map_one,
    this, mul_pow, Algebra.smul_def, ← Nat.sub_add_cancel hi, pow_add, Nat.add_sub_cancel]
  ring

theorem eval_zero_recip {S : Type*} [CommRing S] (P : S[X]) :
    (recip P).eval 0 = P.leadingCoeff := by
  rw [recip, eval_finsetSum, Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => ?_]
  · rw [leadingCoeff]; simp
  · simp [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hi))]

theorem natDegree_recip_le {S : Type*} [CommRing S] (P : S[X]) :
    (recip P).natDegree ≤ 2 * P.natDegree := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have hi : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine natDegree_mul_le.trans ?_
  have h1 := (natDegree_C_mul_le (P.coeff i) (X ^ (P.natDegree - i) : S[X])).trans
    (natDegree_X_pow_le _)
  have h2 : ((X ^ 2 + 1 : S[X]) ^ i).natDegree ≤ 2 * i :=
    (natDegree_pow_le_of_le i (by compute_degree)).trans_eq (mul_comm _ _)
  omega

open Complex IntermediateField in
/-- **The minimal polynomial of `2cos(2π/p)`**, `p ≥ 3`: `X^d Ψ(X + X⁻¹)` is the cyclotomic
polynomial `Φ_p` (`d = deg Ψ = φ(p)/2`). -/
theorem recip_minpoly_cos {p : ℕ} (hp : 3 ≤ p) :
    recip (minpoly ℤ (2 * Real.cos (2 * Real.pi / p))) = cyclotomic p ℤ := by
  have hpos : 0 < p := by omega
  set x : ℝ := 2 * Real.pi / p
  set ζ : ℂ := exp (x * I)
  have hζ : IsPrimitiveRoot ζ p := by
    convert isPrimitiveRoot_exp p hpos.ne' using 2; simp only [x]; push_cast; ring
  have hc : ((2 * Real.cos x : ℝ) : ℂ) = ζ + ζ⁻¹ := by
    rw [show ζ⁻¹ = cos x - sin x * I by rw [cos_sub_sin_I, neg_mul, exp_neg],
      show ζ = cos x + sin x * I from (cos_add_sin_I _).symm]
    push_cast; ring
  have hint : IsIntegral ℤ (ζ + ζ⁻¹) := (hζ.isIntegral hpos).add (hζ.inv.isIntegral hpos)
  have hΨ : minpoly ℤ (2 * Real.cos x) = minpoly ℤ (ζ + ζ⁻¹) := by
    rw [← hc]; exact (minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective _).symm
  rw [hΨ]
  set Ψ := minpoly ℤ (ζ + ζ⁻¹)
  have hmon : Ψ.Monic := minpoly.monic hint
  -- `2 deg Ψ ≤ φ(p)`: `ℚ⟮ζ + ζ⁻¹⟯` is real, so `ℚ⟮ζ⟯` has degree `≥ 2` over it.
  have hdeg : 2 * Ψ.natDegree ≤ p.totient := by
    have hA : Module.finrank ℚ ℚ⟮ζ + ζ⁻¹⟯ = Ψ.natDegree := by
      rw [adjoin.finrank hint.tower_top, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint,
        hmon.natDegree_map]
    have hB : Module.finrank ℚ ℚ⟮ζ⟯ = p.totient := by
      rw [adjoin.finrank (hζ.isIntegral hpos).tower_top, ← cyclotomic_eq_minpoly_rat hζ hpos,
        natDegree_cyclotomic]
    have hle : ℚ⟮ζ + ζ⁻¹⟯ ≤ ℚ⟮ζ⟯ := adjoin_simple_le_iff.2
      (add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ)))
    have hmul := finrank_bot_mul_relfinrank hle
    have hne : relfinrank ℚ⟮ζ + ζ⁻¹⟯ ℚ⟮ζ⟯ ≠ 1 := fun h => by
      have hR : ℚ⟮ζ + ζ⁻¹⟯ ≤ (ofRealAm.restrictScalars ℚ).fieldRange :=
        adjoin_simple_le_iff.2 ⟨2 * Real.cos x, hc⟩
      obtain ⟨r, hr⟩ := hR (relfinrank_eq_one_iff.1 h (mem_adjoin_simple_self ℚ ζ))
      have him := congrArg im (show (r : ℂ) = ζ from hr)
      rw [ofReal_im, exp_ofReal_mul_I_im] at him
      have h3 := mul_le_mul_of_nonneg_left (by exact_mod_cast hp : (3 : ℝ) ≤ p) Real.pi_pos.le
      exact (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
        rw [div_lt_iff₀ (by positivity)]; linarith [Real.pi_pos])).ne him
    have h0 : relfinrank ℚ⟮ζ + ζ⁻¹⟯ ℚ⟮ζ⟯ ≠ 0 := fun h => by
      rw [h, mul_zero, hB] at hmul; exact (Nat.totient_pos.2 hpos).ne hmul
    rw [hA, hB] at hmul
    rw [← hmul, mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have hroot : aeval ζ (recip Ψ) = 0 := by
    rw [aeval_recip _ (exp_ne_zero _), minpoly.aeval, mul_zero]
  obtain ⟨g, hg⟩ := cyclotomic_eq_minpoly hζ hpos ▸
    minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hpos) hroot
  have h1 := eval_zero_recip Ψ
  rw [hmon.leadingCoeff] at h1
  have hg0 : g ≠ 0 := by rintro rfl; simp [hg] at h1
  have h2 := natDegree_recip_le Ψ
  rw [hg, natDegree_mul (cyclotomic_ne_zero p ℤ) hg0, natDegree_cyclotomic] at h2
  rw [hg, eq_C_of_natDegree_eq_zero (show g.natDegree = 0 by omega)] at h1 ⊢
  rw [eval_mul, eval_C, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero ℤ (by omega),
    one_mul] at h1
  rw [h1, C_1, mul_one]

/-- **Page 67's criterion for every `p ≥ 3`.** Over a field of characteristic `0`, for every
`n` and `k + 1 ≤ n`, `σₖσₖ₊₁` has order exactly `p` iff `αₖ` is a root of the minimal
polynomial (over `ℤ`) of `2cos(2π/p)`. -/
theorem orderOf_rho_eq_iff {K : Type*} [Field K] [CharZero K] {α : ℕ → K} {k : ℕ}
    (hk : k + 1 ≤ n) {p : ℕ} (hp : 3 ≤ p) :
    orderOf (rho (n := n) (α := α) k) = p ↔
      aeval (α k) (minpoly ℤ (2 * Real.cos (2 * Real.pi / p))) = 0 := by
  set L := AlgebraicClosure K
  set f := algebraMap K L
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (X ^ 2 - C (f (α k)) * X + 1 : L[X])
    (by rw [show (X ^ 2 - C (f (α k)) * X + 1 : L[X]).degree = 2 by compute_degree!]; simp)
  simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one] at hζ
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have ha : f (α k) = ζ + ζ⁻¹ := mul_left_cancel₀ hζ0 (by
    rw [mul_add, mul_inv_cancel₀ hζ0]; linear_combination -hζ)
  have hpow (m : ℕ) (hm : m ≠ 0) :
      rho (n := n) (α := α) k ^ m = 1 ↔ ζ ^ m = 1 ∧ ζ ^ 2 ≠ 1 := by
    rw [rho_pow_eq_one_iff hk, ← chi_dvd_iff hζ0 hm, ← ha,
      ← map_dvd_map f f.injective (chi_monic _)]
    simp [chi]
  have : NeZero (p : L) := ⟨Nat.cast_ne_zero.2 (by omega)⟩
  have hprim : orderOf (rho (n := n) (α := α) k) = p ↔ IsPrimitiveRoot ζ p := by
    rw [IsPrimitiveRoot.iff_orderOf]
    by_cases h2 : ζ ^ 2 = 1
    · have h0 : orderOf (rho (n := n) (α := α) k) = 0 :=
        orderOf_eq_zero_iff'.2 fun m hm => by simp [hpow m hm.ne', h2]
      have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
      omega
    · rw [(orderOf_eq_orderOf_iff (y := ζ)).2 fun m => ?_]
      rcases eq_or_ne m 0 with rfl | hm
      · simp
      · simp [hpow m hm, h2]
  rw [hprim, ← isRoot_cyclotomic_iff, ← map_cyclotomic_int, ← recip_minpoly_cos hp, IsRoot,
    eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_recip _ hζ0, ← ha, aeval_algebraMap_apply,
    mul_eq_zero, map_eq_zero_iff f f.injective]
  simp [hζ0]

end General

end Grothendieck.Folder70
