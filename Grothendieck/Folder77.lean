module

public import Mathlib

@[expose] public section


/-!
# Folder 77, pages 65–71 and 87: the universal discriminant mod 2 and mod 4

The modernised reading `transcripts/77/77.modern.tex` (« Discriminant des formes
quadratiques », pages 64 to 87) takes the universal quadratic form
`Σ Yᵢ xᵢ² + Σ_{i<j} Yᵢⱼ xᵢ xⱼ` over `ℤ[Y]`, whose polar matrix has `2Yᵢ` on the
diagonal and `Yᵢⱼ` off it, and its determinant `Δ`. It states:

> **Page 68.** `Δ ≡ 0 (mod 2)` if `card I` is odd, so that the half-discriminant
> `δ' = δ/2` is defined over any base in odd rank.
>
> **Pages 68–71.** In even rank `2n`, with `B` the sum over the perfect matchings
> of `I` of the products of the `Yᵢⱼ` (the hafnian of the off-diagonal
> coefficients), `(-1)ⁿ Δ = B² - 4C` for some `C ∈ ℤ[Y]`.

These are findings `77-odd-rank-half-discriminant` and
`77-universal-even-rank-discriminant-mod-4` of `src/content/findings.ts`.
Proving them says only that the claims hold as stated; whether they stand in the
literature is a separate question.

What is formalised.

* Odd rank, every odd `n` (`two_dvd_det_polar`): the variables are indexed by
  `Sym2 (Fin n)`, `s(i, i)` for `Yᵢ` and `s(i, j)` for `Yᵢⱼ`. The proof does not
  follow the graph expansion of the page: modulo `2` the polar matrix agrees with
  the skew-symmetric matrix `K` (`Yᵢⱼ` above the diagonal, `-Yᵢⱼ` below, `0` on
  it), and `det K = 0` over `ℤ[Y]` in odd size since `det Kᵀ = det (-K) = -det K`
  and `ℤ[Y]` has no `2`-torsion. The quotient `halfDisc n` is unique, and its
  value at the coefficients of a form over any commutative ring halves the
  determinant there (`det_polarOf_eq`).
* Even rank, ranks `2` and `4` (`disc_rank_two`, `disc_rank_four`): the identity
  `(-1)ⁿ Δ = B² - 4C` over any commutative ring, with `C` written out. In rank 2
  it is `-Δ = b² - 4ac`. The sign `-(-1)ⁿ` fails in both ranks
  (`not_dvd_rank_two`, `not_dvd_rank_four`).
* Even rank, every `n` (`four_dvd_disc_sub_hafnian_sq`, `disc_even_rank`): `4` divides
  `(-1)ⁿ Δ - B²` in `ℤ[Y]`, `B` the hafnian (`hafnian`). No Pfaffian is used. With `U`
  the upper half of the polar matrix, `P = U + Uᵀ` and the skew matrix is
  `K = U - Uᵀ = P - 2Uᵀ`; the first-order term of `det (P - t Uᵀ)`, computed in the
  fraction field, gives `det K ≡ (1 - 2n) det P (mod 4)` (`det_skew_eq_first_order`).
  Next `det K = r²` in `ℤ[Y]` (`det_skew_eq_sq`): over a field of characteristic `≠ 2` an
  antisymmetric matrix of even size has a square determinant (Schur complement on a
  `2 × 2` block), and `ℤ[Y]` is integrally closed. Modulo `2`, the determinant of a
  symmetric matrix with zero diagonal is the square of its matching sum
  (`det_eq_hafSum_sq`), so `r ≡ B (mod 2)` and `det K ≡ B² (mod 4)`. Finally
  `(-1)ⁿ ≡ 1 - 2n (mod 4)`.

# Folder 77, pages 117–125: the canonical symmetry of a biregular affine quadric

The reading (§ 1'' and § 2) attaches to `(T, q, a)`, `q(a) = 1`, `π = φ(a, ·)`, the map
`σ = id - π ⊗ a` and states (marginal Proposition, p. 123) that it is the only reflection
fixing the hyperplane at infinity and preserving the quadric; it is a symmetry of centre
`a/2` if `2` is invertible and a transvection in characteristic `2` (finding
`77-biregular-affine-quadric-symmetry`). Formalised over any commutative ring:
`piForm_self` (`π(a) = 2`), `canSym_isometry`, `canSym_canSym` (`σ² = id`),
`eq_of_isometry_fix` (with `φ` nondegenerate and `π` onto, a linear isometry fixing `ker π`
pointwise is `x ↦ x - e π(x) a` with `e` idempotent; conversely `isometry_of_idem`),
`eq_id_or_canSym` (no nontrivial idempotent: `id` or `σ`), `canSym_center` (`2`
invertible), `canSym_char_two` (`2 = 0`), and `det_polar_one` (the example `M₂`, `det`, `1`
of p. 124, where `π` is the trace).
-/

namespace Grothendieck.Folder77

open MvPolynomial Matrix

/-! ## Odd rank: the determinant is even -/

/-- The polar matrix of the universal quadratic form of rank `n`: `2 Yᵢ` on the
diagonal, `Yᵢⱼ` off it, the variable `Y_J` being indexed by `J = s(i, j)`
(page 65). -/
noncomputable def polar (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Sym2 (Fin n)) ℤ) :=
  fun i j => if i = j then 2 * X s(i, i) else X s(i, j)

/-- The skew-symmetric matrix that agrees with `polar n` modulo `2`. -/
noncomputable def skew (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Sym2 (Fin n)) ℤ) :=
  fun i j => if i < j then X s(i, j) else if j < i then -X s(i, j) else 0

theorem skew_transpose (n : ℕ) : (skew n)ᵀ = -skew n := by
  refine Matrix.ext fun i j => ?_
  change skew n j i = -skew n i j
  simp only [skew]
  rw [Sym2.eq_swap (a := j) (b := i)]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [ite_eq_left h, ite_eq_right (not_lt_of_gt h)]
  · simp
  · simp only [ite_eq_left h, ite_eq_right (not_lt_of_gt h), neg_neg]

theorem det_skew_of_odd {n : ℕ} (hn : Odd n) : (skew n).det = 0 := by
  have h := det_transpose (skew n)
  rw [skew_transpose, det_neg, Fintype.card_fin, hn.neg_one_pow, neg_one_mul,
    neg_eq_iff_add_eq_zero, ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- Reduction of the coefficients modulo `2`. -/
noncomputable abbrev red (n : ℕ) :
    MvPolynomial (Sym2 (Fin n)) ℤ →+* MvPolynomial (Sym2 (Fin n)) (ZMod 2) :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))

theorem polar_map_red (n : ℕ) : (polar n).map (red n) = (skew n).map (red n) := by
  refine Matrix.ext fun i j => ?_
  simp only [map_apply, polar, skew]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [ite_eq_right h.ne, ite_eq_left h]
  · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl i), ite_eq_right (lt_irrefl i)]
    simp only [map_mul, map_zero, map_ofNat,
      CharTwo.two_eq_zero (R := MvPolynomial (Sym2 (Fin n)) (ZMod 2)), zero_mul]
  · simp only [ite_eq_right h.ne', ite_eq_right (not_lt_of_gt h), ite_eq_left h, map_neg]
    exact (CharTwo.neg_eq (R := MvPolynomial (Sym2 (Fin n)) (ZMod 2)) _).symm

/-- An integer polynomial whose reduction modulo `2` vanishes is divisible by `2`. -/
theorem two_dvd_of_red_eq_zero {n : ℕ} {p : MvPolynomial (Sym2 (Fin n)) ℤ}
    (hp : red n p = 0) : (2 : MvPolynomial (Sym2 (Fin n)) ℤ) ∣ p := by
  have : p ∈ RingHom.ker (red n) := hp
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at this
  simpa using this

/-- **Page 68.** In odd rank the universal discriminant is divisible by `2`
in `ℤ[Y]`. -/
theorem two_dvd_det_polar {n : ℕ} (hn : Odd n) :
    (2 : MvPolynomial (Sym2 (Fin n)) ℤ) ∣ (polar n).det := by
  apply two_dvd_of_red_eq_zero
  rw [RingHom.map_det, RingHom.mapMatrix_apply, polar_map_red, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_skew_of_odd hn, map_zero]

/-- The universal half-discriminant `δ' = Δ / 2` in odd rank. -/
noncomputable def halfDisc {n : ℕ} (hn : Odd n) : MvPolynomial (Sym2 (Fin n)) ℤ :=
  (two_dvd_det_polar hn).choose

theorem det_polar_eq {n : ℕ} (hn : Odd n) : (polar n).det = 2 * halfDisc hn :=
  (two_dvd_det_polar hn).choose_spec

/-- The half-discriminant is the only polynomial with `Δ = 2 δ'`. -/
theorem halfDisc_unique {n : ℕ} (hn : Odd n) {d : MvPolynomial (Sym2 (Fin n)) ℤ}
    (hd : (polar n).det = 2 * d) : d = halfDisc hn := by
  rw [det_polar_eq hn] at hd
  exact (mul_left_cancel₀ two_ne_zero hd).symm

/-- The polar matrix of the quadratic form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` over a
commutative ring `R`. -/
def polarOf {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then 2 * y s(i, i) else y s(i, j)

theorem polar_map_aeval {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    (polar n).map (aeval y) = polarOf y := by
  ext i j
  simp only [map_apply, polar, polarOf]
  split_ifs <;> simp

/-- Over any commutative ring, in odd rank, the determinant of the polar form is
twice the value of the universal half-discriminant: `δ'` is defined over any
base. -/
theorem det_polarOf_eq {R : Type*} [CommRing R] {n : ℕ} (hn : Odd n)
    (y : Sym2 (Fin n) → R) : (polarOf y).det = 2 * aeval y (halfDisc hn) := by
  have := AlgHom.map_det (aeval (R := ℤ) y) (polar n)
  rw [det_polar_eq hn, map_mul, map_ofNat, AlgHom.mapMatrix_apply, polar_map_aeval] at this
  exact this.symm

/-! ## Even rank: `(-1)ⁿ Δ = B² - 4C` in ranks 2 and 4 -/

/-- **Rank 2.** `-Δ = b² - 4ac`; here `B = b` and `C = ac`. -/
theorem disc_rank_two {R : Type*} [CommRing R] (a₁ a₂ b₁₂ : R) :
    -(!![2 * a₁, b₁₂; b₁₂, 2 * a₂]).det = b₁₂ ^ 2 - 4 * (a₁ * a₂) := by
  rw [det_fin_two_of]; ring

/-- The polar matrix of the quadratic form of rank `4`. -/
def polar4 {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄ : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![2 * a₁, b₁₂, b₁₃, b₁₄;
     b₁₂, 2 * a₂, b₂₃, b₂₄;
     b₁₃, b₂₃, 2 * a₃, b₃₄;
     b₁₄, b₂₄, b₃₄, 2 * a₄]

theorem det_polar4 {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄ : R) :
    (polar4 a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄).det =
      16 * a₁ * a₂ * a₃ * a₄
      - 4 * (a₁ * a₂ * b₃₄ ^ 2 + a₁ * a₃ * b₂₄ ^ 2 + a₁ * a₄ * b₂₃ ^ 2
        + a₂ * a₃ * b₁₄ ^ 2 + a₂ * a₄ * b₁₃ ^ 2 + a₃ * a₄ * b₁₂ ^ 2)
      + 4 * (a₁ * b₂₃ * b₂₄ * b₃₄ + a₂ * b₁₃ * b₁₄ * b₃₄ + a₃ * b₁₂ * b₁₄ * b₂₄
        + a₄ * b₁₂ * b₁₃ * b₂₃)
      + b₁₂ ^ 2 * b₃₄ ^ 2 + b₁₃ ^ 2 * b₂₄ ^ 2 + b₁₄ ^ 2 * b₂₃ ^ 2
      - 2 * (b₁₂ * b₁₃ * b₂₄ * b₃₄ + b₁₂ * b₁₄ * b₂₃ * b₃₄ + b₁₃ * b₁₄ * b₂₃ * b₂₄) := by
  rw [polar4, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, Fin.succAbove]
  ring

/-- **Rank 4.** `Δ = B² - 4C`, with `B = b₁₂b₃₄ + b₁₃b₂₄ + b₁₄b₂₃` the sum over the
three perfect matchings of `{1, 2, 3, 4}`. -/
theorem disc_rank_four {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄ : R) :
    (polar4 a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄).det =
      (b₁₂ * b₃₄ + b₁₃ * b₂₄ + b₁₄ * b₂₃) ^ 2
      - 4 * (-4 * a₁ * a₂ * a₃ * a₄
        + a₁ * a₂ * b₃₄ ^ 2 + a₁ * a₃ * b₂₄ ^ 2 + a₁ * a₄ * b₂₃ ^ 2
        + a₂ * a₃ * b₁₄ ^ 2 + a₂ * a₄ * b₁₃ ^ 2 + a₃ * a₄ * b₁₂ ^ 2
        - (a₁ * b₂₃ * b₂₄ * b₃₄ + a₂ * b₁₃ * b₁₄ * b₃₄ + a₃ * b₁₂ * b₁₄ * b₂₄
          + a₄ * b₁₂ * b₁₃ * b₂₃)
        + b₁₂ * b₁₃ * b₂₄ * b₃₄ + b₁₂ * b₁₄ * b₂₃ * b₃₄ + b₁₃ * b₁₄ * b₂₃ * b₂₄) := by
  rw [det_polar4]; ring

/-- The other sign fails in rank 2: at `a = c = 0`, `b = 1`, `B² - Δ = 2` is not
divisible by `4`. -/
theorem not_dvd_rank_two :
    ¬ (4 : ℤ) ∣ (1 : ℤ) ^ 2 - (!![2 * 0, 1; 1, 2 * 0] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rw [det_fin_two_of]; decide

/-- The other sign fails in rank 4: at `b₁₂ = b₃₄ = 1`, all other coefficients
`0`, `B² + Δ = 2` is not divisible by `4`. -/
theorem not_dvd_rank_four :
    ¬ (4 : ℤ) ∣ (1 : ℤ) ^ 2 + (polar4 (0 : ℤ) 0 0 0 1 0 0 0 0 1).det := by
  rw [det_polar4]; decide

/-! ## Even rank, every `n`: `(-1)ⁿ Δ ≡ B² (mod 4)` -/

/-- The upper-triangular half of the universal polar matrix. -/
noncomputable def upper (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Sym2 (Fin m)) ℤ) :=
  fun i j => if i ≤ j then X s(i, j) else 0

theorem polar_eq_upper (m : ℕ) : polar m = upper m + (upper m)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [polar, upper, Matrix.add_apply, transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.ne, h.le, not_le.mpr h]
  · simp [two_mul]
  · simp [h.ne', h.le, not_le.mpr h, Sym2.eq_swap]

theorem skew_eq_upper (m : ℕ) : skew m = upper m - (upper m)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [skew, upper, Matrix.sub_apply, transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.le, not_le.mpr h]
  · simp
  · simp [h, h.le, not_le.mpr h, not_lt.mpr h.le, Sym2.eq_swap]

/-- `Δ ≠ 0`: at `Yᵢ = 1`, `Yᵢⱼ = 0` it is `2 ^ m`. -/
theorem det_polar_ne_zero (m : ℕ) : (polar m).det ≠ 0 := by
  intro h
  let y : Sym2 (Fin m) → ℤ := fun z => if z.IsDiag then 1 else 0
  have hy : polarOf y = diagonal fun _ => 2 := by
    ext i j
    simp only [polarOf, diagonal_apply, y]
    split_ifs with h1 h2 <;> simp_all [Sym2.mk_isDiag_iff]
  have := AlgHom.map_det (aeval (R := ℤ) y) (polar m)
  rw [h, map_zero, AlgHom.mapMatrix_apply, polar_map_aeval, hy, det_diagonal] at this
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact pow_ne_zero m two_ne_zero this.symm

theorem polar_transpose (m : ℕ) : (polar m)ᵀ = polar m := by
  rw [polar_eq_upper, transpose_add, transpose_transpose, add_comm]

/-- First-order expansion of `det (P - t Uᵀ)` at `t = 2`: `det K = det P + 2 c₁ + 4 q` with
`2 c₁ = -m det P`, hence `det K ≡ (1 - m) det P (mod 4)`. -/
theorem det_skew_eq_first_order (m : ℕ) :
    ∃ c₁ q : MvPolynomial (Sym2 (Fin m)) ℤ,
      (skew m).det = (polar m).det + 2 * c₁ + 4 * q ∧
        2 * c₁ = -(m : MvPolynomial (Sym2 (Fin m)) ℤ) * (polar m).det := by
  set P := polar m
  set U := upper m
  let f : Polynomial (MvPolynomial (Sym2 (Fin m)) ℤ) :=
    det (P.map Polynomial.C -
      (Polynomial.X : Polynomial (MvPolynomial (Sym2 (Fin m)) ℤ)) • Uᵀ.map Polynomial.C)
  have hdecomp : f = Polynomial.C (f.coeff 0) + Polynomial.X * (Polynomial.C (f.coeff 1) +
      Polynomial.X * f.divX.divX) := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add f, ← Polynomial.divX_mul_X_add f.divX]
    rw [Polynomial.coeff_divX, zero_add]; ring
  have heval : (Polynomial.evalRingHom 2) f = (skew m).det := by
    rw [RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp [P, U, skew_eq_upper, polar_eq_upper]
    ring
  have h0 : f.coeff 0 = P.det := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp
  refine ⟨f.coeff 1, Polynomial.eval 2 f.divX.divX, ?_, ?_⟩
  · rw [← heval, ← h0]
    conv_lhs => rw [hdecomp]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    ring
  · let F := FractionRing (MvPolynomial (Sym2 (Fin m)) ℤ)
    let φ := algebraMap (MvPolynomial (Sym2 (Fin m)) ℤ) F
    apply IsFractionRing.injective (MvPolynomial (Sym2 (Fin m)) ℤ) F
    set PF := P.map φ
    set UF := U.map φ
    have hdet : φ P.det = PF.det := by rw [RingHom.map_det]; rfl
    have hPF : IsUnit PF.det := by
      rw [isUnit_iff_ne_zero, ← hdet]
      exact (map_ne_zero_iff φ (IsFractionRing.injective _ F)).mpr (det_polar_ne_zero m)
    have hfmap : f.map φ =
        det (PF.map Polynomial.C - (Polynomial.X : Polynomial F) • UFᵀ.map Polynomial.C) := by
      rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
      congr 1
      refine Matrix.ext fun i j => ?_
      simp [PF, UF]
    have hfac : PF.map Polynomial.C - (Polynomial.X : Polynomial F) • UFᵀ.map Polynomial.C =
        PF.map Polynomial.C *
          (1 + (Polynomial.X : Polynomial F) • (-(PF⁻¹ * UFᵀ)).map Polynomial.C) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPF, Matrix.one_mul,
        Matrix.map_neg _ (map_neg Polynomial.C),
        smul_neg, sub_eq_add_neg]
    have hc1 : φ (f.coeff 1) = PF.det * trace (-(PF⁻¹ * UFᵀ)) := by
      rw [← Polynomial.coeff_map, hfmap, hfac, det_mul, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, Polynomial.coeff_C_mul, coeff_det_one_add_X_smul_one]
    have hPFsym : PFᵀ = PF := by rw [← transpose_map, polar_transpose]
    have hPU : P = U + Uᵀ := polar_eq_upper m
    have hPFeq : PF = UF + UFᵀ := by
      simp only [PF, UF, hPU]
      rw [Matrix.map_add _ (map_add φ), transpose_map]
    have htr : trace (PF⁻¹ * UFᵀ) = trace (PF⁻¹ * UF) := by
      rw [← trace_transpose (PF⁻¹ * UF), transpose_mul, transpose_nonsing_inv, hPFsym,
        trace_mul_comm]
    have hsum : trace (PF⁻¹ * UFᵀ) + trace (PF⁻¹ * UF) = m := by
      rw [← trace_add, ← Matrix.mul_add, add_comm, ← hPFeq, Matrix.nonsing_inv_mul _ hPF,
        trace_one, Fintype.card_fin]
    rw [map_mul, map_mul, hc1, map_neg, map_natCast, hdet, trace_neg, map_ofNat]
    linear_combination (-PF.det) * hsum - PF.det * htr

section
open Finset

/-- The fixed-point-free involutions of `Fin m`, that is, the perfect matchings. -/
def fpfInv (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i

/-- The matching sum (hafnian) of a matrix: over the perfect matchings `σ`, the product of
the entries `M i (σ i)` for `i < σ i`. -/
def hafSum {S : Type*} [CommRing S] {m : ℕ} (M : Matrix (Fin m) (Fin m) S) : S :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ univ.filter (fun i => i < σ i), M i (σ i)

/-- For a symmetric matrix and a perfect matching `σ`, `∏ᵢ M (σ i) i` is the square of the
product over the edges. -/
theorem prod_fpf_eq_sq {S : Type*} [CommRing S] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) S) (hM : Mᵀ = M) {σ : Equiv.Perm (Fin m)}
    (hσ : σ ∈ fpfInv m) :
    ∏ i, M (σ i) i = (∏ i ∈ univ.filter (fun i => i < σ i), M i (σ i)) ^ 2 := by
  simp only [fpfInv, mem_filter, mem_univ, true_and] at hσ
  obtain ⟨hinv, hfix⟩ := hσ
  have hss : ∀ i, σ (σ i) = i := fun i => by
    simpa using congrArg (fun τ : Equiv.Perm (Fin m) => τ i) hinv
  have hsym : ∀ i j, M i j = M j i := fun i j => by
    simpa using congrFun (congrFun hM j) i
  rw [← prod_filter_mul_prod_filter_not univ (fun i => i < σ i), sq]
  congr 1
  · exact prod_congr rfl fun i _ => hsym _ _
  · refine prod_nbij' σ σ ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi ⊢
      rw [hss]
      exact lt_of_le_of_ne hi (hfix i)
    · intro i hi
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi ⊢
      rw [hss]; exact hi.le
    · intro i _; exact hss i
    · intro i _; exact hss i
    · intro i _; rw [hss]

/-- In characteristic `2`, the determinant of a symmetric matrix with zero diagonal is the
square of its matching sum: signs disappear, `σ` and `σ⁻¹` give the same product so the
non-involutions cancel in pairs, and involutions with a fixed point give `0`. -/
theorem det_eq_hafSum_sq {S : Type*} [CommRing S] [CharP S 2] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) S) (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) :
    M.det = hafSum M ^ 2 := by
  have h2 : (2 : S) = 0 := by exact_mod_cast CharP.cast_eq_zero S 2
  have hsym : ∀ i j, M i j = M j i := fun i j => by
    simpa using congrFun (congrFun hM j) i
  rw [det_apply]
  have hsign : ∀ σ : Equiv.Perm (Fin m),
      (Equiv.Perm.sign σ) • (∏ i, M (σ i) i) = ∏ i, M (σ i) i := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul]; exact CharTwo.neg_eq _
  simp_rw [hsign]
  rw [← sum_filter_add_sum_filter_not univ (fun σ => σ ∈ fpfInv m)]
  have hzero : ∑ σ ∈ univ.filter (fun σ => σ ∉ fpfInv m), ∏ i, M (σ i) i = 0 := by
    have hinvp : ∀ σ : Equiv.Perm (Fin m), ∏ i, M (σ⁻¹ i) i = ∏ i, M (σ i) i := by
      intro σ
      rw [← Equiv.prod_comp σ]
      exact prod_congr rfl fun i _ => by simp [hsym]
    refine sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      rw [hinvp, ← two_mul, h2, zero_mul]
    · intro σ hσ hne heq
      apply hne
      simp only [fpfInv, mem_filter, mem_univ, true_and, not_and, not_forall,
        not_not] at hσ
      have hinv : σ * σ = 1 := by
        rw [← mul_inv_cancel σ, heq]
      obtain ⟨i, hi⟩ := hσ hinv
      exact prod_eq_zero (mem_univ i) (by rw [hi, hd])
    · intro σ hσ
      simp only [fpfInv, mem_filter, mem_univ, true_and] at hσ ⊢
      intro h
      apply hσ
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, fun i hi => h2 i ?_⟩
      · simpa [_root_.mul_inv_rev] using congrArg (·⁻¹) h1
      · rw [Equiv.Perm.inv_eq_iff_eq]; exact hi.symm
    · intro σ _; exact inv_inv σ
  rw [hzero, add_zero, filter_mem_eq_inter, univ_inter, hafSum, sum_pow_char]
  exact sum_congr rfl fun σ hσ => prod_fpf_eq_sq M hM hσ

end

theorem inv_transpose_of_skew {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hA : Aᵀ = -A) (hu : IsUnit A.det) : A⁻¹ᵀ = -A⁻¹ := by
  rw [transpose_nonsing_inv, hA]
  apply Matrix.inv_eq_right_inv
  rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hu]

/-- Induction step: an antisymmetric matrix of size `m + 2` over a field of characteristic
`≠ 2` has a square determinant if those of size `m` do (Schur complement on the `2 × 2`
block of a nonzero coefficient of the first row). -/
theorem det_skew_step {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (m : ℕ)
    (ih : ∀ K : Matrix (Fin m) (Fin m) k, Kᵀ = -K → ∃ s, K.det = s ^ 2)
    (K : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (hK : Kᵀ = -K) : ∃ s, K.det = s ^ 2 := by
  have hskew : ∀ i j, K j i = -K i j := fun i j => by
    simpa using congrFun (congrFun hK i) j
  have hdiag : ∀ i, K i i = 0 := fun i => by
    have h := hskew i i
    have : (2 : k) * K i i = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  by_cases hrow : ∀ j, K 0 j = 0
  · exact ⟨0, by rw [det_eq_zero_of_row_eq_zero 0 hrow]; ring⟩
  simp only [not_forall] at hrow
  obtain ⟨j, hj⟩ := hrow
  have hj0 : j ≠ 0 := fun h => hj (h ▸ hdiag 0)
  let e := Equiv.swap (1 : Fin (m + 2)) j
  let g : Fin 2 ⊕ Fin m ≃ Fin (m + 2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 m))
  have hg0 : g (Sum.inl 0) = 0 := by ext; simp [g]
  have hg1 : g (Sum.inl 1) = 1 := by ext; simp [g]
  have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by simp) hj0.symm
  have he1 : e 1 = j := Equiv.swap_apply_left _ _
  let N := K.submatrix (g.trans e) (g.trans e)
  have hdetN : N.det = K.det := det_submatrix_equiv_self (g.trans e) K
  have hNskew : ∀ i j, N j i = -N i j := fun i j => hskew _ _
  have hA : N.toBlocks₁₁ = !![0, K 0 j; -K 0 j, 0] := by
    conv_lhs => rw [Matrix.eta_fin_two N.toBlocks₁₁]
    simp only [toBlocks₁₁, of_apply, N, submatrix_apply, Equiv.trans_apply, hg0, hg1, he0, he1,
      hdiag, hskew 0 j]
  have hdetA : N.toBlocks₁₁.det = K 0 j ^ 2 := by rw [hA, det_fin_two_of]; ring
  have hu : IsUnit N.toBlocks₁₁.det := by
    rw [hdetA]; exact (pow_ne_zero 2 hj).isUnit
  let _ : Invertible N.toBlocks₁₁ := invertibleOfIsUnitDet _ hu
  have hAskew : N.toBlocks₁₁ᵀ = -N.toBlocks₁₁ := by
    rw [hA]; ext a b; fin_cases a <;> fin_cases b <;> simp
  have hC : N.toBlocks₂₁ = -N.toBlocks₁₂ᵀ := by
    ext a b; simpa [toBlocks₂₁, toBlocks₁₂] using hNskew (Sum.inl b) (Sum.inr a)
  have hD : N.toBlocks₂₂ᵀ = -N.toBlocks₂₂ := by
    ext a b; simpa [toBlocks₂₂] using hNskew (Sum.inr a) (Sum.inr b)
  have hinv : (⅟N.toBlocks₁₁)ᵀ = -⅟N.toBlocks₁₁ := by
    rw [invOf_eq_nonsing_inv]; exact inv_transpose_of_skew _ hAskew hu
  have hS : (N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂)ᵀ =
      -(N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂) := by
    rw [transpose_sub, transpose_mul, transpose_mul, hD, hinv, hC, transpose_neg,
      transpose_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_sub, Matrix.mul_assoc]
    abel
  obtain ⟨s, hs⟩ := ih _ hS
  refine ⟨K 0 j * s, ?_⟩
  have key : N.det = N.toBlocks₁₁.det *
      (N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂).det := by
    conv_lhs => rw [← fromBlocks_toBlocks N]
    exact det_fromBlocks₁₁ _ _ _ _
  rw [← hdetN, key, hdetA, hs]
  ring

/-- Over a field of characteristic `≠ 2`, an antisymmetric matrix of even size has a square
determinant. -/
theorem det_skew_sq_field {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (n : ℕ)
    (K : Matrix (Fin (2 * n)) (Fin (2 * n)) k) (hK : Kᵀ = -K) : ∃ s, K.det = s ^ 2 := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih => exact det_skew_step h2 (2 * n) ih K hK

theorem skew_map_transpose {k : Type*} [CommRing k] (m : ℕ)
    (φ : MvPolynomial (Sym2 (Fin m)) ℤ →+* k) : ((skew m).map φ)ᵀ = -(skew m).map φ := by
  rw [← transpose_map, skew_transpose, Matrix.map_neg _ (map_neg φ)]

/-- **Even rank.** The universal skew-symmetric determinant is a square in `ℤ[Y]`. -/
theorem det_skew_eq_sq (n : ℕ) : ∃ r, (skew (2 * n)).det = r ^ 2 := by
  let A := MvPolynomial (Sym2 (Fin (2 * n))) ℤ
  let F := FractionRing A
  have h2 : (2 : F) ≠ 0 := by simp
  obtain ⟨s, hs⟩ := det_skew_sq_field h2 n _ (skew_map_transpose (2 * n) (algebraMap A F))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hs
  have hint : IsIntegral A s := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (skew (2 * n)).det,
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [Polynomial.eval₂_sub, hs]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, IsFractionRing.injective A F ?_⟩
  rw [map_pow, hr, hs]

/-- The hafnian of the off-diagonal variables: the sum over the perfect matchings of
`Fin m` (the fixed-point-free involutions) of the products of the `Yᵢⱼ`. -/
noncomputable def hafnian (m : ℕ) : MvPolynomial (Sym2 (Fin m)) ℤ :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ Finset.univ.filter (fun i => i < σ i), X s(i, σ i)

/-- Modulo `2`, `det K` is the square of the hafnian. -/
theorem red_det_skew (m : ℕ) : red m (skew m).det = (red m (hafnian m)) ^ 2 := by
  have hT : ((skew m).map (red m))ᵀ = (skew m).map (red m) := by
    rw [skew_map_transpose]; ext i j; exact CharTwo.neg_eq _
  have hd : ∀ i, (skew m).map (red m) i i = 0 := fun i => by simp [skew]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_hafSum_sq _ hT hd, hafSum, hafnian,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp [skew, hi]

/-- **Even rank.** `det K ≡ B² (mod 4)` for the universal skew-symmetric matrix. -/
theorem four_dvd_det_skew_sub (n : ℕ) :
    (4 : MvPolynomial (Sym2 (Fin (2 * n))) ℤ) ∣ (skew (2 * n)).det - hafnian (2 * n) ^ 2 := by
  obtain ⟨r, hr⟩ := det_skew_eq_sq n
  have h : red (2 * n) (r - hafnian (2 * n)) = 0 := by
    have h1 := red_det_skew (2 * n)
    rw [hr, map_pow] at h1
    have : red (2 * n) (r - hafnian (2 * n)) ^ 2 = 0 := by
      rw [map_sub, sub_pow_char, h1, sub_self]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  obtain ⟨g, hg⟩ := two_dvd_of_red_eq_zero h
  refine ⟨hafnian (2 * n) * g + g ^ 2, ?_⟩
  rw [hr, sub_eq_iff_eq_add.mp hg]
  ring

/-- `(-1)ⁿ ≡ 1 - 2n (mod 4)`. -/
theorem four_dvd_neg_one_pow (n : ℕ) : (4 : ℤ) ∣ (-1) ^ n - (1 - 2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨-c + n, by push_cast; rw [pow_succ]; linear_combination (-1 : ℤ) * hc⟩

/-- **Pages 68–71, every even rank.** In `ℤ[Y]`, `4` divides `(-1)ⁿ Δ - B²`, `Δ` the
determinant of the polar matrix of rank `2n` and `B` the hafnian of the `Yᵢⱼ`. -/
theorem four_dvd_disc_sub_hafnian_sq (n : ℕ) :
    (4 : MvPolynomial (Sym2 (Fin (2 * n))) ℤ) ∣
      (-1) ^ n * (polar (2 * n)).det - hafnian (2 * n) ^ 2 := by
  obtain ⟨c₁, q, hK, hc⟩ := det_skew_eq_first_order (2 * n)
  obtain ⟨d, hd⟩ := four_dvd_neg_one_pow n
  have hd' : ((-1) ^ n : MvPolynomial (Sym2 (Fin (2 * n))) ℤ) = 1 - 2 * n + 4 * d := by
    have := congrArg (Int.cast : ℤ → MvPolynomial (Sym2 (Fin (2 * n))) ℤ) hd
    push_cast at this
    linear_combination this
  obtain ⟨e, he⟩ := four_dvd_det_skew_sub n
  refine ⟨d * (polar (2 * n)).det - q + e, ?_⟩
  push_cast at hc
  rw [hd']
  linear_combination he - hK - hc

/-- **Pages 68–71, every even rank, over any base.** There is `C ∈ ℤ[Y]` such that for every
commutative ring `R` and every form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` of rank `2n` over `R`,
`(-1)ⁿ det P(y) = B(y)² - 4 C(y)`. -/
theorem disc_even_rank (n : ℕ) :
    ∃ C : MvPolynomial (Sym2 (Fin (2 * n))) ℤ, ∀ {R : Type*} [CommRing R]
      (y : Sym2 (Fin (2 * n)) → R),
        (-1) ^ n * (polarOf y).det = aeval y (hafnian (2 * n)) ^ 2 - 4 * aeval y C := by
  obtain ⟨C, hC⟩ := four_dvd_disc_sub_hafnian_sq n
  refine ⟨-C, fun y => ?_⟩
  have h := congrArg (aeval (R := ℤ) y) hC
  rw [map_sub, map_mul, map_pow, map_pow, map_neg, map_one, AlgHom.map_det,
    AlgHom.mapMatrix_apply, polar_map_aeval, map_mul, map_ofNat] at h
  rw [map_neg]
  linear_combination h

/-! ## Pages 117–125: the canonical symmetry of a biregular affine quadric -/

section Symmetry

open QuadraticMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear form `π = φ(a, ·)`, `φ` the polar form of `Q` (page 117, (9)). -/
def piForm (Q : QuadraticForm R M) (a : M) : M →ₗ[R] R := polarBilin Q a

theorem piForm_apply (Q : QuadraticForm R M) (a x : M) :
    piForm Q a x = QuadraticMap.polar Q a x := rfl

/-- The canonical symmetry `σ = id - π ⊗ a` (page 123, (20)). -/
def canSym (Q : QuadraticForm R M) (a : M) : M →ₗ[R] M :=
  LinearMap.id - (piForm Q a).smulRight a

theorem canSym_apply (Q : QuadraticForm R M) (a x : M) :
    canSym Q a x = x - QuadraticMap.polar Q a x • a := rfl

/-- `Q (x + y) = Q x + Q y + φ(x, y)`. -/
theorem quad_map_add (Q : QuadraticForm R M) (x y : M) :
    Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]; ring

variable {Q : QuadraticForm R M} {a : M}

/-- **Page 117, (10).** `π(a) = 2`. -/
theorem piForm_self (ha : Q a = 1) : piForm Q a a = 2 := by
  rw [piForm_apply, polar_self, ha, two_smul, one_add_one_eq_two]

/-- `Q (x + t a) = Q x + t (φ(a, x) + t Q a)` (page 122). -/
theorem quad_map_add_smul (x : M) (t : R) :
    Q (x + t • a) = Q x + t * (QuadraticMap.polar Q a x + t * Q a) := by
  rw [quad_map_add, QuadraticMap.map_smul, polar_smul_right, polar_comm, smul_eq_mul, smul_eq_mul]
  ring

/-- **Page 123, (19)–(20).** `σ` preserves `Q`. -/
theorem canSym_isometry (ha : Q a = 1) (x : M) : Q (canSym Q a x) = Q x := by
  rw [canSym_apply, sub_eq_add_neg, ← neg_smul, quad_map_add_smul, ha]; ring

/-- **Page 123, (21).** `σ² = id`, because `π(a) = 2`. -/
theorem canSym_canSym (ha : Q a = 1) (x : M) : canSym Q a (canSym Q a x) = x := by
  have h : QuadraticMap.polar Q a a = 2 := piForm_self ha
  simp only [canSym_apply, polar_sub_right, polar_smul_right, h, smul_eq_mul]
  module

/-- For `e` idempotent, `x ↦ x - e π(x) a` preserves `Q` (and fixes `ker π`). -/
theorem isometry_of_idem (ha : Q a = 1) {e : R} (he : IsIdempotentElem e) (x : M) :
    Q (x - (e * QuadraticMap.polar Q a x) • a) = Q x := by
  rw [sub_eq_add_neg, ← neg_smul, quad_map_add_smul, ha]
  have h : e * e = e := he
  linear_combination (QuadraticMap.polar Q a x) ^ 2 * h

/-- **Page 123, the marginal Proposition, over any base.** If `φ` is nondegenerate and `π`
is onto, a linear map fixing `ker π` pointwise and preserving `Q` is `x ↦ x - e π(x) a`
with `e` idempotent (the page's `λ(λ + 1) = 0`, with `e = -λ`). -/
theorem eq_of_isometry_fix (ha : Q a = 1)
    (hnd : ∀ y, (∀ x, QuadraticMap.polar Q y x = 0) → y = 0) {b : M}
    (hb : QuadraticMap.polar Q a b = 1)
    (u : M →ₗ[R] M) (hu : ∀ v, QuadraticMap.polar Q a v = 0 → u v = v) (hQ : ∀ x, Q (u x) = Q x) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ x, u x = x - (e * QuadraticMap.polar Q a x) • a := by
  set c := u b - b with hcdef
  have hux : ∀ x, u x = x + QuadraticMap.polar Q a x • c := by
    intro x
    have h := hu (x - QuadraticMap.polar Q a x • b) (by
      rw [polar_sub_right, polar_smul_right, hb, smul_eq_mul, mul_one, sub_self])
    rw [map_sub, map_smul, sub_eq_iff_eq_add] at h
    rw [h, hcdef, smul_sub]; abel
  have hg : ∀ x, QuadraticMap.polar Q a x *
      (QuadraticMap.polar Q a x * Q c + QuadraticMap.polar Q x c) = 0 := by
    intro x
    have := hQ x
    rw [hux, quad_map_add, QuadraticMap.map_smul, polar_smul_right, smul_eq_mul,
      smul_eq_mul] at this
    linear_combination this
  have hfb : Q c + QuadraticMap.polar Q b c = 0 := by
    have := hg b
    rw [hb] at this
    linear_combination this
  have hf : ∀ x, QuadraticMap.polar Q a x * Q c + QuadraticMap.polar Q x c = 0 := by
    intro x
    have := hg (x + b)
    rw [polar_add_right, hb, polar_add_left] at this
    linear_combination this - hg x - (QuadraticMap.polar Q a x + 1) * hfb
  have h0 : c + Q c • a = 0 := by
    apply hnd
    intro x
    rw [polar_add_left, polar_smul_left, smul_eq_mul, polar_comm Q c x]
    linear_combination hf x
  have hc : c = (-Q c) • a := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
  have hidem : Q c * Q c = Q c := by
    conv_rhs => rw [hc]
    rw [QuadraticMap.map_smul, ha, smul_eq_mul, mul_one, neg_mul_neg]
  refine ⟨Q c, hidem, fun x => ?_⟩
  rw [hux]
  conv_lhs => rw [hc]
  rw [smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- Over a base with no nontrivial idempotent, the isometries fixing `ker π` are `id`
and `σ`. -/
theorem eq_id_or_canSym (ha : Q a = 1)
    (hnd : ∀ y, (∀ x, QuadraticMap.polar Q y x = 0) → y = 0) {b : M}
    (hb : QuadraticMap.polar Q a b = 1)
    (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (u : M →ₗ[R] M) (hu : ∀ v, QuadraticMap.polar Q a v = 0 → u v = v) (hQ : ∀ x, Q (u x) = Q x) :
    u = LinearMap.id ∨ u = canSym Q a := by
  obtain ⟨e, he, hux⟩ := eq_of_isometry_fix ha hnd hb u hu hQ
  rcases hR e he with rfl | rfl
  · left; ext x; rw [hux]; simp
  · right; ext x; rw [hux, canSym_apply, one_mul]

/-- **Page 123.** If `2` is invertible, `a/2 ∈ E = π⁻¹(1)` and on `E` the projective map `σ`
(represented by `-σ`, which preserves `E`) is the symmetry of centre `a/2`. -/
theorem canSym_center [Invertible (2 : R)] (ha : Q a = 1) (x : M)
    (hx : QuadraticMap.polar Q a x = 1) :
    QuadraticMap.polar Q a (⅟(2 : R) • a) = 1 ∧ QuadraticMap.polar Q a (-canSym Q a x) = 1 ∧
      -canSym Q a x - ⅟(2 : R) • a = -(x - ⅟(2 : R) • a) := by
  have h : QuadraticMap.polar Q a a = 2 := piForm_self ha
  refine ⟨?_, ?_, ?_⟩
  · rw [polar_smul_right, h, smul_eq_mul, invOf_mul_self]
  · rw [canSym_apply, polar_neg_right, polar_sub_right, polar_smul_right, hx, h]; norm_num
  · rw [canSym_apply, hx, one_smul]
    rw [show -(x - a) - ⅟(2 : R) • a = -(x - ⅟(2 : R) • a) + (a - (2 : R) • ⅟(2 : R) • a) by
      rw [two_smul]; abel, smul_smul, mul_invOf_self, one_smul, sub_self, add_zero]

/-- **Page 123.** If `2 = 0`, `π(a) = 0`: `a ∈ ker π`, `σ` preserves each level of `π` and
acts on `E` as `x ↦ x - a`; `σ` is the transvection `id - π ⊗ a`. -/
theorem canSym_char_two (h2 : (2 : R) = 0) (ha : Q a = 1) :
    QuadraticMap.polar Q a a = 0 ∧
      (∀ x, QuadraticMap.polar Q a (canSym Q a x) = QuadraticMap.polar Q a x) ∧
      ∀ x, QuadraticMap.polar Q a x = 1 → canSym Q a x = x - a := by
  have h := piForm_self ha
  rw [piForm_apply, h2] at h
  refine ⟨h, fun x => ?_, fun x hx => ?_⟩
  · rw [canSym_apply, polar_sub_right, polar_smul_right, h, smul_zero, sub_zero]
  · rw [canSym_apply, hx, one_smul]

/-- **Page 124.** For `T = M₂(R)`, `q = det`, `a = 1`: `φ(x, 1) = tr x`, so `π` is the trace
(the page has `-tr`, from the opposite polar form). -/
theorem det_polar_one (x : Matrix (Fin 2) (Fin 2) R) :
    (x + 1).det - x.det - (1 : Matrix (Fin 2) (Fin 2) R).det = x.trace := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.det_one, Matrix.trace_fin_two]
  simp
  ring

end Symmetry

end Grothendieck.Folder77

/-!
# Folder 77, pages 89–98: the sphere as the Weil restriction of a conic

Finding `77-affine-quadric-weil-restriction` (issue #54), coordinate statement. The special
quadratic module `E` of rank `3` is the pure part of a quaternion algebra `(a, b)` over a field
`K` of characteristic `≠ 2`, `q(u) = u² = a u₁² + b u₂² - ab u₃²` (`M₂`, `q = -det`, for
`a = b = 1`). Proved: `qf_commutator` (21 bis), `q([x, y]) = -4q(x)q(y) + φ(x, y)²`;
`ftilde_mem`, `act_mem`, `ftilde_surjective`, `ftilde_fibre`, gathered in `sphere_quotient`:
`x + iy ↦ [x, y]/2q(x)` maps `Ũ` (`q(x) = q(y)` invertible, `φ(x, y) = 0`) onto `Σ : q = -1`,
with fibres the orbits of `c + id`, `c² + d² ≠ 0`; and `hors_de_U`, the lemma of page 98: an
isotropic `x + iy` with `q(x) = 0` is `(c + id)x₀`, `x₀` isotropic, so `X^{S[i]} ∖ X = U`.
The inverse is explicit: `t ↦ x - i tx` for any `x ⟂ t` with `q(x) ≠ 0`, and every `y` with
`(x, y) ∈ Ũ` is `-tx` (`ftilde_facts`). Monomorphism and epimorphism use only that `t`, `x`, `tx`
form an orthogonal basis of the pure part (`eq_zero_of_anticomm`, `exists_perp`), no étale
localisation. The scheme-level statement and the twisted version (pp. 102–116) are not
formalised.
-/

namespace Grothendieck.Folder77

section QuadriqueAffine

open Quaternion

variable {K : Type*} [Field K] {a b : K}

/-- The quadratic form `q(u) = u²` on the pure quaternions of `(a, b)`:
`q = a u₁² + b u₂² - ab u₃²`. On `M₂` (`a = b = 1`) it is `-det`. -/
def qf (u : ℍ[K,a,b]) : K := a * u.imI ^ 2 + b * u.imJ ^ 2 - a * b * u.imK ^ 2

/-- Its polar form `φ(u, v) = q(u + v) - q(u) - q(v)`. -/
def pol (u v : ℍ[K,a,b]) : K :=
  2 * (a * u.imI * v.imI + b * u.imJ * v.imJ - a * b * u.imK * v.imK)

theorem mul_self_of_pure {u : ℍ[K,a,b]} (hu : u.re = 0) :
    u * u = ((qf u : K) : ℍ[K,a,b]) := by
  rw [show ((qf u : K) : ℍ[K,a,b]) = ⟨qf u, 0, 0, 0⟩ from rfl]
  ext <;> simp [qf, hu] <;> ring

theorem mul_add_mul_of_pure {u v : ℍ[K,a,b]} (hu : u.re = 0) (hv : v.re = 0) :
    u * v + v * u = ((pol u v : K) : ℍ[K,a,b]) := by
  rw [show ((pol u v : K) : ℍ[K,a,b]) = ⟨pol u v, 0, 0, 0⟩ from rfl]
  ext <;> simp [pol, hu, hv] <;> ring

theorem re_mul_of_pure {u v : ℍ[K,a,b]} (hu : u.re = 0) (hv : v.re = 0) :
    2 * (u * v).re = pol u v := by
  simp [pol, hu, hv]

theorem pol_comm (u v : ℍ[K,a,b]) : pol u v = pol v u := by
  simp only [pol]; ring

theorem pol_self (u : ℍ[K,a,b]) : pol u u = 2 * qf u := by
  simp only [pol, qf]; ring

theorem pol_sub_smul (u v w z : ℍ[K,a,b]) (c d : K) :
    pol (u - c • v - d • w) z = pol u z - c * pol v z - d * pol w z := by
  simp [pol]; ring

theorem pol_neg_right (u v : ℍ[K,a,b]) : pol u (-v) = -pol u v := by
  simp [pol]; ring

theorem qf_neg (u : ℍ[K,a,b]) : qf (-u) = qf u := by
  simp [qf]

theorem qf_smul (c : K) (u : ℍ[K,a,b]) : qf (c • u) = c ^ 2 * qf u := by
  simp [qf]; ring

theorem qf_smul_add_smul (c d : K) (u v : ℍ[K,a,b]) :
    qf (c • u + d • v) = c ^ 2 * qf u + d ^ 2 * qf v + c * d * pol u v := by
  simp [qf, pol]; ring

theorem re_commutator {x y : ℍ[K,a,b]} (hx : x.re = 0) (hy : y.re = 0) :
    (x * y - y * x).re = 0 := by
  simp [hx, hy]; ring

/-- **(21 bis)**: `q([x, y]) = -4 q(x) q(y) + φ(x, y)²`. -/
theorem qf_commutator {x y : ℍ[K,a,b]} (hx : x.re = 0) (hy : y.re = 0) :
    qf (x * y - y * x) = -4 * qf x * qf y + pol x y ^ 2 := by
  simp [qf, pol, hx, hy]; ring

theorem anticomm {u v : ℍ[K,a,b]} (hu : u.re = 0) (hv : v.re = 0) (h : pol u v = 0) :
    v * u = -(u * v) := by
  have := mul_add_mul_of_pure hu hv
  rw [h, QuaternionAlgebra.coe_zero] at this
  exact eq_neg_of_add_eq_zero_right this

/-- `Σ`, the affine quadric `q = -1`: pure quaternions `t` with `t² = -1`. -/
def Sphere : Set ℍ[K,a,b] := {t | t.re = 0 ∧ qf t = -1}

/-- `Ũ`: the pairs `(x, y)` of pure quaternions such that `x + iy` is isotropic
(`q(x) = q(y)`, `φ(x, y) = 0`) with `q(x)` invertible. -/
def Utilde : Set (ℍ[K,a,b] × ℍ[K,a,b]) :=
  {ξ | ξ.1.re = 0 ∧ ξ.2.re = 0 ∧ qf ξ.1 = qf ξ.2 ∧ pol ξ.1 ξ.2 = 0 ∧ qf ξ.1 ≠ 0}

/-- `f̃(x + iy) = [x, y]/2q(x)`. -/
noncomputable def ftilde (ξ : ℍ[K,a,b] × ℍ[K,a,b]) : ℍ[K,a,b] :=
  (2 * qf ξ.1)⁻¹ • (ξ.1 * ξ.2 - ξ.2 * ξ.1)

/-- The action of `α = c + id`: `α(x + iy) = (cx - dy) + i(dx + cy)`. -/
def act (c d : K) (ξ : ℍ[K,a,b] × ℍ[K,a,b]) : ℍ[K,a,b] × ℍ[K,a,b] :=
  (c • ξ.1 - d • ξ.2, d • ξ.1 + c • ξ.2)

/-- `f̃` lands in `Σ`. -/
theorem ftilde_mem (h2 : (2 : K) ≠ 0) {ξ : ℍ[K,a,b] × ℍ[K,a,b]} (hξ : ξ ∈ Utilde) :
    ftilde ξ ∈ Sphere := by
  obtain ⟨hx, hy, hq, hp, h0⟩ := hξ
  refine ⟨by simp [ftilde, re_commutator hx hy], ?_⟩
  rw [ftilde, qf_smul, qf_commutator hx hy, hp, ← hq]
  field_simp
  ring

/-- `Ũ` is stable under `𝔾_m^{S[i]}`, and `f̃` is invariant. -/
theorem act_mem {c d : K} (hcd : c ^ 2 + d ^ 2 ≠ 0) {ξ : ℍ[K,a,b] × ℍ[K,a,b]}
    (hξ : ξ ∈ Utilde) : act c d ξ ∈ Utilde ∧ ftilde (act c d ξ) = ftilde ξ := by
  obtain ⟨hx, hy, hq, hp, h0⟩ := hξ
  have hq1 : qf (c • ξ.1 - d • ξ.2) = (c ^ 2 + d ^ 2) * qf ξ.1 := by
    rw [sub_eq_add_neg, ← neg_smul, qf_smul_add_smul, hp, ← hq]; ring
  have hq2 : qf (d • ξ.1 + c • ξ.2) = (c ^ 2 + d ^ 2) * qf ξ.1 := by
    rw [qf_smul_add_smul, hp, ← hq]; ring
  have hp' : pol (c • ξ.1 - d • ξ.2) (d • ξ.1 + c • ξ.2) = 0 := by
    simp only [pol, qf] at hp hq ⊢
    simp only [QuaternionAlgebra.imI_sub, QuaternionAlgebra.imI_add, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_sub, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imJ_smul,
      QuaternionAlgebra.imK_sub, QuaternionAlgebra.imK_add, QuaternionAlgebra.imK_smul,
      smul_eq_mul]
    linear_combination (c ^ 2 - d ^ 2) * hp + 2 * c * d * hq
  have hcomm : (c • ξ.1 - d • ξ.2) * (d • ξ.1 + c • ξ.2) - (d • ξ.1 + c • ξ.2) *
      (c • ξ.1 - d • ξ.2) = (c ^ 2 + d ^ 2) • (ξ.1 * ξ.2 - ξ.2 * ξ.1) := by
    ext <;> simp <;> ring
  refine ⟨⟨by simp [act, hx, hy], by simp [act, hx, hy], by rw [act, hq1, hq2], hp',
    by rw [act, hq1]; exact mul_ne_zero hcd h0⟩, ?_⟩
  simp only [ftilde, act]
  rw [hq1, hcomm, smul_smul]
  congr 1
  field_simp

theorem coe_inj {u v : K} (h : ((u : K) : ℍ[K,a,b]) = (v : K)) : u = v :=
  QuaternionAlgebra.coe_injective h

theorem re_eq_zero_of_two_mul {u : K} (h2 : (2 : K) ≠ 0) (h : 2 * u = 0) : u = 0 :=
  (mul_eq_zero.1 h).resolve_left h2

/-- For `t ∈ Σ` and a pure `x ⟂ t`: `tx` is pure, `x` anticommutes with `t`, and
`(tx)² = q(x)`. -/
theorem perp_facts (h2 : (2 : K) ≠ 0) {t x : ℍ[K,a,b]} (ht : t ∈ Sphere) (hx : x.re = 0)
    (hxt : pol x t = 0) :
    (t * x).re = 0 ∧ x * t = -(t * x) ∧ qf (t * x) = qf x := by
  have htx : (t * x).re = 0 :=
    re_eq_zero_of_two_mul h2 (by rw [re_mul_of_pure ht.1 hx, pol_comm, hxt])
  have hac : x * t = -(t * x) := anticomm ht.1 hx (by rw [pol_comm, hxt])
  refine ⟨htx, hac, coe_inj (a := a) (b := b) ?_⟩
  rw [← mul_self_of_pure htx, ← mul_self_of_pure hx]
  calc t * x * (t * x) = t * (x * t) * x := by noncomm_ring
    _ = -((t * t) * (x * x)) := by rw [hac]; noncomm_ring
    _ = x * x := by
      rw [mul_self_of_pure ht.1, ht.2, mul_self_of_pure hx]; simp

/-- In a quaternion algebra, a pure `r` anticommuting with `t`, `x` and `tx` (with `x ⟂ t`,
`t² = -1`, `q(x) ≠ 0`) is `0`: the three are an orthogonal basis of the pure part. -/
theorem eq_zero_of_anticomm (h2 : (2 : K) ≠ 0) {r t x : ℍ[K,a,b]} (ht : t ∈ Sphere)
    (hx : x.re = 0) (hxt : pol x t = 0) (hq : qf x ≠ 0)
    (h1 : r * t = -(t * r)) (h3 : r * x = -(x * r)) (h4 : r * (t * x) = -((t * x) * r)) :
    r = 0 := by
  obtain ⟨htx, hac, hqtx⟩ := perp_facts h2 ht hx hxt
  have e : r * (t * x) = t * x * r := by
    calc r * (t * x) = (r * t) * x := by noncomm_ring
      _ = -(t * (r * x)) := by rw [h1]; noncomm_ring
      _ = t * x * r := by rw [h3]; noncomm_ring
  have e2 : (2 * qf x : K) • r = 0 := by
    have h5 : t * x * r = -(t * x * r) := e.symm.trans h4
    have h6 := congrArg (fun z => (t * x) * z) h5
    simp only [mul_neg] at h6
    rw [← mul_assoc (t * x) (t * x) r] at h6
    rw [mul_self_of_pure htx, hqtx, QuaternionAlgebra.coe_mul_eq_smul] at h6
    rw [mul_smul, two_smul]
    exact eq_neg_iff_add_eq_zero.1 h6
  exact (smul_eq_zero.1 e2).resolve_left (mul_ne_zero h2 hq)

/-- For `ξ = (x, y) ∈ Ũ` and `t = f̃(ξ)`: `x ⟂ t` and `y = -tx`. -/
theorem ftilde_facts (h2 : (2 : K) ≠ 0) {ξ : ℍ[K,a,b] × ℍ[K,a,b]} (hξ : ξ ∈ Utilde) :
    pol ξ.1 (ftilde ξ) = 0 ∧ ξ.2 = -(ftilde ξ * ξ.1) := by
  obtain ⟨hx, hy, hq, hp, h0⟩ := hξ
  have hyx := anticomm hx hy hp
  have hxx := mul_self_of_pure hx
  have k1 : (ξ.1 * ξ.2 - ξ.2 * ξ.1) * ξ.1 = -((2 * qf ξ.1 : K) • ξ.2) := by
    calc (ξ.1 * ξ.2 - ξ.2 * ξ.1) * ξ.1 = ξ.1 * (ξ.2 * ξ.1) - ξ.2 * (ξ.1 * ξ.1) := by
          noncomm_ring
      _ = -((ξ.1 * ξ.1) * ξ.2) - ξ.2 * (ξ.1 * ξ.1) := by rw [hyx]; noncomm_ring
      _ = _ := by
        rw [hxx, QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_commutes,
          QuaternionAlgebra.coe_mul_eq_smul, mul_smul, two_smul]; abel
  have k2 : ξ.1 * (ξ.1 * ξ.2 - ξ.2 * ξ.1) = (2 * qf ξ.1 : K) • ξ.2 := by
    calc ξ.1 * (ξ.1 * ξ.2 - ξ.2 * ξ.1) = (ξ.1 * ξ.1) * ξ.2 - ξ.1 * (ξ.2 * ξ.1) := by
          noncomm_ring
      _ = (ξ.1 * ξ.1) * ξ.2 + (ξ.1 * ξ.1) * ξ.2 := by rw [hyx]; noncomm_ring
      _ = _ := by rw [hxx, QuaternionAlgebra.coe_mul_eq_smul, mul_smul, two_smul]
  have h20 : (2 * qf ξ.1 : K) ≠ 0 := mul_ne_zero h2 h0
  have htx : ftilde ξ * ξ.1 = -ξ.2 := by
    rw [ftilde, smul_mul_assoc, k1, smul_neg, smul_smul, inv_mul_cancel₀ h20, one_smul]
  have hxt : ξ.1 * ftilde ξ = ξ.2 := by
    rw [ftilde, mul_smul_comm, k2, smul_smul, inv_mul_cancel₀ h20, one_smul]
  refine ⟨coe_inj (a := a) (b := b) ?_, by rw [htx, neg_neg]⟩
  have hft : (ftilde ξ).re = 0 := by simp [ftilde, re_commutator hx hy]
  rw [← mul_add_mul_of_pure hx hft, hxt, htx, add_neg_cancel, QuaternionAlgebra.coe_zero]

/-- A pure `x ⟂ t` with `q(x) ≠ 0` exists for every `t ∈ Σ`: among the projections of
`i`, `j`, `k` on `t^⊥`, one is anisotropic, since otherwise `q(t) = -3`. -/
theorem exists_perp (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {t : ℍ[K,a,b]}
    (ht : t ∈ Sphere) : ∃ x : ℍ[K,a,b], x.re = 0 ∧ pol x t = 0 ∧ qf x ≠ 0 := by
  obtain ⟨ht0, ht1⟩ := ht
  have hqt : a * t.imI ^ 2 + b * t.imJ ^ 2 - a * b * t.imK ^ 2 = -1 := ht1
  let xi : ℍ[K,a,b] := ⟨0, 1 + a * t.imI ^ 2, a * t.imI * t.imJ, a * t.imI * t.imK⟩
  let xj : ℍ[K,a,b] := ⟨0, b * t.imJ * t.imI, 1 + b * t.imJ ^ 2, b * t.imJ * t.imK⟩
  let xk : ℍ[K,a,b] := ⟨0, -(a * b) * t.imK * t.imI, -(a * b) * t.imK * t.imJ,
    1 - a * b * t.imK ^ 2⟩
  have pi : pol xi t = 0 := by
    simp only [pol, xi]; linear_combination 2 * a * t.imI * hqt
  have pj : pol xj t = 0 := by
    simp only [pol, xj]; linear_combination 2 * b * t.imJ * hqt
  have pk : pol xk t = 0 := by
    simp only [pol, xk]; linear_combination -2 * a * b * t.imK * hqt
  have qi : qf xi = a * (1 + a * t.imI ^ 2) := by
    simp only [qf, xi]; linear_combination a ^ 2 * t.imI ^ 2 * hqt
  have qj : qf xj = b * (1 + b * t.imJ ^ 2) := by
    simp only [qf, xj]; linear_combination b ^ 2 * t.imJ ^ 2 * hqt
  have qk : qf xk = -(a * b) * (1 - a * b * t.imK ^ 2) := by
    simp only [qf, xk]; linear_combination a ^ 2 * b ^ 2 * t.imK ^ 2 * hqt
  by_cases hi : qf xi = 0
  · by_cases hj : qf xj = 0
    · by_cases hk : qf xk = 0
      · rw [qi] at hi; rw [qj] at hj; rw [qk] at hk
        have e1 := (mul_eq_zero.1 hi).resolve_left ha
        have e2 := (mul_eq_zero.1 hj).resolve_left hb
        have e3 := (mul_eq_zero.1 hk).resolve_left (neg_ne_zero.2 (mul_ne_zero ha hb))
        exact absurd (by linear_combination e1 + e2 + e3 - hqt) h2
      · exact ⟨xk, rfl, pk, hk⟩
    · exact ⟨xj, rfl, pj, hj⟩
  · exact ⟨xi, rfl, pi, hi⟩

/-- **Page 95–97, épimorphisme.** Every `t ∈ Σ` is `f̃(x + iy)` for some `(x, y) ∈ Ũ`:
take a pure `x ⟂ t` with `q(x) ≠ 0` and `y = -tx`. -/
theorem ftilde_surjective (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {t : ℍ[K,a,b]}
    (ht : t ∈ Sphere) : ∃ ξ ∈ Utilde, ftilde ξ = t := by
  obtain ⟨x, hx, hxt, hq⟩ := exists_perp h2 ha hb ht
  obtain ⟨htx, hac, hqtx⟩ := perp_facts h2 ht hx hxt
  have hp : pol x (-(t * x)) = 0 := by
    rw [pol_neg_right, neg_eq_zero]
    refine coe_inj (a := a) (b := b) ?_
    rw [← mul_add_mul_of_pure hx htx, ← mul_assoc, hac, neg_mul, neg_add_cancel,
      QuaternionAlgebra.coe_zero]
  refine ⟨(x, -(t * x)), ⟨hx, by simp [htx], by simp [qf_neg, hqtx], hp, hq⟩, ?_⟩
  have hc : x * -(t * x) - -(t * x) * x = (2 * qf x : K) • t := by
    calc x * -(t * x) - -(t * x) * x = -((x * t) * x) + t * (x * x) := by noncomm_ring
      _ = t * (x * x) + t * (x * x) := by rw [hac]; noncomm_ring
      _ = _ := by
        rw [mul_self_of_pure hx, QuaternionAlgebra.mul_coe_eq_smul, mul_smul, two_smul]
  simp only [ftilde]
  rw [hc, smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 hq), one_smul]

/-- **Pages 94–96, monomorphisme.** Two points of `Ũ` with the same image under `f̃` differ by
the action of some `α = c + id`, `c² + d² ≠ 0`. -/
theorem ftilde_fibre (h2 : (2 : K) ≠ 0) {ξ ξ' : ℍ[K,a,b] × ℍ[K,a,b]} (hξ : ξ ∈ Utilde)
    (hξ' : ξ' ∈ Utilde) (h : ftilde ξ' = ftilde ξ) :
    ∃ c d : K, c ^ 2 + d ^ 2 ≠ 0 ∧ ξ' = act c d ξ := by
  set t := ftilde ξ with ht_def
  have ht : t ∈ Sphere := ftilde_mem h2 hξ
  obtain ⟨hxt, hy⟩ := ftilde_facts h2 hξ
  obtain ⟨hxt', hy'⟩ := ftilde_facts h2 hξ'
  rw [h] at hxt' hy'
  obtain ⟨hx, -, -, -, hq⟩ := hξ
  obtain ⟨hx', -, -, -, hq'⟩ := hξ'
  obtain ⟨htx, hac, hqtx⟩ := perp_facts h2 ht hx hxt
  have htt : t * t = -1 := by rw [mul_self_of_pure ht.1, ht.2]; simp
  set x := ξ.1
  set x' := ξ'.1
  have h20 : (2 * qf x : K) ≠ 0 := mul_ne_zero h2 hq
  set c := pol x x' / (2 * qf x) with hc
  set d := pol (t * x) x' / (2 * qf x) with hd
  have p1 : pol (t * x) t = 0 := by
    refine coe_inj (a := a) (b := b) ?_
    rw [← mul_add_mul_of_pure htx ht.1, QuaternionAlgebra.coe_zero, mul_assoc, hac, mul_neg,
      ← mul_assoc, neg_add_cancel]
  have p2 : pol (t * x) x = 0 := by
    refine coe_inj (a := a) (b := b) ?_
    rw [← mul_add_mul_of_pure htx hx, QuaternionAlgebra.coe_zero, ← mul_assoc, hac, neg_mul,
      mul_assoc, add_neg_cancel]
  set r := x' - c • x - d • (t * x) with hr_def
  have hr : r.re = 0 := by simp [r, hx, hx', htx]
  have prt : pol r t = 0 := by
    rw [pol_sub_smul, hxt', hxt, p1]; ring
  have prx : pol r x = 0 := by
    rw [pol_sub_smul, pol_self, p2, pol_comm x' x, hc]; field_simp; ring
  have prtx : pol r (t * x) = 0 := by
    rw [pol_sub_smul, pol_self, hqtx, pol_comm x (t * x), p2, pol_comm x' (t * x), hd]
    field_simp; ring
  have hr0 : r = 0 := eq_zero_of_anticomm h2 ht hx hxt hq
    (anticomm ht.1 hr (by rw [pol_comm]; exact prt))
    (anticomm hx hr (by rw [pol_comm]; exact prx))
    (anticomm htx hr (by rw [pol_comm]; exact prtx))
  have hx'eq : x' = c • x + d • (t * x) := by
    rwa [hr_def, sub_sub, sub_eq_zero] at hr0
  have hqx' : qf x' = (c ^ 2 + d ^ 2) * qf x := by
    rw [hx'eq, qf_smul_add_smul, hqtx, pol_comm, p2]; ring
  refine ⟨c, d, fun h0 => hq' (by rw [hqx', h0, zero_mul]), ?_⟩
  refine Prod.ext ?_ ?_
  · change x' = c • x - d • ξ.2
    rw [hy, hx'eq, smul_neg, sub_neg_eq_add]
  · change ξ'.2 = d • x + c • ξ.2
    rw [hy', hy, hx'eq, mul_add, mul_smul_comm, mul_smul_comm, ← mul_assoc, htt, neg_one_mul,
      smul_neg, smul_neg]
    abel

/-- For a ternary diagonal form `⟨d₁, d₂, d₃⟩` with `dᵢ ≠ 0`: if `x` is isotropic with
`x₁ ≠ 0` and `z ⟂ x` is isotropic with `z₁ = 0`, then `z = 0`. -/
theorem diag_aux {d₁ d₂ d₃ x₁ x₂ x₃ z₂ z₃ : K} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0)
    (hx : x₁ ≠ 0) (hC : d₁ * x₁ ^ 2 + d₂ * x₂ ^ 2 + d₃ * x₃ ^ 2 = 0)
    (hB : d₂ * x₂ * z₂ + d₃ * x₃ * z₃ = 0) (hA : d₂ * z₂ ^ 2 + d₃ * z₃ ^ 2 = 0) :
    z₂ = 0 ∧ z₃ = 0 := by
  have e : d₁ * d₃ * x₁ ^ 2 * z₃ ^ 2 = 0 := by
    linear_combination d₃ * z₃ ^ 2 * hC - (d₃ * x₃ * z₃ - d₂ * x₂ * z₂) * hB - d₂ * x₂ ^ 2 * hA
  have hz₃ : z₃ = 0 := by
    simpa [h₁, h₃, hx] using e
  refine ⟨?_, hz₃⟩
  rw [hz₃] at hA
  simpa [h₂] using hA

/-- **Page 98, the lemma.** Over a field of characteristic `≠ 2`, a nonzero isotropic
`x + iy` (`q(x) = q(y)`, `φ(x, y) = 0`) outside `Ũ` (`q(x) = 0`) is `(c + id) x₀` with `x₀`
isotropic: a real point. So `X^{S[i]} ∖ X` is the open set `q(x) ≠ 0`. -/
theorem hors_de_U (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {x y : ℍ[K,a,b]}
    (hx : x.re = 0) (hy : y.re = 0) (hq : qf x = qf y) (hp : pol x y = 0) (h0 : qf x = 0) :
    ∃ x₀ : ℍ[K,a,b], x₀.re = 0 ∧ qf x₀ = 0 ∧ ∃ c d : K, x = c • x₀ ∧ y = d • x₀ := by
  by_cases hx0 : x = 0
  · exact ⟨y, hy, hq ▸ h0, 0, 1, by simp [hx0], by simp⟩
  suffices key : ∃ l : K, y = l • x by
    obtain ⟨l, hl⟩ := key
    exact ⟨x, hx, h0, 1, l, by simp, hl⟩
  have hxne : x.imI ≠ 0 ∨ x.imJ ≠ 0 ∨ x.imK ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (QuaternionAlgebra.ext hx hc.1 hc.2.1 hc.2.2)
  have hqx : a * x.imI ^ 2 + b * x.imJ ^ 2 + -(a * b) * x.imK ^ 2 = 0 := by
    have := h0; simp only [qf] at this; linear_combination this
  have hqy : a * y.imI ^ 2 + b * y.imJ ^ 2 + -(a * b) * y.imK ^ 2 = 0 := by
    have := hq ▸ h0; simp only [qf] at this; linear_combination this
  have hpxy : a * x.imI * y.imI + b * x.imJ * y.imJ + -(a * b) * x.imK * y.imK = 0 := by
    have := hp; simp only [pol] at this
    have := (mul_eq_zero.1 this).resolve_left h2
    linear_combination this
  have hab : -(a * b) ≠ 0 := neg_ne_zero.2 (mul_ne_zero ha hb)
  rcases hxne with h1 | h1 | h1
  · set l := y.imI / x.imI
    have hz : y.imI - l * x.imI = 0 := by simp [l, div_mul_cancel₀ _ h1]
    obtain ⟨e2, e3⟩ := diag_aux (x₂ := x.imJ) (x₃ := x.imK) (z₂ := y.imJ - l * x.imJ)
      (z₃ := y.imK - l * x.imK) ha hb hab h1 hqx
      (by linear_combination hpxy - l * hqx - a * x.imI * hz)
      (by linear_combination hqy - 2 * l * hpxy + l ^ 2 * hqx - a * (y.imI - l * x.imI) * hz)
    exact ⟨l, QuaternionAlgebra.ext (by simp [hx, hy]) (by simp; linear_combination hz)
      (by simp; linear_combination e2) (by simp; linear_combination e3)⟩
  · set l := y.imJ / x.imJ
    have hz : y.imJ - l * x.imJ = 0 := by simp [l, div_mul_cancel₀ _ h1]
    obtain ⟨e2, e3⟩ := diag_aux (x₂ := x.imI) (x₃ := x.imK) (z₂ := y.imI - l * x.imI)
      (z₃ := y.imK - l * x.imK) hb ha hab h1 (by linear_combination hqx)
      (by linear_combination hpxy - l * hqx - b * x.imJ * hz)
      (by linear_combination hqy - 2 * l * hpxy + l ^ 2 * hqx - b * (y.imJ - l * x.imJ) * hz)
    exact ⟨l, QuaternionAlgebra.ext (by simp [hx, hy]) (by simp; linear_combination e2)
      (by simp; linear_combination hz) (by simp; linear_combination e3)⟩
  · set l := y.imK / x.imK
    have hz : y.imK - l * x.imK = 0 := by simp [l, div_mul_cancel₀ _ h1]
    obtain ⟨e2, e3⟩ := diag_aux (x₂ := x.imI) (x₃ := x.imJ) (z₂ := y.imI - l * x.imI)
      (z₃ := y.imJ - l * x.imJ) hab ha hb h1 (by linear_combination hqx)
      (by linear_combination hpxy - l * hqx + a * b * x.imK * hz)
      (by linear_combination hqy - 2 * l * hpxy + l ^ 2 * hqx +
        a * b * (y.imK - l * x.imK) * hz)
    exact ⟨l, QuaternionAlgebra.ext (by simp [hx, hy]) (by simp; linear_combination e2)
      (by simp; linear_combination e3) (by simp; linear_combination hz)⟩

/-- **Pages 94–98, the coordinate statement.** For a quaternion algebra `(a, b)` over a field of
characteristic `≠ 2` (the twisted quaternion algebra `M` of the reading, its pure part the
special quadratic module `E` of rank `3`, `q(u) = u²`), the map
`x + iy ↦ [x, y]/2q(x)` sends `Ũ` onto the affine quadric `Σ : q = -1`, and its fibres are
exactly the orbits of `α = c + id`, `c² + d² ≠ 0`: `Σ ≅ Ũ/𝔾_m^{S[i]}`. -/
theorem sphere_quotient (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ ξ ∈ (Utilde : Set (ℍ[K,a,b] × ℍ[K,a,b])), ftilde ξ ∈ Sphere) ∧
      (∀ t ∈ (Sphere : Set ℍ[K,a,b]), ∃ ξ ∈ Utilde, ftilde ξ = t) ∧
      ∀ ξ ∈ (Utilde : Set (ℍ[K,a,b] × ℍ[K,a,b])), ∀ ξ' ∈ Utilde,
        ftilde ξ' = ftilde ξ ↔ ∃ c d : K, c ^ 2 + d ^ 2 ≠ 0 ∧ ξ' = act c d ξ :=
  ⟨fun _ hξ => ftilde_mem h2 hξ, fun _ ht => ftilde_surjective h2 ha hb ht,
    fun _ hξ _ hξ' => ⟨ftilde_fibre h2 hξ hξ', fun ⟨_, _, hcd, he⟩ => he ▸ (act_mem hcd hξ).2⟩⟩

end QuadriqueAffine

end Grothendieck.Folder77


/-!
## Page 85: condition c) without « étale » does not imply a)

The Proposition of page 85 (`A` noetherian, `2` regular, `A/2A` a normal domain, `Δ ∉ 2A`)
states a) `Δ = b² − 4c`, b) and c) « il existe une extension finie de `A_Δ` qui redonne
`A_{2Δ}[U]/(U² − Δ)` quand on inverse `2` », the word « étale » struck on the page. The reading
restores « finie étale ». As the page writes it, c) does not imply a): for `A = ℤ`, `Δ = 3`,
`B_Δ = ℤ[1/3][U]/(U² − 3)` is finite and free of rank `2`, inverting `2` gives
`ℤ[1/6][U]/(U² − 3)`, and `3 ≠ b² − 4c` since `b² − 4c ≡ 0, 1 (mod 4)`. This is finding
`77-discriminant-extension-across-2`. That `B_Δ` is not étale over `ℤ[1/3]` (it ramifies at `2`),
and the Proposition with « finie étale », are not formalised.
-/

namespace Grothendieck.Folder77

section ExtensionAcrossTwo

open Polynomial

variable {R : Type*} [CommRing R]

/-- The quadratic algebra `R[U]/(U² − d)`. -/
abbrev quadAlg (d : R) : Type _ := AdjoinRoot (X ^ 2 - C d : R[X])

theorem quadAlg_monic (d : R) : (X ^ 2 - C d : R[X]).Monic := monic_X_pow_sub_C _ two_ne_zero

instance (d : R) : Module.Finite R (quadAlg d) := (AdjoinRoot.powerBasis' (quadAlg_monic d)).finite

instance (d : R) : Module.Free R (quadAlg d) :=
  .of_basis (AdjoinRoot.powerBasis' (quadAlg_monic d)).basis

theorem finrank_quadAlg [Nontrivial R] (d : R) : Module.finrank R (quadAlg d) = 2 := by
  simp [(AdjoinRoot.powerBasis' (quadAlg_monic d)).finrank, AdjoinRoot.powerBasis']

/-- Inverting `s` commutes with forming `R[U]/(U² − d)`:
`(R[U]/(U² − d))_s ≅ R_s[U]/(U² − d)`. -/
theorem quadAlg_away (d s : R) :
    Nonempty (Localization.Away (algebraMap R (quadAlg d) s) ≃+*
      quadAlg (algebraMap R (Localization.Away s) d)) := by
  set B := quadAlg d
  set Rs := Localization.Away s
  set Bs := Localization.Away (algebraMap R B s)
  let g := AdjoinRoot.map (algebraMap R Rs) _ _
    (show (X ^ 2 - C (algebraMap R Rs d)) ∣ (X ^ 2 - C d : R[X]).map (algebraMap R Rs) by simp)
  have hg : ∀ r : R, g (algebraMap R B r) = AdjoinRoot.of _ (algebraMap R Rs r) := fun r => by
    show g (AdjoinRoot.of _ r) = _
    simp [g, AdjoinRoot.map]
  have hgu : IsUnit (g (algebraMap R B s)) :=
    hg s ▸ (IsLocalization.Away.algebraMap_isUnit s).map _
  let ψ : Bs →+* quadAlg (algebraMap R Rs d) := IsLocalization.Away.lift _ hgu
  let i : Rs →+* Bs := IsLocalization.Away.map Rs Bs (algebraMap R B) s
  have hi : ∀ r : R, i (algebraMap R Rs r) = algebraMap B Bs (algebraMap R B r) := fun r =>
    IsLocalization.map_eq _ _
  have h0 : (AdjoinRoot.root (X ^ 2 - C d) : B) ^ 2 - algebraMap R B d = 0 := by
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X, ← map_pow, ← map_sub,
      AdjoinRoot.mk_self]
  have hroot : (X ^ 2 - C (algebraMap R Rs d)).eval₂ i
      (algebraMap B Bs (AdjoinRoot.root _)) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hi, ← map_pow, ← map_sub, h0, map_zero]
  let φ : quadAlg (algebraMap R Rs d) →+* Bs := AdjoinRoot.lift i _ hroot
  have hψ : ∀ x : B, ψ (algebraMap B Bs x) = g x := fun x => IsLocalization.Away.lift_eq _ _ x
  have key : ψ.comp i = AdjoinRoot.of _ :=
    IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun r => by simp [hi, hψ, hg])
  refine ⟨RingEquiv.ofRingHom ψ φ ?_ ?_⟩
  · refine Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_)
    · show ψ (φ (AdjoinRoot.of _ a)) = AdjoinRoot.of _ a
      rw [AdjoinRoot.lift_of]
      exact RingHom.congr_fun key a
    · show ψ (φ (AdjoinRoot.root _)) = AdjoinRoot.root _
      simp [φ, hψ, g, AdjoinRoot.map]
  · refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R B s))
      (Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_))
    · show φ (ψ (algebraMap B Bs (algebraMap R B a))) = algebraMap B Bs (algebraMap R B a)
      rw [hψ, hg, AdjoinRoot.lift_of, hi]
    · show φ (ψ (algebraMap B Bs (AdjoinRoot.root _))) = algebraMap B Bs (AdjoinRoot.root _)
      simp [hψ, g, AdjoinRoot.map, φ]

/-- `3` is not of the form `b² − 4c` in `ℤ`: `b² − 4c ≡ 0` or `1 (mod 4)`. -/
theorem sq_sub_four_mul_ne_three (b c : ℤ) : b ^ 2 - 4 * c ≠ 3 := by
  intro h
  have h' := congrArg (Int.cast : ℤ → ZMod 4) h
  push_cast at h'
  generalize (b : ZMod 4) = x at h'
  generalize (c : ZMod 4) = y at h'
  revert x y; decide

end ExtensionAcrossTwo

section ExtensionAcrossTwoExample

/-- `ℤ[1/3]`. -/
abbrev Z3 : Type := Localization.Away (3 : ℤ)

/-- `ℤ[1/3]` is not the zero ring. -/
instance : Nontrivial Z3 :=
  (IsLocalization.Away.lift (S := Z3) (3 : ℤ) (g := Int.castRingHom ℚ)
    (isUnit_iff_ne_zero.mpr (by norm_num))).domain_nontrivial

/-- `ℤ[1/6]`, as `ℤ[1/3][1/2]`. -/
abbrev Z6 : Type := Localization.Away (2 : Z3)

/-- `B_Δ = ℤ[1/3][U]/(U² − 3)`. -/
abbrev B3 : Type := quadAlg (3 : Z3)

/-- `A_{2Δ}[U]/(U² − Δ) = ℤ[1/6][U]/(U² − 3)`. -/
abbrev C6 : Type := quadAlg (3 : Z6)

/-- **Page 85, condition c) without « étale ».** For `A = ℤ`, `Δ = 3` (`2` regular, `A/2A` a
field, `Δ ∉ 2A`), `B_Δ = ℤ[1/3][U]/(U² − 3)` is finite (free of rank `2`) over `A_Δ = ℤ[1/3]`,
and inverting `2` gives `A_{2Δ}[U]/(U² − Δ)`; yet `Δ ≠ b² − 4c` for all `b, c ∈ ℤ`. So c),
with « étale » struck as on the page, does not imply a). -/
theorem extension_across_two_counterexample :
    ¬ (2 : ℤ) ∣ 3 ∧ Module.Finite Z3 B3 ∧ Module.Free Z3 B3 ∧ Module.finrank Z3 B3 = 2 ∧
      Nonempty (Localization.Away (algebraMap Z3 B3 2) ≃+* C6) ∧
      ¬ ∃ b c : ℤ, b ^ 2 - 4 * c = 3 :=
  ⟨by decide, inferInstance, inferInstance, finrank_quadAlg _, (quadAlg_away (3 : Z3) (2 : Z3)).map fun e =>
      e.trans (AdjoinRoot.algEquivOfEq (R := Z6) _ _ (by simp; exact map_ofNat _ _)).toRingEquiv,
    fun ⟨b, c, h⟩ => sq_sub_four_mul_ne_three b c h⟩

end ExtensionAcrossTwoExample

end Grothendieck.Folder77


/-!
## Page 85: the Proposition with « finie étale », c) ⇒ a)

The reading restores « finie étale » in condition c) of the Proposition of page 85: `2` regular
in `A`, `A₀ = A/2A` an integrally closed domain, `Δ ∉ 2A`; if a finite étale `A_Δ`-algebra `B_Δ`
satisfies `(B_Δ)₂ ≅ A_{2Δ}[U]/(U² − Δ)`, then `Δ = b² − 4c` in `A` (`prop85_c_imp_a`). No
noetherian hypothesis is used. The proof does not pass through a monogenic presentation. With
`R = (A_Δ)_{2A_Δ}` (local, maximal ideal `2R`) and `C = R ⊗ B_Δ` realised as a localisation of
`B_Δ`, `C` is finite, unramified, `2`-torsion free and contains `v` with `v² = 4ⁿΔ`. Then
(`prop85_local`): `C/2C` is unramified over the residue field, hence reduced, so `v` descends to
`u ∈ C` with `u² = Δ`; at a maximal ideal `Q` of `C` over `2R`, `C/Q` is separable over `R/2R`
(characteristic `2`), so `u mod Q` lies in `R/2R` and `Δ ≡ c² (mod 2R)`; reducedness of `C/2C`
again gives `u = c + 2s`, whence `Δ − c² ∈ 4C ∩ R = 4R`. Back in `A` (`exists_of_sq_sub`), the
root of `Δ₀` in `Frac A₀` is integral, hence in `A₀`, and `τ ∉ 2A`, `τ y ∈ 4A ⇒ y ∈ 4A`.
Consequences: `B_Δ = ℤ[1/3][U]/(U² − 3)` is not étale (`B3_not_etale`), and an isomorphism
between two such extensions compatible with the identifications after inverting `2` is unique
(`prop85_iso_unique`). That such an isomorphism exists, a) ⇒ c), and Corollary 3 (p. 63) are
not formalised.
-/

namespace Grothendieck.Folder77

section Prop85Local

open IsLocalRing Polynomial

variable {R C : Type*} [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]

/-- A quotient of a finite unramified algebra over a local ring `R` by an ideal over the maximal
ideal is finite and unramified over the residue field. -/
theorem quot_unramified_finite [Algebra.FormallyUnramified R C] [Module.Finite R C]
    (I : Ideal C) [I.LiesOver (maximalIdeal R)] :
    Algebra.FormallyUnramified (R ⧸ maximalIdeal R) (C ⧸ I) ∧
      Module.Finite (R ⧸ maximalIdeal R) (C ⧸ I) := by
  have : Algebra.FormallyUnramified R (C ⧸ I) := inferInstance
  exact ⟨.of_restrictScalars R _ _, .of_restrictScalars_finite R _ _⟩

/-- Such a quotient is reduced. -/
theorem quot_isReduced [Algebra.FormallyUnramified R C] [Module.Finite R C]
    (I : Ideal C) [I.LiesOver (maximalIdeal R)] : IsReduced (C ⧸ I) := by
  obtain ⟨_, _⟩ := quot_unramified_finite (R := R) I
  let := Ideal.Quotient.field (maximalIdeal R)
  exact Algebra.FormallyUnramified.isReduced_of_field (R ⧸ maximalIdeal R) (C ⧸ I)

/-- In a reduced quotient `C/I`, `x² ∈ I` implies `x ∈ I`. -/
theorem sq_mem_quot {I : Ideal C} (hI : IsReduced (C ⧸ I)) {x : C} (hx : x ^ 2 ∈ I) : x ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  exact IsReduced.eq_zero _ ⟨2, by rw [← map_pow]; exact hx⟩

/-- In a field `L` of characteristic `2`, separable over `K`, an element whose square lies in
`K` lies in `K`. -/
theorem mem_range_of_sq_of_char_two {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (h2 : (2 : K) = 0) {x : L} (hx : x ^ 2 ∈ (algebraMap K L).range) :
    x ∈ (algebraMap K L).range := by
  have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hdeg := (minpoly.natSepDegree_eq_one_iff_pow_mem (q := 2) (x := x)).2 ⟨1, by simpa using hx⟩
  rwa [(Algebra.IsSeparable.isSeparable K x).natSepDegree_eq_natDegree,
    minpoly.natDegree_eq_one_iff] at hdeg

/-- **The local step.** `R` local with maximal ideal `2R`, `C` a nonzero finite unramified
`R`-algebra without `2`-torsion, `v ∈ C` with `v² = 4ⁿΔ`. Then `Δ = b² − 4c` in `R`. -/
theorem prop85_local [Algebra.FormallyUnramified R C] [Module.Finite R C] [Nontrivial C]
    (hm : maximalIdeal R = Ideal.span {2}) (h2C : ∀ x : C, 2 * x = 0 → x = 0)
    {Δ : R} {v : C} {n : ℕ} (hv : v ^ 2 = 4 ^ n * algebraMap R C Δ) :
    ∃ b c : R, b ^ 2 - 4 * c = Δ := by
  have hker : RingHom.ker (algebraMap R C) ≤ maximalIdeal R :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQu⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal R) hker
  have h2m : (2 : R) ∈ maximalIdeal R := hm ▸ Ideal.mem_span_singleton_self 2
  have h2Q : (2 : C) ∈ Q := by
    have : (2 : R) ∈ Q.under R := hQu ▸ h2m
    rwa [Ideal.under, Ideal.mem_comap, map_ofNat] at this
  set I : Ideal C := Ideal.span {2}
  have hIu : I.under R = maximalIdeal R :=
    le_antisymm (hQu ▸ Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).2 h2Q))
      (by rw [hm, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under,
        Ideal.mem_comap, map_ofNat]
          exact Ideal.mem_span_singleton_self 2)
  have : I.LiesOver (maximalIdeal R) := ⟨hIu.symm⟩
  have : Q.LiesOver (maximalIdeal R) := ⟨hQu.symm⟩
  have hred := quot_isReduced (R := R) I
  have h2I : ∀ x : C, x ^ 2 ∈ I → ∃ y, x = 2 * y := fun x hx => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (sq_mem_quot hred hx)
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hdesc : ∀ k : ℕ, ∀ v : C, v ^ 2 = 4 ^ k * algebraMap R C Δ →
      ∃ u : C, u ^ 2 = algebraMap R C Δ := by
    intro k
    induction k with
    | zero => exact fun v hv => ⟨v, by simpa using hv⟩
    | succ k ih =>
      intro v hv
      obtain ⟨y, rfl⟩ := h2I v (by
        rw [hv]; exact Ideal.mem_span_singleton'.2 ⟨2 * 4 ^ k * algebraMap R C Δ, by ring⟩)
      refine ih y (sub_eq_zero.1 (h2C _ (h2C _ ?_)))
      linear_combination hv
  obtain ⟨u, hu⟩ := hdesc n v hv
  let := Ideal.Quotient.field (maximalIdeal R)
  let := Ideal.Quotient.field Q
  obtain ⟨_, _⟩ := quot_unramified_finite (R := R) Q
  have : Algebra.IsSeparable (R ⧸ maximalIdeal R) (C ⧸ Q) :=
    Algebra.FormallyUnramified.isSeparable _ _
  have h20 : (2 : R ⧸ maximalIdeal R) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]; exact h2m
  obtain ⟨c0, hc0⟩ := mem_range_of_sq_of_char_two h20 (x := Ideal.Quotient.mk Q u)
    ⟨Ideal.Quotient.mk _ Δ, by rw [Ideal.Quotient.algebraMap_mk_of_liesOver, ← map_pow, hu]⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c0
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq] at hc0
  have hΔc : Δ - c ^ 2 ∈ maximalIdeal R := by
    rw [← hQu, Ideal.under, Ideal.mem_comap, map_sub, map_pow, ← hu]
    rw [show u ^ 2 - (algebraMap R C c) ^ 2 = (u - algebraMap R C c) * (u + algebraMap R C c) by
      ring]
    exact Q.mul_mem_right _ (by rw [← neg_sub]; exact Q.neg_mem hc0)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hm ▸ hΔc)
  obtain ⟨s, hs⟩ := h2I (u - algebraMap R C c) (by
    refine Ideal.mem_span_singleton'.2
      ⟨algebraMap R C y + algebraMap R C c ^ 2 - u * algebraMap R C c, ?_⟩
    have := congrArg (algebraMap R C) hy
    simp only [map_mul, map_sub, map_pow, map_ofNat] at this
    linear_combination this - hu)
  have hyI : algebraMap R C y ∈ I := by
    have := congrArg (algebraMap R C) hy
    simp only [map_mul, map_sub, map_pow, map_ofNat] at this
    refine Ideal.mem_span_singleton'.2 ⟨algebraMap R C c * s + s ^ 2, ?_⟩
    have e : u = algebraMap R C c + 2 * s := by rw [← hs]; ring
    refine (sub_eq_zero.1 (h2C _ (h2C _ ?_))).symm
    rw [e] at hu
    linear_combination 2 * this - 2 * hu
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (hm ▸ (hIu ▸ hyI : y ∈ maximalIdeal R))
  exact ⟨c, -d, by linear_combination hy + 2 * hd⟩

end Prop85Local

section Prop85Global

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A]

/-- If `x` is regular in `A`, its image in a localization of `R` is regular. -/
theorem isLocalization_mul_regular {S : Type*} [CommRing S] [Algebra A S] (M : Submonoid A)
    [IsLocalization M S] {x : A} (hx : ∀ y : A, x * y = 0 → y = 0) (z : S)
    (hz : algebraMap A S x * z = 0) : z = 0 := by
  obtain ⟨y, s, rfl⟩ := IsLocalization.mk'_surjective M z
  rw [← IsLocalization.mk'_one (M := M) S x, ← IsLocalization.mk'_mul, one_mul,
    IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨m, hm⟩ := hz
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨m, hx _ (by rw [← hm]; ring)⟩

/-- `2` regular and `2A` prime: if `τ ∉ 2A` and `τ y ∈ 4A`, then `y ∈ 4A`. -/
theorem dvd_four_of_mul (h2 : ∀ x : A, 2 * x = 0 → x = 0) (hp : (Ideal.span {(2 : A)}).IsPrime)
    {τ y z : A} (hτ : τ ∉ Ideal.span {(2 : A)}) (h : τ * y = 4 * z) : ∃ w, y = 4 * w := by
  have step : ∀ {y z : A}, τ * y = 2 * z → ∃ w, y = 2 * w := fun {y z} h => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 ((hp.mem_or_mem
      (Ideal.mem_span_singleton'.2 ⟨z, by rw [h, mul_comm]⟩ : τ * y ∈ _)).resolve_left hτ)
    exact ⟨w, by rw [← hw, mul_comm]⟩
  obtain ⟨w, rfl⟩ := step (z := 2 * z) (by rw [h]; ring)
  obtain ⟨w', rfl⟩ := step (y := w) (z := z) (sub_eq_zero.1 (h2 _ (by linear_combination h)))
  exact ⟨w', by ring⟩

/-- The descent from `A_{2A}` to `A`: if `α² − τ²Δ ∈ 4A` with `τ ∉ 2A`, `2` regular and
`A/2A` an integrally closed domain, then `Δ = b² − 4c` in `A`. -/
theorem exists_of_sq_sub (h2 : ∀ x : A, 2 * x = 0 → x = 0) [hp : (Ideal.span {(2 : A)}).IsPrime]
    [IsIntegrallyClosed (A ⧸ Ideal.span {(2 : A)})] {Δ α τ z : A}
    (hτ : τ ∉ Ideal.span {(2 : A)}) (h : α ^ 2 - τ ^ 2 * Δ = 4 * z) :
    ∃ b c : A, b ^ 2 - 4 * c = Δ := by
  set p := Ideal.span {(2 : A)}
  let K := FractionRing (A ⧸ p)
  have hτ0 : algebraMap (A ⧸ p) K (Ideal.Quotient.mk p τ) ≠ 0 := by
    rwa [ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have h4 : (4 : A ⧸ p) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk p), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨2, by norm_num⟩
  have hsq : (algebraMap (A ⧸ p) K (Ideal.Quotient.mk p α) /
      algebraMap (A ⧸ p) K (Ideal.Quotient.mk p τ)) ^ 2 =
      algebraMap (A ⧸ p) K (Ideal.Quotient.mk p Δ) := by
    have e := congrArg (fun x => algebraMap (A ⧸ p) K (Ideal.Quotient.mk p x)) h
    simp only [map_sub, map_mul, map_pow, map_ofNat, h4, map_zero, zero_mul] at e
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hτ0)]
    linear_combination e
  obtain ⟨β, hβ⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := A ⧸ p)
    (n := 2) two_pos (by rw [hsq]; exact isIntegral_algebraMap)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  have hab : α - b * τ ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective (A ⧸ p) K
    rw [eq_div_iff hτ0] at hβ
    simp only [map_sub, map_mul, map_zero, hβ, sub_self]
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hab
  obtain ⟨w, hw⟩ := dvd_four_of_mul h2 hp (y := τ * (b ^ 2 - Δ)) (z := z - b * τ * x - x ^ 2)
    hτ (by
      have e : α = b * τ + x * 2 := by linear_combination -hx
      rw [e] at h
      linear_combination h)
  obtain ⟨w', hw'⟩ := dvd_four_of_mul h2 hp hτ hw
  exact ⟨b, w', by linear_combination hw'⟩

/-- **Page 85, c) ⇒ a), with « finie étale ».** Let `2` be regular in `A`, `A₀ = A/2A` an
integrally closed domain, `Δ ∉ 2A`. If `B_Δ` is a finite étale `A_Δ`-algebra with
`(B_Δ)₂ ≅ A_{2Δ}[U]/(U² − Δ)` as `A_Δ`-algebras, then `Δ = b² − 4c` with `b, c ∈ A`.
No noetherian hypothesis is needed. -/
theorem prop85_c_imp_a {Δ : A} (h2 : ∀ x : A, 2 * x = 0 → x = 0)
    [hp : (Ideal.span {(2 : A)}).IsPrime] [IsIntegrallyClosed (A ⧸ Ideal.span {(2 : A)})]
    (hΔ : Δ ∉ Ideal.span {(2 : A)})
    (B : Type*) [CommRing B] [Algebra (Localization.Away Δ) B]
    [Algebra.Etale (Localization.Away Δ) B] [Module.Finite (Localization.Away Δ) B]
    (e : Localization.Away (algebraMap (Localization.Away Δ) B 2) ≃ₐ[Localization.Away Δ]
      quadAlg (algebraMap A (Localization.Away (2 : Localization.Away Δ)) Δ)) :
    ∃ b c : A, b ^ 2 - 4 * c = Δ := by
  set p := Ideal.span {(2 : A)}
  let AΔ := Localization.Away Δ
  have hdisj : Disjoint (Submonoid.powers Δ : Set A) p := by
    rw [Set.disjoint_left]; rintro _ ⟨k, rfl⟩ hk; exact hΔ (hp.mem_of_pow_mem k hk)
  set P : Ideal AΔ := p.map (algebraMap A AΔ) with hPdef
  have hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ p hp hdisj
  have hPu : P.under A = p := IsLocalization.under_map_of_isPrime_disjoint _ _ hp hdisj
  have hP2 : P = Ideal.span {2} := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_ofNat]
  let R := Localization.AtPrime P
  have hm : maximalIdeal R = Ideal.span {2} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, congrArg (Ideal.map (algebraMap AΔ R)) hP2,
      Ideal.map_span, Set.image_singleton, map_ofNat]
  have h2Δ : ∀ z : AΔ, 2 * z = 0 → z = 0 := fun z hz =>
    isLocalization_mul_regular (Submonoid.powers Δ) h2 z (by rwa [map_ofNat])
  have : Nontrivial AΔ :=
    ⟨⟨0, 1, fun h => hP.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact P.zero_mem)⟩⟩
  let A2 := Localization.Away (2 : AΔ)
  have h2nzd : (2 : AΔ) ∈ nonZeroDivisors AΔ :=
    mem_nonZeroDivisors_iff_right.2 fun x hx => h2Δ x (by rw [mul_comm]; exact hx)
  have hA2 : Function.Injective (algebraMap AΔ A2) :=
    IsLocalization.injective A2 (Submonoid.powers_le.2 h2nzd)
  have : Nontrivial A2 := hA2.nontrivial
  set δ : A2 := algebraMap A A2 Δ
  let Q := quadAlg δ
  have hQ : Function.Injective (algebraMap AΔ Q) := by
    rw [IsScalarTower.algebraMap_eq AΔ A2 Q]
    refine (AdjoinRoot.of.injective_of_monic_of_degree_pos (quadAlg_monic δ) ?_).comp hA2
    rw [Polynomial.degree_X_pow_sub_C two_pos]; norm_num
  let B2 := Localization.Away (algebraMap AΔ B 2)
  have hB : Function.Injective (algebraMap AΔ B) := by
    intro x y hxy
    apply hQ
    rw [← e.commutes, ← e.commutes, IsScalarTower.algebraMap_apply AΔ B B2,
      IsScalarTower.algebraMap_apply AΔ B B2 y, hxy]
  have h2B : ∀ z : B, 2 * z = 0 → z = 0 := fun z hz =>
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) h2nzd
      (show (2 : AΔ) • z = (2 : AΔ) • (0 : B) by
        rw [smul_zero, Algebra.smul_def, map_ofNat]; exact hz)
  -- the square root of `Δ` in `B` up to a power of `2`
  have hroot : (AdjoinRoot.root (X ^ 2 - C δ) : Q) ^ 2 = algebraMap AΔ Q (algebraMap A AΔ Δ) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A A2 Q,
      AdjoinRoot.algebraMap_eq, ← sub_eq_zero, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X, ← map_pow,
      ← map_sub, AdjoinRoot.mk_self]
  set δB := algebraMap AΔ B (algebraMap A AΔ Δ)
  obtain ⟨n, v, hv⟩ : ∃ (n : ℕ) (v : B), v ^ 2 = (2 ^ n) ^ 2 * δB := by
    set u0 := e.symm (AdjoinRoot.root _)
    have hu0 : u0 ^ 2 = algebraMap B B2 δB := by
      apply e.injective
      rw [map_pow, e.apply_symm_apply, hroot, ← e.commutes, IsScalarTower.algebraMap_apply AΔ B B2]
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap AΔ B 2)) u0
    obtain ⟨k, hk⟩ := s.2
    have hspec := IsLocalization.mk'_spec B2 b s
    rw [show IsLocalization.mk' B2 b s = u0 from hbs] at hspec
    have : algebraMap B B2 (b ^ 2) = algebraMap B B2 ((s : B) ^ 2 * δB) := by
      rw [map_pow, ← hspec, map_mul, map_pow, ← hu0]; ring
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (Submonoid.powers (algebraMap AΔ B 2)) B2).1 this
    obtain ⟨m, hm⟩ := c.2
    refine ⟨m + k, (c : B) * b, ?_⟩
    rw [← hm]
    rw [← hm, ← hk] at hc
    simp only [map_ofNat] at hc ⊢
    linear_combination (2 : B) ^ m * hc
  -- localise at `2A`
  let S := Algebra.algebraMapSubmonoid B P.primeCompl
  let C := Localization S
  have : IsLocalization (P.primeCompl.map (algebraMap AΔ B)) C := Localization.isLocalization
  have : IsScalarTower AΔ R C := isScalarTower_localizationAlgebra P.primeCompl B
  have : Algebra.FormallyUnramified R C :=
    Algebra.FormallyUnramified.localization_map P.primeCompl (Rₘ := R) (Sₘ := C) (S := B)
  have : Module.Finite R C := Module.Finite.of_isLocalization AΔ B P.primeCompl
  have : Nontrivial C := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    rw [← map_one (algebraMap B C), ← map_zero (algebraMap B C),
      IsLocalization.eq_iff_exists S C] at h
    obtain ⟨⟨_, t, ht, rfl⟩, h⟩ := h
    simp only [mul_one, mul_zero] at h
    exact ht (by rw [hB (h.trans (map_zero _).symm)]; exact P.zero_mem)
  have h2C : ∀ z : C, 2 * z = 0 → z = 0 := fun z hz =>
    isLocalization_mul_regular S h2B z (by rwa [map_ofNat])
  obtain ⟨b', c', hbc⟩ := prop85_local (R := R) (C := C) hm h2C (n := n)
    (Δ := algebraMap AΔ R (algebraMap A AΔ Δ)) (v := algebraMap B C v) (by
      have e1 : algebraMap B C δB = algebraMap R C (algebraMap AΔ R (algebraMap A AΔ Δ)) := by
        rw [← IsScalarTower.algebraMap_apply AΔ R C, IsScalarTower.algebraMap_apply AΔ B C]
      have e2 : ((2 : C) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [← map_pow, hv, map_mul, map_pow, map_pow, map_ofNat, e1, e2])
  -- back to `A`
  have : IsLocalization.AtPrime R p := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers Δ) R P
    have hPu' : P.comap (algebraMap A AΔ) = p := hPu
    have hM : (P.comap (algebraMap A AΔ)).primeCompl = p.primeCompl := by
      ext x; simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, hPu']
    have this' : IsLocalization (P.comap (algebraMap A AΔ)).primeCompl R := this
    change IsLocalization p.primeCompl R
    rw [← hM]; exact this'
  obtain ⟨⟨a1, s1⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl b'
  obtain ⟨⟨a2, s2⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c'
  have h1 := IsLocalization.mk'_spec R a1 s1
  have h2' := IsLocalization.mk'_spec R a2 s2
  rw [← IsScalarTower.algebraMap_apply] at hbc
  have key : algebraMap A R (a1 ^ 2 * s2 - 4 * a2 * s1 ^ 2) =
      algebraMap A R (Δ * s1 ^ 2 * s2) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [← h1, ← h2', ← hbc]; ring
  obtain ⟨⟨t, ht⟩, htk⟩ := (IsLocalization.eq_iff_exists p.primeCompl R).1 key
  have hτ : t * s2 * s1 ∉ p :=
    p.primeCompl.mul_mem (p.primeCompl.mul_mem ht s2.2) s1.2
  exact exists_of_sq_sub h2 (α := t * s2 * a1) (z := t * (t * s2) * a2 * (s1 : A) ^ 2) hτ
    (by linear_combination (t * s2) * htk)

end Prop85Global

section Prop85Consequences

/-- **Page 85, uniqueness of the isomorphism.** Two `A_Δ`-algebra maps `B_Δ → B'_Δ` compatible
with given identifications of `(B_Δ)₂` and `(B'_Δ)₂` with `A_{2Δ}[U]/(U² − Δ)` are equal, as
soon as `2` is regular in `A` and `B'_Δ` is flat (here, étale): `B'_Δ ⊂ (B'_Δ)₂`. -/
theorem prop85_iso_unique {A : Type*} [CommRing A] {Δ : A} (h2 : ∀ x : A, 2 * x = 0 → x = 0)
    (B B' : Type*) [CommRing B] [CommRing B'] [Algebra (Localization.Away Δ) B]
    [Algebra (Localization.Away Δ) B'] [Algebra.Etale (Localization.Away Δ) B']
    (e : Localization.Away (algebraMap (Localization.Away Δ) B 2) ≃ₐ[Localization.Away Δ]
      quadAlg (algebraMap A (Localization.Away (2 : Localization.Away Δ)) Δ))
    (e' : Localization.Away (algebraMap (Localization.Away Δ) B' 2) ≃ₐ[Localization.Away Δ]
      quadAlg (algebraMap A (Localization.Away (2 : Localization.Away Δ)) Δ))
    (φ ψ : B →ₐ[Localization.Away Δ] B')
    (hφ : ∀ x, e' (algebraMap B' _ (φ x)) = e (algebraMap B _ x))
    (hψ : ∀ x, e' (algebraMap B' _ (ψ x)) = e (algebraMap B _ x)) : φ = ψ := by
  let AΔ := Localization.Away Δ
  have h2Δ : ∀ z : AΔ, 2 * z = 0 → z = 0 := fun z hz =>
    isLocalization_mul_regular (Submonoid.powers Δ) h2 z (by rwa [map_ofNat])
  have h2nzd : (2 : AΔ) ∈ nonZeroDivisors AΔ :=
    mem_nonZeroDivisors_iff_right.2 fun x hx => h2Δ x (by rw [mul_comm]; exact hx)
  have hr : IsSMulRegular B' (2 : AΔ) := Module.Flat.isSMulRegular_of_nonZeroDivisors h2nzd
  have h2B : algebraMap AΔ B' 2 ∈ nonZeroDivisors B' :=
    mem_nonZeroDivisors_iff_right.2 fun z hz => hr (by
      change (2 : AΔ) • z = (2 : AΔ) • (0 : B')
      rw [smul_zero, Algebra.smul_def, mul_comm]; exact hz)
  have hinj : Function.Injective
      (algebraMap B' (Localization.Away (algebraMap AΔ B' 2))) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 h2B)
  ext x
  exact hinj (e'.injective ((hφ x).trans (hψ x).symm))

instance : (Ideal.span {(2 : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two).isMaximal (by simp)

instance : IsIntegrallyClosed (ℤ ⧸ Ideal.span {(2 : ℤ)}) := by
  let := Ideal.Quotient.field (Ideal.span {(2 : ℤ)})
  infer_instance

/-- **Page 85, the struck « étale ».** `B_Δ = ℤ[1/3][U]/(U² − 3)` is not étale over `ℤ[1/3]`:
otherwise the Proposition with « finie étale » would give `3 = b² − 4c` in `ℤ`. -/
theorem B3_not_etale : ¬ Algebra.Etale Z3 B3 := by
  intro hB
  obtain ⟨e⟩ := quadAlg_away (3 : Z3) (2 : Z3)
  let e₁ := e.trans (AdjoinRoot.algEquivOfEq (R := Z6)
    (Polynomial.X ^ 2 - Polynomial.C (algebraMap Z3 Z6 (3 : Z3)))
    (Polynomial.X ^ 2 - Polynomial.C (algebraMap ℤ Z6 (3 : ℤ)))
    (by rw [map_ofNat (algebraMap Z3 Z6), map_ofNat (algebraMap ℤ Z6)])).toRingEquiv
  have hc : ∀ x : Z3, e₁ (algebraMap Z3 _ x) = algebraMap Z3 _ x := by
    have := IsLocalization.ringHom_ext (Submonoid.powers (3 : ℤ)) (S := Z3)
      (j := e₁.toRingHom.comp (algebraMap Z3 _)) (k := algebraMap Z3 _) (RingHom.ext_int _ _)
    exact fun x => RingHom.congr_fun this x
  obtain ⟨b, c, h⟩ := prop85_c_imp_a (A := ℤ) (Δ := 3)
    (fun x hx => by omega) (by rw [Ideal.mem_span_singleton]; decide) B3
    (AlgEquiv.ofRingEquiv (f := e₁) hc)
  exact sq_sub_four_mul_ne_three b c h

end Prop85Consequences

end Grothendieck.Folder77
