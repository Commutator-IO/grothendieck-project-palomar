module

public import Mathlib
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.NumberTheory.Wilson
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Choose.Dvd
public import Grothendieck.Upstream.HasseDerivXPowMul
public import Grothendieck.Upstream.PolynomialIsCoprimeX
public import Grothendieck.Upstream.DerivationLieMulLeft
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


/-!
# Folder 93, pages 72, 115–123: the Schwarzian difference with divided derivatives

**Partial, and chosen.** The finding `93-integral-schwarzian-level-p2`
(`src/content/findings.ts`) states, from the modernised reading
`transcripts/93/93.modern.tex` (stations III and IX):

> The Schwarzian difference written with divided derivatives,
> `G₀(t,s) = −D⁽³⁾s/D⁽¹⁾s + (D⁽²⁾s/D⁽¹⁾s)² = G/12`, is an `ω^{⊗2}`-valued cocycle defined
> over any base, characteristics 2 and 3 included, and its vanishing forces a homography
> at Frobenius level `p` for `p > 3` but only at level `p²` for `p = 2, 3`.

This file proves the algebraic core, in the local model `R[X]` over an arbitrary
commutative ring `R` (`X` playing the uniformisant `t`, `D k = Polynomial.hasseDeriv k`
the divided derivative `D⁽ᵏ⁾ = (1/k!) dᵏ/dtᵏ`, defined without dividing by `k!`):

* `N f = (D⁽²⁾f)² − D⁽³⁾f · D⁽¹⁾f` and `G0 f = N f / (D⁽¹⁾f)²` (with `Ring.inverse`),
  over any `R`, characteristics 2 and 3 included.
* `Ncl_eq`, `G_eq` (page 120): `G = 12 G₀`, with `G` the classical
  `−2 f⁽³⁾/f' + 3 (f⁽²⁾/f')²`, over any ring (no division by 2 or 3).
* `chain` (Faà di Bruno to order 3), `N_comp` (the cocycle cleared of denominators,
  with no unit hypothesis) and `G0_comp` (the cocycle (II) of pages 115–117:
  `G₀(t, s∘u) = G₀(t, s)∘u · (D⁽¹⁾u)² + G₀(t, u)` when `D⁽¹⁾s`, `D⁽¹⁾u` are units).
* `N_homography`, `G0_homography`, `G0_homography_const` (invariance (1) of page 115):
  if `s · (cX + d) = aX + b`, with `a, b, c, d` killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾`, then
  `(cX + d)² · N(s) = 0`, hence `G₀(s) = 0` when `cX + d` is a unit.
* `N_X_sq`, `N_X_cube` (page 72): `G₀(t, t²) = 1/(4t²)` (the page writes `1/(2t)`;
  the reading footnotes it) and `G₀(t, t³) = 2/(3t²)`, in cleared form.
* `killed_iff_of_gt`, `killed_iff_two`, `killed_iff_three` (margin of page 121, « OK »):
  over `R` of prime characteristic `p`, `f` is killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾` iff every
  exponent in `f` is divisible by `p` (`p > 3`), by `4` (`p = 2`), by `9` (`p = 3`);
  `Killed.comp`: every polynomial in a killed `u` is killed.
* `char_two`, `char_three`: in characteristic 2, `D⁽¹⁾(t²) = 0` but
  `G₀(t, t + t²) = 1`; in characteristic 3, `D⁽¹⁾(t³) = D⁽²⁾(t³) = 0` but
  `G₀(t, t + t³) = −1`. Translation by a `p`-th power does not leave `G₀` invariant
  for `p = 2, 3`, which is why the coefficients of the homographies must be taken in
  `O^{p²}` there.

* Rigidity (the Proposition of pages 121–123), in the truncated model
  `B = A[T]/(T^n)` with `α = 0`, written in `A[X]`: `G₀(t, s) = 0` in `B` is `X^n ∣ N s`
  (well defined by `hasseDeriv_X_pow_mul`, `N_add_X_pow_mul` when `n = p^N > 3` in
  characteristic `p`), and `D⁽¹⁾s ∈ B*` is `s₁ ∈ A*`.
  `step` (page 122): if `s · (cX + d)` is affine modulo `X^(j+3)`, the coefficient of `X^j`
  in `(cX + d) · N(s)` is `−C(j+3,3) · s₁ · [X^(j+3)](s · (cX + d))`.
  `rigidity_core`, `rigidity_explicit`, `rigidity`: over any commutative ring `A` in which
  `C(k,3)` is a unit for `3 ≤ k < n`, `X^n ∣ N s` and `s₁ ∈ A*` give `a, b, c ∈ A` with
  `a − bc = s₁` and `s · (cX + 1) ≡ aX + b` modulo `X^n` (`c = −s₂/s₁`).
  `rigidity_of_gt` (`n = p`, any ring of characteristic `p`, no hypothesis on `Pic(A)`),
  `rigidity_iff_of_gt` (with the converse `N_of_homography_trunc`, `p > 3`),
  `rigidity_four` (`n = 4`, level `p²` for `p = 2`: over any ring), `rigidity_nine`
  (`n = 9`, level `p²` for `p = 3`: `C(k,3) ≢ 0 mod 3` for `3 ≤ k ≤ 8`),
  `rigidity_char_zero` (`A` a `ℚ`-algebra, in `A[X]` itself: `s · (cX + 1) = aX + b`).
* `det_one_square`, `det_one_counterexample`: the normalisation « `ad − bc = 1` » added on
  page 121 fails: in `𝔽₅[T]/(T^5)`, `s = 2t` has `G₀ = 0` but is no homography of
  determinant `1`. The determinant `s₁` is a unit, not a square in general.

Not proved: the reduction from `T^(p^N) − α` to `T^(p^N)` for `α ≠ 0` (it is where
`Pic(A) = 0` would enter), the torsor `Conn₀`, uniqueness of `G₀` up to sign over `ℤ`
(page 72), and the passage from the local model to a smooth curve.
Proving these statements says only that they hold as stated; the literature question
of the finding stays open.
-/

open Polynomial
open scoped Ring

namespace Grothendieck.Folder93

variable {R : Type*} [CommRing R]

local notation "D" => Polynomial.hasseDeriv

lemma D_mul_one (f g : R[X]) : D 1 (f * g) = D 1 f * g + f * D 1 g := by
  rw [hasseDeriv_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring

lemma D_mul_two (f g : R[X]) :
    D 2 (f * g) = D 2 f * g + D 1 f * D 1 g + f * D 2 g := by
  rw [hasseDeriv_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring

lemma D_mul_three (f g : R[X]) :
    D 3 (f * g) = D 3 f * g + D 2 f * D 1 g + D 1 f * D 2 g + f * D 3 g := by
  rw [hasseDeriv_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring


@[simp] lemma D1_X : D 1 (X : R[X]) = 1 := by simp
@[simp] lemma D2_X : D 2 (X : R[X]) = 0 := hasseDeriv_X (k := 2) (by norm_num)
@[simp] lemma D3_X : D 3 (X : R[X]) = 0 := hasseDeriv_X (k := 3) (by norm_num)

/-- The chain rule for divided derivatives up to order 3 (Faà di Bruno). -/
theorem chain (s u : R[X]) :
    D 1 (s.comp u) = (D 1 s).comp u * D 1 u ∧
    D 2 (s.comp u) = (D 1 s).comp u * D 2 u + (D 2 s).comp u * D 1 u ^ 2 ∧
    D 3 (s.comp u) = (D 1 s).comp u * D 3 u + 2 * (D 2 s).comp u * D 1 u * D 2 u
      + (D 3 s).comp u * D 1 u ^ 3 := by
  induction s using Polynomial.induction_on with
  | C a =>
    simp [hasseDeriv_C]
  | add f g hf hg =>
    obtain ⟨f1, f2, f3⟩ := hf
    obtain ⟨g1, g2, g3⟩ := hg
    simp only [add_comp, map_add, f1, f2, f3, g1, g2, g3]
    refine ⟨by ring, by ring, by ring⟩
  | monomial n a ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring]
    set w := C a * X ^ n
    simp only [mul_comp, X_comp, D_mul_one, D_mul_two, D_mul_three, D1_X, D2_X, D3_X,
      h1, h2, h3, add_comp, zero_mul, one_mul, add_zero, zero_add]
    refine ⟨by ring, by ring, by ring⟩

/-- Numerator of `G₀`: `G₀(t, f) · (D⁽¹⁾f)² = (D⁽²⁾f)² − D⁽³⁾f · D⁽¹⁾f`. -/
noncomputable def N (f : R[X]) : R[X] := D 2 f ^ 2 - D 3 f * D 1 f

/-- `G₀(t, f) = −D⁽³⁾f / D⁽¹⁾f + (D⁽²⁾f / D⁽¹⁾f)²`, with `Ring.inverse` for the division. -/
noncomputable def G0 (f : R[X]) : R[X] := N f * (D 1 f ^ 2)⁻¹ʳ

/-- Numerator of the classical `G = −2 f⁽³⁾/f' + 3 (f⁽²⁾/f')²`. -/
noncomputable def Ncl (f : R[X]) : R[X] :=
  3 * (derivative^[2] f) ^ 2 - 2 * derivative^[3] f * derivative f

/-- The classical `G`. -/
noncomputable def G (f : R[X]) : R[X] := Ncl f * (derivative f ^ 2)⁻¹ʳ

/-- Page 120: `G = 12 G₀`, cleared of denominators, over any commutative ring. -/
theorem Ncl_eq (f : R[X]) : Ncl f = 12 * N f := by
  have h2 := congrFun (factorial_smul_hasseDeriv (R := R) (k := 2)) f
  have h3 := congrFun (factorial_smul_hasseDeriv (R := R) (k := 3)) f
  simp only [LinearMap.smul_apply] at h2 h3
  rw [Ncl, N, ← h2, ← h3, hasseDeriv_one']
  simp only [Nat.factorial, nsmul_eq_mul]
  push_cast
  ring

/-- Page 120: `G = 12 G₀`. -/
theorem G_eq (f : R[X]) : G f = 12 * G0 f := by
  rw [G, G0, Ncl_eq, hasseDeriv_one', mul_assoc]

/-- The cocycle relation cleared of denominators: no unit hypothesis. -/
theorem N_comp (s u : R[X]) :
    N (s.comp u) = (N s).comp u * D 1 u ^ 4 + ((D 1 s).comp u) ^ 2 * N u := by
  obtain ⟨h1, h2, h3⟩ := chain s u
  simp only [N, h1, h2, h3, sub_comp, mul_comp, pow_comp]
  ring

lemma inverse_comp {x : R[X]} (hx : IsUnit x) (u : R[X]) : (x⁻¹ʳ).comp u = (x.comp u)⁻¹ʳ := by
  obtain ⟨v, rfl⟩ := hx
  have h : (v : R[X]).comp u = ((Units.map (compRingHom u).toMonoidHom v : R[X]ˣ) : R[X]) := rfl
  rw [h, Ring.inverse_unit, Ring.inverse_unit, Units.coe_map_inv]
  rfl

lemma unit_algebra {S : Type*} [CommRing S] {a b n m k : S} (ha : IsUnit a) (hb : IsUnit b)
    (h : n = m * a ^ 4 + b ^ 2 * k) :
    n * ((b * a) ^ 2)⁻¹ʳ = m * (b ^ 2)⁻¹ʳ * a ^ 2 + k * (a ^ 2)⁻¹ʳ := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  simp only [← Units.val_mul, ← Units.val_pow_eq_pow_val, Ring.inverse_unit]
  subst h
  have hA : (A : S) * (A⁻¹ : Sˣ) = 1 := A.mul_inv
  have hB : (B : S) * (B⁻¹ : Sˣ) = 1 := B.mul_inv
  push_cast
  rw [mul_inv, Units.val_mul]
  linear_combination (m * (A : S) ^ 2 * ((B⁻¹ : Sˣ) : S) ^ 2 * (A * (A⁻¹ : Sˣ) + 1)) * hA
    + (k * ((A⁻¹ : Sˣ) : S) ^ 2 * (B * (B⁻¹ : Sˣ) + 1)) * hB

/-- Pages 115–117, relation (II): `G₀(t, s∘u) = G₀(u, s∘u) + G₀(t, u)`, where
`G₀(u, s∘u) = G₀(t, s)∘u · (D⁽¹⁾u)²` expresses the quadratic differential in `dt²`. -/
theorem G0_comp (s u : R[X]) (hs : IsUnit (D 1 s)) (hu : IsUnit (D 1 u)) :
    G0 (s.comp u) = (G0 s).comp u * D 1 u ^ 2 + G0 u := by
  have hsu : IsUnit ((D 1 s).comp u) := hs.map (compRingHom u)
  rw [G0, G0, G0, (chain s u).1, mul_comp, inverse_comp (hs.pow 2), pow_comp]
  exact unit_algebra hu hsu (N_comp s u)

/-- `G₀(t, t) = 0`. -/
theorem N_X : N (X : R[X]) = 0 := by simp [N]

theorem G0_X : G0 (X : R[X]) = 0 := by simp [G0, N_X]

/-- Invariance under homographies, cleared of denominators: if `s · q = p` with `p`, `q`
killed by `D⁽²⁾` and `D⁽³⁾`, then `q² · N(s) = 0`. -/
theorem N_homography {s p q : R[X]} (hp2 : D 2 p = 0) (hp3 : D 3 p = 0)
    (hq2 : D 2 q = 0) (hq3 : D 3 q = 0) (h : s * q = p) : q ^ 2 * N s = 0 := by
  have e2 := congrArg (D 2) h
  have e3 := congrArg (D 3) h
  rw [D_mul_two, hp2, hq2] at e2
  rw [D_mul_three, hp3, hq2, hq3] at e3
  rw [N]
  linear_combination (D 2 s * q) * e2 - (D 1 s * q) * e3

lemma D_mul_X_of_const {a : R[X]} (h1 : D 1 a = 0) (h2 : D 2 a = 0) (h3 : D 3 a = 0) :
    D 1 (a * X) = a ∧ D 2 (a * X) = 0 ∧ D 3 (a * X) = 0 := by
  rw [D_mul_one, D_mul_two, D_mul_three, h1, h2, h3, D1_X, D2_X, D3_X]
  simp

/-- Homographies whose coefficients are killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾` satisfy `G₀ = 0`. -/
theorem G0_homography {s a b c d : R[X]}
    (ha : D 1 a = 0 ∧ D 2 a = 0 ∧ D 3 a = 0) (hb : D 1 b = 0 ∧ D 2 b = 0 ∧ D 3 b = 0)
    (hc : D 1 c = 0 ∧ D 2 c = 0 ∧ D 3 c = 0) (hd : D 1 d = 0 ∧ D 2 d = 0 ∧ D 3 d = 0)
    (hq : IsUnit (c * X + d)) (h : s * (c * X + d) = a * X + b) : G0 s = 0 := by
  obtain ⟨-, a2, a3⟩ := D_mul_X_of_const ha.1 ha.2.1 ha.2.2
  obtain ⟨-, c2, c3⟩ := D_mul_X_of_const hc.1 hc.2.1 hc.2.2
  have key := N_homography (by simp [a2, hb.2.1]) (by simp [a3, hb.2.2])
    (by simp [c2, hd.2.1]) (by simp [c3, hd.2.2]) h
  have hN : N s = 0 := (hq.pow 2).mul_left_cancel (by rw [key, mul_zero])
  simp [G0, hN]

/-- Constant homographies: `a, b, c, d ∈ R`. -/
theorem G0_homography_const {s : R[X]} {a b c d : R} (hq : IsUnit (C c * X + C d))
    (h : s * (C c * X + C d) = C a * X + C b) : G0 s = 0 := by
  have k : ∀ r : R, D 1 (C r) = 0 ∧ D 2 (C r) = 0 ∧ D 3 (C r) = 0 := fun r =>
    ⟨hasseDeriv_C 1 r (by norm_num), hasseDeriv_C 2 r (by norm_num), hasseDeriv_C 3 r (by norm_num)⟩
  exact G0_homography (k a) (k b) (k c) (k d) hq h

/-! ### Test values (page 72) -/

lemma D_X_pow (k n : ℕ) : D k (X ^ n : R[X]) = (n.choose k : R[X]) * X ^ (n - k) := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial, mul_one, ← C_mul_X_pow_eq_monomial,
    map_natCast]

/-- `G₀(t, t²) · (2t)² = 1`, so `G₀(t, t²) = 1/(4t²)` where `2` is invertible. -/
theorem N_X_sq : N (X ^ 2 : R[X]) = 1 ∧ D 1 (X ^ 2 : R[X]) = 2 * X := by
  simp only [N, D_X_pow]
  norm_num

/-- `G₀(t, t³) · (3t²)² = 6t²`, so `G₀(t, t³) = 2/(3t²)` where `3` is invertible. -/
theorem N_X_cube : N (X ^ 3 : R[X]) = 6 * X ^ 2 ∧ D 1 (X ^ 3 : R[X]) = 3 * X ^ 2 := by
  simp only [N, D_X_pow]
  norm_num
  ring

/-! ### Characteristics 2 and 3 -/

lemma natCast_eq_zero (p : ℕ) [CharP R p] : (p : R[X]) = 0 := by
  rw [← map_natCast C, CharP.cast_eq_zero, map_zero]

/-- In characteristic 2, `t²` is killed by `D⁽¹⁾` but `G₀(t, t + t²) = 1`. -/
theorem char_two [CharP R 2] :
    D 1 (X ^ 2 : R[X]) = 0 ∧ D 1 (X + X ^ 2 : R[X]) = 1 ∧ G0 (X + X ^ 2 : R[X]) = 1 := by
  have h2 : (2 : R[X]) = 0 := by exact_mod_cast natCast_eq_zero (R := R) 2
  have d1 : D 1 (X + X ^ 2 : R[X]) = 1 := by
    rw [map_add, D_X_pow, D1_X]; norm_num; linear_combination h2
  refine ⟨by rw [D_X_pow]; norm_num; exact h2, d1, ?_⟩
  have n : N (X + X ^ 2 : R[X]) = 1 := by
    simp only [N, map_add, D_X_pow, D1_X, D2_X, D3_X]
    norm_num
  rw [G0, n, d1]
  simp

/-- In characteristic 3, `t³` is killed by `D⁽¹⁾` and `D⁽²⁾` but not by `D⁽³⁾`, and
`G₀(t, t + t³) = −1`. -/
theorem char_three [CharP R 3] :
    D 1 (X ^ 3 : R[X]) = 0 ∧ D 2 (X ^ 3 : R[X]) = 0 ∧ D 3 (X ^ 3 : R[X]) = 1 ∧
      D 1 (X + X ^ 3 : R[X]) = 1 ∧ G0 (X + X ^ 3 : R[X]) = -1 := by
  have h3 : (3 : R[X]) = 0 := by exact_mod_cast natCast_eq_zero (R := R) 3
  have d1 : D 1 (X + X ^ 3 : R[X]) = 1 := by
    rw [map_add, D_X_pow, D1_X]; norm_num; linear_combination X ^ 2 * h3
  refine ⟨by rw [D_X_pow]; norm_num; linear_combination X ^ 2 * h3,
    by rw [D_X_pow]; norm_num; linear_combination h3, by rw [D_X_pow]; norm_num, d1, ?_⟩
  have n : N (X + X ^ 3 : R[X]) = -1 := by
    simp only [N, map_add, D_X_pow, D1_X, D2_X, D3_X]
    norm_num
    linear_combination (2 * X ^ 2) * h3
  rw [G0, n, d1]
  simp

/-! ### The functions killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾` (margin of page 121) -/

/-- `f` is killed by `D⁽¹⁾`, `D⁽²⁾` and `D⁽³⁾`. -/
def Killed (f : R[X]) : Prop := D 1 f = 0 ∧ D 2 f = 0 ∧ D 3 f = 0

/-- If `u` is killed, so is every polynomial in `u` (by the chain rule). -/
theorem Killed.comp {u : R[X]} (hu : Killed u) (f : R[X]) : Killed (f.comp u) := by
  obtain ⟨h1, h2, h3⟩ := chain f u
  obtain ⟨u1, u2, u3⟩ := hu
  exact ⟨by rw [h1, u1, mul_zero], by rw [h2, u1, u2]; ring, by rw [h3, u1, u2, u3]; ring⟩

lemma hasseDeriv_eq_zero_iff (k : ℕ) (f : R[X]) :
    D k f = 0 ↔ ∀ n, (n.choose k : R) * f.coeff n = 0 := by
  refine ⟨fun h n => ?_, fun h => ext fun n => by
    rw [hasseDeriv_coeff, coeff_zero]; exact h (n + k)⟩
  rcases lt_or_ge n k with hn | hn
  · simp [Nat.choose_eq_zero_of_lt hn]
  · simpa [hasseDeriv_coeff, Nat.sub_add_cancel hn] using congrArg (coeff · (n - k)) h

lemma natCast_isUnit (p : ℕ) [Fact p.Prime] [CharP R p] {m : ℕ} (h : ¬ p ∣ m) :
    IsUnit (m : R) := by
  have hz : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  simpa using (IsUnit.mk0 _ hz).map (ZMod.castHom (dvd_refl p) R)

lemma natCast_mul_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p] (c : ℕ) (a : R) :
    (c : R) * a = 0 ↔ p ∣ c ∨ a = 0 := by
  refine ⟨fun h => or_iff_not_imp_left.2 fun hc => (natCast_isUnit p hc).mul_right_eq_zero.1 h, ?_⟩
  rintro (h | h)
  · rw [(CharP.cast_eq_zero_iff R p c).2 h, zero_mul]
  · rw [h, mul_zero]

/-- In characteristic `p`, `f` is killed if and only if, for every exponent `n` that occurs
in `f`, `p` divides `C(n,1)`, `C(n,2)` and `C(n,3)`. -/
theorem killed_iff (p : ℕ) [Fact p.Prime] [CharP R p] (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → p ∣ n ∧ p ∣ n.choose 2 ∧ p ∣ n.choose 3 := by
  simp only [Killed, hasseDeriv_eq_zero_iff, natCast_mul_eq_zero p]
  constructor
  · rintro ⟨h1, h2, h3⟩ n hn
    exact ⟨by simpa using (h1 n).resolve_right hn, (h2 n).resolve_right hn,
      (h3 n).resolve_right hn⟩
  · intro h
    refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;>
      (by_cases hn : f.coeff n = 0; exact Or.inr hn; left)
    · simpa using (h n hn).1
    · exact (h n hn).2.1
    · exact (h n hn).2.2

/-- Lucas, for `k < p`: `p ∣ n` implies `p ∣ C(n, k)` when `0 < k`. -/
lemma dvd_choose_of_dvd (p : ℕ) [hp : Fact p.Prime] {n k : ℕ} (hk0 : 0 < k) (hkp : k < p)
    (hn : p ∣ n) : p ∣ n.choose k := by
  have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  rw [Nat.mod_eq_zero_of_dvd hn, Nat.mod_eq_of_lt hkp, Nat.choose_eq_zero_of_lt hk0,
    zero_mul] at this
  exact Nat.dvd_of_mod_eq_zero this

/-- Margin of page 121, `p > 3`: the killed polynomials are those in `X^p`. -/
theorem killed_iff_of_gt (p : ℕ) [Fact p.Prime] [CharP R p] (hp : 3 < p) (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → p ∣ n := by
  rw [killed_iff p]
  refine forall_congr' fun n => imp_congr_right fun _ => ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩
  · exact dvd_choose_of_dvd p (by norm_num) (by omega) h
  · exact dvd_choose_of_dvd p (by norm_num) hp h

/-- Margin of page 121, `p = 2`: the killed polynomials are those in `X^4`. -/
theorem killed_iff_two [CharP R 2] (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → 4 ∣ n := by
  rw [killed_iff 2]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  have l2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2) (p := 2)
  have l3 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 3) (p := 2)
  norm_num at l2 l3
  unfold Nat.ModEq at l2 l3
  constructor
  · rintro ⟨h1, h2, -⟩
    omega
  · intro h
    refine ⟨by omega, by omega, ?_⟩
    simp [show n % 2 = 0 by omega] at l3
    omega

/-- Margin of page 121, `p = 3`: the killed polynomials are those in `X^9`. -/
theorem killed_iff_three [CharP R 3] (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → 9 ∣ n := by
  rw [killed_iff 3]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  have l2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2) (p := 3)
  have l3 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 3) (p := 3)
  norm_num at l2 l3
  unfold Nat.ModEq at l2 l3
  constructor
  · rintro ⟨h1, -, h3⟩
    omega
  · intro h
    refine ⟨by omega, ?_, by omega⟩
    simp [show n % 3 = 0 by omega] at l2
    omega

/-! ### Rigidity (the Proposition of pages 121–123) -/

lemma killed_C (r : R) : Killed (C r) :=
  ⟨hasseDeriv_C 1 r (by norm_num), hasseDeriv_C 2 r (by norm_num), hasseDeriv_C 3 r (by norm_num)⟩

lemma D_lin (c d : R) :
    D 1 (C c * X + C d) = C c ∧ D 2 (C c * X + C d) = 0 ∧ D 3 (C c * X + C d) = 0 := by
  obtain ⟨h1, h2, h3⟩ := D_mul_X_of_const (killed_C c).1 (killed_C c).2.1 (killed_C c).2.2
  obtain ⟨k1, k2, k3⟩ := killed_C d
  simp [h2, h3, k2, k3]

/-- The invariance computation with `q = cX + d`, kept with its right-hand side:
`q · N(s) = D⁽²⁾s · D⁽²⁾(sq) − D⁽¹⁾s · D⁽³⁾(sq)`. -/
theorem N_mul_lin (s : R[X]) (c d : R) :
    (C c * X + C d) * N s =
      D 2 s * D 2 (s * (C c * X + C d)) - D 1 s * D 3 (s * (C c * X + C d)) := by
  obtain ⟨q1, q2, q3⟩ := D_lin c d
  rw [D_mul_two, D_mul_three, q1, q2, q3, N]
  ring

lemma coeff_lin_of_two_le (a b : R) {i : ℕ} (hi : 2 ≤ i) : (C a * X + C b).coeff i = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [coeff_add, coeff_C_mul_X, coeff_C]
  simp; omega

/-- The step of page 122: if `s · (cX + d) ≡ aX + b` modulo `X^(j+3)`, the coefficient of
`X^j` in `(cX + d) · N(s)` is `−C(j+3,3) · s₁ · (coefficient of X^(j+3) in s·(cX+d))`. -/
theorem step (s : R[X]) (a b c d : R) (j : ℕ)
    (h : X ^ (j + 3) ∣ s * (C c * X + C d) - (C a * X + C b)) :
    ((C c * X + C d) * N s).coeff j =
      -(((j + 3).choose 3 : ℕ) : R) * s.coeff 1 * (s * (C c * X + C d)).coeff (j + 3) := by
  set r := s * (C c * X + C d) - (C a * X + C b) with hr
  have e : s * (C c * X + C d) = r + (C a * X + C b) := by rw [hr]; ring
  obtain ⟨-, l2, l3⟩ := D_lin a b
  have hD2 : X ^ (j + 1) ∣ D 2 r := X_pow_dvd_iff.2 fun i hi => by
    rw [hasseDeriv_coeff, (X_pow_dvd_iff.1 h) (i + 2) (by omega), mul_zero]
  have hD3 : X ^ j ∣ D 3 r := X_pow_dvd_iff.2 fun i hi => by
    rw [hasseDeriv_coeff, (X_pow_dvd_iff.1 h) (i + 3) (by omega), mul_zero]
  obtain ⟨w2, hw2⟩ := hD2
  obtain ⟨w3, hw3⟩ := hD3
  have c3 : (D 3 r).coeff j = w3.coeff 0 := by
    rw [hw3, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
  have rj : r.coeff (j + 3) = (s * (C c * X + C d)).coeff (j + 3) := by
    rw [hr, coeff_sub, coeff_lin_of_two_le a b (by omega), sub_zero]
  have e2 : D 2 (s * (C c * X + C d)) = D 2 r := by rw [e, map_add, l2, add_zero]
  have e3 : D 3 (s * (C c * X + C d)) = D 3 r := by rw [e, map_add, l3, add_zero]
  rw [N_mul_lin, e2, e3, hw2, hw3, coeff_sub,
    show D 2 s * (X ^ (j + 1) * w2) = X ^ (j + 1) * (D 2 s * w2) by ring,
    show D 1 s * (X ^ j * w3) = X ^ j * (D 1 s * w3) by ring,
    coeff_X_pow_mul', coeff_X_pow_mul', ite_eq_right (by omega), ite_eq_left le_rfl, Nat.sub_self,
    mul_coeff_zero, ← c3, hasseDeriv_coeff, hasseDeriv_coeff, ← rj]
  simp
  ring

/-- The induction of pages 121–123, over any commutative ring: if `C(k,3)` is a unit for
`3 ≤ k < n`, `s₁` is a unit, `s · (cX + d)` has no `X²` term and the coefficients of `N(s)`
vanish below `X^(n−3)`, then `s · (cX + d)` is affine modulo `X^n`. -/
theorem rigidity_core (n : ℕ) (hC : ∀ k, 3 ≤ k → k < n → IsUnit ((k.choose 3 : ℕ) : R))
    (s : R[X]) (hs : IsUnit (s.coeff 1)) (c d : R) (h2 : (s * (C c * X + C d)).coeff 2 = 0)
    (hN : ∀ m, m + 3 < n → (N s).coeff m = 0) :
    X ^ n ∣ s * (C c * X + C d) -
      (C ((s * (C c * X + C d)).coeff 1) * X + C ((s * (C c * X + C d)).coeff 0)) := by
  set q := C c * X + C d
  set a := (s * q).coeff 1
  set b := (s * q).coeff 0
  have key : ∀ i, i < n → (s * q - (C a * X + C b)).coeff i = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases lt_or_ge i 3 with h3 | h3
      · interval_cases i <;> simp [a, b, coeff_C, h2]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h3
        have hdiv : X ^ (j + 3) ∣ s * q - (C a * X + C b) :=
          X_pow_dvd_iff.2 fun m hm => ih m hm (by omega)
        have hst := step s a b c d j hdiv
        have hz : (q * N s).coeff j = 0 := by
          have : X ^ (j + 1) ∣ N s := X_pow_dvd_iff.2 fun m hm => hN m (by omega)
          exact X_pow_dvd_iff.1 (this.mul_left q) j (by omega)
        rw [hz, neg_mul, neg_mul, zero_eq_neg] at hst
        have u := (hC (j + 3) (by omega) hi).mul hs
        rw [coeff_sub, coeff_lin_of_two_le a b (by omega), sub_zero]
        exact u.mul_right_eq_zero.1 hst
  exact X_pow_dvd_iff.2 key

lemma coeff_mul_lin_zero (s : R[X]) (c d : R) : (s * (C c * X + C d)).coeff 0 = d * s.coeff 0 := by
  rw [mul_add, coeff_add, ← mul_assoc, mul_coeff_zero, coeff_mul_C]
  simp [mul_comm]

lemma coeff_mul_lin_succ (s : R[X]) (c d : R) (i : ℕ) :
    (s * (C c * X + C d)).coeff (i + 1) = c * s.coeff i + d * s.coeff (i + 1) := by
  rw [mul_add, coeff_add, ← mul_assoc, coeff_mul_X, coeff_mul_C, coeff_mul_C]
  ring

/-- The Proposition of pages 121–123 with an explicit homography: for
`c = −s₂/s₁`, `s · (cX + 1) ≡ (s₁ + c s₀) X + s₀` modulo `X^n`. -/
theorem rigidity_explicit (n : ℕ) (hC : ∀ k, 3 ≤ k → k < n → IsUnit ((k.choose 3 : ℕ) : R))
    (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : ∀ m, m + 3 < n → (N s).coeff m = 0) :
    X ^ n ∣ s * (C (-(s.coeff 2 * (s.coeff 1)⁻¹ʳ)) * X + 1) -
      (C (s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0) * X + C (s.coeff 0)) := by
  set c := -(s.coeff 2 * (s.coeff 1)⁻¹ʳ)
  have h2 : (s * (C c * X + C 1)).coeff 2 = 0 := by
    rw [coeff_mul_lin_succ, one_mul]
    have := Ring.inverse_mul_cancel _ hs
    linear_combination (-(s.coeff 2)) * this
  have := rigidity_core n hC s hs c 1 h2 hN
  rwa [coeff_mul_lin_succ, coeff_mul_lin_zero, map_one, zero_add, one_mul, one_mul,
    add_comm (c * _)] at this

/-- The Proposition of pages 121–123 in `B = A[T]/(T^n)` (`G₀(t, s) = 0` in `B` reads
`X^n ∣ N(s)`, and `D⁽¹⁾s` is a unit of `B` iff `s₁` is a unit of `A`), over any commutative
ring `A` in which `C(k,3)` is a unit for `3 ≤ k < n`: `s = (at + b)/(ct + 1)` in `B`, with
`a, b, c ∈ A` and determinant `a − bc = s₁`. -/
theorem rigidity (n : ℕ) (hC : ∀ k, 3 ≤ k → k < n → IsUnit ((k.choose 3 : ℕ) : R))
    (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : X ^ n ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ n ∣ s * (C c * X + 1) - (C a * X + C b) :=
  ⟨s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0, s.coeff 0,
    -(s.coeff 2 * (s.coeff 1)⁻¹ʳ), by ring,
    rigidity_explicit n hC s hs fun m hm => X_pow_dvd_iff.1 hN m (by omega)⟩

/-- Characteristic `p > 3`, `B = A[T]/(T^p)`: the Proposition of pages 121–122, over any
ring of characteristic `p` (no hypothesis on `Pic(A)`). -/
theorem rigidity_of_gt (p : ℕ) [hp : Fact p.Prime] [CharP R p] (s : R[X])
    (hs : IsUnit (s.coeff 1)) (hN : X ^ p ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ p ∣ s * (C c * X + 1) - (C a * X + C b) := by
  refine rigidity p (fun k hk3 hkp => natCast_isUnit p fun hdvd => ?_) s hs hN
  have hf : p ∣ k.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial (show 3 ≤ k from hk3), mul_assoc]
    exact hdvd.mul_right _
  exact absurd ((Nat.Prime.dvd_factorial hp.out).1 hf) (by omega)

/-- `B = A[T]/(T^4)`, the level `p²` for `p = 2` (page 123): only `C(3,3) = 1` occurs, and
the statement holds over any commutative ring. -/
theorem rigidity_four (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : X ^ 4 ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ 4 ∣ s * (C c * X + 1) - (C a * X + C b) :=
  rigidity 4 (fun k hk3 hk4 => by
    obtain rfl : k = 3 := by omega
    simp) s hs hN

/-- `B = A[T]/(T^9)`, the level `p²` for `p = 3` (page 123, right-hand column):
`C(k,3) ≢ 0 mod 3` for `3 ≤ k ≤ 8`. -/
theorem rigidity_nine [CharP R 3] (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : X ^ 9 ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ 9 ∣ s * (C c * X + 1) - (C a * X + C b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rigidity 9 (fun k hk3 hk9 => natCast_isUnit 3 ?_) s hs hN
  interval_cases k <;> decide

/-- Characteristic `0` (`A` a `ℚ`-algebra), in `A[X]` itself: `N(s) = 0` with `s₁` a unit
forces `s · (cX + 1) = aX + b`. -/
theorem rigidity_char_zero [Algebra ℚ R] (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : N s = 0) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ s * (C c * X + 1) = C a * X + C b := by
  have hC : ∀ k, 3 ≤ k → IsUnit ((k.choose 3 : ℕ) : R) := fun k hk => by
    have h0 : ((k.choose 3 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simpa using (IsUnit.mk0 _ h0).map (algebraMap ℚ R)
  refine ⟨s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0, s.coeff 0,
    -(s.coeff 2 * (s.coeff 1)⁻¹ʳ), by ring, ?_⟩
  set f := s * (C (-(s.coeff 2 * (s.coeff 1)⁻¹ʳ)) * X + 1) -
      (C (s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0) * X + C (s.coeff 0))
  have hd := rigidity_explicit (f.natDegree + 1) (fun k hk _ => hC k hk) s hs
    (fun m _ => by rw [hN, coeff_zero])
  have hf : f = 0 := by
    ext i
    rw [coeff_zero]
    rcases lt_or_ge i (f.natDegree + 1) with hi | hi
    · exact X_pow_dvd_iff.1 hd i hi
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact sub_eq_zero.1 hf

/-! ### The truncated ring `A[T]/(T^(p^N))` -/

/-- In characteristic `p`, `D⁽ᵏ⁾` for `k < p^N` is `A[X^(p^N)]`-linear on multiples of
`X^(p^N)`; hence it passes to `A[T]/(T^(p^N))`. -/
theorem hasseDeriv_X_pow_mul (p M : ℕ) [hp : Fact p.Prime] [CharP R p] {k : ℕ}
    (hk : k < p ^ M) (g : R[X]) : D k (X ^ (p ^ M) * g) = X ^ (p ^ M) * D k g :=
  Polynomial.hasseDeriv_X_pow_mul p hk g

/-- `N(s)` modulo `X^(p^N)` depends only on `s` modulo `X^(p^N)` (`3 < p^N`), so
`G₀(t, s) = 0` in `A[T]/(T^(p^N))` reads `X^(p^N) ∣ N(s)`. -/
theorem N_add_X_pow_mul (p M : ℕ) [Fact p.Prime] [CharP R p] (hM : 3 < p ^ M) (s g : R[X]) :
    X ^ (p ^ M) ∣ N (s + X ^ (p ^ M) * g) - N s := by
  rw [N, N, map_add, map_add, map_add, hasseDeriv_X_pow_mul p M (by omega),
    hasseDeriv_X_pow_mul p M (by omega), hasseDeriv_X_pow_mul p M (by omega)]
  exact ⟨2 * D 2 s * D 2 g + X ^ (p ^ M) * D 2 g ^ 2 - D 3 s * D 1 g - D 3 g * D 1 s
    - X ^ (p ^ M) * D 3 g * D 1 g, by ring⟩

/-- `cX + d` with `d` a unit is coprime to `X` (`Polynomial.isCoprime_X_iff`), hence to `Xⁿ`. -/
lemma X_pow_dvd_of_mul_lin {n : ℕ} {c d : R} (hd : IsUnit d) {F : R[X]}
    (h : X ^ n ∣ F * (C c * X + C d)) : X ^ n ∣ F :=
  (Polynomial.isCoprime_X_iff.2 (by simpa using hd)).pow_left.dvd_of_dvd_mul_right h

/-- The converse in `A[T]/(T^(p^N))`, `3 < p^N`: a homography `(at + b)/(ct + d)` with
`a, b, c, d ∈ A` and `d` a unit has `G₀ = 0`. -/
theorem N_of_homography_trunc (p M : ℕ) [Fact p.Prime] [CharP R p] (hM : 3 < p ^ M)
    (s : R[X]) {a b c d : R} (hd : IsUnit d)
    (h : X ^ (p ^ M) ∣ s * (C c * X + C d) - (C a * X + C b)) : X ^ (p ^ M) ∣ N s := by
  obtain ⟨g, hg⟩ := h
  have e : s * (C c * X + C d) = (C a * X + C b) + X ^ (p ^ M) * g := by
    rw [← hg]; ring
  obtain ⟨-, l2, l3⟩ := D_lin a b
  have key := N_mul_lin s c d
  rw [e, map_add (D 2) (C a * X + C b), map_add (D 3) (C a * X + C b), l2, l3,
    hasseDeriv_X_pow_mul p M (by omega),
    hasseDeriv_X_pow_mul p M (by omega), zero_add, zero_add] at key
  refine X_pow_dvd_of_mul_lin (c := c) hd ⟨D 2 s * D 2 g - D 1 s * D 3 g, ?_⟩
  rw [mul_comm, key]
  ring

/-- The Proposition of pages 121–123 as an equivalence in `A[T]/(T^p)`, `p > 3`. -/
theorem rigidity_iff_of_gt (p : ℕ) [hp : Fact p.Prime] [CharP R p] (hp3 : 3 < p) (s : R[X])
    (hs : IsUnit (s.coeff 1)) :
    X ^ p ∣ N s ↔
      ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ p ∣ s * (C c * X + 1) - (C a * X + C b) := by
  refine ⟨rigidity_of_gt p s hs, ?_⟩
  rintro ⟨a, b, c, -, h⟩
  simpa using N_of_homography_trunc p 1 (by simpa using hp3) s (d := 1) isUnit_one
    (by simpa using h)

/-! ### The determinant cannot be normalised to `1` -/

/-- If `uX` is a homography of determinant `1` modulo `X³`, then `u` is a square. -/
theorem det_one_square (u : R) {a b c d : R} (hdet : a * d - b * c = 1)
    (h : X ^ 3 ∣ C u * X * (C c * X + C d) - (C a * X + C b)) : ∃ v, u = v ^ 2 := by
  have h0 := X_pow_dvd_iff.1 h 0 (by norm_num)
  have h1 := X_pow_dvd_iff.1 h 1 (by norm_num)
  rw [coeff_sub, coeff_mul_lin_zero] at h0
  rw [coeff_sub, coeff_mul_lin_succ] at h1
  simp [coeff_C, coeff_X] at h0 h1
  refine ⟨u * d, ?_⟩
  linear_combination (-u) * hdet - u * d * h1 - u * c * h0

/-- Page 121 adds « avec `ad − bc = 1` »: in `𝔽₅[T]/(T^5)`, `s = 2t` has `G₀ = 0` and
`D⁽¹⁾s = 2` a unit, and is `(2t + 0)/(0·t + 1)`, but no homography of determinant `1` gives
it, `2` not being a square mod `5`. -/
theorem det_one_counterexample :
    N (C 2 * X : (ZMod 5)[X]) = 0 ∧ IsUnit ((C 2 * X : (ZMod 5)[X]).coeff 1) ∧
      X ^ 5 ∣ (C 2 * X : (ZMod 5)[X]) * (C 0 * X + C 1) - (C 2 * X + C 0) ∧
      ¬ ∃ a b c d : ZMod 5, a * d - b * c = 1 ∧
        X ^ 5 ∣ (C 2 * X : (ZMod 5)[X]) * (C c * X + C d) - (C a * X + C b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨-, l2, l3⟩ := D_lin (2 : ZMod 5) 0
    rw [map_zero, add_zero] at l2 l3
    simp [N, l2, l3]
  · rw [coeff_C_mul_X]; exact IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide)
  · simp
  · rintro ⟨a, b, c, d, hdet, h⟩
    obtain ⟨v, hv⟩ := det_one_square 2 hdet
      (dvd_trans (pow_dvd_pow X (by norm_num)) h)
    revert v; decide

open CategoryTheory CochainComplex HomComplex

/-! ## Pages 233–235: the derived morphism defined by a torsor

Finding `93-derived-morphism-homotopy-torsor`.

The abelian-group version of pages 234–235: `P` a torsor under an abelian group `G`,
`u : P → Hom⁰(K', K'')`, `k : G → Hom⁻¹(K', K'')` additive with `u(g + p) − u(p) = δ(k g)`
(`δ` is Mathlib's differential of the Hom complex, `dk + kd`), and `u(p)` morphisms of complexes.

* `Gbar`, `ι`, `j`, `e`: the extension `0 → G → Ḡ → ℤ → 0` with `j⁻¹(1) = P`, built as a quotient of
  `G × ℤ[P]` without choosing a point; `ι_injective`, `j_eq_zero_iff`, `j_surjective` (so
  `𝓛 = [G → Ḡ]` is quasi-isomorphic to `ℤ`), `e_injective`, `j_eq_one_iff` (`j⁻¹(1) = P`).
* `φ0`, `φ0_e`, `φ0_ι`, `δ_φ0`: `φ⁰ : Ḡ → Hom⁰` with `φ⁰|_P = u`, `φ⁰ ∘ ι = δ ∘ k`, `δ ∘ φ⁰ = 0`:
  `(k, φ⁰)` is a morphism of complexes `𝓛 → Hom•(K', K'')`.
* `quotient_map_eq`, `derived_map_eq`: the class of `u(p)` in the homotopy category, and in the
  derived category, does not depend on `p`; `φ0_of_j_eq_one`: it is the class `φ` gives on
  `j⁻¹(1)`, the generator of `H⁰(𝓛) = ℤ`.

Not formalised: the sheaf version (where `P` may have no global section and the point is that no
covering is needed), and the de Rham application. -/

section Torsor

variable (G P : Type*) [AddCommGroup G] [AddTorsor G P]

/-- The relations `e(g + p) − e(p) = g` defining `Ḡ`. -/
def barRel : AddSubgroup (G × FreeAbelianGroup P) :=
  AddSubgroup.closure (Set.range fun x : G × P =>
    ((-x.1, FreeAbelianGroup.of (x.1 +ᵥ x.2) - FreeAbelianGroup.of x.2) : G × FreeAbelianGroup P))

/-- `Ḡ`, the extension of `ℤ` by `G` with `j⁻¹(1) = P`, built without choosing a point. -/
abbrev Gbar := (G × FreeAbelianGroup P) ⧸ barRel G P

variable {G P}

/-- `G → Ḡ`. -/
def ι : G →+ Gbar G P := (QuotientAddGroup.mk' _).comp (AddMonoidHom.inl G _)

/-- `P → Ḡ`. -/
def e (p : P) : Gbar G P := QuotientAddGroup.mk' _ (0, FreeAbelianGroup.of p)

/-- `j : Ḡ → ℤ`. -/
def j : Gbar G P →+ ℤ :=
  QuotientAddGroup.lift _ ((FreeAbelianGroup.lift fun _ : P => (1 : ℤ)).comp
    (AddMonoidHom.snd G _)) (by
    rw [barRel, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simp)

theorem j_ι (g : G) : j (ι (P := P) g) = 0 := by simp [j, ι]

theorem j_e (p : P) : j (e (G := G) p) = 1 := by simp [j, e]

theorem ι_add_e (g : G) (p : P) : ι g + e p = e (g +ᵥ p) := by
  have h : ((-g, FreeAbelianGroup.of (g +ᵥ p) - FreeAbelianGroup.of p) :
      G × FreeAbelianGroup P) ∈ barRel G P := AddSubgroup.subset_closure ⟨(g, p), rfl⟩
  simp only [ι, e, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
    QuotientAddGroup.coe_mk', ← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
  convert h using 1
  ext <;> simp
  abel

/-- A retraction of `ι`, depending on a point `p₀`. -/
def r (p₀ : P) : Gbar G P →+ G :=
  QuotientAddGroup.lift _ ((AddMonoidHom.fst G _) +
    (FreeAbelianGroup.lift fun p : P => p -ᵥ p₀).comp (AddMonoidHom.snd G _)) (by
    rw [barRel, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simp [vadd_vsub_assoc])

theorem r_ι (p₀ : P) (g : G) : r p₀ (ι g) = g := by simp [r, ι]

theorem ι_injective : Function.Injective (ι : G →+ Gbar G P) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  exact Function.LeftInverse.injective (r_ι p₀)

/-- Every element of `Ḡ` is `ι g + n • e p₀`. -/
theorem eq_ι_add (p₀ : P) (x : Gbar G P) : x = ι (r p₀ x) + j x • e p₀ := by
  let dif : Gbar G P →+ Gbar G P :=
    AddMonoidHom.id _ - (ι.comp (r p₀) + (zmultiplesHom _ (e p₀)).comp j)
  have hD : dif = 0 := by
    refine QuotientAddGroup.addMonoidHom_ext _ ?_
    set dif' := dif.comp (QuotientAddGroup.mk' (barRel G P))
    have h1 : dif'.comp (AddMonoidHom.inl _ _) = 0 := by
      ext g
      simp [dif', dif, r, ι, j]
    have h2 : dif'.comp (AddMonoidHom.inr _ _) = 0 := by
      ext p
      have h3 := ι_add_e (p -ᵥ p₀) p₀
      rw [vsub_vadd] at h3
      simp only [dif', dif, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inr_apply,
        AddMonoidHom.sub_apply, AddMonoidHom.id_apply, AddMonoidHom.add_apply,
        AddMonoidHom.zero_apply]
      change e p - (ι (r p₀ (e p)) + zmultiplesHom _ (e p₀) (j (e p))) = 0
      rw [j_e, ← h3, map_add, r_ι]
      simp [r, e]
    ext y
    have hy : y = (AddMonoidHom.inl _ _ y.1) + (AddMonoidHom.inr _ _ y.2) := by ext <;> simp
    rw [AddMonoidHom.zero_comp, AddMonoidHom.zero_apply, hy, map_add,
      ← AddMonoidHom.comp_apply dif' (AddMonoidHom.inl _ _),
      ← AddMonoidHom.comp_apply dif' (AddMonoidHom.inr _ _), h1, h2]
    simp
  have := congrArg (· x) hD
  simpa [dif, sub_eq_zero] using this

/-- The complex `𝓛 = [G → Ḡ]` is quasi-isomorphic to `ℤ`: `ι` is injective (above), its image is
the kernel of `j`, and `j` is onto. -/
theorem j_eq_zero_iff (x : Gbar G P) : j x = 0 ↔ ∃ g, ι g = x := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  refine ⟨fun h => ⟨r p₀ x, ?_⟩, fun ⟨g, hg⟩ => hg ▸ j_ι g⟩
  conv_rhs => rw [eq_ι_add p₀ x, h, zero_zsmul, add_zero]

theorem j_surjective : Function.Surjective (j : Gbar G P →+ ℤ) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  exact fun n => ⟨n • e p₀, by rw [map_zsmul, j_e, smul_eq_mul, mul_one]⟩

theorem r_e (p₀ p : P) : r p₀ (e (G := G) p) = p -ᵥ p₀ := by simp [r, e]

/-- `j⁻¹(1) = P`: `e` is a bijection of `P` onto `j⁻¹(1)`. -/
theorem e_injective : Function.Injective (e : P → Gbar G P) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  intro p p' h
  have := congrArg (r p₀) h
  rw [r_e, r_e] at this
  rw [← vsub_vadd p p₀, this, vsub_vadd]

theorem j_eq_one_iff (x : Gbar G P) : j x = 1 ↔ ∃ p, e p = x := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  refine ⟨fun h => ⟨r p₀ x +ᵥ p₀, ?_⟩, fun ⟨p, hp⟩ => hp ▸ j_e p⟩
  rw [← ι_add_e]
  conv_rhs => rw [eq_ι_add p₀ x, h, one_zsmul]

section Complex

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {K' K'' : CochainComplex C ℤ}
  (k : G →+ Cochain K' K'' (-1)) (u : P → Cochain K' K'' 0)
  (hu : ∀ (g : G) (p : P), u (g +ᵥ p) - u p = δ (-1) 0 (k g))

/-- `φ⁰ : Ḡ → Hom⁰(K', K'')`, equal to `dk + kd` on `G` and to `u` on `P`. -/
def φ0 : Gbar G P →+ Cochain K' K'' 0 :=
  QuotientAddGroup.lift _ ((((δ_hom ℤ K' K'' (-1) 0).toAddMonoidHom.comp k).comp
      (AddMonoidHom.fst G _)) + (FreeAbelianGroup.lift u).comp (AddMonoidHom.snd G _)) (by
    rw [barRel, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.add_apply,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
      map_neg, map_sub, FreeAbelianGroup.lift_apply_of, LinearMap.toAddMonoidHom_coe]
    rw [hu]
    simp [δ_hom])

theorem φ0_e (p : P) : φ0 k u hu (e p) = u p := by simp [φ0, e]

/-- `φ⁰ ∘ ι = δ ∘ k`: the square of `φ : 𝓛 → Hom•(K', K'')` in degrees `−1 → 0`. -/
theorem φ0_ι (g : G) : φ0 k u hu (ι g) = δ (-1) 0 (k g) := by simp [φ0, ι, δ_hom]

variable (hc : ∀ p, δ 0 1 (u p) = 0)
include hu hc

/-- `δ ∘ φ⁰ = 0`: the square in degrees `0 → 1`, so `φ` is a morphism of complexes. -/
theorem δ_φ0 (x : Gbar G P) : δ 0 1 (φ0 k u hu x) = 0 := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  rw [eq_ι_add p₀ x, map_add, map_zsmul, φ0_ι, φ0_e, δ_add, δ_δ, δ_smul, hc, smul_zero,
    add_zero]

/-- The morphism of complexes `u(p) : K' → K''`. -/
def homOf' (p : P) : K' ⟶ K'' := Cocycle.homOf (Cocycle.mk (u p) 1 (zero_add 1) (hc p))

/-- `k(p' − p)` is a homotopy from `u(p')` to `u(p)`. -/
def homotopy (p p' : P) : Homotopy (homOf' u hc p') (homOf' u hc p) :=
  (Cochain.equivHomotopy _ _).symm ⟨k (p' -ᵥ p), by
    simp only [homOf', Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe]
    rw [← hu, vsub_vadd, sub_add_cancel]⟩

/-- **Pages 234–235.** The class of `u(p)` in the homotopy category does not depend on `p`:
the morphism defined by `(P, u, k)` needs no choice of a point. -/
theorem quotient_map_eq (p p' : P) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (homOf' u hc p) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (homOf' u hc p') :=
  (HomotopyCategory.eq_of_homotopy _ _ (homotopy k u hu hc p p')).symm

omit hc in
/-- The value of `φ⁰` on `j⁻¹(1)` is `u(p)` for some `p`: the class given by `φ` on the
generator of `H⁰(𝓛) = ℤ` is the class of any `u(p)`. -/
theorem φ0_of_j_eq_one (x : Gbar G P) (hx : j x = 1) : ∃ p, φ0 k u hu x = u p := by
  obtain ⟨p, rfl⟩ := (j_eq_one_iff x).1 hx
  exact ⟨p, φ0_e k u hu p⟩

end Complex

section Derived

open CategoryTheory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] {K' K'' : CochainComplex C ℤ}
  (k : G →+ Cochain K' K'' (-1)) (u : P → Cochain K' K'' 0)
  (hu : ∀ (g : G) (p : P), u (g +ᵥ p) - u p = δ (-1) 0 (k g)) (hc : ∀ p, δ 0 1 (u p) = 0)
include hu

/-- The same in the derived category `D(C)`: `(P, u, k)` defines one morphism `K' → K''`. -/
theorem derived_map_eq (p p' : P) :
    DerivedCategory.Q.map (homOf' u hc p) = DerivedCategory.Q.map (homOf' u hc p') :=
  (DerivedCategory.Q_map_eq_of_homotopy (h := homotopy k u hu hc p p')).symm

end Derived

end Torsor

end Grothendieck.Folder93

/-!
## Pages 193–194 and 208: the `p`-curvature in rank one

Over a commutative ring `A` of characteristic `p` with a derivation `D`, in `Module.End ℤ A`
(`μ c` is multiplication by `c`):

* `iterate_leibniz`, `pDerivation`: `Dᵖ` is again a derivation;
* `jacobson`: `(D + μ a)ᵖ = Dᵖ + μ (aᵖ + D^{p-1} a)` (Jacobson's formula in rank one), proved by
  differentiating `(D + t·μ a)ᵖ` in `t` (`Polynomial` over `Module.End ℤ A`);
* `pCurvature_eq_zero`: if `y` is a unit with `D y + a y = 0`, the connection `∇ = D + a` with
  form `ω = -dy/y` has `(∇_D)ᵖ = ∇_{Dᵖ}`: its `p`-curvature vanishes (the easy direction);
* `jacobson_logDeriv`, `jacobson_logDeriv_of_pow_eq_zero`: hence `aᵖ + D^{p-1} a = -(Dᵖ y)/y`,
  and `aᵖ + D^{p-1} a = 0` when `Dᵖ = 0`.
-/

namespace Grothendieck.Folder93.PCurvature

open Finset Polynomial

section CharLemmas

variable {R : Type*} [Ring R] (p : ℕ) [hp : Fact p.Prime] (hR : (p : R) = 0)
include hR

theorem nsmul_choose_eq_zero {k : ℕ} (hk0 : k ≠ 0) (hkp : k < p) (z : R) :
    p.choose k • z = 0 := by
  obtain ⟨j, hj⟩ := Nat.Prime.dvd_choose_self hp.out hk0 hkp
  rw [nsmul_eq_mul, hj, Nat.cast_mul, hR, zero_mul, zero_mul]

theorem eq_zero_of_mul_natCast {n : ℕ} (hn0 : 0 < n) (hnp : n < p) {z : R}
    (h : z * n = 0) : z = 0 := by
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_of_lt_prime hn0.ne' hnp hp.out).symm (Nat.Prime.one_lt hp.out)
  have h1 : ((n * k : ℕ) : R) = 1 := by
    rw [← Nat.div_add_mod (n * k) p, hk, Nat.cast_add, Nat.cast_mul, hR, zero_mul, zero_add,
      Nat.cast_one]
  rw [← mul_one z, ← h1, Nat.cast_mul, ← mul_assoc, h, zero_mul]

end CharLemmas

section Abstract

variable {A R : Type*} [Ring R] (M : A → R) (D : A → A) (L : R)
  (hL : ∀ c, L * M c = M c * L + M (D c))
include hL

/-- Leibniz's rule for `Lⁿ` against a family `M c` with `[L, M c] = M (D c)`. -/
theorem pow_mul_eq_sum (n : ℕ) (c : A) :
    L ^ n * M c = ∑ ij ∈ antidiagonal n, n.choose ij.1 • (M (D^[ij.1] c) * L ^ ij.2) := by
  have key : ∀ x j, L * (M x * L ^ j) = M x * L ^ (j + 1) + M (D x) * L ^ j := fun x j => by
    rw [← mul_assoc, hL, add_mul, mul_assoc, ← pow_succ']
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (fun i j => M (D^[i] c) * L ^ j) n, pow_succ',
      mul_assoc, ih, mul_sum]
    simp only [mul_smul_comm, key, smul_add, sum_add_distrib, Function.iterate_succ_apply']
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

variable (p : ℕ) [hp : Fact p.Prime] (hR : (p : R) = 0)
include hR

/-- In characteristic `p`, `[Lᵖ, M c] = M (Dᵖ c)`. -/
theorem pow_char_mul (c : A) : L ^ p * M c = M c * L ^ p + M (D^[p] c) := by
  rw [pow_mul_eq_sum M D L hL, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => p.choose i • (M (D^[i] c) * L ^ j)), sum_range_succ', sum_eq_single (p - 1)]
  · simp [Nat.sub_add_cancel (Nat.Prime.one_le hp.out), add_comm]
  · intro k hk hne
    exact nsmul_choose_eq_zero p hR (Nat.succ_ne_zero k) (by simp at hk; omega) _
  · intro h; simp at h; have := (Nat.Prime.one_le hp.out); omega

/-- In characteristic `p`, `∑ᵢ Lⁱ (M c) L^{p-1-i} = M (D^{p-1} c)`. -/
theorem sum_pow_mul_pow (c : A) :
    ∑ i ∈ range p, L ^ i * M c * L ^ (p - 1 - i) = M (D^[p - 1] c) := by
  have hs : ∀ n k, ∑ i ∈ range n, i.choose k = n.choose (k + 1) := fun n k => by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, Nat.choose_succ_succ', add_comm]
  have step : ∀ i ∈ range p, L ^ i * M c * L ^ (p - 1 - i) =
      ∑ k ∈ range p, i.choose k • (M (D^[k] c) * L ^ (p - 1 - k)) := by
    intro i hi
    rw [mem_range] at hi
    rw [pow_mul_eq_sum M D L hL, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k j => i.choose k • (M (D^[k] c) * L ^ j)), sum_mul]
    symm
    rw [← sum_subset (range_subset_range.2 (by omega : i + 1 ≤ p)) fun k _ hk => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega), zero_smul]]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [smul_mul_assoc, mul_assoc, ← pow_add]
    congr 3
    omega
  rw [sum_congr rfl step, sum_comm]
  simp_rw [← sum_smul, hs]
  rw [sum_eq_single (p - 1)]
  · simp [Nat.sub_add_cancel (Nat.Prime.one_le hp.out)]
  · intro k hk hne
    exact nsmul_choose_eq_zero p hR (Nat.succ_ne_zero k) (by simp at hk; omega) _
  · intro h; simp at h; have := (Nat.Prime.one_le hp.out); omega

end Abstract

section Ring

variable {A : Type*} [CommRing A] (D : Derivation ℤ A A)

local notation "μ" => LinearMap.mulLeft ℤ
local notation "δ" => (D : Module.End ℤ A)

/-- Leibniz's rule as an identity of operators: `D ∘ μ c = μ c ∘ D + μ (D c)`
(`Derivation.lie_mulLeft`). -/
theorem comm_mulLeft (c : A) :
    (D : Module.End ℤ A) * μ c = μ c * (D : Module.End ℤ A) + μ (D c) := by
  rw [← D.lie_mulLeft, Ring.lie_def, add_sub_cancel]

variable (p : ℕ) [hp : Fact p.Prime] [CharP A p]

omit hp in
theorem natCast_end : ((p : ℕ) : Module.End ℤ A) = 0 := by
  ext x; simp [Module.End.natCast_apply, nsmul_eq_mul]

/-- **Statement 1.** In characteristic `p`, the iterate `Dᵖ` satisfies Leibniz's rule. -/
theorem iterate_leibniz (x y : A) : D^[p] (x * y) = x * D^[p] y + D^[p] x * y := by
  have := congrArg (· y) (pow_char_mul μ D (D : Module.End ℤ A) (comm_mulLeft D) p
    (natCast_end p) x)
  simpa [Module.End.pow_apply, mul_comm] using this

/-- `Dᵖ` packaged as a derivation. -/
def pDerivation : Derivation ℤ A A :=
  Derivation.mk' ((D : Module.End ℤ A) ^ p) fun x y => by
    simp [Module.End.pow_apply, iterate_leibniz, smul_eq_mul]; ring

theorem pDerivation_apply (x : A) : pDerivation D p x = D^[p] x := by
  simp [pDerivation, Module.End.pow_apply]

/-- **Statement 2 (Jacobson's formula in rank one).** -/
theorem jacobson (a : A) :
    ((D : Module.End ℤ A) + μ a) ^ p = (D : Module.End ℤ A) ^ p + μ (a ^ p + D^[p - 1] a) := by
  set q : (Module.End ℤ A)[X] := C δ + X * C (μ a) with hqdef
  clear_value q
  have hq : ∀ c, q * C (μ c) = C (μ c) * q + C (μ (D c)) := by
    intro c
    have hc : μ a * μ c = μ c * μ a := by ext x; simp; ring
    have hX : C (μ c) * (X * C (μ a)) = X * (C (μ a) * C (μ c)) := by
      rw [← mul_assoc, ← X_mul, mul_assoc, ← C_mul, ← C_mul, hc]
    rw [hqdef, add_mul, mul_add, ← C_mul, comm_mulLeft, C_add, mul_assoc, hX, C_mul]
    abel
  have hP : ((p : ℕ) : (Module.End ℤ A)[X]) = 0 := by
    rw [← map_natCast C, natCast_end, C_0]
  have dq : derivative q = C (μ a) := by simp [hqdef]
  have hdpow : ∀ n, derivative (q ^ n) = ∑ i ∈ range n, q ^ i * C (μ a) * q ^ (n - 1 - i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, derivative_mul, ih, dq, sum_range_succ, sum_mul]
      refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) ?_
      · rw [mem_range] at hi
        rw [mul_assoc, ← pow_succ, show n - 1 - i + 1 = n + 1 - 1 - i by omega]
      · simp
  have hd : derivative (q ^ p) = C (μ (D^[p - 1] a)) := by
    rw [hdpow, sum_pow_mul_pow (fun c => C (μ c)) D q hq p hP a]
  have hdeg : q.natDegree ≤ 1 := by
    rw [hqdef, X_mul, add_comm]; exact natDegree_linear_le (a := μ a) (b := δ)
  have ev : ∀ x : Module.End ℤ A, (∀ r, Commute r x) →
      eval₂ (RingHom.id _) x (q ^ p) = (δ + μ a * x) ^ p := by
    intro x hx
    have := map_pow (eval₂RingHom' (RingHom.id _) x hx) q p
    simpa [hqdef, eval₂_X_mul, (hx _).eq] using this
  have key : q ^ p = C (δ ^ p) + C (μ (D^[p - 1] a)) * X + C (μ a ^ p) * X ^ p := by
    ext n : 1
    simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    have hp2 := (Nat.Prime.two_le hp.out)
    rcases lt_trichotomy n p with h | rfl | h
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [coeff_zero_eq_eval_zero, eval, ev 0 fun r => Commute.zero_right r]
        simp; omega
      · have hd' := congrArg (coeff · (n - 1)) hd
        simp only [coeff_derivative, coeff_C, Nat.sub_add_cancel hn0] at hd'
        by_cases hn1 : n = 1
        · subst hn1; simpa [show (1 : ℕ) ≠ p by omega] using hd'
        · simp only [show n - 1 ≠ 0 by omega, ite_false] at hd'
          simp only [show n ≠ 0 by omega, hn1, show n ≠ p by omega, ite_false, add_zero]
          refine eq_zero_of_mul_natCast p (natCast_end p) (z := (q ^ p).coeff n) hn0 h ?_
          rwa [← Nat.cast_add_one, Nat.sub_add_cancel hn0] at hd'
    · simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, ite_false, ite_true, zero_add]
      have hc := coeff_pow_of_natDegree_le (m := n) hdeg
      rw [mul_one] at hc
      rw [hc, hqdef]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt (natDegree_pow_le.trans_lt (by nlinarith))]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ p by omega, ite_false,
        add_zero]
  have h1 := ev 1 fun r => Commute.one_right r
  rw [key, C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial] at h1
  simp only [eval₂_add, eval₂_C, eval₂_monomial, RingHom.id_apply, one_pow, mul_one] at h1
  rw [← h1, LinearMap.pow_mulLeft]
  ext x; simp; ring


omit [CharP A p] in
theorem iterate_one : D^[p] (1 : A) = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel (Nat.Prime.one_le hp.out)).symm⟩
  rw [hm, Function.iterate_succ_apply, Derivation.map_one_eq_zero,
    Function.iterate_fixed (map_zero D)]

/-- **Statement 3 (the easy direction in rank one).** If the unit `y` is horizontal for the
connection `D + a` on `A`, i.e. `D y + a y = 0`, then `(D + a)ᵖ = Dᵖ + ω(Dᵖ)` with
`ω = -dy/y` the connection form: the `p`-curvature `(∇_D)ᵖ - ∇_{Dᵖ}` vanishes. -/
theorem pCurvature_eq_zero (y z a : A) (hu : y * z = 1) (hy : D y + a * y = 0) :
    (δ + μ a) ^ p = δ ^ p + μ (-(D^[p] y) * z) := by
  have hinv : μ z * μ y = 1 := by ext x; simp [← mul_assoc, mul_comm z y, hu]
  -- conjugation by the unit `y` (`Derivation.mulLeft_mul_mul_mulLeft_inv`)
  have hconj : δ + μ a = μ y * δ * μ z := by
    rw [show μ y * δ * μ z = _ from D.mulLeft_mul_mul_mulLeft_inv (Units.mkOfMulEqOne y z hu)]
    have hza : a = -(z * D y) := by linear_combination z * hy - a * hu
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply, hza]
    change _ = _ - z * D y * x
    ring
  have hpow : ∀ n, (μ y * δ * μ z) ^ (n + 1) = μ y * δ ^ (n + 1) * μ z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ δ (n + 1)]
      calc μ y * δ ^ (n + 1) * μ z * (μ y * δ * μ z)
          = μ y * δ ^ (n + 1) * (μ z * μ y) * δ * μ z := by
            simp only [mul_assoc]
        _ = _ := by rw [hinv, mul_one]; simp only [mul_assoc]
  have hl := iterate_leibniz D p y z
  rw [hu, iterate_one] at hl
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel (Nat.Prime.one_le hp.out)).symm⟩
  rw [hconj, hm, hpow, ← hm, mul_assoc,
    pow_char_mul μ D δ (comm_mulLeft D) p (natCast_end p)]
  ext x
  simp [Module.End.pow_apply, mul_add]
  linear_combination (D^[p] x) * hu - x * hl

/-- Statements 2 and 3 together: `a ^ p + D^{p-1} a = -(Dᵖ y)/y` for `a = -Dy/y`. -/
theorem jacobson_logDeriv (y z a : A) (hu : y * z = 1) (hy : D y + a * y = 0) :
    a ^ p + D^[p - 1] a = -(D^[p] y) * z := by
  have h := congrArg (· 1) ((jacobson D p a).symm.trans (pCurvature_eq_zero D p y z a hu hy))
  simpa [Module.End.pow_apply, iterate_one] using h

/-- When `Dᵖ = 0` (as for `d/dX` on `𝔽_p(X)`), a logarithmic derivative `a = -Dy/y`
satisfies `a ^ p + D^{p-1} a = 0`. -/
theorem jacobson_logDeriv_of_pow_eq_zero (hD : ∀ x, D^[p] x = 0) (y z a : A) (hu : y * z = 1)
    (hy : D y + a * y = 0) : a ^ p + D^[p - 1] a = 0 := by
  rw [jacobson_logDeriv D p y z a hu hy, hD, neg_zero, zero_mul]

end Ring

/-!
## Page 193, an illustration in rank `n` (rank `2` for the examples)

The edition's illustration, not a statement of the page. On `Aⁿ` (`A` commutative of
characteristic `p`, `D` a derivation), the connection `∇ = D + Γ` acts by
`v ↦ D v + Γ v`, `D` applied to each coordinate (`nabla`, `nabla 0` is `D` itself):

* `nabla_comm`: `[∇, c] = D c`, the rule that made `Dᵖ` a derivation in rank one;
* `pCurvature`, `pCurvature_smul`: `ψ = ∇ᵖ - Dᵖ` is `A`-linear (it is `∇ᵖ - ∇_{Dᵖ}` when
  `Dᵖ = 0`, as for `d/dx` on `𝔽_p[x]`);
* `curvMat`, `pCurvature_apply`: `ψ v = Γ_p v` with `Γ₀ = 1`, `Γ_{k+1} = D Γ_k + Γ Γ_k`;
* `curvMat_mul_horizontal`, `curvMat_eq_zero_of_horizontal`: an invertible matrix `Y` of
  horizontal columns gives `Γ_p Y = -Dᵖ Y`, hence `ψ = 0` when `Dᵖ = 0` (the easy direction);
* `curvMat_diagonal_char`: for `Γ` diagonal, `ψ` is diagonal with the rank-one `p`-curvatures
  `aᵖ + D^{p-1} a`;
* `curvMat_unipotent_char`: for `Γ = [[0, f], [0, 0]]`, `ψ = [[0, D^{p-1} f], [0, 0]]`; on
  `𝔽_p[x]` with `f = x^{p-1}`, `ψ = [[0, -1], [0, 0]] ≠ 0` (`curvMat_unipotent_X_pow`), so
  there is no basis of horizontal sections (`not_horizontal_unipotent_X_pow`), although the
  sub-bundle and the quotient are trivial;
* `curvMat_airy_three`, `curvMat_airy_five`: for the Airy connection `Γ = [[0, 1], [x, 0]]`
  (`Dx = 1`), `ψ = [[-1, x], [x², 1]]` in characteristic `3` and
  `ψ = [[x, x²], [x³ - 1, -x]]` in characteristic `5`.
-/

section Rank

variable {A : Type*} [CommRing A] (D : Derivation ℤ A A) {n : ℕ}

/-- The connection `∇ = D + Γ` on `Aⁿ`. -/
def nabla (Γ : Matrix (Fin n) (Fin n) A) : Module.End ℤ (Fin n → A) where
  toFun v i := D (v i) + Γ.mulVec v i
  map_add' v w := by ext i; simp [Matrix.mulVec_add]; ring
  map_smul' m v := by
    ext i; simp only [Pi.smul_apply, map_zsmul, Matrix.mulVec_smul, smul_add, RingHom.id_apply]

/-- Multiplication by `c ∈ A` on `Aⁿ`. -/
def smulEnd (c : A) : Module.End ℤ (Fin n → A) where
  toFun v := c • v
  map_add' := smul_add c
  map_smul' m v := smul_comm c m v

/-- Leibniz's rule `∇ ∘ c = c ∘ ∇ + D c`. -/
theorem nabla_comm (Γ : Matrix (Fin n) (Fin n) A) (c : A) :
    nabla D Γ * smulEnd c = smulEnd c * nabla D Γ + smulEnd (D c) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [nabla, smulEnd, Matrix.mulVec_smul, smul_eq_mul]; ring

theorem nabla_col (Γ M : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    nabla D Γ (fun i => M i j) = fun i => (M.map D + Γ * M) i j := by
  funext i; simp [nabla, Matrix.mulVec, Matrix.mul_apply, dotProduct]

/-- `Γ₀ = 1`, `Γ_{k+1} = D Γ_k + Γ Γ_k`: the columns of `Γ_k` are `∇ᵏ` of the basis. -/
def curvMat (Γ : Matrix (Fin n) (Fin n) A) : ℕ → Matrix (Fin n) (Fin n) A
  | 0 => 1
  | k + 1 => (curvMat Γ k).map D + Γ * curvMat Γ k

theorem nabla_pow_col (Γ : Matrix (Fin n) (Fin n) A) (k : ℕ) (j : Fin n) :
    (nabla D Γ ^ k) (fun i => (1 : Matrix (Fin n) (Fin n) A) i j) =
      fun i => curvMat D Γ k i j := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, nabla_col]; rfl

theorem nabla_zero_pow (k : ℕ) (v : Fin n → A) :
    (nabla D 0 ^ k) v = fun i => D^[k] (v i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext i; simp [nabla, Function.iterate_succ_apply']

theorem curvMat_diagonal (d : Fin n → A) (k : ℕ) : curvMat D (Matrix.diagonal d) k =
    Matrix.diagonal fun i => (((D : Module.End ℤ A) + LinearMap.mulLeft ℤ (d i)) ^ k) 1 := by
  induction k with
  | zero => simp [curvMat]
  | succ k ih =>
    rw [curvMat, ih, Matrix.diagonal_map (map_zero D), Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add]
    congr 1; funext i; simp [pow_succ']

theorem curvMat_unipotent (f : A) (k : ℕ) :
    curvMat D !![0, f; 0, 0] (k + 1) = !![0, D^[k] f; 0, 0] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [curvMat]
  | succ k ih =>
    rw [curvMat, ih]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Function.iterate_succ_apply']

theorem curvMat_succ_fin_two (Γ : Matrix (Fin 2) (Fin 2) A) (k : ℕ) (a b c d : A)
    (h : curvMat D Γ k = !![a, b; c, d]) : curvMat D Γ (k + 1) =
      !![D a + (Γ 0 0 * a + Γ 0 1 * c), D b + (Γ 0 0 * b + Γ 0 1 * d);
        D c + (Γ 1 0 * a + Γ 1 1 * c), D d + (Γ 1 0 * b + Γ 1 1 * d)] := by
  rw [curvMat, h]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The Airy connection `Γ = [[0, 1], [x, 0]]` with `D x = 1`: `Γ₂, …, Γ₅` over any ring. -/
theorem curvMat_airy (x : A) (hx : D x = 1) :
    curvMat D !![0, 1; x, 0] 3 = !![2, x; x ^ 2, 1] ∧
      curvMat D !![0, 1; x, 0] 5 = !![6 * x, x ^ 2; x ^ 3 + 4, 4 * x] := by
  set Γ : Matrix (Fin 2) (Fin 2) A := !![0, 1; x, 0] with hΓ
  have d2 : D 2 = 0 := by exact_mod_cast D.map_natCast 2
  have d4 : D 4 = 0 := by exact_mod_cast D.map_natCast 4
  have h1 : curvMat D Γ 1 = !![0, 1; x, 0] := by
    rw [curvMat_succ_fin_two D Γ 0 1 0 0 1 (Matrix.one_fin_two)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ]
  have h2 : curvMat D Γ 2 = !![x, 0; 1, x] := by
    rw [curvMat_succ_fin_two D Γ 1 _ _ _ _ h1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx]
  have h3 : curvMat D Γ 3 = !![2, x; x ^ 2, 1] := by
    rw [curvMat_succ_fin_two D Γ 2 _ _ _ _ h2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx] <;> ring
  have h4 : curvMat D Γ 4 = !![x ^ 2, 2; 4 * x, x ^ 2] := by
    rw [curvMat_succ_fin_two D Γ 3 _ _ _ _ h3]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx, d2, Derivation.leibniz_pow] <;> ring
  refine ⟨h3, ?_⟩
  rw [curvMat_succ_fin_two D Γ 4 _ _ _ _ h4]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx, d2, d4, Derivation.leibniz_pow] <;> ring

/-- In characteristic `3`, the Airy connection has `ψ = [[-1, x], [x², 1]]`. -/
theorem curvMat_airy_three [CharP A 3] (x : A) (hx : D x = 1) :
    curvMat D !![0, 1; x, 0] 3 = !![-1, x; x ^ 2, 1] := by
  have h3 : (3 : A) = 0 := by exact_mod_cast CharP.cast_eq_zero A 3
  rw [(curvMat_airy D x hx).1]
  ext i j; fin_cases i <;> fin_cases j <;> simp; linear_combination h3

/-- In characteristic `5`, the Airy connection has `ψ = [[x, x²], [x³ - 1, -x]]`. -/
theorem curvMat_airy_five [CharP A 5] (x : A) (hx : D x = 1) :
    curvMat D !![0, 1; x, 0] 5 = !![x, x ^ 2; x ^ 3 - 1, -x] := by
  have h5 : (5 : A) = 0 := by exact_mod_cast CharP.cast_eq_zero A 5
  rw [(curvMat_airy D x hx).2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    first | linear_combination h5 | linear_combination x * h5

variable (p : ℕ) [hp : Fact p.Prime] [CharP A p]

omit hp in
theorem natCast_endPi : ((p : ℕ) : Module.End ℤ (Fin n → A)) = 0 :=
  LinearMap.ext fun v => funext fun i => by simp [Module.End.natCast_apply, nsmul_eq_mul]

/-- The `p`-curvature `ψ = ∇ᵖ - Dᵖ`. -/
def pCurvature (Γ : Matrix (Fin n) (Fin n) A) : Module.End ℤ (Fin n → A) :=
  nabla D Γ ^ p - nabla D 0 ^ p

/-- **Statement 4.** In characteristic `p`, the `p`-curvature is `A`-linear. -/
theorem pCurvature_smul (Γ : Matrix (Fin n) (Fin n) A) (c : A) (v : Fin n → A) :
    pCurvature D p Γ (c • v) = c • pCurvature D p Γ v := by
  have h : pCurvature D p Γ * smulEnd c = smulEnd c * pCurvature D p Γ := by
    rw [pCurvature, sub_mul, mul_sub,
      pow_char_mul smulEnd D (nabla D Γ) (nabla_comm D Γ) p (natCast_endPi p),
      pow_char_mul smulEnd D (nabla D 0) (nabla_comm D 0) p (natCast_endPi p)]
    abel
  simpa [smulEnd] using congrArg (· v) h

/-- **Statement 5.** `ψ` is the matrix `Γ_p`. -/
theorem pCurvature_apply (Γ : Matrix (Fin n) (Fin n) A) (v : Fin n → A) :
    pCurvature D p Γ v = (curvMat D Γ p).mulVec v := by
  have hcol j : pCurvature D p Γ (fun i => (1 : Matrix (Fin n) (Fin n) A) i j) =
      fun i => curvMat D Γ p i j := by
    rw [pCurvature, LinearMap.sub_apply, nabla_zero_pow, nabla_pow_col]
    funext i
    rw [Pi.sub_apply, Matrix.one_apply]
    split_ifs <;> simp [iterate_one D p, Function.iterate_fixed (map_zero D)]
  have hv : v = ∑ j, v j • fun i => (1 : Matrix (Fin n) (Fin n) A) i j := by
    funext i; simp [Matrix.one_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, pCurvature_smul, hcol]
  funext i; simp [Matrix.mulVec, dotProduct, mul_comm]

/-- **Statement 6 (the easy direction).** If the columns of `Y` are horizontal,
`D Y + Γ Y = 0`, then `Γ_p Y = -Dᵖ Y`. -/
theorem curvMat_mul_horizontal (Γ Y : Matrix (Fin n) (Fin n) A) (hY : Y.map D + Γ * Y = 0) :
    curvMat D Γ p * Y = -Y.map D^[p] := by
  ext i j
  have hcol : nabla D Γ (fun i => Y i j) = 0 := by rw [nabla_col, hY]; rfl
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have h := congrFun (pCurvature_apply D p Γ fun i => Y i j) i
  rw [pCurvature, LinearMap.sub_apply, nabla_zero_pow, hm, pow_succ, Module.End.mul_apply,
    hcol, map_zero, ← hm] at h
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, eq_neg_iff_add_eq_zero, add_comm] using
    h.symm

/-- A basis of horizontal sections forces `ψ = 0` when `Dᵖ = 0`. -/
theorem curvMat_eq_zero_of_horizontal (hD : ∀ x, D^[p] x = 0) (Γ Y Z : Matrix (Fin n) (Fin n) A)
    (hYZ : Y * Z = 1) (hY : Y.map D + Γ * Y = 0) : curvMat D Γ p = 0 := by
  have h0 : Y.map D^[p] = 0 := by ext; simp [hD]
  rw [← mul_one (curvMat D Γ p), ← hYZ, ← mul_assoc, curvMat_mul_horizontal D p Γ Y hY, h0]
  simp

/-- For `Γ` diagonal, `ψ` is diagonal with the rank-one `p`-curvatures. -/
theorem curvMat_diagonal_char (d : Fin n → A) :
    curvMat D (Matrix.diagonal d) p = Matrix.diagonal fun i => d i ^ p + D^[p - 1] (d i) := by
  rw [curvMat_diagonal]
  congr 1; funext i
  simp [jacobson, Module.End.pow_apply, iterate_one]

omit [CharP A p] in
theorem curvMat_unipotent_char (f : A) :
    curvMat D !![0, f; 0, 0] p = !![0, D^[p - 1] f; 0, 0] := by
  simpa [Nat.sub_add_cancel hp.out.one_le] using curvMat_unipotent D f (p - 1)

end Rank

section Concrete

variable (p : ℕ) [hp : Fact p.Prime]

/-- `d/dx` on `𝔽_p[x]`, as a `ℤ`-derivation. -/
noncomputable def dX : @Derivation ℤ (ZMod p)[X] (ZMod p)[X] _ _ _ (Ring.toIntAlgebra _) _ _ :=
  Derivation.mk' ((derivative : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X]).restrictScalars ℤ)
    fun f g => by simp [derivative_mul, smul_eq_mul]; ring

theorem dX_apply (f : (ZMod p)[X]) : dX p f = derivative f := rfl

theorem dX_iterate (k : ℕ) (f : (ZMod p)[X]) : (dX p)^[k] f = derivative^[k] f := rfl

/-- `(d/dx)ᵖ = 0` on `𝔽_p[x]`. -/
theorem dX_iterate_char (f : (ZMod p)[X]) : (dX p)^[p] f = 0 := by
  rw [dX_iterate, iterate_derivative_eq_factorial_smul_sum, nsmul_eq_mul,
    (CharP.cast_eq_zero_iff (ZMod p)[X] p _).2 (Nat.dvd_factorial hp.out.pos le_rfl), zero_mul]

/-- On `𝔽_p[x]`, `∇ = d/dx + [[0, x^{p-1}], [0, 0]]` has `ψ = [[0, -1], [0, 0]]`. -/
theorem curvMat_unipotent_X_pow :
    curvMat (dX p) !![0, X ^ (p - 1); 0, 0] p = !![0, -1; 0, 0] := by
  rw [curvMat_unipotent_char, dX_iterate, iterate_derivative_X_pow_eq_smul,
    Nat.descFactorial_self, ZMod.wilsons_lemma]
  simp

/-- Hence no invertible matrix of horizontal sections exists for it. -/
theorem not_horizontal_unipotent_X_pow :
    ¬ ∃ Y Z : Matrix (Fin 2) (Fin 2) (ZMod p)[X],
      Y * Z = 1 ∧ Y.map (dX p) + !![0, X ^ (p - 1); 0, 0] * Y = 0 := by
  rintro ⟨Y, Z, hYZ, hY⟩
  have := curvMat_eq_zero_of_horizontal (dX p) p (dX_iterate_char p) _ Y Z hYZ hY
  simpa [curvMat_unipotent_X_pow] using congrFun (congrFun this 0) 1

end Concrete

/-!
## Cartier's converse in rank one (#83)

The edition's complement to page 193, not a statement of the page: the converse of
`pCurvature_eq_zero`, the easy case of the content of Grothendieck–Katz. Over `A` commutative of
characteristic `p`, with a derivation `D` such that `Dᵖ = 0` and an `x` with `D x = 1` (as `d/dx`
on `𝔽_p[x]`, `𝔽_p(x)`, `𝔽_p[[x]]`), and `u k = 1/k!` for `k < p`:

* `exp_mul_exp`: `(∑ xʲ Tʲ/j!)(∑ (-x)ᵏ Tᵏ/k!) ≡ 1` modulo `Tᵖ`;
* `proj`, `mul_proj`: if `∇ᵖ = 0`, Cartier's projector `P = ∑_{k<p} (-x)ᵏ/k! ∇ᵏ` lands in the
  horizontal sections; `taylor`: `∑_{j<p} xʲ/j! P ∇ʲ = 1` (both in any ring of operators `E`
  with `[∇, c] = D c`);
* `horizontal_generate`, `horizontal_span`: if `ψ = 0`, the horizontal sections generate, in
  rank one and in rank `n`;
* `horizontal_unit_iff`: over a local ring, `D + a` has a horizontal basis iff
  `aᵖ + D^{p-1} a = 0`;
* `horizontal_unit_iff_Fp`: the same over `𝔽_p[x]`, where both sides say `a = 0`.
-/

section Cartier

variable {A : Type*} [CommRing A] (p : ℕ) [hp : Fact p.Prime] [CharP A p]

omit hp in
lemma isUnit_natCast_of_coprime {m : ℕ} (h : m.Coprime p) : IsUnit (m : A) := by
  simpa using (ZMod.unitOfCoprime m h).isUnit.map (ZMod.castHom (dvd_refl p) A)

lemma isUnit_factorial {k : ℕ} (hk : k < p) : IsUnit (k.factorial : A) :=
  isUnit_natCast_of_coprime p <| (Nat.coprime_comm.1 <|
    (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h => by
      have := (Nat.Prime.dvd_factorial hp.out).1 h; omega)

/-- `u k = 1/k!`, defined for `k < p`. -/
noncomputable def u (k : ℕ) : A := Ring.inverse (k.factorial : A)

lemma u_mul {k : ℕ} (hk : k < p) : u k * (k.factorial : A) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_factorial p hk)

lemma u_zero : u 0 = (1 : A) := by simp [u]

lemma succ_mul_u {k : ℕ} (hk : k + 1 < p) : ((k + 1 : ℕ) : A) * u (k + 1) = u k := by
  have h1 := u_mul (A := A) p hk
  have h0 := u_mul (A := A) p (k := k) (by omega)
  rw [Nat.factorial_succ, Nat.cast_mul] at h1
  linear_combination (u k) * h1 - (((k + 1 : ℕ) : A) * u (k + 1)) * h0

lemma u_mul_u {i j : ℕ} (hij : i + j < p) :
    u i * u j = ((i + j).choose j : A) * u (i + j) := by
  have hi := u_mul (A := A) p (k := i) (by omega)
  have hj := u_mul (A := A) p (k := j) (by omega)
  have hm := u_mul (A := A) p hij
  have hf : (((i + j).choose j : ℕ) : A) * i.factorial * j.factorial = (i + j).factorial := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.add_choose_mul_factorial_mul_factorial]
  linear_combination (-(u i * u j)) * hm + (-(u i * u j * u (i + j))) * hf
    + (((i + j).choose j : A) * u (i + j) * u j * j.factorial) * hi
    + (((i + j).choose j : A) * u (i + j)) * hj

/-- The truncated exponentials `exp(xT)` and `exp(-xT)` modulo `T^p` are inverse. -/
theorem exp_mul_exp (x : A) :
    ∃ r : A[X], (∑ j ∈ range p, monomial j (x ^ j * u j)) *
      (∑ k ∈ range p, monomial k ((-x) ^ k * u k)) = 1 + r * X ^ p := by
  obtain ⟨r, hr⟩ : X ^ p ∣ (∑ j ∈ range p, monomial j (x ^ j * u j)) *
      (∑ k ∈ range p, monomial k ((-x) ^ k * u k)) - 1 := by
    refine X_pow_dvd_iff.2 fun m hm => ?_
    simp only [coeff_sub, coeff_mul, finsetSum_coeff, coeff_monomial, sum_ite_eq',
      mem_range, coeff_one]
    have hs : ∑ ij ∈ antidiagonal m, (if ij.1 < p then x ^ ij.1 * u ij.1 else 0) *
        (if ij.2 < p then (-x) ^ ij.2 * u ij.2 else 0) =
        (∑ ij ∈ antidiagonal m, m.choose ij.1 • (x ^ ij.1 * (-x) ^ ij.2)) * u m := by
      rw [sum_mul]
      refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
      obtain rfl : i + j = m := mem_antidiagonal.1 hij
      simp only [show i < p by omega, show j < p by omega, ↓reduceIte, nsmul_eq_mul]
      rw [mul_mul_mul_comm, u_mul_u p hm, Nat.choose_symm_add]; ring
    rw [hs, ← (Commute.all x (-x)).add_pow', add_neg_cancel]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [u_zero]
    · simp [hm0.ne', zero_pow hm0.ne']
  exact ⟨r, by rw [mul_comm r]; linear_combination hr⟩


lemma D_u (D : Derivation ℤ A A) {k : ℕ} (hk : k < p) : D (u k) = 0 := by
  have h := congrArg D (u_mul (A := A) p hk)
  rw [Derivation.leibniz, Derivation.map_natCast, Derivation.map_one_eq_zero, smul_zero,
    zero_add, smul_eq_mul] at h
  linear_combination (u k) * h - D (u k) * u_mul (A := A) p hk

lemma D_g (D : Derivation ℤ A A) (x : A) (hx : D x = 1) {k : ℕ} (hk : k + 1 < p) :
    D ((-x) ^ (k + 1) * u (k + 1)) = -((-x) ^ k * u k) := by
  rw [Derivation.leibniz, D_u p D hk, Derivation.leibniz_pow, map_neg, hx]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  rw [← succ_mul_u p hk]; push_cast; ring

variable {E : Type*} [Ring E] (S : A →+* E) (D : Derivation ℤ A A) (N : E) (x : A)

/-- Cartier's projector `P = ∑_{k<p} (-x)ᵏ/k! ∇ᵏ` onto the horizontal sections. -/
noncomputable def proj : E := ∑ k ∈ range p, S ((-x) ^ k * u k) * N ^ k

variable {S D N x}

/-- If `∇ᵖ = 0` (`ψ = 0` and `Dᵖ = 0`), `∇ ∘ P = 0`: `P` takes values in horizontal sections. -/
theorem mul_proj (hN : ∀ c, N * S c = S c * N + S (D c)) (hx : D x = 1) (hNp : N ^ p = 0) :
    N * proj p S N x = 0 := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have hD : ∀ k ∈ range q, S (D ((-x) ^ (k + 1) * u (k + 1))) * N ^ (k + 1) =
      -(S ((-x) ^ k * u k) * N ^ (k + 1)) := fun k hk => by
    rw [D_g p D x hx (by simp at hk; omega), map_neg, neg_mul]
  simp only [proj, mul_sum, ← mul_assoc, hN, add_mul, sum_add_distrib]
  rw [hq, sum_range_succ (fun k => S ((-x) ^ k * u k) * N * N ^ k),
    sum_range_succ' (fun k => S (D ((-x) ^ k * u k)) * N ^ k), sum_congr rfl hD, sum_neg_distrib]
  simp only [mul_assoc, ← pow_succ', ← hq, hNp, mul_zero, pow_zero, mul_one, u_zero, mul_one,
    Derivation.map_one_eq_zero, map_zero, add_zero]
  abel

/-- Taylor's formula: `∑_{j<p} xʲ/j! P ∇ʲ = 1` when `∇ᵖ = 0`. -/
theorem taylor (hNp : N ^ p = 0) :
    ∑ j ∈ range p, S (x ^ j * u j) * proj p S N x * N ^ j = 1 := by
  obtain ⟨r, hr⟩ := exp_mul_exp (A := A) p x
  have h : ∑ j ∈ range p, S (x ^ j * u j) * proj p S N x * N ^ j =
      ((∑ j ∈ range p, monomial j (x ^ j * u j)) *
        (∑ k ∈ range p, monomial k ((-x) ^ k * u k))).eval₂ S N := by
    rw [sum_mul_sum]
    simp only [monomial_mul_monomial, eval₂_finsetSum, eval₂_monomial, proj,
      mul_sum, sum_mul, map_mul, pow_add, mul_assoc]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    rw [← pow_add, ← pow_add, add_comm]
  rw [h, hr, eval₂_add, eval₂_one, eval₂_mul_noncomm, eval₂_X_pow, hNp, mul_zero, add_zero]
  intro k; rw [coeff_X_pow]; split_ifs <;> simp

end Cartier

section CartierApply

variable {A : Type*} [CommRing A] (D : Derivation ℤ A A) (p : ℕ) [hp : Fact p.Prime] [CharP A p]

/-- Multiplication `A → End_ℤ(A)` as a ring morphism. -/
def mulLeftHom : A →+* Module.End ℤ A where
  toFun := LinearMap.mulLeft ℤ
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [add_mul]

/-- Scalar multiplication `A → End_ℤ(Aⁿ)` as a ring morphism. -/
def smulHom (n : ℕ) : A →+* Module.End ℤ (Fin n → A) where
  toFun := smulEnd
  map_one' := by ext; simp [smulEnd]
  map_mul' a b := by ext; simp [smulEnd, mul_assoc]
  map_zero' := by ext; simp [smulEnd]
  map_add' a b := by ext; simp [smulEnd, add_mul]

/-- **Cartier in rank one.** If `Dᵖ = 0`, `D x = 1` and the `p`-curvature `aᵖ + D^{p-1} a` of
`∇ = D + a` vanishes, the horizontal sections generate `A`: `∑_{j<p} xʲ/j! yⱼ = 1` with
`D yⱼ + a yⱼ = 0`. -/
theorem horizontal_generate (hD : ∀ y, D^[p] y = 0) (x : A) (hx : D x = 1) (a : A)
    (hψ : a ^ p + D^[p - 1] a = 0) :
    ∃ y : ℕ → A, ∑ j ∈ range p, x ^ j * u j * y j = 1 ∧ ∀ j, D (y j) + a * y j = 0 := by
  set N := (D : Module.End ℤ A) + LinearMap.mulLeft ℤ a
  have hN : ∀ c, N * mulLeftHom c = mulLeftHom c * N + mulLeftHom (D c) := fun c => by
    have hc : LinearMap.mulLeft ℤ a * LinearMap.mulLeft ℤ c =
        LinearMap.mulLeft ℤ c * LinearMap.mulLeft ℤ a := by ext; simp; ring
    simp only [N, mulLeftHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, add_mul, mul_add,
      comm_mulLeft, hc]
    abel
  have hNp : N ^ p = 0 := by
    rw [jacobson, hψ]
    ext y; simp [Module.End.pow_apply, hD]
  refine ⟨fun j => (proj p mulLeftHom N x * N ^ j) 1, ?_, fun j => ?_⟩
  · simpa [Module.End.mul_apply, LinearMap.sum_apply, mulLeftHom, mul_assoc] using
      congrArg (· 1) (taylor p (S := mulLeftHom) (x := x) hNp)
  · have := congrArg (· ((N ^ j) 1)) (mul_proj p hN hx hNp)
    simpa [N, Module.End.mul_apply] using this

/-- **Cartier in rank one, over a local ring** (a field such as `𝔽_p(x)`, or `𝔽_p[[x]]`): if
`Dᵖ = 0` and `D x = 1`, the connection `D + a` has a horizontal basis iff its `p`-curvature
vanishes. The converse of `jacobson_logDeriv_of_pow_eq_zero`. -/
theorem horizontal_unit_iff [IsLocalRing A] (hD : ∀ y, D^[p] y = 0) (x : A) (hx : D x = 1)
    (a : A) : (∃ y z, y * z = 1 ∧ D y + a * y = 0) ↔ a ^ p + D^[p - 1] a = 0 := by
  refine ⟨fun ⟨y, z, hu, hy⟩ => jacobson_logDeriv_of_pow_eq_zero D p hD y z a hu hy,
    fun hψ => ?_⟩
  obtain ⟨y, hsum, hy⟩ := horizontal_generate D p hD x hx a hψ
  by_contra hne
  have hmem : ∀ j, y j ∈ IsLocalRing.maximalIdeal A := fun j =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hj => hne <| by
      obtain ⟨z, hz⟩ := hj.exists_right_inv
      exact ⟨y j, z, hz, hy j⟩
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top <| (Ideal.eq_top_iff_one _).2 <|
    hsum ▸ Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j)

/-- **Cartier in rank `n`.** If `Dᵖ = 0`, `D x = 1` and `ψ = 0` for `∇ = D + Γ` on `Aⁿ`, every
`v` is `∑_{j<p} xʲ/j! wⱼ` with `wⱼ = P ∇ʲ v` horizontal. -/
theorem horizontal_span {n : ℕ} (hD : ∀ y, D^[p] y = 0) (x : A) (hx : D x = 1)
    (Γ : Matrix (Fin n) (Fin n) A) (hψ : curvMat D Γ p = 0) (v : Fin n → A) :
    ∃ w : ℕ → Fin n → A, ∑ j ∈ range p, (x ^ j * u j) • w j = v ∧
      ∀ j, nabla D Γ (w j) = 0 := by
  have hNp : nabla D Γ ^ p = 0 := by
    have h := fun v => pCurvature_apply D p Γ v
    simp only [hψ, Matrix.zero_mulVec, pCurvature, LinearMap.sub_apply, nabla_zero_pow, hD] at h
    refine LinearMap.ext fun v => funext fun i => ?_
    simpa using congrFun (sub_eq_zero.1 (h v)) i
  refine ⟨fun j => (proj p (smulHom n) (nabla D Γ) x * nabla D Γ ^ j) v, ?_, fun j => ?_⟩
  · simpa [Module.End.mul_apply, LinearMap.sum_apply, smulHom, smulEnd, mul_assoc] using
      congrArg (· v) (taylor p (S := smulHom n) (x := x) hNp)
  · simpa [Module.End.mul_apply] using
      congrArg (· ((nabla D Γ ^ j) v)) (mul_proj p (nabla_comm D Γ) hx hNp)

end CartierApply

section CartierFp

variable (p : ℕ) [hp : Fact p.Prime]

/-- On `𝔽_p[x]`, a nonzero `y` with `y' + a y = 0` forces `a = 0`. -/
lemma eq_zero_of_horizontal {a y : (ZMod p)[X]} (hy0 : y ≠ 0) (hy : derivative y + a * y = 0) :
    a = 0 := by
  by_contra ha
  have e : derivative y = -(a * y) := eq_neg_of_add_eq_zero_left hy
  by_cases hd : y.natDegree = 0
  · rw [derivative_of_natDegree_zero hd, zero_eq_neg] at e
    exact mul_ne_zero ha hy0 e
  · have h1 := natDegree_derivative_lt hd
    rw [e, natDegree_neg, natDegree_mul ha hy0] at h1
    omega

/-- **Cartier in rank one over `𝔽_p[x]`.** `∇ = d/dx + a` has a horizontal basis iff
`ψ = aᵖ + a^{(p-1)} = 0`; both say `a = 0`, the units of `𝔽_p[x]` being constants. -/
theorem horizontal_unit_iff_Fp (a : (ZMod p)[X]) :
    (∃ y z, y * z = 1 ∧ dX p y + a * y = 0) ↔ a ^ p + (dX p)^[p - 1] a = 0 := by
  refine ⟨fun ⟨y, z, hu, hy⟩ =>
    jacobson_logDeriv_of_pow_eq_zero (dX p) p (dX_iterate_char p) y z a hu hy, fun hψ => ?_⟩
  obtain ⟨y, hsum, hy⟩ := horizontal_generate (dX p) p (dX_iterate_char p) X
    (by simp [dX_apply]) a hψ
  obtain ⟨j, -, hj⟩ : ∃ j ∈ range p, y j ≠ 0 := by
    by_contra! h
    rw [sum_eq_zero fun j hj => by rw [h j hj, mul_zero]] at hsum
    exact zero_ne_one hsum
  obtain rfl := eq_zero_of_horizontal p hj (hy j)
  exact ⟨1, 1, one_mul 1, by simp⟩

end CartierFp

/-!
## Pages 193–194: the converse asked by the page (statement only)

Page 194 asks of the remark of page 193, « La réciproque est-elle vraie ? »: if the
`p`-curvature of a connection vanishes for almost all `p`, is the monodromy finite? This is the
Grothendieck–Katz `p`-curvature conjecture (Katz 1972, *Algebraic solutions of differential
equations*). It is open. `PCurvatureConjecture` **states it, without proof,** for a vector
bundle with connection on an open subset of the affine line over a base of finite type: the
ring `A = R[x][1/g]`, `R` a domain of finite type over `ℤ` of characteristic `0`, with `D = d/dx`
(a derivation with `D x = 1` that kills `R`), and `∇ = D + Γ` on `Aⁿ`.

* The `p`-curvature at `p` is the reduction modulo `p` of `Γ_p = curvMat D Γ p`
  (`pCurvature_apply`): on `A/pA` the operator `Dᵖ` vanishes, so `∇ᵖ - ∇_{Dᵖ}` is `Γ_p`
  reduced. The hypothesis says that for all but finitely many primes `p` every entry of `Γ_p`
  lies in `pA`.
* Finite monodromy at the generic point is written, as Katz writes it, as a full set of
  algebraic solutions: a field `L ⊇ A` with a derivation extending `D`, and an invertible
  matrix `Y` with entries algebraic over `A` and `D Y + Γ Y = 0`.

Over a single curve with a chosen coordinate this is a special case of the conjecture, still
open in rank `≥ 2` and outside the solvable case (Chudnovsky, André, Bost). A `Prop`, not an
axiom; nothing depends on it. The easy direction in characteristic `p` is
`curvMat_eq_zero_of_horizontal`, and Cartier's converse, at one prime, is
`horizontal_unit_iff` and `horizontal_span`.
-/

open Polynomial in
/-- **The Grothendieck–Katz `p`-curvature conjecture** on an open subset of the affine line
(statement, open; page 194, « La réciproque est-elle vraie ? »). -/
def PCurvatureConjecture : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R]
    (g : R[X]), g ≠ 0 →
    ∀ (A : Type) [CommRing A] [Algebra R[X] A] [IsLocalization.Away g A]
      (D : Derivation ℤ A A),
    D (algebraMap R[X] A X) = 1 → (∀ r : R, D (algebraMap R[X] A (C r)) = 0) →
    ∀ (n : ℕ) (Γ : Matrix (Fin n) (Fin n) A),
    {p : ℕ | p.Prime ∧ ¬ ∀ i j, curvMat D Γ p i j ∈ Ideal.span {(p : A)}}.Finite →
    ∃ (L : Type) (_ : Field L) (_ : Algebra A L),
      Function.Injective (algebraMap A L) ∧
      ∃ D' : Derivation ℤ L L, (∀ a, D' (algebraMap A L a) = algebraMap A L (D a)) ∧
        ∃ Y : Matrix (Fin n) (Fin n) L, IsUnit Y.det ∧ (∀ i j, IsAlgebraic A (Y i j)) ∧
          Y.map D' + Γ.map (algebraMap A L) * Y = 0

end Grothendieck.Folder93.PCurvature

/-!
# Folder 93, pages 121–123: the reduction from `T^(p^N) − α` to `T^(p^N)`

The Proposition of pages 121–123 is stated in `B = A[T]/(T^(p^N) − α)` and the page reduces
to `α = 0` without argument (« OPS »). The rigidity for `α = 0` is `rigidity` above; this
section proves the reduction, with `B = AdjoinRoot (T^(p^N) − α)`.

* `θ`: the Taylor map `A[X] → B[Y]`, `f ↦ f(β + Y)`, `β` the class of `T`; `θ_coeff`
  (its coefficients are the classes of the divided derivatives), `θ_D` (it commutes with them),
  `θ_P` (`θ(T^(p^N) − α) = Y^(p^N)`, Frobenius), `θ_N`. Over `B`, `θ(s)` satisfies the
  hypotheses of the case `α = 0`: this is the base change `A → B`, where
  `T^(p^N) − α = (T − β)^(p^N)`.
* The osculating homography at `β` is `(a(T − β) + s)/(c(T − β) + 1)`, `c = −D⁽²⁾s/D⁽¹⁾s`,
  `a = D⁽¹⁾s + c s`, with coefficient vector `v = (a, s − aT, c, 1 − cT)` in `B⁴`. `Good`:
  `(cY + 1)^k · θ(x) ≡ x` modulo `Y^(p^N)`; the four coordinates of `v` are good of weight `1`,
  so every product of `p^N` of their `A`-combinations is good of weight `p^N`, where
  `(cY + 1)^(p^N) ≡ 1`; `descent` then puts it in `A` (`Good.top`, `descent`).
* `rigidity_alpha`: over any `A` of characteristic `p` with `C(k,3)` a unit for `3 ≤ k < p^N`,
  for every `ℓ = λc + μ(1 − cT)` (`λ, μ ∈ A`) there are `a, b, c', d ∈ A` with
  `s · (c'T + d) = aT + b` in `B`, `c'T + d = ℓ^(p^N − 1)` and `ℓ^(p^N) ∈ A`.
* `rigidity_alpha_local`, `rigidity_alpha_of_gt`, `rigidity_alpha_four`, `rigidity_alpha_nine`:
  for `A` local (hence `Pic(A) = 0`), `s = (aT + b)/(cT + d)` in `B` with `a, b, c, d ∈ A` and
  `cT + d` a unit of `B`: one of `c^(p^N)`, `(1 − cT)^(p^N) = 1 − c^(p^N) α` is a unit of `A`.

Not proved: the case of a non-local `A` with `Pic(A) = 0` (the vectors `ℓ^(p^N − 1) v` lie in
`A⁴` and span a rank-one module; that it is free is where `Pic(A) = 0` would enter).
-/


namespace Grothendieck.Folder93.Alpha

open Polynomial
open scoped Ring

local notation "D" => Polynomial.hasseDeriv

variable {A : Type*} [CommRing A] (p n : ℕ) (α : A)

/-- `T^(p^n) − α`. -/
noncomputable abbrev P : A[X] := X ^ p ^ n - C α

/-- `B = A[T]/(T^(p^n) − α)`. -/
abbrev B := AdjoinRoot (P p n α)

lemma q_pos [hp : Fact p.Prime] : 0 < p ^ n := pow_pos hp.out.pos n

lemma P_monic [Fact p.Prime] : (P p n α).Monic := monic_X_pow_sub_C α (q_pos p n).ne'

/-- A multiple of `T^(p^n) − α` of degree `< p^n` is `0`. -/
lemma eq_zero_of_P_dvd [Fact p.Prime] {f : A[X]} (h : P p n α ∣ f)
    (hf : ∀ m, p ^ n ≤ m → f.coeff m = 0) : f = 0 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have hd : f.degree < (P p n α).degree := by
    rw [degree_X_pow_sub_C (q_pos p n), degree_lt_iff_coeff_zero]
    exact fun m hm => hf m (by exact_mod_cast hm)
  rw [← (modByMonic_eq_self_iff (P_monic p n α)).2 hd]
  exact (modByMonic_eq_zero_iff_dvd (P_monic p n α)).2 h

variable [Fact p.Prime] in
lemma of_injective : Function.Injective (AdjoinRoot.of (P p n α)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at ha
  exact C_eq_zero.1 <| eq_zero_of_P_dvd p n α ha fun m hm => by
    rw [coeff_C, ite_eq_right_iff.2 fun h => absurd h (by have := q_pos p n; omega)]

instance charP_B [Fact p.Prime] [CharP A p] : CharP (B p n α) p := charP_of_injective_ringHom (of_injective p n α) p

/-- The Taylor map `f ↦ f(β + Y)`, `β` the class of `T` in `B`. -/
noncomputable def θ : A[X] →ₐ[A] (B p n α)[X] := aeval (X + C (AdjoinRoot.root (P p n α)))

theorem θ_coeff (f : A[X]) (k : ℕ) :
    (θ p n α f).coeff k = AdjoinRoot.mk (P p n α) (D k f) := by
  have e : θ p n α f = taylor (AdjoinRoot.root (P p n α)) (f.map (AdjoinRoot.of (P p n α))) := by
    rw [taylor_apply, comp, eval₂_map, θ, aeval_def]
    rfl
  rw [e, taylor_coeff, hasseDeriv_map, eval_map, ← AdjoinRoot.aeval_eq, aeval_def,
    AdjoinRoot.algebraMap_eq]

theorem θ_D (f : A[X]) (k : ℕ) : θ p n α (D k f) = D k (θ p n α f) := by
  ext j
  rw [θ_coeff, hasseDeriv_coeff, θ_coeff]
  have := LinearMap.congr_fun (hasseDeriv_comp (R := A) j k) f
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply] at this
  rw [this, nsmul_eq_mul, map_mul, map_natCast, Nat.choose_symm_add]

theorem θ_X : θ p n α X = X + C (AdjoinRoot.root (P p n α)) := by simp [θ]

theorem θ_C (a : A) : θ p n α (C a) = C (AdjoinRoot.mk (P p n α) (C a)) := by
  simp [θ, AdjoinRoot.mk_C]

theorem root_pow : AdjoinRoot.root (P p n α) ^ p ^ n = AdjoinRoot.mk (P p n α) (C α) := by
  have : AdjoinRoot.mk (P p n α) (X ^ p ^ n - C α) = 0 := AdjoinRoot.mk_self
  rwa [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at this

theorem θ_P [Fact p.Prime] [CharP A p] : θ p n α (P p n α) = X ^ p ^ n := by
  have hr := root_pow p n α
  change θ p n α (X ^ p ^ n - C α) = _
  rw [map_sub, map_pow, θ_X, θ_C, add_pow_char_pow, ← C_pow, hr]
  ring

theorem θ_N (f : A[X]) : θ p n α (N f) = N (θ p n α f) := by
  simp only [N, map_sub, map_pow, map_mul, θ_D]


theorem θ_of_mk_eq_zero [Fact p.Prime] [CharP A p] {f : A[X]} (h : AdjoinRoot.mk (P p n α) f = 0) :
    X ^ p ^ n ∣ θ p n α f := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_eq_zero.1 h
  rw [map_mul, θ_P]
  exact dvd_mul_right _ _

/-- Descent: if the Taylor expansion `f(β + Y)` of `f` is constant modulo `Y^(p^n)`, then `f` is
congruent to a constant of `A` modulo `T^(p^n) − α`. -/
theorem descent [Fact p.Prime] [CharP A p] (x : A[X])
    (h : X ^ p ^ n ∣ θ p n α x - C (AdjoinRoot.mk (P p n α) x)) :
    ∃ x₀ : A, P p n α ∣ x - C x₀ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, dvd_of_eq (Subsingleton.elim _ _)⟩
  set r := x %ₘ P p n α
  have hx : x = r + P p n α * (x /ₘ P p n α) := (modByMonic_add_div x (P p n α)).symm
  have hr : ∀ m, p ^ n ≤ m → r.coeff m = 0 := fun m hm =>
    coeff_eq_zero_of_degree_lt ((degree_modByMonic_lt x (P_monic p n α)).trans_le
      (by rw [degree_X_pow_sub_C (q_pos p n)]; exact_mod_cast hm))
  have hmk : AdjoinRoot.mk (P p n α) x = AdjoinRoot.mk (P p n α) r := by
    rw [hx, map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  have h' : X ^ p ^ n ∣ θ p n α r - C (AdjoinRoot.mk (P p n α) r) := by
    have hθx : θ p n α x = θ p n α r + X ^ p ^ n * θ p n α (x /ₘ P p n α) := by
      conv_lhs => rw [hx]
      rw [map_add, map_mul, θ_P]
    have e : θ p n α r - C (AdjoinRoot.mk (P p n α) r) =
        (θ p n α x - C (AdjoinRoot.mk (P p n α) x)) - X ^ p ^ n * θ p n α (x /ₘ P p n α) := by
      rw [hθx, hmk]; ring
    rw [e]
    exact dvd_sub h (dvd_mul_right _ _)
  have hk : ∀ k, 0 < k → k < p ^ n → r.coeff k = 0 := by
    intro k hk0 hkq
    have h1 := X_pow_dvd_iff.1 h' k hkq
    rw [coeff_sub, coeff_C, ite_eq_right_iff.2 fun h => absurd h (by omega), sub_zero, θ_coeff, AdjoinRoot.mk_eq_zero] at h1
    have h2 := eq_zero_of_P_dvd p n α h1 fun m hm => by
      rw [hasseDeriv_coeff, hr _ (by omega), mul_zero]
    simpa [hasseDeriv_coeff] using congrArg (coeff · 0) h2
  refine ⟨r.coeff 0, ⟨x /ₘ P p n α, ?_⟩⟩
  have hrC : r = C (r.coeff 0) := by
    ext m
    rcases m with _ | m
    · simp
    · rw [coeff_C, ite_eq_right_iff.2 fun h => absurd h (by omega)]
      rcases lt_or_ge (m + 1) (p ^ n) with hm | hm
      · exact hk _ (by omega) hm
      · exact hr _ hm
  rw [sub_eq_iff_eq_add', ← hrC]
  exact hx

/-- `x` is good of weight `k` for the denominator `L = c̄Y + 1` when
`L^k · x(β + Y) ≡ x(β)` modulo `Y^(p^n)`. -/
def Good (cb : B p n α) (k : ℕ) (x : A[X]) : Prop :=
  X ^ p ^ n ∣ (C cb * X + 1) ^ k * θ p n α x - C (AdjoinRoot.mk (P p n α) x)

variable {p n α}

lemma Good.C_mul_left {cb : B p n α} {k : ℕ} {x : A[X]} (h : Good p n α cb k x) (l : A) :
    Good p n α cb k (C l * x) := by
  unfold Good at *
  have e : (C cb * X + 1) ^ k * θ p n α (C l * x) - C (AdjoinRoot.mk (P p n α) (C l * x)) =
      C (AdjoinRoot.mk (P p n α) (C l)) *
        ((C cb * X + 1) ^ k * θ p n α x - C (AdjoinRoot.mk (P p n α) x)) := by
    rw [map_mul, θ_C, map_mul, Polynomial.C_mul]; ring
  rw [e]; exact h.mul_left _

lemma Good.add {cb : B p n α} {k : ℕ} {x y : A[X]} (hx : Good p n α cb k x)
    (hy : Good p n α cb k y) : Good p n α cb k (x + y) := by
  unfold Good at *
  have e : (C cb * X + 1) ^ k * θ p n α (x + y) - C (AdjoinRoot.mk (P p n α) (x + y)) =
      ((C cb * X + 1) ^ k * θ p n α x - C (AdjoinRoot.mk (P p n α) x)) +
        ((C cb * X + 1) ^ k * θ p n α y - C (AdjoinRoot.mk (P p n α) y)) := by
    rw [map_add, map_add, C_add]; ring
  rw [e]; exact dvd_add hx hy

lemma Good.mul {cb : B p n α} {k m : ℕ} {x y : A[X]} (hx : Good p n α cb k x)
    (hy : Good p n α cb m y) : Good p n α cb (k + m) (x * y) := by
  unfold Good at *
  have e : (C cb * X + 1) ^ (k + m) * θ p n α (x * y) - C (AdjoinRoot.mk (P p n α) (x * y)) =
      ((C cb * X + 1) ^ k * θ p n α x - C (AdjoinRoot.mk (P p n α) x)) *
          ((C cb * X + 1) ^ m * θ p n α y) +
        C (AdjoinRoot.mk (P p n α) x) *
          ((C cb * X + 1) ^ m * θ p n α y - C (AdjoinRoot.mk (P p n α) y)) := by
    rw [map_mul, map_mul, Polynomial.C_mul]; ring
  rw [e]; exact dvd_add (hx.mul_right _) (hy.mul_left _)

lemma Good.pow {cb : B p n α} {x : A[X]} (hx : Good p n α cb 1 x) (m : ℕ) :
    Good p n α cb m (x ^ m) := by
  induction m with
  | zero => simp [Good, θ]
  | succ m ih => rw [pow_succ]; exact ih.mul hx

/-- Weight `p^n`: `L^(p^n) = 1 + c̄^(p^n) Y^(p^n)`, so `x(β + Y) ≡ x(β)` modulo `Y^(p^n)`. -/
lemma Good.top [Fact p.Prime] [CharP A p] {cb : B p n α} {x : A[X]}
    (hx : Good p n α cb (p ^ n) x) :
    X ^ p ^ n ∣ θ p n α x - C (AdjoinRoot.mk (P p n α) x) := by
  unfold Good at hx
  rw [add_pow_char_pow, one_pow, mul_pow, ← C_pow] at hx
  convert dvd_sub hx (dvd_mul_right (X ^ p ^ n) (C (cb ^ p ^ n) * θ p n α x)) using 1
  ring


variable (p n α)

/-- The combination `λ · c + μ · (1 − c T)` of the two denominator coefficients of the
osculating homography, `c = −D⁽²⁾s · g`, `g` an inverse of `D⁽¹⁾s` modulo `T^(p^n) − α`. -/
noncomputable def denom (s g : A[X]) (l m : A) : A[X] :=
  C l * -(D 2 s * g) + C m * (1 + D 2 s * g * X)

/-- The reduction to `α = 0` (pages 121–123), over any commutative ring `A` of characteristic `p`
in which `C(k,3)` is a unit for `3 ≤ k < p^n`. -/
theorem rigidity_alpha [Fact p.Prime] [CharP A p] (hq : 3 < p ^ n)
    (hC : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : A))
    (s g : A[X]) (hg : AdjoinRoot.mk (P p n α) (D 1 s * g) = 1)
    (hN : AdjoinRoot.mk (P p n α) (N s) = 0) (l m : A) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p n α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p n α) (C a * X + C b) ∧
      AdjoinRoot.mk (P p n α) (C c * X + C d) =
        AdjoinRoot.mk (P p n α) (denom s g l m) ^ (p ^ n - 1) ∧
      ∃ γ : A, AdjoinRoot.mk (P p n α) (denom s g l m) ^ p ^ n = AdjoinRoot.mk (P p n α) (C γ) := by
  set π := AdjoinRoot.mk (P p n α)
  set c : A[X] := -(D 2 s * g) with hc
  set a : A[X] := D 1 s + c * s with ha
  set S := θ p n α s
  set β := AdjoinRoot.root (P p n α)
  have hS : ∀ k, S.coeff k = π (D k s) := fun k => θ_coeff p n α s k
  have hπg : π (D 1 s) * π g = 1 := by rw [← map_mul, hg]
  have hunit : IsUnit (S.coeff 1) := by rw [hS]; exact IsUnit.of_mul_eq_one _ hπg
  have hinv : (S.coeff 1)⁻¹ʳ = π g := by
    rw [hS]
    calc (π (D 1 s))⁻¹ʳ = (π (D 1 s))⁻¹ʳ * (π (D 1 s) * π g) := by rw [hπg, mul_one]
      _ = π g := by rw [← mul_assoc, Ring.inverse_mul_cancel _ (hS 1 ▸ hunit), one_mul]
  have hC' : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : B p n α) := fun k h1 h2 => by
    simpa using (hC k h1 h2).map (AdjoinRoot.of (P p n α))
  have hNS : X ^ p ^ n ∣ N S := by rw [← θ_N]; exact θ_of_mk_eq_zero p n α hN
  have hrig := Grothendieck.Folder93.rigidity_explicit (p ^ n) hC' S hunit
    (fun m hm => X_pow_dvd_iff.1 hNS m (by omega))
  have e2 : -(S.coeff 2 * (S.coeff 1)⁻¹ʳ) = π c := by rw [hinv, hS, hc, map_neg, map_mul]
  have e1 : S.coeff 1 + π c * S.coeff 0 = π a := by rw [hS, hS, ha]; simp
  rw [e2, e1, hS 0, hasseDeriv_zero, LinearMap.id_apply] at hrig
  set cb := π c with hcb
  obtain ⟨r, hr⟩ := hrig
  have hL := D_lin cb 1
  rw [map_one] at hL
  have hl := D_lin (π a) (π s)
  have hq1 : 1 < p ^ n := by omega
  have hq2 : 2 < p ^ n := by omega
  have E1 : D 1 S * (C cb * X + 1) + S * C cb - C (π a) = X ^ p ^ n * D 1 r := by
    have := congrArg (D 1) hr
    rwa [map_sub, D_mul_one, hL.1, hl.1, hasseDeriv_X_pow_mul p n hq1] at this
  have E2 : D 2 S * (C cb * X + 1) + D 1 S * C cb = X ^ p ^ n * D 2 r := by
    have := congrArg (D 2) hr
    rwa [map_sub, D_mul_two, hL.1, hL.2.1, hl.2.1, hasseDeriv_X_pow_mul p n hq2, mul_zero,
      add_zero, sub_zero] at this
  obtain ⟨u, hu⟩ : X ^ p ^ n ∣ D 1 S * θ p n α g - 1 := by
    have h0 : π (D 1 s * g - 1) = 0 := by rw [map_sub, hg, map_one, sub_self]
    have := θ_of_mk_eq_zero p n α h0
    rwa [map_sub, map_mul, θ_D, map_one] at this
  have θc : θ p n α c = -(D 2 S * θ p n α g) := by rw [hc, map_neg, map_mul, θ_D]
  have G3 : Good p n α cb 1 c := by
    refine ⟨-θ p n α g * D 2 r + C cb * u, ?_⟩
    rw [pow_one, θc]
    linear_combination (-θ p n α g) * E2 + C cb * hu
  obtain ⟨w3, hw3⟩ := id G3
  have G1 : Good p n α cb 1 a := by
    refine ⟨D 1 r + S * w3, ?_⟩
    rw [pow_one] at hw3 ⊢
    rw [ha, map_add, map_mul, θ_D]
    linear_combination E1 + S * hw3
  obtain ⟨w1, hw1⟩ := id G1
  have G2 : Good p n α cb 1 (s - a * X) := by
    refine ⟨r - (X + C β) * w1, ?_⟩
    rw [pow_one] at hw1 ⊢
    simp only [map_sub, map_mul, θ_X, AdjoinRoot.mk_X]
    linear_combination hr - (X + C β) * hw1
  have G4 : Good p n α cb 1 (1 - c * X) := by
    refine ⟨-(X + C β) * w3, ?_⟩
    rw [pow_one] at hw3 ⊢
    simp only [map_sub, map_mul, map_one, θ_X, AdjoinRoot.mk_X]
    linear_combination (-(X + C β)) * hw3
  have hden : denom s g l m = C l * c + C m * (1 - c * X) := by
    simp only [denom, hc]; ring
  have Gl : Good p n α cb 1 (denom s g l m) := by
    rw [hden]; exact (G3.C_mul_left l).add (G4.C_mul_left m)
  have hq0 : p ^ n - 1 + 1 = p ^ n := Nat.sub_add_cancel (q_pos p n)
  have top : ∀ v, Good p n α cb 1 v → ∃ x₀ : A,
      π (C x₀) = π (denom s g l m ^ (p ^ n - 1) * v) := fun v hv => by
    have := (Gl.pow (p ^ n - 1)).mul hv
    rw [hq0] at this
    obtain ⟨x₀, hx₀⟩ := descent p n α _ this.top
    exact ⟨x₀, (AdjoinRoot.mk_eq_mk.2 hx₀).symm⟩
  obtain ⟨m1, k1⟩ := top a G1
  obtain ⟨m2, k2⟩ := top _ G2
  obtain ⟨m3, k3⟩ := top c G3
  obtain ⟨m4, k4⟩ := top _ G4
  obtain ⟨γ, kγ⟩ := descent p n α _ (Gl.pow (p ^ n)).top
  refine ⟨m1, m2, m3, m4, ?_, ?_, γ, ?_⟩
  · simp only [map_mul, map_add] at k1 k2 k3 k4 ⊢
    rw [k1, k2, k3, k4]
    simp only [map_mul, map_sub, map_one]
    ring
  · simp only [map_mul, map_add] at k3 k4 ⊢
    rw [k3, k4]
    simp only [map_mul, map_sub, map_one, map_pow]
    ring
  · rw [← map_pow]; exact AdjoinRoot.mk_eq_mk.2 kγ


/-- The Proposition of pages 121–123 in `B = A[T]/(T^(p^n) − α)` for a local ring `A`
(so `Pic(A) = 0`), `α` arbitrary: if `C(k,3)` is a unit for `3 ≤ k < p^n`, `D⁽¹⁾s` is a unit
of `B` and `G₀(t, s) = 0` in `B`, then `s = (at + b)/(ct + d)` in `B` with `a, b, c, d ∈ A`
and `ct + d` a unit of `B`. -/
theorem rigidity_alpha_local [IsLocalRing A] [Fact p.Prime] [CharP A p] (hq : 3 < p ^ n)
    (hC : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : A)) (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P p n α) (D 1 s))) (hN : AdjoinRoot.mk (P p n α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p n α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p n α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p n α) (C c * X + C d)) := by
  set π := AdjoinRoot.mk (P p n α)
  obtain ⟨u, hu⟩ := hs
  obtain ⟨g, hg⟩ : ∃ g, π g = ↑u⁻¹ :=
    AdjoinRoot.induction_on (f := P p n α) (↑u⁻¹ : B p n α) fun g => ⟨g, rfl⟩
  have hg1 : π (D 1 s * g) = 1 := by rw [map_mul, ← hu, hg, Units.mul_inv]
  have hq0 : p ^ n ≠ 0 := (q_pos p n).ne'
  obtain ⟨a, b, c, d, h1, h2, γ, h3⟩ := rigidity_alpha p n α hq hC s g hg1 hN 1 0
  by_cases hγ : IsUnit γ
  · refine ⟨a, b, c, d, h1, ?_⟩
    rw [h2]
    have : IsUnit (π (denom s g 1 0) ^ p ^ n) := by
      rw [h3, AdjoinRoot.mk_C]; exact hγ.map _
    exact ((isUnit_pow_iff hq0).1 this).pow _
  · obtain ⟨a, b, c, d, h1, h2, -⟩ := rigidity_alpha p n α hq hC s g hg1 hN 0 1
    refine ⟨a, b, c, d, h1, ?_⟩
    rw [h2]
    have e1 : π (denom s g 1 0) = -(π (D 2 s) * π g) := by simp [π, denom]
    have e2 : π (denom s g 0 1) = 1 - π (denom s g 1 0) * AdjoinRoot.root (P p n α) := by
      rw [e1]; simp [π, denom]
    have e3 : π (denom s g 0 1) ^ p ^ n = π (C (1 - γ * α)) := by
      rw [e2, sub_pow_char_pow, mul_pow, h3, root_pow, one_pow, ← map_mul]
      simp [π]
    have hu1 : IsUnit (1 - γ * α) :=
      (IsLocalRing.isUnit_or_isUnit_one_sub_self (γ * α)).resolve_left
        fun h => hγ (isUnit_of_mul_isUnit_left h)
    have : IsUnit (π (denom s g 0 1) ^ p ^ n) := by
      rw [e3, AdjoinRoot.mk_C]; exact hu1.map _
    exact ((isUnit_pow_iff hq0).1 this).pow _

/-- `p > 3`, `B = A[T]/(T^p − α)` (page 122), `A` local. -/
theorem rigidity_alpha_of_gt [IsLocalRing A] [hp : Fact p.Prime] [CharP A p] (hp3 : 3 < p)
    (s : A[X]) (hs : IsUnit (AdjoinRoot.mk (P p 1 α) (D 1 s)))
    (hN : AdjoinRoot.mk (P p 1 α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p 1 α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p 1 α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p 1 α) (C c * X + C d)) := by
  refine rigidity_alpha_local p 1 α (by simpa using hp3) (fun k hk3 hkp => ?_) s hs hN
  refine natCast_isUnit p fun hdvd => ?_
  have hf : p ∣ k.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial (show 3 ≤ k from hk3), mul_assoc]
    exact hdvd.mul_right _
  exact absurd ((Nat.Prime.dvd_factorial hp.out).1 hf) (by simp at hkp; omega)

/-- `p = 2`, `B = A[T]/(T^4 − α)` (page 123), `A` local. -/
theorem rigidity_alpha_four [IsLocalRing A] [CharP A 2] (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P 2 2 α) (D 1 s))) (hN : AdjoinRoot.mk (P 2 2 α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P 2 2 α) (s * (C c * X + C d)) = AdjoinRoot.mk (P 2 2 α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P 2 2 α) (C c * X + C d)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine rigidity_alpha_local 2 2 α (by norm_num) (fun k hk3 hk4 => ?_) s hs hN
  obtain rfl : k = 3 := by norm_num at hk4; omega
  simp

/-- `p = 3`, `B = A[T]/(T^9 − α)` (page 123, right-hand column), `A` local. -/
theorem rigidity_alpha_nine [IsLocalRing A] [CharP A 3] (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P 3 2 α) (D 1 s))) (hN : AdjoinRoot.mk (P 3 2 α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P 3 2 α) (s * (C c * X + C d)) = AdjoinRoot.mk (P 3 2 α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P 3 2 α) (C c * X + C d)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rigidity_alpha_local 3 2 α (by norm_num) (fun k hk3 hk9 => natCast_isUnit 3 ?_) s hs hN
  norm_num at hk9
  interval_cases k <;> decide

end Grothendieck.Folder93.Alpha

/-!
# Folder 93, pages 121–123: the reduction for `Pic(A) = 0`

`rigidity_alpha_pic`: the Proposition of pages 121–123 in `B = A[T]/(T^(p^N) − α)` for any
`A` with `Pic(A) = 0`. The `A`-submodule `I = {x ∈ A + AT : s x ∈ A + AT}` of `B` (the
denominators of the homographies equal to `s`) satisfies `c I ⊆ A` and `(1 − cT) I ⊆ A`, by the
coefficient of `Y²` in the Taylor expansion of `s x`; it contains `c^(p^N − 1)` and
`(1 − cT)^(p^N − 1)` (`rigidity_alpha`), and `α c^(p^N) + (1 − cT)^(p^N) = 1`. So
`I · (Ac + A(1 − cT)) = A`: `I` is an invertible submodule of `B`, and `Pic(A) = 0` makes it
`A u` with `u` a unit of `B` (`Submodule.ker_unitsToPic`). `rigidity_alpha_pic_of_gt`,
`rigidity_alpha_pic_four`, `rigidity_alpha_pic_nine`: the cases `p > 3`, `p = 2`, `p = 3`.
-/

namespace Grothendieck.Folder93.Alpha

open Polynomial

local notation "D" => Polynomial.hasseDeriv

variable {A : Type*} [CommRing A] (p n : ℕ) (α : A)

/-- The Proposition of pages 121–123 in `B = A[T]/(T^(p^n) − α)` when `Pic(A) = 0`. -/
theorem rigidity_alpha_pic [Subsingleton (CommRing.Pic A)] [Fact p.Prime] [CharP A p]
    (hq : 3 < p ^ n) (hC : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : A)) (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P p n α) (D 1 s))) (hN : AdjoinRoot.mk (P p n α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p n α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p n α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p n α) (C c * X + C d)) := by
  set π := AdjoinRoot.mk (P p n α)
  set β := AdjoinRoot.root (P p n α)
  obtain ⟨u, hu⟩ := hs
  obtain ⟨g, hg⟩ : ∃ g, π g = ↑u⁻¹ :=
    AdjoinRoot.induction_on (f := P p n α) (↑u⁻¹ : B p n α) fun g => ⟨g, rfl⟩
  have hg1 : π (D 1 s * g) = 1 := by rw [map_mul, ← hu, hg, Units.mul_inv]
  have : FaithfulSMul A (B p n α) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (of_injective p n α)
  let I : Submodule A (B p n α) :=
    { carrier := {x | ∃ c d a b : A,
        x = π (C c * X + C d) ∧ π (s * (C c * X + C d)) = π (C a * X + C b)}
      add_mem' := by
        rintro _ _ ⟨c, d, a, b, rfl, h⟩ ⟨c', d', a', b', rfl, h'⟩
        refine ⟨c + c', d + d', a + a', b + b', by simp only [map_add, map_mul]; ring, ?_⟩
        simp only [map_add, map_mul] at h h' ⊢
        linear_combination h + h'
      zero_mem' := ⟨0, 0, 0, 0, by simp⟩
      smul_mem' := by
        rintro l _ ⟨c, d, a, b, rfl, h⟩
        refine ⟨l * c, l * d, l * a, l * b, ?_, ?_⟩ <;>
          simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply,
            map_add, map_mul] at h ⊢ <;> [ring; linear_combination π (C l) * h] }
  set cb := π (denom s g 1 0)
  have hcb : cb = -(π (D 2 s) * π g) := by simp [cb, denom]
  have key : ∀ x ∈ I, (∃ y : A, π (C y) = x * cb) ∧ ∃ y : A, π (C y) = x * (1 - cb * β) := by
    rintro _ ⟨c, d, a, b, rfl, h⟩
    have h2 := X_pow_dvd_iff.1 (θ_of_mk_eq_zero p n α (sub_eq_zero.2 h)) 2 (by omega)
    simp only [map_sub, map_mul, map_add, θ_X, θ_C, coeff_sub, coeff_add, mul_add, coeff_mul_C,
      coeff_C, ← mul_assoc, coeff_mul_X, θ_coeff] at h2
    norm_num [← hasseDeriv_one] at h2
    have e : π (C c * X + C d) * cb = π (C c) := by
      rw [hcb]; simp only [π, map_mul, map_add, AdjoinRoot.mk_C, AdjoinRoot.mk_X] at hg1 h2 ⊢
      linear_combination (-π g) * h2 + AdjoinRoot.of (P p n α) c * hg1
    refine ⟨⟨c, e.symm⟩, d, ?_⟩
    rw [mul_sub, mul_one, ← mul_assoc, e]; simp [π, β]
  obtain ⟨a₁, b₁, c₁, d₁, h1, h1', γ, hγ⟩ := rigidity_alpha p n α hq hC s g hg1 hN 1 0
  obtain ⟨a₂, b₂, c₂, d₂, h2, h2', -⟩ := rigidity_alpha p n α hq hC s g hg1 hN 0 1
  have hm1 : cb ^ (p ^ n - 1) ∈ I := ⟨c₁, d₁, a₁, b₁, h1'.symm, h1⟩
  have e2 : π (denom s g 0 1) = 1 - cb * β := by rw [hcb]; simp [π, β, denom]
  have hm2 : (1 - cb * β) ^ (p ^ n - 1) ∈ I := ⟨c₂, d₂, a₂, b₂, by rw [h2', e2], h2⟩
  let J : Submodule A (B p n α) := Submodule.span A {cb, 1 - cb * β}
  have hIJ : I * J = 1 := by
    apply le_antisymm
    · refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨l, m, rfl⟩ := Submodule.mem_span_pair.1 hy
      obtain ⟨⟨y₁, e₁⟩, y₂, e₂⟩ := key x hx
      refine Submodule.mem_one.2 ⟨l * y₁ + m * y₂, ?_⟩
      rw [mul_add, mul_smul_comm, mul_smul_comm, ← e₁, ← e₂]
      simp [Algebra.smul_def, π]
    · rw [Submodule.one_le]
      have : (1 : B p n α) =
          α • (cb ^ (p ^ n - 1) * cb) + (1 - cb * β) ^ (p ^ n - 1) * (1 - cb * β) := by
        rw [← pow_succ, ← pow_succ, Nat.sub_add_cancel (q_pos p n), sub_pow_char_pow, mul_pow, hγ,
          root_pow, one_pow]
        simp [Algebra.smul_def]; ring
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.mul_mem_mul hm1 (Submodule.subset_span
        (by simp)))) (Submodule.mul_mem_mul hm2 (Submodule.subset_span (by simp)))
  obtain ⟨v, hv⟩ :
      Units.mkOfMulEqOne I J hIJ ∈ (Units.map (Submodule.spanSingleton A).toMonoidHom).range := by
    rw [← Submodule.ker_unitsToPic, MonoidHom.mem_ker]; exact Subsingleton.elim _ _
  obtain ⟨c, d, a, b, e, h⟩ : (v : B p n α) ∈ I := by
    rw [← show _ = I from congrArg Units.val hv]; exact Submodule.mem_span_singleton_self _
  exact ⟨a, b, c, d, h, e ▸ v.isUnit⟩

/-- `p > 3`, `B = A[T]/(T^p − α)` (page 122), `Pic(A) = 0`. -/
theorem rigidity_alpha_pic_of_gt [Subsingleton (CommRing.Pic A)] [hp : Fact p.Prime]
    [CharP A p] (hp3 : 3 < p) (s : A[X]) (hs : IsUnit (AdjoinRoot.mk (P p 1 α) (D 1 s)))
    (hN : AdjoinRoot.mk (P p 1 α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p 1 α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p 1 α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p 1 α) (C c * X + C d)) := by
  refine rigidity_alpha_pic p 1 α (by simpa using hp3) (fun k hk3 hkp => natCast_isUnit p
    fun h => ?_) s hs hN
  have := (Nat.Prime.dvd_factorial hp.out).1 <| by
    rw [← Nat.choose_mul_factorial_mul_factorial hk3, mul_assoc]; exact h.mul_right _
  simp at hkp; omega

/-- `p = 2`, `B = A[T]/(T^4 − α)` (page 123), `Pic(A) = 0`. -/
theorem rigidity_alpha_pic_four [Subsingleton (CommRing.Pic A)] [CharP A 2] (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P 2 2 α) (D 1 s))) (hN : AdjoinRoot.mk (P 2 2 α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P 2 2 α) (s * (C c * X + C d)) = AdjoinRoot.mk (P 2 2 α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P 2 2 α) (C c * X + C d)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rigidity_alpha_pic 2 2 α (by norm_num) (fun k hk3 hk4 => by
    obtain rfl : k = 3 := by norm_num at hk4; omega
    simp) s hs hN

/-- `p = 3`, `B = A[T]/(T^9 − α)` (page 123, right-hand column), `Pic(A) = 0`. -/
theorem rigidity_alpha_pic_nine [Subsingleton (CommRing.Pic A)] [CharP A 3] (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P 3 2 α) (D 1 s))) (hN : AdjoinRoot.mk (P 3 2 α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P 3 2 α) (s * (C c * X + C d)) = AdjoinRoot.mk (P 3 2 α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P 3 2 α) (C c * X + C d)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rigidity_alpha_pic 3 2 α (by norm_num) (fun k hk3 hk9 => natCast_isUnit 3 <| by
    norm_num at hk9; interval_cases k <;> decide) s hs hN


end Grothendieck.Folder93.Alpha
