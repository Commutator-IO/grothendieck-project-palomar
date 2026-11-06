module

public import Mathlib

@[expose] public section


/-!
# Folder 78, pages 109–113: the closure criterion `u_α^n = id ⇔ F_n(α) = 0`

The modernised reading `transcripts/78/78.modern.tex` (§ V, « Les polynômes `F_n` et le
critère `u_α^n = 1` ») defines `F_n ∈ ℤ[U]` by `F_n(T + T⁻¹) = (T^n − 1)/(T − 1) · T^{−(n−1)/2}`
for `n` odd and `(T^n − 1)/(T² − 1) · T^{−(n−2)/2}` for `n` even, `F_0 = 0`, `F_{−n} = −F_n`,
and states, for the affine map `u_α (x, y) = (1 − y + α x, x)` of `k²` over any commutative
ring `k`:

> **Proposition (p. 109).** `F_n F_{n+1} − U F_{n−1} F_n + F_{n−2} F_{n−1} = 1` for all `n ∈ ℤ`;
> hence `A_n F_{n−1} + B_n F_{n+1} = 1` with `B_n = F_n`, `A_n = F_{n−2} − U F_n`.
>
> **Vertices (p. 111).** `s_n = u_α^n(0, 0) = (F_n F_{n+1}(α), F_{n−1} F_n(α))`, and `u_α^n`
> sends `(s_0, s_1, s_{−1})` to `(s_n, s_{n+1}, s_{n−1})`.
>
> **Théorème (p. 112).** For `n ∈ ℤ` the following are equivalent: a) `u_α^n = id`;
> b) `s_n = s_0`; c) `u_α^n s_i = s_i` for one fixed `i`; d) `F_n(α) = 0`.

This is finding `78-closure-criterion-over-rings` of `src/content/findings.ts`.

What is formalised. `F R n` is defined through mathlib's rescaled Chebyshev polynomials of
the second kind (`Polynomial.Chebyshev.S`): `F_{2m} = S_{m−1}`, `F_{2m+1} = S_m + S_{m−1}`.
That this is the reading's `F_n` is `F_even_closed` and `F_odd_closed` (the defining
formulas, cleared of denominators, for `t` a unit of any commutative ring and `n ≥ 1`),
together with `F_zero` and `F_neg`. Then `F_identity` (p. 109, every `n ∈ ℤ`, the step
being mathlib's Cassini identity `S_sq_add_S_sq`), `F_bezout` and `isCoprime_F` (the reading's
`A_n`), `page_A_four_fails` (the page's `A_n = F_{n−2} − U F_{n−1}` fails at `n = 4`),
`u_zpow_apply` (`u^n (x, y) = (1 − x − y) s_n + x s_{n+1} + y s_{n−1}`, the matrix of p. 111,
first version), `vertex` and the four conditions `zpow_eq_one_iff`, `vertex_eq_iff`,
`zpow_fix_iff`. Also `inv_eq_conj` (`σ₁ u σ₁ = u⁻¹`, `σ₁ (x, y) = (y, x)`), `swap_vertex`
(`σ₁ s_n = s_{−n}`), `conic_invariant` (`f_α = x² − x + y² − y − α x y` is `u_α`-invariant
and vanishes on the vertices), and `affine_eq_of_frame` (an affinity of `k²` is determined
by its values at `s_0, s_1, s_{−1} = (0, 0), (1, 0), (0, 1)`).

# Folder 78, pages 84–85 and 94–99: the strip `2p`-gons (existence)

Finding `78-strip-2p-gon`, existence half only. In characteristic `p` (`CharP k p`, `p`
prime, `k` nontrivial), `α = −2`: `strip_vertex` (`s_{2m} = (−m, m)`, `s_{2m+1} = (1 + m, −m)`,
so the even vertices lie on `x + y = 0`, the odd ones on `x + y = 1`, `strip_lines`),
`strip_zpow_eq_one_iff` (`u^n = id ⇔ 2p ∣ n`), `strip_orderOf` (order `2p`),
`strip_vertex_eq_iff` (`s_n = s_m ⇔ 2p ∣ n − m`, so `2p` distinct vertices), `strip_conic`
(`f_{−2} = (x + y)(x + y − 1)`), `strip_F_eq_zero_iff` (`F_n(−2) = 0 ⇔ 2p ∣ n`),
`strip_noncollinear` (three consecutive vertices span, determinant `1`), `linPart_det`
(unimodular). The improper polygon `u (x, y) = (1 − y, −x)` of p. 85: `imp_zpow_apply`
(`u^{2m}` is the translation by `m (1, −1)`), `imp_zpow_eq_one_iff`, `imp_orderOf`,
`imp_vertex` (`(m, −m)`, `(m + 1, −m)`, the same two lines), `imp_vertex_eq_iff`,
`imp_noncollinear`, `imp_inv_eq_conj`, and `imp_linPart_det` (`−1`, so not unimodular when
`p` is odd). The claim that the improper polygon is the only non-unimodular finite regular
polygon needs the classification and is not proved.
-/

namespace Grothendieck.Folder78

open Polynomial Polynomial.Chebyshev

/-! ## The polynomials `F_n` -/

section Poly

variable (R : Type*) [CommRing R]

/-- The polynomial `F_n` of page 109: `F_{2m} = S_{m−1}`, `F_{2m+1} = S_m + S_{m−1}`, with
`S` the rescaled Chebyshev polynomials of the second kind. -/
noncomputable def F (n : ℤ) : R[X] :=
  if Even n then S R (n / 2 - 1) else S R (n / 2) + S R (n / 2 - 1)

theorem F_even (n m : ℤ) (h : n = 2 * m) : F R n = S R (m - 1) := by
  simp [F, h]

theorem F_odd (n m : ℤ) (h : n = 2 * m + 1) : F R n = S R m + S R (m - 1) := by
  subst h
  have h2 : (2 * m + 1) / 2 = m := by omega
  have hne : ¬ Even (2 * m + 1) := Int.not_even_iff_odd.mpr (odd_two_mul_add_one m)
  simp [F, h2, hne]

theorem F_zero : F R 0 = 0 := by
  rw [F_even R 0 0 (by ring)]; simp

theorem F_one : F R 1 = 1 := by
  rw [F_odd R 1 0 (by ring)]; simp

theorem F_two : F R 2 = 1 := by
  rw [F_even R 2 1 (by ring)]; simp

theorem F_three : F R 3 = X + 1 := by
  rw [F_odd R 3 1 (by ring)]; simp

theorem F_four : F R 4 = X := by
  rw [F_even R 4 2 (by ring)]; simp

theorem F_five : F R 5 = X ^ 2 + X - 1 := by
  rw [F_odd R 5 2 (by ring), show (2 : ℤ) - 1 = 1 by norm_num, S_two, S_one]; ring

theorem F_six : F R 6 = X ^ 2 - 1 := by
  rw [F_even R 6 3 (by ring), show (3 : ℤ) - 1 = 2 by norm_num, S_two]

/-- `F_{−n} = −F_n`. -/
theorem F_neg (n : ℤ) : F R (-n) = -F R n := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [F_even R (-(2 * m)) (-m) (by ring), F_even R (2 * m) m rfl,
      ← show -(m - 1) - 2 = -m - 1 by ring, S_neg_sub_two]
  · rw [F_odd R (-(2 * m + 1)) (-m - 1) (by ring), F_odd R (2 * m + 1) m rfl,
      show -m - 1 - 1 = -m - 2 by ring, ← show -(m - 1) - 2 = -m - 1 by ring, S_neg_sub_two,
      S_neg_sub_two]
    ring

/-- `F_{n+4} = U F_{n+2} − F_n`: the recursion within each parity class. -/
theorem F_add_four (n : ℤ) : F R (n + 4) = X * F R (n + 2) - F R n := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [F_even R (2 * m + 4) (m + 2) (by ring), F_even R (2 * m + 2) (m + 1) (by ring),
      F_even R (2 * m) m rfl, show m + 2 - 1 = m - 1 + 2 by ring,
      show m + 1 - 1 = m - 1 + 1 by ring]
    exact S_add_two R (m - 1)
  · rw [F_odd R (2 * m + 1 + 4) (m + 2) (by ring), F_odd R (2 * m + 1 + 2) (m + 1) (by ring),
      F_odd R (2 * m + 1) m rfl]
    have h1 := S_add_two R m
    have h2 := S_add_two R (m - 1)
    rw [show m - 1 + 2 = m + 1 by ring, show m - 1 + 1 = m by ring] at h2
    rw [show m + 2 - 1 = m + 1 by ring, show m + 1 - 1 = m by ring, h1, h2]
    ring

/-- **Proposition (p. 109).** `F_n F_{n+1} − U F_{n−1} F_n + F_{n−2} F_{n−1} = 1`. -/
theorem F_identity (n : ℤ) :
    F R n * F R (n + 1) - X * F R (n - 1) * F R n + F R (n - 2) * F R (n - 1) = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [F_even R (2 * m) m rfl, F_odd R (2 * m + 1) m rfl,
      F_odd R (2 * m - 1) (m - 1) (by ring), F_even R (2 * m - 2) (m - 1) (by ring)]
    have hS := S_eq R m
    have hC := S_sq_add_S_sq R (m - 2)
    rw [show m - 2 + 1 = m - 1 by ring] at hC
    rw [show m - 1 - 1 = m - 2 by ring]
    linear_combination S R (m - 1) * hS + hC
  · rw [F_odd R (2 * m + 1) m rfl, F_even R (2 * m + 1 + 1) (m + 1) (by ring),
      F_even R (2 * m + 1 - 1) m (by ring), F_odd R (2 * m + 1 - 2) (m - 1) (by ring)]
    have hS := S_eq R m
    have hC := S_sq_add_S_sq R (m - 1)
    rw [show m - 1 + 1 = m by ring] at hC
    rw [show m + 1 - 1 = m by ring, show m - 1 - 1 = m - 2 by ring]
    linear_combination S R (m - 1) * hS + hC

/-- The Bézout relation of page 113, with the reading's coefficient `A_n = F_{n−2} − U F_n`. -/
theorem F_bezout (n : ℤ) :
    (F R (n - 2) - X * F R n) * F R (n - 1) + F R n * F R (n + 1) = 1 := by
  linear_combination F_identity R n

theorem isCoprime_F (n : ℤ) : IsCoprime (F R (n - 1)) (F R (n + 1)) :=
  ⟨_, _, F_bezout R n⟩

end Poly

/-- The page's coefficient `A_n = F_{n−2} − U F_{n−1}` does not give a Bézout relation at
`n = 4`. -/
theorem page_A_four_fails :
    (F ℤ 2 - X * F ℤ 3) * F ℤ 3 + F ℤ 4 * F ℤ 5 ≠ 1 := fun h => by
  have := congrArg (eval 1) h
  norm_num [F_two, F_three, F_four, F_five] at this

/-- The defining formula for `n = 2m + 2` even, cleared of denominators:
`F_n(t + t⁻¹) (t² − 1) t^{m} = t^{2m+2} − 1`, for `t t' = 1` in any commutative ring. -/
theorem F_even_closed {k : Type*} [CommRing k] (t t' : k) (ht : t * t' = 1) (m : ℕ) :
    (F k (2 * m + 2)).eval (t + t') * (t ^ 2 - 1) * t ^ m = t ^ (2 * m + 2) - 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [F_two]
  | one =>
    rw [show 2 * ((1 : ℕ) : ℤ) + 2 = 4 by norm_num, F_four]; simp
    linear_combination (t ^ 2 - 1) * ht
  | more m ih0 ih1 =>
    have hrec := F_add_four k (2 * (m : ℤ) + 2)
    rw [show 2 * (m : ℤ) + 2 + 4 = 2 * ((m + 2 : ℕ) : ℤ) + 2 by push_cast; ring,
      show 2 * (m : ℤ) + 2 + 2 = 2 * ((m + 1 : ℕ) : ℤ) + 2 by push_cast; ring] at hrec
    rw [hrec, eval_sub, eval_mul, eval_X]
    linear_combination (t + t') * t * ih1 - t ^ 2 * ih0 + (t ^ (2 * (m + 1) + 2) - 1) * ht

/-- The defining formula for `n = 2m + 1` odd, cleared of denominators:
`F_n(t + t⁻¹) (t − 1) t^m = t^{2m+1} − 1`. -/
theorem F_odd_closed {k : Type*} [CommRing k] (t t' : k) (ht : t * t' = 1) (m : ℕ) :
    (F k (2 * m + 1)).eval (t + t') * (t - 1) * t ^ m = t ^ (2 * m + 1) - 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [F_one]
  | one =>
    rw [show 2 * ((1 : ℕ) : ℤ) + 1 = 3 by norm_num, F_three]; simp
    linear_combination (t - 1) * ht
  | more m ih0 ih1 =>
    have hrec := F_add_four k (2 * (m : ℤ) + 1)
    rw [show 2 * (m : ℤ) + 1 + 4 = 2 * ((m + 2 : ℕ) : ℤ) + 1 by push_cast; ring,
      show 2 * (m : ℤ) + 1 + 2 = 2 * ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at hrec
    rw [hrec, eval_sub, eval_mul, eval_X]
    linear_combination (t + t') * t * ih1 - t ^ 2 * ih0 + (t ^ (2 * (m + 1) + 1) - 1) * ht

/-! ## The map `u_α` and its vertices -/

section Map

variable {k : Type*} [CommRing k]

/-- `u_α (x, y) = (1 − y + α x, x)`, as a permutation of `k²`. -/
def u (α : k) : Equiv.Perm (k × k) where
  toFun p := (1 - p.2 + α * p.1, p.1)
  invFun p := (p.2, 1 - p.1 + α * p.2)
  left_inv p := Prod.ext rfl (show 1 - (1 - p.2 + α * p.1) + α * p.1 = p.2 by ring)
  right_inv p := Prod.ext (show 1 - (1 - p.1 + α * p.2) + α * p.2 = p.1 by ring) rfl

theorem u_apply (α : k) (p : k × k) : u α p = (1 - p.2 + α * p.1, p.1) := rfl

theorem u_inv_apply (α : k) (p : k × k) : (u α)⁻¹ p = (p.2, 1 - p.1 + α * p.2) := rfl

theorem zpow_succ_apply {X : Type*} (g : Equiv.Perm X) (n : ℤ) (p : X) :
    (g ^ (n + 1)) p = g ((g ^ n) p) := by
  rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]

theorem zpow_pred_apply {X : Type*} (g : Equiv.Perm X) (n : ℤ) (p : X) :
    (g ^ (n - 1)) p = g⁻¹ ((g ^ n) p) := by
  rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]

theorem orbit_eq_iff {X : Type*} (g : Equiv.Perm X) (n m : ℤ) (q : X) :
    (g ^ n) q = (g ^ m) q ↔ (g ^ (n - m)) q = q := by
  conv_lhs => rw [show n = m + (n - m) by ring, zpow_add, Equiv.Perm.mul_apply]
  exact (g ^ m).injective.eq_iff

/-- `X_n(α) = F_n F_{n+1}(α)`. -/
noncomputable def xs (α : k) (n : ℤ) : k := (F k n).eval α * (F k (n + 1)).eval α

theorem F_identity_eval (α : k) (n : ℤ) :
    (F k n).eval α * (F k (n + 1)).eval α - α * (F k (n - 1)).eval α * (F k n).eval α
      + (F k (n - 2)).eval α * (F k (n - 1)).eval α = 1 := by
  simpa using congrArg (eval α) (F_identity k n)

/-- `X_{n+1} = α X_n − X_{n−1} + 1`. -/
theorem xs_rec (α : k) (n : ℤ) : xs α (n + 1) = α * xs α n - xs α (n - 1) + 1 := by
  have h := F_identity_eval α (n + 1)
  rw [show n + 1 - 1 = n by ring, show n + 1 - 2 = n - 1 by ring] at h
  unfold xs
  rw [show n - 1 + 1 = n by ring]
  linear_combination h

/-- The affine map sending `(0,0), (1,0), (0,1)` to `s_n, s_{n+1}, s_{n−1}`. -/
noncomputable def V (α : k) (n : ℤ) (p : k × k) : k × k :=
  ((1 - p.1 - p.2) * xs α n + p.1 * xs α (n + 1) + p.2 * xs α (n - 1),
    (1 - p.1 - p.2) * xs α (n - 1) + p.1 * xs α n + p.2 * xs α (n - 2))

theorem u_V (α : k) (n : ℤ) (p : k × k) : u α (V α n p) = V α (n + 1) p := by
  have r0 := xs_rec α (n - 1)
  have r1 := xs_rec α n
  have r2 := xs_rec α (n + 1)
  rw [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] at r0
  rw [show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring] at r2
  rw [u_apply]
  refine Prod.ext ?_ ?_
  · simp only [V, show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring]
    linear_combination -(1 - p.1 - p.2) * r1 - p.1 * r2 - p.2 * r0
  · simp only [V, show n + 1 - 1 = n by ring, show n + 1 - 2 = n - 1 by ring]

/-- **Page 111.** `u_α^n (x, y) = (1 − x − y) s_n + x s_{n+1} + y s_{n−1}`, with
`s_n = (X_n, X_{n−1})`: the matrix of `u^n` (its first version). -/
theorem u_zpow_apply (α : k) (n : ℤ) (p : k × k) : (u α ^ n) p = V α n p := by
  induction n using Int.induction_on with
  | zero =>
    have h0 : xs α 0 = 0 := by simp [xs, F_zero]
    have h1 : xs α 1 = 1 := by
      simp [xs, F_one, show (1 : ℤ) + 1 = 2 by norm_num, F_two]
    have hm1 : xs α (-1) = 0 := by simp [xs, F_zero]
    have hm2 : xs α (-2) = 1 := by
      simp [xs, F_neg, show (-2 : ℤ) + 1 = -1 by norm_num, F_one, F_two]
    simp only [zpow_zero, Equiv.Perm.coe_one, id, V, zero_add, zero_sub, h0, h1, hm1, hm2]
    ext <;> simp
  | succ n ih => rw [zpow_succ_apply, ih, u_V]
  | pred n ih =>
    have h := u_V α (-(n : ℤ) - 1) p
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at h
    rw [zpow_pred_apply, ih, ← h]
    exact (u α).symm_apply_apply _

/-- `s_n = u_α^n (0, 0)`. -/
noncomputable def s (α : k) (n : ℤ) : k × k := (u α ^ n) (0, 0)

/-- **Page 111.** `s_n = (F_n F_{n+1}(α), F_{n−1} F_n(α))`. -/
theorem vertex (α : k) (n : ℤ) :
    s α n = ((F k n).eval α * (F k (n + 1)).eval α,
      (F k (n - 1)).eval α * (F k n).eval α) := by
  rw [s, u_zpow_apply]
  simp [V, xs]

theorem s_zero (α : k) : s α 0 = (0, 0) := by simp [s]

theorem s_one (α : k) : s α 1 = (1, 0) := by simp [s, u_apply]

theorem s_neg_one (α : k) : s α (-1) = (0, 1) := by simp [s, u_inv_apply]

/-- d) ⇒ a) and b) ⇒ d): **Théorème (p. 112)**, `s_n = s_0 ⇔ F_n(α) = 0`. -/
theorem vertex_eq_iff (α : k) (n : ℤ) : s α n = (0, 0) ↔ (F k n).eval α = 0 := by
  rw [vertex, Prod.mk.injEq]
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => by simp [h]⟩
  linear_combination -((F k n).eval α) * F_identity_eval α n + (F k n).eval α * h1
    + ((F k (n - 2)).eval α - α * (F k n).eval α) * h2

/-- a) ⇔ d): **Théorème (p. 112)**, `u_α^n = id ⇔ F_n(α) = 0`, over any commutative ring. -/
theorem zpow_eq_one_iff (α : k) (n : ℤ) : u α ^ n = 1 ↔ (F k n).eval α = 0 := by
  refine ⟨fun h => by rw [← vertex_eq_iff, s, h]; rfl, fun h => ?_⟩
  have hx0 : xs α n = 0 := by simp [xs, h]
  have hxm : xs α (n - 1) = 0 := by simp [xs, h, show n - 1 + 1 = n by ring]
  have hx1 : xs α (n + 1) = 1 := by rw [xs_rec, hx0, hxm]; ring
  have hxm2 : xs α (n - 2) = 1 := by
    have := xs_rec α (n - 1)
    rw [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring, hx0, hxm] at this
    linear_combination this
  ext p
  · rw [u_zpow_apply]; simp [V, hx0, hx1, hxm]
  · rw [u_zpow_apply]; simp [V, hx0, hxm, hxm2]

/-- c) ⇔ d): `u_α^n s_i = s_i` for one `i` iff `F_n(α) = 0`. -/
theorem zpow_fix_iff (α : k) (n i : ℤ) :
    (u α ^ n) (s α i) = s α i ↔ (F k n).eval α = 0 := by
  rw [← vertex_eq_iff, s, s, ← Equiv.Perm.mul_apply, ← zpow_add, add_comm, zpow_add,
    Equiv.Perm.mul_apply, (u α ^ i).injective.eq_iff]

/-- `σ₁ (x, y) = (y, x)`. -/
def σ₁ : Equiv.Perm (k × k) := Equiv.prodComm k k

/-- `σ₁ u_α σ₁ = u_α⁻¹`: `u_α` and `σ₁` generate a dihedral action. -/
theorem inv_eq_conj (α : k) : σ₁ * u α * σ₁ = (u α)⁻¹ := by
  ext p <;> simp [σ₁, u_apply, u_inv_apply]

/-- `σ₁ s_n = s_{−n}`. -/
theorem swap_vertex (α : k) (n : ℤ) : σ₁ (s α n) = s α (-n) := by
  have h : σ₁ * u α ^ n * σ₁ = (u α)⁻¹ ^ n := by
    rw [← inv_eq_conj]
    have hσ : (σ₁ : Equiv.Perm (k × k)) * σ₁ = 1 := by ext p <;> simp [σ₁]
    have : ∀ g : Equiv.Perm (k × k), σ₁ * g * σ₁ = MulAut.conj σ₁ g := fun g => by
      simp [MulAut.conj_apply, show (σ₁ : Equiv.Perm (k × k))⁻¹ = σ₁ from
        inv_eq_of_mul_eq_one_right hσ]
    rw [this, this, map_zpow]
  have := congrArg (fun g => g (0, 0)) h
  simp only [Equiv.Perm.mul_apply, inv_zpow', s] at this ⊢
  rw [show σ₁ ((0 : k), (0 : k)) = (0, 0) from rfl] at this
  exact this

/-- The invariant conic of page 96: `f_α (x, y) = x² − x + y² − y − α x y`. -/
def fα (α : k) (p : k × k) : k := p.1 ^ 2 - p.1 + p.2 ^ 2 - p.2 - α * p.1 * p.2

/-- `f_α ∘ u_α = f_α`, and `f_α` vanishes on every vertex. -/
theorem conic_invariant (α : k) :
    (∀ p, fα α (u α p) = fα α p) ∧ ∀ n, fα α (s α n) = 0 := by
  have hinv : ∀ p, fα α (u α p) = fα α p := fun p => by simp only [fα, u_apply]; ring
  refine ⟨hinv, fun n => ?_⟩
  induction n using Int.induction_on with
  | zero => simp [s, fα]
  | succ n ih => rw [s, zpow_succ_apply, hinv]; exact ih
  | pred n ih =>
    rw [← hinv, s, ← zpow_succ_apply, show -(n : ℤ) - 1 + 1 = -n by ring]; exact ih

/-- The linear part of `u_α`, `(x, y) ↦ (α x − y, x)`, has determinant `1`. -/
theorem linPart_det (α : k) : !![α, -1; 1, 0].det = 1 := by
  simp [Matrix.det_fin_two]

/-- An affinity of `k²` is determined by its values at `(0, 0), (1, 0), (0, 1)`, i.e. at
`s_0, s_1, s_{−1}`. -/
theorem affine_eq_of_frame (f g : (k × k) →ᵃ[k] (k × k)) (h0 : f (0, 0) = g (0, 0))
    (h1 : f (1, 0) = g (1, 0)) (h2 : f (0, 1) = g (0, 1)) : f = g := by
  have hl : f.linear = g.linear := by
    have e1 : f.linear (1, 0) = g.linear (1, 0) := by
      have a := f.linear_apply_vsub (1, 0) (0, 0)
      have b := g.linear_apply_vsub (1, 0) (0, 0)
      simp only [vsub_eq_sub, Prod.mk_sub_mk, sub_self, sub_zero] at a b
      rw [a, b, h0, h1]
    have e2 : f.linear (0, 1) = g.linear (0, 1) := by
      have a := f.linear_apply_vsub (0, 1) (0, 0)
      have b := g.linear_apply_vsub (0, 1) (0, 0)
      simp only [vsub_eq_sub, Prod.mk_sub_mk, sub_self, sub_zero] at a b
      rw [a, b, h0, h2]
    apply LinearMap.prod_ext
    · apply LinearMap.ext_ring; simpa using e1
    · apply LinearMap.ext_ring; simpa using e2
  exact AffineMap.ext_linear hl h0

end Map

/-! ## The strip `2p`-gon: `α = −2` in characteristic `p` -/

section Strip

variable {k : Type*} [CommRing k]

/-- **Page 95.** For `α = −2`: `s_{2m} = (−m, m)` and `s_{2m+1} = (1 + m, −m)`. -/
theorem strip_vertex (m : ℤ) :
    s (-2 : k) (2 * m) = (-(m : k), (m : k)) ∧ s (-2 : k) (2 * m + 1) = (1 + (m : k), -(m : k)) := by
  have step : ∀ n, s (-2 : k) (n + 1) = u (-2) (s (-2) n) := fun n => zpow_succ_apply _ _ _
  induction m using Int.induction_on with
  | zero => simp [s, u_apply]
  | succ m ih =>
    have e1 : s (-2 : k) (2 * (m + 1)) = (-((m + 1 : ℤ) : k), ((m + 1 : ℤ) : k)) := by
      rw [show 2 * ((m : ℤ) + 1) = 2 * m + 1 + 1 by ring, step, ih.2, u_apply]
      ext <;> push_cast <;> ring
    refine ⟨e1, ?_⟩
    rw [step, e1, u_apply]; ext <;> push_cast <;> ring
  | pred m ih =>
    have e2 : s (-2 : k) (2 * (-(m : ℤ) - 1) + 1) = (1 + ((-(m : ℤ) - 1 : ℤ) : k),
        -((-(m : ℤ) - 1 : ℤ) : k)) := by
      apply (u (-2 : k)).injective
      rw [← step, show 2 * (-(m : ℤ) - 1) + 1 + 1 = 2 * -(m : ℤ) by ring, ih.1, u_apply]
      ext <;> push_cast <;> ring
    refine ⟨?_, e2⟩
    apply (u (-2 : k)).injective
    rw [← step, e2, u_apply]
    ext <;> push_cast <;> ring

/-- The even vertices lie on `x + y = 0`, the odd ones on the parallel line `x + y = 1`. -/
theorem strip_lines (m : ℤ) :
    (s (-2 : k) (2 * m)).1 + (s (-2 : k) (2 * m)).2 = 0 ∧
      (s (-2 : k) (2 * m + 1)).1 + (s (-2 : k) (2 * m + 1)).2 = 1 := by
  rw [(strip_vertex m).1, (strip_vertex m).2]; constructor <;> simp

/-- **Page 99.** `f_{−2} = (x + y)(x + y − 1)`: the invariant conic is the pair of lines. -/
theorem strip_conic (q : k × k) : fα (-2) q = (q.1 + q.2) * (q.1 + q.2 - 1) := by
  simp only [fα]; ring

variable [Nontrivial k] (p : ℕ) [CharP k p]

include p in
theorem strip_vertex_eq_zero_iff (n : ℤ) : s (-2 : k) n = (0, 0) ↔ (2 * p : ℤ) ∣ n := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [(strip_vertex m).1, Prod.mk.injEq, neg_eq_zero, and_self,
      CharP.intCast_eq_zero_iff k p]
    exact (mul_dvd_mul_iff_left two_ne_zero).symm
  · rw [(strip_vertex m).2, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [neg_eq_zero.1 h2, add_zero] at h1
      exact absurd h1 one_ne_zero
    · rintro ⟨c, hc⟩
      exact absurd ⟨p * c, by rw [hc]; ring⟩ (Int.not_even_iff_odd.mpr (odd_two_mul_add_one m))

include p in
/-- **Pages 94–95.** In characteristic `p`, `u_{−2}^n = id ⇔ 2p ∣ n`. -/
theorem strip_zpow_eq_one_iff (n : ℤ) : u (-2 : k) ^ n = 1 ↔ (2 * p : ℤ) ∣ n := by
  rw [zpow_eq_one_iff, ← vertex_eq_iff, strip_vertex_eq_zero_iff p]

include p in
/-- `F_n(−2) = 0 ⇔ 2p ∣ n` in characteristic `p`. -/
theorem strip_F_eq_zero_iff (n : ℤ) : (F k n).eval (-2) = 0 ↔ (2 * p : ℤ) ∣ n := by
  rw [← vertex_eq_iff, strip_vertex_eq_zero_iff p]

include p in
/-- `u_{−2}` has order `2p`. -/
theorem strip_orderOf : orderOf (u (-2 : k)) = 2 * p := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, strip_zpow_eq_one_iff p]; push_cast; rfl
  · have h := pow_orderOf_eq_one (u (-2 : k))
    rw [← zpow_natCast, strip_zpow_eq_one_iff p] at h
    exact_mod_cast h

include p in
/-- The vertices: `s_n = s_m ⇔ 2p ∣ n − m`; there are `2p` of them. -/
theorem strip_vertex_eq_iff (n m : ℤ) : s (-2 : k) n = s (-2) m ↔ (2 * p : ℤ) ∣ n - m := by
  rw [s, s, orbit_eq_iff, ← s, strip_vertex_eq_zero_iff p]

omit [Nontrivial k] in
/-- Three consecutive vertices are never collinear: the determinant of
`(s_{n+1} − s_n, s_{n−1} − s_n)` is `1`. -/
theorem strip_noncollinear (n : ℤ) :
    ((s (-2 : k) (n + 1)).1 - (s (-2) n).1) * ((s (-2 : k) (n - 1)).2 - (s (-2) n).2)
      - ((s (-2 : k) (n + 1)).2 - (s (-2) n).2) * ((s (-2 : k) (n - 1)).1 - (s (-2) n).1)
      = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [show 2 * m - 1 = 2 * (m - 1) + 1 by ring, (strip_vertex m).1, (strip_vertex m).2,
      (strip_vertex (m - 1)).2]
    push_cast; ring
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, show 2 * m + 1 - 1 = 2 * m by ring,
      (strip_vertex m).1, (strip_vertex m).2, (strip_vertex (m + 1)).1]
    push_cast; ring

end Strip

/-! ## The improper `2p`-gon of page 85 -/

section Improper

variable {k : Type*} [CommRing k]

/-- **Page 85.** The improper realisation `u (x, y) = (1 − y, −x)`. -/
def ui : Equiv.Perm (k × k) where
  toFun q := (1 - q.2, -q.1)
  invFun q := (-q.2, 1 - q.1)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

theorem ui_apply (q : k × k) : (ui : Equiv.Perm (k × k)) q = (1 - q.2, -q.1) := rfl

/-- `u^{2m}` is the translation by `m (1, −1)`, and `u^{2m+1} (x, y) = (1 − y + m, −x − m)`. -/
theorem imp_zpow_apply (m : ℤ) (q : k × k) :
    ((ui : Equiv.Perm (k × k)) ^ (2 * m)) q = (q.1 + m, q.2 - m) ∧
      ((ui : Equiv.Perm (k × k)) ^ (2 * m + 1)) q = (1 - q.2 + m, -q.1 - m) := by
  induction m using Int.induction_on with
  | zero => simp [ui_apply]
  | succ m ih =>
    have e1 : ((ui : Equiv.Perm (k × k)) ^ (2 * ((m : ℤ) + 1))) q =
        (q.1 + ((m + 1 : ℤ) : k), q.2 - ((m + 1 : ℤ) : k)) := by
      rw [show 2 * ((m : ℤ) + 1) = 2 * m + 1 + 1 by ring, zpow_succ_apply, ih.2, ui_apply]
      ext <;> push_cast <;> ring
    refine ⟨e1, ?_⟩
    rw [zpow_succ_apply, e1, ui_apply]; ext <;> push_cast <;> ring
  | pred m ih =>
    have e2 : ((ui : Equiv.Perm (k × k)) ^ (2 * (-(m : ℤ) - 1) + 1)) q =
        (1 - q.2 + ((-(m : ℤ) - 1 : ℤ) : k), -q.1 - ((-(m : ℤ) - 1 : ℤ) : k)) := by
      apply (ui : Equiv.Perm (k × k)).injective
      rw [← zpow_succ_apply, show 2 * (-(m : ℤ) - 1) + 1 + 1 = 2 * -(m : ℤ) by ring, ih.1,
        ui_apply]
      ext <;> push_cast <;> ring
    refine ⟨?_, e2⟩
    apply (ui : Equiv.Perm (k × k)).injective
    rw [← zpow_succ_apply, e2, ui_apply]; ext <;> push_cast <;> ring

/-- The vertices of the improper polygon: `(m, −m)` and `(m + 1, −m)`. -/
theorem imp_vertex (m : ℤ) :
    ((ui : Equiv.Perm (k × k)) ^ (2 * m)) (0, 0) = ((m : k), -(m : k)) ∧
      ((ui : Equiv.Perm (k × k)) ^ (2 * m + 1)) (0, 0) = ((m : k) + 1, -(m : k)) := by
  rw [(imp_zpow_apply m _).1, (imp_zpow_apply m _).2]
  constructor <;> ext <;> simp; ring

/-- `σ₁ u σ₁ = u⁻¹` for the improper `u` too. -/
theorem imp_inv_eq_conj : σ₁ * ui * σ₁ = (ui : Equiv.Perm (k × k))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  ext q <;> simp [σ₁, ui_apply]

/-- The linear part `(x, y) ↦ (−y, −x)` has determinant `−1`: not unimodular when `2 ≠ 0`. -/
theorem imp_linPart_det : !![(0 : k), -1; -1, 0].det = -1 := by
  simp [Matrix.det_fin_two]

/-- Three consecutive vertices of the improper polygon are not collinear (determinant `±1`). -/
theorem imp_noncollinear (m : ℤ) :
    let w := fun n : ℤ => ((ui : Equiv.Perm (k × k)) ^ n) (0, 0)
    ((w (2 * m + 1)).1 - (w (2 * m)).1) * ((w (2 * m - 1)).2 - (w (2 * m)).2)
        - ((w (2 * m + 1)).2 - (w (2 * m)).2) * ((w (2 * m - 1)).1 - (w (2 * m)).1) = 1 ∧
      ((w (2 * m + 2)).1 - (w (2 * m + 1)).1) * ((w (2 * m)).2 - (w (2 * m + 1)).2)
        - ((w (2 * m + 2)).2 - (w (2 * m + 1)).2) * ((w (2 * m)).1 - (w (2 * m + 1)).1)
        = -1 := by
  intro w
  simp only [w]
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 by ring, show 2 * m + 2 = 2 * (m + 1) by ring,
    (imp_vertex m).1, (imp_vertex m).2, (imp_vertex (m - 1)).2, (imp_vertex (m + 1)).1]
  constructor <;> push_cast <;> ring

variable [Nontrivial k] (p : ℕ) [CharP k p]

include p in
theorem imp_vertex_eq_zero_iff (n : ℤ) :
    ((ui : Equiv.Perm (k × k)) ^ n) (0, 0) = (0, 0) ↔ (2 * p : ℤ) ∣ n := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [(imp_vertex m).1, Prod.mk.injEq, neg_eq_zero, and_self,
      CharP.intCast_eq_zero_iff k p]
    exact (mul_dvd_mul_iff_left two_ne_zero).symm
  · rw [(imp_vertex m).2, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [neg_eq_zero.1 h2, zero_add] at h1
      exact absurd h1 one_ne_zero
    · rintro ⟨c, hc⟩
      exact absurd ⟨p * c, by rw [hc]; ring⟩ (Int.not_even_iff_odd.mpr (odd_two_mul_add_one m))

include p in
/-- **Page 85.** In characteristic `p`, `u^n = id ⇔ 2p ∣ n`. -/
theorem imp_zpow_eq_one_iff (n : ℤ) :
    (ui : Equiv.Perm (k × k)) ^ n = 1 ↔ (2 * p : ℤ) ∣ n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← imp_vertex_eq_zero_iff (k := k) p, h]; rfl
  obtain ⟨c, rfl⟩ := h
  have hc : ((p * c : ℤ) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).2 (dvd_mul_right _ _)
  ext q <;> simp [show (2 * (p : ℤ) * c) = 2 * (p * c) by ring, (imp_zpow_apply _ q).1, hc]

include p in
theorem imp_orderOf : orderOf (ui : Equiv.Perm (k × k)) = 2 * p := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, imp_zpow_eq_one_iff p]; push_cast; rfl
  · have h := pow_orderOf_eq_one (ui : Equiv.Perm (k × k))
    rw [← zpow_natCast, imp_zpow_eq_one_iff p] at h
    exact_mod_cast h

include p in
/-- The `2p` vertices of the improper polygon are distinct: `s_n = s_m ⇔ 2p ∣ n − m`. -/
theorem imp_vertex_eq_iff (n m : ℤ) :
    ((ui : Equiv.Perm (k × k)) ^ n) (0, 0) = (ui ^ m) (0, 0) ↔ (2 * p : ℤ) ∣ n - m := by
  rw [orbit_eq_iff, imp_vertex_eq_zero_iff p]

end Improper

end Grothendieck.Folder78
