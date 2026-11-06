module

public import Mathlib

@[expose] public section


/-!
# Folder 146, page 70: the trivialising exponents of `L_i` and `L` on `M_{0,n}`, `n = 4, 5, 6`

The modernised reading `transcripts/146/146.modern.tex` (« Les fibrés `L_i` et le groupe de
Picard équivariant », pages 70 to 73) describes the table of page 70: for `n = card I`, the
smallest exponent that makes the line bundles `L_i` (attached to the marked points), and
`L = ⊗ L_i`, trivial compatibly with the symmetric group on `M_{0,I}`; for `n = 4` the table
gives `3` for `L` and `6` for `L_i`. The reading does not verify the table. This file settles the
two entries for `n = 4`; it is the reachable part of finding
`146-equivariant-trivialising-exponents` of `src/content/findings.ts`, which drops if the
`n = 4` values do not check.

The model. `M_{0,4} = U = ℙ¹ ∖ {0, 1, ∞}` with coordinate `λ`, the fourth point moving;
`𝔖_{I∖{4}} = 𝔖₃` permutes `0, 1, ∞` and acts on `U` by the six anharmonic substitutions
(`anh`, composition table `mul`, `mul_group`, `anh_mul`), and on the tangent line `L₄` at the
moving point through the derivative `g′(λ)` (`der`). By the chain rule (`der_mul`),
`g ↦ g′(λ)` is a 1-cocycle of `𝔖₃` with values in the units of `O(U)`; as `Pic(U) = 0`, the
equivariant structures on `L₄^{⊗m}` up to isomorphism are classified by the class of its
`m`-th power, and the exponent of the table is the order of that class.

* `der_pow_six`: `g′(λ)⁶ = h(gλ)/h(λ)` with `h = λ⁴(1 − λ)⁴`, so `L₄^{⊗6}` is equivariantly
  trivial.
* `six_dvd`: if `g′(λ)^m = h(gλ)/h(λ)` for all `g` and `λ ∈ U(K)`, for any nowhere-zero function
  `h`, regular or not, then `6 ∣ m` — over a field with `2 ≠ 0`, `3 ≠ 0` and a root `ζ` of
  `ζ² − ζ + 1`. At a fixed point of `g` the right side is `1`: `λ = −1` is fixed by `1/λ`, where
  `g′ = −1`, and `ζ` is fixed by `1/(1 − λ)`, where `g′ = ζ²`, a primitive cube root of unity.

So the class of `L₄` has order exactly `6`, the value of the table.

The entry `3` for `L = L₁ ⊗ L₂ ⊗ L₃ ⊗ L₄` under `𝔖₄`, page 70, also checks, for the cocycle
`derL g = sgn g · g′(λ)` of `L` (the Klein group acting trivially, see the section on `L`):
* `derL_mul`: it is a 1-cocycle; `derL_pow_three`: its cube is the coboundary of
  `λ²(1 − λ)²`;
* `coboundary_derL_iff`: its `m`-th power is the coboundary of a nowhere-zero function on
  `U(K)` iff `3 ∣ m` (`3 ≠ 0`, a root `ζ` of `ζ² − ζ + 1`, where the factor is `ζ²`).
Page 72 only claims `L^{⊗6} ≃ 1`.

Not formalised: the identification of the equivariant Picard group with `H¹(𝔖₃, O(U)^*)`, the
reduction from `𝔖₄` to `𝔖₃` and the formula `sgn g · g′(λ)` for the action on `L`.

The column `n = 5`, queried on the page (« 12 ? » for `L` and for `L_i`), is settled at the
end of the file at the level of cocycles: `L` has order `4` (`coboundary_cL_iff`), `L₅` has
order `12` (`coboundary_c5_iff`). The column `n = 6` (« 20 ? » for `L`, « 60 ? » for `L_i`) is
settled after it: `L` has order `5` (`coboundary_cL6_iff`), `L₆` has order `20`
(`coboundary_c6_iff`).

The last section proves the general formula, for every `n`, in a homogeneous model of
`M_{0,n}` (configurations of vectors of `K²`, functions of weight instead of cocycles): `L`
has order `n − 1` (`trivL_iff`) and `L_i` has order `(n − 1)(n − 2)` (`trivLi_iff`). The
final section shows that, for `n = 4, 5, 6`, the two models agree: a trivialisation in the
homogeneous model restricts to one of the normalised cocycles (`coboundary_cL_of_trivL` and
its companions, `trivL_five_iff` and its companions).
-/

namespace Grothendieck.Folder146

/-! ## The anharmonic group -/

/-- Composition table of the six anharmonic substitutions `λ, 1/λ, 1 − λ, λ/(λ − 1),
1/(1 − λ), (λ − 1)/λ`: `mul a b` is `a ∘ b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 0, 4, 5, 2, 3], ![2, 5, 0, 4, 3, 1], ![3, 4, 5, 0, 1, 2],
    ![4, 3, 1, 2, 5, 0], ![5, 2, 3, 1, 0, 4]] a b

/-- The table is a group with unit `0`, and it is not commutative: it is `𝔖₃`. -/
theorem mul_group : (∀ a b c, mul (mul a b) c = mul a (mul b c)) ∧ (∀ a, mul 0 a = a) ∧
    (∀ a, ∃ b, mul b a = 0) ∧ mul 1 2 ≠ mul 2 1 := by decide

variable {K : Type*} [Field K]

/-- The substitutions. -/
def anh : Fin 6 → K → K
  | 0 => fun x => x
  | 1 => fun x => 1 / x
  | 2 => fun x => 1 - x
  | 3 => fun x => x / (x - 1)
  | 4 => fun x => 1 / (1 - x)
  | 5 => fun x => (x - 1) / x

/-- Their derivatives `g′(λ)`: the action on the tangent line `L₄` at the fourth point. -/
def der : Fin 6 → K → K
  | 0 => fun _ => 1
  | 1 => fun x => -1 / x ^ 2
  | 2 => fun _ => -1
  | 3 => fun x => -1 / (x - 1) ^ 2
  | 4 => fun x => 1 / (1 - x) ^ 2
  | 5 => fun x => 1 / x ^ 2

/-- `U = ℙ¹ ∖ {0, 1, ∞}`. -/
def U (x : K) : Prop := x ≠ 0 ∧ x ≠ 1

/-- The substitutions compose by the table: an action of `𝔖₃` on `U`. -/
theorem anh_mul (a b : Fin 6) {x : K} (hx : U x) : anh (mul a b) x = anh a (anh b x) := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> fin_cases b
  all_goals first
    | (change (1 : K) / x = (1 / (1 - x)) / (1 / (1 - x) - 1)
       rw [div_sub_one h1'', sub_sub_cancel]; field_simp)
    | (change (x - 1) / x = 1 / (1 - 1 / (1 - x))
       rw [one_sub_div h1'', sub_sub_cancel_left]; field_simp; ring)
    | (simp [mul, anh]; field_simp; ring)
    | (simp [mul, anh]; field_simp)
    | simp [mul, anh]

/-- The chain rule `(g ∘ h)′(λ) = g′(h λ) h′(λ)`: `g ↦ g′(λ)` is a 1-cocycle of `𝔖₃` with
values in the units of `O(U)`. -/
theorem der_mul (a b : Fin 6) {x : K} (hx : U x) :
    der (mul a b) x = der a (anh b x) * der b x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> fin_cases b
  all_goals first
    | (change (-1 : K) / x ^ 2 = -1 / (1 / (1 - x) - 1) ^ 2 * (1 / (1 - x) ^ 2)
       rw [div_sub_one h1'', sub_sub_cancel]; field_simp)
    | (change (1 : K) / x ^ 2 = 1 / (1 - 1 / (1 - x)) ^ 2 * (1 / (1 - x) ^ 2)
       rw [one_sub_div h1'', sub_sub_cancel_left]; field_simp)
    | (simp [mul, anh, der]; field_simp; ring)
    | (simp [mul, anh, der]; field_simp)
    | simp [mul, anh, der]

/-- `h = λ⁴(1 − λ)⁴`. -/
def h6 (x : K) : K := x ^ 4 * (1 - x) ^ 4

/-- `L₄^{⊗6}` is equivariantly trivial: `g′(λ)⁶ = h(gλ)/h(λ)` with `h = λ⁴(1 − λ)⁴`. -/
theorem der_pow_six (a : Fin 6) {x : K} (hx : U x) : der a x ^ 6 = h6 (anh a x) / h6 x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> simp [anh, der, h6] <;> field_simp <;> ring

/-- The root `ζ` of `ζ² − ζ + 1` is a point of `U` fixed by `1/(1 − λ)`, where the derivative
is `ζ²`. -/
lemma fix_zeta {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) : U ζ ∧ anh 4 ζ = ζ ∧ der 4 ζ = ζ ^ 2 := by
  have hUζ : U ζ := ⟨fun e => by simp [e] at hζ, fun e => by simp [e] at hζ⟩
  have hfix : 1 / (1 - ζ) = ζ := by
    have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hUζ.2)
    field_simp; linear_combination hζ
  exact ⟨hUζ, hfix, show 1 / (1 - ζ) ^ 2 = ζ ^ 2 by rw [one_div, ← inv_pow, ← one_div, hfix]⟩

/-- `ζ²` is a primitive cube root of unity when `3 ≠ 0`: `(ζ²)^m = 1` forces `3 ∣ m`. -/
lemma three_dvd_of_pow (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ)
    (e : (ζ ^ 2) ^ m = 1) : 3 ∣ m := by
  have w1 : ζ ^ 2 ≠ 1 := fun e => h3 (by linear_combination (-1 - ζ) * e + (ζ + 2) * hζ)
  have w3 : (ζ ^ 2) ^ 3 = 1 := by linear_combination (ζ ^ 4 + ζ ^ 3 - ζ - 1) * hζ
  have hw0 : ζ ^ 2 ≠ 0 := pow_ne_zero _ (fix_zeta hζ).1.1
  generalize ζ ^ 2 = w at e w1 w3 hw0
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2) ∧ m = 3 * q + r :=
    ⟨m / 3, m % 3, by omega, by omega⟩
  rw [zpow_add₀ hw0, zpow_mul, show w ^ (3 : ℤ) = 1 by exact_mod_cast w3, one_zpow,
    one_mul] at e
  rcases hr with rfl | rfl | rfl
  · simp
  · exact absurd (by simpa using e) w1
  · rw [pow_succ, show w ^ 2 = 1 by simpa using e, one_mul] at w3
    exact absurd w3 w1

/-- No smaller power is a coboundary, even among all nowhere-zero functions on `U(K)`: if
`g′(λ)^m = h(gλ)/h(λ)` for all `g` and `λ`, then `6 ∣ m`. At `λ = −1`, fixed by `1/λ` with
derivative `−1`, and at a root `ζ` of `ζ² − ζ + 1`, fixed by `1/(1 − λ)` with derivative `ζ²`,
a primitive cube root of unity. -/
theorem six_dvd (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0)
    (m : ℤ) (h : K → K) (hh : ∀ x, U x → h x ≠ 0)
    (hc : ∀ a x, U x → der a x ^ m = h (anh a x) / h x) : 6 ∣ m := by
  have hU1 : U (-1 : K) := ⟨by simp, fun e => h2 (by linear_combination -e)⟩
  have e1' : (-1 : K) ^ m = 1 := by simpa [der, anh, hh _ hU1] using hc 1 (-1) hU1
  have h2m : 2 ∣ m := by
    rcases Int.even_or_odd m with he | ho
    · exact even_iff_two_dvd.1 he
    · rw [ho.neg_one_zpow] at e1'
      exact absurd (by linear_combination -e1') h2
  obtain ⟨hUζ, hfix, hder⟩ := fix_zeta hζ
  have e := hc 4 ζ hUζ
  rw [hder, hfix, div_self (hh _ hUζ)] at e
  have := three_dvd_of_pow h3 hζ m e
  omega

/-! ## The bundle `L = L₁ ⊗ L₂ ⊗ L₃ ⊗ L₄` under `𝔖₄`

On `M_{0,4}`, `g ∈ 𝔖₄` acts on `L` by the product of the derivatives of the induced
automorphism of the fibre at the four marked points. The Klein subgroup acts trivially on `U`
and on `L` (it pairs the points, and the derivatives at the two points of a pair multiply to
`1`), and `𝔖₄/V₄ ≃ 𝔖₃`, the stabiliser of the fourth point. For `g` in it the derivatives at
`0, 1, ∞` multiply to the constant `sgn g` and the one at `λ` is `g′(λ)`, so the cocycle of
`L` is `sgn g · g′(λ)` (`derL`). These identifications, and the injectivity of inflation
`H¹(𝔖₃, ·) → H¹(𝔖₄, ·)` that makes the order under `𝔖₄` the order under `𝔖₃`, are not
formalised. -/

/-- The sign of the six substitutions. -/
def sgn : Fin 6 → K
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1
  | 4 => 1
  | 5 => 1

lemma sgn_mul (a b : Fin 6) : sgn (K := K) (mul a b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> simp [sgn, mul]

/-- The cocycle of `L = ⊗ L_i`: `sgn g · g′(λ)`. -/
def derL (a : Fin 6) (x : K) : K := sgn a * der a x

/-- `derL` is a 1-cocycle. -/
theorem derL_mul (a b : Fin 6) {x : K} (hx : U x) :
    derL (mul a b) x = derL a (anh b x) * derL b x := by
  simp only [derL, sgn_mul, der_mul a b hx]; ring

/-- `h = λ²(1 − λ)²`. -/
def h3 (x : K) : K := x ^ 2 * (1 - x) ^ 2

/-- `L^{⊗3}` is equivariantly trivial: `(sgn g · g′(λ))³ = h(gλ)/h(λ)` with `h = λ²(1 − λ)²`. -/
theorem derL_pow_three (a : Fin 6) {x : K} (hx : U x) :
    derL a x ^ 3 = h3 (anh a x) / h3 x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> simp [derL, sgn, anh, der, h3] <;> field_simp <;> ring

/-- The entry « 3 » of page 70 for `L`, `n = 4`: a power `m` of the cocycle of `L` is a
coboundary of a nowhere-zero function on `U(K)` iff `3 ∣ m` (`3 ≠ 0`, `ζ² − ζ + 1 = 0`). At `ζ`,
fixed by `1/(1 − λ)`, the factor is `ζ²`. -/
theorem coboundary_derL_iff (h3K : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) :
    (∃ h : K → K, (∀ x, U x → h x ≠ 0) ∧ ∀ a x, U x → derL a x ^ m = h (anh a x) / h x) ↔
      3 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hUζ, hfix, hder⟩ := fix_zeta hζ
    have e := hc 4 ζ hUζ
    rw [derL, hder, hfix, div_self (hh _ hUζ)] at e
    exact three_dvd_of_pow h3K hζ m (by simpa [sgn] using e)
  · rintro ⟨t, rfl⟩
    refine ⟨fun x => h3 x ^ t, fun x ⟨h0, h1⟩ => zpow_ne_zero _ (mul_ne_zero (pow_ne_zero _ h0)
      (pow_ne_zero _ (sub_ne_zero.2 (Ne.symm h1)))), fun a x hx => ?_⟩
    rw [zpow_mul, show derL a x ^ (3 : ℤ) = _ by exact_mod_cast derL_pow_three a hx, div_zpow]

/-! ## The column `n = 5`: `L` has order `4`, `L₅` has order `12`

`M_{0,5}` is the set of `(λ, μ)` with `λ, μ ∉ {0, 1}` and `λ ≠ μ` (`U5`), the five points being
`0, 1, ∞, λ, μ`. The adjacent transpositions `s₁, …, s₄` of the labels act by `act5`, the
substitution obtained by renormalising the permuted points to `0, 1, ∞`, and on the tangent lines
at the marked points by the derivative of that renormalisation: `cL` is the factor on
`L = L₁ ⊗ ⋯ ⊗ L₅` (product of the five derivatives), `c5` the factor on `L₅` under the
stabiliser `𝔖₄` of the fifth point (`s₁, s₂, s₃`). A word in the generators acts by composition
(`wAct`) and carries the factor given by the cocycle rule (`wCoc`). Not formalised: that `act5`,
`cL`, `c5` satisfy the Coxeter relations of `𝔖₅` (checked by computer algebra), so that the
words factor through `𝔖₅`, and the derivation of the factors.

* `cL_pow_four`: `cL⁴` is the coboundary of `(λμ(1 − λ)(1 − μ)(λ − μ))²`;
  `coboundary_cL_iff`: a power `m` of `cL` is a coboundary iff `4 ∣ m` — at `(−1, i)`, fixed by
  the `4`-cycle `s₁s₂s₃`, the factor is `i`.
* `c5_pow_twelve`: `c5¹²` is the coboundary of `μ⁶(1 − μ)⁶(λ − μ)⁶/(λ²(1 − λ)²)`;
  `coboundary_c5_iff`: a power `m` of `c5` is a coboundary iff `12 ∣ m` — the factor is `i` at
  `(−1, i)`, and `ζ²` at `(1 − ζ, ζ)`, fixed by the `3`-cycle `s₁s₂`.
So the entry « 12 ? » for `L_i` checks and the entry « 12 ? » for `L` does not: `L^{⊗12}` is
trivial, but already `L^{⊗4}` is. -/

/-- Composition of a word of substitutions, the last letter acting first. -/
def wAct {ι α : Type*} (act : ι → α → α) : List ι → α → α
  | [] => id
  | i :: w => act i ∘ wAct act w

/-- The factor carried by a word, by the cocycle rule `c(gh)(x) = c(g)(hx) c(h)(x)`. -/
def wCoc {ι α : Type*} (act : ι → α → α) (c : ι → α → K) : List ι → α → K
  | [] => fun _ => 1
  | i :: w => fun x => c i (wAct act w x) * wCoc act c w x

/-- A cocycle whose `m`-th power is a coboundary on the generators is one on all words. -/
lemma wCoc_zpow {ι α : Type*} {act : ι → α → α} {c : ι → α → K} {V : α → Prop} {h : α → K}
    {m : ℤ} (hV : ∀ i x, V x → V (act i x)) (hh : ∀ x, V x → h x ≠ 0)
    (hc : ∀ i x, V x → c i x ^ m = h (act i x) / h x) :
    ∀ w x, V x → wCoc act c w x ^ m = h (wAct act w x) / h x
  | [], x, hx => by simp [wCoc, wAct, hh x hx]
  | i :: w, x, hx => by
    have hw : V (wAct act w x) := by
      induction w with
      | nil => exact hx
      | cons j w ih => exact hV j _ ih
    simp only [wCoc, wAct, Function.comp, mul_zpow, hc i _ hw, wCoc_zpow hV hh hc w x hx]
    field_simp [hh _ hw]

/-- `M_{0,5}`: `λ, μ ∉ {0, 1}`, `λ ≠ μ`. -/
def U5 (p : K × K) : Prop := p.1 ≠ 0 ∧ p.1 ≠ 1 ∧ p.2 ≠ 0 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2

/-- The adjacent transpositions `s₁, s₂, s₃, s₄` of the five labels. -/
def act5 : Fin 4 → K × K → K × K
  | 0 => fun p => (1 - p.1, 1 - p.2)
  | 1 => fun p => (p.1 / (p.1 - 1), p.2 / (p.2 - 1))
  | 2 => fun p => (1 - p.1, p.2 * (p.1 - 1) / (p.1 - p.2))
  | 3 => fun p => (p.2, p.1)

/-- Their factor on `L = L₁ ⊗ ⋯ ⊗ L₅`. -/
def cL : Fin 4 → K × K → K
  | 0 => fun _ => -1
  | 1 => fun p => -1 / ((p.1 - 1) ^ 2 * (p.2 - 1) ^ 2)
  | 2 => fun p => p.1 * (p.1 - 1) / (p.1 - p.2) ^ 2
  | 3 => fun _ => 1

/-- The factor of `s₁, s₂, s₃` on `L₅`. -/
def c5 : Fin 3 → K × K → K
  | 0 => fun _ => -1
  | 1 => fun p => -1 / (p.2 - 1) ^ 2
  | 2 => fun p => p.1 * (p.1 - 1) / (p.1 - p.2) ^ 2

/-- `s₁, s₂, s₃` as substitutions. -/
def act4 (i : Fin 3) : K × K → K × K := act5 i.castSucc

lemma act5_U5 (i : Fin 4) {p : K × K} (hp : U5 p) : U5 (act5 i p) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  simp only at a0 a1 b0 b1 ab
  have a1' : p1 - 1 ≠ 0 := sub_ne_zero.2 a1
  have b1' : p2 - 1 ≠ 0 := sub_ne_zero.2 b1
  have ab' : p1 - p2 ≠ 0 := sub_ne_zero.2 ab
  have a1'' : 1 - p1 ≠ 0 := sub_ne_zero.2 (Ne.symm a1)
  fin_cases i
  · change U5 (1 - p1, 1 - p2)
    exact ⟨a1'', fun e => a0 (by linear_combination -e), sub_ne_zero.2 (Ne.symm b1),
      fun e => b0 (by linear_combination -e), fun e => ab (by linear_combination -e)⟩
  · change U5 (p1 / (p1 - 1), p2 / (p2 - 1))
    refine ⟨div_ne_zero a0 a1', fun e => ?_, div_ne_zero b0 b1', fun e => ?_, fun e => ?_⟩
    · rw [div_eq_one_iff_eq a1'] at e; exact one_ne_zero (α := K) (by linear_combination e)
    · rw [div_eq_one_iff_eq b1'] at e; exact one_ne_zero (α := K) (by linear_combination e)
    · rw [div_eq_div_iff a1' b1'] at e; exact ab (by linear_combination -e)
  · change U5 (1 - p1, p2 * (p1 - 1) / (p1 - p2))
    refine ⟨a1'', fun e => a0 (by linear_combination -e), div_ne_zero (mul_ne_zero b0 a1') ab',
      fun e => ?_, fun e => ?_⟩
    · rw [div_eq_one_iff_eq ab'] at e; exact mul_ne_zero a0 b1' (by linear_combination e)
    · rw [eq_div_iff ab'] at e; exact mul_ne_zero a1'' a0 (by linear_combination e)
  · exact (⟨b0, b1, a0, a1, Ne.symm ab⟩ : U5 (p2, p1))

/-- `h = (λμ(1 − λ)(1 − μ)(λ − μ))²`. -/
def hL (p : K × K) : K := (p.1 * p.2 * (1 - p.1) * (1 - p.2) * (p.1 - p.2)) ^ 2

/-- `h = μ⁶(1 − μ)⁶(λ − μ)⁶/(λ²(1 − λ)²)`. -/
def h5 (p : K × K) : K := p.2 ^ 6 * (1 - p.2) ^ 6 * (p.1 - p.2) ^ 6 / (p.1 ^ 2 * (1 - p.1) ^ 2)

lemma hL_ne {p : K × K} (hp : U5 p) : hL p ≠ 0 := by
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm; have := sub_ne_zero.2 ab
  simp only [hL]; positivity

lemma h5_ne {p : K × K} (hp : U5 p) : h5 p ≠ 0 := by
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm; have := sub_ne_zero.2 ab
  simp only [h5]; positivity

/-- `L^{⊗4}` is equivariantly trivial: `cL(s)⁴ = h(sx)/h(x)` on the generators, with
`h = (λμ(1 − λ)(1 − μ)(λ − μ))²`. -/
theorem cL_pow_four (i : Fin 4) {p : K × K} (hp : U5 p) :
    cL i p ^ 4 = hL (act5 i p) / hL p := by
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  have := sub_ne_zero.2 a1; have := sub_ne_zero.2 b1; have := sub_ne_zero.2 ab
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm
  fin_cases i <;> simp [cL, act5, hL] <;> field_simp <;> ring

/-- `L₅^{⊗12}` is equivariantly trivial under `𝔖₄`: `c5(s)¹² = h(sx)/h(x)` on the generators,
with `h = μ⁶(1 − μ)⁶(λ − μ)⁶/(λ²(1 − λ)²)`. -/
theorem c5_pow_twelve (i : Fin 3) {p : K × K} (hp : U5 p) :
    c5 i p ^ 12 = h5 (act4 i p) / h5 p := by
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  have := sub_ne_zero.2 a1; have := sub_ne_zero.2 b1; have := sub_ne_zero.2 ab
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm
  fin_cases i <;> simp [c5, act4, act5, h5] <;> field_simp <;> ring

/-- `i` is a primitive fourth root of unity when `2 ≠ 0`: `i^m = 1` forces `4 ∣ m`. -/
lemma four_dvd_of_pow (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) (m : ℤ) (e : ι ^ m = 1) :
    4 ∣ m := by
  have hι0 : ι ≠ 0 := fun h => h2 (by rw [h] at hι; linear_combination 2 * hι)
  have w4 : ι ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((2 * 2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_mul, hι]; norm_num
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) ∧ m = 4 * q + r :=
    ⟨m / 4, m % 4, by omega, by omega⟩
  rw [zpow_add₀ hι0, zpow_mul, w4, one_zpow, one_mul] at e
  rcases hr with rfl | rfl | rfl | rfl
  · simp
  · have : ι = 1 := by simpa using e
    exact absurd (by rw [this] at hι; linear_combination hι) h2
  · have : ι ^ 2 = 1 := by simpa using e
    exact absurd (by linear_combination hι - this) h2
  · have : ι ^ 3 = 1 := by simpa using e
    exact absurd (by linear_combination (1 - ι ^ 2 + ι) * hι + (ι - 1) * this) h2

/-- The point `(−1, i)` of `M_{0,5}` is fixed by the `4`-cycle `s₁s₂s₃`, where the factor on
`L`, and on `L₅`, is `i`. -/
lemma fix_four (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) :
    U5 ((-1 : K), ι) ∧ wAct act5 [0, 1, 2] ((-1 : K), ι) = (-1, ι) ∧
      wCoc act5 cL [0, 1, 2] ((-1 : K), ι) = ι ∧
      wAct act4 [0, 1, 2] ((-1 : K), ι) = (-1, ι) ∧
      wCoc act4 c5 [0, 1, 2] ((-1 : K), ι) = ι := by
  have hι0 : ι ≠ 0 := fun h => h2 (by rw [h] at hι; linear_combination 2 * hι)
  have hι1 : ι ≠ 1 := fun h => h2 (by rw [h] at hι; linear_combination hι)
  have hιm : ι ≠ -1 := fun h => h2 (by rw [h] at hι; linear_combination hι)
  have hne : (-1 : K) - ι ≠ 0 := fun h => hιm (by linear_combination -h)
  have s2 : act5 2 ((-1 : K), ι) = (2, ι + 1) := by
    change ((1 - -1 : K), ι * (-1 - 1) / (-1 - ι)) = (2, ι + 1)
    rw [show ι * (-1 - 1) / (-1 - ι) = ι + 1 by rw [div_eq_iff hne]; linear_combination hι]
    norm_num
  have s1 : act5 1 ((2 : K), ι + 1) = (2, 1 - ι) := by
    change ((2 : K) / (2 - 1), (ι + 1) / (ι + 1 - 1)) = (2, 1 - ι)
    rw [show (ι + 1) / (ι + 1 - 1) = 1 - ι by
      rw [add_sub_cancel_right, div_eq_iff hι0]; linear_combination hι]
    norm_num
  have s0 : act5 0 ((2 : K), 1 - ι) = (-1, ι) := by
    change ((1 - 2 : K), 1 - (1 - ι)) = (-1, ι)
    exact Prod.ext (by norm_num) (by ring)
  have hv : (-1 : K) * (-1 / ((2 - 1) ^ 2 * (ι + 1 - 1) ^ 2) * (-1 * (-1 - 1) / (-1 - ι) ^ 2 * 1))
      = ι := by
    rw [show (ι + 1 - 1 : K) ^ 2 = -1 by linear_combination hι,
      show (-1 - ι : K) ^ 2 = 2 * ι by linear_combination hι]
    field_simp
    linear_combination -2 * hι
  have hfix : wAct act5 [0, 1, 2] ((-1 : K), ι) = (-1, ι) := by
    change act5 0 (act5 1 (act5 2 ((-1 : K), ι))) = _
    rw [s2, s1, s0]
  refine ⟨⟨by norm_num, fun h => h2 (by linear_combination -h), hι0, hι1, fun h => hιm h.symm⟩,
    hfix, ?_, hfix, ?_⟩
  · change cL 0 (act5 1 (act5 2 ((-1 : K), ι))) * (cL 1 (act5 2 ((-1 : K), ι)) *
      (cL 2 ((-1 : K), ι) * 1)) = ι
    rw [s2, s1]; exact hv
  · change c5 0 (act5 1 (act5 2 ((-1 : K), ι))) * (c5 1 (act5 2 ((-1 : K), ι)) *
      (c5 2 ((-1 : K), ι) * 1)) = ι
    rw [s2, s1]
    exact (by norm_num : (-1 : K) * (-1 / (ι + 1 - 1) ^ 2 * (-1 * (-1 - 1) / (-1 - ι) ^ 2 * 1))
      = _).trans hv

/-- The point `(1 − ζ, ζ)` of `M_{0,5}` is fixed by the `3`-cycle `s₁s₂`, where the factor on
`L₅` is `ζ²`. -/
lemma fix_three (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) :
    U5 (1 - ζ, ζ) ∧ wAct act4 [0, 1] (1 - ζ, ζ) = (1 - ζ, ζ) ∧
      wCoc act4 c5 [0, 1] (1 - ζ, ζ) = ζ ^ 2 := by
  obtain ⟨⟨hζ0, hζ1⟩, -, -⟩ := fix_zeta hζ
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζ1'' : 1 - ζ - 1 ≠ 0 := by rw [sub_sub_cancel_left]; exact neg_ne_zero.2 hζ0
  have s1 : act5 1 (1 - ζ, ζ) = (ζ, 1 - ζ) := by
    change ((1 - ζ) / (1 - ζ - 1), ζ / (ζ - 1)) = (ζ, 1 - ζ)
    exact Prod.ext (by rw [div_eq_iff hζ1'']; linear_combination hζ)
      (by rw [div_eq_iff hζ1']; linear_combination hζ)
  refine ⟨⟨fun h => hζ1 (by linear_combination -h), fun h => hζ0 (by linear_combination -h),
    hζ0, hζ1, fun h => h3 (by linear_combination 4 * hζ - (1 - 2 * ζ) * h)⟩, ?_, ?_⟩
  · change act5 0 (act5 1 (1 - ζ, ζ)) = _
    rw [s1]; exact Prod.ext rfl (sub_sub_cancel 1 ζ)
  · change c5 0 (act5 1 (1 - ζ, ζ)) * (c5 1 (1 - ζ, ζ) * 1) = ζ ^ 2
    rw [s1]
    change (-1 : K) * (-1 / (ζ - 1) ^ 2 * 1) = ζ ^ 2
    rw [show (-1 : K) * (-1 / (ζ - 1) ^ 2 * 1) = 1 / (ζ - 1) ^ 2 by ring,
      div_eq_iff (pow_ne_zero 2 hζ1')]
    linear_combination (-(ζ ^ 2 - ζ - 1)) * hζ

/-- The entry « 12 ? » of page 70 for `L`, `n = 5`, does not check: a power `m` of the cocycle
of `L` is the coboundary of a nowhere-zero function on `M_{0,5}(K)` iff `4 ∣ m` (`2 ≠ 0`,
`i² = −1`). -/
theorem coboundary_cL_iff (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) (m : ℤ) :
    (∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act5 cL w p ^ m = h (wAct act5 w p) / h p) ↔ 4 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hU, hfix, hcoc, -, -⟩ := fix_four h2 hι
    exact four_dvd_of_pow h2 hι m <| by
      simpa only [hfix, hcoc, div_self (hh _ hU)] using hc [0, 1, 2] _ hU
  · rintro ⟨t, rfl⟩
    have hh p (hp : U5 p) : hL p ^ t ≠ (0 : K) := zpow_ne_zero _ (hL_ne hp)
    refine ⟨_, hh, wCoc_zpow (fun i p hp => act5_U5 i hp) hh fun i p hp => ?_⟩
    rw [zpow_mul, show cL i p ^ (4 : ℤ) = _ by exact_mod_cast cL_pow_four i hp, div_zpow]

/-- The entry « 12 ? » of page 70 for `L_i`, `n = 5`, checks: a power `m` of the cocycle of
`L₅` under `𝔖₄` is the coboundary of a nowhere-zero function on `M_{0,5}(K)` iff `12 ∣ m`
(`2 ≠ 0`, `3 ≠ 0`, `i² = −1`, `ζ² − ζ + 1 = 0`). -/
theorem coboundary_c5_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1)
    {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) :
    (∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act4 c5 w p ^ m = h (wAct act4 w p) / h p) ↔ 12 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hU, -, -, hfix, hcoc⟩ := fix_four h2 hι
    have e := hc [0, 1, 2] _ hU
    rw [hfix, hcoc, div_self (hh _ hU)] at e
    obtain ⟨hU', hfix', hcoc'⟩ := fix_three h3 hζ
    have e' := hc [0, 1] _ hU'
    rw [hfix', hcoc', div_self (hh _ hU')] at e'
    have := four_dvd_of_pow h2 hι m e
    have := three_dvd_of_pow h3 hζ m e'
    omega
  · rintro ⟨t, rfl⟩
    have hh p (hp : U5 p) : h5 p ^ t ≠ (0 : K) := zpow_ne_zero _ (h5_ne hp)
    refine ⟨_, hh, wCoc_zpow (fun i p hp => act5_U5 i.castSucc hp) hh fun i p hp => ?_⟩
    rw [zpow_mul, show c5 i p ^ (12 : ℤ) = _ by exact_mod_cast c5_pow_twelve i hp, div_zpow]

/-! ## The column `n = 6`: `L` has order `5`, `L₆` has order `20`

`M_{0,6}` is the set of `(λ, μ, ν)` with `λ, μ, ν ∉ {0, 1}` pairwise distinct (`U6`), the six
points being `0, 1, ∞, λ, μ, ν`. As for `n = 5`, the adjacent transpositions `s₁, …, s₅` act by
renormalising the permuted points to `0, 1, ∞` (`act6`), with factor `cL6` on `L = L₁ ⊗ ⋯ ⊗ L₆`
and `c6` on `L₆` under the stabiliser `𝔖₅` of the sixth point (`s₁, …, s₄`, `act6s`). The units
of `O(M_{0,6})` are, up to constants, the monomials in the nine functions `λ, μ, ν, 1 − λ, 1 − μ,
1 − ν, λ − μ, λ − ν, μ − ν`; the functions `h` below come from solving the linear system on their
exponents. Not formalised, as for `n = 5`: the Coxeter relations of `𝔖₆` for `act6`, `cL6`, `c6`
(checked by computer algebra) and the derivation of the factors.

* `cL6_pow_five`: `cL6⁵` is the coboundary of the square of the product of the nine units;
  `coboundary_cL6_iff`: a power `m` of `cL6` is a coboundary iff `5 ∣ m` — at the configuration
  `0, ω, …, ω⁴` (`fix_five`), fixed by the `5`-cycle `s₁s₂s₃s₄`, the factor is `ω`.
* `c6_pow_ten`: `c6¹⁰ = −g(sx)/g(x)`, so `c6²⁰` is the coboundary of `g²`;
  `coboundary_c6_iff`: a power `m` of `c6` is a coboundary iff `20 ∣ m` — the factor is `ω` at the
  same point, and `i` at `(−1, −i, i)` (`fix_four6`), fixed by the `4`-cycle `s₁s₂s₃`.
So the entries « 20 ? » for `L` and « 60 ? » for `L_i` of page 70 do not check: the orders are
`5` and `20`. -/

/-- `M_{0,6}`: `λ, μ, ν ∉ {0, 1}`, pairwise distinct; that is, `(λ, μ)` and `(λ, ν)` are points
of `M_{0,5}` and `μ ≠ ν`. -/
def U6 (p : K × K × K) : Prop := U5 (p.1, p.2.1) ∧ U5 (p.1, p.2.2) ∧ p.2.1 ≠ p.2.2

/-- The adjacent transpositions `s₁, …, s₅` of the six labels. -/
def act6 : Fin 5 → K × K × K → K × K × K
  | 0 => fun p => (1 - p.1, 1 - p.2.1, 1 - p.2.2)
  | 1 => fun p => (p.1 / (p.1 - 1), p.2.1 / (p.2.1 - 1), p.2.2 / (p.2.2 - 1))
  | 2 => fun p => (1 - p.1, p.2.1 * (p.1 - 1) / (p.1 - p.2.1), p.2.2 * (p.1 - 1) / (p.1 - p.2.2))
  | 3 => fun p => (p.2.1, p.1, p.2.2)
  | 4 => fun p => (p.1, p.2.2, p.2.1)

/-- Their factor on `L = L₁ ⊗ ⋯ ⊗ L₆`. -/
def cL6 : Fin 5 → K × K × K → K
  | 0 => fun _ => 1
  | 1 => fun p => 1 / ((p.1 - 1) ^ 2 * (p.2.1 - 1) ^ 2 * (p.2.2 - 1) ^ 2)
  | 2 => fun p => p.1 ^ 2 * (p.1 - 1) ^ 2 / ((p.1 - p.2.1) ^ 2 * (p.1 - p.2.2) ^ 2)
  | 3 => fun _ => 1
  | 4 => fun _ => 1

/-- The factor of `s₁, …, s₄` on `L₆`. -/
def c6 : Fin 4 → K × K × K → K
  | 0 => fun _ => -1
  | 1 => fun p => -1 / (p.2.2 - 1) ^ 2
  | 2 => fun p => p.1 * (p.1 - 1) / (p.1 - p.2.2) ^ 2
  | 3 => fun _ => 1

/-- `s₁, …, s₄` as substitutions. -/
def act6s (i : Fin 4) : K × K × K → K × K × K := act6 i.castSucc

lemma act6_U6 (i : Fin 5) {p : K × K × K} (hp : U6 p) : U6 (act6 i p) := by
  obtain ⟨l, m, n⟩ := p
  obtain ⟨hm, hn, mn⟩ := hp
  dsimp only at hm hn mn
  obtain ⟨a0, a1, b0, b1, ab⟩ := id hm
  obtain ⟨-, -, c0, c1, ac⟩ := id hn
  have a1' : l - 1 ≠ 0 := sub_ne_zero.2 a1
  fin_cases i
  · refine ⟨act5_U5 0 hm, act5_U5 0 hn, fun e => mn ?_⟩
    change 1 - m = 1 - n at e
    linear_combination -e
  · refine ⟨act5_U5 1 hm, act5_U5 1 hn, fun e => mn ?_⟩
    change m / (m - 1) = n / (n - 1) at e
    rw [div_eq_div_iff (sub_ne_zero.2 b1) (sub_ne_zero.2 c1)] at e
    linear_combination -e
  · refine ⟨act5_U5 2 hm, act5_U5 2 hn, fun e => mul_ne_zero (mul_ne_zero a1' a0)
      (sub_ne_zero.2 mn) ?_⟩
    change m * (l - 1) / (l - m) = n * (l - 1) / (l - n) at e
    rw [div_eq_div_iff (sub_ne_zero.2 ab) (sub_ne_zero.2 ac)] at e
    linear_combination e
  · exact ⟨act5_U5 3 hm, (⟨b0, b1, c0, c1, mn⟩ : U5 (m, n)), ac⟩
  · exact ⟨hn, hm, Ne.symm mn⟩

/-- `h = (λμν(1 − λ)(1 − μ)(1 − ν)(λ − μ)(λ − ν)(μ − ν))²`, the square of the product of the nine
units. -/
def hL6 (p : K × K × K) : K :=
  (p.1 * p.2.1 * p.2.2 * (1 - p.1) * (1 - p.2.1) * (1 - p.2.2) * (p.1 - p.2.1) * (p.1 - p.2.2) *
    (p.2.1 - p.2.2)) ^ 2

/-- `g = ν⁴(1 − ν)⁴(λ − ν)⁴(μ − ν)⁴/(λμ(1 − λ)(1 − μ)(λ − μ))`; `g²` trivialises `L₆^{⊗20}`. -/
def g6 (p : K × K × K) : K :=
  (p.2.2 * (1 - p.2.2) * (p.1 - p.2.2) * (p.2.1 - p.2.2)) ^ 4 /
    (p.1 * p.2.1 * (1 - p.1) * (1 - p.2.1) * (p.1 - p.2.1))

lemma hL6_ne {p : K × K × K} (hp : U6 p) : hL6 p ≠ 0 := by
  obtain ⟨⟨a0, a1, b0, b1, ab⟩, ⟨-, -, c0, c1, ac⟩, bc⟩ := hp
  dsimp only at a0 a1 b0 b1 ab c0 c1 ac
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm; have := sub_ne_zero.2 c1.symm
  have := sub_ne_zero.2 ab; have := sub_ne_zero.2 ac; have := sub_ne_zero.2 bc
  simp only [hL6]; positivity

lemma g6_num_ne {p : K × K × K} (hp : U6 p) :
    (p.2.2 * (1 - p.2.2) * (p.1 - p.2.2) * (p.2.1 - p.2.2)) ^ 4 ≠ 0 := by
  obtain ⟨-, ⟨-, -, c0, c1, ac⟩, bc⟩ := hp
  dsimp only at c0 c1 ac
  have := sub_ne_zero.2 c1.symm; have := sub_ne_zero.2 ac; have := sub_ne_zero.2 bc
  positivity

lemma g6_den_ne {p : K × K × K} (hp : U6 p) :
    p.1 * p.2.1 * (1 - p.1) * (1 - p.2.1) * (p.1 - p.2.1) ≠ 0 := by
  obtain ⟨⟨a0, a1, b0, b1, ab⟩, -, -⟩ := hp
  dsimp only at a0 a1 b0 b1 ab
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm; have := sub_ne_zero.2 ab
  positivity

lemma g6_ne {p : K × K × K} (hp : U6 p) : g6 p ≠ 0 :=
  div_ne_zero (g6_num_ne hp) (g6_den_ne hp)

/-- `L^{⊗5}` is equivariantly trivial: `cL(s)⁵ = h(sx)/h(x)` on the generators, with `h` the
square of the product of the nine units. -/
theorem cL6_pow_five (i : Fin 5) {p : K × K × K} (hp : U6 p) :
    cL6 i p ^ 5 = hL6 (act6 i p) / hL6 p := by
  obtain ⟨l, m, n⟩ := p
  obtain ⟨⟨a0, a1, b0, b1, ab⟩, ⟨-, -, c0, c1, ac⟩, bc⟩ := hp
  simp only at a0 a1 b0 b1 ab c0 c1 ac bc
  have := sub_ne_zero.2 a1; have := sub_ne_zero.2 b1; have := sub_ne_zero.2 c1
  have := sub_ne_zero.2 ab; have := sub_ne_zero.2 ac; have := sub_ne_zero.2 bc
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 b1.symm; have := sub_ne_zero.2 c1.symm
  fin_cases i <;> simp [cL6, act6, hL6] <;> field_simp <;> ring

/-- On the generators, the factor `c` of `L₆` satisfies `c(s)¹⁰ = −g(sx)/g(x)`. -/
theorem c6_pow_ten (i : Fin 4) {p : K × K × K} (hp : U6 p) :
    c6 i p ^ 10 = -(g6 (act6s i p) / g6 p) := by
  have hq : U6 (act6s i p) := act6_U6 i.castSucc hp
  rw [g6, g6, div_div_div_eq, ← neg_div, eq_div_iff (mul_ne_zero (g6_den_ne hq) (g6_num_ne hp))]
  obtain ⟨l, m, n⟩ := p
  obtain ⟨⟨a0, a1, b0, b1, ab⟩, ⟨-, -, c0, c1, ac⟩, bc⟩ := hp
  simp only at a0 a1 b0 b1 ab c0 c1 ac bc
  have := sub_ne_zero.2 a1; have := sub_ne_zero.2 b1; have := sub_ne_zero.2 c1
  have := sub_ne_zero.2 ab; have := sub_ne_zero.2 ac
  have := sub_ne_zero.2 a1.symm; have := sub_ne_zero.2 c1.symm
  fin_cases i <;> simp [c6, act6s, act6] <;> field_simp <;> ring

/-- A root `ω` of `ω⁴ + ω³ + ω² + ω + 1` is a primitive fifth root of unity when `5 ≠ 0`:
`ω^m = 1` forces `5 ∣ m`. -/
lemma five_dvd_of_pow (h5 : (5 : K) ≠ 0) {ω : K} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (m : ℤ) (e : ω ^ m = 1) : 5 ∣ m := by
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω
  have w5 : ω ^ 5 = 1 := by linear_combination (ω - 1) * hω
  have w1 : ω ≠ 1 := fun h => h5 (by rw [h] at hω; linear_combination hω)
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) ∧ m = 5 * q + r :=
    ⟨m / 5, m % 5, by omega, by omega⟩
  rw [zpow_add₀ hω0, zpow_mul, show ω ^ (5 : ℤ) = 1 by exact_mod_cast w5, one_zpow,
    one_mul] at e
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simp
  · exact absurd (by simpa using e) w1
  · have : ω ^ 2 = 1 := by simpa using e
    exact absurd (by linear_combination (ω - 1) * hω - (ω ^ 3 + ω) * this) w1
  · have : ω ^ 3 = 1 := by simpa using e
    exact absurd (by linear_combination (1 + ω ^ 3) * this - ω * (ω - 1) * hω) w1
  · have : ω ^ 4 = 1 := by simpa using e
    exact absurd (by linear_combination (ω - 1) * hω - ω * this) w1

/-- The point `(ω² + ω³, 1 + ω² + ω³, −ω⁴)` of `M_{0,6}`, the configuration `0, 1, ω, …, ω⁴`
up to a homography, is fixed by the `5`-cycle `s₁s₂s₃s₄`, where the factor on `L`, and on `L₆`,
is `ω`. -/
lemma fix_five {ω : K} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    U6 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) ∧
      wAct act6 [0, 1, 2, 3] ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) =
        (ω ^ 2 + ω ^ 3, 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) ∧
      wCoc act6 cL6 [0, 1, 2, 3] ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) = ω ∧
      wAct act6s [0, 1, 2, 3] ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) =
        (ω ^ 2 + ω ^ 3, 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) ∧
      wCoc act6s c6 [0, 1, 2, 3] ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) = ω := by
  -- each quantity below is a unit of `ℤ[ω]`: `A x + B (ω⁴ + ω³ + ω² + ω + 1) = 1`
  have ne : ∀ {x : K} (A B : K), A * x + B * (ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1) = 1 → x ≠ 0 :=
    fun A B h e => one_ne_zero (h.symm.trans (by rw [e, hω]; ring))
  have ha : ω ^ 2 + ω ^ 3 ≠ 0 := ne (1 + ω ^ 2 + ω ^ 3) (1 - ω - ω ^ 2) (by ring)
  have ha1 : ω ^ 2 + ω ^ 3 ≠ 1 :=
    sub_ne_zero.1 (ne (-2 - ω ^ 2 - ω ^ 3) (-1 + ω + ω ^ 2) (by ring))
  have hb : 1 + ω ^ 2 + ω ^ 3 ≠ 0 := ne (ω ^ 2 + ω ^ 3) (1 - ω - ω ^ 2) (by ring)
  have hb1 : 1 + ω ^ 2 + ω ^ 3 ≠ 1 :=
    sub_ne_zero.1 (ne (1 + ω ^ 2 + ω ^ 3) (1 - ω - ω ^ 2) (by ring))
  have hab : ω ^ 2 + ω ^ 3 ≠ 1 + ω ^ 2 + ω ^ 3 := sub_ne_zero.1 (ne (-1) 0 (by ring))
  have hc : -ω ^ 4 ≠ 0 := ne (-ω) (1 - ω) (by ring)
  have hc1 : -ω ^ 4 ≠ 1 := sub_ne_zero.1 (ne (-1 - ω - ω ^ 3) (-ω + ω ^ 2 - ω ^ 3) (by ring))
  have hac : ω ^ 2 + ω ^ 3 ≠ -ω ^ 4 := sub_ne_zero.1 (ne (ω + ω ^ 3) (1 - ω - ω ^ 3) (by ring))
  have hd : 1 + ω ^ 2 + ω ^ 3 - -ω ^ 4 ≠ 0 :=
    ne (1 + ω + ω ^ 2 + ω ^ 3) (-ω - ω ^ 2 - ω ^ 3) (by ring)
  have d1 : -ω ^ 2 - ω ^ 3 - 1 ≠ 0 := ne (-ω ^ 2 - ω ^ 3) (1 - ω - ω ^ 2) (by ring)
  have d2 : 1 - ω ^ 2 - ω ^ 3 - 1 ≠ 0 := ne (-1 - ω ^ 2 - ω ^ 3) (1 - ω - ω ^ 2) (by ring)
  have d3 : 1 + ω - 1 ≠ 0 := ne (-1 - ω - ω ^ 2 - ω ^ 3) 1 (by ring)
  have d4 : 1 + ω ^ 2 + ω ^ 3 - (ω ^ 2 + ω ^ 3) ≠ 0 := ne 1 0 (by ring)
  have s4 : act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) =
      (1 + ω ^ 2 + ω ^ 3, ω ^ 2 + ω ^ 3, -ω ^ 4) := rfl
  have s3 : act6 2 ((1 + ω ^ 2 + ω ^ 3 : K), ω ^ 2 + ω ^ 3, -ω ^ 4) =
      (-ω ^ 2 - ω ^ 3, 1 - ω ^ 2 - ω ^ 3, 1 + ω) := by
    change (1 - (1 + ω ^ 2 + ω ^ 3), (ω ^ 2 + ω ^ 3) * (1 + ω ^ 2 + ω ^ 3 - 1) /
      (1 + ω ^ 2 + ω ^ 3 - (ω ^ 2 + ω ^ 3)), -ω ^ 4 * (1 + ω ^ 2 + ω ^ 3 - 1) /
      (1 + ω ^ 2 + ω ^ 3 - -ω ^ 4)) = _
    simp only [Prod.mk.injEq]
    refine ⟨by ring, ?_, ?_⟩
    · rw [div_eq_iff d4]; linear_combination (-1 + ω + ω ^ 2) * hω
    · rw [div_eq_iff hd]; linear_combination (-1 - ω ^ 3) * hω
  have s2 : act6 1 ((-ω ^ 2 - ω ^ 3 : K), 1 - ω ^ 2 - ω ^ 3, 1 + ω) =
      (1 - ω ^ 2 - ω ^ 3, -ω ^ 2 - ω ^ 3, 1 + ω ^ 4) := by
    change ((-ω ^ 2 - ω ^ 3) / (-ω ^ 2 - ω ^ 3 - 1), (1 - ω ^ 2 - ω ^ 3) / (1 - ω ^ 2 - ω ^ 3 - 1),
      (1 + ω) / (1 + ω - 1)) = _
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [div_eq_iff d1]; linear_combination (1 - ω - ω ^ 2) * hω
    · rw [div_eq_iff d2]; linear_combination (1 - ω - ω ^ 2) * hω
    · rw [div_eq_iff d3]; linear_combination (1 - ω) * hω
  have s1 : act6 0 ((1 - ω ^ 2 - ω ^ 3 : K), -ω ^ 2 - ω ^ 3, 1 + ω ^ 4) =
      (ω ^ 2 + ω ^ 3, 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) := by
    change ((1 - (1 - ω ^ 2 - ω ^ 3) : K), 1 - (-ω ^ 2 - ω ^ 3), 1 - (1 + ω ^ 4)) = _
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  have e3 : (1 + ω ^ 2 + ω ^ 3) * (1 + ω ^ 2 + ω ^ 3 - 1) / (1 + ω ^ 2 + ω ^ 3 - -ω ^ 4) ^ 2 =
      ω ^ 3 := by
    rw [div_eq_iff (pow_ne_zero 2 hd)]
    linear_combination (ω ^ 2 - ω ^ 3 + ω ^ 4 - ω ^ 5 - ω ^ 6 - ω ^ 7) * hω
  have hfix : wAct act6 [0, 1, 2, 3] ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) =
      (ω ^ 2 + ω ^ 3, 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) := by
    change act6 0 (act6 1 (act6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4)))) = _
    rw [s4, s3, s2, s1]
  refine ⟨⟨⟨ha, ha1, hb, hb1, hab⟩, ⟨ha, ha1, hc, hc1, hac⟩, sub_ne_zero.1 hd⟩, hfix, ?_, hfix, ?_⟩
  · change cL6 0 (act6 1 (act6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4)))) *
      (cL6 1 (act6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4))) *
      (cL6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4)) *
      (cL6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) * 1))) = ω
    rw [s4, s3]
    change (1 : K) * (1 / ((-ω ^ 2 - ω ^ 3 - 1) ^ 2 * (1 - ω ^ 2 - ω ^ 3 - 1) ^ 2 *
      (1 + ω - 1) ^ 2) * ((1 + ω ^ 2 + ω ^ 3) ^ 2 * (1 + ω ^ 2 + ω ^ 3 - 1) ^ 2 /
      ((1 + ω ^ 2 + ω ^ 3 - (ω ^ 2 + ω ^ 3)) ^ 2 * (1 + ω ^ 2 + ω ^ 3 - -ω ^ 4) ^ 2) *
      (1 * 1))) = ω
    rw [show (1 : K) / ((-ω ^ 2 - ω ^ 3 - 1) ^ 2 * (1 - ω ^ 2 - ω ^ 3 - 1) ^ 2 *
        (1 + ω - 1) ^ 2) = ω ^ 3 by
          rw [div_eq_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 d1) (pow_ne_zero 2 d2))
            (pow_ne_zero 2 d3))]
          linear_combination
            (1 - ω + ω ^ 5 - ω ^ 6 - ω ^ 9 - 2 * ω ^ 11 - 3 * ω ^ 12 - ω ^ 13) * hω,
      show (1 + ω ^ 2 + ω ^ 3) ^ 2 * (1 + ω ^ 2 + ω ^ 3 - 1) ^ 2 /
        ((1 + ω ^ 2 + ω ^ 3 - (ω ^ 2 + ω ^ 3)) ^ 2 * (1 + ω ^ 2 + ω ^ 3 - -ω ^ 4) ^ 2) = ω ^ 3 by
          rw [div_eq_iff (mul_ne_zero (pow_ne_zero 2 d4) (pow_ne_zero 2 hd))]
          linear_combination (-ω ^ 3 + 2 * ω ^ 4 - ω ^ 5 + ω ^ 6 + 2 * ω ^ 7 + ω ^ 8) * hω]
    linear_combination (-ω + ω ^ 2) * hω
  · change c6 0 (act6 1 (act6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4)))) *
      (c6 1 (act6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4))) *
      (c6 2 (act6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4)) *
      (c6 3 ((ω ^ 2 + ω ^ 3 : K), 1 + ω ^ 2 + ω ^ 3, -ω ^ 4) * 1))) = ω
    rw [s4, s3]
    change (-1 : K) * (-1 / (1 + ω - 1) ^ 2 * ((1 + ω ^ 2 + ω ^ 3) * (1 + ω ^ 2 + ω ^ 3 - 1) /
      (1 + ω ^ 2 + ω ^ 3 - -ω ^ 4) ^ 2 * (1 * 1))) = ω
    rw [e3, show (-1 : K) / (1 + ω - 1) ^ 2 = -ω ^ 3 by
      rw [div_eq_iff (pow_ne_zero 2 d3)]; linear_combination (-1 + ω) * hω]
    linear_combination (-ω + ω ^ 2) * hω

/-- The point `(−1, −i, i)` of `M_{0,6}` is fixed by the `4`-cycle `s₁s₂s₃`, where the factor on
`L₆` is `i`. -/
lemma fix_four6 (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) :
    U6 ((-1 : K), -ι, ι) ∧ wAct act6s [0, 1, 2] ((-1 : K), -ι, ι) = (-1, -ι, ι) ∧
      wCoc act6s c6 [0, 1, 2] ((-1 : K), -ι, ι) = ι := by
  have hι0 : ι ≠ 0 := fun h => h2 (by rw [h] at hι; linear_combination 2 * hι)
  have hι1 : ι ≠ 1 := fun h => h2 (by rw [h] at hι; linear_combination hι)
  have hιm : ι ≠ -1 := fun h => h2 (by rw [h] at hι; linear_combination hι)
  have t3 : act6 2 ((-1 : K), -ι, ι) = (2, 1 - ι, ι + 1) := by
    change ((1 - -1 : K), -ι * (-1 - 1) / (-1 - -ι), ι * (-1 - 1) / (-1 - ι)) = _
    simp only [Prod.mk.injEq]
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [div_eq_iff (fun h => hι1 (by linear_combination h))]; linear_combination hι
    · rw [div_eq_iff (fun h => hιm (by linear_combination -h))]; linear_combination hι
  have t2 : act6 1 ((2 : K), 1 - ι, ι + 1) = (2, ι + 1, 1 - ι) := by
    change ((2 : K) / (2 - 1), (1 - ι) / (1 - ι - 1), (ι + 1) / (ι + 1 - 1)) = _
    simp only [Prod.mk.injEq]
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [div_eq_iff (fun h => hι0 (by linear_combination -h))]; linear_combination hι
    · rw [div_eq_iff (fun h => hι0 (by linear_combination h))]; linear_combination hι
  have t1 : act6 0 ((2 : K), ι + 1, 1 - ι) = (-1, -ι, ι) := by
    change ((1 - 2 : K), 1 - (ι + 1), 1 - (1 - ι)) = _
    simp only [Prod.mk.injEq]
    exact ⟨by norm_num, by ring, by ring⟩
  refine ⟨⟨⟨by norm_num, fun h => h2 (by linear_combination -h), neg_ne_zero.2 hι0,
    fun h => hιm (by linear_combination -h), fun h => hι1 (by linear_combination h)⟩,
    (fix_four h2 hι).1, fun h => h2 (by linear_combination ι * h + 2 * hι)⟩, ?_,
    (fix_four h2 hι).2.2.2.2⟩
  change act6 0 (act6 1 (act6 2 ((-1 : K), -ι, ι))) = _
  rw [t3, t2, t1]

/-- The entry « 20 ? » of page 70 for `L`, `n = 6`, does not check: a power `m` of the cocycle
of `L` is the coboundary of a nowhere-zero function on `M_{0,6}(K)` iff `5 ∣ m` (`5 ≠ 0`, a root
`ω` of `ω⁴ + ω³ + ω² + ω + 1`). -/
theorem coboundary_cL6_iff (h5 : (5 : K) ≠ 0) {ω : K} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (m : ℤ) : (∃ h : K × K × K → K, (∀ p, U6 p → h p ≠ 0) ∧
      ∀ w p, U6 p → wCoc act6 cL6 w p ^ m = h (wAct act6 w p) / h p) ↔ 5 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hU, hfix, hcoc, -, -⟩ := fix_five hω
    exact five_dvd_of_pow h5 hω m <| by
      simpa only [hfix, hcoc, div_self (hh _ hU)] using hc [0, 1, 2, 3] _ hU
  · rintro ⟨t, rfl⟩
    have hh p (hp : U6 p) : hL6 p ^ t ≠ (0 : K) := zpow_ne_zero _ (hL6_ne hp)
    refine ⟨_, hh, wCoc_zpow (fun i p hp => act6_U6 i hp) hh fun i p hp => ?_⟩
    rw [zpow_mul, show cL6 i p ^ (5 : ℤ) = _ by exact_mod_cast cL6_pow_five i hp, div_zpow]

/-- The entry « 60 ? » of page 70 for `L_i`, `n = 6`, does not check: a power `m` of the cocycle
of `L₆` under `𝔖₅` is the coboundary of a nowhere-zero function on `M_{0,6}(K)` iff `20 ∣ m`
(`2 ≠ 0`, `5 ≠ 0`, `i² = −1`, `ω⁴ + ω³ + ω² + ω + 1 = 0`). -/
theorem coboundary_c6_iff (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1)
    {ω : K} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (m : ℤ) :
    (∃ h : K × K × K → K, (∀ p, U6 p → h p ≠ 0) ∧
      ∀ w p, U6 p → wCoc act6s c6 w p ^ m = h (wAct act6s w p) / h p) ↔ 20 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hU, -, -, hfix, hcoc⟩ := fix_five hω
    have e := hc [0, 1, 2, 3] _ hU
    rw [hfix, hcoc, div_self (hh _ hU)] at e
    obtain ⟨hU', hfix', hcoc'⟩ := fix_four6 h2 hι
    have e' := hc [0, 1, 2] _ hU'
    rw [hfix', hcoc', div_self (hh _ hU')] at e'
    have := five_dvd_of_pow h5 hω m e
    have := four_dvd_of_pow h2 hι m e'
    omega
  · rintro ⟨t, rfl⟩
    have hh p (hp : U6 p) : (g6 p ^ 2) ^ t ≠ (0 : K) := zpow_ne_zero _ (pow_ne_zero _ (g6_ne hp))
    refine ⟨_, hh, wCoc_zpow (fun i p hp => act6_U6 i.castSucc hp) hh fun i p hp => ?_⟩
    rw [zpow_mul, show c6 i p ^ (20 : ℤ) = g6 (act6s i p) ^ 2 / g6 p ^ 2 by
      rw [show (20 : ℤ) = ((10 * 2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_mul,
        c6_pow_ten i hp]; ring, div_zpow]

/-! ## All `n`: `L` has order `n − 1`, `L_i` has order `(n − 1)(n − 2)`

The three columns above suggest a pattern, `n − 1` for `L` and `(n − 1)(n − 2)` for `L_i`, and
this section proves it for every `n`, in a model where the cocycle no longer has to be written
in normalised coordinates.

The model. A point of `ℙ¹(K)` is a nonzero vector of `K²` up to a scalar, and `n` points are
distinct iff all the brackets `[vᵢ vⱼ] = vᵢ₁vⱼ₂ − vᵢ₂vⱼ₁`, `i ≠ j`, are nonzero (`Conf`). A
function on `M_{0,n}(K)` is a function of such a configuration invariant under `GL₂(K)` and
under rescaling each `vᵢ`. The tangent line of `ℙ¹` at the point `⟨v⟩` is
`Hom(⟨v⟩, K²/⟨v⟩) ≃ ⟨v⟩^{⊗−2} ⊗ det K²`, so a nowhere-zero section of `L_i^{⊗m}` invariant under
`PGL₂(K)` is, up to inverting it, a nowhere-zero function of weight `t^{2m}` when `vᵢ` is
multiplied by `t`, weight `1` in the other vectors, and weight `det(g)^m` under `g ∈ GL₂(K)`;
for `L = L₁ ⊗ ⋯ ⊗ Lₙ` the weights are `tᵢ^{2m}` in each vector and `det(g)^{mn}`. An
equivariant trivialisation of `L^{⊗m}` (`TrivL`), of `L_i^{⊗m}` under the stabiliser of the
`i`-th point (`TrivLi`), is such a function invariant under relabelling the points. As in the
sections above, the function is not required to be regular. Not formalised: this dictionary
between line bundles on `M_{0,n}` and functions of weight on configurations; its agreement
with the cocycles `derL`, `der`, `cL`, `c5`, `cL6`, `c6` of the normalised coordinates is the
last section.

* Upper bounds, for every `n` and every field (`trivL_of_dvd`, `trivLi_of_dvd`): the product
  `disc` of the brackets over the ordered pairs (`± Δ²`, `Δ` the Vandermonde-type product)
  trivialises `L^{⊗(n−1)}`; with the `n`-th point `p` and the `k = n − 1` others,
  `(∏ᵢ [vᵢ p])^{2(k−1)} / disc(v)` trivialises `Lₙ^{⊗k(k−1)}`. These generalise
  `(λμ(1 − λ)(1 − μ)(λ − μ))²` and its companions above.
* Lower bounds, by isotropy points: the configuration `{0} ∪ μ_{n−1}` is fixed by the
  `(n − 1)`-cycle together with `z ↦ ωz`, of determinant `ω`, which forces `ω^{mn} = 1` for
  `L` and `ω^m = 1` for `Lₙ` (`0` the `n`-th point); the configuration `{0, ∞} ∪ μ_{n−2}`
  (`0` the `n`-th point) gives `ζ^m = 1` with `ζ` of order `n − 2`. As `n − 1` and `n − 2` are
  coprime, `(n − 1)(n − 2) ∣ m`.

`trivL_iff`: over a field with a primitive `(n − 1)`-th root of unity, `L^{⊗m}` is equivariantly
trivial iff `(n − 1) ∣ m`; `trivLi_iff`: with primitive roots of orders `n − 1` and `n − 2`,
`Lₙ^{⊗m}` is iff `(n − 1)(n − 2) ∣ m`. For `n = 4, 5, 6` this gives `3, 4, 5` and `6, 12, 20`,
the values found above. -/

/-- The bracket `[v w] = v₁w₂ − v₂w₁`: it vanishes iff `v` and `w` give the same point of
`ℙ¹(K)` (or one of them is zero). -/
def br (v w : K × K) : K := v.1 * w.2 - v.2 * w.1

/-- The linear substitution `(x, y) ↦ (ax + by, cx + dy)`. -/
def lin (a b c d : K) (v : K × K) : K × K := (a * v.1 + b * v.2, c * v.1 + d * v.2)

/-- `n` vectors of `K²` giving `n` distinct points of `ℙ¹(K)`. -/
def Conf {n : ℕ} (v : Fin n → K × K) : Prop := ∀ i j, i ≠ j → br (v i) (v j) ≠ 0

/-- The product of the brackets `[vᵢ vⱼ]` over the ordered pairs `i ≠ j`. -/
def disc {n : ℕ} (v : Fin n → K × K) : K := ∏ i, ∏ j, if i = j then 1 else br (v i) (v j)

/-- The product of the brackets `[vᵢ p]`. -/
def brp {k : ℕ} (p : K × K) (v : Fin k → K × K) : K := ∏ i, br (v i) p

variable (K) in
/-- An equivariant trivialisation of `L^{⊗m}`, `L = L₁ ⊗ ⋯ ⊗ Lₙ`, on `M_{0,n}(K)`. -/
def TrivL (n : ℕ) (m : ℤ) : Prop :=
  ∃ F : (Fin n → K × K) → K, ∀ v, Conf v → F v ≠ 0 ∧
    (∀ t : Fin n → K, (∀ i, t i ≠ 0) → F (fun i => t i • v i) = (∏ i, t i) ^ (2 * m) * F v) ∧
    (∀ a b c d : K, a * d - b * c ≠ 0 →
      F (fun i => lin a b c d (v i)) = (a * d - b * c) ^ (m * n) * F v) ∧
    ∀ σ : Equiv.Perm (Fin n), F (v ∘ σ) = F v

variable (K) in
/-- An equivariant trivialisation of `Lₙ^{⊗m}` on `M_{0,n}(K)`, `n = k + 1`, under the
stabiliser `𝔖_k` of the `n`-th point `p`; `v` are the `k` other points. -/
def TrivLi (k : ℕ) (m : ℤ) : Prop :=
  ∃ F : K × K → (Fin k → K × K) → K, ∀ p v, Conf v → (∀ i, br p (v i) ≠ 0) → F p v ≠ 0 ∧
    (∀ (s : K) (t : Fin k → K), s ≠ 0 → (∀ i, t i ≠ 0) →
      F (s • p) (fun i => t i • v i) = s ^ (2 * m) * F p v) ∧
    (∀ a b c d : K, a * d - b * c ≠ 0 →
      F (lin a b c d p) (fun i => lin a b c d (v i)) = (a * d - b * c) ^ m * F p v) ∧
    ∀ σ : Equiv.Perm (Fin k), F p (v ∘ σ) = F p v

lemma br_lin (a b c d : K) (v w : K × K) :
    br (lin a b c d v) (lin a b c d w) = (a * d - b * c) * br v w := by
  simp only [br, lin]; ring

lemma br_smul (s t : K) (v w : K × K) : br (s • v) (t • w) = s * t * br v w := by
  simp only [br, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma prod_ite_ne {n : ℕ} (i : Fin n) (c : K) :
    ∏ j, (if i = j then 1 else c) = c ^ (n - 1) := by
  simp [Finset.prod_ite, Finset.filter_ne]

/-- Counting the factors of a product over the ordered pairs `i ≠ j`. -/
lemma prod_offdiag {n : ℕ} (c : K) (u : Fin n → K) (e : Fin n → Fin n → K) :
    ∏ i, ∏ j, (if i = j then 1 else c * u i * u j * e i j) =
      c ^ (n * (n - 1)) * (∏ i, u i) ^ (2 * (n - 1)) * ∏ i, ∏ j, if i = j then 1 else e i j := by
  have h (i j) : (if i = j then 1 else c * u i * u j * e i j) = (if i = j then 1 else c) *
      (if i = j then 1 else u i) * (if j = i then 1 else u j) * if i = j then 1 else e i j := by
    by_cases h : i = j <;> simp [h, eq_comm]
  have hC : ∏ i, ∏ j, (if j = i then (1 : K) else u j) = ∏ j, u j ^ (n - 1) := by
    rw [Finset.prod_comm]; exact Finset.prod_congr rfl fun j _ => prod_ite_ne j _
  simp only [h, Finset.prod_mul_distrib, hC, prod_ite_ne, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow]
  ring

lemma disc_smul {n : ℕ} (t : Fin n → K) (v : Fin n → K × K) :
    disc (fun i => t i • v i) = (∏ i, t i) ^ (2 * (n - 1)) * disc v := by
  simpa [disc, br_smul] using prod_offdiag 1 t fun i j => br (v i) (v j)

lemma disc_lin {n : ℕ} (a b c d : K) (v : Fin n → K × K) :
    disc (fun i => lin a b c d (v i)) = (a * d - b * c) ^ (n * (n - 1)) * disc v := by
  simpa [disc, br_lin] using prod_offdiag (a * d - b * c) 1 fun i j => br (v i) (v j)

lemma disc_perm {n : ℕ} (v : Fin n → K × K) (σ : Equiv.Perm (Fin n)) :
    disc (v ∘ σ) = disc v := by
  let f i j := if i = j then (1 : K) else br (v i) (v j)
  have e : disc (v ∘ σ) = ∏ i, ∏ j, f (σ i) (σ j) := by simp [disc, f, σ.injective.eq_iff]
  rw [e]
  exact (Finset.prod_congr rfl fun i _ => Equiv.prod_comp σ (f (σ i))).trans
    (Equiv.prod_comp σ fun i => ∏ j, f i j)

lemma disc_ne {n : ℕ} {v : Fin n → K × K} (hv : Conf v) : disc v ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => by
    split_ifs with h
    exacts [one_ne_zero, hv i j h]

/-- `L^{⊗(n−1)}` is equivariantly trivial on `M_{0,n}`, trivialised by `disc`, for every `n`
and every field. -/
theorem trivL_of_dvd {n : ℕ} {m : ℤ} (h : ((n - 1 : ℕ) : ℤ) ∣ m) : TrivL K n m := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨fun v => disc v ^ q, fun v hv => ⟨zpow_ne_zero _ (disc_ne hv), fun t ht => ?_,
    fun a b c d hd => ?_, fun σ => by simp only [disc_perm]⟩⟩
  · simp only [disc_smul, mul_zpow, ← zpow_natCast, ← zpow_mul]
    congr 2; push_cast; ring
  · simp only [disc_lin, mul_zpow, ← zpow_natCast, ← zpow_mul]
    congr 2; push_cast; ring

/-- `Lₙ^{⊗(n−1)(n−2)}` is equivariantly trivial on `M_{0,n}`, `n = k + 1`, trivialised by
`(∏ᵢ [vᵢ p])^{2(k−1)} / disc(v)`, for every `n` and every field. -/
theorem trivLi_of_dvd {k : ℕ} {m : ℤ} (h : ((k * (k - 1) : ℕ) : ℤ) ∣ m) : TrivLi K k m := by
  obtain ⟨q, rfl⟩ := h
  have hR (p : K × K) (v : Fin k → K × K) (hp : ∀ i, br p (v i) ≠ 0) : brp p v ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [show br (v i) p = -br p (v i) by simp only [br]; ring]; exact neg_ne_zero.2 (hp i)
  refine ⟨fun p v => (brp p v ^ (2 * (k - 1)) / disc v) ^ q, fun p v hv hp =>
    ⟨zpow_ne_zero _ (div_ne_zero (pow_ne_zero _ (hR p v hp)) (disc_ne hv)), fun s t hs ht => ?_,
    fun a b c d hd => ?_, fun σ => ?_⟩⟩
  · have hT : ∏ i, t i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht i
    have : brp (s • p) (fun i => t i • v i) ^ (2 * (k - 1)) / disc (fun i => t i • v i) =
        s ^ (2 * (k * (k - 1))) * (brp p v ^ (2 * (k - 1)) / disc v) := by
      simp only [brp, br_smul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, disc_smul]
      field_simp
      ring
    dsimp only; rw [this]; simp only [mul_zpow, ← zpow_natCast, ← zpow_mul]
    congr 2; push_cast; ring
  · have : brp (lin a b c d p) (fun i => lin a b c d (v i)) ^ (2 * (k - 1)) /
        disc (fun i => lin a b c d (v i)) =
        (a * d - b * c) ^ (k * (k - 1)) * (brp p v ^ (2 * (k - 1)) / disc v) := by
      simp only [brp, br_lin, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, disc_lin]
      field_simp
      ring
    dsimp only; rw [this]; simp only [mul_zpow, ← zpow_natCast, ← zpow_mul]
  · simp only [disc_perm, brp, Function.comp_apply]
    rw [Equiv.prod_comp σ fun i => br (v i) p]

/-- The `k`-th roots of unity `ω^i`, as points `(ω^i, 1)`. -/
def rts (ω : K) (k : ℕ) (i : Fin k) : K × K := (ω ^ (i : ℕ), 1)

lemma rts_rot {k : ℕ} {ω : K} (hω : ω ^ k = 1) :
    rts ω k ∘ finRotate k = fun i => lin ω 0 0 1 (rts ω k i) := by
  funext i
  cases k with
  | zero => exact i.elim0
  | succ k =>
    simp only [Function.comp_apply, rts, lin, coe_finRotate]
    split_ifs with h
    · subst h; simp [Fin.val_last, ← pow_succ', hω]
    · simp [pow_succ']

lemma conf_rts {k : ℕ} {ω : K} (hω : IsPrimitiveRoot ω k) : Conf (rts ω k) := fun i j hij => by
  simp only [rts, br, mul_one, one_mul]
  exact sub_ne_zero.2 fun h => hij (Fin.ext (hω.pow_inj i.isLt j.isLt h))

lemma rts_ne {k : ℕ} {ω : K} (hω : IsPrimitiveRoot ω k) (i : Fin k) : ω ^ (i : ℕ) ≠ 0 :=
  pow_ne_zero _ (hω.ne_zero (by have := i.isLt; omega))

lemma conf_cons {k : ℕ} {q : K × K} {r : Fin k → K × K} (hq : ∀ i, br q (r i) ≠ 0)
    (hr : Conf r) : Conf (Fin.cons q r : Fin (k + 1) → K × K) := fun i j hij => by
  cases i using Fin.cases <;> cases j using Fin.cases
  · exact absurd rfl hij
  · simpa using hq _
  · simp only [Fin.cons_succ, Fin.cons_zero]
    rw [show ∀ v w : K × K, br v w = -br w v by intro v w; simp only [br]; ring]
    exact neg_ne_zero.2 (hq _)
  · simpa using hr _ _ fun h => hij (by rw [h])

lemma conf_comp {k : ℕ} {v : Fin k → K × K} (hv : Conf v) (σ : Equiv.Perm (Fin k)) :
    Conf (v ∘ σ) := fun _ _ h => hv _ _ (σ.injective.ne h)

/-- The cycle of the points `1, …, k`, fixing the point `0`. -/
def cyc (k : ℕ) : Equiv.Perm (Fin (k + 1)) := Equiv.Perm.decomposeFin.symm (0, finRotate k)

lemma cons_rot {k : ℕ} {ω : K} (hω : ω ^ k = 1) (q : K × K) :
    (Fin.cons q (rts ω k) : Fin (k + 1) → K × K) ∘ cyc k =
      Fin.cons q fun i => lin ω 0 0 1 (rts ω k i) := by
  funext i
  cases i using Fin.cases
  · simp [cyc]
  · simpa [cyc] using congrFun (rts_rot hω) _

lemma cons_lin (a b c d : K) {k : ℕ} (q : K × K) (r : Fin k → K × K) :
    (fun i => lin a b c d ((Fin.cons q r : Fin (k + 1) → K × K) i)) =
      Fin.cons (lin a b c d q) fun i => lin a b c d (r i) := by
  funext i; cases i using Fin.cases <;> simp

/-- The isotropy point `{0} ∪ μ_{n−1}` for `L`, `n = j + 2`: `ω^{mn} = 1` forces
`(n − 1) ∣ m`. -/
theorem dvd_of_trivL {j : ℕ} {ω : K} (hω : IsPrimitiveRoot ω (j + 1)) {m : ℤ}
    (h : TrivL K (j + 2) m) : ((j + 1 : ℕ) : ℤ) ∣ m := by
  obtain ⟨F, hF⟩ := h
  let v : Fin (j + 2) → K × K := Fin.cons (0, 1) (rts ω (j + 1))
  have hc : Conf v := conf_cons (fun i => by simpa [br, rts] using rts_ne hω i) (conf_rts hω)
  obtain ⟨h0, -, hg, hσ⟩ := hF v hc
  have e := hg ω 0 0 1 (by simpa using hω.ne_zero (by omega))
  rw [cons_lin, ← cons_rot hω.pow_eq_one, show lin ω 0 0 1 ((0 : K), (1 : K)) = (0, 1) by
    simp [lin], hσ] at e
  have e1 := hω.zpow_eq_one_iff_dvd _ |>.1 <| by
    simpa using mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
  have : ((j + 1 : ℕ) : ℤ) ∣ m * ((j + 1 : ℕ) : ℤ) + m := by
    convert e1 using 1; push_cast; ring
  exact (dvd_add_right (dvd_mul_left _ _)).1 this

/-- The isotropy points `{0} ∪ μ_{n−1}` and `{0, ∞} ∪ μ_{n−2}` for `Lₙ`, `n = j + 3`, `0` the
`n`-th point: `ω^m = 1` and `ζ^m = 1` force `(n − 1)(n − 2) ∣ m`. -/
theorem dvd_of_trivLi {j : ℕ} {ω ζ : K} (hω : IsPrimitiveRoot ω (j + 2))
    (hζ : IsPrimitiveRoot ζ (j + 1)) {m : ℤ} (h : TrivLi K (j + 2) m) :
    (((j + 2) * (j + 1) : ℕ) : ℤ) ∣ m := by
  obtain ⟨F, hF⟩ := h
  have hp0 : lin ω 0 0 1 ((0 : K), (1 : K)) = (0, 1) := by simp [lin]
  have hp0' : lin ζ 0 0 1 ((0 : K), (1 : K)) = (0, 1) := by simp [lin]
  -- the point `{0} ∪ μ_{n−1}`
  have hc := conf_rts hω
  have hp : ∀ i, br ((0 : K), (1 : K)) (rts ω (j + 2) i) ≠ 0 := fun i => by
    simpa [br, rts] using rts_ne hω i
  obtain ⟨h0, -, hg, hσ⟩ := hF _ _ hc hp
  have e := hg ω 0 0 1 (by simpa using hω.ne_zero (by omega))
  rw [hp0, show (fun i => lin ω 0 0 1 (rts ω (j + 2) i)) = _ from (rts_rot hω.pow_eq_one).symm,
    hσ] at e
  have d1 := hω.zpow_eq_one_iff_dvd _ |>.1 <| by
    simpa using mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
  -- the point `{0, ∞} ∪ μ_{n−2}`
  let v : Fin (j + 2) → K × K := Fin.cons (1, 0) (rts ζ (j + 1))
  have hc' : Conf v := conf_cons (fun i => by simp [br, rts]) (conf_rts hζ)
  have hp' : ∀ i, br ((0 : K), (1 : K)) (v i) ≠ 0 := fun i => by
    cases i using Fin.cases
    · simp [v, br]
    · simpa [v, br, rts] using rts_ne hζ _
  obtain ⟨h0', -, hg', hσ'⟩ := hF _ _ hc' hp'
  obtain ⟨-, hs, -, -⟩ := hF _ _ (conf_comp hc' (cyc (j + 1))) fun i => hp' _
  have e' := hg' ζ 0 0 1 (by simpa using hζ.ne_zero (by omega))
  have hv : (fun i => lin ζ 0 0 1 (v i)) =
      fun i => (Fin.cons ζ fun _ => 1 : Fin (j + 2) → K) i • (v ∘ cyc (j + 1)) i := by
    rw [cons_lin, cons_rot hζ.pow_eq_one]
    funext i; cases i using Fin.cases <;> simp [lin]
  rw [hp0', hv, ← one_smul K ((0 : K), (1 : K)),
    hs 1 _ one_ne_zero fun i => by cases i using Fin.cases <;> simp [hζ.ne_zero], one_zpow,
    one_mul, one_smul, hσ'] at e'
  have d2 := hζ.zpow_eq_one_iff_dvd _ |>.1 <| by
    simpa using mul_right_cancel₀ h0' (e'.symm.trans (one_mul _).symm)
  push_cast at d1 d2 ⊢
  exact IsCoprime.mul_dvd ⟨1, -1, by ring⟩ d1 d2

/-- The general formula for `L`: over a field with a primitive `(n − 1)`-th root of unity, `n ≥ 2`,
`L^{⊗m}` is equivariantly trivial on `M_{0,n}` iff `(n − 1) ∣ m` (énoncé de l'édition). -/
theorem trivL_iff {n : ℕ} (hn : 2 ≤ n) {ω : K} (hω : IsPrimitiveRoot ω (n - 1)) (m : ℤ) :
    TrivL K n m ↔ ((n - 1 : ℕ) : ℤ) ∣ m := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  exact ⟨dvd_of_trivL hω, trivL_of_dvd⟩

/-- The general formula for `L_i`: over a field with primitive roots of unity of orders `n − 1`
and `n − 2`, `n ≥ 3`, `Lₙ^{⊗m}` is equivariantly trivial on `M_{0,n}` under the stabiliser of
the `n`-th point iff `(n − 1)(n − 2) ∣ m` (énoncé de l'édition). -/
theorem trivLi_iff {n : ℕ} (hn : 3 ≤ n) {ω ζ : K} (hω : IsPrimitiveRoot ω (n - 1))
    (hζ : IsPrimitiveRoot ζ (n - 2)) (m : ℤ) :
    TrivLi K (n - 1) m ↔ (((n - 1) * (n - 2) : ℕ) : ℤ) ∣ m := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  exact ⟨dvd_of_trivLi hω hζ, trivLi_of_dvd⟩

/-! ## The two models agree, `n = 4, 5, 6` (#83)

The homogeneous model of the last section and the normalised cocycles of the first sections
describe the same line bundles. Put the points in normal position: `0, 1, ∞, λ` (`cfg4`),
`0, 1, ∞, λ, μ` (`cfg5`), `0, 1, ∞, λ, μ, ν` (`cfg6`), as vectors `(0, 1), (1, 1), (1, 0),
(λ, 1), …` of `K²`. A generator relabels the points; the substitution `g` of the
normalisation carries the relabelled configuration back to normal position up to rescaling
each vector by some `tᵢ` (`step4`, `step5`, `step5i`, `step6`, `step6i`, where the matrices
and the `tᵢ` are written out). A function `F` of weight `t^{2m}` and `det(g)^{mn}` then
satisfies `F(cfg(gx)) = ((∏ tᵢ)² det(g)ⁿ)^m F(cfg x)` (`trivL_step`; `trivLi_step` for `L_i`,
with `s² det(g)`), and the factor `(∏ tᵢ)² det(g)ⁿ` is exactly `derL`, `cL`, `cL6` (and
`s² det(g)` is `der`, `c5`, `c6`): `cob_of_trivL`, `cob_of_trivLi`.

* `coboundary_derL_of_trivL`, `coboundary_der_of_trivLi`, `coboundary_cL_of_trivL`,
  `coboundary_c5_of_trivLi`, `coboundary_cL6_of_trivL`, `coboundary_c6_of_trivLi`: an
  equivariant trivialisation of the homogeneous model restricts to `h = F ∘ cfg`, whose
  coboundary is the `m`-th power of the normalised cocycle, with no hypothesis on `K`.
* `trivL_four_iff`, `trivLi_four_iff`, `trivL_five_iff`, `trivLi_five_iff`, `trivL_six_iff`,
  `trivLi_six_iff`: the two conditions are equivalent, under the hypotheses on `K` of the
  normalised sections (the converse goes through the orders computed there and
  `trivL_of_dvd`, `trivLi_of_dvd`, not through an extension of `h`). -/

/-- Clear denominators in one or two coordinate equations. -/
local macro "field_ring" : tactic =>
  `(tactic| first | (constructor <;> (field_simp; try ring)) | (field_simp; try ring))

/-- One step of the restriction: a trivialisation of `L^{⊗m}` evaluated at
`tᵢ · g(v_{σ i})` picks up `((∏ tᵢ)² det(g)ⁿ)^m`. -/
lemma trivL_step {n : ℕ} {m : ℤ} {F : (Fin n → K × K) → K}
    (hF : ∀ v, Conf v → F v ≠ 0 ∧
      (∀ t : Fin n → K, (∀ i, t i ≠ 0) → F (fun i => t i • v i) = (∏ i, t i) ^ (2 * m) * F v) ∧
      (∀ a b c d : K, a * d - b * c ≠ 0 →
        F (fun i => lin a b c d (v i)) = (a * d - b * c) ^ (m * n) * F v) ∧
      ∀ σ : Equiv.Perm (Fin n), F (v ∘ σ) = F v)
    {v : Fin n → K × K} (hv : Conf v) (σ : Equiv.Perm (Fin n)) {a b c d : K}
    (hd : a * d - b * c ≠ 0) {t : Fin n → K} (ht : ∀ i, t i ≠ 0) :
    F (fun i => t i • lin a b c d (v (σ i))) =
      ((∏ i, t i) ^ 2 * (a * d - b * c) ^ n) ^ m * F v := by
  have hw := conf_comp hv σ
  have hw' : Conf fun i => lin a b c d ((v ∘ σ) i) := fun i j hij => by
    rw [br_lin]; exact mul_ne_zero hd (hw i j hij)
  change F (fun i => t i • lin a b c d ((v ∘ σ) i)) = _
  rw [(hF _ hw').2.1 t ht, (hF _ hw).2.2.1 a b c d hd, (hF v hv).2.2.2 σ, mul_zpow,
    ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 3; ring

/-- The same for `L_i^{⊗m}`: `((s)² det(g))^m`. -/
lemma trivLi_step {k : ℕ} {m : ℤ} {F : K × K → (Fin k → K × K) → K}
    (hF : ∀ p v, Conf v → (∀ i, br p (v i) ≠ 0) → F p v ≠ 0 ∧
      (∀ (s : K) (t : Fin k → K), s ≠ 0 → (∀ i, t i ≠ 0) →
        F (s • p) (fun i => t i • v i) = s ^ (2 * m) * F p v) ∧
      (∀ a b c d : K, a * d - b * c ≠ 0 →
        F (lin a b c d p) (fun i => lin a b c d (v i)) = (a * d - b * c) ^ m * F p v) ∧
      ∀ σ : Equiv.Perm (Fin k), F p (v ∘ σ) = F p v)
    {p : K × K} {v : Fin k → K × K} (hv : Conf v) (hp : ∀ i, br p (v i) ≠ 0)
    (σ : Equiv.Perm (Fin k)) {a b c d : K} (hd : a * d - b * c ≠ 0) {s : K} {t : Fin k → K}
    (hs : s ≠ 0) (ht : ∀ i, t i ≠ 0) :
    F (s • lin a b c d p) (fun i => t i • lin a b c d (v (σ i))) =
      (s ^ 2 * (a * d - b * c)) ^ m * F p v := by
  have hw := conf_comp hv σ
  have hpw : ∀ i, br p ((v ∘ σ) i) ≠ 0 := fun i => hp (σ i)
  have hw' : Conf fun i => lin a b c d ((v ∘ σ) i) := fun i j hij => by
    rw [br_lin]; exact mul_ne_zero hd (hw i j hij)
  have hpw' : ∀ i, br (lin a b c d p) (lin a b c d ((v ∘ σ) i)) ≠ 0 := fun i => by
    rw [br_lin]; exact mul_ne_zero hd (hpw i)
  change F _ (fun i => t i • lin a b c d ((v ∘ σ) i)) = _
  rw [(hF _ _ hw' hpw').2.1 s t hs ht, (hF _ _ hw hpw).2.2.1 a b c d hd, (hF p v hv hp).2.2.2 σ,
    mul_zpow, ← mul_assoc, ← zpow_natCast, ← zpow_mul]
  rfl

/-- Restricting a trivialisation of `L^{⊗m}` to normalised configurations `cfg x` gives a
function `h` whose coboundary is the `m`-th power of the cocycle `c`, provided each generator
`i` moves `cfg x` to `cfg (act i x)` by a relabelling `σ i`, a substitution `g` and rescalings
`t`, with `c i x = (∏ t)² det(g)ⁿ`. -/
lemma cob_of_trivL {ι α : Type*} {n : ℕ} {m : ℤ} {V : α → Prop} {act : ι → α → α}
    {c : ι → α → K} (cfg : α → Fin n → K × K) (σ : ι → Equiv.Perm (Fin n))
    (hconf : ∀ x, V x → Conf (cfg x))
    (hstep : ∀ i x, V x → ∃ (a b c' d : K) (t : Fin n → K), a * d - b * c' ≠ 0 ∧
      (∀ k, t k ≠ 0) ∧ cfg (act i x) = (fun k => t k • lin a b c' d (cfg x (σ i k))) ∧
      (∏ k, t k) ^ 2 * (a * d - b * c') ^ n = c i x)
    (h : TrivL K n m) :
    ∃ h : α → K, (∀ x, V x → h x ≠ 0) ∧ ∀ i x, V x → c i x ^ m = h (act i x) / h x := by
  obtain ⟨F, hF⟩ := h
  refine ⟨fun x => F (cfg x), fun x hx => (hF _ (hconf x hx)).1, fun i x hx => ?_⟩
  obtain ⟨a, b, c', d, t, hd, ht, he, hc⟩ := hstep i x hx
  rw [eq_div_iff (hF _ (hconf x hx)).1]
  dsimp only
  rw [he, trivL_step hF (hconf x hx) _ hd ht, hc]

/-- The same for `L_i`, the moving point being `pt x`, `s` its rescaling. -/
lemma cob_of_trivLi {ι α : Type*} {k : ℕ} {m : ℤ} {V : α → Prop} {act : ι → α → α}
    {c : ι → α → K} (pt : α → K × K) (cfg : α → Fin k → K × K) (σ : ι → Equiv.Perm (Fin k))
    (hconf : ∀ x, V x → Conf (cfg x)) (hpt : ∀ x, V x → ∀ i, br (pt x) (cfg x i) ≠ 0)
    (hstep : ∀ i x, V x → ∃ (a b c' d s : K) (t : Fin k → K), a * d - b * c' ≠ 0 ∧ s ≠ 0 ∧
      (∀ j, t j ≠ 0) ∧ pt (act i x) = s • lin a b c' d (pt x) ∧
      cfg (act i x) = (fun j => t j • lin a b c' d (cfg x (σ i j))) ∧
      s ^ 2 * (a * d - b * c') = c i x)
    (h : TrivLi K k m) :
    ∃ h : α → K, (∀ x, V x → h x ≠ 0) ∧ ∀ i x, V x → c i x ^ m = h (act i x) / h x := by
  obtain ⟨F, hF⟩ := h
  refine ⟨fun x => F (pt x) (cfg x), fun x hx => (hF _ _ (hconf x hx) (hpt x hx)).1,
    fun i x hx => ?_⟩
  obtain ⟨a, b, c', d, s, t, hd, hs, ht, hp, he, hc⟩ := hstep i x hx
  rw [eq_div_iff (hF _ _ (hconf x hx) (hpt x hx)).1]
  dsimp only
  rw [hp, he,
    trivLi_step hF (hconf x hx) (hpt x hx) _ hd hs ht, hc]

/-- `M_{0,5}` in the homogeneous model: the points `0, 1, ∞, λ, μ`. -/
def cfg5 (p : K × K) : Fin 5 → K × K := ![(0, 1), (1, 1), (1, 0), (p.1, 1), (p.2, 1)]

lemma conf_cfg5 {p : K × K} (hp : U5 p) : Conf (cfg5 p) := by
  obtain ⟨h0, h1, h0', h1', h⟩ := hp
  have : (1 : K) - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have : (1 : K) - p.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h1')
  have : p.1 - p.2 ≠ 0 := sub_ne_zero.2 h
  have : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have : p.2 - 1 ≠ 0 := sub_ne_zero.2 h1'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [cfg5, br, sub_eq_zero, eq_comm]

lemma step5 (i : Fin 4) {p : K × K} (hp : U5 p) : ∃ (a b c d : K) (t : Fin 5 → K),
    a * d - b * c ≠ 0 ∧ (∀ k, t k ≠ 0) ∧
    cfg5 (act5 i p) = (fun k => t k • lin a b c d (cfg5 p (Equiv.swap i.castSucc i.succ k))) ∧
    (∏ k, t k) ^ 2 * (a * d - b * c) ^ 5 = cL i p := by
  obtain ⟨h0, h1, h0', h1', h⟩ := hp
  have e1 : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have e1' : p.2 - 1 ≠ 0 := sub_ne_zero.2 h1'
  have e2 : 1 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e3 : p.2 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e3' : p.1 - p.2 ≠ 0 := sub_ne_zero.2 h
  fin_cases i
  · refine ⟨-1, 1, 0, 1, ![1, 1, -1, 1, 1], by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · funext k; fin_cases k <;> simp [cfg5, lin, act5, Equiv.swap_apply_def] <;> ring
    · simp [Fin.prod_univ_succ, cL]; norm_num
  · refine ⟨1, 0, 1, -1, ![-1, 1, 1, 1 / (p.1 - 1), 1 / (p.2 - 1)], by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [e1, e1']
    · funext k; fin_cases k <;> simp [cfg5, lin, act5, Equiv.swap_apply_def] <;>
        (try refine ⟨?_, ?_⟩) <;> (field_simp; try ring)
    · simp [Fin.prod_univ_succ, cL]; field_simp
  · refine ⟨1 - p.1, 0, 1, -p.1, ![-1 / p.1, 1 / (1 - p.1), 1 / (p.1 * (1 - p.1)), 1,
      1 / (p.2 - p.1)], ?_, ?_, ?_, ?_⟩
    · simp [h0, e2]
    · intro k; fin_cases k <;> simp [h0, e2, e3]
    · funext k; fin_cases k <;> simp [cfg5, lin, act5, Equiv.swap_apply_def] <;>
        (try refine ⟨?_, ?_⟩) <;> (field_simp; try ring)
    · simp [Fin.prod_univ_succ, cL]; field_simp; ring
  · refine ⟨1, 0, 0, 1, ![1, 1, 1, 1, 1], by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · funext k; fin_cases k <;> simp [cfg5, lin, act5, Equiv.swap_apply_def]
    · simp [Fin.prod_univ_succ, cL]

/-- **The two models agree for `L`, `n = 5`**: restricting a trivialisation of the homogeneous
model to `0, 1, ∞, λ, μ` trivialises the normalised cocycle `cL`. -/
theorem coboundary_cL_of_trivL {m : ℤ} (h : TrivL K 5 m) :
    ∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act5 cL w p ^ m = h (wAct act5 w p) / h p := by
  obtain ⟨h, hh, hc⟩ := cob_of_trivL cfg5 (fun i : Fin 4 => Equiv.swap i.castSucc i.succ)
    (fun p hp => conf_cfg5 hp) (fun i p hp => step5 i hp) h
  exact ⟨h, hh, wCoc_zpow (fun i p hp => act5_U5 i hp) hh hc⟩

theorem trivL_five_iff (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) (m : ℤ) :
    TrivL K 5 m ↔ ∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act5 cL w p ^ m = h (wAct act5 w p) / h p :=
  ⟨coboundary_cL_of_trivL, fun H => trivL_of_dvd (by simpa using (coboundary_cL_iff h2 hι m).1 H)⟩

/-- The four points `0, 1, ∞, λ` other than `μ`. -/
def pts4 (p : K × K) : Fin 4 → K × K := ![(0, 1), (1, 1), (1, 0), (p.1, 1)]

lemma conf_pts4 {p : K × K} (hp : U5 p) : Conf (pts4 p) ∧ ∀ i, br (p.2, 1) (pts4 p i) ≠ 0 := by
  obtain ⟨h0, h1, h0', h1', h⟩ := hp
  have : (1 : K) - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have : (1 : K) - p.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h1')
  have : p.1 - p.2 ≠ 0 := sub_ne_zero.2 h
  have : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have : p.2 - 1 ≠ 0 := sub_ne_zero.2 h1'
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [pts4, br, sub_eq_zero, eq_comm]
  · fin_cases i <;> simp_all [pts4, br, sub_eq_zero, eq_comm]

lemma step5i (i : Fin 3) {p : K × K} (hp : U5 p) : ∃ (a b c d s : K) (t : Fin 4 → K),
    a * d - b * c ≠ 0 ∧ s ≠ 0 ∧ (∀ k, t k ≠ 0) ∧
    ((act4 i p).2, (1 : K)) = s • lin a b c d (p.2, 1) ∧
    pts4 (act4 i p) = (fun k => t k • lin a b c d (pts4 p (Equiv.swap i.castSucc i.succ k))) ∧
    s ^ 2 * (a * d - b * c) = c5 i p := by
  obtain ⟨h0, h1, h0', h1', h⟩ := hp
  have e1 : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have e1' : p.2 - 1 ≠ 0 := sub_ne_zero.2 h1'
  have e2 : 1 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e3 : p.2 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e3' : p.1 - p.2 ≠ 0 := sub_ne_zero.2 h
  fin_cases i
  · refine ⟨-1, 1, 0, 1, 1, ![1, 1, -1, 1], by norm_num, one_ne_zero, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · simp [act4, act5, lin]; ring
    · funext k; fin_cases k <;> (simp [pts4, lin, act4, act5, Equiv.swap_apply_def]; try ring)
    · simp [c5]
  · refine ⟨1, 0, 1, -1, 1 / (p.2 - 1), ![-1, 1, 1, 1 / (p.1 - 1)], by norm_num, by simp [e1'],
      ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [e1]
    · simp [act4, act5, lin]; refine ⟨?_, ?_⟩ <;> (field_simp; try ring)
    · funext k
      fin_cases k <;> (simp [pts4, lin, act4, act5, Equiv.swap_apply_def]
                       try field_ring)
    · simp [c5]; field_simp
  · refine ⟨1 - p.1, 0, 1, -p.1, 1 / (p.2 - p.1), ![-1 / p.1, 1 / (1 - p.1),
      1 / (p.1 * (1 - p.1)), 1], by simp [h0, e2], by simp [e3], ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [h0, e2]
    · simp [act4, act5, lin]; refine ⟨?_, ?_⟩ <;> (field_simp; try ring)
    · funext k; fin_cases k <;> simp [pts4, lin, act4, act5, Equiv.swap_apply_def] <;>
        (try refine ⟨?_, ?_⟩) <;> (field_simp; try ring)
    · simp [c5]; field_simp; ring

/-- **The two models agree for `L₅`, `n = 5`**: restricting a trivialisation of `L₅^{⊗m}` in
the homogeneous model trivialises the normalised cocycle `c5`. -/
theorem coboundary_c5_of_trivLi {m : ℤ} (h : TrivLi K 4 m) :
    ∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act4 c5 w p ^ m = h (wAct act4 w p) / h p := by
  obtain ⟨h, hh, hc⟩ := cob_of_trivLi (fun p : K × K => (p.2, (1 : K))) pts4
    (fun i : Fin 3 => Equiv.swap i.castSucc i.succ) (fun p hp => (conf_pts4 hp).1)
    (fun p hp => (conf_pts4 hp).2) (fun i p hp => step5i i hp) h
  exact ⟨h, hh, wCoc_zpow (fun i p hp => act5_U5 i.castSucc hp) hh hc⟩

theorem trivLi_five_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1)
    {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) :
    TrivLi K 4 m ↔ ∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act4 c5 w p ^ m = h (wAct act4 w p) / h p :=
  ⟨coboundary_c5_of_trivLi, fun H =>
    trivLi_of_dvd (by simpa using (coboundary_c5_iff h2 h3 hι hζ m).1 H)⟩

/-- `M_{0,6}` in the homogeneous model: the points `0, 1, ∞, λ, μ, ν`. -/
def cfg6 (p : K × K × K) : Fin 6 → K × K :=
  ![(0, 1), (1, 1), (1, 0), (p.1, 1), (p.2.1, 1), (p.2.2, 1)]

/-- The five points other than `ν`. -/
def pts5 (p : K × K × K) : Fin 5 → K × K := ![(0, 1), (1, 1), (1, 0), (p.1, 1), (p.2.1, 1)]

lemma conf_cfg6 {p : K × K × K} (hp : U6 p) :
    Conf (cfg6 p) ∧ Conf (pts5 p) ∧ ∀ i, br (p.2.2, 1) (pts5 p i) ≠ 0 := by
  obtain ⟨⟨h0, h1, h0', h1', h⟩, ⟨-, -, h0'', h1'', h'⟩, h''⟩ := hp
  dsimp only at *
  have : (1 : K) - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have : (1 : K) - p.2.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1')
  have : (1 : K) - p.2.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h1'')
  have : p.1 - p.2.1 ≠ 0 := sub_ne_zero.2 h
  have : p.1 - p.2.2 ≠ 0 := sub_ne_zero.2 h'
  have : p.2.1 - p.2.2 ≠ 0 := sub_ne_zero.2 h''
  have : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have : p.2.1 - 1 ≠ 0 := sub_ne_zero.2 h1'
  have : p.2.2 - 1 ≠ 0 := sub_ne_zero.2 h1''
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [cfg6, br, sub_eq_zero, eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [pts5, br, sub_eq_zero, eq_comm]
  · fin_cases i <;> simp_all [pts5, br, sub_eq_zero, eq_comm]

lemma step6 (i : Fin 5) {p : K × K × K} (hp : U6 p) : ∃ (a b c d : K) (t : Fin 6 → K),
    a * d - b * c ≠ 0 ∧ (∀ k, t k ≠ 0) ∧
    cfg6 (act6 i p) = (fun k => t k • lin a b c d (cfg6 p (Equiv.swap i.castSucc i.succ k))) ∧
    (∏ k, t k) ^ 2 * (a * d - b * c) ^ 6 = cL6 i p := by
  obtain ⟨⟨h0, h1, h0', h1', h⟩, ⟨-, -, h0'', h1'', h'⟩, h''⟩ := hp
  dsimp only at *
  have e1 : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have e1' : p.2.1 - 1 ≠ 0 := sub_ne_zero.2 h1'
  have e1'' : p.2.2 - 1 ≠ 0 := sub_ne_zero.2 h1''
  have e2 : 1 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e3 : p.2.1 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e3' : p.1 - p.2.1 ≠ 0 := sub_ne_zero.2 h
  have e4 : p.2.2 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h')
  have e4' : p.1 - p.2.2 ≠ 0 := sub_ne_zero.2 h'
  fin_cases i
  · refine ⟨-1, 1, 0, 1, ![1, 1, -1, 1, 1, 1], by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · funext k
      fin_cases k <;> (simp [cfg6, lin, act6, Equiv.swap_apply_def]; try ring)
    · simp [Fin.prod_univ_succ, cL6]; norm_num
  · refine ⟨1, 0, 1, -1, ![-1, 1, 1, 1 / (p.1 - 1), 1 / (p.2.1 - 1), 1 / (p.2.2 - 1)],
      by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [e1, e1', e1'']
    · funext k
      fin_cases k <;> (simp [cfg6, lin, act6, Equiv.swap_apply_def]
                       try field_ring)
    · simp [Fin.prod_univ_succ, cL6]; field_simp
  · refine ⟨1 - p.1, 0, 1, -p.1, ![-1 / p.1, 1 / (1 - p.1), 1 / (p.1 * (1 - p.1)), 1,
      1 / (p.2.1 - p.1), 1 / (p.2.2 - p.1)], by simp [h0, e2], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [h0, e2, e3, e4]
    · funext k
      fin_cases k <;> (simp [cfg6, lin, act6, Equiv.swap_apply_def]
                       try field_ring)
    · simp [Fin.prod_univ_succ, cL6]; field_simp; ring
  · refine ⟨1, 0, 0, 1, ![1, 1, 1, 1, 1, 1], by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · funext k; fin_cases k <;> simp [cfg6, lin, act6, Equiv.swap_apply_def]
    · simp [Fin.prod_univ_succ, cL6]
  · refine ⟨1, 0, 0, 1, ![1, 1, 1, 1, 1, 1], by norm_num, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · funext k; fin_cases k <;> simp [cfg6, lin, act6, Equiv.swap_apply_def]
    · simp [Fin.prod_univ_succ, cL6]

lemma step6i (i : Fin 4) {p : K × K × K} (hp : U6 p) : ∃ (a b c d s : K) (t : Fin 5 → K),
    a * d - b * c ≠ 0 ∧ s ≠ 0 ∧ (∀ k, t k ≠ 0) ∧
    ((act6s i p).2.2, (1 : K)) = s • lin a b c d (p.2.2, 1) ∧
    pts5 (act6s i p) = (fun k => t k • lin a b c d (pts5 p (Equiv.swap i.castSucc i.succ k))) ∧
    s ^ 2 * (a * d - b * c) = c6 i p := by
  obtain ⟨⟨h0, h1, h0', h1', h⟩, ⟨-, -, h0'', h1'', h'⟩, h''⟩ := hp
  dsimp only at *
  have e1 : p.1 - 1 ≠ 0 := sub_ne_zero.2 h1
  have e1' : p.2.1 - 1 ≠ 0 := sub_ne_zero.2 h1'
  have e1'' : p.2.2 - 1 ≠ 0 := sub_ne_zero.2 h1''
  have e2 : 1 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e3 : p.2.1 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e3' : p.1 - p.2.1 ≠ 0 := sub_ne_zero.2 h
  have e4 : p.2.2 - p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h')
  have e4' : p.1 - p.2.2 ≠ 0 := sub_ne_zero.2 h'
  fin_cases i
  · refine ⟨-1, 1, 0, 1, 1, ![1, 1, -1, 1, 1], by norm_num, one_ne_zero, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · simp [act6s, act6, lin]; ring
    · funext k
      fin_cases k <;> (simp [pts5, lin, act6s, act6, Equiv.swap_apply_def]; try ring)
    · simp [c6]
  · refine ⟨1, 0, 1, -1, 1 / (p.2.2 - 1), ![-1, 1, 1, 1 / (p.1 - 1), 1 / (p.2.1 - 1)],
      by norm_num, by simp [e1''], ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [e1, e1']
    · simp [act6s, act6, lin]; refine ⟨?_, ?_⟩ <;> (field_simp; try ring)
    · funext k
      fin_cases k <;> (simp [pts5, lin, act6s, act6, Equiv.swap_apply_def]
                       try field_ring)
    · simp [c6]; field_simp
  · refine ⟨1 - p.1, 0, 1, -p.1, 1 / (p.2.2 - p.1), ![-1 / p.1, 1 / (1 - p.1),
      1 / (p.1 * (1 - p.1)), 1, 1 / (p.2.1 - p.1)], by simp [h0, e2], by simp [e4], ?_, ?_,
      ?_, ?_⟩
    · intro k; fin_cases k <;> simp [h0, e2, e3]
    · simp [act6s, act6, lin]; refine ⟨?_, ?_⟩ <;> (field_simp; try ring)
    · funext k
      fin_cases k <;> (simp [pts5, lin, act6s, act6, Equiv.swap_apply_def]
                       try field_ring)
    · simp [c6]; field_simp; ring
  · refine ⟨1, 0, 0, 1, 1, ![1, 1, 1, 1, 1], by norm_num, one_ne_zero, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp
    · simp [act6s, act6, lin]
    · funext k; fin_cases k <;> simp [pts5, lin, act6s, act6, Equiv.swap_apply_def]
    · simp [c6]

/-- **The two models agree for `L`, `n = 6`.** -/
theorem coboundary_cL6_of_trivL {m : ℤ} (h : TrivL K 6 m) :
    ∃ h : K × K × K → K, (∀ p, U6 p → h p ≠ 0) ∧
      ∀ w p, U6 p → wCoc act6 cL6 w p ^ m = h (wAct act6 w p) / h p := by
  obtain ⟨h, hh, hc⟩ := cob_of_trivL cfg6 (fun i : Fin 5 => Equiv.swap i.castSucc i.succ)
    (fun p hp => (conf_cfg6 hp).1) (fun i p hp => step6 i hp) h
  exact ⟨h, hh, wCoc_zpow (fun i p hp => act6_U6 i hp) hh hc⟩

theorem trivL_six_iff (h5 : (5 : K) ≠ 0) {ω : K} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (m : ℤ) : TrivL K 6 m ↔ ∃ h : K × K × K → K, (∀ p, U6 p → h p ≠ 0) ∧
      ∀ w p, U6 p → wCoc act6 cL6 w p ^ m = h (wAct act6 w p) / h p :=
  ⟨coboundary_cL6_of_trivL, fun H =>
    trivL_of_dvd (by simpa using (coboundary_cL6_iff h5 hω m).1 H)⟩

/-- **The two models agree for `L₆`, `n = 6`.** -/
theorem coboundary_c6_of_trivLi {m : ℤ} (h : TrivLi K 5 m) :
    ∃ h : K × K × K → K, (∀ p, U6 p → h p ≠ 0) ∧
      ∀ w p, U6 p → wCoc act6s c6 w p ^ m = h (wAct act6s w p) / h p := by
  obtain ⟨h, hh, hc⟩ := cob_of_trivLi (fun p : K × K × K => (p.2.2, (1 : K))) pts5
    (fun i : Fin 4 => Equiv.swap i.castSucc i.succ) (fun p hp => (conf_cfg6 hp).2.1)
    (fun p hp => (conf_cfg6 hp).2.2) (fun i p hp => step6i i hp) h
  exact ⟨h, hh, wCoc_zpow (fun i p hp => act6_U6 i.castSucc hp) hh hc⟩

theorem trivLi_six_iff (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1)
    {ω : K} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (m : ℤ) :
    TrivLi K 5 m ↔ ∃ h : K × K × K → K, (∀ p, U6 p → h p ≠ 0) ∧
      ∀ w p, U6 p → wCoc act6s c6 w p ^ m = h (wAct act6s w p) / h p :=
  ⟨coboundary_c6_of_trivLi, fun H =>
    trivLi_of_dvd (by simpa using (coboundary_c6_iff h2 h5 hι hω m).1 H)⟩

/-- `M_{0,4}` in the homogeneous model: the points `0, 1, ∞, λ`. -/
def cfg4 (x : K) : Fin 4 → K × K := ![(0, 1), (1, 1), (1, 0), (x, 1)]

/-- The three fixed points `0, 1, ∞`. -/
def pts3 : Fin 3 → K × K := ![(0, 1), (1, 1), (1, 0)]

/-- The relabelling of `0, 1, ∞` by the six substitutions. -/
def perm4 {n : ℕ} : Fin 6 → Equiv.Perm (Fin (n + 3))
  | 0 => 1
  | 1 => Equiv.swap 0 2
  | 2 => Equiv.swap 0 1
  | 3 => Equiv.swap 1 2
  | 4 => Equiv.swap 0 1 * Equiv.swap 0 2
  | 5 => Equiv.swap 0 2 * Equiv.swap 0 1

/-- The substitutions as matrices `(a, b, c, d)`. -/
def mat4 : Fin 6 → K × K × K × K
  | 0 => (1, 0, 0, 1)
  | 1 => (0, 1, 1, 0)
  | 2 => (-1, 1, 0, 1)
  | 3 => (1, 0, 1, -1)
  | 4 => (0, 1, -1, 1)
  | 5 => (1, -1, 1, 0)

/-- The rescalings at `0, 1, ∞, λ`. -/
def t4 : Fin 6 → K → Fin 4 → K
  | 0 => fun _ => ![1, 1, 1, 1]
  | 1 => fun x => ![1, 1, 1, 1 / x]
  | 2 => fun _ => ![1, 1, -1, 1]
  | 3 => fun x => ![-1, 1, 1, 1 / (x - 1)]
  | 4 => fun x => ![-1, 1, 1, 1 / (1 - x)]
  | 5 => fun x => ![1, 1, -1, 1 / x]

lemma conf_cfg4 {x : K} (hx : U x) :
    Conf (cfg4 x) ∧ Conf (pts3 (K := K)) ∧ ∀ i, br (x, 1) (pts3 i) ≠ 0 := by
  obtain ⟨h0, h1⟩ := hx
  have : (1 : K) - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have : x - 1 ≠ 0 := sub_ne_zero.2 h1
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [cfg4, br, eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [pts3, br]
  · fin_cases i <;> simp_all [pts3, br, eq_comm]

lemma step4 (a : Fin 6) {x : K} (hx : U x) :
    (mat4 (K := K) a).1 * (mat4 a).2.2.2 - (mat4 a).2.1 * (mat4 a).2.2.1 ≠ 0 ∧ (∀ k, t4 a x k ≠ 0) ∧
    cfg4 (anh a x) = (fun k => t4 a x k •
      lin (mat4 a).1 (mat4 a).2.1 (mat4 a).2.2.1 (mat4 a).2.2.2 (cfg4 x (perm4 a k))) ∧
    (pts3 : Fin 3 → K × K) = (fun k => t4 a x k.castSucc •
      lin (mat4 a).1 (mat4 a).2.1 (mat4 a).2.2.1 (mat4 a).2.2.2 (pts3 (perm4 a k))) ∧
    (∏ k, t4 a x k) ^ 2 *
      ((mat4 a).1 * (mat4 a).2.2.2 - (mat4 a).2.1 * (mat4 a).2.2.1) ^ 4 = derL a x ∧
    t4 a x 3 ^ 2 * ((mat4 a).1 * (mat4 a).2.2.2 - (mat4 a).2.1 * (mat4 a).2.2.1) =
      der a x := by
  obtain ⟨h0, h1⟩ := hx
  have e1 : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have e2 : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> refine ⟨by simp [mat4], fun k => by fin_cases k <;> simp [t4, h0, e1, e2],
    funext fun k => ?_, funext fun k => ?_, ?_, ?_⟩
  all_goals first
    | (fin_cases k <;> (simp [mat4, t4, cfg4, pts3, perm4, lin, anh, Equiv.swap_apply_def]
                        try field_ring))
    | (simp [mat4, t4, der, derL, sgn, Fin.prod_univ_succ]; try field_ring)

/-- **The two models agree for `L`, `n = 4`**: restricting a trivialisation of the homogeneous
model to `0, 1, ∞, λ` trivialises the cocycle `derL` of the anharmonic group. -/
theorem coboundary_derL_of_trivL {m : ℤ} (h : TrivL K 4 m) :
    ∃ h : K → K, (∀ x, U x → h x ≠ 0) ∧ ∀ a x, U x → derL a x ^ m = h (anh a x) / h x :=
  cob_of_trivL cfg4 perm4 (fun x hx => (conf_cfg4 hx).1) (fun a x hx => by
    obtain ⟨hd, ht, hv, -, hL, -⟩ := step4 a hx
    exact ⟨_, _, _, _, _, hd, ht, hv, hL⟩) h

theorem trivL_four_iff (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) :
    TrivL K 4 m ↔
      ∃ h : K → K, (∀ x, U x → h x ≠ 0) ∧ ∀ a x, U x → derL a x ^ m = h (anh a x) / h x :=
  ⟨coboundary_derL_of_trivL, fun H =>
    trivL_of_dvd (by simpa using (coboundary_derL_iff h3 hζ m).1 H)⟩

/-- **The two models agree for `L₄`, `n = 4`**: the cocycle `der` (`g ↦ g′(λ)`). -/
theorem coboundary_der_of_trivLi {m : ℤ} (h : TrivLi K 3 m) :
    ∃ h : K → K, (∀ x, U x → h x ≠ 0) ∧ ∀ a x, U x → der a x ^ m = h (anh a x) / h x :=
  cob_of_trivLi (fun x : K => (x, (1 : K))) (fun _ => pts3) perm4
    (fun x hx => (conf_cfg4 hx).2.1) (fun x hx => (conf_cfg4 hx).2.2) (fun a x hx => by
      obtain ⟨hd, ht, hv, hw, -, hs⟩ := step4 a hx
      refine ⟨_, _, _, _, _, _, hd, ht 3, fun k => ht _, ?_, hw, hs⟩
      have h3 : perm4 a (3 : Fin 4) = 3 := by fin_cases a <;> rfl
      simpa [cfg4, h3] using congrFun hv 3) h

theorem trivLi_four_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ζ : K}
    (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) : TrivLi K 3 m ↔
      ∃ h : K → K, (∀ x, U x → h x ≠ 0) ∧ ∀ a x, U x → der a x ^ m = h (anh a x) / h x :=
  ⟨coboundary_der_of_trivLi, fun ⟨h, hh, hc⟩ =>
    trivLi_of_dvd (by simpa using six_dvd h2 h3 hζ m h hh hc)⟩


/-! ## The Coxeter relations of `𝔖₅` and `𝔖₆`

The sections on `n = 5` and `n = 6` give the substitutions and their factors on the adjacent
transpositions only, and work with words (`wAct`, `wCoc`). They satisfy the Coxeter relations of
type `A`: `s_i² = 1`, `s_i s_j s_i = s_j s_i s_j` for `|i − j| = 1` and `s_i s_j = s_j s_i` for
`|i − j| ≥ 2`, both for the substitution and for the factor composed by the cocycle rule
(`CoxRel`; `coxRel_cL`, `coxRel_c5`, `coxRel_cL6`, `coxRel_c6`). So the maps
`(x, t) ↦ (s x, c(s)(x) t)` of the trivial line bundle over `M_{0,n}(K)` define an action of the
Coxeter group of type `A_{n−1}` (`CoxRel.lift`, Mathlib's `CoxeterSystem.lift`), and the
substitution and the factor of a word depend only on its image in that group
(`CoxRel.wAct_eq`), on every field. That the Coxeter group of type `A_{n−1}` is `𝔖_n` is
classical; Mathlib does not state it. -/

/-- The Coxeter relations of type `A_n` for substitutions `act` of `V` and factors `c`, on the
generators: `s_i² = 1`, the braid relation for `j + 1 = i` and commutation for `j + 1 < i`,
each for the substitution and for the factor by the cocycle rule. -/
structure CoxRel {α : Type*} (n : ℕ) (V : α → Prop) (act : Fin n → α → α) (c : Fin n → α → K) :
    Prop where
  maps : ∀ i x, V x → V (act i x)
  sq : ∀ i x, V x → act i (act i x) = x ∧ c i (act i x) * c i x = 1
  braid : ∀ i j : Fin n, (j : ℕ) + 1 = i → ∀ x, V x →
    act i (act j (act i x)) = act j (act i (act j x)) ∧
      c i (act j (act i x)) * c j (act i x) * c i x = c j (act i (act j x)) * c i (act j x) * c j x
  comm : ∀ i j : Fin n, (j : ℕ) + 1 < i → ∀ x, V x →
    act i (act j x) = act j (act i x) ∧ c i (act j x) * c j x = c j (act i x) * c i x

variable {α : Type*} {n : ℕ} {V : α → Prop} {act : Fin n → α → α} {c : Fin n → α → K}

/-- The generator `s_i` on the trivial line bundle over `V`: `(x, t) ↦ (s_i x, c(s_i)(x) t)`. -/
def bun (hV : ∀ i x, V x → V (act i x)) (c : Fin n → α → K) (i : Fin n) :
    Function.End ({x // V x} × K) :=
  fun q => (⟨act i q.1, hV i _ q.1.2⟩, c i q.1 * q.2)

/-- The maps `bun` satisfy the relations `(s_i s_j)^{m_{ij}} = 1` of the Coxeter matrix of
type `A_n` (`m_{ii} = 1`, `m_{ij} = 3` for `|i − j| = 1`, `2` otherwise). -/
theorem CoxRel.isLiftable (h : CoxRel n V act c) :
    (CoxeterMatrix.A n).IsLiftable (bun h.maps c) := by
  have sq i : bun h.maps c i * bun h.maps c i = 1 := funext fun ⟨⟨x, hx⟩, t⟩ =>
    Prod.ext (Subtype.ext (h.sq i x hx).1) (by
      change c i (act i x) * (c i x * t) = t; linear_combination t * (h.sq i x hx).2)
  have br {i j : Fin n} (hij : (j : ℕ) + 1 = i) : bun h.maps c i * (bun h.maps c j *
      bun h.maps c i) = bun h.maps c j * (bun h.maps c i * bun h.maps c j) :=
    funext fun ⟨⟨x, hx⟩, t⟩ => Prod.ext (Subtype.ext (h.braid i j hij x hx).1) (by
      change c i (act j (act i x)) * (c j (act i x) * (c i x * t)) =
        c j (act i (act j x)) * (c i (act j x) * (c j x * t))
      linear_combination t * (h.braid i j hij x hx).2)
  have cm {i j : Fin n} (hij : (j : ℕ) + 1 < i) : bun h.maps c i * bun h.maps c j =
      bun h.maps c j * bun h.maps c i := funext fun ⟨⟨x, hx⟩, t⟩ =>
    Prod.ext (Subtype.ext (h.comm i j hij x hx).1) (by
      change c i (act j x) * (c j x * t) = c j (act i x) * (c i x * t)
      linear_combination t * (h.comm i j hij x hx).2)
  have can {a : Function.End ({x // V x} × K)} (ha : a * a = 1) X : a * (a * X) = X := by
    rw [← mul_assoc, ha, one_mul]
  have three {a b : Function.End ({x // V x} × K)} (ha : a * a = 1) (hb : b * b = 1)
      (e : a * (b * a) = b * (a * b)) : (a * b) ^ 3 = 1 :=
    calc (a * b) ^ 3 = a * (b * a) * (b * (a * b)) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [e]; simp only [mul_assoc, can ha, can hb, hb]
  have two {a b : Function.End ({x // V x} × K)} (ha : a * a = 1) (hb : b * b = 1)
      (e : a * b = b * a) : (a * b) ^ 2 = 1 :=
    calc (a * b) ^ 2 = a * (b * a) * b := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [← e]; simp only [can ha, hb]
  intro i j
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs with h1 h2
  · subst h1; rw [pow_one, sq]
  · rcases h2 with h2 | h2
    · exact three (sq i) (sq j) (br h2)
    · exact three (sq i) (sq j) (br h2).symm
  · rcases lt_or_gt_of_ne (show (j : ℕ) ≠ i from fun e => h1 (Fin.ext e.symm)) with h3 | h3
    · exact two (sq i) (sq j) (cm (by omega))
    · exact two (sq i) (sq j) (cm (by omega)).symm

/-- The action of the Coxeter group of type `A_n` on the trivial line bundle over `V`. -/
def CoxRel.lift (h : CoxRel n V act c) :
    (CoxeterMatrix.A n).Group →* Function.End ({x // V x} × K) :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift ⟨_, h.isLiftable⟩

/-- A word acts by its substitution and its factor. -/
theorem CoxRel.lift_word (h : CoxRel n V act c) (w : List (Fin n)) (x : {x // V x}) (t : K) :
    (h.lift (w.map (CoxeterMatrix.A n).toCoxeterSystem.simple).prod (x, t)).1.1 =
        wAct act w x ∧
      (h.lift (w.map (CoxeterMatrix.A n).toCoxeterSystem.simple).prod (x, t)).2 =
        wCoc act c w x * t := by
  induction w with
  | nil => exact ⟨rfl, (one_mul t).symm⟩
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, map_mul, CoxRel.lift, CoxeterSystem.lift_apply_simple]
    exact ⟨congrArg (act i) ih.1, by simp only [wCoc, ← ih.1, ← ih.2, mul_assoc]; rfl⟩

/-- **The words pass to the group**: two words with the same image in the Coxeter group of
type `A_n` have the same substitution and the same factor. -/
theorem CoxRel.wAct_eq (h : CoxRel n V act c) {w w' : List (Fin n)}
    (e : (w.map (CoxeterMatrix.A n).toCoxeterSystem.simple).prod =
      (w'.map (CoxeterMatrix.A n).toCoxeterSystem.simple).prod) {x : α} (hx : V x) :
    wAct act w x = wAct act w' x ∧ wCoc act c w x = wCoc act c w' x := by
  have h1 := h.lift_word w ⟨x, hx⟩ 1
  have h2 := h.lift_word w' ⟨x, hx⟩ 1
  rw [e] at h1
  exact ⟨h1.1.symm.trans h2.1, by simpa using h1.2.symm.trans h2.2⟩

lemma U5_ne {p : K × K} (h : U5 p) : p.1 ≠ 0 ∧ p.1 - 1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 - 1 ≠ 0 ∧
    p.1 - p.2 ≠ 0 :=
  ⟨h.1, sub_ne_zero.2 h.2.1, h.2.2.1, sub_ne_zero.2 h.2.2.2.1, sub_ne_zero.2 h.2.2.2.2⟩

lemma U6_ne {p : K × K × K} (h : U6 p) : p.1 ≠ 0 ∧ p.1 - 1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.1 - 1 ≠ 0 ∧
    p.1 - p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2 - 1 ≠ 0 ∧ p.1 - p.2.2 ≠ 0 ∧ p.2.1 - p.2.2 ≠ 0 :=
  ⟨h.1.1, sub_ne_zero.2 h.1.2.1, h.1.2.2.1, sub_ne_zero.2 h.1.2.2.2.1,
    sub_ne_zero.2 h.1.2.2.2.2, h.2.1.2.2.1, sub_ne_zero.2 h.2.1.2.2.2.1,
    sub_ne_zero.2 h.2.1.2.2.2.2, sub_ne_zero.2 h.2.2⟩

lemma act4_U5 (i : Fin 3) {p : K × K} (hp : U5 p) : U5 (act4 i p) := act5_U5 _ hp

lemma act6s_U6 (i : Fin 4) {p : K × K × K} (hp : U6 p) : U6 (act6s i p) := act6_U6 _ hp

section

attribute [local simp] act5 cL act4 c5 act6 cL6 act6s c6

/-- Closes the components left once all intermediate points are substituted. -/
macro "cox_close" : tactic => `(tactic| (split_ands <;> first | trivial | ring))

set_option hygiene false in
/-- Checks `s_i² = 1`: the intermediate point is a variable `q`, the denominators are cleared
in `q`, then `q` is substituted and they are cleared in `x`. -/
macro "cox_sq " act:ident hU:ident hne:ident : tactic => `(tactic| (
  have h1 := $hU i hx
  generalize e1 : $act i x = q at *
  have := $hne hx; have := $hne h1
  casesm* _ ∧ _
  fin_cases i <;> simp [Prod.ext_iff] <;> (try field_simp) <;> simp at e1 <;> subst e1 <;>
    dsimp only <;> (try field_simp) <;> cox_close))

set_option hygiene false in
/-- Checks the braid relation, one level of intermediate points at a time. -/
macro "cox_braid " act:ident hU:ident hne:ident : tactic => `(tactic| (
  have h1 := $hU i hx; have h2 := $hU j h1; have h3 := $hU j hx; have h4 := $hU i h3
  generalize e1 : $act i x = q at *; generalize e2 : $act j q = r at *
  generalize e3 : $act j x = q' at *; generalize e4 : $act i q' = r' at *
  have := $hne hx; have := $hne h1; have := $hne h2; have := $hne h3; have := $hne h4
  casesm* _ ∧ _
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [Prod.ext_iff] <;> (try field_simp) <;>
    simp at e2 e4 <;> subst e2 e4 <;> dsimp only <;> (try field_simp) <;>
    simp at e1 e3 <;> subst e1 e3 <;> dsimp only <;> (try field_simp) <;> cox_close))

set_option hygiene false in
/-- Checks the commutation of distant generators. -/
macro "cox_comm " act:ident hU:ident hne:ident : tactic => `(tactic| (
  have h1 := $hU j hx; have h3 := $hU i hx
  generalize e1 : $act j x = q at *; generalize e3 : $act i x = q' at *
  have := $hne hx; have := $hne h1; have := $hne h3
  casesm* _ ∧ _
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [Prod.ext_iff] <;> (try field_simp) <;>
    simp at e1 e3 <;> subst e1 e3 <;> dsimp only <;> (try field_simp) <;> cox_close))

/-- **The Coxeter relations of `𝔖₅`** for the substitutions `act5` and the factors `cL` of
`L`, checked with the intermediate points as variables, clearing the denominators one level at
a time. -/
theorem coxRel_cL : CoxRel 4 U5 (act5 (K := K)) cL where
  maps i _ := act5_U5 i
  sq i x hx := by cox_sq act5 act5_U5 U5_ne
  braid i j hij x hx := by cox_braid act5 act5_U5 U5_ne
  comm i j hij x hx := by cox_comm act5 act5_U5 U5_ne

/-- **The Coxeter relations of `𝔖₄`** for `s₁, s₂, s₃` and the factors `c5` of `L₅`. -/
theorem coxRel_c5 : CoxRel 3 U5 (act4 (K := K)) c5 where
  maps i _ := act4_U5 i
  sq i x hx := by cox_sq act4 act4_U5 U5_ne
  braid i j hij x hx := by cox_braid act4 act4_U5 U5_ne
  comm i j hij x hx := by cox_comm act4 act4_U5 U5_ne

/-- **The Coxeter relations of `𝔖₆`** for the substitutions `act6` and the factors `cL6`. -/
theorem coxRel_cL6 : CoxRel 5 U6 (act6 (K := K)) cL6 where
  maps i _ := act6_U6 i
  sq i x hx := by cox_sq act6 act6_U6 U6_ne
  braid i j hij x hx := by cox_braid act6 act6_U6 U6_ne
  comm i j hij x hx := by cox_comm act6 act6_U6 U6_ne

/-- **The Coxeter relations of `𝔖₅`** for `s₁, …, s₄` on `M_{0,6}` and the factors `c6` of
`L₆`. -/
theorem coxRel_c6 : CoxRel 4 U6 (act6s (K := K)) c6 where
  maps i _ := act6s_U6 i
  sq i x hx := by cox_sq act6s act6s_U6 U6_ne
  braid i j hij x hx := by cox_braid act6s act6s_U6 U6_ne
  comm i j hij x hx := by cox_comm act6s act6s_U6 U6_ne

end

end Grothendieck.Folder146
