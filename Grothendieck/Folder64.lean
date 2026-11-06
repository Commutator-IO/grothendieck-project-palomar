module

public import Mathlib

public section


/-!
# Folder 64, pages 48–51: the octahedral configuration in characteristic 5

The modernised reading `transcripts/64/64.modern.tex` (part II, § 1, « Actions du groupe de
Klein, configuration octaédrale ») puts a faithful action of the Klein group on `ℙ¹` in the
normal form `σ₁(z) = −z`, `σ₂(z) = 1/z` and calls `Δ = {0, ∞, ±1, ±i}` the octahedral
configuration. To identify `Aut(X, Δ)` with the octahedral rotation group, page 48 computes
the fixer of the two non-opposite vertices `∞` and `−1`: such an automorphism is
`z ↦ a z + (a − 1)`, and if it is not the identity it permutes `{0, 1, i, −i}`; the four
resulting conditions on `a` « have empty intersection if the characteristic is `≠ 2, 5` ».
The margin bounds the computation by « car. ≠ 3 et 5 », and the reading adds « 5 invertible »
wherever the identification `Aut(X, Δ) ≃ 𝔖₄` is used: over `𝔽₅` the configuration is all of
`ℙ¹(𝔽₅)`. This is the reachable part of finding `64-octahedral-configurations-relative` of
`src/content/findings.ts`.

* `fixer_five`: over a field with `i² = −1` and `2 ≠ 0`, if `z ↦ a z + (a − 1)` maps
  `{0, 1, i, −i}` into itself then `5 (a − 1) = 0`. The map is then a bijection of the four
  points, whose sum is `1`, and it changes that sum into `5a − 4`.
* `fixer_trivial`: hence `a = 1` once `5 ≠ 0` — the page's claim, with characteristic `3`
  needing no special case.
* `fixer_nontrivial_char5`: in characteristic `5` the map `z ↦ 2z + 1` permutes
  `{0, 1, i, −i}`, so the fixer of `∞` and `−1` is not trivial.
* Over `𝔽₅`, with `i = 2` (`two_sq`) and Möbius maps given by their matrices:
  `octahedral_eq_univ`, the configuration is all of `ℙ¹(𝔽₅)`; `perm_octa`, every invertible
  matrix permutes it; `card_pgl`, the induced bijections — `PGL₂(𝔽₅)`, all of which preserve
  `Δ` — are `120`, not `24`; `card_fixer`, the fixer of `∞` and `−1` among them is the identity
  and `z ↦ a z + (a − 1)` for `a = 2, 3, 4` (the common part `{2, 3, 4}` of the reading's
  footnote).

Not formalised: the relative statements over a base `S`, the bijections of the Théorème of
page 51 and the two corollaries of page 52.

The finite checks over `𝔽₅` use `decide +kernel`, which the kernel checks.
-/

namespace Grothendieck.Folder64

open Finset

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- The four vertices other than `∞` and `−1`. -/
def quad (i : K) : Finset K := {0, 1, i, -i}

variable {i : K}

omit [DecidableEq K] in
lemma quad_facts (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    i ≠ 0 ∧ i ≠ 1 ∧ i ≠ -1 ∧ (1 : K) ≠ -1 :=
  ⟨fun h => h2 (by linear_combination 2 * hi - 2 * i * h),
    fun h => h2 (by linear_combination hi - (1 + i) * h),
    fun h => h2 (by linear_combination hi + (1 - i) * h), fun h => h2 (by linear_combination h)⟩

lemma quad_distinct (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    (0 : K) ∉ ({1, i, -i} : Finset K) ∧ (1 : K) ∉ ({i, -i} : Finset K) ∧ i ≠ -i := by
  obtain ⟨h0, h1, hm, -⟩ := quad_facts hi h2
  have f1 : (1 : K) ≠ -i := fun h => hm (by linear_combination h)
  have f2 : (0 : K) ≠ -i := fun h => h0 (by linear_combination h)
  have hii : i ≠ -i := fun h => h2 (by linear_combination 2 * hi - i * h)
  simp [f1, f2, h0.symm, h1.symm, hii]

lemma card_quad (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) : (quad i).card = 4 := by
  obtain ⟨n0, n1, hii⟩ := quad_distinct hi h2
  rw [quad, card_insert_of_notMem n0, card_insert_of_notMem n1, card_pair hii]

lemma quad_sum (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) : ∑ z ∈ quad i, z = 1 := by
  obtain ⟨n0, n1, hii⟩ := quad_distinct hi h2
  rw [quad, sum_insert n0, sum_insert n1, sum_pair hii]
  ring

/-- Page 48: an automorphism fixing `∞` and `−1` is `z ↦ a z + (a − 1)`; if it maps
`{0, 1, i, −i}` into itself, then `5 (a − 1) = 0`. -/
theorem fixer_five (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (a : K)
    (h : ∀ z ∈ quad i, a * z + (a - 1) ∈ quad i) : (5 : K) * (a - 1) = 0 := by
  obtain ⟨h0, h1, hm, h11⟩ := quad_facts hi h2
  rcases eq_or_ne a 0 with rfl | ha
  · exact absurd (h 0 (by simp [quad])) (by simp [quad, h11.symm, hm.symm, h1.symm])
  set f : K → K := fun z => a * z + (a - 1)
  have hinj : Set.InjOn f (quad i) := fun x _ y _ hxy => by
    simpa [f, ha] using hxy
  have himg : (quad i).image f = quad i :=
    eq_of_subset_of_card_le (image_subset_iff.2 h) (card_image_of_injOn hinj).ge
  have hsum := congr(∑ z ∈ $himg, z)
  simp only [sum_image hinj, f, sum_add_distrib, sum_const, card_quad hi h2, nsmul_eq_mul,
    Nat.cast_ofNat] at hsum
  rw [← mul_sum, quad_sum hi h2] at hsum
  linear_combination hsum

/-- With `5` invertible as well, the fixer of `∞` and `−1` in `Aut(ℙ¹, Δ)` is trivial. -/
theorem fixer_trivial (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) (a : K)
    (h : ∀ z ∈ quad i, a * z + (a - 1) ∈ quad i) : a = 1 := by
  simpa [h5, sub_eq_zero] using fixer_five hi h2 a h

/-- In characteristic `5`, `z ↦ 2z + 1` (`a = 2`) maps `{0, 1, i, −i}` into itself. -/
theorem fixer_nontrivial_char5 (hi : i ^ 2 = -1) (h5 : (5 : K) = 0) :
    ∀ z ∈ quad i, 2 * z + (2 - 1) ∈ quad i := by
  have hi2 : (i - 2) * (i + 2) = 0 := by linear_combination hi - h5
  simp only [quad, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  rcases mul_eq_zero.1 hi2 with h | h
  · obtain rfl : i = 2 := by linear_combination h
    exact ⟨Or.inr (Or.inl (by norm_num)), Or.inr (Or.inr (Or.inr (by linear_combination h5))),
      Or.inl (by linear_combination h5), Or.inr (Or.inr (Or.inl (by linear_combination -h5)))⟩
  · obtain rfl : i = -2 := by linear_combination h
    exact ⟨Or.inr (Or.inl (by norm_num)), Or.inr (Or.inr (Or.inl (by linear_combination h5))),
      Or.inr (Or.inr (Or.inr (by linear_combination -h5))), Or.inl (by linear_combination h5)⟩

end Field

/-- A matrix `(a b; c d)` over `𝔽₅`, as a quadruple. -/
abbrev Mat5 := ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5

/-- Its determinant. -/
def det5 (q : Mat5) : ZMod 5 := q.1 * q.2.2.2 - q.2.1 * q.2.2.1

/-- The inverse of a nonzero element of `𝔽₅`, `z⁻¹ = z³`. -/
def inv5 (z : ZMod 5) : ZMod 5 := z * z * z

/-- The Möbius map `z ↦ (az + b)/(cz + d)` on `ℙ¹(𝔽₅) = 𝔽₅ ∪ {∞}` (`none` is `∞`). -/
def mob (q : Mat5) : Option (ZMod 5) → Option (ZMod 5)
  | none => if q.2.2.1 = 0 then none else some (q.1 * inv5 q.2.2.1)
  | some z =>
    if q.2.2.1 * z + q.2.2.2 = 0 then none
    else some ((q.1 * z + q.2.1) * inv5 (q.2.2.1 * z + q.2.2.2))

/-- The octahedral configuration `∞, 0, 1, −1, i, −i` with `i = 2`, in this order. -/
def octa : List (Option (ZMod 5)) := [none, some 0, some 1, some (-1), some 2, some (-2)]

theorem two_sq : (2 : ZMod 5) ^ 2 = -1 := by decide

theorem octahedral_eq_univ : octa.toFinset = Finset.univ := by decide

/-- The bijections of `ℙ¹(𝔽₅)` induced by invertible matrices, recorded by their values on
`octa`: the group `PGL₂(𝔽₅)`. -/
def pgl : Finset (List (Option (ZMod 5))) :=
  (Finset.univ.filter fun q : Mat5 => det5 q ≠ 0).image fun q => octa.map (mob q)

theorem perm_octa : ∀ q : Mat5, det5 q ≠ 0 → (octa.map (mob q)).Nodup := by decide +kernel

theorem card_pgl : pgl.card = 120 := by decide +kernel

theorem card_fixer :
    (pgl.filter fun l => l[0]? = some (none : Option (ZMod 5)) ∧
        l[3]? = some (some (-1 : ZMod 5))) =
      (({1, 2, 3, 4} : Finset (ZMod 5)).image fun a => octa.map (mob (a, a - 1, 0, 1))) := by
  decide +kernel

end Grothendieck.Folder64
