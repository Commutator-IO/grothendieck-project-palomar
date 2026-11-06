module

public import Mathlib

public section


/-!
# Folder 145, pages 34–35: the unit-exponent exercise

The modernised reading `transcripts/145/145.modern.tex` (« Les rectificateurs triviaux »,
pages 34 and 35) reduces the profinite case of the trivial-rectifier systems to the
statement (14), which the page leaves as « Exercice ! »: in the free profinite group on
`l₀, l₁`, with `l_∞ l₁ l₀ = 1`, a unit `p ∈ ℤ̂*` satisfies

  `l_∞^p l₁^p l₀^p = 1  ⟹  p = 1`.

This is finding `145-unit-exponent-exercise` of `src/content/findings.ts`; the proof is
the edition's (a dihedral quotient). Proving it says only that the claim holds as stated;
whether it stands in the literature is a separate question.

What is formalised.

mathlib has no free profinite group and no `ℤ̂`-powers. A relation holds in the free
profinite group on `l₀, l₁` iff it holds for every image of `(l₀, l₁)` in every finite
group, and `p ∈ ℤ̂` acts on a finite group `G` through its residue modulo `card G`. So
`p` is a compatible family of residues `p n ∈ ZMod n` (`n ≠ 0`), `x ^ p` in a finite
group `G` is `x ^ (p (card G)).val` (`hatPow`), and (14) for `p` is `Rel14 p`: for every
finite group `G` and `x y z : G` with `z * y * x = 1`, `z^p * y^p * x^p = 1`.

* `dihedral_witness`: for an odd integer `m` and `N ≠ 0`, in `DihedralGroup N` the
  reflections `x = sr 1`, `y = sr 0` and `z = (y x)⁻¹` satisfy `z^m y^m x^m = 1` iff
  `m ≡ 1 (mod N)`.
* `rel14_iff` (the exercise): if `p 2 = 1` — `p` odd, which a unit of `ℤ̂` is — then
  `Rel14 p` iff `p n = 1` for every `n ≠ 0`. `rel14_unit_iff` is the page's form, with
  `p` a unit.
* `rel14_zero`: the oddness cannot be dropped, `p = 0` satisfies (14).

So the exercise holds, more generally: only the oddness of `p` is used, not that `p` is
a unit at the odd primes. The compatibility of the family is used only to pass from
`p (2N)` to `p N` and to `p 2`.
-/

namespace Grothendieck.Folder145

open DihedralGroup

/-- A profinite integer, as a family of residues: `p n ∈ ZMod n` for `n ≠ 0`, compatible
under reduction. (The value at `n = 0` plays no role.) -/
def Compatible (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ m n : ℕ, n ≠ 0 → ∀ h : m ∣ n, ZMod.castHom h (ZMod m) (p n) = p m

/-- `x ^ p` for `p ∈ ℤ̂` in a finite group: the power by the residue of `p` modulo the
order of the group. -/
def hatPow {G : Type*} [Group G] [Fintype G] (p : ∀ n : ℕ, ZMod n) (x : G) : G :=
  x ^ (p (Fintype.card G)).val

/-- Relation (14) of page 35, `l_∞^p l₁^p l₀^p = 1` under `l_∞ l₁ l₀ = 1`, read in every
finite quotient of the free profinite group on `l₀, l₁`. -/
def Rel14 (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (x y z : G),
    z * y * x = 1 → hatPow p z * hatPow p y * hatPow p x = 1

lemma pow_odd_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) {m : ℕ}
    (hm : Odd m) : x ^ m = x := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hx, one_pow, one_mul]

/-- The dihedral witness: for `m` odd, `(sr 0 · sr 1)⁻¹ ^ m · sr 0 ^ m · sr 1 ^ m = 1`
in `DihedralGroup N` iff `m ≡ 1 (mod N)`. -/
theorem dihedral_witness (N : ℕ) {m : ℕ} (hm : Odd m) :
    ((sr 0 * sr 1 : DihedralGroup N)⁻¹) ^ m * (sr 0) ^ m * (sr 1) ^ m = 1 ↔
      (m : ZMod N) = 1 := by
  rw [pow_odd_of_mul_self (sr_mul_self 0) hm, pow_odd_of_mul_self (sr_mul_self 1) hm,
    sr_mul_sr, sub_zero, inv_pow, r_one_pow, mul_assoc, sr_mul_sr, sub_zero, inv_mul_eq_one]
  simp only [r.injEq]

lemma val_odd_of_two (p : ∀ n : ℕ, ZMod n) (hp : Compatible p) (h2 : p 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (h : 2 ∣ n) : Odd (p n).val := by
  have hc := hp 2 n hn h
  have : NeZero n := ⟨hn⟩
  rw [h2, ZMod.castHom_apply, ZMod.cast_eq_val] at hc
  rw [Nat.odd_iff, ← ZMod.val_natCast, hc]
  rfl

/-- **The exercise of page 35**, more generally: for a compatible family `p` with `p` odd
(`p 2 = 1`), relation (14) holds in every finite group iff `p = 1`. -/
theorem rel14_iff (p : ∀ n : ℕ, ZMod n) (hp : Compatible p) (h2 : p 2 = 1) :
    Rel14 p ↔ ∀ n : ℕ, n ≠ 0 → p n = 1 := by
  constructor
  · intro h n hn
    have h2n : 2 * n ≠ 0 := by omega
    have hodd := val_odd_of_two p hp h2 h2n (dvd_mul_right 2 n)
    have : NeZero n := ⟨hn⟩
    have key := h (DihedralGroup n) (sr 1) (sr 0) (sr 0 * sr 1)⁻¹ (by group)
    rw [hatPow, hatPow, hatPow, DihedralGroup.card] at key
    have : NeZero (2 * n) := ⟨h2n⟩
    rw [← hp n (2 * n) h2n (dvd_mul_left n 2), ZMod.castHom_apply, ZMod.cast_eq_val,
      (dihedral_witness n hodd).1 key]
  · intro h G _ _ x y z hxyz
    simpa only [hatPow, h _ Fintype.card_ne_zero, ZMod.val_one_eq_one_mod, pow_mod_card,
      pow_one] using hxyz

/-- The page's form: `p` a unit of `ℤ̂` (each residue a unit). -/
theorem rel14_unit_iff (p : ∀ n : ℕ, ZMod n) (hp : Compatible p)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (p n)) :
    Rel14 p ↔ ∀ n : ℕ, n ≠ 0 → p n = 1 := by
  refine rel14_iff p hp ?_
  have := hu 2 (by norm_num)
  generalize p 2 = a at this
  revert a; decide

/-- The oddness cannot be dropped: `p = 0` satisfies (14). -/
theorem rel14_zero : Rel14 (fun _ => 0) := by
  intro G _ _ x y z _
  simp [hatPow]

theorem compatible_zero : Compatible (fun _ => 0) := fun _ _ _ _ => map_zero _

end Grothendieck.Folder145
