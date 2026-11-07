module

public import Mathlib
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# Folder 88: the order `2ν` (pages 6–8) and the trichotomy of (6) (page 14)

**Partial, and chosen.** Issue #26 names for this folder "the Coxeter
presentation of the cartographic group". In the reading
(`transcripts/88/88.modern.tex`, page 10) that presentation,
`Γ̂ = ⟨σ₀, σ₁, σ₂ | σᵢ², (σ₀σ₂)²⟩`, is a *definition* taken from the *Esquisse*,
not a statement — there is nothing to prove about it. The run 2 statements
about it ((1)–(7), `Aut(C_{p,q}) ≃ Γ_{p,q}`, finiteness of `Γ_{p,q}` in the
spherical case, free subgroups in the hyperbolic case) are marked
« à prouver » on the leaf and need maps on surfaces, which mathlib lacks. What
this file formalises is the two crisp statements of the reading that are
reachable.

## 1. The Proposition of page 8

The reading attaches to a root system the quadruple `(W, R, I, φ)` — `W` the
Weyl group, `R` its bases, a `W`-torsor, `φ(r, i)` the simple reflection of
index `i` for the base `r` — with a) `φ(w r, i) = int(w) φ(r, i)`, and the
operations on repères `R × Rep'(I)`, `Rep'(I) = Bij([1, ℓ], I)`:

> `σᵢ(r, u) = (r, u ∘ τ_{i+1})` (`0 ≤ i ≤ ℓ-2`),
> `σ_{ℓ-1}(r, u) = (φ(r, u(ℓ)) · r, u)`.
>
> **Proposition.** L'ordre de `σ_{ℓ-2} σ_{ℓ-1}` sur `R × Rep'(I)` est `2ν`, où
> `ν` est le plus petit commun multiple des `n_{ij}`, `i ≠ j`.

This is `proposition_ordre`. It is proved for any group `W`, any `W`-torsor
`R` and any `φ` satisfying a) and `φ(r, i)² = 1` (half of c)), which is what
makes `σ_{ℓ-1}` an involution. The rest of the hypotheses — that `W` is a Weyl
group, b), the presentation c), the Coxeter graph d) — are not used. Nor is
finiteness: with mathlib's convention that `orderOf` is `0` for an element of
infinite order, the formula `2ν` holds also when some `n_{ij}` is infinite.
The reading's footnote that `σ_{ℓ-2}σ_{ℓ-1}` is the inverse of the `π` it
computes with is confirmed (`sigmaAvant_mul_sigmaDernier`). The relation
`σ_{ℓ-1}² = 1` is `sigmaDernier_involutive`.

## 2. The trichotomy of (6)

> `C_{p,q}` est sphérique exactement pour `p = 2` ; `q = 2` ; et `(3,3)`,
> `(3,4)`, `(4,3)`, `(3,5)`, `(5,3)` ; euclidienne exactement pour `(4,4)`,
> `(3,6)`, `(6,3)` ; hyperbolique pour `p, q ≥ 3` dès que `p + q ≥ 9` et
> `(p,q) ≠ (3,6), (6,3)`. Les trois cas sont ceux où `1/p + 1/q` est supérieur,
> égal ou inférieur à `1/2`.

The geometric content (which surface carries `C_{p,q}`) is out of reach; the
arithmetic the reading uses to sort the cases is not, and it is checked for
finite types `(p, q)`, `p, q ≥ 1`, excluding the types `(1, p)`, `(p, 1)`,
`p ≠ 2`, which (2) says are not attained (`spherique_iff`, `euclidien_iff`,
`hyperbolique_iff`). It holds as the reading states it — including its
corrected form of the page's `(c₂)`.

What the formalisation found: nothing wrong. One hypothesis of the setting is
superfluous for the Proposition (everything but a), `φ(r,i)² = 1` and the
torsor structure), and so is finiteness.
-/

namespace Grothendieck.Folder88

open Equiv

/-! ### 1. The operations on repères and the order `2ν` -/

section Ordre

variable {W R I : Type*} [Group W] [MulAction W R]

/-- The data of the reading: a `W`-torsor `R` and `φ : R × I → W` with a)
`φ(w r, i) = w φ(r, i) w⁻¹` and `φ(r, i)² = 1`. -/
structure Epinglage (W R I : Type*) [Group W] [MulAction W R] where
  /-- `φ(r, i)`, the simple reflection of index `i` for the base `r`. -/
  φ : R → I → W
  /-- a) `φ(w r, i) = int(w) φ(r, i)`. -/
  equivariant : ∀ (w : W) r i, φ (w • r) i = w * φ r i * w⁻¹
  /-- `φ(r, i)² = 1`. -/
  involution : ∀ r i, φ r i * φ r i = 1
  /-- `W` acts freely on `R`. -/
  libre : ∀ (w : W) (r : R), w • r = r → w = 1
  /-- `W` acts transitively on `R`. -/
  transitif : ∀ r r' : R, ∃ w : W, w • r = r'

variable (E : Epinglage W R I) (n : ℕ)

/-- `Rep'(I) = Bij([1, ℓ], I)`, with `ℓ = n + 2` and `[1, ℓ]` written
`Fin (n + 2)` (position `k` of the reading is `k - 1` here). -/
abbrev Rep' (n : ℕ) (I : Type*) := Fin (n + 2) ≃ I

/-- The position `ℓ`. -/
def dernier : Fin (n + 2) := Fin.last (n + 1)

/-- The position `ℓ - 1`. -/
def avantDernier : Fin (n + 2) := (Fin.last n).castSucc

theorem avantDernier_ne_dernier : avantDernier n ≠ dernier n :=
  (Fin.castSucc_lt_last _).ne

/-- `τ_{ℓ-1}`, the transposition of `ℓ - 1` and `ℓ`. -/
def τ : Perm (Fin (n + 2)) := swap (avantDernier n) (dernier n)

/-- `σ_{ℓ-2}(r, u) = (r, u ∘ τ_{ℓ-1})`. -/
def sigmaAvant : Perm (R × Rep' n I) :=
  Function.Involutive.toPerm (fun x => (x.1, (τ n).trans x.2)) fun x => by
    ext k <;> simp [τ, swap_apply_self]

@[simp] theorem sigmaAvant_apply (x : R × Rep' n I) :
    sigmaAvant n x = (x.1, (τ n).trans x.2) := rfl

theorem sigmaDernier_aux (r : R) (i : I) :
    E.φ (E.φ r i • r) i • E.φ r i • r = r := by
  rw [E.equivariant, mul_inv_cancel_right, smul_smul, E.involution, one_smul]

/-- `σ_{ℓ-1}(r, u) = (φ(r, u(ℓ)) · r, u)`. -/
def sigmaDernier : Perm (R × Rep' n I) :=
  Function.Involutive.toPerm (fun x => (E.φ x.1 (x.2 (dernier n)) • x.1, x.2)) fun x => by
    simp only [sigmaDernier_aux]

@[simp] theorem sigmaDernier_apply (x : R × Rep' n I) :
    sigmaDernier E n x = (E.φ x.1 (x.2 (dernier n)) • x.1, x.2) := rfl

/-- `σ_{ℓ-1}² = 1`. -/
theorem sigmaDernier_involutive : sigmaDernier (I := I) E n * sigmaDernier E n = 1 := by
  ext x <;> simp [sigmaDernier_aux]

theorem sigmaAvant_mul_self : sigmaAvant (R := R) (I := I) n * sigmaAvant n = 1 := by
  ext x k <;> simp [τ, swap_apply_self]

/-- `π = σ_{ℓ-1} σ_{ℓ-2}`, the product the reading computes with. -/
def pi : Perm (R × Rep' n I) := sigmaDernier E n * sigmaAvant n

/-- The footnote: `σ_{ℓ-2} σ_{ℓ-1}` is the inverse of `π`. -/
theorem sigmaAvant_mul_sigmaDernier :
    sigmaAvant n * sigmaDernier E n = (pi E n)⁻¹ := by
  rw [pi, mul_inv_rev, inv_eq_of_mul_eq_one_right (sigmaAvant_mul_self n),
    inv_eq_of_mul_eq_one_right (sigmaDernier_involutive E n)]

/-- `a = φ(r, u(ℓ-1))`, `b = φ(r, u(ℓ))`; the reading's `ab`. -/
def ab (r : R) (u : Rep' n I) : W := E.φ r (u (avantDernier n)) * E.φ r (u (dernier n))

theorem pi_apply (r : R) (u : Rep' n I) :
    pi E n (r, u) = (E.φ r (u (avantDernier n)) • r, (τ n).trans u) := by
  simp [pi, τ]

/-- `π²(g r, u) = (g a b r, u)`. -/
theorem pi_sq (g : W) (r : R) (u : Rep' n I) :
    (pi E n ^ 2) (g • r, u) = ((g * ab E n r u) • r, u) := by
  rw [pow_two, Perm.mul_apply, pi_apply, pi_apply, E.equivariant, smul_smul,
    inv_mul_cancel_right, smul_smul, E.equivariant, smul_smul]
  have h1 : ((τ n).trans u) (avantDernier n) = u (dernier n) := by
    simp [τ, swap_apply_left]
  have h2 : (τ n).trans ((τ n).trans u) = u := by
    ext k; simp [τ, swap_apply_self]
  rw [h1, h2, E.equivariant, ab]
  congr 2
  group

/-- `π^{2m}(r, u) = ((ab)^m r, u)`. -/
theorem pi_pow_pair (r : R) (u : Rep' n I) (m : ℕ) :
    (pi E n ^ (2 * m)) (r, u) = ((ab E n r u) ^ m • r, u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add, mul_one, add_comm, pow_add, Perm.mul_apply, ih, pi_sq, pow_succ]

/-- An odd power of `π` changes `u`. -/
theorem pi_pow_impair (r : R) (u : Rep' n I) (m : ℕ) :
    ((pi E n ^ (2 * m + 1)) (r, u)).2 ≠ u := by
  rw [add_comm, pow_add, pow_one, Perm.mul_apply, pi_pow_pair, pi_apply]
  intro h
  have := congrArg (fun v : Rep' n I => v (dernier n)) h
  simp only [Equiv.trans_apply, τ, swap_apply_right] at this
  exact avantDernier_ne_dernier n (u.injective this)

/-- `π^k` fixes `(r, u)` iff `2 n_{u(ℓ-1), u(ℓ)}` divides `k`. -/
theorem pi_pow_fixe (r : R) (u : Rep' n I) (k : ℕ) :
    (pi E n ^ k) (r, u) = (r, u) ↔ 2 * orderOf (ab E n r u) ∣ k := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [pi_pow_pair, Nat.mul_dvd_mul_iff_left two_pos, orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun h => E.libre _ _ (congrArg Prod.fst h), fun h => by rw [h, one_smul]⟩
  · exact iff_of_false (fun h => pi_pow_impair E n r u m (congrArg Prod.snd h)) fun h =>
      absurd ((dvd_mul_right 2 _).trans h) (by omega)

/-- `n_{ij}` does not depend on the base: `φ(w r, i) φ(w r, j)` is conjugate to
`φ(r, i) φ(r, j)`. -/
theorem orderOf_indep (r r' : R) (i j : I) :
    orderOf (E.φ r' i * E.φ r' j) = orderOf (E.φ r i * E.φ r j) := by
  obtain ⟨w, rfl⟩ := E.transitif r r'
  rw [E.equivariant, E.equivariant, conj_mul, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

/-- Every ordered pair `i ≠ j` is `(u(ℓ-1), u(ℓ))` for some `u ∈ Rep'(I)`. -/
theorem existe_rep [DecidableEq I] (e : Rep' n I) (i j : I) (hij : i ≠ j) :
    ∃ u : Rep' n I, u (avantDernier n) = i ∧ u (dernier n) = j := by
  let u₁ : Rep' n I := e.trans (swap (e (avantDernier n)) i)
  have h₁ : u₁ (avantDernier n) = i := by simp [u₁]
  refine ⟨u₁.trans (swap (u₁ (dernier n)) j), ?_, by simp⟩
  have hne : u₁ (dernier n) ≠ i := by
    rw [← h₁]; exact fun h => avantDernier_ne_dernier n (u₁.injective h).symm
  simp only [Equiv.trans_apply, h₁]
  exact swap_apply_of_ne_of_ne hne.symm hij

variable [Fintype I] [DecidableEq I]

/-- `ν`, the lcm of the `n_{ij}`, `i ≠ j`, computed at a base `r₀`. -/
noncomputable def nu (r₀ : R) : ℕ :=
  ((Finset.univ : Finset (I × I)).filter (fun p => p.1 ≠ p.2)).lcm
    fun p => orderOf (E.φ r₀ p.1 * E.φ r₀ p.2)

/-- **Proposition** (page 8). For `ℓ = n + 2 = Card I` and `R` non-empty, the
order of `σ_{ℓ-2} σ_{ℓ-1}` on `R × Rep'(I)` is `2ν`. -/
theorem proposition_ordre (r₀ : R) (e : Rep' n I) :
    orderOf (sigmaAvant n * sigmaDernier E n) = 2 * nu E r₀ := by
  rw [sigmaAvant_mul_sigmaDernier, orderOf_inv]
  set S := (Finset.univ : Finset (I × I)).filter (fun p => p.1 ≠ p.2)
  set f : I × I → ℕ := fun p => orderOf (E.φ r₀ p.1 * E.φ r₀ p.2)
  have hS (u : Rep' n I) : (u (avantDernier n), u (dernier n)) ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => avantDernier_ne_dernier n (u.injective h)⟩
  -- `π^k = 1` iff `2 n_{ij} ∣ k` for all `i ≠ j`, iff `2ν ∣ k`.
  have key : ∀ k, pi E n ^ k = 1 ↔ 2 * S.lcm f ∣ k := by
    intro k
    have step1 : pi E n ^ k = 1 ↔ ∀ p ∈ S, 2 * f p ∣ k := by
      constructor
      · intro h p hp
        obtain ⟨u, hu1, hu2⟩ := existe_rep n e p.1 p.2 (Finset.mem_filter.1 hp).2
        simpa [ab, hu1, hu2, f] using (pi_pow_fixe E n r₀ u k).1 (by rw [h]; rfl)
      · intro h
        ext1 ⟨r, u⟩
        rw [Perm.one_apply, pi_pow_fixe, ab, orderOf_indep E r₀ r]
        exact h _ (hS u)
    refine step1.trans ⟨fun h => ?_, fun h p hp =>
      (Nat.mul_dvd_mul_left 2 (Finset.dvd_lcm hp)).trans h⟩
    obtain ⟨m, rfl⟩ : 2 ∣ k := (dvd_mul_right 2 _).trans (h _ (hS e))
    rw [Nat.mul_dvd_mul_iff_left two_pos]
    exact Finset.lcm_dvd fun p hp => (Nat.mul_dvd_mul_iff_left two_pos).1 (h p hp)
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((key _).2 dvd_rfl))
    ((key _).1 (pow_orderOf_eq_one _))

end Ordre

/-! ### 2. The arithmetic of (6) -/

/-- The types attained by (2): `p, q ≥ 1`, not `(1, p)` or `(p, 1)` with
`p ≠ 2`. -/
def TypeAtteint (p q : ℕ) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ (p = 1 → q = 2) ∧ (q = 1 → p = 2)

/-- **Spherical** (`1/p + 1/q > 1/2`, i.e. `pq < 2(p + q)`): exactly `p = 2`,
`q = 2`, and `(3,3), (3,4), (4,3), (3,5), (5,3)`. -/
theorem spherique_iff (p q : ℕ) (h : TypeAtteint p q) :
    p * q < 2 * (p + q) ↔
      p = 2 ∨ q = 2 ∨ (p, q) = (3, 3) ∨ (p, q) = (3, 4) ∨ (p, q) = (4, 3) ∨
        (p, q) = (3, 5) ∨ (p, q) = (5, 3) := by
  obtain ⟨hp, hq, h1, h2⟩ := h
  simp only [Prod.mk.injEq]
  constructor
  · intro hlt
    by_cases hp7 : p ≤ 6 <;> by_cases hq7 : q ≤ 6
    · interval_cases p <;> interval_cases q <;> simp_all
    · have : p ≤ 2 := by nlinarith
      interval_cases p <;> simp_all
    · have : q ≤ 2 := by nlinarith
      interval_cases q <;> simp_all
    · nlinarith
  · rintro (rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

/-- **Euclidean** (`1/p + 1/q = 1/2`): exactly `(4,4), (3,6), (6,3)`. -/
theorem euclidien_iff (p q : ℕ) (h : TypeAtteint p q) :
    p * q = 2 * (p + q) ↔ (p, q) = (4, 4) ∨ (p, q) = (3, 6) ∨ (p, q) = (6, 3) := by
  obtain ⟨hp, hq, -, -⟩ := h
  simp only [Prod.mk.injEq]
  constructor
  · intro heq
    by_cases hp7 : p ≤ 6 <;> by_cases hq7 : q ≤ 6
    · interval_cases p <;> interval_cases q <;> simp_all
    · have : p ≤ 2 := by nlinarith
      interval_cases p <;> omega
    · have : q ≤ 2 := by nlinarith
      interval_cases q <;> omega
    · nlinarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

/-- **Hyperbolic** (`1/p + 1/q < 1/2`), for `p, q ≥ 3`: exactly `p + q ≥ 9` with
`(p, q) ≠ (3,6), (6,3)`. -/
theorem hyperbolique_iff (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
    2 * (p + q) < p * q ↔ 9 ≤ p + q ∧ (p, q) ≠ (3, 6) ∧ (p, q) ≠ (6, 3) := by
  simp only [ne_eq, Prod.mk.injEq]
  constructor
  · intro hlt
    by_cases hp7 : p ≤ 6 <;> by_cases hq7 : q ≤ 6
    · interval_cases p <;> interval_cases q <;> simp_all
    · omega
    · omega
    · omega
  · rintro ⟨h9, h36, h63⟩
    by_cases hp7 : p ≤ 6 <;> by_cases hq7 : q ≤ 6
    · interval_cases p <;> interval_cases q <;> simp_all
    · nlinarith
    · nlinarith
    · nlinarith

end Grothendieck.Folder88
