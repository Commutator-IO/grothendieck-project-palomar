module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

@[expose] public section


/-!
# Folder 16: the `𝔰𝔩₂` side of hard Lefschetz, against the folder's pseudo-inverse `Λ`

Issue #26 lists folder 16 in tier 2: « Hard Lefschetz via `𝔰𝔩₂`-representations;
the representation theory is partly there, the geometry is not ». Only the
algebraic `𝔰𝔩₂` statements of `transcripts/16/16.modern.tex` are formalised
here; none of the geometry (hyperplane sections, standard conjectures).

The folder itself never uses `𝔰𝔩₂`: its `Λ` is a *pseudo-inverse* of `L`,
normalised by `(6.7)`, `LΛ = 1 - ∑_{i ≤ n} π_{i,0}`, `ΛL = 1 - ∑_{i ≥ n} π_{i,0}`,
so as to stay over `ℤ`. The reading states three things about how this differs
from the `𝔰𝔩₂` (Hodge) normalisation, and a fourth about the manuscript's model:

> (page 9) … l'adjoint de `L` pour la métrique, lequel satisfait `[L,Λ] = H` et
> agit sur `L^k P^i` par des scalaires entiers non triviaux — sur une classe
> primitive de degré `i` on a `Λ L x = (n-i) x` et non `x`.
>
> (page 16) avec un `Λ` normalisé en pseudo-inverse, ce commutateur vaut
> `∑_{i ≥ n} π_{i,0} - ∑_{i ≤ n} π_{i,0}` et ne retient que les extrémités des
> chaînes.
>
> (page 16) Le couple `(L₀, Λ₀)` formé de `ξ₀ ∧ -` et de `ξ₀* ⌟ -` … Sur
> l'unité, qui est primitive de degré `0`, `Λ₀ L₀ (1) = ⟨ξ₀*, ξ₀⟩ = n`, alors que
> `(6.15)` exige `1` … l'identification ne vaut donc que pour `n = 1`.

* `sl2_normalisation` — in any representation with an `𝔰𝔩₂`-triple, on a
  primitive vector of weight `μ` (`= n - i` in degree `i`): `ΛLx = μx`,
  `Λ L^{k+1} x = (k+1)(μ-k) L^k x`, `⁅H, L^k x⁆ = (μ-2k) L^k x`. From mathlib
  (`IsSl2Triple.HasPrimitiveVectorWith`). mathlib's `H = ⁅Λ, L⁆` is minus the
  reading's `[L, Λ]`.
* `identification_seulement_si` — if the `𝔰𝔩₂` `Λ` also satisfied `ΛLx = x` on a
  primitive class, as `(6.7)` asks at the bottom of a chain, then `μ = 1`
  (over a domain acting without torsion).
* `commutateur_pseudo_inverse` — the commutator formula, from `(6.7)` alone.
* `lambda0_L0_un`, `lambda0_L0_un_ne_un` — in the exterior algebra `Λ M₀`,
  `M₀ = R^{2n}`, `ξ₀ = ∑ e_{2k-1} ∧ e_{2k}`: `Λ₀ L₀ (1) = n`, hence `≠ 1` for
  `n ≠ 1` in characteristic `0`. This is the reading's correction of page 13,
  where the manuscript identifies the contraction `Λ₀` with the `Λ₀` of `(6.15)`.

* `inverse_mem_of_charpoly`, `inverse_Lefschetz_algebrique` — pages 47–48 (finding
  `16-algebraic-iso-suffices`): under `D(X)` (characteristic polynomials of algebraic
  endomorphisms with coefficients in `F`), any algebraic isomorphism `u : H^{2n-i} → H^i`
  makes the inverse of the isomorphism `v` induced by `L^{n-i}` algebraic. « Algebraic » is
  membership in given sets of maps, stable under composition and `F`-scalars.
* `projecteurs_mem`, `projecteurs_mem_lefschetz` — pages 6–8 (no. 5 and `(6.3)ᵢ`, the first
  part of finding `16-graded-ring-lefschetz-criterion`): in a ring with grading idempotents,
  one-sided inverses `wᵢ ∈ ℰ` of `L^{n-i}` put every `πᵢ` in the subring `ℰ`, over `ℤ`.
* `not_exists_xi₀_pow_mul_eq_vol`, `L₀_pow_ne_vol` — page 13 over `ℤ` (finding
  `16-universal-lefschetz-ring`): for `n ≥ 2`, `ξ₀ⁿ ∧ y` is never the top class `vol` of
  `Λ ℤ^{2n}` (`ξ₀²` is even), so `(6.3)₀` fails in the exterior model over `ℤ` and no `Λ₀`
  in the sense of `(6.15)` exists in `End_ℤ(Λ M₀)`.
* `pseudo_inverse_unique` — a pseudo-inverse with `ΛLΛ = Λ` is determined by `ΛL` and `LΛ`.

* Pages 24–28, the « algèbres de Hodge d'ordre 2 » (finding `16-hodge-algebras-order-2`).
  `DonneesHodge` holds `(φ, ψ, Q)`: `φ` alternating on `V`, `ψ : Λ²V → W`, `Q` symmetric on `W`;
  `AlgHodge` is `k ⊕ V ⊕ (kξ ⊕ W) ⊕ V̌ ⊕ kξ²` and `DonneesHodge.mul` the product of page 24.
  `produits`, `produit_force` — the products of the reading, and the `H¹ × H²` one is the only
  one compatible with associativity and the pairing `H¹ × H³`; `one_mul`, `mul_one`, `mulₗ`,
  `mul_comm_of_pair`, `mul_anticomm_of_impair`, `mul_self_of_impair` — whatever `φ, ψ, Q`, a
  bilinear unital graded-anticommutative law; `assoc_iff` — associative iff
  `φ(x,y)φ(t,z) + Q(ψ(x,y), ψ(t,z)) = φ(t,x)φ(y,z) + Q(ψ(t,x), ψ(y,z))`; `lefschetz_iff` —
  `ξ² : H⁰ → H⁴` is always bijective and `ξ : H¹ → H³` is iff `φ` is non-degenerate
  (`V` finite-dimensional); `poincare_iff` — `H⁰ × H⁴`, `H¹ × H³` always perfect, `H² × H²`
  non-degenerate iff `Q` is (no finiteness). Page 26: `chi_eq` (`xyzt = χ(x,y,z,t)ξ²`),
  `chi_alt`, `identite_iff_chi` (associativity ⇔ `χ` alternating ⇔ `χ(x,y,y,t) = 0`), and
  `reformulation`, `reformulation_spec`: from `(W̃, Q̃, α, ξ)` with `Q̃(ξ,ξ) = 1`, `W = ξ^⊥`,
  `φ = Q̃(α(·), ξ)`, `ψ = α - φξ`, `Q = Q̃|_W`, associativity is `Q̃(α(x∧y), α(y∧t)) = 0`,
  Lefschetz is « `φ` non dégénérée » and Poincaré is « `Q̃` non dégénérée ».

**What the formalisation finds.** The reading's comparison of the two normalisations holds
as stated, and its correction of the manuscript (the two `Λ₀` differ as soon as `n ≥ 2`) is
confirmed by `Λ₀ L₀ (1) = n`; the `𝔰𝔩₂` facts themselves are already in mathlib. The
Cayley–Hamilton argument of page 47 and the projector argument of no. 5 hold as stated.
But the reading's repair of page 13 — keep `Φ₀ = ℤ[L₀, Λ₀] ⊂ End(Λ M₀)` with `Λ₀` in the
sense of `(6.15)` — fails over `ℤ` for `n ≥ 2`: `L₀ⁿ : Λ⁰ → Λ^{2n}` is multiplication by
`n!` (here: by an even number), so the exterior model over `ℤ` does not satisfy the
Lefschetz conditions. Over `ℚ` the obstruction disappears.

The Hodge algebras of order 2 hold as the reading states them, over any commutative ring for the
construction and associativity, over a field for the two conditions: associativity reduces to
the single triple `H¹ × H¹ × H¹` (the triples with one factor in `H²` hold by the definition of
`x · h`, using only that `φ`, `ψ` are alternating and `Q` symmetric), and each condition reads
on one datum. Finite dimension is used once, for Lefschetz (`ξ : V → V̌` injective ⇒ onto);
Poincaré needs none. The quadrilinear identity is exactly the alternance of `χ`, and in the
reformulation `Q̃` is non-degenerate iff its restriction to `ξ^⊥` is, because `Q̃(ξ,ξ) = 1`.

**Not formalised.** That `(L₀, Λ₀)` generate an `𝔰𝔩₂`-representation on all of
`Λ M₀` (only its value on `1` is computed); the derivation of hard Lefschetz from
`𝔰𝔩₂` (the folder takes the primitive decomposition as known); in the theorem of no. 6,
that `Λ` and the projectors `π_{i,α}` given by the formulas of pages 10–12 satisfy `(6.7)`
and are the projectors of the primitive decomposition; the existence and uniqueness of the
homomorphism `Φ₀ → ℰ`; the Corollary of page 48; the dimension-6 counterexample of page
21; the finiteness question of page 28 on the orbit under `u` (an unreconstructible sketch);
everything geometric.

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder16

open LieModule

section Sl2

variable {R 𝔤 M : Type*} [CommRing R] [LieRing 𝔤] [LieAlgebra R 𝔤]
  [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable {H Λ L : 𝔤} (t : IsSl2Triple H Λ L)

/-- **Page 9 (the editor's comparison), Hodge normalisation.** In a representation
of `𝔰𝔩₂` with `Λ` lowering and `L` raising (mathlib's `e` and `f`), let `x` be a
primitive class (`Λ x = 0`) of weight `μ` (for a class of degree `i` with top
degree `2n`, `μ = n - i`; mathlib's `H = ⁅Λ, L⁆` is minus the reading's
`[L, Λ]`). Then `Λ L x = μ x` — « sur une classe primitive de degré `i` on a
`Λ L x = (n-i) x` et non `x` » — and more generally `Λ` acts on `L^{k+1} x` by
the integer `(k+1)(μ-k)`, while the commutator restores the degree:
`⁅H, L^k x⁆ = (μ - 2k) L^k x`. -/
theorem sl2_normalisation {x : M} {μ : R} (P : t.HasPrimitiveVectorWith x μ) (k : ℕ) :
    ⁅Λ, ⁅L, x⁆⁆ = μ • x ∧
      ⁅Λ, (toEnd R 𝔤 M L ^ (k + 1)) x⁆ = ((k + 1) * (μ - k)) • (toEnd R 𝔤 M L ^ k) x ∧
      ⁅H, (toEnd R 𝔤 M L ^ k) x⁆ = (μ - 2 * k) • (toEnd R 𝔤 M L ^ k) x := by
  refine ⟨?_, P.lie_e_pow_succ_toEnd_f k, P.lie_h_pow_toEnd_f k⟩
  simpa using P.lie_e_pow_succ_toEnd_f 0

/-- **Page 16, « l'identification ne vaut donc que pour `n = 1` ».** If the `𝔰𝔩₂`
operator `Λ` were also the pseudo-inverse of `(6.7)`, so that `Λ L x = x` on a
primitive class `x` of the bottom of a chain, then `(μ - 1) x = 0`; over a
domain acting without torsion, `μ = 1`. For the unit of the exterior algebra,
primitive of degree `0`, `μ = n`: the two normalisations agree only for
`n = 1`. -/
theorem identification_seulement_si [IsDomain R] [Module.IsTorsionFree R M] {x : M} {μ : R}
    (P : t.HasPrimitiveVectorWith x μ) (h : ⁅Λ, ⁅L, x⁆⁆ = x) : μ = 1 := by
  have h1 := (sl2_normalisation t P 0).1
  rw [h] at h1
  have : (μ - 1) • x = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right P.ne_zero)

end Sl2

section PseudoInverse

variable {E : Type*} [Ring E]

/-- **Page 16 (the editor's computation from `(6.7)`).** With `Λ` normalised as a
two-sided pseudo-inverse, `LΛ = 1 - ∑_{0 ≤ i ≤ n} π_{i,0}` and
`ΛL = 1 - ∑_{n ≤ i ≤ 2n} π_{i,0}`, the commutator is
`[L, Λ] = ∑_{i ≥ n} π_{i,0} - ∑_{i ≤ n} π_{i,0}`: it only sees the ends of the
chains, and does not restore the grading. -/
theorem commutateur_pseudo_inverse (n : ℕ) (Lf Λf : E) (π : ℕ → E)
    (h₁ : Lf * Λf = 1 - ∑ i ∈ Finset.range (n + 1), π i)
    (h₂ : Λf * Lf = 1 - ∑ i ∈ Finset.Icc n (2 * n), π i) :
    Lf * Λf - Λf * Lf = ∑ i ∈ Finset.Icc n (2 * n), π i - ∑ i ∈ Finset.range (n + 1), π i := by
  rw [h₁, h₂]
  abel

end PseudoInverse

section ModeleExterieur

open CliffordAlgebra

variable (R : Type*) [CommRing R] (n : ℕ)

/-- `M₀ = R^{2n}`, with basis `e_{k,0}, e_{k,1}` (`k < n`), i.e. `e_{2k-1}, e_{2k}`. -/
abbrev M₀ := Fin n × Fin 2 → R

/-- The basis vector `e_{k,b}` of `M₀`. -/
noncomputable def base (k : Fin n) (b : Fin 2) : M₀ R n := Pi.single (k, b) 1

/-- `ξ₀ = ∑_k e_{k,0} ∧ e_{k,1}` in `Λ M₀`. -/
noncomputable def xi₀ : ExteriorAlgebra R (M₀ R n) :=
  ∑ k : Fin n, ExteriorAlgebra.ι R (base R n k 0) * ExteriorAlgebra.ι R (base R n k 1)

/-- `L₀ x = ξ₀ ∧ x`. -/
noncomputable def L₀ (x : ExteriorAlgebra R (M₀ R n)) : ExteriorAlgebra R (M₀ R n) := xi₀ R n * x

/-- `Λ₀ x = ξ₀* ⌟ x`, contraction by the dual form `ξ₀* = ∑_k e*_{k,0} ∧ e*_{k,1}`,
with the convention that `a ∧ b` contracts as `ι_b ∘ ι_a`. -/
noncomputable def Λ₀ (x : ExteriorAlgebra R (M₀ R n)) : ExteriorAlgebra R (M₀ R n) :=
  ∑ k : Fin n, contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 1))
    (contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 0)) x)

/-- **Page 16 (the reading's footnote).** « Sur l'unité, qui est primitive de
degré `0`, `Λ₀ L₀ (1) = ⟨ξ₀*, ξ₀⟩ = n`. » -/
theorem lambda0_L0_un : Λ₀ R n (L₀ R n 1) = (n : ExteriorAlgebra R (M₀ R n)) := by
  simp only [L₀, mul_one, xi₀, Λ₀, map_sum]
  have key : ∀ k j : Fin n,
      contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 1))
        (contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 0))
          (ExteriorAlgebra.ι R (base R n j 0) * ExteriorAlgebra.ι R (base R n j 1))) =
        if k = j then 1 else 0 := by
    intro k j
    rw [contractLeft_ι_mul, contractLeft_ι]
    simp only [base, LinearMap.proj_apply, Pi.single_apply, Prod.mk.injEq]
    have h01 : ((0 : Fin 2) = 1) = False := by decide
    simp only [h01, and_false, ite_false, map_zero, mul_zero, sub_zero, and_true, map_smul]
    rw [ExteriorAlgebra.ι, contractLeft_ι]
    simp only [LinearMap.proj_apply, Pi.single_apply, Prod.mk.injEq, and_true]
    split_ifs <;> simp
  simp_rw [key]
  simp

/-- **Page 16.** « `Λ₀ L₀ (1) = n`, alors que `(6.15)` exige `1` … l'identification
ne vaut donc que pour `n = 1` »: in characteristic zero, the contraction `Λ₀`
satisfies `Λ₀ L₀ (1) = 1` only if `n = 1`. -/
theorem lambda0_L0_un_ne_un [CharZero R] (hn : n ≠ 1) :
    Λ₀ R n (L₀ R n 1) ≠ 1 := by
  rw [lambda0_L0_un]
  intro h
  have := congrArg (ExteriorAlgebra.algebraMapInv (R := R) (M := M₀ R n)) h
  simp only [map_natCast, map_one] at this
  exact hn (by exact_mod_cast this)

end ModeleExterieur

section CayleyHamilton

open Polynomial

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- **Page 47, the Cayley–Hamilton step.** Let `V` be finite-dimensional over a field `K`
(`H^i(X)` over `ℚ_ℓ`), `F ⊆ K` a subfield (`ℚ`), and `𝒜` a ring of endomorphisms stable under
`F`-scalars (the algebraic ones), whose characteristic polynomials have coefficients in `F`
(the hypothesis `D(X)` of the letter). Then the inverse of an invertible `w ∈ 𝒜` is in `𝒜`:
Cayley–Hamilton writes `w⁻¹` as `-σ_b(w)⁻¹ ∑ ± σ_j(w) w^{j}`, with coefficients in `F`. -/
theorem inverse_mem_of_charpoly (F : Subfield K) (𝒜 : Subring (Module.End K V))
    (hsmul : ∀ c ∈ F, ∀ g ∈ 𝒜, c • g ∈ 𝒜)
    (hD : ∀ g ∈ 𝒜, ∀ j, g.charpoly.coeff j ∈ F)
    {w : Module.End K V} (hw : w ∈ 𝒜) (hunit : IsUnit w) :
    ∃ g ∈ 𝒜, g * w = 1 ∧ w * g = 1 := by
  set p := w.charpoly with hp
  have hCH : aeval w p = 0 := LinearMap.aeval_self_charpoly w
  have hc0 : p.coeff 0 ≠ 0 := fun h => ((LinearMap.isUnit_iff_isUnit_det w).1 hunit).ne_zero (by
    rw [LinearMap.det_eq_sign_charpoly_coeff w, ← hp, h, mul_zero])
  set q := aeval w p.divX with hq
  have hqw : q * w = -algebraMap K _ (p.coeff 0) := by
    have := congrArg (aeval w) (divX_mul_X_add p)
    rw [map_add, map_mul, aeval_X, aeval_C, hCH] at this
    exact eq_neg_of_add_eq_zero_left this
  have hwq : w * q = q * w := by simpa only [aeval_X] using ((commute_X p.divX).map (aeval w)).eq
  have hqmem : q ∈ 𝒜 := by
    rw [hq, aeval_eq_sum_range]
    refine Subring.sum_mem _ fun j _ => ?_
    exact hsmul _ (by rw [coeff_divX]; exact hD w hw _) _ (Subring.pow_mem _ hw _)
  have key : (-(p.coeff 0)⁻¹ • q) * w = 1 := by
    rw [smul_mul_assoc, hqw, smul_neg, neg_smul, neg_neg, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨-(p.coeff 0)⁻¹ • q, ?_, key, ?_⟩
  · exact hsmul _ (F.neg_mem (F.inv_mem (hD w hw 0))) _ hqmem
  · rw [mul_smul_comm, hwq, ← smul_mul_assoc, key]

/-- **Pages 47–48, « un isomorphisme algébrique quelconque ».** With `V = H^i(X)`,
`W = H^{2n-i}(X)` and « algebraic » read as membership in given sets of maps
(`𝒜V` a ring as above, satisfying `D(X)`; `𝒜WV`, `𝒜VW` the algebraic maps between the two
degrees, stable under composition): if `u : W → V` is *some* algebraic isomorphism and `v`
(induced by `L^{n-i}`) is an algebraic isomorphism, then `v⁻¹` is algebraic. The proof is the
letter's: `w = u ∘ v` is an algebraic automorphism of `V`, `w⁻¹` is algebraic by
Cayley–Hamilton, and `v⁻¹ = w⁻¹ ∘ u`. -/
theorem inverse_Lefschetz_algebrique (F : Subfield K) (𝒜V : Subring (Module.End K V))
    (𝒜WV : Set (W →ₗ[K] V)) (𝒜VW : Set (V →ₗ[K] W))
    (hsmul : ∀ c ∈ F, ∀ g ∈ 𝒜V, c • g ∈ 𝒜V)
    (hD : ∀ g ∈ 𝒜V, ∀ j, g.charpoly.coeff j ∈ F)
    (hcomp₁ : ∀ g ∈ 𝒜V, ∀ h ∈ 𝒜WV, g ∘ₗ h ∈ 𝒜WV)
    (hcomp₂ : ∀ h ∈ 𝒜WV, ∀ k ∈ 𝒜VW, h ∘ₗ k ∈ 𝒜V)
    {u : W →ₗ[K] V} (hu : u ∈ 𝒜WV) (hub : Function.Bijective u)
    {v : V →ₗ[K] W} (hv : v ∈ 𝒜VW) (hvb : Function.Bijective v) :
    ∃ v' ∈ 𝒜WV, v' ∘ₗ v = LinearMap.id ∧ v ∘ₗ v' = LinearMap.id := by
  have hw : u ∘ₗ v ∈ 𝒜V := hcomp₂ _ hu _ hv
  have hunit : IsUnit (u ∘ₗ v : Module.End K V) :=
    (Module.End.isUnit_iff _).2 (hub.comp hvb)
  obtain ⟨g, hg, hgw, -⟩ := inverse_mem_of_charpoly F 𝒜V hsmul hD hw hunit
  have hleft : (g ∘ₗ u) ∘ₗ v = LinearMap.id := (LinearMap.comp_assoc _ _ _).trans hgw
  refine ⟨g ∘ₗ u, hcomp₁ _ hg _ hu, hleft, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := hvb.2 y
  exact congrArg v (LinearMap.congr_fun hleft x)

end CayleyHamilton

section Projecteurs

variable {E : Type*} [Ring E]

/-- `x` is homogeneous of degree `d` for the grading given by the idempotents `π`:
`π_b x π_a = 0` unless `b = a + d`. -/
def Homogene (π : ℤ → E) (d : ℤ) (x : E) : Prop :=
  ∀ a b, b ≠ a + d → π b * x * π a = 0

/-- The grading data: `π` orthogonal idempotents of sum `1`, zero outside `[0, 2n]`. -/
structure Graduation (π : ℤ → E) (n : ℕ) : Prop where
  idem : ∀ a, π a * π a = π a
  orth : ∀ a b, a ≠ b → π a * π b = 0
  supp : ∀ a, a ∉ Finset.Icc (0 : ℤ) (2 * n) → π a = 0
  sum : ∑ a ∈ Finset.Icc (0 : ℤ) (2 * n), π a = 1

variable {π : ℤ → E} {n : ℕ}

/-- `x π_a = π_{a+d} x π_a` for `x` homogeneous of degree `d`. -/
theorem Graduation.mul_proj (G : Graduation π n) {d : ℤ} {x : E} (hx : Homogene π d x) (a : ℤ) :
    x * π a = π (a + d) * x * π a := by
  calc x * π a = (∑ b ∈ Finset.Icc (0 : ℤ) (2 * n), π b) * x * π a := by rw [G.sum, one_mul]
    _ = ∑ b ∈ Finset.Icc (0 : ℤ) (2 * n), π b * x * π a := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = π (a + d) * x * π a := by
      refine Finset.sum_eq_single (a + d) (fun b _ hb => hx a b hb) (fun h => ?_)
      rw [G.supp _ h, zero_mul, zero_mul]

theorem Graduation.homogene_one (G : Graduation π n) : Homogene π 0 (1 : E) :=
  fun a b hab => by rw [mul_one, G.orth b a (by omega)]

theorem Graduation.homogene_mul (G : Graduation π n) {d e : ℤ} {x y : E}
    (hx : Homogene π d x) (hy : Homogene π e y) : Homogene π (d + e) (x * y) := by
  intro a b hab
  rw [← mul_assoc, mul_assoc _ y, G.mul_proj hy, ← mul_assoc, ← mul_assoc,
    hx (a + e) b (by omega), zero_mul, zero_mul]

theorem Graduation.homogene_pow (G : Graduation π n) {L : E} (hL : Homogene π 2 L) (k : ℕ) :
    Homogene π (2 * k) (L ^ k) := by
  induction k with
  | zero => simpa using G.homogene_one
  | succ k ih =>
    rw [pow_succ, show 2 * ((k + 1 : ℕ) : ℤ) = 2 * k + 2 by push_cast; ring]
    exact G.homogene_mul ih hL

/-- The computation of no. 5: `ψ v φ = π_{2n-i} v π_i` when only one pair of degrees survives. -/
theorem sandwich {d : ℤ} {x : E} (hx : Homogene π d x) (A B : Finset ℤ) {a₀ : ℤ}
    (ha₀ : a₀ ∈ A) (hb₀ : a₀ + d ∈ B) (huniq : ∀ a ∈ A, a + d ∈ B → a = a₀) :
    (∑ b ∈ B, π b) * x * (∑ a ∈ A, π a) = π (a₀ + d) * x * π a₀ := by
  rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_eq_single (a₀ + d)]
  · exact Finset.sum_eq_single a₀ (fun a _ ha => hx a _ (fun h => ha (by omega)))
      fun h => absurd ha₀ h
  · intro b hb hne
    refine Finset.sum_eq_zero fun a ha => hx a b fun h => hne ?_
    rw [h, huniq a ha (h ▸ hb)]
  · exact fun h => absurd hb₀ h

/-- The complement of a sum of known projectors. -/
theorem Graduation.sum_filter_not (G : Graduation π n) (P : ℤ → Prop) [DecidablePred P] :
    ∑ a ∈ (Finset.Icc (0 : ℤ) (2 * n)).filter (fun a => ¬ P a), π a =
      1 - ∑ a ∈ (Finset.Icc (0 : ℤ) (2 * n)).filter P, π a := by
  rw [← G.sum, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc (0 : ℤ) (2 * n)) P π]
  abel

/-- **Pages 6–7 (`(4.4)ᵢ` and no. 5, on the leaf « 5 bis »), over `ℤ`.** Let `ℰ` be a
subring of a ring `E` in which orthogonal idempotents `π_a` of sum `1`, zero outside
`[0, 2n]`, define the
grading. If for each `i ≤ n` there are `vᵢ ∈ ℰ` of degree `2n - 2i` and `wᵢ ∈ ℰ` of degree
`-(2n - 2i)` with `(wᵢvᵢ - 1)πᵢ = 0` and `(vᵢwᵢ - 1)π_{2n-i} = 0`, then every `π_a` is in `ℰ`.
Descending induction: `φᵢ = ∑_{a ≥ i} π_a` and `ψ_{2n-i} = ∑_{a ≤ 2n-i} π_a` are in `ℰ`,
`v'ᵢ = ψ vᵢ φ = π_{2n-i} vᵢ πᵢ`, `w'ᵢ = φ wᵢ ψ = πᵢ wᵢ π_{2n-i}`, and
`w'ᵢ v'ᵢ = πᵢ`, `v'ᵢ w'ᵢ = π_{2n-i}`. No module is used, and `ℰ` is only a ring. -/
theorem projecteurs_mem (ℰ : Subring E) (G : Graduation π n) (v w : ℕ → E)
    (hvE : ∀ i ≤ n, v i ∈ ℰ) (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hv : ∀ i ≤ n, Homogene π (2 * ((n : ℤ) - i)) (v i))
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * v i * π i = π i)
    (h₂ : ∀ i ≤ n, v i * w i * π (2 * n - i) = π (2 * n - i)) :
    ∀ a, π a ∈ ℰ := by
  have step : ∀ i : ℕ, i ≤ n + 1 → ∀ a : ℤ, (a < i ∨ 2 * n - i < a) → π a ∈ ℰ := by
    intro i
    induction i with
    | zero =>
      intro _ a ha
      rw [G.supp a (by simp only [Finset.mem_Icc]; omega)]; exact ℰ.zero_mem
    | succ i ih =>
      intro hi
      have hin : i ≤ n := by omega
      have ih := ih (by omega)
      -- φ = ∑_{a ≥ i} π a and ψ = ∑_{a ≤ 2n - i} π a are in ℰ
      set A := (Finset.Icc (0 : ℤ) (2 * n)).filter (fun a : ℤ => ¬ a < (i : ℤ))
      set B := (Finset.Icc (0 : ℤ) (2 * n)).filter (fun a : ℤ => ¬ (2 * n - i : ℤ) < a)
      have hφ : ∑ a ∈ A, π a ∈ ℰ := by
        rw [G.sum_filter_not (fun a : ℤ => a < i)]
        exact ℰ.sub_mem ℰ.one_mem (ℰ.sum_mem fun a ha => ih a (Or.inl (Finset.mem_filter.1 ha).2))
      have hψ : ∑ a ∈ B, π a ∈ ℰ := by
        rw [G.sum_filter_not (fun a : ℤ => (2 * n - i : ℤ) < a)]
        exact ℰ.sub_mem ℰ.one_mem (ℰ.sum_mem fun a ha => ih a (Or.inr (Finset.mem_filter.1 ha).2))
      have hv' : π (2 * n - i) * v i * π i ∈ ℰ := by
        have := sandwich (hv i hin) A B (a₀ := i) (by simp [A]; omega) (by simp [B]; omega)
          (fun a ha hb => by simp [A, B] at ha hb; omega)
        rw [show (i : ℤ) + 2 * ((n : ℤ) - i) = 2 * n - i by ring] at this
        rw [← this]; exact ℰ.mul_mem (ℰ.mul_mem hψ (hvE i hin)) hφ
      have hw' : π i * w i * π (2 * n - i) ∈ ℰ := by
        have := sandwich (hw i hin) B A (a₀ := 2 * n - i) (by simp [B]; omega) (by simp [A]; omega)
          (fun a ha hb => by simp [A, B] at ha hb; omega)
        rw [show (2 * n - i : ℤ) + -(2 * ((n : ℤ) - i)) = i by ring] at this
        rw [← this]; exact ℰ.mul_mem (ℰ.mul_mem hφ (hwE i hin)) hψ
      have hvπ : π (2 * n - i) * v i * π i = v i * π i := by
        rw [G.mul_proj (hv i hin) i, show (i : ℤ) + 2 * ((n : ℤ) - i) = 2 * n - i by ring]
      have hwπ : π i * w i * π (2 * n - i) = w i * π (2 * n - i) := by
        rw [G.mul_proj (hw i hin) (2 * n - i),
          show (2 * n - i : ℤ) + -(2 * ((n : ℤ) - i)) = i by ring]
      have hπi : π i ∈ ℰ := by
        have : (π i * w i * π (2 * n - i)) * (π (2 * n - i) * v i * π i) = π i := by
          calc _ = π i * w i * (π (2 * n - i) * π (2 * n - i) * v i * π i) := by noncomm_ring
            _ = π i * (w i * v i * π i) := by rw [G.idem, hvπ]; noncomm_ring
            _ = π i := by rw [h₁ i hin, G.idem]
        rw [← this]; exact ℰ.mul_mem hw' hv'
      have hπi' : π (2 * n - i) ∈ ℰ := by
        have : (π (2 * n - i) * v i * π i) * (π i * w i * π (2 * n - i)) = π (2 * n - i) := by
          calc _ = π (2 * n - i) * v i * (π i * π i * w i * π (2 * n - i)) := by noncomm_ring
            _ = π (2 * n - i) * (v i * w i * π (2 * n - i)) := by rw [G.idem, hwπ]; noncomm_ring
            _ = π (2 * n - i) := by rw [h₂ i hin, G.idem]
        rw [← this]; exact ℰ.mul_mem hv' hw'
      intro a ha
      push_cast at ha
      rcases lt_trichotomy a i with h | h | h
      · exact ih a (Or.inl h)
      · exact h ▸ hπi
      · rcases lt_trichotomy a (2 * n - i) with h' | h' | h'
        · omega
        · exact h' ▸ hπi'
        · exact ih a (Or.inr h')
  exact fun a => step (n + 1) le_rfl a (by push_cast; omega)

/-- **Page 8 (no. 6, `(6.3)ᵢ`).** The case `vᵢ = L^{n-i}`, `L ∈ ℰ` of degree `2`: one-sided
inverses `wᵢ ∈ ℰ` of `L^{n-i}` (on `πᵢ` and on `π_{2n-i}`) put all the grading projectors
in `ℰ`. -/
theorem projecteurs_mem_lefschetz (ℰ : Subring E) (G : Graduation π n) {L : E} (hLE : L ∈ ℰ)
    (hL : Homogene π 2 L) (w : ℕ → E) (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i)) :
    ∀ a, π a ∈ ℰ :=
  projecteurs_mem ℰ G (fun i => L ^ (n - i)) w (fun _ _ => ℰ.pow_mem hLE _) hwE
    (fun i hi => Nat.cast_sub (R := ℤ) hi ▸ G.homogene_pow hL (n - i)) hw h₁ h₂

end Projecteurs

section Entiers

open ExteriorAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `ι x ι y = -(ι y ι x)`. -/
theorem ι_mul_ι_anticomm {M : Type*} [AddCommGroup M] [Module R M] (x y : M) :
    ι R x * ι R y = -(ι R y * ι R x) :=
  eq_neg_of_add_eq_zero_left (ι_add_mul_swap x y)

/-- A product of two vectors commutes with every vector up to two sign changes. -/
theorem commute_paire_ι {M : Type*} [AddCommGroup M] [Module R M] (x y z : M) :
    Commute (ι R x * ι R y) (ι R z) := by
  show ι R x * ι R y * ι R z = ι R z * (ι R x * ι R y)
  rw [mul_assoc, ι_mul_ι_anticomm y z, mul_neg, ← mul_assoc, ι_mul_ι_anticomm x z, neg_mul,
    neg_neg, mul_assoc]

/-- Two products of two vectors commute. -/
theorem commute_paires {M : Type*} [AddCommGroup M] [Module R M] (x y z t : M) :
    Commute (ι R x * ι R y) (ι R z * ι R t) :=
  (commute_paire_ι x y z).mul_right (commute_paire_ι x y t)

/-- `(x ∧ y)² = 0`. -/
theorem paire_sq {M : Type*} [AddCommGroup M] [Module R M] (x y : M) :
    (ι R x * ι R y) * (ι R x * ι R y) = 0 := by
  rw [← mul_assoc, (commute_paire_ι x y x).eq, ← mul_assoc, ι_sq_zero, zero_mul, zero_mul]

/-- Over any ring, `ξ₀²` is twice an element: the cross terms come in equal pairs. -/
theorem xi₀_sq_two_mul : ∃ c : ExteriorAlgebra R (M₀ R n), xi₀ R n * xi₀ R n = c + c := by
  unfold xi₀
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert k s hk ih =>
    obtain ⟨c, hc⟩ := ih
    set a := ι R (base R n k 0) * ι R (base R n k 1)
    set S := ∑ j ∈ s, ι R (base R n j 0) * ι R (base R n j 1)
    have hcomm : S * a = a * S :=
      (Commute.sum_left _ _ _ fun j _ => commute_paires _ _ _ _).eq
    refine ⟨a * S + c, ?_⟩
    rw [Finset.sum_insert hk, add_mul, mul_add, mul_add, paire_sq, hc, hcomm]
    abel

/-- The basis of `M₀ = ℤ^{2n}` indexed by `Fin (n * 2)`. -/
noncomputable def baseFin : Module.Basis (Fin (n * 2)) R (M₀ R n) :=
  (Pi.basisFun R (Fin n × Fin 2)).reindex finProdFinEquiv

/-- The top exterior product `e₁ ∧ ⋯ ∧ e_{2n}`, a generator of `Λ^{2n} M₀`. -/
noncomputable def vol : ⋀[R]^(n * 2) (M₀ R n) :=
  exteriorPower.ιMulti_family R (n * 2) (baseFin (R := R) (n := n))
    ⟨Finset.univ, by simp⟩

/-- **Page 13, over `ℤ`.** For `n ≥ 2`, the top class of `Λ M₀` is not of the form
`ξ₀ⁿ ∧ y`, whatever `y`: `L₀ⁿ` does not reach `Λ^{2n} M₀` over `ℤ`. -/
theorem not_exists_xi₀_pow_mul_eq_vol (hn : 2 ≤ n) :
    ¬ ∃ y : ExteriorAlgebra ℤ (M₀ ℤ n),
      xi₀ ℤ n ^ n * y = ((vol (R := ℤ) (n := n) : ⋀[ℤ]^(n * 2) (M₀ ℤ n)) :
        ExteriorAlgebra ℤ (M₀ ℤ n)) := by
  rintro ⟨y, hy⟩
  obtain ⟨c, hc⟩ := xi₀_sq_two_mul (R := ℤ) (n := n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  set z := xi₀ ℤ (2 + m) ^ m * c * y
  have h2 : ((vol (R := ℤ) (n := 2 + m)) : ExteriorAlgebra ℤ (M₀ ℤ (2 + m))) = z + z := by
    rw [← hy, show xi₀ ℤ (2 + m) ^ (2 + m) = xi₀ ℤ (2 + m) ^ m * (xi₀ ℤ (2 + m) * xi₀ ℤ (2 + m)) by
      rw [← sq, ← pow_add, add_comm], hc]
    simp only [z]; noncomm_ring
  let φ : ExteriorAlgebra ℤ (M₀ ℤ (2 + m)) → ℤ := fun x =>
    exteriorPower.ιMultiDual ℤ ((2 + m) * 2) (baseFin (R := ℤ) (n := 2 + m)) ⟨Finset.univ, by simp⟩
      (DirectSum.decompose (fun i : ℕ => ⋀[ℤ]^i (M₀ ℤ (2 + m))) x ((2 + m) * 2))
  have hφadd : ∀ x x', φ (x + x') = φ x + φ x' := fun x x' => by
    simp only [φ, DirectSum.decompose_add, DirectSum.add_apply, map_add]
  have hφvol : φ (vol (R := ℤ) (n := 2 + m)) = 1 := by
    simp only [φ]
    have : DirectSum.decompose (fun i : ℕ => ⋀[ℤ]^i (M₀ ℤ (2 + m)))
        ((vol (R := ℤ) (n := 2 + m)) : ExteriorAlgebra ℤ (M₀ ℤ (2 + m))) ((2 + m) * 2) = vol :=
      Subtype.ext (DirectSum.decompose_of_mem_same _ (vol (R := ℤ) (n := 2 + m)).2)
    rw [this]
    exact exteriorPower.ιMultiDual_apply_diag ℤ _ _ _
  have := congrArg φ h2
  rw [hφadd, hφvol] at this
  omega

/-- **Page 13, over `ℤ`: no `Λ₀` of `(6.15)` in `End_ℤ(Λ M₀)` for `n ≥ 2`.** Whatever the map
`w` (in particular `w = Λ₀ⁿ`, which the Remarque of page 12 requires to satisfy
`(L₀ⁿ Λ₀ⁿ - 1) π_{2n} = 0`), `L₀ⁿ (w (vol)) ≠ vol`: `(6.3)₀` fails in the exterior model
over `ℤ`, because `ξ₀ⁿ = n! · vol`. -/
theorem L₀_pow_ne_vol (hn : 2 ≤ n)
    (w : ExteriorAlgebra ℤ (M₀ ℤ n) → ExteriorAlgebra ℤ (M₀ ℤ n)) :
    (L₀ ℤ n)^[n] (w (vol (R := ℤ) (n := n))) ≠ (vol (R := ℤ) (n := n)) := by
  rw [show L₀ ℤ n = (xi₀ ℤ n * ·) from rfl, mul_left_iterate]
  exact fun h => not_exists_xi₀_pow_mul_eq_vol hn ⟨_, h⟩

end Entiers

section Unicite

variable {E : Type*} [Ring E]

/-- **Pages 14–15, « unique quand il existe » (the algebraic step).** A pseudo-inverse `Λ` of
`L` with `ΛLΛ = Λ` is determined by the two idempotents `ΛL` and `LΛ`. -/
theorem pseudo_inverse_unique {L Λ Λ' : E} (h : Λ * L * Λ = Λ) (h' : Λ' * L * Λ' = Λ')
    (hl : Λ * L = Λ' * L) (hr : L * Λ = L * Λ') : Λ = Λ' :=
  calc Λ = Λ * L * Λ := h.symm
    _ = Λ' * (L * Λ) := by rw [hl, mul_assoc]
    _ = Λ' * L * Λ' := by rw [hr, mul_assoc]
    _ = Λ' := h'

end Unicite

section AlgebresHodge

/-- **Page 24, the three data.** An alternating form `φ` on `V`, an alternating bilinear map
`ψ : V × V → W` (i.e. `Λ²V → W`), a symmetric bilinear form `Q` on `W`. -/
structure DonneesHodge (k V W : Type*) [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] where
  /-- the alternating form `φ` on `V` -/
  φ : LinearMap.BilinForm k V
  /-- `ψ : Λ²V → W` -/
  ψ : V →ₗ[k] V →ₗ[k] W
  /-- the symmetric form `Q` on `W` -/
  Q : LinearMap.BilinForm k W
  φ_alt : ∀ x, φ x x = 0
  ψ_alt : ∀ x, ψ x x = 0
  Q_symm : ∀ w w', Q w w' = Q w' w

/-- The graded space `H⁰ ⊕ H¹ ⊕ H² ⊕ H³ ⊕ H⁴ = k ⊕ V ⊕ (kξ ⊕ W) ⊕ V̌ ⊕ kξ²`; an element is
`(a₀, a₁, (c, w), a₃, a₄)`, with `c` the coefficient of `ξ` and `a₄` that of `ξ²`. -/
abbrev AlgHodge (k V W : Type*) [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] :=
  k × V × (k × W) × Module.Dual k V × k

variable {k V W : Type*}

section Anneau

variable [CommRing k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- `H⁰ → A`. -/
def deg0 (c : k) : AlgHodge k V W := (c, 0, (0, 0), 0, 0)
/-- `H¹ = V → A`. -/
def deg1 (x : V) : AlgHodge k V W := (0, x, (0, 0), 0, 0)
/-- `H² = kξ ⊕ W → A`. -/
def deg2 (c : k) (w : W) : AlgHodge k V W := (0, 0, (c, w), 0, 0)
/-- `H³ = V̌ → A`. -/
def deg3 (u : Module.Dual k V) : AlgHodge k V W := (0, 0, (0, 0), u, 0)
/-- `H⁴ = kξ² → A`. -/
def deg4 (c : k) : AlgHodge k V W := (0, 0, (0, 0), 0, c)
/-- The polarisation `ξ ∈ H²`. -/
def xi : AlgHodge k V W := deg2 1 0

namespace DonneesHodge

variable (D : DonneesHodge k V W)

theorem φ_anti (x y : V) : D.φ y x = -D.φ x y := by
  have := D.φ_alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.φ_alt, zero_add, add_zero] at this
  exact eq_neg_of_add_eq_zero_left this

theorem ψ_anti (x y : V) : D.ψ y x = -D.ψ x y := by
  have := D.ψ_alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.ψ_alt, zero_add, add_zero] at this
  exact eq_neg_of_add_eq_zero_left this

theorem Qψ_anti (x y : V) (w : W) : D.Q (D.ψ y x) w = -D.Q (D.ψ x y) w := by
  rw [D.ψ_anti, map_neg, LinearMap.neg_apply]

/-- The product `H¹ × H² → H³`, forced by `⟨t, x h⟩ ξ² = (t x) h`:
`x · (cξ + w) = (t ↦ c φ(t,x) + Q(ψ(t,x), w))`, i.e. `x ξ = φ̃(x)` and `x w = ρ(w,x)`. -/
def act (x : V) (c : k) (w : W) : Module.Dual k V :=
  c • D.φ.flip x + (D.Q.flip w).comp (D.ψ.flip x)

@[simp]
theorem act_apply (x : V) (c : k) (w : W) (t : V) :
    D.act x c w t = c * D.φ t x + D.Q (D.ψ t x) w := by
  simp [act]

/-- **Page 24, the multiplication.** `x y = φ(x,y) ξ + ψ(x,y)` on `H¹ × H¹`, `x h` as in `act`,
`x y' = ⟨x, y'⟩ ξ²` on `H¹ × H³`, `ξ² = ξ²`, `ξ w = 0`, `w w' = Q(w,w') ξ²`, extended by
graded anticommutativity and `H⁰ = k`. -/
def mul (a b : AlgHodge k V W) : AlgHodge k V W :=
  (a.1 * b.1,
   a.1 • b.2.1 + b.1 • a.2.1,
   (a.1 * b.2.2.1.1 + b.1 * a.2.2.1.1 + D.φ a.2.1 b.2.1,
    a.1 • b.2.2.1.2 + b.1 • a.2.2.1.2 + D.ψ a.2.1 b.2.1),
   a.1 • b.2.2.2.1 + b.1 • a.2.2.2.1 + D.act a.2.1 b.2.2.1.1 b.2.2.1.2 +
     D.act b.2.1 a.2.2.1.1 a.2.2.1.2,
   a.1 * b.2.2.2.2 + b.1 * a.2.2.2.2 + a.2.2.1.1 * b.2.2.1.1 + D.Q a.2.2.1.2 b.2.2.1.2 +
     b.2.2.2.1 a.2.1 - a.2.2.2.1 b.2.1)

/-- **Page 24, the products of the reading.** -/
theorem produits (x y : V) (w w' : W) (u : Module.Dual k V) :
    D.mul (deg1 x) (deg1 y) = deg2 (D.φ x y) (D.ψ x y) ∧
      D.mul (deg1 x) xi = deg3 (D.φ.flip x) ∧
      D.mul (deg1 x) (deg2 0 w) = deg3 ((D.Q.flip w).comp (D.ψ.flip x)) ∧
      D.mul (deg1 x) (deg3 u) = deg4 (u x) ∧
      D.mul xi xi = (deg4 1 : AlgHodge k V W) ∧
      D.mul xi (deg2 0 w) = 0 ∧
      D.mul (deg2 0 w) (deg2 0 w') = deg4 (D.Q w w') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [mul, deg1, deg2, deg3, deg4, xi, act]

/-- **Page 24, « les produits restants sont alors forcés ».** The product `H¹ × H² → H³` is
the only one compatible with associativity and the pairing `H¹ × H³ → H⁴`: a `u ∈ V̌` satisfies
`t u = (t x) h` for every `t ∈ V` if and only if `u = x h`. -/
theorem produit_force (x : V) (c : k) (w : W) (u : Module.Dual k V) :
    (∀ t, D.mul (deg1 t) (deg3 u) = D.mul (D.mul (deg1 t) (deg1 x)) (deg2 c w)) ↔
      u = (D.mul (deg1 x) (deg2 c w)).2.2.2.1 := by
  constructor
  · intro h
    ext t
    have := congrArg (fun p => p.2.2.2.2) (h t)
    simp [mul, deg1, deg2, deg3] at this
    simp [mul, deg1, deg2, this]
    ring
  · rintro rfl t
    simp [mul, deg1, deg2, deg3, act, mul_comm]

/-- **Page 24, « on obtient ainsi une loi … unifère ».** -/
theorem one_mul (a : AlgHodge k V W) : D.mul (deg0 1) a = a := by
  obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
  simp [mul, deg0, act]

theorem mul_one (a : AlgHodge k V W) : D.mul a (deg0 1) = a := by
  obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
  simp [mul, deg0, act]

/-- The multiplication is `k`-bilinear. -/
def mulₗ : AlgHodge k V W →ₗ[k] AlgHodge k V W →ₗ[k] AlgHodge k V W :=
  LinearMap.mk₂ k D.mul
    (fun a a' b => by
      obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
      obtain ⟨a0', a1', ⟨ac', aw'⟩, a3', a4'⟩ := a'
      obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
      simp only [mul, Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by ring, by module, ⟨by simp; ring, by simp; module⟩, ?_, by simp; ring⟩
      ext t; simp; ring)
    (fun r a b => by
      obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
      obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
      simp only [mul, Prod.smul_mk, Prod.mk.injEq, smul_eq_mul]
      refine ⟨by ring, by module, ⟨by simp; ring, by simp; module⟩, ?_, by simp; ring⟩
      ext t; simp; ring)
    (fun a b b' => by
      obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
      obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
      obtain ⟨b0', b1', ⟨bc', bw'⟩, b3', b4'⟩ := b'
      simp only [mul, Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by ring, by module, ⟨by simp; ring, by simp; module⟩, ?_, by simp; ring⟩
      ext t; simp; ring)
    (fun r a b => by
      obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
      obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
      simp only [mul, Prod.smul_mk, Prod.mk.injEq, smul_eq_mul]
      refine ⟨by ring, by module, ⟨by simp; ring, by simp; module⟩, ?_, by simp; ring⟩
      ext t; simp; ring)

/-- An element is even if it lies in `H⁰ ⊕ H² ⊕ H⁴`, odd if it lies in `H¹ ⊕ H³`. -/
def Pair (a : AlgHodge k V W) : Prop := a.2.1 = 0 ∧ a.2.2.2.1 = 0

/-- Odd elements. -/
def Impair (a : AlgHodge k V W) : Prop := a.1 = 0 ∧ a.2.2.1 = 0 ∧ a.2.2.2.2 = 0

/-- **Page 24, anticommutativity (1): even elements are central.** -/
theorem mul_comm_of_pair {a : AlgHodge k V W} (ha : Pair a) (b : AlgHodge k V W) :
    D.mul a b = D.mul b a := by
  obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
  obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
  obtain ⟨(rfl : a1 = 0), (rfl : a3 = 0)⟩ := ha
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by abel, ⟨by simp; ring, by simp; abel⟩, ?_, ?_⟩
  · ext t; simp
  · simp [D.Q_symm aw bw]; ring

/-- **Page 24, anticommutativity (2): odd elements anticommute.** -/
theorem mul_anticomm_of_impair {a b : AlgHodge k V W} (ha : Impair a) (hb : Impair b) :
    D.mul a b = -D.mul b a := by
  obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
  obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
  obtain ⟨(rfl : a0 = 0), (h2 : (ac, aw) = 0), (rfl : a4 = 0)⟩ := ha
  obtain ⟨(rfl : b0 = 0), (h2' : (bc, bw) = 0), (rfl : b4 = 0)⟩ := hb
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨rfl, rfl⟩ := h2'
  simp only [mul, Prod.neg_mk, Prod.mk.injEq]
  refine ⟨by ring, by simp, ⟨by simp [D.φ_anti a1 b1], by simp [D.ψ_anti a1 b1]⟩, ?_, ?_⟩
  · ext t; simp
  · simp

/-- **Page 24, anticommutativity (3): odd elements square to zero.** -/
theorem mul_self_of_impair {a : AlgHodge k V W} (ha : Impair a) : D.mul a a = 0 := by
  obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
  obtain ⟨(rfl : a0 = 0), (h2 : (ac, aw) = 0), (rfl : a4 = 0)⟩ := ha
  obtain ⟨rfl, rfl⟩ := h2
  simp [mul, D.φ_alt, D.ψ_alt, act]

/-- The quadrilinear identity of page 24, `(xy)(tz) = (tx)(yz)`. -/
def IdentiteQuadrilineaire : Prop :=
  ∀ x y z t : V, D.φ x y * D.φ t z + D.Q (D.ψ x y) (D.ψ t z) =
    D.φ t x * D.φ y z + D.Q (D.ψ t x) (D.ψ y z)

/-- **Page 24, associativity ⇔ the quadrilinear identity.** Whatever `φ`, `ψ`, `Q`, the
multiplication is associative if and only if
`φ(x,y)φ(t,z) + Q(ψ(x,y), ψ(t,z)) = φ(t,x)φ(y,z) + Q(ψ(t,x), ψ(y,z))`. Only the triple
`H¹ × H¹ × H¹` is not automatic; the others hold by the definition of `act`. -/
theorem assoc_iff :
    (∀ a b c : AlgHodge k V W, D.mul (D.mul a b) c = D.mul a (D.mul b c)) ↔
      D.IdentiteQuadrilineaire := by
  constructor
  · intro H x y z t
    have := congrArg (fun p => p.2.2.2.1 t) (H (deg1 x) (deg1 y) (deg1 z))
    simp [mul, deg1] at this
    linear_combination this + D.Q_symm (D.ψ x y) (D.ψ t z)
  · intro h a b c
    obtain ⟨a0, a1, ⟨ac, aw⟩, a3, a4⟩ := a
    obtain ⟨b0, b1, ⟨bc, bw⟩, b3, b4⟩ := b
    obtain ⟨c0, c1, ⟨cc, cw⟩, c3, c4⟩ := c
    simp only [mul, Prod.mk.injEq]
    refine ⟨by ring, by module, ⟨by simp; ring, by simp; module⟩, ?_, ?_⟩
    · ext t
      simp
      linear_combination h a1 b1 c1 t + D.Q_symm (D.ψ t c1) (D.ψ a1 b1)
    · simp
      linear_combination (-bc) * D.φ_anti c1 a1 - D.Qψ_anti c1 a1 bw -
        ac * D.φ_anti c1 b1 - D.Qψ_anti c1 b1 aw + D.Q_symm (D.ψ b1 c1) aw

/-- `χ(x,y,z,t)`, page 26: `x y z t = χ(x,y,z,t) ξ²` (see `chi_eq`). -/
def chi (x y z t : V) : k := D.φ x y * D.φ z t + D.Q (D.ψ x y) (D.ψ z t)

/-- **Page 26, `x y z t = χ(x,y,z,t) ξ²`**, with the product taken from the left; this holds
whether or not the multiplication is associative. -/
theorem chi_eq (x y z t : V) :
    D.mul (D.mul (D.mul (deg1 x) (deg1 y)) (deg1 z)) (deg1 t) = deg4 (D.chi x y z t) := by
  simp [mul, deg1, deg4, act, chi]
  rw [D.φ_anti t z, D.ψ_anti t z, D.Q_symm]
  simp only [map_neg]
  ring

/-- **Page 26, the quadrilinear form `χ` is alternating** as soon as the multiplication is
associative: it vanishes whenever two of its arguments coincide. -/
theorem chi_alt (h : D.IdentiteQuadrilineaire) (x y z t : V) :
    D.chi x x z t = 0 ∧ D.chi x y y t = 0 ∧ D.chi x y z z = 0 ∧ D.chi x y x t = 0 ∧
      D.chi x y z x = 0 ∧ D.chi x y z y = 0 := by
  have h1 := h x y y t
  have h2 := h x y t x
  have h3 := h x y z x
  have h4 := h x y y z
  simp only [D.φ_alt, D.ψ_alt, map_zero, LinearMap.zero_apply, zero_mul, mul_zero, add_zero] at h1 h2 h3 h4
  refine ⟨by simp [chi, D.φ_alt, D.ψ_alt], ?_, by simp [chi, D.φ_alt, D.ψ_alt], ?_, ?_, ?_⟩
  · simp only [chi]; rw [D.φ_anti t y, D.ψ_anti t y]; simp only [map_neg]; linear_combination -h1
  · simpa only [chi] using h2
  · simp only [chi]; rw [D.φ_anti x z, D.ψ_anti x z]; simp only [map_neg]; linear_combination -h3
  · simpa only [chi] using h4

/-- **Pages 24–26, associativity ⇔ `χ` alternating.** The quadrilinear identity is equivalent
to `χ(x,y,y,t) = 0`: the vanishing in the two other adjacent positions is automatic. -/
theorem identite_iff_chi : D.IdentiteQuadrilineaire ↔ ∀ x y t : V, D.chi x y y t = 0 := by
  refine ⟨fun h x y t => (D.chi_alt h x y y t).2.1, fun g x y z t => ?_⟩
  have pol : ∀ x y z t : V, D.chi x y z t = -D.chi x z y t := by
    intro x y z t
    have := g x (y + z) t
    have g1 := g x y t
    have g2 := g x z t
    simp only [chi, map_add, LinearMap.add_apply] at this g1 g2 ⊢
    linear_combination this - g1 - g2
  have := pol x y t z
  simp only [chi] at this
  linear_combination this - D.φ y z * D.φ_anti x t - D.Qψ_anti x t (D.ψ y z)

end DonneesHodge

end Anneau

section Corps

variable [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- For a symmetric form, non-degenerate means left-separating. -/
theorem nondegenerate_iff_of_symm {M : Type*} [AddCommGroup M] [Module k M]
    (B : LinearMap.BilinForm k M) (hB : ∀ u v, B u v = B v u) :
    B.Nondegenerate ↔ B.SeparatingLeft :=
  ⟨fun h => h.1, fun h => ⟨h, fun y hy => h y fun x => by rw [hB]; exact hy x⟩⟩

namespace DonneesHodge

variable (D : DonneesHodge k V W)

/-- **Page 24, the Lefschetz condition** for `L = ξ ·`: `L² : H⁰ → H⁴` and `L : H¹ → H³` are
isomorphisms (`L⁰ : H² → H²` is the identity). -/
def Lefschetz : Prop :=
  Function.Bijective (fun c : k => (D.mul (D.mul xi xi) (deg0 c)).2.2.2.2) ∧
    Function.Bijective (fun x : V => (D.mul xi (deg1 x)).2.2.2.1)

/-- **Page 24, the Poincaré condition**: the pairings `H⁰ × H⁴`, `H¹ × H³`, `H² × H² → H⁴` are
non-degenerate (on both sides). -/
def Poincare : Prop :=
  (∀ c : k, (∀ d : k, (D.mul (deg0 c) (deg4 d)).2.2.2.2 = 0) → c = 0) ∧
    (∀ d : k, (∀ c : k, (D.mul (deg0 c) (deg4 d)).2.2.2.2 = 0) → d = 0) ∧
    (∀ x : V, (∀ u : Module.Dual k V, (D.mul (deg1 x) (deg3 u)).2.2.2.2 = 0) → x = 0) ∧
    (∀ u : Module.Dual k V, (∀ x : V, (D.mul (deg1 x) (deg3 u)).2.2.2.2 = 0) → u = 0) ∧
    (∀ (c : k) (w : W), (∀ (c' : k) (w' : W), (D.mul (deg2 c w) (deg2 c' w')).2.2.2.2 = 0) →
      c = 0 ∧ w = 0)

/-- **Page 24, « condition de Lefschetz ⇔ `φ` non dégénérée ».** `ξ² : H⁰ → H⁴` is always an
isomorphism, and `ξ : H¹ → H³`, `x ↦ φ(·, x)`, is one iff `φ` is non-degenerate (`V` of finite
dimension). -/
theorem lefschetz_iff [FiniteDimensional k V] : D.Lefschetz ↔ D.φ.Nondegenerate := by
  have e1 : (fun c : k => (D.mul (D.mul xi xi) (deg0 c)).2.2.2.2) = id := by
    funext c; simp [mul, xi, deg2, deg0]
  have e2 : (fun x : V => (D.mul xi (deg1 x)).2.2.2.1) = ⇑(LinearMap.flip D.φ) := by
    funext x; ext t; simp [mul, xi, deg2, deg1]
  rw [Lefschetz, e1, e2]
  have hinj : Function.Injective (LinearMap.flip D.φ) ↔ D.φ.SeparatingRight := by
    rw [← LinearMap.flip_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot,
      LinearMap.ker_eq_bot]
  have hbij : Function.Bijective (LinearMap.flip D.φ) ↔ Function.Injective (LinearMap.flip D.φ) :=
    ⟨fun h => h.1, fun h => ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 h⟩⟩
  have hLR : D.φ.SeparatingRight → D.φ.SeparatingLeft :=
    fun h x hx => h x fun y => by rw [D.φ_anti, hx, neg_zero]
  rw [hbij, hinj]
  exact ⟨fun h => ⟨hLR h.2, h.2⟩, fun h => ⟨Function.bijective_id, h.2⟩⟩

/-- **Page 24, « condition de Poincaré ⇔ `Q` non dégénérée ».** The pairings `H⁰ × H⁴` and
`H¹ × H³` are always perfect, and `H² × H² → H⁴`, `(cξ + w, c'ξ + w') ↦ cc' + Q(w,w')`, is
non-degenerate iff `Q` is. No finiteness is needed. -/
theorem poincare_iff : D.Poincare ↔ D.Q.Nondegenerate := by
  rw [nondegenerate_iff_of_symm _ D.Q_symm]
  have p0 : ∀ c d : k, (D.mul (deg0 c) (deg4 d)).2.2.2.2 = c * d := fun c d => by
    simp [mul, deg0, deg4]
  have p1 : ∀ (x : V) (u : Module.Dual k V), (D.mul (deg1 x) (deg3 u)).2.2.2.2 = u x :=
    fun x u => by simp [mul, deg1, deg3]
  have p2 : ∀ (c c' : k) (w w' : W), (D.mul (deg2 c w) (deg2 c' w')).2.2.2.2 =
      c * c' + D.Q w w' := fun c c' w w' => by simp [mul, deg2]
  simp only [Poincare, p0, p1, p2]
  have a0 : ∀ c : k, (∀ d : k, c * d = 0) → c = 0 := fun c h => by simpa using h 1
  have a0' : ∀ d : k, (∀ c : k, c * d = 0) → d = 0 := fun d h => by simpa using h 1
  have a1 : ∀ x : V, (∀ u : Module.Dual k V, u x = 0) → x = 0 :=
    fun x => (Module.forall_dual_apply_eq_zero_iff k x).1
  have a1' : ∀ u : Module.Dual k V, (∀ x : V, u x = 0) → u = 0 := fun u h => LinearMap.ext h
  refine ⟨fun h w hw => ?_, fun h => ⟨a0, a0', a1, a1', fun c w hcw => ?_⟩⟩
  · exact (h.2.2.2.2 0 w fun c' w' => by simp [hw w']).2
  · have hc : c = 0 := by simpa using hcw 1 0
    subst hc
    exact ⟨rfl, h w fun w' => by simpa using hcw 0 w'⟩

end DonneesHodge

/-- **Page 26, the reformulation `(V, χ, (W̃, Q̃, α), ξ)`.** From a symmetric form `Q̃` on
`W̃`, an alternating `α : Λ²V → W̃` and `ξ ∈ W̃` with `Q̃(ξ,ξ) = 1`, the data of page 24 are
recovered with `W = ξ^⊥`, `φ(x,y) = Q̃(α(x∧y), ξ)`, `ψ = α - φ ξ` and `Q = Q̃|_W`. -/
def reformulation {W' : Type*} [AddCommGroup W'] [Module k W']
    (Q' : LinearMap.BilinForm k W') (hQ' : ∀ u v, Q' u v = Q' v u)
    (α : V →ₗ[k] V →ₗ[k] W') (hα : ∀ x, α x x = 0) (ξ' : W') (hξ : Q' ξ' ξ' = 1) :
    DonneesHodge k V (LinearMap.ker (Q' ξ')) where
  φ := α.compr₂ (Q' ξ')
  ψ := LinearMap.mk₂ k (fun x y => ⟨α x y - Q' ξ' (α x y) • ξ', by simp [hξ]⟩)
    (fun x x' y => Subtype.ext (by simp; module))
    (fun r x y => Subtype.ext (by simp [smul_sub, smul_smul]))
    (fun x y y' => Subtype.ext (by simp; module))
    (fun r x y => Subtype.ext (by simp [smul_sub, smul_smul]))
  Q := Q'.restrict _
  φ_alt x := by simp [hα]
  ψ_alt x := Subtype.ext (by simp [hα])
  Q_symm w w' := hQ' _ _

section Reformulation

variable {W' : Type*} [AddCommGroup W'] [Module k W']
    (Q' : LinearMap.BilinForm k W') (hQ' : ∀ u v, Q' u v = Q' v u)
    (α : V →ₗ[k] V →ₗ[k] W') (hα : ∀ x, α x x = 0) (ξ' : W') (hξ : Q' ξ' ξ' = 1)

/-- **Page 26.** In the reformulation: `φ(x,y) = Q̃(α(x∧y), ξ)`, `α = φ ξ + ψ`, `χ` is
`Q̃(α(x∧y), α(z∧t))` — so associativity reads `Q̃(α(x∧y), α(y∧t)) = 0`, the compatibility of
`α` with `χ'` — and the two non-degeneracy conditions become « `Q̃` non dégénérée » and
« `φ` non dégénérée ». -/
theorem reformulation_spec [FiniteDimensional k V] :
    let D := reformulation Q' hQ' α hα ξ' hξ
    (∀ x y, D.φ x y = Q' (α x y) ξ') ∧
      (∀ x y, α x y = D.φ x y • ξ' + (D.ψ x y : W')) ∧
      (∀ x y z t, Q' (α x y) (α z t) = D.chi x y z t) ∧
      ((∀ a b c : AlgHodge k V _, D.mul (D.mul a b) c = D.mul a (D.mul b c)) ↔
        ∀ x y t, Q' (α x y) (α y t) = 0) ∧
      (D.Lefschetz ↔ D.φ.Nondegenerate) ∧
      (D.Poincare ↔ Q'.Nondegenerate) := by
  intro D
  have hφ : ∀ x y, D.φ x y = Q' (α x y) ξ' := fun x y => by
    simp [D, reformulation, hQ' ξ']
  have hdec : ∀ x y, α x y = D.φ x y • ξ' + (D.ψ x y : W') := fun x y => by
    simp [D, reformulation]
  have hchi : ∀ x y z t, Q' (α x y) (α z t) = D.chi x y z t := fun x y z t => by
    simp only [DonneesHodge.chi]
    conv_lhs => rw [hdec x y, hdec z t]
    have h1 : Q' ξ' (D.ψ z t : W') = 0 := (D.ψ z t).2
    have h2 : Q' (D.ψ x y : W') ξ' = 0 := (hQ' _ _).trans (D.ψ x y).2
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hξ, h1,
      h2]
    simp [D, reformulation]
    ring
  refine ⟨hφ, hdec, hchi, ?_, D.lefschetz_iff, ?_⟩
  · rw [D.assoc_iff, D.identite_iff_chi]
    simp only [hchi]
  · rw [D.poincare_iff, nondegenerate_iff_of_symm _ D.Q_symm, nondegenerate_iff_of_symm _ hQ']
    constructor
    · intro h v hv
      have hvk : v ∈ LinearMap.ker (Q' ξ') := (hQ' ξ' v).trans (hv ξ')
      have := h ⟨v, hvk⟩ fun w => by simp [D, reformulation, hv]
      simpa using congrArg Subtype.val this
    · intro h w hw
      have hw' : Q' ξ' (w : W') = 0 := w.2
      refine Subtype.ext (h w fun v => ?_)
      have hv : v - Q' ξ' v • ξ' ∈ LinearMap.ker (Q' ξ') := by simp [hξ]
      have := hw ⟨_, hv⟩
      simp [D, reformulation] at this
      rwa [hQ' (w : W') ξ', hw', mul_zero, sub_zero] at this

end Reformulation

end Corps

end AlgebresHodge

section DecompositionPrimitive

/-! ### No. 6, pages 8–12: `Λ` and the primitive projectors in `ℰ`

Finding `16-graded-ring-lefschetz-criterion`. The folder takes the primitive decomposition
as known (« la décomposition primitive y est admise ») and computes, from the inverses `wⱼ`
of `L^{n-j}`, each of its projectors and `Λ` as polynomials in `L`, the `wⱼ` and the `πₐ`.
The decomposition is read here inside the ring `E`, with no module: `p j β` is the projector
onto `L^β P^j ⊂ M^{j+2β}` (`j ≤ n`, `β ≤ n - j`), so that the reading's `π_{i,α}` is
`p (i-2α) α` for `i ≤ n` and `π_{2n-i,α}` is `p (i-2α) (n-i+α)`. -/

variable {E : Type*} [Ring E] {π : ℤ → E} {n : ℕ}

theorem homogene_congr {d d' : ℤ} (h : d = d') {x : E} (hx : Homogene π d x) :
    Homogene π d' x := h ▸ hx

theorem homogene_sum {ι : Type*} (s : Finset ι) {d : ℤ} {f : ι → E}
    (h : ∀ i ∈ s, Homogene π d (f i)) : Homogene π d (∑ i ∈ s, f i) := by
  intro a b hab
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_eq_zero fun i hi => h i hi a b hab

/-- The primitive decomposition `M^a = ⊕ L^β P^j` (`j + 2β = a`), read in the ring `E`:
orthogonal idempotents `p j β` of sum `1`, `p j β` living in degree `j + 2β`, `L` carrying
the block `(j, β)` to `(j, β + 1)` and killing the top `(j, n - j)` of each chain, and the
image of `p j β` contained in `L^β` times the image of `p j 0` (`L^β P^j`, not merely a
complement). -/
structure DecompositionPrimitive (π : ℤ → E) (n : ℕ) (L : E) (p : ℕ → ℕ → E) : Prop where
  idem : ∀ j ≤ n, ∀ β ≤ n - j, p j β * p j β = p j β
  orth : ∀ j ≤ n, ∀ β ≤ n - j, ∀ k ≤ n, ∀ γ ≤ n - k, (j, β) ≠ (k, γ) → p j β * p k γ = 0
  sum : ∑ j ∈ Finset.range (n + 1), ∑ β ∈ Finset.range (n - j + 1), p j β = 1
  left : ∀ j ≤ n, ∀ β ≤ n - j, ∀ a : ℤ,
    π a * p j β = if a = (j : ℤ) + 2 * β then p j β else 0
  right : ∀ j ≤ n, ∀ β ≤ n - j, ∀ a : ℤ,
    p j β * π a = if a = (j : ℤ) + 2 * β then p j β else 0
  comm : ∀ j ≤ n, ∀ β < n - j, L * p j β = p j (β + 1) * L
  top : ∀ j ≤ n, L * p j (n - j) = 0
  image : ∀ j ≤ n, ∀ β ≤ n - j, ∃ y, p j β = L ^ β * p j 0 * y

/-- The pseudo-inverse of pages 11–12, block by block:
`Λ = ∑_j ∑_{β < n-j} L^β wⱼ L^{n-j-β-1} p_{j,β+1}`, and `Λ` kills the bottoms `p j 0`. -/
def pseudoInverse (n : ℕ) (L : E) (w : ℕ → E) (p : ℕ → ℕ → E) : E :=
  ∑ j ∈ Finset.range (n + 1), ∑ β ∈ Finset.range (n - j),
    L ^ β * w j * L ^ (n - j - (β + 1)) * p j (β + 1)

namespace DecompositionPrimitive

variable {L : E} {p : ℕ → ℕ → E} (D : DecompositionPrimitive π n L p)
include D

theorem pow_mul_of_le {j β k : ℕ} (hj : j ≤ n) (h : β + k ≤ n - j) :
    L ^ k * p j β = p j (β + k) * L ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc L ^ (k + 1) * p j β = L * (L ^ k * p j β) := by rw [pow_succ', mul_assoc]
      _ = L * p j (β + k) * L ^ k := by rw [ih (by omega), mul_assoc]
      _ = p j (β + k + 1) * (L * L ^ k) := by rw [D.comm j hj (β + k) (by omega), mul_assoc]
      _ = _ := by rw [← pow_succ', add_assoc]

theorem pow_mul_eq_zero {j β k : ℕ} (hj : j ≤ n) (hβ : β ≤ n - j) (h : n - j < β + k) :
    L ^ k * p j β = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + (n - j - β) := ⟨k - 1 - (n - j - β), by omega⟩
  calc L ^ (m + 1 + (n - j - β)) * p j β = L ^ m * (L * p j (n - j)) * L ^ (n - j - β) := by
        rw [pow_add, mul_assoc, D.pow_mul_of_le hj (by omega : β + (n - j - β) ≤ n - j),
          show β + (n - j - β) = n - j by omega, pow_succ]
        simp only [mul_assoc]
    _ = 0 := by rw [D.top j hj, mul_zero, zero_mul]

/-- The bottom `p j 0` projects onto primitive classes: `L^{n-j+1} p_{j,0} = 0`. -/
theorem primitif {j : ℕ} (hj : j ≤ n) : L ^ (n - j + 1) * p j 0 = 0 :=
  D.pow_mul_eq_zero hj (Nat.zero_le _) (by omega)

theorem homogene_zero {j β : ℕ} (hj : j ≤ n) (hβ : β ≤ n - j) : Homogene π 0 (p j β) := by
  intro a b hab
  rw [D.left j hj β hβ b]
  split_ifs with h
  · rw [D.right j hj β hβ a, ite_eq_right (by omega)]
  · rw [zero_mul]

/-- The key computation of page 11: on `L^β P^j`, `L^β wⱼ L^{n-j-β}` is the identity. -/
theorem inverse_bloc {w : ℕ → E} (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    {j β : ℕ} (hj : j ≤ n) (hβ : β ≤ n - j) :
    L ^ β * w j * L ^ (n - j - β) * p j β = p j β := by
  obtain ⟨y, hy⟩ := D.image j hj β hβ
  have hp0 : π j * p j 0 = p j 0 := by simp [D.left j hj 0 (Nat.zero_le _)]
  have e : L ^ (n - j - β) * L ^ β = L ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [hy]
  calc L ^ β * w j * L ^ (n - j - β) * (L ^ β * p j 0 * y)
      = L ^ β * (w j * (L ^ (n - j - β) * L ^ β) * π j * p j 0) * y := by
        rw [mul_assoc _ (π (j : ℤ)), hp0]; simp only [mul_assoc]
    _ = L ^ β * p j 0 * y := by rw [e, h₁ j hj, hp0]

/-- **Page 11, formula (6.9).** Below the middle (`j + 2β ≤ n`), with `α = β`, `i = j + 2β`:
`π_{i,α} = L^α w_{i-2α} L^{n-i+α} πᵢ (1 - ∑_{α' > α} π_{i,α'})`; the sum is written over all
blocks with a smaller primitive degree, `πᵢ` keeping those of degree `i`. -/
theorem formule_bas {w : ℕ → E} (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    {j β : ℕ} (hj : j ≤ n) (hjβ : j + 2 * β ≤ n) :
    p j β = L ^ β * w j * L ^ (n - j - β) * π ((j : ℤ) + 2 * β) *
      (1 - ∑ j' ∈ Finset.range j, ∑ β' ∈ Finset.range (n - j' + 1), p j' β') := by
  have hβ : β ≤ n - j := by omega
  have hS : 1 - ∑ j' ∈ Finset.range j, ∑ β' ∈ Finset.range (n - j' + 1), p j' β' =
      ∑ j' ∈ Finset.Ico j (n + 1), ∑ β' ∈ Finset.range (n - j' + 1), p j' β' := by
    rw [← D.sum, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ n + 1)]; abel
  have key : L ^ (n - j - β) * π ((j : ℤ) + 2 * β) *
      (∑ j' ∈ Finset.Ico j (n + 1), ∑ β' ∈ Finset.range (n - j' + 1), p j' β') =
      L ^ (n - j - β) * p j β := by
    rw [Finset.mul_sum, Finset.sum_eq_single j]
    · rw [Finset.mul_sum, Finset.sum_eq_single β]
      · rw [mul_assoc, D.left j hj β hβ, ite_eq_left rfl]
      · intro β' hβ' hne
        rw [Finset.mem_range] at hβ'
        rw [mul_assoc, D.left j hj β' (by omega), ite_eq_right (by omega), mul_zero]
      · exact fun h => absurd (Finset.mem_range.2 (by omega)) h
    · intro j' hj' hne
      rw [Finset.mem_Ico] at hj'
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun β' hβ' => ?_
      rw [Finset.mem_range] at hβ'
      rw [mul_assoc, D.left j' (by omega) β' (by omega)]
      split_ifs with h
      · exact D.pow_mul_eq_zero (by omega) (by omega) (by omega)
      · rw [mul_zero]
    · exact fun h => absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) h
  rw [hS]
  have h' := congrArg (fun x => L ^ β * w j * x) key
  have K := D.inverse_bloc h₁ hj hβ
  simp only [mul_assoc] at h' K ⊢
  rw [h', K]

/-- **Page 11, formula (6.10).** Above the middle (`n ≤ j + 2β`), with `i = 2n - j - 2β`:
`π_{2n-i,α} = L^{n-i} π_{i,α} wᵢ π_{2n-i}`. -/
theorem formule_haut {w : ℕ → E}
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i))
    {j β : ℕ} (hj : j ≤ n) (hβ : β ≤ n - j) (hn : n ≤ j + 2 * β) :
    p j β = L ^ (j + 2 * β - n) * p j (n - j - β) * w (j + 2 * (n - j - β)) *
      π ((j : ℤ) + 2 * β) := by
  have h := h₂ (j + 2 * (n - j - β)) (by omega)
  rw [show n - (j + 2 * (n - j - β)) = j + 2 * β - n by omega,
    show (2 * n - ((j + 2 * (n - j - β) : ℕ) : ℤ)) = (j : ℤ) + 2 * β by omega] at h
  calc p j β = p j β * π ((j : ℤ) + 2 * β) := by rw [D.right j hj β hβ, ite_eq_left rfl]
    _ = p j β * (L ^ (j + 2 * β - n) * w (j + 2 * (n - j - β)) * π ((j : ℤ) + 2 * β)) := by
        rw [h]
    _ = _ := by
        rw [D.pow_mul_of_le (β := n - j - β) (k := j + 2 * β - n) hj (by omega),
          show n - j - β + (j + 2 * β - n) = β by omega]
        simp only [mul_assoc]

/-- **Pages 10–11 (no. 6), (1) ⇒ (3), over `ℤ` and with no module.** If `L ∈ ℰ` has degree `2`
and the one-sided inverses `wᵢ` of `L^{n-i}` of `(6.3)` lie in `ℰ`, every projector of the
primitive decomposition lies in `ℰ`. Induction on the primitive degree `j` (the folder's
descending induction on `α`), through `formule_bas` and `formule_haut`. -/
theorem projecteurs_primitifs_mem (ℰ : Subring E) (G : Graduation π n) (hLE : L ∈ ℰ)
    (hL : Homogene π 2 L) {w : ℕ → E} (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i)) :
    ∀ j ≤ n, ∀ β ≤ n - j, p j β ∈ ℰ := by
  have hπ := projecteurs_mem_lefschetz ℰ G hLE hL w hwE hw h₁ h₂
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hS : (1 - ∑ j' ∈ Finset.range j, ∑ β' ∈ Finset.range (n - j' + 1), p j' β') ∈ ℰ :=
      ℰ.sub_mem ℰ.one_mem (ℰ.sum_mem fun j' hj' => ℰ.sum_mem fun β' hβ' => by
        rw [Finset.mem_range] at hj' hβ'
        exact ih j' hj' (by omega) β' (by omega))
    have bas : ∀ β, j + 2 * β ≤ n → p j β ∈ ℰ := fun β hβ => by
      rw [D.formule_bas h₁ hj hβ]
      exact ℰ.mul_mem (ℰ.mul_mem (ℰ.mul_mem (ℰ.mul_mem (ℰ.pow_mem hLE _) (hwE j hj))
        (ℰ.pow_mem hLE _)) (hπ _)) hS
    intro β hβ
    by_cases hn : j + 2 * β ≤ n
    · exact bas β hn
    · rw [D.formule_haut h₂ hj hβ (by omega)]
      exact ℰ.mul_mem (ℰ.mul_mem (ℰ.mul_mem (ℰ.pow_mem hLE _) (bas _ (by omega)))
        (hwE _ (by omega))) (hπ _)

/-- **Page 9, `(6.7)`, first relation.** `LΛ = 1 - ∑_{0 ≤ i ≤ n} π_{i,0}`. -/
theorem mul_pseudoInverse {w : ℕ → E} (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i) :
    L * pseudoInverse n L w p = 1 - ∑ j ∈ Finset.range (n + 1), p j 0 := by
  rw [eq_sub_iff_add_eq, ← D.sum]
  simp only [pseudoInverse]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [Finset.mem_range] at hβ
  have K := D.inverse_bloc h₁ (by omega : j ≤ n) (by omega : β + 1 ≤ n - j)
  rw [pow_succ'] at K
  simpa only [mul_assoc] using K

/-- **Page 9, `(6.7)`, second relation.** `ΛL = 1 - ∑_{n ≤ i ≤ 2n} π_{i,0}`, the tops of the
chains. -/
theorem pseudoInverse_mul {w : ℕ → E} (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i) :
    pseudoInverse n L w p * L = 1 - ∑ j ∈ Finset.range (n + 1), p j (n - j) := by
  rw [eq_sub_iff_add_eq, ← D.sum]
  simp only [pseudoInverse]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Finset.sum_range_succ, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [Finset.mem_range] at hβ
  rw [mul_assoc _ (p j (β + 1)) L, ← D.comm j (by omega) β hβ]
  calc _ = L ^ β * w j * (L ^ (n - j - (β + 1)) * L) * p j β := by simp only [mul_assoc]
    _ = p j β := by
      rw [← pow_succ, show n - j - (β + 1) + 1 = n - j - β by omega,
        D.inverse_bloc h₁ (by omega) (by omega)]

theorem homogene_pseudoInverse (G : Graduation π n) (hL : Homogene π 2 L) {w : ℕ → E}
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i)) :
    Homogene π (-2) (pseudoInverse n L w p) := by
  refine homogene_sum _ fun j hj => homogene_sum _ fun β hβ => ?_
  rw [Finset.mem_range] at hj hβ
  exact homogene_congr (by omega) (G.homogene_mul (G.homogene_mul (G.homogene_mul
    (G.homogene_pow hL β) (hw j (by omega))) (G.homogene_pow hL _))
    (D.homogene_zero (β := β + 1) (by omega) (by omega)))

end DecompositionPrimitive

/-- **Pages 4–12, the criterion of no. 6, (1) ⇒ (2) and (3), over `ℤ` and with no module**
(finding `16-graded-ring-lefschetz-criterion`). In a ring `E` graded by orthogonal idempotents
`π_a` (`a ∈ [0, 2n]`), let `ℰ` be a subring containing `L` of degree `2` and one-sided inverses
`wᵢ` of `L^{n-i}` (`(6.3)ᵢ`), and let `p` be the primitive decomposition, read in `E`. Then the
grading projectors, every primitive projector and the pseudo-inverse `Λ` lie in `ℰ`; `Λ` has
degree `-2` and satisfies `(6.7)`. -/
theorem critere_lefschetz (ℰ : Subring E) (G : Graduation π n) {L : E} (hLE : L ∈ ℰ)
    (hL : Homogene π 2 L) {w : ℕ → E} (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i))
    {p : ℕ → ℕ → E} (D : DecompositionPrimitive π n L p) :
    (∀ a, π a ∈ ℰ) ∧ (∀ j ≤ n, ∀ β ≤ n - j, p j β ∈ ℰ) ∧
      ∃ Λ ∈ ℰ, Homogene π (-2) Λ ∧
        L * Λ = 1 - ∑ j ∈ Finset.range (n + 1), p j 0 ∧
        Λ * L = 1 - ∑ j ∈ Finset.range (n + 1), p j (n - j) := by
  have hp := D.projecteurs_primitifs_mem ℰ G hLE hL hwE hw h₁ h₂
  refine ⟨projecteurs_mem_lefschetz ℰ G hLE hL w hwE hw h₁ h₂, hp,
    pseudoInverse n L w p, ?_, D.homogene_pseudoInverse G hL hw, D.mul_pseudoInverse h₁,
    D.pseudoInverse_mul h₁⟩
  refine ℰ.sum_mem fun j hj => ℰ.sum_mem fun β hβ => ?_
  rw [Finset.mem_range] at hj hβ
  exact ℰ.mul_mem (ℰ.mul_mem (ℰ.mul_mem (ℰ.pow_mem hLE _) (hwE j (by omega)))
    (ℰ.pow_mem hLE _)) (hp j (by omega) (β + 1) (by omega))

end DecompositionPrimitive

end Grothendieck.Folder16

/-! ### No. 6, page 9: the converse (3) ⇒ (1)

The theorem of page 9 states (1) ⇔ (2) ⇔ (3), with (1) « the Lefschetz conditions `(6.1)ᵢ`,
`(6.2)ᵢ` (the inverse of `L^{n-i}` in `ℰ`) hold and the `πᵢ` are in `ℰ` » and (3) « every
projector `π_{i,α}` of the primitive decomposition is in `ℰ` »; page 12 marks one implication
« Démonstration à fournir ». Of (3) ⇒ (1), only the projectors follow:
`projecteurs_mem_of_primitifs` puts every `π_a` in `ℰ` (`π_a` is the sum of the blocks of
degree `a`). The inverses do not: `reciproque_trois_un_fausse` is a ring `E = M₂(R)`, `n = 1`,
`L = e₂₁`, in which the decomposition and the inverse of `L` exist in `E` and every projector
lies in the subring `ℰ` of lower-triangular matrices, but no `w ∈ ℰ` has `w L π₀ = π₀` and no
`Λ ∈ ℰ` has `LΛ = 1 - ∑ p_{j,0}`: (3) implies neither (1) nor (2). -/

namespace Grothendieck.Folder16

section Reciproque

variable {E : Type*} [Ring E] {π : ℤ → E} {n : ℕ} {L : E} {p : ℕ → ℕ → E}

/-- `π_a` is the sum of the primitive blocks of degree `a`. -/
theorem DecompositionPrimitive.proj_eq_sum (D : DecompositionPrimitive π n L p) (a : ℤ) :
    π a = ∑ j ∈ Finset.range (n + 1), ∑ β ∈ Finset.range (n - j + 1),
      if a = (j : ℤ) + 2 * β then p j β else 0 := by
  rw [← mul_one (π a), ← D.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [Finset.mem_range] at hj hβ
  exact D.left j (by omega) β (by omega) a

/-- **Page 9, (3) ⇒ (1), the projectors.** If every primitive projector `p_{j,β}` lies in the
subring `ℰ`, so does every grading projector `π_a`. -/
theorem projecteurs_mem_of_primitifs (ℰ : Subring E) (D : DecompositionPrimitive π n L p)
    (hp : ∀ j ≤ n, ∀ β ≤ n - j, p j β ∈ ℰ) (a : ℤ) : π a ∈ ℰ := by
  rw [D.proj_eq_sum a]
  refine ℰ.sum_mem fun j hj => ℰ.sum_mem fun β hβ => ?_
  rw [Finset.mem_range] at hj hβ
  split_ifs
  · exact hp j (by omega) β (by omega)
  · exact ℰ.zero_mem

end Reciproque

section ContreExemple

/-- Entrywise check of a `2 × 2` matrix identity. -/
local macro "mat" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]))

variable (R : Type*) [CommRing R]

/-- The lower-triangular matrices, a subring of `M₂(R)`. -/
def triInf : Subring (Matrix (Fin 2) (Fin 2) R) where
  carrier := {M | M 0 1 = 0}
  mul_mem' {A B} hA hB := by
    simp_all [Matrix.mul_apply, Fin.sum_univ_two]
  one_mem' := by simp
  add_mem' {A B} hA hB := by simp_all
  zero_mem' := by simp
  neg_mem' {A} hA := by simp_all

/-- The grading of the counterexample: `M⁰ = R e₁`, `M² = R e₂`, `M¹ = 0`. -/
def πc : ℤ → Matrix (Fin 2) (Fin 2) R := fun a =>
  if a = 0 then !![1, 0; 0, 0] else if a = 2 then !![0, 0; 0, 1] else 0

/-- `L = e₂₁`, `e₁ ↦ e₂`. -/
def Lc : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

/-- The primitive decomposition: `P⁰ = R e₁`, `L P⁰ = R e₂`, `P¹ = 0`. -/
def pc : ℕ → ℕ → Matrix (Fin 2) (Fin 2) R := fun j β =>
  if j = 0 ∧ β = 0 then !![1, 0; 0, 0] else if j = 0 ∧ β = 1 then !![0, 0; 0, 1] else 0

/-- The inverse of `L : M⁰ → M²` in `E`, `e₂ ↦ e₁`; it is not lower-triangular. -/
def wc : ℕ → Matrix (Fin 2) (Fin 2) R := fun i => if i = 0 then !![0, 1; 0, 0] else 0

theorem graduation_c : Graduation (πc R) 1 where
  idem a := by unfold πc; split_ifs <;> mat
  orth a b h := by unfold πc; split_ifs <;> first | omega | mat
  supp a ha := by
    simp only [Finset.mem_Icc, Nat.cast_one, mul_one] at ha
    simp only [πc]; split_ifs <;> first | omega | rfl
  sum := by
    rw [show Finset.Icc (0 : ℤ) (2 * (1 : ℕ)) = {0, 1, 2} by decide]
    simp only [πc]; mat

theorem homogene_Lc : Homogene (πc R) 2 (Lc R) := by
  intro a b hab
  unfold πc Lc; split_ifs <;> first | omega | mat

theorem decomposition_c : DecompositionPrimitive (πc R) 1 (Lc R) (pc R) where
  idem j hj β hβ := by unfold pc; split_ifs <;> mat
  orth j hj β hβ k hk γ hγ h := by
    unfold pc; split_ifs <;> first | (exfalso; apply h; ext <;> simp <;> omega) |
      mat
  sum := by simp only [Finset.sum_range_succ, pc]; mat
  left j hj β hβ a := by
    unfold πc pc; split_ifs <;> first | omega | mat
  right j hj β hβ a := by
    unfold πc pc; split_ifs <;> first | omega | mat
  comm j hj β hβ := by
    obtain rfl : j = 0 := by omega
    obtain rfl : β = 0 := by omega
    simp only [pc, Lc]; mat
  top j hj := by
    interval_cases j <;> (simp only [pc, Lc]; mat)
  image j hj β hβ := by
    interval_cases j
    · interval_cases β
      · exact ⟨1, by simp⟩
      · exact ⟨!![0, 1; 0, 0], by simp only [pc, Lc]; mat⟩
    · obtain rfl : β = 0 := by omega
      exact ⟨0, by simp [pc]⟩

/-- **Page 9, (3) ⇏ (1) and (3) ⇏ (2).** In `E = M₂(R)` (`R` any nonzero commutative ring,
`ℤ` included), with `n = 1`, `L = e₂₁` of degree `2`: the primitive decomposition holds in `E`,
`L : M⁰ → M²` has an inverse of degree `-2` in `E` (`(6.3)` holds in `E`), and `L`, every
grading projector and every primitive projector lie in the subring `ℰ` of lower-triangular
matrices; yet no `w ∈ ℰ` satisfies `w L π₀ = π₀` (`(6.3)₀` fails in `ℰ`) and no `Λ ∈ ℰ`
satisfies the first relation of `(6.7)`. -/
theorem reciproque_trois_un_fausse [Nontrivial R] :
    ∃ (π : ℤ → Matrix (Fin 2) (Fin 2) R) (L : Matrix (Fin 2) (Fin 2) R)
      (p : ℕ → ℕ → Matrix (Fin 2) (Fin 2) R) (ℰ : Subring (Matrix (Fin 2) (Fin 2) R)),
      Graduation π 1 ∧ Homogene π 2 L ∧ DecompositionPrimitive π 1 L p ∧
      (∃ w : ℕ → Matrix (Fin 2) (Fin 2) R,
        (∀ i : ℕ, i ≤ 1 → Homogene π (-(2 * ((1 : ℕ) - (i : ℤ)))) (w i)) ∧
        (∀ i ≤ 1, w i * L ^ (1 - i) * π i = π i) ∧
        (∀ i ≤ 1, L ^ (1 - i) * w i * π (2 * 1 - i) = π (2 * 1 - i))) ∧
      L ∈ ℰ ∧ (∀ a, π a ∈ ℰ) ∧ (∀ j ≤ 1, ∀ β ≤ 1 - j, p j β ∈ ℰ) ∧
      (¬ ∃ w ∈ ℰ, w * L ^ (1 - 0) * π 0 = π 0) ∧
      (¬ ∃ Λ ∈ ℰ, L * Λ = 1 - ∑ j ∈ Finset.range (1 + 1), p j 0) := by
  refine ⟨πc R, Lc R, pc R, triInf R, graduation_c R, homogene_Lc R, decomposition_c R,
    ⟨wc R, ?_, ?_, ?_⟩, show Lc R 0 1 = 0 by simp [Lc], ?_, ?_, ?_, ?_⟩
  · intro i hi a b hab
    interval_cases i
    · unfold πc wc; split_ifs <;> first | omega | mat
    · simp [wc]
  · intro i hi
    interval_cases i <;> (simp only [πc, wc, Lc]; mat)
  · intro i hi
    interval_cases i
    · simp only [πc, wc, Lc]; mat
    · simp [πc, wc]
  · exact fun a => by show πc R a 0 1 = 0; unfold πc; split_ifs <;> simp
  · exact fun j _ β _ => by show pc R j β 0 1 = 0; unfold pc; split_ifs <;> simp
  · rintro ⟨w, hw, h⟩
    have h01 : w 0 1 = 0 := hw
    have := congrFun (congrFun h 0) 0
    simp [πc, Lc, Matrix.mul_apply, Fin.sum_univ_two, h01] at this
  · rintro ⟨Λ, hΛ, h⟩
    have h01 : Λ 0 1 = 0 := hΛ
    have := congrFun (congrFun h 1) 1
    simp [pc, Lc, Matrix.mul_apply, Fin.sum_univ_two, h01] at this

end ContreExemple


/-!
## Page 49: splitting the critical Lefschetz condition (the edition's reconstruction)

Page 49 of the letter to Coates factors the critical Lefschetz operator through a hyperplane
section `φ : Y → X` and splits the critical condition `A⁰(X)` into a restriction condition
`A'⁰` and a Gysin condition `A''⁰`. The statements below are the edition's reconstruction
(problems paper, Problem 5), in abstract linear algebra: cohomology groups are `k`-modules, the
algebraic classes are submodules `a…`, `res` is `φ^*`, `gys` is `φ_*`.

* `split_even` (`dim X = 2m`): with `L² = φ_* ∘ L_Y ∘ φ^*`, `φ^*` onto in degree `2m − 2` and
  `L_Y : H^{2m-2}(Y) ≃ H^{2m}(Y)`, the conditions `A''⁰(X)` (every algebraic class of
  `H^{2m+2}(X)` is `φ_*` of an algebraic class), `A⁰(Y)` (`L_Y⁻¹` keeps algebraic classes) and
  `A'⁰(X)` (`x` is algebraic when `φ^* x` is) put every algebraic class of `H^{2m+2}(X)` in
  `L²` of the algebraic classes of `H^{2m-2}(X)`.
* `split_odd` (`dim X = 2m + 1`): with `L = φ_* ∘ φ^*` invertible, the same conclusion follows
  from `A''⁰`, `A'⁰` and the condition that the projection `p = φ^* L⁻¹ φ_*` keeps algebraic
  classes; `split_odd_circular`: that condition already follows from `A⁰(X)` itself, so in odd
  dimension the splitting is a reformulation.

Not formalised: weak and hard Lefschetz, Weil cohomologies, and whether `A⁰(Y_T)` is supplied
on a hyperplane section of `X × X`, which is the open point of Problem 5.
-/

section Scission

variable {k H₂ H₄ G₂ G₄ : Type*} [Field k]
  [AddCommGroup H₂] [Module k H₂] [AddCommGroup H₄] [Module k H₄]
  [AddCommGroup G₂] [Module k G₂] [AddCommGroup G₄] [Module k G₄]

/-- Page 49, even dimension (the edition's reconstruction): `A''⁰(X) + A⁰(Y) + A'⁰(X)` puts the
algebraic classes of `H^{2m+2}(X)` in `L² = φ_* L_Y φ^*` of those of `H^{2m-2}(X)`. -/
theorem split_even (res : H₂ →ₗ[k] G₂) (hres : Function.Surjective res)
    (LY : G₂ ≃ₗ[k] G₄) (gys : G₄ →ₗ[k] H₄)
    (aH₂ : Submodule k H₂) (aH₄ : Submodule k H₄) (aG₂ : Submodule k G₂) (aG₄ : Submodule k G₄)
    (hA'' : aH₄ ≤ aG₄.map gys) (hAY : aG₄.map LY.symm.toLinearMap ≤ aG₂)
    (hA' : ∀ x, res x ∈ aG₂ → x ∈ aH₂) :
    aH₄ ≤ aH₂.map (gys ∘ₗ LY.toLinearMap ∘ₗ res) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hA'' hz
  have hw : LY.symm y ∈ aG₂ := hAY ⟨y, hy, rfl⟩
  obtain ⟨x, hx⟩ := hres (LY.symm y)
  refine ⟨x, hA' x (hx ▸ hw), ?_⟩
  simp [hx]

/-- Page 49, odd dimension: with `L = φ_* φ^*` invertible, `A''⁰`, `A'⁰` and the stability of
the algebraic classes under `p = φ^* L⁻¹ φ_*` give `A⁰(X)` (surjectivity on algebraic
classes). The factorisation `L = φ_* φ^*` is not even needed: the argument only inverts `L`. -/
theorem split_odd (res : H₂ →ₗ[k] G₂) (gys : G₂ →ₗ[k] H₄) (L : H₂ ≃ₗ[k] H₄)
    (aH₂ : Submodule k H₂) (aH₄ : Submodule k H₄) (aG : Submodule k G₂)
    (hA'' : aH₄ ≤ aG.map gys) (hp : ∀ y ∈ aG, res (L.symm (gys y)) ∈ aG)
    (hA' : ∀ x, res x ∈ aG → x ∈ aH₂) :
    aH₄ ≤ aH₂.map L.toLinearMap := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hA'' hz
  exact ⟨L.symm (gys y), hA' _ (hp y hy), by simp⟩

/-- The odd case is circular: if `φ^*` and `φ_*` keep algebraic classes and `L⁻¹` does
(`A⁰(X)`), the projection `p = φ^* L⁻¹ φ_*` keeps them. -/
theorem split_odd_circular (res : H₂ →ₗ[k] G₂) (gys : G₂ →ₗ[k] H₄) (L : H₂ ≃ₗ[k] H₄)
    (aH₂ : Submodule k H₂) (aH₄ : Submodule k H₄) (aG : Submodule k G₂)
    (hres : ∀ x ∈ aH₂, res x ∈ aG) (hgys : ∀ y ∈ aG, gys y ∈ aH₄)
    (hA0 : ∀ z ∈ aH₄, L.symm z ∈ aH₂) :
    ∀ y ∈ aG, res (L.symm (gys y)) ∈ aG :=
  fun y hy => hres _ (hA0 _ (hgys y hy))

end Scission

end Grothendieck.Folder16
