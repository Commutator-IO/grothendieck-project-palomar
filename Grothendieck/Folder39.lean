module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Grothendieck.Upstream.IsAdicCompleteOfIsNilpotent

@[expose] public section


/-!
# Folder 39, the formal preparation theorem (pages 18–19): the adic and discrete cases

The modernised reading `transcripts/39/39.modern.tex` (manuscript pages 18–19)
states:

> **Théorème** (« de préparation “formel” »). Soit `A` un anneau linéairement
> topologisé, séparé et complet, `Z` une indéterminée,
> `F = ∑ aᵢ Zⁱ ∈ A[[Z]]`, et `N ∈ ℕ` tel que (i) `aᵢ` est topologiquement
> nilpotent pour `0 ⩽ i ⩽ N-1` ; (ii) `a_N` est inversible. Alors `F` est un
> élément régulier de `A[[Z]]`, et … tout `G ∈ A[[Z]]` s'écrit de façon unique
> `G = QF + ∑_{0 ⩽ i ⩽ N-1} bᵢ Zⁱ`, `Q ∈ A[[Z]]`, `bᵢ ∈ A`.
>
> *Démonstration.* `A` est limite projective de ses quotients discrets `A/I` …
> on peut supposer `A` discret. Alors (i) signifie que `a₀, …, a_{N-1}` sont
> nilpotents. Soit `𝔪` l'idéal qu'ils engendrent : il est de type fini et
> engendré par des nilpotents, donc nilpotent. …

**This is a partial formalisation.** What is proved:

* `preparation_adique` — the theorem for `A` complete and separated for an
  `I`-adic topology, with `aᵢ ∈ I` for `i < N` and `a_N` a unit (in the `I`-adic
  topology « topologiquement nilpotent » means `aᵢ ∈ √I`, slightly weaker than
  `aᵢ ∈ I`; that gap is not closed here): `F` is regular,
  and every `G` is uniquely `QF + r` with `r` a polynomial of degree `< N`
  (which is `∑_{i<N} bᵢ Zⁱ`). This is a short application of mathlib's
  Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt`), once one checks
  that the order of `F` modulo `I` is exactly `N`.
* `preparation_discrete` — the case the proof reduces to: `A` any commutative
  ring, `a₀, …, a_{N-1}` nilpotent, `a_N` a unit. As the reading says, the ideal
  `𝔪` they generate is nilpotent (`ideal_nilpotent`), so `A` is `𝔪`-adically
  complete (`isAdicComplete_of_nilpotent`) and the adic case applies.

Not formalised: the general linearly topologised case, i.e. the passage from
the discrete quotients `A/J` back to `A = lim A/J`. mathlib has the vocabulary
(`IsLinearTopology`, `IsTopologicallyNilpotent`) but not the identification of
`A[[Z]]` with `lim (A/J)[[Z]]` that the gluing needs; building it is beyond the
scope of a check. Pages 9–14 (the axioms of a class of formal functions) are
formalised in the second part of this file, `Grothendieck.Folder39.Henselian`.

**What the formalisation finds.** Nothing false, and the discrete step is exactly
as the reading gives it: finitely many nilpotents generate a nilpotent ideal,
and a ring is complete for a nilpotent ideal. The formalisation confirms that
the hypotheses are used only as stated — (ii) is the unit condition mathlib calls
a Weierstrass divisor, and (i) is what makes the order of `F` modulo the ideal
equal to `N`. In the adic form no finiteness of the ideal is needed (the reading
uses « de type fini » only to get `𝔪ʲA[[Z]] = 𝔪ʲ[[Z]]` inside its own proof).

What this certifies is that the reading holds together at this point, not that
it is what the pages say (issue #26).
-/

namespace Grothendieck.Folder39

open PowerSeries Polynomial

variable {A : Type*} [CommRing A]

/-- A ring is complete and separated for a nilpotent ideal. -/
theorem isAdicComplete_of_nilpotent {I : Ideal A} (hI : IsNilpotent I) : IsAdicComplete I A :=
  IsAdicComplete.of_isNilpotent A hI

/-- **Formal preparation, adic case.** `A` complete and separated for the
`I`-adic topology, `aᵢ ∈ I` for `i < N`, `a_N` a unit: `F` is regular, and every
`G` is uniquely `QF + r` with `deg r < N`. -/
theorem preparation_adique (I : Ideal A) [IsAdicComplete I A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, coeff i F ∈ I) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · -- `A` is the zero ring.
    have := ‹IsAdicComplete ⊤ A›.subsingleton
    exact ⟨fun H _ => Subsingleton.elim _ _, fun G =>
      ⟨(0, 0), ⟨by simp, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩⟩
  have := Ideal.Quotient.nontrivial_iff.2 hI
  -- The order of `F` modulo `I` is `N`.
  have hord : (F.map (Ideal.Quotient.mk I)).order.toNat = N := by
    have : (F.map (Ideal.Quotient.mk I)).order = N := PowerSeries.order_eq_nat.2
      ⟨(h2.map (Ideal.Quotient.mk I)).ne_zero, fun i hi =>
        Ideal.Quotient.eq_zero_iff_mem.2 (h1 i hi)⟩
    rw [this, ENat.toNat_natCast]
  have H : F.IsWeierstrassDivisorAt I := by
    rwa [IsWeierstrassDivisorAt, hord]
  refine ⟨fun Q hQ => ?_, fun G => ?_⟩
  · have hdeg : (0 : A[X]).degree < ((F.map (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) :=
      Polynomial.degree_zero.trans_lt (WithBot.bot_lt_coe _)
    exact (H.eq_zero_of_mul_eq hdeg (by rw [hQ, Polynomial.coe_zero])).1
  · have hdiv := H.isWeierstrassDivisionAt_div_mod G
    have hdeg := hdiv.degree_lt
    rw [hord] at hdeg
    refine ⟨(H.div G, H.mod G), ⟨hdeg, ?_⟩, ?_⟩
    · show G = H.div G * F + ↑(H.mod G)
      rw [mul_comm]
      exact hdiv.eq_mul_add
    rintro ⟨q, r⟩ ⟨hr, hG⟩
    simp only at hr hG
    have hr' : r.degree < ((F.map (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) := by
      rwa [hord]
    have heq : F * q + ↑r = F * H.div G + ↑(H.mod G) := by
      rw [mul_comm F q, ← hG]
      exact hdiv.eq_mul_add
    exact Prod.ext_iff.2 (H.eq_of_mul_add_eq_mul_add hr' hdiv.degree_lt heq)

/-- « il est de type fini et engendré par des nilpotents, donc nilpotent ». -/
theorem ideal_nilpotent (F : A⟦X⟧) (N : ℕ) (h1 : ∀ i < N, IsNilpotent (coeff i F)) :
    IsNilpotent (Ideal.span (Set.range fun i : Fin N => coeff (i : ℕ) F)) := by
  classical
  rw [(Ideal.FG.isNilpotent_iff_le_nilradical
    ⟨Finset.univ.image fun i : Fin N => coeff (i : ℕ) F, by simp⟩), Ideal.span_le]
  exact Set.range_subset_iff.2 fun i => h1 i i.2

/-- **Formal preparation, discrete case.** Over any commutative ring, if
`a₀, …, a_{N-1}` are nilpotent and `a_N` is a unit, `F` is regular and every `G`
is uniquely `QF + r` with `deg r < N`. -/
theorem preparation_discrete (F : A⟦X⟧) (N : ℕ) (h1 : ∀ i < N, IsNilpotent (coeff i F))
    (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  have := isAdicComplete_of_nilpotent (ideal_nilpotent F N h1)
  exact preparation_adique (Ideal.span (Set.range fun i : Fin N => coeff (i : ℕ) F)) F N
    (fun i hi => Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩) h2

end Grothendieck.Folder39

/-!
# Folder 39, pages 9–14: the axioms (I), (S), (R), (H), (D) of a class of formal functions

The reading states, over an arbitrary commutative ring `k`, for a family of subrings
`A_n ⊆ k[[t₁, …, tₙ]]`: (I) the coordinates are in `A_n`; (S) `A` is closed under substitution
of arguments with nilpotent constant terms; (R) each `A_n` is a unital subring; (H) the inverse
of an `A`-morphism `X_n → X_n` that is a formal isomorphism is an `A`-morphism; (D) the
coefficients of `f ∈ A_{n+m}` in the last `m` variables lie in `A_n`. Page 11 derives from (H)
Corollary 1 (`f(0)` invertible in `k` ⟹ `f⁻¹ ∈ A_n`), page 12 Corollary 2 (the pair
`(A_n, A_n ∩ 𝔪_n)` is henselian) and Corollary 3 (implicit functions); page 14 derives from (D)
`A_n ⊆ k₀[[t]]`, `k₀ = A_0`. The reading holds Corollary 1, and with it the pair statement,
only under (D), since the page's proof substitutes `t_{n+1} = 1`.

What is proved (`IsFormalClass` is (I)+(S)+(R)+(H), `CoeffClosed` is (D) one variable at a
time):

* `implicit_function` — the formal implicit function theorem in one unknown over any ring (no
  class): `Q(0) = 0`, `∂Q/∂Z (0)` a unit give a unique `F`, `F(0) = 0`, `Q(F(t), t) = 0`. Proved
  by Weierstrass division by `Q` in `k[[t]][[Z]]` (`exists_eq_unit_mul_X_sub`).
* `implicit_mem` — Corollary 3 under (I), (S), (R), (H): that `F` lies in `A_n`, by the page's
  argument (invert `(Z, t) ↦ (P(Z, t), t)`, set `Z = 0`).
* `hensel_mem` — Corollary 2 under (I), (S), (R), (H): with `∂` invertible in `k`.
* `henselianRing` — the pair `(A_n, A_n ∩ 𝔪_n)` is henselian (mathlib's `HenselianRing`), in
  particular zariskian, under (I), (S), (R), (H) **without (D)**.
* `inv_mem` — Corollary 1 under (I), (S), (R), (H), (D).
* `intConst_isFormalClass`, `intConst_not_inv_mem` — Corollary 1 is **not** a consequence of
  (I), (S), (R), (H): over `ℚ`, the series with integral constant term satisfy them and `2 ∈ A_0`
  has no inverse in `A_0`.
* `coeff_mem` — the corollary of page 14 under (D).

(H) is taken with « isomorphisme formel » meaning « has a two-sided inverse for substitution »;
by `implicit_function` this is the Jacobian condition of the page for the maps
`(Z, t) ↦ (P, t)` used here. The transversal fibre products, formal subschemes, principal parts
and the faithful flatness question of the margin of page 12 are not formalised.

**What the formalisation finds.** The zariskian and henselian properties of
`(A_n, A_n ∩ 𝔪_n)` need only (H): Corollary 3, which does not use Corollary 1, inverts
`1 + g` for `g(0) = 0` (solve `(1 + g)(1 + Z) - 1 = 0`). What needs more than (H) is only the
strong form of Corollary 1, for `f(0)` a unit of `k` not known to be invertible in `A_0`; it
fails without (D), and (D) gives it through its case `n = 0`.
-/

namespace Grothendieck.Folder39.Henselian

open MvPowerSeries

variable {k : Type*} [CommRing k]

theorem finSuccEquiv_rename_succ {n : ℕ} (c : MvPowerSeries (Fin n) k) :
    finSuccEquiv k n (rename (Fin.succEmb n) c) = PowerSeries.C c := by
  ext j x
  rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C]
  split_ifs with hj
  · subst hj
    have : (Finsupp.cons 0 x : Fin (n+1) →₀ ℕ) = Finsupp.embDomain (Fin.succEmb n) x := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i
      · simp [Finsupp.embDomain_of_notMem_range]
      · rw [show i.succ = Fin.succEmb n i from rfl, Finsupp.embDomain_apply]; simp
    rw [this, coeff_embDomain_rename]
  · rw [coeff_rename_eq_zero, map_zero]
    rintro ⟨y, hy⟩
    have := congrArg (· 0) hy
    simp [Finsupp.mapDomain_of_notMem_range] at this
    exact hj this.symm

theorem finSuccEquiv_symm_C {n : ℕ} (c : MvPowerSeries (Fin n) k) :
    (finSuccEquiv k n).symm (PowerSeries.C c) = rename (Fin.succEmb n) c := by
  rw [AlgEquiv.symm_apply_eq, finSuccEquiv_rename_succ]

/-- For finitely many variables, a series without constant term lies in the ideal of the
variables. -/
theorem mem_span_X {n : ℕ} (f : MvPowerSeries (Fin n) k) (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range X) := by
  induction n with
  | zero =>
    have : f = C (constantCoeff f) := by
      ext e; rw [Subsingleton.elim e 0]; simp
    rw [this, hf, map_zero]; exact zero_mem _
  | succ n ih =>
    set g := finSuccEquiv k n f
    have hf' : f = rename (Fin.succEmb n) (PowerSeries.constantCoeff g) +
        X 0 * (finSuccEquiv k n).symm (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) g) := by
      apply (finSuccEquiv k n).injective
      rw [map_add, map_mul, finSuccEquiv_X_zero, AlgEquiv.apply_symm_apply,
        finSuccEquiv_rename_succ, add_comm (PowerSeries.C _)]
      exact PowerSeries.eq_X_mul_shift_add_const g
    rw [hf']
    refine add_mem ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩))
    have h0 : constantCoeff (PowerSeries.constantCoeff g) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_coeff_finSuccEquiv]
      simpa using hf
    have := Ideal.mem_map_of_mem (rename (R := k) (Fin.succEmb n)) (ih _ h0)
    rw [Ideal.map_span] at this
    refine Ideal.span_mono ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, (rename_X _ i).symm⟩

/-- One variable over an `I`-adically complete ring: a series whose constant term is in `I` and
whose linear coefficient is a unit is a unit times `X - r`, `r ∈ I`. -/
theorem exists_eq_unit_mul_X_sub {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (g : PowerSeries A) (h0 : PowerSeries.coeff 0 g ∈ I) (h1 : IsUnit (PowerSeries.coeff 1 g)) :
    ∃ r ∈ I, ∃ u : PowerSeries A, IsUnit u ∧ g = u * (PowerSeries.X - PowerSeries.C r) := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := (‹IsAdicComplete ⊤ A›.toIsHausdorff).subsingleton
    exact ⟨0, Submodule.mem_top, 1, isUnit_one, Subsingleton.elim _ _⟩
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hord : (g.map (Ideal.Quotient.mk I)).order = (1 : ℕ) := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map]; exact (h1.map _).ne_zero
    · obtain rfl : i = 0 := by omega
      rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact h0
  have H : g.IsWeierstrassDivisorAt I := by
    rw [PowerSeries.IsWeierstrassDivisorAt, hord]; exact h1
  obtain ⟨hdeg, heq⟩ := H.isWeierstrassDivisionAt_div_mod PowerSeries.X
  rw [hord] at hdeg
  set q := H.div PowerSeries.X
  set r := H.mod PowerSeries.X
  have hr : (r : PowerSeries A) = PowerSeries.C (r.coeff 0) := by
    rw [Polynomial.eq_C_of_degree_le_zero (p := r)
      (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hdeg))]
    simp
  rw [hr] at heq
  have c0 : 0 = PowerSeries.coeff 0 g * PowerSeries.coeff 0 q + r.coeff 0 := by
    simpa [PowerSeries.coeff_mul] using congrArg (PowerSeries.coeff 0) heq
  have c1 : 1 = PowerSeries.coeff 0 g * PowerSeries.coeff 1 q +
      PowerSeries.coeff 1 g * PowerSeries.coeff 0 q := by
    simpa [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ] using
      congrArg (PowerSeries.coeff 1) heq
  have hq0 : IsUnit (PowerSeries.coeff 0 q) := by
    have hj := IsAdicComplete.le_jacobson_bot I
      (Ideal.mul_mem_right (PowerSeries.coeff 1 q) _ h0)
    rw [Ideal.mem_jacobson_bot] at hj
    have := hj (-1)
    rw [show PowerSeries.coeff 0 g * PowerSeries.coeff 1 q * -1 + 1 =
      PowerSeries.coeff 1 g * PowerSeries.coeff 0 q by linear_combination c1] at this
    exact isUnit_of_mul_isUnit_right this
  have hqu : IsUnit q := PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hq0)
  refine ⟨-(PowerSeries.coeff 0 g * PowerSeries.coeff 0 q), ?_,
    ((hqu.unit⁻¹ : (PowerSeries A)ˣ) : PowerSeries A), Units.isUnit _, ?_⟩
  · exact neg_mem (Ideal.mul_mem_right _ _ h0)
  · have : g * q = PowerSeries.X - PowerSeries.C (r.coeff 0) := by rw [heq]; ring
    rw [show -(PowerSeries.coeff 0 g * PowerSeries.coeff 0 q) = r.coeff 0 by
      linear_combination c0, ← this]
    rw [mul_comm g, ← mul_assoc]; simp


theorem hasSubst_cons {m : ℕ} {F : MvPowerSeries (Fin m) k} (hF : constantCoeff F = 0) :
    HasSubst (Fin.cons F X : Fin (m + 1) → MvPowerSeries (Fin m) k) :=
  hasSubst_of_constantCoeff_zero fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hF]

theorem subst_cons_rename {m : ℕ} {F : MvPowerSeries (Fin m) k} (hF : constantCoeff F = 0)
    (c : MvPowerSeries (Fin m) k) :
    subst (Fin.cons F X : Fin (m + 1) → MvPowerSeries (Fin m) k)
      (rename (Fin.succEmb m) c) = c := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) (hasSubst_cons hF)]
  convert congrFun (subst_self (R := k) (σ := Fin m)) c using 2
  · funext i
    simp [subst_X (hasSubst_cons hF)]
  · rfl

theorem subst_cons_finSuccEquiv_symm {m : ℕ} {F : MvPowerSeries (Fin m) k}
    (hF : constantCoeff F = 0) (u : PowerSeries (MvPowerSeries (Fin m) k))
    (r : MvPowerSeries (Fin m) k) :
    subst (Fin.cons F X : Fin (m + 1) → MvPowerSeries (Fin m) k)
      ((finSuccEquiv k m).symm (u * (PowerSeries.X - PowerSeries.C r))) =
      subst (Fin.cons F X : Fin (m + 1) → MvPowerSeries (Fin m) k)
        ((finSuccEquiv k m).symm u) * (F - r) := by
  have h := hasSubst_cons hF
  rw [map_mul, subst_mul h, map_sub, subst_sub h, finSuccEquiv_symm_C, subst_cons_rename hF,
    ← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply, subst_X h]
  rfl

/-- The formal implicit function theorem in one unknown, over any commutative ring. -/
theorem implicit_function {m : ℕ} (Q : MvPowerSeries (Fin (m + 1)) k)
    (h0 : constantCoeff Q = 0) (h1 : IsUnit (coeff (Finsupp.single 0 1) Q)) :
    ∃! F : MvPowerSeries (Fin m) k, constantCoeff F = 0 ∧
      subst (Fin.cons F X : Fin (m + 1) → MvPowerSeries (Fin m) k) Q = 0 := by
  set g := finSuccEquiv k m Q
  have hg0 : PowerSeries.coeff 0 g ∈ Ideal.span (Set.range X) := by
    refine mem_span_X _ ?_
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_coeff_finSuccEquiv]
    simpa using h0
  have hg1 : IsUnit (PowerSeries.coeff 1 g) := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
      coeff_coeff_finSuccEquiv]
    convert h1
    ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  obtain ⟨r, hr, u, hu, hgu⟩ := exists_eq_unit_mul_X_sub _ g hg0 hg1
  have hr0 : constantCoeff r = 0 := by
    have : Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) k)) ≤
        RingHom.ker constantCoeff := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; simp
    exact this hr
  have hQ : Q = (finSuccEquiv k m).symm (u * (PowerSeries.X - PowerSeries.C r)) := by
    rw [← hgu, AlgEquiv.symm_apply_apply]
  refine ⟨r, ⟨hr0, ?_⟩, fun F ⟨hF0, hF⟩ => ?_⟩
  · rw [hQ, subst_cons_finSuccEquiv_symm hr0, sub_self, mul_zero]
  · rw [hQ, subst_cons_finSuccEquiv_symm hF0] at hF
    have hunit : IsUnit (subst (Fin.cons F X : Fin (m + 1) → MvPowerSeries (Fin m) k)
        ((finSuccEquiv k m).symm u)) := by
      rw [← coe_substAlgHom (hasSubst_cons hF0)]
      exact (hu.map _).map _
    exact sub_eq_zero.mp ((hunit.mul_right_eq_zero).mp hF)


/-- Conditions (I), (S), (R), (H) of pages 9–11 on a family `A n ⊆ k[[t₁, …, tₙ]]`; (R) is
built in, each `A n` being a unital subring. (S) is taken in its strong form (constants
allowed in `φ`), (H) with « isomorphisme formel » read as « has a two-sided inverse for
substitution ». -/
structure IsFormalClass (A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)) : Prop where
  /-- (I) -/
  X_mem : ∀ n (i : Fin n), X i ∈ A n
  /-- (S) -/
  subst_mem : ∀ {n m : ℕ} {φ : MvPowerSeries (Fin n) k} {f : Fin n → MvPowerSeries (Fin m) k},
    φ ∈ A n → (∀ i, f i ∈ A m) → (∀ i, IsNilpotent (constantCoeff (f i))) → subst f φ ∈ A m
  /-- (H) -/
  inv_mem : ∀ {n : ℕ} {f g : Fin n → MvPowerSeries (Fin n) k}, (∀ i, f i ∈ A n) →
    (∀ i, IsNilpotent (constantCoeff (f i))) → (∀ i, IsNilpotent (constantCoeff (g i))) →
    (∀ i, subst g (f i) = X i) → (∀ i, subst f (g i) = X i) → ∀ i, g i ∈ A n

theorem hasSubst_of_zero {m n : ℕ} {a : Fin m → MvPowerSeries (Fin n) k}
    (h : ∀ i, constantCoeff (a i) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero h

theorem subst_cons_rename_succAbove {n : ℕ} {W : MvPowerSeries (Fin (n + 1)) k}
    (hW : constantCoeff W = 0) (P : MvPowerSeries (Fin (n + 1)) k) :
    subst (Fin.cons W X : Fin (n + 2) → MvPowerSeries (Fin (n + 1)) k)
      (rename (Fin.succAboveEmb 1) P) =
      subst (Fin.cons W (fun i => X i.succ) : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k) P := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) (hasSubst_cons hW)]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [subst_X (hasSubst_cons hW)]
  · simp [subst_X (hasSubst_cons hW), Fin.succAbove]


theorem subst_cons_rename_succ {n : ℕ} {W : MvPowerSeries (Fin (n + 1)) k}
    (hW : constantCoeff W = 0) (P : MvPowerSeries (Fin (n + 1)) k) :
    subst (Fin.cons W X : Fin (n + 2) → MvPowerSeries (Fin (n + 1)) k)
      (rename (Fin.succEmb (n + 1)) P) = P :=
  subst_cons_rename hW P

theorem cons_X_zero_X_succ {n : ℕ} :
    (Fin.cons (X 0) (fun i => X i.succ) : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k) = X := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

variable {A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)}

/-- Corollary 3 of page 12 (the implicit function theorem in the class), under (I), (S), (R),
(H) alone: if `P ∈ A_{n+1}` (variables `Z, t₁, …, tₙ`) has `P(0) = 0` and `∂P/∂Z (0)` a unit
of `k`, the unique `F` with `F(0) = 0` and `P(F(t), t) = 0` lies in `A_n`. -/
theorem implicit_mem (hA : IsFormalClass A) {n : ℕ} {P : MvPowerSeries (Fin (n + 1)) k}
    (hP : P ∈ A (n + 1)) (h0 : constantCoeff P = 0)
    (h1 : IsUnit (coeff (Finsupp.single 0 1) P)) {F : MvPowerSeries (Fin n) k}
    (hF0 : constantCoeff F = 0)
    (hF : subst (Fin.cons F X : Fin (n + 1) → MvPowerSeries (Fin n) k) P = 0) : F ∈ A n := by
  -- `Q(W, Z, t) = P(W, t) - Z`, solved for `W`
  set e := Fin.succAboveEmb (1 : Fin (n + 2))
  have he : Finsupp.embDomain e (Finsupp.single 0 1) = Finsupp.single 0 1 := by
    rw [Finsupp.embDomain_single]; rfl
  set Q := rename e P - X 1
  have hQ0 : constantCoeff Q = 0 := by simp [Q, constantCoeff_rename, h0]
  have hQ1 : IsUnit (coeff (Finsupp.single 0 1) Q) := by
    simp only [Q, map_sub, ← he, coeff_embDomain_rename]
    have hne : Finsupp.single (0 : Fin (n + 2)) 1 ≠ Finsupp.single 1 1 := by
      intro h; have := congrArg (· 0) h; simp at this
    rw [he, coeff_X]
    simpa [hne] using h1
  obtain ⟨φ, ⟨hφ0, hφ⟩, -⟩ := implicit_function Q hQ0 hQ1
  set v : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k := Fin.cons φ (fun i => X i.succ)
  set u : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k := Fin.cons P (fun i => X i.succ)
  have hv0 : ∀ i, constantCoeff (v i) = 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [v, hφ0]
  have hu0 : ∀ i, constantCoeff (u i) = 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [u, h0]
  have hv := hasSubst_of_zero hv0
  have hu := hasSubst_of_zero hu0
  -- `P(φ(Z, t), t) = Z`
  have hvP : subst v P = X 0 := by
    have := hφ
    rw [show Q = rename e P - X 1 from rfl, subst_sub (hasSubst_cons hφ0),
      subst_cons_rename_succAbove hφ0, subst_X (hasSubst_cons hφ0)] at this
    exact sub_eq_zero.mp this
  -- `φ(P(Z, t), t) = Z`, by uniqueness for `R(W, Z, t) = P(W, t) - P(Z, t)`
  have huφ : subst u φ = X 0 := by
    set R := rename e P - rename (Fin.succEmb (n + 1)) P
    have hR0 : constantCoeff R = 0 := by simp [R, constantCoeff_rename, h0]
    have hR1 : IsUnit (coeff (Finsupp.single 0 1) R) := by
      simp only [R, map_sub, ← he, coeff_embDomain_rename]
      rw [he, coeff_rename_eq_zero, sub_zero]
      · exact h1
      · rintro ⟨y, hy⟩
        have := congrArg (· 0) hy
        simp [Finsupp.mapDomain_of_notMem_range] at this
    have hψ0 : constantCoeff (subst u φ) = 0 := constantCoeff_subst_eq_zero hu hu0 hφ0
    obtain ⟨W, -, hW⟩ := implicit_function R hR0 hR1
    have e1 := hW _ ⟨constantCoeff_X 0, by
      rw [subst_sub (hasSubst_cons (constantCoeff_X 0)),
        subst_cons_rename_succAbove (constantCoeff_X 0), cons_X_zero_X_succ,
        subst_self, subst_cons_rename_succ (constantCoeff_X 0)]
      exact sub_self _⟩
    have e2 := hW _ ⟨hψ0, by
      rw [subst_sub (hasSubst_cons hψ0), subst_cons_rename_succAbove hψ0,
        subst_cons_rename_succ hψ0, sub_eq_zero]
      have : (Fin.cons (subst u φ) (fun i => X i.succ) :
          Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k) = fun i => subst u (v i) := by
        funext i; refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · simp [v, subst_X hu, u]
      rw [this, ← subst_comp_subst_apply hv hu, hvP, subst_X hu]
      rfl⟩
    rw [e2, e1]
  -- (H): `v = u⁻¹` is an `A`-morphism, so `φ ∈ A_{n+1}`
  have hφA : φ ∈ A (n + 1) := by
    have := hA.inv_mem (f := u) (g := v)
      (Fin.cases hP fun _ => hA.X_mem _ _)
      (fun i => (hu0 i).symm ▸ IsNilpotent.zero)
      (fun i => (hv0 i).symm ▸ IsNilpotent.zero)
      (fun i => by refine Fin.cases ?_ (fun i => ?_) i
                   · exact hvP
                   · simp [u, subst_X hv, v])
      (fun i => by refine Fin.cases ?_ (fun i => ?_) i
                   · exact huφ
                   · simp [v, subst_X hu, u]) 0
    simpa [v] using this
  -- (S): `F' = φ(0, t) ∈ A_n`, and it is the root
  set w : Fin (n + 1) → MvPowerSeries (Fin n) k := Fin.cons 0 X
  have hw0 : ∀ i, constantCoeff (w i) = 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [w]
  have hw := hasSubst_of_zero hw0
  have hF'A : subst w φ ∈ A n := hA.subst_mem hφA (Fin.cases (zero_mem _) fun _ => hA.X_mem _ _)
    (fun i => (hw0 i).symm ▸ IsNilpotent.zero)
  have hF'0 : constantCoeff (subst w φ) = 0 := constantCoeff_subst_eq_zero hw hw0 hφ0
  have hF'root : subst (Fin.cons (subst w φ) X : Fin (n + 1) → MvPowerSeries (Fin n) k) P = 0 := by
    have : (Fin.cons (subst w φ) X : Fin (n + 1) → MvPowerSeries (Fin n) k) =
        fun i => subst w (v i) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · simp [v, subst_X hw, w]
    rw [this, ← subst_comp_subst_apply hv hw, hvP, subst_X hw]
    rfl
  obtain ⟨_, -, huniq⟩ := implicit_function P h0 h1
  rw [huniq F ⟨hF0, hF⟩, ← huniq _ ⟨hF'0, hF'root⟩]
  exact hF'A


/-- `T ↦ T(Z)` as a series in `Z, t₁, …, tₙ`, for a polynomial `T` over `k[[t]]`. -/
noncomputable def polyToSeries (n : ℕ) :
    Polynomial (MvPowerSeries (Fin n) k) →+* MvPowerSeries (Fin (n + 1)) k :=
  (finSuccEquiv k n).symm.toRingEquiv.toRingHom.comp (Polynomial.coeToPowerSeries.ringHom)

theorem polyToSeries_C {n : ℕ} (c : MvPowerSeries (Fin n) k) :
    polyToSeries n (Polynomial.C c) = rename (Fin.succEmb n) c := by
  simp [polyToSeries, finSuccEquiv_symm_C]

theorem polyToSeries_X {n : ℕ} : polyToSeries (k := k) n Polynomial.X = X 0 := by
  simp [polyToSeries, AlgEquiv.symm_apply_eq]

theorem subst_cons_polyToSeries {n : ℕ} {G : MvPowerSeries (Fin n) k} (hG : constantCoeff G = 0)
    (T : Polynomial (MvPowerSeries (Fin n) k)) :
    subst (Fin.cons G X : Fin (n + 1) → MvPowerSeries (Fin n) k) (polyToSeries n T) =
      T.eval G := by
  have h := hasSubst_cons hG
  have : ((substAlgHom h).toRingHom.comp (polyToSeries n)) = Polynomial.eval₂RingHom
      (RingHom.id _) G := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        coe_substAlgHom, polyToSeries_C, subst_cons_rename hG, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, RingHom.id_apply]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        coe_substAlgHom, polyToSeries_X, subst_X h, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      rfl
  have := congrArg (fun φ => φ T) this
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    coe_substAlgHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_id] using this

theorem coeff_polyToSeries {n : ℕ} (T : Polynomial (MvPowerSeries (Fin n) k)) (j : ℕ)
    (x : Fin n →₀ ℕ) : coeff (Finsupp.cons j x) (polyToSeries n T) = coeff x (T.coeff j) := by
  rw [← coeff_coeff_finSuccEquiv]
  simp [polyToSeries, Polynomial.coeff_coe]

theorem polyToSeries_mem (hA : IsFormalClass A) {n : ℕ} {P : Polynomial (MvPowerSeries (Fin n) k)}
    (hP : ∀ i, P.coeff i ∈ A n) {q : Polynomial (MvPowerSeries (Fin n) k)}
    (hq : polyToSeries n q ∈ A (n + 1)) : polyToSeries n (P.comp q) ∈ A (n + 1) := by
  rw [Polynomial.comp, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ hq _)
  rw [RingHom.comp_apply, polyToSeries_C, rename_eq_subst]
  exact hA.subst_mem (hP i) (fun i => hA.X_mem _ _) (fun i => by simp)

/-- Corollary 2 of page 12, under (I), (S), (R), (H) alone: a simple root of the reduced
polynomial lifts, uniquely, to a root in `A_n`. Here the approximate root `a₀` may be any element
of `A_n` (the page takes a constant `ζ ∈ k₀`). -/
theorem hensel_mem (hA : IsFormalClass A) {n : ℕ} {P : Polynomial (MvPowerSeries (Fin n) k)}
    (hP : ∀ i, P.coeff i ∈ A n) {a₀ : MvPowerSeries (Fin n) k} (ha₀ : a₀ ∈ A n)
    (h0 : constantCoeff (P.eval a₀) = 0)
    (h1 : IsUnit (constantCoeff (P.derivative.eval a₀))) :
    ∃! F : MvPowerSeries (Fin n) k, (constantCoeff F = constantCoeff a₀ ∧ P.eval F = 0) ∧
      F ∈ A n := by
  set Q := polyToSeries n (P.comp (Polynomial.X + Polynomial.C a₀))
  have hT : P.comp (Polynomial.X + Polynomial.C a₀) = Polynomial.taylor a₀ P := rfl
  have hQ : Q ∈ A (n + 1) := polyToSeries_mem hA hP (by
    rw [map_add, polyToSeries_X, polyToSeries_C, rename_eq_subst]
    exact add_mem (hA.X_mem _ _) (hA.subst_mem ha₀ (fun i => hA.X_mem _ _) (fun i => by simp)))
  have hQ0 : constantCoeff Q = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, show (0 : Fin (n + 1) →₀ ℕ) = Finsupp.cons 0 0 by
      simp, coeff_polyToSeries, hT, Polynomial.taylor_coeff_zero]
    simpa using h0
  have hQ1 : IsUnit (coeff (Finsupp.single 0 1) Q) := by
    rw [show (Finsupp.single 0 1 : Fin (n + 1) →₀ ℕ) = Finsupp.cons 1 0 by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp, coeff_polyToSeries, hT,
      Polynomial.taylor_coeff_one]
    simpa using h1
  have hroot : ∀ G, constantCoeff G = 0 →
      (subst (Fin.cons G X : Fin (n + 1) → MvPowerSeries (Fin n) k) Q = 0 ↔
        P.eval (G + a₀) = 0) := fun G hG => by
    rw [subst_cons_polyToSeries hG, hT, Polynomial.taylor_eval]
  obtain ⟨G, ⟨hG0, hG⟩, huniq⟩ := implicit_function Q hQ0 hQ1
  refine ⟨G + a₀, ⟨⟨by simp [hG0], (hroot G hG0).mp hG⟩,
    add_mem (implicit_mem hA hQ hQ0 hQ1 hG0 hG) ha₀⟩, fun F hFF => ?_⟩
  obtain ⟨⟨hF0, hF⟩, -⟩ := hFF
  have hc : constantCoeff (F - a₀) = 0 := by simp [hF0]
  have := huniq (F - a₀) ⟨hc, (hroot _ hc).mpr (by simpa using hF)⟩
  rw [← this]; ring


/-- The ideal `A_n ∩ 𝔪_n` of `A_n`: the elements without constant term. -/
noncomputable def idealM (A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)) (n : ℕ) : Ideal (A n) :=
  RingHom.ker ((constantCoeff : MvPowerSeries (Fin n) k →+* k).comp (A n).subtype)

/-- Corollaries 1–2 of pages 11–12 as the pair statement, under (I), (S), (R), (H) alone: the pair
`(A_n, A_n ∩ 𝔪_n)` is henselian, in particular zariskian (`A_n ∩ 𝔪_n ⊆ rad A_n`). -/
theorem henselianRing (hA : IsFormalClass A) (n : ℕ) : HenselianRing (A n) (idealM A n) := by
  have hev : ∀ (g : Polynomial (A n)) (a : A n),
      (g.map (A n).subtype).eval (a : MvPowerSeries (Fin n) k) = ((g.eval a : A n) : _) :=
    fun g a => by rw [Polynomial.eval_map]; exact Polynomial.eval₂_hom (A n).subtype a
  have key : ∀ (f : Polynomial (A n)) (a₀ : A n),
      constantCoeff ((f.map (A n).subtype).eval (a₀ : MvPowerSeries (Fin n) k)) = 0 →
      IsUnit (constantCoeff ((f.map (A n).subtype).derivative.eval
        (a₀ : MvPowerSeries (Fin n) k))) →
      ∃ a : A n, f.IsRoot a ∧ a - a₀ ∈ idealM A n := by
    intro f a₀ h0 h1
    obtain ⟨F, ⟨⟨hF0, hF⟩, hFA⟩, -⟩ := hensel_mem hA (P := f.map (A n).subtype)
      (fun i => by rw [Polynomial.coeff_map]; exact (f.coeff i).2) a₀.2 h0 h1
    refine ⟨⟨F, hFA⟩, ?_, ?_⟩
    · apply Subtype.val_injective
      rw [← hev]; exact hF
    · simp [idealM, hF0]
  refine ⟨fun x hx => ?_, fun f _ a₀ h0 h1 => ?_⟩
  · rw [Ideal.mem_jacobson_bot]
    intro y
    have hx0 : constantCoeff (x : MvPowerSeries (Fin n) k) = 0 := hx
    obtain ⟨a, ha, -⟩ := key (Polynomial.C (x * y + 1) * Polynomial.X - 1) 1
      (by simp [hx0]) (by simp [hx0])
    refine IsUnit.of_mul_eq_one a ?_
    have := ha
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] at this
    exact sub_eq_zero.mp this
  · refine key f a₀ (by rw [hev]; exact h0) ?_
    obtain ⟨b, hb⟩ := h1.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hb
    have : constantCoeff ((f.derivative.eval a₀ : A n) : MvPowerSeries (Fin n) k) *
        constantCoeff (b : MvPowerSeries (Fin n) k) = 1 := by
      have : constantCoeff ((f.derivative.eval a₀ * b - 1 : A n) :
          MvPowerSeries (Fin n) k) = 0 := hb
      push_cast at this
      rwa [map_sub, map_mul, map_one, sub_eq_zero] at this
    rw [Polynomial.derivative_map, hev]
    exact IsUnit.of_mul_eq_one _ this


/-- Condition (D) of page 14, in one variable at a time: the coefficients of `f ∈ A_{n+1}` as a
series in its first variable lie in `A_n`. -/
def CoeffClosed (A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)) : Prop :=
  ∀ {n : ℕ} {f : MvPowerSeries (Fin (n + 1)) k}, f ∈ A (n + 1) →
    ∀ j, PowerSeries.coeff j (finSuccEquiv k n f) ∈ A n

theorem C_mem (hA : IsFormalClass A) {n : ℕ} {c : k} (hc : (C c : MvPowerSeries (Fin 0) k) ∈ A 0) :
    (C c : MvPowerSeries (Fin n) k) ∈ A n := by
  have := hA.subst_mem (m := n) (f := Fin.elim0) hc (fun i => i.elim0) (fun i => i.elim0)
  rwa [subst_C] at this

/-- Corollary 1 of page 11 under (I), (S), (R), (H) and (D): if `f ∈ A_n` and `f(0)` is a unit of
`k`, then `f⁻¹ ∈ A_n`. (D) is used once, for `n = 0`, as in the page's argument: the inverse of
`s ↦ f(0) s` is in `A_1` by (H), and its coefficient `f(0)⁻¹` is in `A_0` by (D). -/
theorem inv_mem (hA : IsFormalClass A) (hD : CoeffClosed A) {n : ℕ}
    {f : MvPowerSeries (Fin n) k} (hf : f ∈ A n) (hu : IsUnit (constantCoeff f)) :
    ∃ g ∈ A n, f * g = 1 := by
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hC1 : (C (constantCoeff f) : MvPowerSeries (Fin 1) k) ∈ A 1 := by
    have := hA.subst_mem (m := 1) (f := 0) hf (fun _ => zero_mem _) (fun _ => IsNilpotent.zero)
    rwa [subst_zero_eq_C_constantCoeff, map_C, Algebra.algebraMap_self, RingHom.id_apply] at this
  -- (H) for `s ↦ f(0) s` on `X₁`
  have hcX : C c * X 0 ∈ A 1 := by
    have h1 : HasSubst (fun _ : Fin 1 => (C c * X 0 : MvPowerSeries (Fin 1) k)) :=
      hasSubst_of_zero fun _ => by simp
    have h2 : HasSubst (fun _ : Fin 1 => (C (constantCoeff f) * X 0 : MvPowerSeries (Fin 1) k)) :=
      hasSubst_of_zero fun _ => by simp
    refine hA.inv_mem (n := 1) (f := fun _ => C (constantCoeff f) * X 0)
      (g := fun _ => C c * X 0) (fun _ => mul_mem hC1 (hA.X_mem _ _)) (fun _ => by simp)
      (fun _ => by simp) (fun i => ?_) (fun i => ?_) 0
    · rw [subst_mul h1, subst_C, subst_X h1, Subsingleton.elim i 0, ← mul_assoc, ← map_mul,
        mul_comm, hc, map_one, mul_one]
    · rw [subst_mul h2, subst_C, subst_X h2, Subsingleton.elim i 0, ← mul_assoc, ← map_mul,
        mul_comm c, hc, map_one, one_mul]
  -- (D): its coefficient `c` is in `A₀`
  have hc0 : (C c : MvPowerSeries (Fin 0) k) ∈ A 0 := by
    have := hD hcX 1
    simpa [PowerSeries.coeff_C_mul] using this
  -- the inverse, by Corollary 2 for `f Z - 1` at `Z = c`
  obtain ⟨g, ⟨⟨-, hg⟩, hgA⟩, -⟩ := hensel_mem hA (P := Polynomial.C f * Polynomial.X - 1)
    (fun i => by
      rcases i with _ | _ | i <;> simp [Polynomial.coeff_one, Polynomial.coeff_C,
        Polynomial.coeff_X, hf, one_mem])
    (C_mem hA hc0) (by simp [hc]) (by simpa using hu)
  refine ⟨g, hgA, ?_⟩
  simpa [sub_eq_zero] using hg

/-- The corollary of page 14, under (D) alone: `A_n ⊆ k₀[[t₁, …, tₙ]]`, `k₀ = A_0`. -/
theorem coeff_mem (hD : CoeffClosed A) {n : ℕ} {f : MvPowerSeries (Fin n) k} (hf : f ∈ A n)
    (e : Fin n →₀ ℕ) : (C (coeff e f) : MvPowerSeries (Fin 0) k) ∈ A 0 := by
  induction n with
  | zero =>
    convert hf
    ext d
    rw [Subsingleton.elim d 0, Subsingleton.elim e 0]
    simp
  | succ n ih =>
    have := ih (hD hf (e 0)) e.tail
    rwa [coeff_coeff_finSuccEquiv, Finsupp.cons_tail] at this

/-- Corollary 1 of page 11 does not follow from (I), (S), (R), (H): over `k = ℚ`, the series
whose constant term is an integer form a family satisfying them, and `2 ∈ A_0` has no inverse
in `A_0` although `2` is a unit of `ℚ`. -/
noncomputable def intConst (n : ℕ) : Subring (MvPowerSeries (Fin n) ℚ) :=
  (Int.castRingHom ℚ).range.comap constantCoeff

theorem constantCoeff_subst_of_zero {m n : ℕ} {a : Fin m → MvPowerSeries (Fin n) k}
    (ha : ∀ i, constantCoeff (a i) = 0) (φ : MvPowerSeries (Fin m) k) :
    constantCoeff (subst a φ) = constantCoeff φ := by
  have h := hasSubst_of_zero ha
  have : φ = C (constantCoeff φ) + (φ - C (constantCoeff φ)) := by ring
  rw [this, subst_add h, subst_C, map_add, constantCoeff_subst_eq_zero h ha (by simp)]
  simp

theorem intConst_isFormalClass : IsFormalClass intConst where
  X_mem n i := Subring.mem_comap.mpr ⟨0, by simp⟩
  subst_mem {n m φ f} hφ _ hf := by
    refine Subring.mem_comap.mpr ?_
    rw [constantCoeff_subst_of_zero fun i => (hf i).eq_zero]
    exact Subring.mem_comap.mp hφ
  inv_mem {n f g} _ _ hg _ _ i := Subring.mem_comap.mpr ⟨0, by simp [(hg i).eq_zero]⟩

theorem intConst_not_inv_mem :
    (C 2 : MvPowerSeries (Fin 0) ℚ) ∈ intConst 0 ∧
      IsUnit (constantCoeff (C 2 : MvPowerSeries (Fin 0) ℚ)) ∧
      ¬ ∃ g ∈ intConst 0, (C 2 : MvPowerSeries (Fin 0) ℚ) * g = 1 := by
  refine ⟨⟨2, by simp⟩, by simp, ?_⟩
  rintro ⟨g, ⟨z, hz⟩, hg⟩
  have := congrArg constantCoeff hg
  rw [map_mul, constantCoeff_C, ← hz, map_one] at this
  simp only [Int.coe_castRingHom] at this
  have : (2 * z : ℤ) = 1 := by exact_mod_cast this
  omega

end Grothendieck.Folder39.Henselian
