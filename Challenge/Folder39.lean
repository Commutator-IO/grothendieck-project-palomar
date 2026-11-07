module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian

@[expose] public section

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

variable {A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)}

/-- Corollary 3 of page 12 (the implicit function theorem in the class), under (I), (S), (R),
(H) alone: if `P ∈ A_{n+1}` (variables `Z, t₁, …, tₙ`) has `P(0) = 0` and `∂P/∂Z (0)` a unit
of `k`, the unique `F` with `F(0) = 0` and `P(F(t), t) = 0` lies in `A_n`. -/
theorem implicit_mem (hA : IsFormalClass A) {n : ℕ} {P : MvPowerSeries (Fin (n + 1)) k}
    (hP : P ∈ A (n + 1)) (h0 : constantCoeff P = 0)
    (h1 : IsUnit (coeff (Finsupp.single 0 1) P)) {F : MvPowerSeries (Fin n) k}
    (hF0 : constantCoeff F = 0)
    (hF : subst (Fin.cons F X : Fin (n + 1) → MvPowerSeries (Fin n) k) P = 0) : F ∈ A n := by
  sorry

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

end Grothendieck.Folder39.Henselian
