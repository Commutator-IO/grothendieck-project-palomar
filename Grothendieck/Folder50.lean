module

public import Mathlib

@[expose] public section


/-!
# Folder 50: the axiomatic trace formula (pages 6–10)

Finding `50-axiomatic-trace-formula` (`src/content/findings.ts`), on the reading
`transcripts/50/50.modern.tex`. Pages 10, 9, 8, 7 and 6 set out an axiomatic
frame for the endomorphisms of an abelian variety — an additive category with a
duality `D`, a group `N(A)` of antisymmetric elements of `Hom(A, D(A))`, two
cones `N⁺`, `N^>`, an `r`-linear intersection form `I` with values in `ℤ` and a
degree `ν` with `I(u*ξ₁, …, u*ξᵣ) = ν(u) I(ξ₁, …, ξᵣ)` — and derive from it the
coefficients `σᵢ(α)` of `ν(α + n)` and the trace formula
`tr(α) = r · I(ξ^{r−1}, D_ξ(α)) / I(ξ^r)`.

The frame is taken at one object `A` and at one class `ξ` with `φ_ξ` a
`ℚ`-isomorphism, transported to `E = End(A)` by `ψ(η) = φ_ξ⁻¹ φ_η`: the Rosati
involution `α' = φ_ξ⁻¹ ᵗα φ_ξ` is a `StarRing` structure on `E`, and
`φ_{α*η} = ᵗα φ_η α` reads `ψ(α*η) = α' ψ(η) α` (`Frame`).

* `ψ_D`, `D_eq_Dξ_star_mul`, `D_eq_Dξ_star_mul'`, `Dξ_star`: the identities
  (1)–(3) of page 9, `D_ξ(α, β) = φ_ξ(α'β + β'α)`,
  `D_ξ(α, β) = D_ξ(α'β) = D_ξ(β'α)`, `D_ξ(α) = D_ξ(α')`;
* `pb_mul`, `nu_mul`: `(uv)* = v* u*` and `ν(uv) = ν(u) ν(v)`;
* `eval_charPoly`, `charPoly_unique`, `charPoly_monic`, `natDegree_charPoly`,
  `coeff_zero_charPoly`: `ν(α + n)` is, for `n ∈ ℤ`, the value of a unique
  monic polynomial of degree `2r` over `ℚ`, with constant term `ν(α)` — the
  `σᵢ(α)` of page 8 are well defined;
* `tr_mul_I`: the trace formula, **when `I` is symmetric**;
* `tr_star_mul_self_mul_I`, `tr_mul_star_self_mul_I`: the formulas of page 6,
  `tr(α'α) = 2r I(ξ^{r−1}, α*ξ)/I(ξ^r)` and the same for `αα'` with `α'*ξ`;
* `ModelA.not_trace_formula`: without symmetry the trace formula fails, in a
  model of all the axioms (with `r = 2`, `I(x, y) = x₁y₂`), in either slot;
* `ModelB.tr_star_i_mul_i`, `ModelB.nef_pos`: Rosati positivity, the
  Corollaire of page 6, does not follow from the axioms, even with
  `I(ξ^{r−1}, η) > 0` for every nonzero `η ∈ N⁺`: in `ℍ[ℤ, 0, 0, 0]`,
  `i ≠ 0` and `tr(i'i) = 0`;
* `tr_star_mul_self_pos`: it follows once that positivity on `N⁺` and
  `α ≠ 0 ⇒ α*ξ ≠ 0` are added.

Not formalised: the category itself, Propriété fondamentale 1 on products, the
first half of the folder (pages 2 and 4).
-/

namespace Grothendieck.Folder50

open Polynomial Finset

/-- The frame of pages 6–10 at one object and one class `ξ` with `φ_ξ` a
`ℚ`-isomorphism, transported to `E = End(A)` by `ψ(η) = φ_ξ⁻¹ φ_η`; the star is
the Rosati involution. -/
structure Frame (E N : Type*) [Ring E] [StarRing E] [AddCommGroup N] (r : ℕ) where
  /-- `η ↦ φ_ξ⁻¹ φ_η`. -/
  ψ : N →+ E
  ψ_injective : Function.Injective ψ
  /-- The classes are antisymmetric, so their images are Rosati-symmetric. -/
  star_ψ : ∀ η, star (ψ η) = ψ η
  /-- The pullback `α*η`. -/
  pb : E → N → N
  ψ_pb : ∀ α η, ψ (pb α η) = star α * ψ η * α
  /-- The class `ξ`. -/
  ξ : N
  ψ_ξ : ψ ξ = 1
  /-- The intersection form of (e). -/
  I : MultilinearMap ℤ (fun _ : Fin r => N) ℤ
  /-- The degree of (e) 3). -/
  ν : E → ℤ
  I_pb : ∀ u (v : Fin r → N), I (fun i => pb u (v i)) = ν u * I v
  I_ξ : I (fun _ => ξ) ≠ 0

namespace Frame

variable {E N : Type*} [Ring E] [StarRing E] [AddCommGroup N] {r : ℕ} (F : Frame E N r)

/-- `D_ξ(α, β) = (α + β)*ξ − α*ξ − β*ξ`. -/
def D (α β : E) : N := F.pb (α + β) F.ξ - F.pb α F.ξ - F.pb β F.ξ

/-- `D_ξ(α) = D_ξ(α, 1)`. -/
def Dξ (α : E) : N := F.D α 1

theorem ψ_D (α β : E) : F.ψ (F.D α β) = star α * β + star β * α := by
  simp only [D, map_sub, ψ_pb, ψ_ξ, mul_one, star_add]
  noncomm_ring

theorem ψ_Dξ (α : E) : F.ψ (F.Dξ α) = α + star α := by
  simp [Dξ, ψ_D, add_comm]

theorem D_eq_Dξ_star_mul (α β : E) : F.D α β = F.Dξ (star α * β) :=
  F.ψ_injective (by rw [ψ_D, ψ_Dξ, star_mul, star_star])

theorem D_eq_Dξ_star_mul' (α β : E) : F.D α β = F.Dξ (star β * α) :=
  F.ψ_injective (by rw [ψ_D, ψ_Dξ, star_mul, star_star, add_comm])

theorem Dξ_star (α : E) : F.Dξ (star α) = F.Dξ α :=
  F.ψ_injective (by rw [ψ_Dξ, ψ_Dξ, star_star, add_comm])

theorem pb_mul (u v : E) (η : N) : F.pb (u * v) η = F.pb v (F.pb u η) :=
  F.ψ_injective (by rw [ψ_pb, ψ_pb, ψ_pb, star_mul]; noncomm_ring)

theorem nu_mul (u v : E) : F.ν (u * v) = F.ν u * F.ν v := by
  have h1 := F.I_pb (u * v) (fun _ => F.ξ)
  have h2 := F.I_pb v (fun _ => F.pb u F.ξ)
  have h3 := F.I_pb u (fun _ => F.ξ)
  simp only [pb_mul] at h1
  refine mul_right_cancel₀ F.I_ξ ?_
  rw [← h1, h2, h3, mul_assoc, mul_left_comm]

theorem pb_add_intCast (α : E) (n : ℤ) :
    F.pb (α + n) F.ξ = (n ^ 2) • F.ξ + n • F.Dξ α + F.pb α F.ξ :=
  F.ψ_injective (by
    simp only [map_add, map_zsmul, ψ_pb, ψ_ξ, ψ_Dξ, mul_one, star_add, star_intCast,
      zsmul_eq_mul, add_mul, mul_add, ← (Int.cast_commute n (star α)).eq]
    push_cast
    noncomm_ring)

/-- The weight of each summand of `(α + n)*ξ = n²ξ + n D_ξ(α) + α*ξ`. -/
def wt : Fin 3 → ℕ := ![2, 1, 0]

/-- The three summands. -/
def sel (α : E) : Fin 3 → N := ![F.ξ, F.Dξ α, F.pb α F.ξ]

theorem wt_le (j : Fin 3) : wt j ≤ 2 := by fin_cases j <;> simp [wt]

theorem I_pb_add_intCast (α : E) (n : ℤ) :
    F.I (fun _ => F.pb (α + n) F.ξ) =
      ∑ f : Fin r → Fin 3, n ^ (∑ i, wt (f i)) * F.I (fun i => F.sel α (f i)) := by
  have h : F.pb (α + n) F.ξ = ∑ j : Fin 3, (n ^ wt j) • F.sel α j := by
    rw [pb_add_intCast, Fin.sum_univ_three]
    simp [wt, sel]
  rw [h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, prod_pow_eq_pow_sum, smul_eq_mul]

/-- The polynomial `P` with `P(n) = ν(α + n)`, over `ℚ`. -/
noncomputable def charPoly (α : E) : ℚ[X] :=
  C ((F.I fun _ => F.ξ : ℤ) : ℚ)⁻¹ *
    ∑ f : Fin r → Fin 3, C ((F.I fun i => F.sel α (f i) : ℤ) : ℚ) * X ^ (∑ i, wt (f i))

/-- `σᵢ(α)`, the coefficient of `n^{2r − i}` in `ν(α + n)`. -/
noncomputable def σ (i : ℕ) (α : E) : ℚ := (F.charPoly α).coeff (2 * r - i)

/-- `tr(α) = σ₁(α)`. -/
noncomputable def tr (α : E) : ℚ := F.σ 1 α

theorem I_ξ_cast : ((F.I fun _ => F.ξ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast F.I_ξ

theorem eval_charPoly (α : E) (n : ℤ) : (F.charPoly α).eval (n : ℚ) = F.ν (α + n) := by
  have h := congrArg (Int.cast : ℤ → ℚ) (F.I_pb (α + n) (fun _ => F.ξ))
  rw [I_pb_add_intCast] at h
  push_cast at h
  simp only [charPoly, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X]
  rw [inv_mul_eq_iff_eq_mul₀ F.I_ξ_cast, mul_comm _ ((F.ν (α + n) : ℤ) : ℚ), ← h]
  exact Finset.sum_congr rfl fun f _ => mul_comm _ _

/-- The `σᵢ` are well defined: `ν(α + n)`, `n ∈ ℤ`, determines the polynomial. -/
theorem charPoly_unique (α : E) (Q : ℚ[X]) (hQ : ∀ n : ℤ, Q.eval (n : ℚ) = F.ν (α + n)) :
    Q = F.charPoly α := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Int.cast_injective)
  rintro _ ⟨n, rfl⟩
  simp [hQ, eval_charPoly]

theorem coeff_charPoly (α : E) (k : ℕ) :
    (F.charPoly α).coeff k = ((F.I fun _ => F.ξ : ℤ) : ℚ)⁻¹ *
      ∑ f : Fin r → Fin 3,
        if k = ∑ i, wt (f i) then ((F.I fun i => F.sel α (f i) : ℤ) : ℚ) else 0 := by
  simp [charPoly, coeff_C_mul, finsetSum_coeff]

theorem sum_wt_le (f : Fin r → Fin 3) : ∑ i, wt (f i) ≤ 2 * r := by
  calc ∑ i, wt (f i) ≤ ∑ _i : Fin r, 2 := sum_le_sum fun i _ => wt_le _
    _ = 2 * r := by simp [mul_comm]

theorem two_mul_eq_sum_wt_iff (f : Fin r → Fin 3) :
    2 * r = ∑ i, wt (f i) ↔ f = fun _ => 0 := by
  constructor
  · intro h
    have h2 : ∑ i, wt (f i) = ∑ _i : Fin r, 2 := by simp [← h, mul_comm]
    rw [sum_eq_sum_iff_of_le fun i _ => wt_le _] at h2
    funext i
    have := h2 i (mem_univ _)
    revert this
    generalize f i = x
    fin_cases x <;> simp [wt]
  · rintro rfl
    simp [wt, mul_comm]

theorem natDegree_charPoly_le (α : E) : (F.charPoly α).natDegree ≤ 2 * r := by
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun f _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (sum_wt_le f)

theorem coeff_two_mul_charPoly (α : E) : (F.charPoly α).coeff (2 * r) = 1 := by
  rw [coeff_charPoly]
  simp only [two_mul_eq_sum_wt_iff, sum_ite_eq', mem_univ, ite_true]
  simp only [sel, Matrix.cons_val_zero]
  exact inv_mul_cancel₀ F.I_ξ_cast

theorem charPoly_monic (α : E) : (F.charPoly α).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one _ (F.natDegree_charPoly_le α) (F.coeff_two_mul_charPoly α)

theorem natDegree_charPoly (α : E) : (F.charPoly α).natDegree = 2 * r :=
  natDegree_eq_of_le_of_coeff_ne_zero (F.natDegree_charPoly_le α)
    (by rw [coeff_two_mul_charPoly]; exact one_ne_zero)

/-- `σ_{2r}(α) = ν(α)`. -/
theorem coeff_zero_charPoly (α : E) : (F.charPoly α).coeff 0 = F.ν α := by
  rw [coeff_zero_eq_eval_zero, ← Int.cast_zero, eval_charPoly, Int.cast_zero, add_zero]

theorem σ_two_mul (α : E) : F.σ (2 * r) α = F.ν α := by
  simp [σ, coeff_zero_charPoly]

theorem two_mul_add_one_eq_sum_wt_iff {m : ℕ} (f : Fin (m + 1) → Fin 3) :
    2 * m + 1 = ∑ i, wt (f i) ↔ ∃ i, f = Function.update (fun _ => 0) i 1 := by
  constructor
  · intro h
    have hd : ∑ i, (2 - wt (f i)) = 1 := by
      have h1 : ∑ i, (wt (f i) + (2 - wt (f i))) = 2 * (m + 1) := by
        simp [Nat.add_sub_cancel' (wt_le _), mul_comm]
      rw [sum_add_distrib] at h1
      omega
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (s := univ)
      (f := fun i => 2 - wt (f i)) (by rw [hd]; exact one_ne_zero)
    have hrest := add_sum_erase univ (fun j => 2 - wt (f j)) (mem_univ i)
    rw [hd] at hrest
    have hi1 : 2 - wt (f i) = 1 := by omega
    have hz : ∀ j ∈ univ.erase i, 2 - wt (f j) = 0 := sum_eq_zero_iff.mp (by omega)
    refine ⟨i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      revert hi1
      generalize f j = x
      fin_cases x <;> simp [wt]
    · have := hz j (mem_erase.mpr ⟨hj, mem_univ _⟩)
      rw [Function.update_of_ne hj]
      revert this
      generalize f j = x
      fin_cases x <;> simp [wt]
  · rintro ⟨i, rfl⟩
    have : ∀ j, wt (Function.update (fun _ => (0 : Fin 3)) i 1 j) =
        Function.update (fun _ => 2) i 1 j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [wt]
      · simp [Function.update_of_ne hj, wt]
    simp only [this, sum_update_of_mem (mem_univ i), sum_const, card_sdiff, card_univ,
      Fintype.card_fin, smul_eq_mul]
    simp
    omega

/-- **The trace formula** (head of page 8), for a symmetric intersection form:
`tr(α) · I(ξ^r) = r · I(ξ^{r−1}, D_ξ(α))`. -/
theorem tr_mul_I {m : ℕ} (F : Frame E N (m + 1))
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → N), F.I (v ∘ σ) = F.I v)
    (α : E) :
    F.tr α * ((F.I fun _ => F.ξ : ℤ) : ℚ) =
      (m + 1) * ((F.I (Function.update (fun _ => F.ξ) 0 (F.Dξ α)) : ℤ) : ℚ) := by
  have hk : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [tr, σ, hk, coeff_charPoly, mul_comm, ← mul_assoc, mul_inv_cancel₀ F.I_ξ_cast, one_mul,
    ← sum_filter]
  have hfilt : (univ.filter fun f : Fin (m + 1) → Fin 3 => 2 * m + 1 = ∑ i, wt (f i)) =
      univ.image (fun i => Function.update (fun _ => (0 : Fin 3)) i 1) := by
    ext f
    simp [two_mul_add_one_eq_sum_wt_iff, eq_comm]
  have hinj : Function.Injective
      (fun i : Fin (m + 1) => Function.update (fun _ => (0 : Fin 3)) i 1) := by
    intro i j h
    by_contra hij
    have := congrFun h i
    simp [Function.update_of_ne hij] at this
  have hterm : ∀ i : Fin (m + 1),
      F.I (fun k => F.sel α (Function.update (fun _ => (0 : Fin 3)) i 1 k)) =
        F.I (Function.update (fun _ => F.ξ) 0 (F.Dξ α)) := by
    intro i
    have e1 : (fun k => F.sel α (Function.update (fun _ => (0 : Fin 3)) i 1 k)) =
        Function.update (fun _ => F.ξ) i (F.Dξ α) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp [sel]
      · simp [Function.update_of_ne hk, sel]
    rw [e1, ← hsym (Equiv.swap 0 i), Function.update_comp_equiv]
    simp
    rfl
  rw [hfilt, sum_image fun i _ j _ h => hinj h]
  simp [hterm]

/-- `D_ξ(α'α) = 2 α*ξ`. -/
theorem Dξ_star_mul_self (α : E) : F.Dξ (star α * α) = (2 : ℤ) • F.pb α F.ξ :=
  F.ψ_injective (by rw [ψ_Dξ, map_zsmul, ψ_pb, ψ_ξ, mul_one, star_mul, star_star, two_zsmul])

/-- Page 6: `tr(α'α) · I(ξ^r) = 2r · I(ξ^{r−1}, α*ξ)`. -/
theorem tr_star_mul_self_mul_I {m : ℕ} (F : Frame E N (m + 1))
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → N), F.I (v ∘ σ) = F.I v)
    (α : E) :
    F.tr (star α * α) * ((F.I fun _ => F.ξ : ℤ) : ℚ) =
      2 * (m + 1) * ((F.I (Function.update (fun _ => F.ξ) 0 (F.pb α F.ξ)) : ℤ) : ℚ) := by
  rw [tr_mul_I F hsym, Dξ_star_mul_self, MultilinearMap.map_update_smul, smul_eq_mul]
  push_cast
  ring

/-- Page 6 as written, with `αα'`: the axioms give `α'*ξ` in the last slot. -/
theorem tr_mul_star_self_mul_I {m : ℕ} (F : Frame E N (m + 1))
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → N), F.I (v ∘ σ) = F.I v)
    (α : E) :
    F.tr (α * star α) * ((F.I fun _ => F.ξ : ℤ) : ℚ) =
      2 * (m + 1) * ((F.I (Function.update (fun _ => F.ξ) 0 (F.pb (star α) F.ξ)) : ℤ) : ℚ) := by
  simpa using F.tr_star_mul_self_mul_I hsym (star α)

end Frame

/-- The cones of (d) and the positivity of (e) 2), with the stability of `N⁺` under
all pullbacks and of `N^>` under isogenies (`ν(u) ≠ 0`). -/
structure Positivity {E N : Type*} [Ring E] [StarRing E] [AddCommGroup N] {r : ℕ}
    (F : Frame E N r) where
  /-- `N⁺`. -/
  Pos : Set N
  /-- `N^>`. -/
  Amp : Set N
  Pos_add : ∀ x ∈ Pos, ∀ y ∈ Pos, x + y ∈ Pos
  Pos_nsmul : ∀ n : ℕ, 0 < n → ∀ x ∈ Pos, n • x ∈ Pos
  Amp_add : ∀ x ∈ Amp, ∀ y ∈ Amp, x + y ∈ Amp
  Amp_nsmul : ∀ n : ℕ, 0 < n → ∀ x ∈ Amp, n • x ∈ Amp
  Amp_subset : Amp ⊆ Pos
  Amp_closure : AddSubgroup.closure Amp = ⊤
  /-- `φ_x` is a `ℚ`-isomorphism. -/
  Amp_iso : ∀ x ∈ Amp, ∃ y : E, ∃ m : ℤ, m ≠ 0 ∧ F.ψ x * y = m ∧ y * F.ψ x = m
  I_pos : ∀ v : Fin r → N, (∀ i, v i ∈ Amp) → 0 < F.I v
  ξ_mem : F.ξ ∈ Amp
  Pos_pb : ∀ u, ∀ x ∈ Pos, F.pb u x ∈ Pos
  Amp_pb : ∀ u, F.ν u ≠ 0 → ∀ x ∈ Amp, F.pb u x ∈ Amp

/-- The Corollaire of page 6 (Rosati positivity) under two added axioms:
`I(ξ^{r−1}, η) > 0` for every nonzero `η ∈ N⁺`, and `α ≠ 0 ⇒ α*ξ ≠ 0`. -/
theorem tr_star_mul_self_pos {E N : Type*} [Ring E] [StarRing E] [AddCommGroup N] {m : ℕ}
    {F : Frame E N (m + 1)} (P : Positivity F)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → N), F.I (v ∘ σ) = F.I v)
    (hnef : ∀ η ∈ P.Pos, η ≠ 0 → 0 < F.I (Function.update (fun _ => F.ξ) 0 η))
    (hfaith : ∀ α : E, α ≠ 0 → F.pb α F.ξ ≠ 0) (α : E) (hα : α ≠ 0) :
    0 < F.tr (star α * α) := by
  have h := F.tr_star_mul_self_mul_I hsym α
  have hI : (0 : ℚ) < ((F.I fun _ => F.ξ : ℤ) : ℚ) := by
    exact_mod_cast P.I_pos _ fun _ => P.ξ_mem
  have hp : (0 : ℚ) < ((F.I (Function.update (fun _ => F.ξ) 0 (F.pb α F.ξ)) : ℤ) : ℚ) := by
    exact_mod_cast hnef _ (P.Pos_pb α _ (P.Amp_subset P.ξ_mem)) (hfaith α hα)
  have : 0 < F.tr (star α * α) * ((F.I fun _ => F.ξ : ℤ) : ℚ) := by
    rw [h]; positivity
  exact (mul_pos_iff_of_pos_right hI).mp this

/-! ### Without symmetry the trace formula fails -/

namespace ModelA

/-- `I(x, y) = x₁ y₂` on `ℤ²`. -/
def I : MultilinearMap ℤ (fun _ : Fin 2 => ℤ × ℤ) ℤ :=
  (MultilinearMap.mkPiAlgebra ℤ (Fin 2) ℤ).compLinearMap
    ![LinearMap.fst ℤ ℤ ℤ, LinearMap.snd ℤ ℤ ℤ]

theorem I_apply (v : Fin 2 → ℤ × ℤ) : I v = (v 0).1 * (v 1).2 := by
  simp [I, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_two]

/-- `E = N = ℤ²`, trivial involution, `ξ = (1, 1)`, `ν(u) = u₁² u₂²`, `r = 2`. -/
def F : Frame (ℤ × ℤ) (ℤ × ℤ) 2 where
  ψ := AddMonoidHom.id _
  ψ_injective := Function.injective_id
  star_ψ := fun η => star_trivial η
  pb := fun α η => α * η * α
  ψ_pb := fun α η => by simp [star_trivial]
  ξ := 1
  ψ_ξ := rfl
  I := I
  ν := fun u => u.1 ^ 2 * u.2 ^ 2
  I_pb := fun u v => by simp only [I_apply, Prod.fst_mul, Prod.snd_mul]; ring
  I_ξ := by simp [I_apply]

/-- The cones `N⁺ = {x₁, x₂ ≥ 0}`, `N^> = {x₁, x₂ > 0}`. -/
def P : Positivity F where
  Pos := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}
  Amp := {x | 0 < x.1 ∧ 0 < x.2}
  Pos_add := fun x hx y hy => ⟨add_nonneg hx.1 hy.1, add_nonneg hx.2 hy.2⟩
  Pos_nsmul := fun n _ x hx => ⟨by simpa using mul_nonneg n.cast_nonneg hx.1,
    by simpa using mul_nonneg n.cast_nonneg hx.2⟩
  Amp_add := fun x hx y hy => ⟨add_pos hx.1 hy.1, add_pos hx.2 hy.2⟩
  Amp_nsmul := fun n hn x hx => ⟨by simpa using mul_pos (Nat.cast_pos.mpr hn) hx.1,
    by simpa using mul_pos (Nat.cast_pos.mpr hn) hx.2⟩
  Amp_subset := fun x hx => ⟨hx.1.le, hx.2.le⟩
  Amp_closure := by
    refine eq_top_iff.mpr fun x _ => ?_
    have h11 : ((1, 1) : ℤ × ℤ) ∈ AddSubgroup.closure {x : ℤ × ℤ | 0 < x.1 ∧ 0 < x.2} :=
      AddSubgroup.subset_closure ⟨one_pos, one_pos⟩
    have h12 : ((1, 2) : ℤ × ℤ) ∈ AddSubgroup.closure {x : ℤ × ℤ | 0 < x.1 ∧ 0 < x.2} :=
      AddSubgroup.subset_closure ⟨one_pos, two_pos⟩
    have hx : x = (2 * x.1 - x.2) • ((1, 1) : ℤ × ℤ) + (x.2 - x.1) • ((1, 2) : ℤ × ℤ) := by
      ext <;> simp <;> ring
    rw [hx]
    exact add_mem (zsmul_mem h11 _) (zsmul_mem h12 _)
  Amp_iso := fun x hx => ⟨(x.2, x.1), x.1 * x.2, mul_ne_zero hx.1.ne' hx.2.ne',
    by ext <;> simp [F, mul_comm], by ext <;> simp [F, mul_comm]⟩
  I_pos := fun v hv => by
    change 0 < I v
    rw [I_apply]; exact mul_pos (hv 0).1 (hv 1).2
  ξ_mem := ⟨one_pos, one_pos⟩
  Pos_pb := fun u x hx => by
    change 0 ≤ (u * x * u).1 ∧ 0 ≤ (u * x * u).2
    simp only [Prod.fst_mul, Prod.snd_mul]
    exact ⟨by nlinarith [mul_self_nonneg u.1, hx.1], by nlinarith [mul_self_nonneg u.2, hx.2]⟩
  Amp_pb := fun u hu x hx => by
    change 0 < (u * x * u).1 ∧ 0 < (u * x * u).2
    have h1 : u.1 ≠ 0 := fun h => hu (by simp [F, h])
    have h2 : u.2 ≠ 0 := fun h => hu (by simp [F, h])
    simp only [Prod.fst_mul, Prod.snd_mul]
    exact ⟨by nlinarith [mul_self_pos.mpr h1, hx.1], by nlinarith [mul_self_pos.mpr h2, hx.2]⟩

theorem tr_one_zero : F.tr (1, 0) = 2 := by
  have h : (X ^ 4 + C 2 * X ^ 3 + X ^ 2 : ℚ[X]) = F.charPoly (1, 0) := by
    refine F.charPoly_unique _ _ fun n => ?_
    simp [F]
    ring
  rw [Frame.tr, Frame.σ, ← h]
  simp [coeff_X_pow]

theorem Dξ_one_zero : F.Dξ (1, 0) = (2, 0) := by
  simp [Frame.Dξ, Frame.D, F]
  rfl

/-- In this model of all the axioms, with `I` not symmetric, the trace formula
`tr(α) I(ξ²) = 2 I(ξ, D_ξ(α))` fails for `α = (1, 0)`, whichever slot holds
`D_ξ(α)`: the two sides are `2` and `4`, or `2` and `0`. -/
theorem not_trace_formula :
    F.tr (1, 0) * ((F.I fun _ => F.ξ : ℤ) : ℚ) ≠
        2 * ((F.I (Function.update (fun _ => F.ξ) 0 (F.Dξ (1, 0)))) : ℚ) ∧
      F.tr (1, 0) * ((F.I fun _ => F.ξ : ℤ) : ℚ) ≠
        2 * ((F.I (Function.update (fun _ => F.ξ) 1 (F.Dξ (1, 0)))) : ℚ) := by
  rw [tr_one_zero, Dξ_one_zero]
  refine ⟨?_, ?_⟩ <;> simp [F, I_apply, Function.update]

end ModelA

/-! ### Rosati positivity does not follow -/

namespace ModelB

open Quaternion

/-- `I(x) = x` on `ℤ`, `r = 1`. -/
def I : MultilinearMap ℤ (fun _ : Fin 1 => ℤ) ℤ := MultilinearMap.mkPiAlgebra ℤ (Fin 1) ℤ

theorem I_apply (v : Fin 1 → ℤ) : I v = v 0 := by
  simp [I, MultilinearMap.mkPiAlgebra_apply]

/-- `E = ℍ[ℤ, 0, 0, 0]` with its conjugation, `N = ℤ`, `ξ = 1`, `α*x = (re α)² x`,
`ν(α) = (re α)²`. -/
def F : Frame ℍ[ℤ, 0, 0, 0] ℤ 1 where
  ψ := ⟨⟨fun x => (x : ℍ[ℤ, 0, 0, 0]), QuaternionAlgebra.coe_zero⟩,
    fun x y => QuaternionAlgebra.coe_add x y⟩
  ψ_injective := QuaternionAlgebra.coe_injective
  star_ψ := fun η => QuaternionAlgebra.star_coe η
  pb := fun u x => u.re ^ 2 * x
  ψ_pb := fun u x => by
    change ((u.re ^ 2 * x : ℤ) : ℍ[ℤ, 0, 0, 0]) = star u * (x : ℍ[ℤ, 0, 0, 0]) * u
    ext <;> simp [sq] <;> ring
  ξ := 1
  ψ_ξ := QuaternionAlgebra.coe_one
  I := I
  ν := fun u => u.re ^ 2
  I_pb := fun u v => by simp [I_apply]
  I_ξ := by simp [I_apply]

/-- `N⁺ = ℕ`, `N^> = ℕ∖{0}`. -/
def P : Positivity F where
  Pos := {x | 0 ≤ x}
  Amp := {x | 0 < x}
  Pos_add := fun x (hx : 0 ≤ x) y (hy : 0 ≤ y) => show 0 ≤ x + y from add_nonneg hx hy
  Pos_nsmul := fun n _ x (hx : 0 ≤ x) => show 0 ≤ n • x by
    simpa using mul_nonneg n.cast_nonneg hx
  Amp_add := fun x (hx : 0 < x) y (hy : 0 < y) => show 0 < x + y from add_pos hx hy
  Amp_nsmul := fun n hn x (hx : 0 < x) => show 0 < n • x by
    simpa using mul_pos (Nat.cast_pos.mpr hn) hx
  Amp_subset := fun x (hx : 0 < x) => show 0 ≤ x from hx.le
  Amp_closure := by
    refine eq_top_iff.mpr fun x _ => ?_
    have : (1 : ℤ) ∈ AddSubgroup.closure {x : ℤ | 0 < x} :=
      AddSubgroup.subset_closure (by simp)
    simpa using zsmul_mem this x
  Amp_iso := fun x (hx : 0 < x) => ⟨1, x, ne_of_gt hx, by ext <;> simp [F], by ext <;> simp [F]⟩
  I_pos := fun v hv => by
    change 0 < I v
    rw [I_apply]; exact hv 0
  ξ_mem := show (0 : ℤ) < 1 from one_pos
  Pos_pb := fun u x hx => by
    change 0 ≤ u.re ^ 2 * x
    exact mul_nonneg (sq_nonneg _) hx
  Amp_pb := fun u hu x hx => by
    change 0 < u.re ^ 2 * x
    have : 0 < u.re ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hu)
    exact mul_pos this hx

/-- The unit `i`, with `i² = 0`. -/
def i : ℍ[ℤ, 0, 0, 0] := ⟨0, 1, 0, 0⟩

theorem i_ne_zero : i ≠ 0 := fun h => by simpa [i] using congrArg QuaternionAlgebra.imI h

theorem star_i_mul_i : star i * i = 0 := by ext <;> simp [i]

theorem pb_i : F.pb i F.ξ = 0 := by simp [F, i]

/-- The extra axiom `I(ξ^{r−1}, η) > 0` for every nonzero `η ∈ N⁺` holds. -/
theorem nef_pos : ∀ η ∈ P.Pos, η ≠ 0 → 0 < F.I (Function.update (fun _ => F.ξ) 0 η) := by
  intro η hη h0
  have hη' : 0 ≤ η := hη
  have : F.I (Function.update (fun _ => F.ξ) 0 η) = η := by
    change I _ = η
    rw [I_apply]; simp
  rw [this]
  exact lt_of_le_of_ne hη' (Ne.symm h0)

/-- **The Corollaire fails**: `i ≠ 0` and `tr(i'i) = 0`. -/
theorem tr_star_i_mul_i : F.tr (star i * i) = 0 := by
  have h : (X ^ 2 : ℚ[X]) = F.charPoly (star i * i) := by
    refine F.charPoly_unique _ _ fun n => ?_
    simp [star_i_mul_i, F]
  rw [Frame.tr, Frame.σ, ← h]
  simp [coeff_X_pow]

end ModelB

end Grothendieck.Folder50
