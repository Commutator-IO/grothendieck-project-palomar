module

public import Mathlib
public import Grothendieck.Upstream.SingularValuesSigmaTwo

@[expose] public section


/-!
# Folder 1: the system (16) of page 71 for `m ≤ 2`, and (16) ⟹ (15)

The modernised reading `transcripts/1/1.modern.tex` (manuscript pages 71–73, Théorème 2)
states, for compact `u, v` and `0 ≤ m ≤ n`,

> `σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`  (16),

where `σ_n^m(w)` is the elementary symmetric function of degree `m` of the first `n`
singular values of `w` (17), and the product form

> `∏_{i≤n} (1 + r s_i(u+v)) ≤ ∏_{i≤n} (1 + r s_i(u)) ∏_{i≤n} (1 + r s_i(v))`, `r ≥ 0`  (15).

This is the finding `1-sigma-nm-system` of `src/content/findings.ts`. Proved here, for
linear maps between finite-dimensional inner product spaces over `ℝ` or `ℂ`, with mathlib's
`LinearMap.singularValues` (zero-indexed, so `s_0` is the largest):

* `sum_singularValues_add_le`: Ky Fan's inequality, the case `m = 1` of (16), for every `n`;
* `sigma_system_of_le_one`: (16) for `m ≤ 1` and every `n`;
* `prod_le_of_sigma_system`: (16) for all `m ≤ n` implies (15) for that `n`;
* `one_add_singularValues_zero_le`: (15) for `n = 1`;
* `sigma_two_add_le`: (16) for `m = 2`, `σ_n^2(u+v) ≤ σ_n^2(u) + σ_n^1(u) σ_n^1(v) + σ_n^2(v)`,
  for every `n`; hence `sigma_system_of_le_two` ((16) for `m ≤ 2`) and `prod_le_of_le_two`
  ((15) for `n ≤ 2`).

Ky Fan's maximum principle (`norm_sum_inner_le`) is proved for families that are pairwise
orthogonal of norm `≤ 1`, not only orthonormal. The case `m = 2` follows the page's route
through `Λ²` without building the Hilbert space `Λ² E`: the inner product
`⟪a ∧ b, c ∧ d⟫ = ⟪a, c⟫⟪b, d⟫ - ⟪a, d⟫⟪b, c⟫` is written as `2 × 2` minors (`minor2`), with
Cauchy–Binet (`two_mul_sum_minor`) and Lagrange's inequality (`sum_sum_norm_sub_sq_le`); the
mixed term `u ∧ v + v ∧ u` is bounded by `σ_n^1(u) σ_n^1(v)` (`norm_bform_le_mul`, the page's
constant `p! q!/(p+q)! = 1/2`), the pure terms by `2 σ_n^2` (`norm_bform_self_le`, through the
weight lemma `sum_sum_mul_le_of_weights`). Not proved: (16) for `3 ≤ m ≤ n`, Prop. 3 in
general, and the passage to compact operators. A proof says only that the claim holds as stated; whether
the system is in the literature stays open.

**Pages 123–124** (finding `1-mixed-schwarz-fredholm-coefficients`, issue #54), for complex
square matrices, with `α_k(T)` the coefficient of `X^k` in `det(1 + X T)` (`alpha`; by mathlib,
the sum of the principal `k × k` minors) and `|A| = (A*A)^{1/2}` mathlib's `CFC.abs`:

* `corollaire2`: `|α_k(A + B)|² ≤ α_k(|A| + |B|) · α_k(|A*| + |B*|)` — Corollaire 2 holds;
* `corollaire3`: `|det(1 + A + B)| ≤ ½[det(1 + |A| + |B|) + det(1 + |A*| + |B*|)]` (Corollaire 3)
  and the geometric-mean form `|det(1 + A + B)|² ≤ det(1 + |A| + |B|) det(1 + |A*| + |B*|)`.

The proof is not the page's multilinear expansion: `[[|A|, A*], [A, |A*|]]` is `|H| + H` for the
self-adjoint `H = [[0, A*], [A, 0]]`, hence `≥ 0` (`block_posSemidef`); adding the blocks of `A`
and `B` and restricting to `S ⊔ S`, each principal minor satisfies `|det T_S|² ≤ det P_S det Q_S`
(`norm_det_sq_le`, by the Schur complement and the monotonicity of `det`, `det_le_det_add`), and
Cauchy–Schwarz over the subsets `S` gives Corollaire 2. Trace-class operators are not formalised.

**Pages 126–139** (finding `1-schatten-p-via-fredholm-determinant`, issue #54), the route from
the Fredholm determinant to the subadditivity of `S_p`, `0 < p < 1`, in finite dimension:

* `integral_kernel`: `s^p · K_p = ∫₀^∞ log(1 + v s) v^{−1−p} dv` for `s ≥ 0`, with
  `K_p = ∫₀^∞ log(1 + t) t^{−1−p} dt > 0` (`K_pos`; its value `π/(p sin πp)` is not needed);
* `sum_rpow_le_of_prod_le`: if `∏ (1 + r aᵢ) ≤ ∏ (1 + r bᵢ) ∏ (1 + r cᵢ)` for all `r ≥ 0`, then
  `Σ aᵢ^p ≤ Σ bᵢ^p + Σ cᵢ^p` — page 129's deduction;
* `sum_singularValues_rpow_add_le_of_prod`: hence `S_p(u + v) ≤ S_p(u) + S_p(v)` on the first
  `n` singular values whenever (15) holds for that `n`, and unconditionally for `n ≤ 2`
  (`sum_singularValues_rpow_add_le_of_le_two`).

Not proved: (15) for `n ≥ 3`, so the subadditivity in general; Weyl's inequality via Jensen's
formula and the power trick; Hölder for all exponents.
-/

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Bessel's inequality for a finite family of pairwise orthogonal vectors of norm `≤ 1`. -/
theorem sum_norm_inner_sq_le {ι : Type*} (s : Finset ι) (y : ι → E)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫_𝕜 = 0) (hle : ∀ i ∈ s, ‖y i‖ ≤ 1)
    (z : E) : ∑ i ∈ s, ‖⟪y i, z⟫_𝕜‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  classical
  set c : ι → 𝕜 := fun i => ⟪y i, z⟫_𝕜 with hc
  set p : E := ∑ i ∈ s, c i • y i with hp
  set S : ℝ := ∑ i ∈ s, ‖c i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => by positivity
  have hpz : ⟪p, z⟫_𝕜 = (S : 𝕜) := by
    rw [hp, sum_inner, hS]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hc, RCLike.conj_mul]
  have hyp : ∀ i ∈ s, ⟪y i, p⟫_𝕜 = c i * ⟪y i, y i⟫_𝕜 := by
    intro i hi
    rw [hp, inner_sum, sum_eq_single i]
    · rw [inner_smul_right]
    · intro j hj hji
      rw [inner_smul_right, horth i hi j hj (Ne.symm hji), mul_zero]
    · intro h; exact absurd hi h
  have hpp : ‖p‖ ^ 2 ≤ S := by
    have h1 : ‖p‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 * ‖y i‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq 𝕜, hp, sum_inner, map_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [inner_smul_left, ← hp, hyp i hi, ← mul_assoc, RCLike.conj_mul,
        inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h1, hS]
    exact sum_le_sum fun i hi =>
      mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) (hle i hi))
  have hSle : S ≤ ‖p‖ * ‖z‖ := by
    have := norm_inner_le_norm (𝕜 := 𝕜) p z
    rwa [hpz, RCLike.norm_ofReal, abs_of_nonneg hS0] at this
  have hpz' : ‖p‖ ≤ ‖z‖ := by nlinarith [norm_nonneg p, norm_nonneg z]
  nlinarith [norm_nonneg z]


/-- The key counting step: for `s` antitone and nonnegative, and weights `0 ≤ c j ≤ 1` of total
mass `≤ n`, the weighted sum `∑ s j c j` is at most the sum of the `n` largest `s j`. -/
theorem sum_mul_le_sum_range {d : ℕ} (s : ℕ → ℝ) (hs : Antitone s) (hs0 : ∀ j, 0 ≤ s j)
    (c : Fin d → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) {n : ℕ}
    (hcn : ∑ j, c j ≤ n) : ∑ j : Fin d, s j * c j ≤ ∑ j ∈ range n, s j := by
  classical
  have key : ∀ j : Fin d, s j * c j ≤ (if (j : ℕ) < n then s j else 0)
      + s n * (c j - if (j : ℕ) < n then 1 else 0) := by
    intro j
    split_ifs with hj
    · have := hs hj.le
      nlinarith [hc1 j]
    · have := hs (not_lt.mp hj)
      nlinarith [hc0 j]
  have hcard : ∑ j : Fin d, c j ≤ ∑ j : Fin d, (if (j : ℕ) < n then (1 : ℝ) else 0) := by
    rw [sum_boole, Fin.card_filter_val_lt]
    rcases le_total d n with h | h
    · rw [min_eq_left h]
      calc ∑ j, c j ≤ ∑ _j : Fin d, (1 : ℝ) := sum_le_sum fun j _ => hc1 j
        _ = d := by simp
    · rw [min_eq_right h]; exact hcn
  have hfin : ∑ j : Fin d, (if (j : ℕ) < n then s j else 0) ≤ ∑ j ∈ range n, s j := by
    have h1 : ∑ j : Fin d, (if (j : ℕ) < n then s j else 0) =
        ∑ k ∈ range d, (if k < n then s k else 0) :=
      Fin.sum_univ_eq_sum_range (fun k => if k < n then s k else 0) d
    rw [h1, ← sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.2 (mem_filter.1 hk).2)
      fun k _ _ => hs0 k
  calc ∑ j : Fin d, s j * c j ≤ ∑ j : Fin d, ((if (j : ℕ) < n then s j else 0)
        + s n * (c j - if (j : ℕ) < n then 1 else 0)) := sum_le_sum fun j _ => key j
    _ = ∑ j : Fin d, (if (j : ℕ) < n then s j else 0)
        + s n * (∑ j : Fin d, c j - ∑ j : Fin d, (if (j : ℕ) < n then (1 : ℝ) else 0)) := by
          rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
    _ ≤ ∑ j ∈ range n, s j + s n * 0 :=
          add_le_add hfin (mul_le_mul_of_nonneg_left (by linarith) (hs0 n))
    _ = _ := by ring

/-- A sum over `range n` of a function vanishing from `d` on is a sum over `{j : Fin d | j < n}`. -/
theorem sum_range_eq_sum_filter (d : ℕ) (f : ℕ → ℝ) (hf : ∀ k, d ≤ k → f k = 0) (n : ℕ) :
    ∑ j ∈ range n, f j = ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) < n), f j := by
  have h1 : ∑ j : Fin d, (if (j : ℕ) < n then f j else 0) =
      ∑ k ∈ range d, (if k < n then f k else 0) :=
    Fin.sum_univ_eq_sum_range (fun k => if k < n then f k else 0) _
  rw [sum_filter, h1, ← sum_filter]
  symm
  apply sum_subset
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    exact hk.2
  · intro k hk hk'
    simp only [mem_filter, mem_range, not_and, not_lt] at hk hk'
    exact hf k (not_lt.mp fun h => (not_lt.mpr (hk' h)) hk)

section SVD

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- An orthonormal basis `(e_j)` of `E` made of eigenvectors of `T* T`, in the order of
decreasing eigenvalues `s_j(T)²`. -/
noncomputable def ebasis (T : E →ₗ[𝕜] F) : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

theorem inner_apply_ebasis (T : E →ₗ[𝕜] F) (j k : Fin (finrank 𝕜 E)) :
    ⟪T (ebasis T j), T (ebasis T k)⟫_𝕜 =
      ((T.singularValues k ^ 2 : ℝ) : 𝕜) * ⟪ebasis T j, ebasis T k⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply (LinearMap.adjoint T) T, ebasis,
    LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_right, T.sq_singularValues_fin rfl]

theorem norm_apply_ebasis (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ‖T (ebasis T j)‖ = T.singularValues j := by
  have h := inner_apply_ebasis T j j
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, (ebasis T).orthonormal.1 j] at h
  simp only [RCLike.ofReal_one, one_pow, mul_one] at h
  norm_cast at h
  exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp h

theorem inner_apply_ebasis_of_ne (T : E →ₗ[𝕜] F) {j k : Fin (finrank 𝕜 E)} (h : j ≠ k) :
    ⟪T (ebasis T j), T (ebasis T k)⟫_𝕜 = 0 := by
  rw [inner_apply_ebasis, (ebasis T).orthonormal.2 h, mul_zero]

/-- The second Schmidt family `f_j = s_j⁻¹ T e_j` (zero when `s_j = 0`). -/
noncomputable def fvec (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) : F :=
  (((T.singularValues j)⁻¹ : ℝ) : 𝕜) • T (ebasis T j)

theorem apply_ebasis_eq (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    T (ebasis T j) = ((T.singularValues j : ℝ) : 𝕜) • fvec T j := by
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · have h0 : T (ebasis T j) = 0 := by rw [← norm_eq_zero, norm_apply_ebasis, h]
    rw [h0, h, RCLike.ofReal_zero, zero_smul]
  · rw [fvec, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ h, RCLike.ofReal_one, one_smul]

theorem inner_fvec_of_ne (T : E →ₗ[𝕜] F) {j k : Fin (finrank 𝕜 E)} (h : j ≠ k) :
    ⟪fvec T j, fvec T k⟫_𝕜 = 0 := by
  rw [fvec, fvec, inner_smul_left, inner_smul_right, inner_apply_ebasis_of_ne T h, mul_zero,
    mul_zero]

theorem norm_fvec_le (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) : ‖fvec T j‖ ≤ 1 := by
  rw [fvec, norm_smul, norm_apply_ebasis, RCLike.norm_ofReal, abs_inv,
    abs_of_nonneg (T.singularValues_nonneg _)]
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem inner_fvec_apply_ebasis (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ⟪fvec T j, T (ebasis T j)⟫_𝕜 = ((T.singularValues j : ℝ) : 𝕜) := by
  rw [fvec, inner_smul_left, inner_self_eq_norm_sq_to_K, norm_apply_ebasis, RCLike.conj_ofReal]
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · simp [h]
  · rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- **Ky Fan's maximum principle, upper bound.** For families `(x_i)` in `E` and `(y_i)` in `F`
indexed by a set of `≤ n` elements, each pairwise orthogonal and of norm `≤ 1`,
`|∑ ⟪y_i, T x_i⟫| ≤ s_0(T) + ⋯ + s_{n-1}(T)`. -/
theorem norm_sum_inner_le {ι : Type*} (s : Finset ι) (x : ι → E) (y : ι → F)
    (hx : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪x i, x j⟫_𝕜 = 0) (hx1 : ∀ i ∈ s, ‖x i‖ ≤ 1)
    (hy : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫_𝕜 = 0) (hy1 : ∀ i ∈ s, ‖y i‖ ≤ 1)
    (T : E →ₗ[𝕜] F) {n : ℕ} (hn : #s ≤ n) :
    ‖∑ i ∈ s, ⟪y i, T (x i)⟫_𝕜‖ ≤ ∑ j ∈ range n, T.singularValues j := by
  have hexp : ∑ i ∈ s, ⟪y i, T (x i)⟫_𝕜 =
      ∑ j, ∑ i ∈ s, ⟪ebasis T j, x i⟫_𝕜 *
        (((T.singularValues j : ℝ) : 𝕜) * ⟪y i, fvec T j⟫_𝕜) := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    calc ⟪y i, T (x i)⟫_𝕜 = ⟪y i, T (∑ j, ⟪ebasis T j, x i⟫_𝕜 • ebasis T j)⟫_𝕜 := by
          rw [(ebasis T).sum_repr']
      _ = _ := by
          rw [map_sum, inner_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [map_smul, inner_smul_right, apply_ebasis_eq, inner_smul_right]
  have hbound : ‖∑ i ∈ s, ⟪y i, T (x i)⟫_𝕜‖ ≤
      ∑ j : Fin (finrank 𝕜 E), T.singularValues j * ((∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2
        + ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2) / 2) := by
    rw [hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_add_distrib, sum_div, mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (T.singularValues_nonneg _),
      norm_inner_symm (ebasis T j) (x i)]
    have hσ := T.singularValues_nonneg j
    nlinarith [mul_nonneg hσ (sq_nonneg (‖⟪x i, ebasis T j⟫_𝕜‖ - ‖⟪y i, fvec T j⟫_𝕜‖))]
  have ha1 : ∀ j, ∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 ≤ 1 := fun j => by
    have := sum_norm_inner_sq_le s x hx hx1 (ebasis T j)
    rwa [(ebasis T).orthonormal.1 j, one_pow] at this
  have hb1 : ∀ j, ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 ≤ 1 := fun j => by
    have := sum_norm_inner_sq_le s y hy hy1 (fvec T j)
    have h2 : ‖fvec T j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_fvec_le T j)
    linarith
  have ha : ∑ j, ∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 ≤ #s := by
    rw [sum_comm]
    calc ∑ i ∈ s, ∑ j, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := sum_norm_inner_sq_le univ (ebasis T)
            (fun j _ k _ h => (ebasis T).orthonormal.2 h)
            (fun j _ => ((ebasis T).orthonormal.1 j).le) (x i)
          have h1' : ∑ j, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 = ∑ j, ‖⟪ebasis T j, x i⟫_𝕜‖ ^ 2 :=
            sum_congr rfl fun j _ => by rw [norm_inner_symm]
          have h3 : ‖x i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hx1 i hi)
          linarith
      _ = #s := by simp
  have hb : ∑ j, ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 ≤ #s := by
    rw [sum_comm]
    calc ∑ i ∈ s, ∑ j, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := sum_norm_inner_sq_le univ (fvec T)
            (fun j _ k _ h => inner_fvec_of_ne T h) (fun j _ => norm_fvec_le T j) (y i)
          have h1' : ∑ j, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 = ∑ j, ‖⟪fvec T j, y i⟫_𝕜‖ ^ 2 :=
            sum_congr rfl fun j _ => by rw [norm_inner_symm]
          have h3 : ‖y i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hy1 i hi)
          linarith
      _ = #s := by simp
  refine hbound.trans (sum_mul_le_sum_range T.singularValues T.singularValues_antitone
    T.singularValues_nonneg
    (fun j => (∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 + ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2) / 2)
    (fun j => by positivity) (fun j => by linarith [ha1 j, hb1 j]) ?_)
  rw [← sum_div, sum_add_distrib]
  have : (#s : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The sum of the first `n` singular values, as a sum over the indices `j < dim E`. -/
theorem sum_range_singularValues_eq (T : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ j ∈ range n, T.singularValues j =
      ∑ j ∈ univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n), T.singularValues j :=
  sum_range_eq_sum_filter _ _ (fun _ hk => T.singularValues_of_finrank_le hk) n

/-- **Ky Fan's inequality** (the case `m = 1` of the system of page 71):
`s_0(u+v) + ⋯ + s_{n-1}(u+v) ≤ (s_0(u) + ⋯ + s_{n-1}(u)) + (s_0(v) + ⋯ + s_{n-1}(v))`. -/
theorem sum_singularValues_add_le (u v : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ j ∈ range n, (u + v).singularValues j ≤
      ∑ j ∈ range n, u.singularValues j + ∑ j ∈ range n, v.singularValues j :=
  LinearMap.sum_singularValues_add_le u v n

/-- `σ_n^m(T)`, the elementary symmetric function of degree `m` of the first `n` singular
values `s_0(T), …, s_{n-1}(T)` (page 71, (17)). -/
noncomputable def sigma (n m : ℕ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, T.singularValues i

theorem sigma_nonneg (n m : ℕ) (T : E →ₗ[𝕜] F) : 0 ≤ sigma n m T :=
  sum_nonneg fun _ _ => prod_nonneg fun i _ => T.singularValues_nonneg i

theorem sigma_zero (n : ℕ) (T : E →ₗ[𝕜] F) : sigma n 0 T = 1 := by simp [sigma]

theorem sigma_one (n : ℕ) (T : E →ₗ[𝕜] F) :
    sigma n 1 T = ∑ j ∈ range n, T.singularValues j := by
  simp [sigma, powersetCard_one]

/-- **The system (16) of page 71 for `m ≤ 1`**:
`σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`. For `m = 0` both sides are `1`; for `m = 1`
this is Ky Fan's inequality. -/
theorem sigma_system_of_le_one (u v : E →ₗ[𝕜] F) (n m : ℕ) (hm : m ≤ 1) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  interval_cases m
  · simp [sigma_zero]
  · simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
      sigma_zero, sigma_one, one_mul, mul_one]
    linarith [sum_singularValues_add_le u v n]

end SVD

/-- `∏_{i<n} (1 + r a_i) = ∑_{m=0}^{n} r^m e_m(a_0, …, a_{n-1})`. -/
theorem prod_one_add_eq (a : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    ∏ i ∈ range n, (1 + r * a i) =
      ∑ m ∈ range (n + 1), r ^ m * ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, a i := by
  rw [prod_one_add, sum_powerset, card_range]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp ht).2]

/-- The Cauchy-product step: coefficientwise bounds `C_m ≤ ∑_{p ≤ m} A_p B_{m-p}` for `m ≤ n`
give `∑_{m ≤ n} r^m C_m ≤ (∑_{m ≤ n} r^m A_m)(∑_{m ≤ n} r^m B_m)` for `r ≥ 0`. -/
theorem sum_pow_mul_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (A B C : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hB : ∀ m, 0 ≤ B m) (h : ∀ m ≤ n, C m ≤ ∑ p ∈ range (m + 1), A p * B (m - p)) :
    ∑ m ∈ range (n + 1), r ^ m * C m ≤
      (∑ m ∈ range (n + 1), r ^ m * A m) * ∑ m ∈ range (n + 1), r ^ m * B m := by
  have g0 : ∀ p k, 0 ≤ r ^ p * A p * (r ^ k * B k) := fun p k => by
    have := hA p; have := hB k; positivity
  have hcomm := sum_Ico_Ico_comm 0 (n + 1) (fun p m => r ^ p * A p * (r ^ (m - p) * B (m - p)))
  simp only [Nat.Ico_zero_eq_range] at hcomm
  calc ∑ m ∈ range (n + 1), r ^ m * C m
      ≤ ∑ m ∈ range (n + 1), ∑ p ∈ range (m + 1), r ^ p * A p * (r ^ (m - p) * B (m - p)) := by
        refine sum_le_sum fun m hm => ?_
        have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
        calc r ^ m * C m ≤ r ^ m * ∑ p ∈ range (m + 1), A p * B (m - p) :=
              mul_le_mul_of_nonneg_left (h m hmn) (pow_nonneg hr m)
          _ = _ := by
            rw [mul_sum]
            refine sum_congr rfl fun p hp => ?_
            have hpm : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hp)
            rw [show r ^ m = r ^ p * r ^ (m - p) by rw [← pow_add, Nat.add_sub_cancel' hpm]]
            ring
    _ = ∑ p ∈ range (n + 1), ∑ m ∈ Ico p (n + 1), r ^ p * A p * (r ^ (m - p) * B (m - p)) :=
        hcomm.symm
    _ = ∑ p ∈ range (n + 1), ∑ k ∈ range (n + 1 - p), r ^ p * A p * (r ^ k * B k) := by
        refine sum_congr rfl fun p _ => ?_
        rw [sum_Ico_eq_sum_range]
        refine sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_cancel_left]
    _ ≤ ∑ p ∈ range (n + 1), ∑ k ∈ range (n + 1), r ^ p * A p * (r ^ k * B k) := by
        refine sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => g0 p k
        intro k hk
        exact mem_range.mpr ((mem_range.mp hk).trans_le (Nat.sub_le _ _))
    _ = _ := by rw [sum_mul_sum]

section Product

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The system (16) implies the product form (15)** (page 71): if
`σ_n^m(u+v) ≤ ∑_{p ≤ m} σ_n^p(u) σ_n^{m-p}(v)` for all `m ≤ n`, then for `r ≥ 0`,
`∏_{i<n} (1 + r s_i(u+v)) ≤ ∏_{i<n} (1 + r s_i(u)) ∏_{i<n} (1 + r s_i(v))`. -/
theorem prod_le_of_sigma_system (u v : E →ₗ[𝕜] F) (n : ℕ)
    (h : ∀ m ≤ n, sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v)
    {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ range n, (1 + r * (u + v).singularValues i) ≤
      (∏ i ∈ range n, (1 + r * u.singularValues i)) *
        ∏ i ∈ range n, (1 + r * v.singularValues i) := by
  rw [prod_one_add_eq, prod_one_add_eq, prod_one_add_eq]
  exact sum_pow_mul_le hr (fun m => sigma n m u) (fun m => sigma n m v)
    (fun m => sigma n m (u + v)) (fun m => sigma_nonneg n m u) (fun m => sigma_nonneg n m v) h

/-- The product form (15) for `n = 1`: `1 + r s_0(u+v) ≤ (1 + r s_0(u)) (1 + r s_0(v))`. -/
theorem one_add_singularValues_zero_le (u v : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) :
    1 + r * (u + v).singularValues 0 ≤
      (1 + r * u.singularValues 0) * (1 + r * v.singularValues 0) := by
  simpa using prod_le_of_sigma_system u v 1 (fun m hm => sigma_system_of_le_one u v 1 m hm) hr

end Product

/-! ## The system (16) for `m = 2` -/

open scoped ComplexConjugate

/-- Lagrange's inequality: `∑_{i,j ∈ S} |a_i b_j - a_j b_i|² ≤ 2 (∑ |a_i|²)(∑ |b_i|²)`. -/
theorem sum_sum_norm_sub_sq_le {ι : Type*} (S : Finset ι) (a b : ι → 𝕜) :
    ∑ i ∈ S, ∑ j ∈ S, ‖a i * b j - a j * b i‖ ^ 2 ≤
      2 * (∑ i ∈ S, ‖a i‖ ^ 2) * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  set z : ι → 𝕜 := fun i => conj (a i) * b i with hz
  have key : ∀ i j, ‖a i * b j - a j * b i‖ ^ 2 =
      (‖a i‖ ^ 2 * ‖b j‖ ^ 2 + ‖a j‖ ^ 2 * ‖b i‖ ^ 2) - 2 * RCLike.re (z i * conj (z j)) := by
    intro i j
    rw [@norm_sub_sq 𝕜, RCLike.inner_apply', norm_mul, norm_mul]
    have : conj (a i * b j) * (a j * b i) = z i * conj (z j) := by
      simp only [hz, map_mul, RCLike.conj_conj]; ring
    rw [this]; ring
  have h2 : ∑ i ∈ S, ∑ j ∈ S, RCLike.re (z i * conj (z j)) = ‖∑ i ∈ S, z i‖ ^ 2 := by
    have h : (∑ i ∈ S, z i) * conj (∑ i ∈ S, z i) = ∑ i ∈ S, ∑ j ∈ S, z i * conj (z j) := by
      rw [map_sum, sum_mul_sum]
    rw [RCLike.mul_conj] at h
    have h' := congrArg RCLike.re h
    rw [← RCLike.ofReal_pow, RCLike.ofReal_re] at h'
    rw [h']
    simp only [map_sum]
  have h3 : ∑ i ∈ S, ∑ j ∈ S, (‖a i‖ ^ 2 * ‖b j‖ ^ 2 + ‖a j‖ ^ 2 * ‖b i‖ ^ 2) =
      2 * (∑ i ∈ S, ‖a i‖ ^ 2) * ∑ i ∈ S, ‖b i‖ ^ 2 := by
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun i j => ‖a j‖ ^ 2 * ‖b i‖ ^ 2), mul_assoc, sum_mul_sum]
    ring
  calc ∑ i ∈ S, ∑ j ∈ S, ‖a i * b j - a j * b i‖ ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, (‖a i‖ ^ 2 * ‖b j‖ ^ 2 + ‖a j‖ ^ 2 * ‖b i‖ ^ 2)
        - 2 * ∑ i ∈ S, ∑ j ∈ S, RCLike.re (z i * conj (z j)) := by
        simp only [key, sum_sub_distrib, mul_sum]
    _ ≤ _ := by rw [h3, h2]; nlinarith [sq_nonneg ‖∑ i ∈ S, z i‖]

/-- `2 e_2(f_0, …, f_{n-1}) = (∑ f_i)² - ∑ f_i²`. -/
theorem two_mul_sum_powersetCard_two (f : ℕ → ℝ) (n : ℕ) :
    2 * ∑ t ∈ (range n).powersetCard 2, ∏ i ∈ t, f i =
      (∑ i ∈ range n, f i) ^ 2 - ∑ i ∈ range n, f i ^ 2 := by
  induction n with
  | zero => rw [range_zero, powersetCard_eq_empty.mpr (by simp)]; simp
  | succ n ih =>
    have hn : n ∉ range n := notMem_range_self
    rw [range_add_one, powersetCard_succ_insert hn, sum_union, sum_image, sum_insert hn,
      sum_insert hn, mul_add, ih, powersetCard_one, sum_map]
    · have : ∑ x ∈ range n, ∏ i ∈ insert n ({x} : Finset ℕ), f i = f n * ∑ i ∈ range n, f i := by
        rw [mul_sum]
        refine sum_congr rfl fun x hx => ?_
        rw [prod_insert (by simpa using (ne_of_gt (mem_range.mp hx))), prod_singleton]
      simp only [Function.Embedding.coeFn_mk] at this ⊢
      rw [this]; ring
    · intro t ht t' ht' h
      have h1 : n ∉ t := fun h => hn ((mem_powersetCard.mp ht).1 h)
      have h2 : n ∉ t' := fun h => hn ((mem_powersetCard.mp ht').1 h)
      rw [← erase_insert h1, ← erase_insert h2, h]
    · rw [disjoint_left]
      intro t ht ht'
      obtain ⟨t', _, rfl⟩ := mem_image.mp ht'
      exact hn ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

/-- The weight lemma for `σ²`. Let `s ≥ 0` and `θ ≥ 0` with `s_k ≥ θ` on a finite set `G` and
`s_k ≤ θ` off `G`. Let `(α_{kl})` be symmetric with entries in `[0,1]` and zero diagonal, and
`p_k ∈ [0,1]` with `∑ p_k ≤ |G|` and row sums `∑_l α_{kl} ≤ (|G| - 1) p_k`. Then
`∑_{k,l} α_{kl} s_k s_l ≤ (∑_{k ∈ G} s_k)² - ∑_{k ∈ G} s_k²`. -/
theorem sum_sum_mul_le_of_weights {κ : Type*} [Fintype κ] [DecidableEq κ] (G : Finset κ)
    (s : κ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (hs0 : ∀ k, 0 ≤ s k) (hG : ∀ k ∈ G, θ ≤ s k)
    (hGc : ∀ k ∉ G, s k ≤ θ) (α : κ → κ → ℝ) (p : κ → ℝ) (hα0 : ∀ k l, 0 ≤ α k l)
    (hα1 : ∀ k l, α k l ≤ 1) (hdiag : ∀ k, α k k = 0) (hsymm : ∀ k l, α k l = α l k)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (hrow : ∀ k, ∑ l, α k l ≤ ((#G : ℝ) - 1) * p k)
    (hp : ∑ k, p k ≤ #G) :
    ∑ k, ∑ l, α k l * (s k * s l) ≤ (∑ k ∈ G, s k) ^ 2 - ∑ k ∈ G, s k ^ 2 := by
  set g : ℝ := (#G : ℝ) with hg
  set m : κ → ℝ := fun k => min (s k) θ with hm
  set d : κ → ℝ := fun k => s k - m k with hd
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_min (hs0 k) hθ
  have hmθ : ∀ k, m k ≤ θ := fun k => min_le_right _ _
  have hd0 : ∀ k, 0 ≤ d k := fun k => sub_nonneg.mpr (min_le_left _ _)
  have hdG : ∀ k ∉ G, d k = 0 := fun k hk => by
    simp only [hd, hm, min_eq_left (hGc k hk), sub_self]
  have hmG : ∀ k ∈ G, m k = θ := fun k hk => min_eq_right (hG k hk)
  have hsd : ∀ k, s k = m k + d k := fun k => by simp only [hd]; ring
  set D : ℝ := ∑ k ∈ G, d k with hD
  have hDu : ∑ k, d k = D := (sum_subset (subset_univ G) fun k _ hk => hdG k hk).symm
  have hd2u : ∑ k, d k ^ 2 = ∑ k ∈ G, d k ^ 2 :=
    (sum_subset (subset_univ G) fun k _ hk => by rw [hdG k hk]; ring).symm
  -- the three bounds
  have hcol : ∀ l, ∑ k, α k l ≤ (g - 1) * p l := fun l => by
    simpa only [hsymm _ l] using hrow l
  have hdp : ∀ l, d l * ((g - 1) * p l) ≤ d l * (g - 1) := fun l => by
    by_cases hl : l ∈ G
    · have : (1 : ℝ) ≤ g := by rw [hg]; exact_mod_cast card_pos.mpr ⟨l, hl⟩
      have := hd0 l; have := hp1 l
      nlinarith [mul_nonneg (hd0 l) (sub_nonneg.mpr this)]
    · rw [hdG l hl]; ring_nf; rfl
  have hgp : (g - 1) * ∑ k, p k ≤ (g - 1) * g := by
    rcases Nat.eq_zero_or_pos #G with h0 | h0
    · have hg0 : g = 0 := by rw [hg, h0]; simp
      have : 0 ≤ ∑ k, p k := sum_nonneg fun k _ => hp0 k
      rw [hg0]; linarith [hp, hg0]
    · have : (1 : ℝ) ≤ g := by rw [hg]; exact_mod_cast h0
      exact mul_le_mul_of_nonneg_left hp (by linarith)
  have b1 : ∑ k, ∑ l, α k l * (m k * m l) ≤ θ ^ 2 * ((g - 1) * g) := by
    calc ∑ k, ∑ l, α k l * (m k * m l) ≤ ∑ k, ∑ l, α k l * θ ^ 2 := by
          refine sum_le_sum fun k _ => sum_le_sum fun l _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hα0 k l)
          rw [sq]; exact mul_le_mul (hmθ k) (hmθ l) (hm0 l) hθ
      _ = θ ^ 2 * ∑ k, ∑ l, α k l := by rw [mul_sum]; simp only [← sum_mul, mul_comm]
      _ ≤ θ ^ 2 * ((g - 1) * ∑ k, p k) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg θ)
          rw [mul_sum]; exact sum_le_sum fun k _ => hrow k
      _ ≤ _ := mul_le_mul_of_nonneg_left hgp (sq_nonneg θ)
  have b2 : ∑ k, ∑ l, α k l * (m k * d l) ≤ θ * ((g - 1) * D) := by
    calc ∑ k, ∑ l, α k l * (m k * d l) ≤ ∑ k, ∑ l, α k l * (θ * d l) := by
          refine sum_le_sum fun k _ => sum_le_sum fun l _ => ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmθ k) (hd0 l)) (hα0 k l)
      _ = θ * ∑ l, d l * ∑ k, α k l := by
          rw [sum_comm, mul_sum]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun k _ => ?_
          ring
      _ ≤ θ * ∑ l, d l * (g - 1) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun l _ => ?_) hθ
          exact (mul_le_mul_of_nonneg_left (hcol l) (hd0 l)).trans (hdp l)
      _ = _ := by rw [← sum_mul, hDu]; ring
  have b3 : ∑ k, ∑ l, α k l * (d k * m l) ≤ θ * ((g - 1) * D) := by
    calc ∑ k, ∑ l, α k l * (d k * m l) ≤ ∑ k, ∑ l, α k l * (d k * θ) := by
          refine sum_le_sum fun k _ => sum_le_sum fun l _ => ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmθ l) (hd0 k)) (hα0 k l)
      _ = θ * ∑ k, d k * ∑ l, α k l := by
          rw [mul_sum]
          refine sum_congr rfl fun k _ => ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun l _ => ?_
          ring
      _ ≤ θ * ∑ k, d k * (g - 1) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_) hθ
          exact (mul_le_mul_of_nonneg_left (hrow k) (hd0 k)).trans (hdp k)
      _ = _ := by rw [← sum_mul, hDu]; ring
  have b4 : ∑ k, ∑ l, α k l * (d k * d l) ≤ D ^ 2 - ∑ k ∈ G, d k ^ 2 := by
    calc ∑ k, ∑ l, α k l * (d k * d l)
        ≤ ∑ k, ∑ l, (d k * d l - if k = l then d k * d l else 0) := by
          refine sum_le_sum fun k _ => sum_le_sum fun l _ => ?_
          split_ifs with h
          · rw [h, hdiag]; simp
          · have := mul_nonneg (hd0 k) (hd0 l)
            nlinarith [hα1 k l]
      _ = _ := by
          simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]
          rw [← sum_mul_sum, hDu, ← hd2u]
          simp only [sq]
  have hsG : ∑ k ∈ G, s k = g * θ + D := by
    rw [sum_congr rfl fun k hk => (show s k = θ + d k by rw [hsd, hmG k hk]), sum_add_distrib,
      sum_const, nsmul_eq_mul]
  have hs2G : ∑ k ∈ G, s k ^ 2 = g * θ ^ 2 + 2 * θ * D + ∑ k ∈ G, d k ^ 2 := by
    rw [sum_congr rfl fun k hk => (show s k ^ 2 = θ ^ 2 + 2 * θ * d k + d k ^ 2 by
      rw [hsd, hmG k hk]; ring), sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul,
      ← mul_sum]
  calc ∑ k, ∑ l, α k l * (s k * s l)
      = ∑ k, ∑ l, α k l * (m k * m l) + ∑ k, ∑ l, α k l * (m k * d l)
        + ∑ k, ∑ l, α k l * (d k * m l) + ∑ k, ∑ l, α k l * (d k * d l) := by
        simp only [← sum_add_distrib]
        refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
        rw [hsd k, hsd l]; ring
    _ ≤ θ ^ 2 * ((g - 1) * g) + θ * ((g - 1) * D) + θ * ((g - 1) * D)
        + (D ^ 2 - ∑ k ∈ G, d k ^ 2) := by linarith
    _ = _ := by rw [hsG, hs2G]; ring

section Frames

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The `2 × 2` minor `⟪g_k, h_i⟫⟪g'_l, h_j⟫ - ⟪g_k, h_j⟫⟪g'_l, h_i⟫`, that is
`⟪g_k ∧ g'_l, h_i ∧ h_j⟫` up to conjugation. -/
def minor2 {κ ι : Type*} (g g' : κ → H) (h : ι → H) (k l : κ) (i j : ι) : 𝕜 :=
  ⟪g k, h i⟫_𝕜 * ⟪g' l, h j⟫_𝕜 - ⟪g k, h j⟫_𝕜 * ⟪g' l, h i⟫_𝕜

/-- `Λ_{kl} = ∑_{i,j ∈ S} |minor2 g g' h k l i j|²`. -/
def lam {κ ι : Type*} (g g' : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, ‖(minor2 g g' h k l i j : 𝕜)‖ ^ 2

/-- `p_k = ∑_{i ∈ S} |⟪g_k, h_i⟫|²`. -/
def wt {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k : κ) : ℝ :=
  ∑ i ∈ S, ‖⟪g k, h i⟫_𝕜‖ ^ 2

theorem lam_nonneg {κ ι : Type*} (g g' : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) :
    0 ≤ lam (𝕜 := 𝕜) g g' h S k l :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

theorem wt_nonneg {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k : κ) :
    0 ≤ wt (𝕜 := 𝕜) g h S k :=
  sum_nonneg fun _ _ => by positivity

theorem lam_le {κ ι : Type*} (g g' : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) :
    lam (𝕜 := 𝕜) g g' h S k l ≤ 2 * wt (𝕜 := 𝕜) g h S k * wt (𝕜 := 𝕜) g' h S l :=
  sum_sum_norm_sub_sq_le S (fun i => ⟪g k, h i⟫_𝕜) (fun i => ⟪g' l, h i⟫_𝕜)

theorem lam_self {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k : κ) :
    lam (𝕜 := 𝕜) g g h S k k = 0 := by
  simp [lam, minor2, mul_comm]

theorem lam_symm {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) :
    lam (𝕜 := 𝕜) g g h S k l = lam (𝕜 := 𝕜) g g h S l k := by
  unfold lam
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [← norm_neg (minor2 g g h l k i j)]
  congr 2
  simp only [minor2]; ring

variable {ι : Type*} (S : Finset ι) (h : ι → H)
  (hh : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪h i, h j⟫_𝕜 = 0) (hh1 : ∀ i ∈ S, ‖h i‖ ≤ 1)
include hh hh1

theorem wt_le_one {κ : Type*} (g : κ → H) (hg1 : ∀ k, ‖g k‖ ≤ 1) (k : κ) :
    wt (𝕜 := 𝕜) g h S k ≤ 1 := by
  have := sum_norm_inner_sq_le S h hh hh1 (g k)
  have h2 : ‖g k‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hg1 k)
  unfold wt
  simp only [norm_inner_symm (g k)]
  linarith

omit hh in
theorem sum_wt_le {κ : Type*} [Fintype κ] (g : κ → H)
    (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫_𝕜 = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1) :
    ∑ k, wt (𝕜 := 𝕜) g h S k ≤ #S := by
  unfold wt
  rw [sum_comm]
  calc ∑ i ∈ S, ∑ k, ‖⟪g k, h i⟫_𝕜‖ ^ 2 ≤ ∑ _i ∈ S, (1 : ℝ) := by
        refine sum_le_sum fun i hi => ?_
        have := sum_norm_inner_sq_le univ g (fun k _ l _ hkl => hg k l hkl) (fun k _ => hg1 k)
          (h i)
        have h3 : ‖h i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hh1 i hi)
        linarith
    _ = #S := by simp

/-- Row sums of `Λ`: `∑_l Λ_{kl} ≤ 2 (|S| - 1) p_k`, by Bessel's inequality in the index `l`. -/
theorem sum_lam_le {κ : Type*} [Fintype κ] (g : κ → H)
    (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫_𝕜 = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1) (k : κ) :
    ∑ l, lam (𝕜 := 𝕜) g g h S k l ≤ 2 * ((#S : ℝ) - 1) * wt (𝕜 := 𝕜) g h S k := by
  classical
  unfold lam
  set c : ι → 𝕜 := fun i => ⟪g k, h i⟫_𝕜 with hc
  have hz : ∀ l i j, minor2 g g h k l i j = ⟪g l, c i • h j - c j • h i⟫_𝕜 := by
    intro l i j
    simp only [minor2, inner_sub_right, inner_smul_right, hc]
  have hij : ∀ i ∈ S, ∀ j ∈ S, ∑ l, ‖(minor2 g g h k l i j : 𝕜)‖ ^ 2 ≤
      ‖c i‖ ^ 2 + ‖c j‖ ^ 2 - (if i = j then 2 * ‖c i‖ ^ 2 else 0) := by
    intro i hi j hj
    simp only [hz]
    refine (sum_norm_inner_sq_le univ g (fun k _ l _ hkl => hg k l hkl) (fun k _ => hg1 k)
      _).trans ?_
    split_ifs with h0
    · subst h0; simp; linarith
    · rw [@norm_sub_sq 𝕜, inner_smul_left, inner_smul_right, hh j hj i hi (Ne.symm h0),
        mul_zero, mul_zero, map_zero, mul_zero, sub_zero, norm_smul, norm_smul]
      have := hh1 i hi; have := hh1 j hj
      have h1 : ‖h j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hh1 j hj)
      have h2 : ‖h i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hh1 i hi)
      rw [mul_pow, mul_pow]
      nlinarith [sq_nonneg ‖c i‖, sq_nonneg ‖c j‖]
  rw [sum_comm]
  calc ∑ i ∈ S, ∑ l, ∑ j ∈ S, ‖(minor2 g g h k l i j : 𝕜)‖ ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, ∑ l, ‖(minor2 g g h k l i j : 𝕜)‖ ^ 2 :=
        sum_congr rfl fun i _ => sum_comm
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (‖c i‖ ^ 2 + ‖c j‖ ^ 2 - (if i = j then 2 * ‖c i‖ ^ 2 else 0)) :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hij i hi j hj
    _ = ∑ i ∈ S, ((#S : ℝ) * ‖c i‖ ^ 2 + ∑ j ∈ S, ‖c j‖ ^ 2 - 2 * ‖c i‖ ^ 2) := by
        refine sum_congr rfl fun i hi => ?_
        rw [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
        simp only [sum_ite_eq, ite_eq_left hi]
    _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← mul_sum]
        simp only [wt, hc]
        ring

/-- The weight lemma applied to `α_{kl} = Λ_{kl} / 2` and `p_k = wt g h S k`. -/
theorem sum_lam_mul_le {κ : Type*} [Fintype κ] [DecidableEq κ] (g : κ → H)
    (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫_𝕜 = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1) (G : Finset κ)
    (s : κ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (hs0 : ∀ k, 0 ≤ s k) (hG : ∀ k ∈ G, θ ≤ s k)
    (hGc : ∀ k ∉ G, s k ≤ θ) (hSG : #S ≤ #G) :
    ∑ k, ∑ l, lam (𝕜 := 𝕜) g g h S k l / 2 * (s k * s l) ≤
      (∑ k ∈ G, s k) ^ 2 - ∑ k ∈ G, s k ^ 2 := by
  have hSG' : ((#S : ℕ) : ℝ) ≤ #G := by exact_mod_cast hSG
  have hp1 := wt_le_one S h hh hh1 g hg1
  have hp0 := wt_nonneg (𝕜 := 𝕜) g h S
  refine sum_sum_mul_le_of_weights G s hθ hs0 hG hGc (fun k l => lam (𝕜 := 𝕜) g g h S k l / 2)
    (wt (𝕜 := 𝕜) g h S) (fun k l => by have := lam_nonneg (𝕜 := 𝕜) g g h S k l; positivity)
    (fun k l => ?_) (fun k => by simp [lam_self]) (fun k l => by rw [lam_symm]) hp0 hp1
    (fun k => ?_) ((sum_wt_le S h hh1 g hg hg1).trans hSG')
  · have := lam_le (𝕜 := 𝕜) g g h S k l
    have := mul_le_mul (hp1 k) (hp1 l) (hp0 l) zero_le_one
    linarith
  · have := sum_lam_le S h hh hh1 g hg hg1 k
    rw [← sum_div]
    have := hp0 k
    nlinarith

end Frames

/-- The algebraic identity behind `Λ²`: for `A_{ij} = ∑_k s_k P_{ik} Q_{kj}` and
`C_{ij} = ∑_l t_l P'_{il} Q'_{lj}`, twice the sum of the mixed principal `2 × 2` minors is
`∑_{k,l} s_k t_l ∑_{i,j} (P_{ik} P'_{jl} - P_{jk} P'_{il}) (Q_{ki} Q'_{lj} - Q_{kj} Q'_{li})`
(Cauchy–Binet for `2 × 2` minors). -/
theorem two_mul_sum_minor {R ι κ : Type*} [CommRing R] [Fintype κ] (S : Finset ι)
    (s t : κ → R) (P P' : ι → κ → R) (Q Q' : κ → ι → R) :
    2 * ∑ i ∈ S, ∑ j ∈ S, ((∑ k, s k * P i k * Q k i) * (∑ l, t l * P' j l * Q' l j) -
        (∑ k, s k * P i k * Q k j) * (∑ l, t l * P' j l * Q' l i)) =
      ∑ k, ∑ l, s k * t l * ∑ i ∈ S, ∑ j ∈ S,
        (P i k * P' j l - P j k * P' i l) * (Q k i * Q' l j - Q k j * Q' l i) := by
  set f1 : κ → κ → ι → ι → R := fun k l i j => P i k * Q k i * (P' j l * Q' l j) with hf1
  set f2 : κ → κ → ι → ι → R := fun k l i j => P i k * Q k j * (P' j l * Q' l i) with hf2
  have hin : ∀ k l, ∑ i ∈ S, ∑ j ∈ S,
      (P i k * P' j l - P j k * P' i l) * (Q k i * Q' l j - Q k j * Q' l i) =
        2 * ∑ i ∈ S, ∑ j ∈ S, (f1 k l i j - f2 k l i j) := by
    intro k l
    have e : ∀ i j, (P i k * P' j l - P j k * P' i l) * (Q k i * Q' l j - Q k j * Q' l i) =
        (f1 k l i j - f2 k l i j) + (f1 k l j i - f2 k l j i) := by
      intro i j; simp only [hf1, hf2]; ring
    simp only [e, sum_add_distrib]
    rw [sum_comm (f := fun i j => f1 k l j i - f2 k l j i)]
    ring
  have hout : ∀ i j, (∑ k, s k * P i k * Q k i) * (∑ l, t l * P' j l * Q' l j) -
      (∑ k, s k * P i k * Q k j) * (∑ l, t l * P' j l * Q' l i) =
        ∑ k, ∑ l, s k * t l * (f1 k l i j - f2 k l i j) := by
    intro i j
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun l _ => ?_
    simp only [hf1, hf2]; ring
  simp only [hout, hin]
  simp only [mul_sum]
  calc _ = ∑ i ∈ S, ∑ k, ∑ j ∈ S, ∑ l, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ k, ∑ i ∈ S, ∑ j ∈ S, ∑ l, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) := sum_comm
    _ = ∑ k, ∑ i ∈ S, ∑ l, ∑ j ∈ S, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) :=
        sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_comm
    _ = ∑ k, ∑ l, ∑ i ∈ S, ∑ j ∈ S, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) :=
        sum_congr rfl fun k _ => sum_comm
    _ = _ := by
        refine sum_congr rfl fun k _ => sum_congr rfl fun l _ =>
          sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        ring

section SigmaTwoOp

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The Schmidt expansion `⟪y, T x⟫ = ∑_k s_k(T) ⟪y, f_k⟫ ⟪e_k, x⟫`. -/
theorem inner_apply_eq_sum (T : E →ₗ[𝕜] F) (x : E) (y : F) :
    ⟪y, T x⟫_𝕜 = ∑ k : Fin (finrank 𝕜 E), ((T.singularValues k : ℝ) : 𝕜) * conj ⟪fvec T k, y⟫_𝕜 *
      ⟪ebasis T k, x⟫_𝕜 := by
  calc ⟪y, T x⟫_𝕜 = ⟪y, T (∑ k : Fin (finrank 𝕜 E), ⟪ebasis T k, x⟫_𝕜 • ebasis T k)⟫_𝕜 := by
        rw [(ebasis T).sum_repr']
    _ = _ := by
        rw [map_sum, inner_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [map_smul, inner_smul_right, apply_ebasis_eq, inner_smul_right, inner_conj_symm]
        ring

/-- The sum over ordered pairs `i, j ∈ S` of the mixed principal `2 × 2` minors of the
compressions `(⟪y_i, T x_j⟫)` and `(⟪y_i, T' x_j⟫)`; for `T = T'` it is twice the second
elementary symmetric function of the eigenvalues of the compression. -/
def bform {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F) (T T' : E →ₗ[𝕜] F) : 𝕜 :=
  ∑ i ∈ S, ∑ j ∈ S,
    (⟪y i, T (x i)⟫_𝕜 * ⟪y j, T' (x j)⟫_𝕜 - ⟪y i, T (x j)⟫_𝕜 * ⟪y j, T' (x i)⟫_𝕜)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
theorem bform_add {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F) (u v : E →ₗ[𝕜] F) :
    bform S x y (u + v) (u + v) =
      bform S x y u u + bform S x y u v + bform S x y v u + bform S x y v v := by
  simp only [bform, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [LinearMap.add_apply, inner_add_right]
  ring

/-- `|bform| ≤ ¼ ∑_{k,l} s_k(T) s_l(T') (Λ^f_{kl} + Λ^e_{kl})`, from the Cauchy–Binet identity
and `|ab| ≤ (|a|² + |b|²)/2`. -/
theorem norm_bform_le {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F) (T T' : E →ₗ[𝕜] F) :
    ‖bform S x y T T'‖ ≤ (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T'.singularValues l *
      (lam (𝕜 := 𝕜) (fvec T) (fvec T') y S k l +
        lam (𝕜 := 𝕜) (ebasis T) (ebasis T') x S k l) := by
  have h2 : (2 : 𝕜) * bform S x y T T' = ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), ((T.singularValues k : ℝ) : 𝕜) *
      ((T'.singularValues l : ℝ) : 𝕜) * ∑ i ∈ S, ∑ j ∈ S,
        conj (minor2 (fvec T) (fvec T') y k l i j) * minor2 (ebasis T) (ebasis T') x k l i j := by
    have := two_mul_sum_minor S (fun k : Fin (finrank 𝕜 E) => ((T.singularValues k : ℝ) : 𝕜))
      (fun l : Fin (finrank 𝕜 E) => ((T'.singularValues l : ℝ) : 𝕜))
      (fun i (k : Fin (finrank 𝕜 E)) => conj ⟪fvec T k, y i⟫_𝕜)
      (fun i (l : Fin (finrank 𝕜 E)) => conj ⟪fvec T' l, y i⟫_𝕜)
      (fun (k : Fin (finrank 𝕜 E)) j => ⟪ebasis T k, x j⟫_𝕜)
      (fun (l : Fin (finrank 𝕜 E)) j => ⟪ebasis T' l, x j⟫_𝕜)
    rw [bform]
    simp only [inner_apply_eq_sum T, inner_apply_eq_sum T']
    refine this.trans ?_
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [minor2, map_sub, map_mul]
  have hb : ‖(2 : 𝕜) * bform S x y T T'‖ ≤ ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T'.singularValues l *
      ((lam (𝕜 := 𝕜) (fvec T) (fvec T') y S k l +
        lam (𝕜 := 𝕜) (ebasis T) (ebasis T') x S k l) / 2) := by
    rw [h2]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ =>
      (norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
      abs_of_nonneg (T.singularValues_nonneg _), abs_of_nonneg (T'.singularValues_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (T.singularValues_nonneg _) (T'.singularValues_nonneg _))
    unfold lam
    rw [← sum_add_distrib, sum_div]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
    rw [← sum_add_distrib, sum_div]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖(minor2 (fvec T) (fvec T') y k l i j : 𝕜)‖ -
      ‖(minor2 (ebasis T) (ebasis T') x k l i j : 𝕜)‖)]
  have e : ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T'.singularValues l *
      ((lam (𝕜 := 𝕜) (fvec T) (fvec T') y S k l +
        lam (𝕜 := 𝕜) (ebasis T) (ebasis T') x S k l) / 2) =
      2 * ((1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T'.singularValues l *
      (lam (𝕜 := 𝕜) (fvec T) (fvec T') y S k l +
        lam (𝕜 := 𝕜) (ebasis T) (ebasis T') x S k l)) := by
    rw [← mul_assoc, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring
  rw [norm_mul, RCLike.norm_two, e] at hb
  linarith

variable {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F)
  (hx : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪x i, x j⟫_𝕜 = 0) (hx1 : ∀ i ∈ S, ‖x i‖ ≤ 1)
  (hy : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪y i, y j⟫_𝕜 = 0) (hy1 : ∀ i ∈ S, ‖y i‖ ≤ 1)
include hx hx1 hy hy1

/-- **The mixed term** (the bound `p! q!/(p+q)! = 1/2` of page 71 for `p = q = 1`):
`|bform S x y T T'| ≤ σ_n^1(T) σ_n^1(T')` when `|S| ≤ n`. -/
theorem norm_bform_le_mul (T T' : E →ₗ[𝕜] F) {n : ℕ} (hn : #S ≤ n) :
    ‖bform S x y T T'‖ ≤
      (∑ j ∈ range n, T.singularValues j) * ∑ j ∈ range n, T'.singularValues j := by
  have hKF : ∀ (T : E →ₗ[𝕜] F) (c : Fin (finrank 𝕜 E) → ℝ), (∀ k, 0 ≤ c k) → (∀ k, c k ≤ 1) →
      ∑ k : Fin (finrank 𝕜 E), c k ≤ #S → ∑ k : Fin (finrank 𝕜 E), T.singularValues k * c k ≤ ∑ j ∈ range n, T.singularValues j :=
    fun T c h0 h1 hs => sum_mul_le_sum_range T.singularValues T.singularValues_antitone
      T.singularValues_nonneg c h0 h1 (hs.trans (by exact_mod_cast hn))
  have hfo : ∀ T : E →ₗ[𝕜] F, ∀ k l, k ≠ l → ⟪fvec T k, fvec T l⟫_𝕜 = 0 :=
    fun T k l h => inner_fvec_of_ne T h
  have heo : ∀ T : E →ₗ[𝕜] F, ∀ k l, k ≠ l → ⟪ebasis T k, ebasis T l⟫_𝕜 = 0 :=
    fun T k l h => (ebasis T).orthonormal.2 h
  have he1 : ∀ T : E →ₗ[𝕜] F, ∀ k, ‖ebasis T k‖ ≤ 1 :=
    fun T k => ((ebasis T).orthonormal.1 k).le
  have Aq : ∀ T : E →ₗ[𝕜] F, ∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜) (fvec T) y S k ≤
      ∑ j ∈ range n, T.singularValues j := fun T =>
    hKF T _ (wt_nonneg _ _ _) (wt_le_one S y hy hy1 _ (norm_fvec_le T))
      (sum_wt_le S y hy1 _ (hfo T) (norm_fvec_le T))
  have Ap : ∀ T : E →ₗ[𝕜] F, ∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜) (ebasis T) x S k ≤
      ∑ j ∈ range n, T.singularValues j := fun T =>
    hKF T _ (wt_nonneg _ _ _) (wt_le_one S x hx hx1 _ (he1 T))
      (sum_wt_le S x hx1 _ (heo T) (he1 T))
  have N : ∀ (T : E →ₗ[𝕜] F) (c : Fin (finrank 𝕜 E) → ℝ), (∀ k, 0 ≤ c k) →
      0 ≤ ∑ k : Fin (finrank 𝕜 E), T.singularValues k * c k :=
    fun T c h => sum_nonneg fun k _ => mul_nonneg (T.singularValues_nonneg _) (h k)
  have K0 : ∀ T : E →ₗ[𝕜] F, 0 ≤ ∑ j ∈ range n, T.singularValues j :=
    fun T => sum_nonneg fun j _ => T.singularValues_nonneg j
  calc ‖bform S x y T T'‖
      ≤ (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T'.singularValues l *
        (lam (𝕜 := 𝕜) (fvec T) (fvec T') y S k l +
          lam (𝕜 := 𝕜) (ebasis T) (ebasis T') x S k l) := norm_bform_le S x y T T'
    _ ≤ (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T'.singularValues l *
        (2 * wt (𝕜 := 𝕜) (fvec T) y S k * wt (𝕜 := 𝕜) (fvec T') y S l +
          2 * wt (𝕜 := 𝕜) (ebasis T) x S k * wt (𝕜 := 𝕜) (ebasis T') x S l) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => sum_le_sum fun l _ => ?_)
          (by norm_num)
        exact mul_le_mul_of_nonneg_left (add_le_add (lam_le _ _ _ _ _ _) (lam_le _ _ _ _ _ _))
          (mul_nonneg (T.singularValues_nonneg _) (T'.singularValues_nonneg _))
    _ = (1 / 2) * ((∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜) (fvec T) y S k) *
          (∑ l : Fin (finrank 𝕜 E), T'.singularValues l * wt (𝕜 := 𝕜) (fvec T') y S l) +
        (∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜) (ebasis T) x S k) *
          (∑ l : Fin (finrank 𝕜 E), T'.singularValues l * wt (𝕜 := 𝕜) (ebasis T') x S l)) := by
        rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib, mul_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [← sum_add_distrib, mul_sum, mul_sum]
        refine sum_congr rfl fun l _ => ?_
        ring
    _ ≤ (1 / 2) * ((∑ j ∈ range n, T.singularValues j) * (∑ j ∈ range n, T'.singularValues j) +
        (∑ j ∈ range n, T.singularValues j) * (∑ j ∈ range n, T'.singularValues j)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
        · exact mul_le_mul (Aq T) (Aq T') (N T' _ (wt_nonneg _ _ _)) (K0 T)
        · exact mul_le_mul (Ap T) (Ap T') (N T' _ (wt_nonneg _ _ _)) (K0 T)
    _ = _ := by ring

/-- **The pure term**: `|bform S x y T T| ≤ (∑_{k∈G} s_k)² - ∑_{k∈G} s_k²` for a set `G` of
indices cut off by a threshold `θ` and `|S| ≤ |G|`. -/
theorem norm_bform_self_le (T : E →ₗ[𝕜] F) (G : Finset (Fin (finrank 𝕜 E))) {θ : ℝ}
    (hθ : 0 ≤ θ) (hG : ∀ k ∈ G, θ ≤ T.singularValues k)
    (hGc : ∀ k ∉ G, T.singularValues k ≤ θ) (hSG : #S ≤ #G) :
    ‖bform S x y T T‖ ≤ (∑ k ∈ G, T.singularValues k) ^ 2 - ∑ k ∈ G, T.singularValues k ^ 2 := by
  have Bf := sum_lam_mul_le S y hy hy1 (fvec T) (fun k l h => inner_fvec_of_ne T h)
    (norm_fvec_le T) G (fun k => T.singularValues k) hθ (fun k => T.singularValues_nonneg _)
    hG hGc hSG
  have Be := sum_lam_mul_le S x hx hx1 (ebasis T) (fun k l h => (ebasis T).orthonormal.2 h)
    (fun k => ((ebasis T).orthonormal.1 k).le) G (fun k => T.singularValues k) hθ
    (fun k => T.singularValues_nonneg _) hG hGc hSG
  have e : (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k * T.singularValues l *
      (lam (𝕜 := 𝕜) (fvec T) (fvec T) y S k l + lam (𝕜 := 𝕜) (ebasis T) (ebasis T) x S k l) =
      (1 / 2) * (∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), lam (𝕜 := 𝕜) (fvec T) (fvec T) y S k l / 2 *
        (T.singularValues k * T.singularValues l) +
        ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), lam (𝕜 := 𝕜) (ebasis T) (ebasis T) x S k l / 2 *
        (T.singularValues k * T.singularValues l)) := by
    rw [← sum_add_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring
  have := norm_bform_le S x y T T
  rw [e] at this
  linarith

end SigmaTwoOp

section SigmaTwo

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- `2 σ_n^2(T) = (∑_{k<n} s_k)² - ∑_{k<n} s_k²`, the sums over the indices `k < dim E`. -/
theorem two_mul_sigma_two (T : E →ₗ[𝕜] F) (n : ℕ) :
    2 * sigma n 2 T =
      (∑ k ∈ univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n), T.singularValues k) ^ 2 -
        ∑ k ∈ univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n), T.singularValues k ^ 2 := by
  rw [sigma, two_mul_sum_powersetCard_two,
    sum_range_eq_sum_filter _ _ (fun k hk => T.singularValues_of_finrank_le hk) n,
    sum_range_eq_sum_filter _ (fun k => T.singularValues k ^ 2)
      (fun k hk => by simp [T.singularValues_of_finrank_le hk]) n]

/-- For `w` and its own Schmidt families, `bform` is `2 σ_n^2(w)`. -/
theorem bform_ebasis_fvec (w : E →ₗ[𝕜] F) (n : ℕ) :
    bform (univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n)) (ebasis w) (fvec w) w w =
      ((2 * sigma n 2 w : ℝ) : 𝕜) := by
  have hij : ∀ i j, ⟪fvec w i, w (ebasis w j)⟫_𝕜 =
      if i = j then ((w.singularValues i : ℝ) : 𝕜) else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact inner_fvec_apply_ebasis w i
    · rw [apply_ebasis_eq, inner_smul_right, inner_fvec_of_ne w h, mul_zero]
  rw [two_mul_sigma_two, bform]
  set G := univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n)
  have e : ∀ i j, ⟪fvec w i, w (ebasis w i)⟫_𝕜 * ⟪fvec w j, w (ebasis w j)⟫_𝕜 -
      ⟪fvec w i, w (ebasis w j)⟫_𝕜 * ⟪fvec w j, w (ebasis w i)⟫_𝕜 =
      ((w.singularValues i * w.singularValues j -
        if i = j then w.singularValues i ^ 2 else 0 : ℝ) : 𝕜) := by
    intro i j
    simp only [hij, ite_true]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  have hr : ∑ i ∈ G, ∑ j ∈ G, (w.singularValues i * w.singularValues j -
      if i = j then w.singularValues i ^ 2 else 0) =
      (∑ k ∈ G, w.singularValues k) ^ 2 - ∑ k ∈ G, w.singularValues k ^ 2 := by
    simp only [sum_sub_distrib]
    rw [sq, sum_mul_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    simp only [sum_ite_eq, ite_eq_left hi]
  simp only [e]
  rw [← hr]
  simp only [RCLike.ofReal_sum]

/-- **The system (16) of page 71 for `m = 2`**:
`σ_n^2(u+v) ≤ σ_n^2(u) + σ_n^1(u) σ_n^1(v) + σ_n^2(v)`, for every `n`. -/
theorem sigma_two_add_le (u v : E →ₗ[𝕜] F) (n : ℕ) :
    sigma n 2 (u + v) ≤ sigma n 2 u + sigma n 1 u * sigma n 1 v + sigma n 2 v :=
  by rw [sigma_one, sigma_one]; exact LinearMap.sum_powersetCard_two_prod_singularValues_add_le u v n

/-- **The system (16) of page 71 for `m ≤ 2`** and every `n`. -/
theorem sigma_system_of_le_two (u v : E →ₗ[𝕜] F) (n m : ℕ) (hm : m ≤ 2) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  rcases Nat.lt_or_ge m 2 with h | h
  · exact sigma_system_of_le_one u v n m (by omega)
  · obtain rfl : m = 2 := le_antisymm hm h
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
      sigma_zero, one_mul, mul_one, show 2 - 1 = 1 from rfl]
    linarith [sigma_two_add_le u v n]

/-- The product form (15) for `n ≤ 2`:
`∏_{i<n} (1 + r s_i(u+v)) ≤ ∏_{i<n} (1 + r s_i(u)) ∏_{i<n} (1 + r s_i(v))`, `r ≥ 0`. -/
theorem prod_le_of_le_two (u v : E →ₗ[𝕜] F) {n : ℕ} (hn : n ≤ 2) {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ range n, (1 + r * (u + v).singularValues i) ≤
      (∏ i ∈ range n, (1 + r * u.singularValues i)) *
        ∏ i ∈ range n, (1 + r * v.singularValues i) :=
  prod_le_of_sigma_system u v n (fun m hm => sigma_system_of_le_two u v n m (hm.trans hn)) hr

end SigmaTwo

/-! ### Pages 123–124: Fredholm coefficients and the mixed Schwarz inequality -/

section Fredholm

open Matrix Polynomial
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `k`-th Fredholm coefficient `α_k(T)`, the coefficient of `X^k` in `det(1 + X T)`:
the `k`-th elementary symmetric function of the eigenvalues, the trace of `Λᵏ T`. -/
noncomputable def alpha (k : ℕ) (T : Matrix n n ℂ) : ℂ :=
  (det (1 + (X : ℂ[X]) • T.map C)).coeff k

theorem alpha_eq_sum_minors (k : ℕ) (T : Matrix n n ℂ) :
    alpha k T = ∑ s ∈ Finset.univ.powersetCard k,
      (T.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det :=
  coeff_det_one_add_X_smul_eq_sum_minors T k

theorem alpha_zero (T : Matrix n n ℂ) : alpha 0 T = 1 := by
  rw [alpha_eq_sum_minors, Finset.powersetCard_zero, Finset.sum_singleton]
  exact det_isEmpty

/-- `α_k` of a positive semidefinite matrix is `≥ 0`: its principal minors are. -/
theorem alpha_nonneg {T : Matrix n n ℂ} (hT : T.PosSemidef) (k : ℕ) : 0 ≤ alpha k T := by
  rw [alpha_eq_sum_minors]
  exact Finset.sum_nonneg fun s _ => (hT.submatrix _).det_nonneg

/-- `det(1 + T) = ∑_k α_k(T)`. -/
theorem det_one_add_eq_sum_alpha (T : Matrix n n ℂ) :
    det (1 + T) = ∑ k ∈ Finset.range (Fintype.card n + 1), alpha k T := by
  have hdeg : (det (1 + (X : ℂ[X]) • T.map C)).natDegree < Fintype.card n + 1 := by
    have := natDegree_det_X_add_C_le T (1 : Matrix n n ℂ)
    rw [Matrix.map_one _ (map_zero C) (map_one C), add_comm] at this
    omega
  have h := eval_eq_sum_range' hdeg 1
  simp only [one_pow, mul_one] at h
  simp only [alpha]
  rw [← h, eval, ← coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- `det(1 + R) ≥ 1` for `R ≥ 0`. -/
theorem one_le_det_one_add {R : Matrix n n ℂ} (hR : R.PosSemidef) : 1 ≤ det (1 + R) := by
  rw [det_one_add_eq_sum_alpha, ← alpha_zero R]
  exact Finset.single_le_sum (fun k _ => alpha_nonneg hR k) (Finset.mem_range.2 (by omega))

/-- Monotonicity of the determinant: `det S ≤ det (R + S)` for `R, S ≥ 0`. -/
theorem det_le_det_add {R S : Matrix n n ℂ} (hR : R.PosSemidef) (hS : S.PosSemidef) :
    det S ≤ det (R + S) := by
  by_cases h0 : det S = 0
  · rw [h0]; exact (hR.add hS).det_nonneg
  have hS0 : 0 ≤ S := hS.nonneg
  set s := CFC.sqrt S with hs
  have hss : s * s = S := CFC.sqrt_mul_sqrt_self S
  have hsH : sᴴ = s := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hdet : det s * det s = det S := by rw [← det_mul, hss]
  have hsu : IsUnit (det s) := isUnit_iff_ne_zero.2 fun h => h0 (by rw [← hdet, h, zero_mul])
  set R' := s⁻¹ * R * s⁻¹
  have hR' : R'.PosSemidef := by
    have := hR.conjTranspose_mul_mul_same s⁻¹
    rwa [conjTranspose_nonsing_inv, hsH] at this
  have hRS : R + S = s * (1 + R') * s := by
    simp only [R', mul_add, add_mul, mul_one, ← mul_assoc, mul_nonsing_inv _ hsu, one_mul,
      hss]
    rw [mul_assoc, nonsing_inv_mul _ hsu, mul_one, add_comm]
  have : det s * det (1 + R') * det s = det S * det (1 + R') := by rw [← hdet]; ring
  rw [hRS, det_mul, det_mul, this]
  exact le_mul_of_one_le_right hS.det_nonneg (one_le_det_one_add hR')

/-- For a positive semidefinite block matrix `[[P, Xᴴ], [X, Q]]`, `|det X|² ≤ det P · det Q`. -/
theorem norm_det_sq_le {m : Type*} [Fintype m] [DecidableEq m] {P Q X : Matrix m m ℂ}
    (h : (fromBlocks P Xᴴ X Q).PosSemidef) : ((‖det X‖ ^ 2 : ℝ) : ℂ) ≤ det P * det Q := by
  have hP : P.PosSemidef := by
    have := h.submatrix Sum.inl
    rwa [show (fromBlocks P Xᴴ X Q).submatrix Sum.inl Sum.inl = P by ext; rfl] at this
  have hQ : Q.PosSemidef := by
    have := h.submatrix Sum.inr
    rwa [show (fromBlocks P Xᴴ X Q).submatrix Sum.inr Sum.inr = Q by ext; rfl] at this
  have hX : ((‖det X‖ ^ 2 : ℝ) : ℂ) = det X * det Xᴴ := by
    rw [det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  by_cases hP0 : det P = 0
  · obtain ⟨v, hv, hPv⟩ := exists_mulVec_eq_zero_iff.2 hP0
    have hw : star (Sum.elim v 0) ⬝ᵥ (fromBlocks P Xᴴ X Q *ᵥ Sum.elim v 0) = 0 := by
      simp [fromBlocks_mulVec, hPv, dotProduct, Fintype.sum_sum_type]
    have hMw := (h.dotProduct_mulVec_zero_iff).1 hw
    have hXv : X *ᵥ v = 0 := by
      ext i
      have := congrFun hMw (Sum.inr i)
      simpa [fromBlocks_mulVec] using this
    have : det X = 0 := exists_mulVec_eq_zero_iff.1 ⟨v, hv, hXv⟩
    rw [hX, this, hP0]; simp
  have hPd : P.PosDef := hP.posDef_iff_det_ne_zero.2 hP0
  have : Invertible P := invertibleOfIsUnitDet P (isUnit_iff_ne_zero.2 hP0)
  have hschur : (Q - X * P⁻¹ * Xᴴ).PosSemidef := by
    have := (PosDef.fromBlocks₁₁ Xᴴ Q hPd).1 (by rwa [conjTranspose_conjTranspose])
    rwa [conjTranspose_conjTranspose] at this
  have hS : (X * P⁻¹ * Xᴴ).PosSemidef := hPd.inv.posSemidef.mul_mul_conjTranspose_same X
  have hle := det_le_det_add hschur hS
  rw [sub_add_cancel] at hle
  have hdS : det (X * P⁻¹ * Xᴴ) * det P = det X * det Xᴴ := by
    rw [det_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    field_simp
  rw [hX, ← hdS, mul_comm (det P)]
  exact mul_le_mul_of_nonneg_right hle hP.det_nonneg

/-- `|H| = [[|A|, 0], [0, |A*|]]` for `H = [[0, A*], [A, 0]]`. -/
theorem abs_block (A : Matrix n n ℂ) :
    CFC.abs (fromBlocks 0 Aᴴ A 0) = fromBlocks (CFC.abs A) 0 0 (CFC.abs Aᴴ) := by
  have hD : (fromBlocks (CFC.abs A) 0 0 (CFC.abs Aᴴ)).PosSemidef := by
    have h1 := posSemidef_iff_dotProduct_mulVec.mp (CFC.abs_nonneg A).posSemidef
    have h2 := posSemidef_iff_dotProduct_mulVec.mp (CFC.abs_nonneg Aᴴ).posSemidef
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨by simp [IsHermitian, fromBlocks_conjTranspose,
      h1.1.eq, h2.1.eq], fun x => ?_⟩
    rw [(Sum.elim_comp_inl_inr x).symm, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add]
    convert add_nonneg (h1.2 (x ∘ Sum.inl)) (h2.2 (x ∘ Sum.inr)) using 1
    simp [dotProduct, Fintype.sum_sum_type]
  rw [CFC.abs]
  refine CFC.sqrt_unique ?_ hD.nonneg
  rw [fromBlocks_multiply]
  simp only [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
    conjTranspose_zero, conjTranspose_conjTranspose, mul_zero, zero_mul, add_zero, zero_add]
  rw [CFC.abs_mul_abs, CFC.abs_mul_abs]
  simp [star_eq_conjTranspose]

/-- `[[|A|, A*], [A, |A*|]] ≥ 0`: it is `|H| + H`, `H = [[0, A*], [A, 0]]`. -/
theorem block_posSemidef (A : Matrix n n ℂ) :
    (fromBlocks (CFC.abs A) Aᴴ A (CFC.abs Aᴴ)).PosSemidef := by
  have hH : IsSelfAdjoint (fromBlocks 0 Aᴴ A 0 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
    simp [IsSelfAdjoint, star_eq_conjTranspose, fromBlocks_conjTranspose]
  have h := CFC.abs_add_self _ hH
  have h0 : 0 ≤ CFC.abs (fromBlocks 0 Aᴴ A 0 : Matrix (n ⊕ n) (n ⊕ n) ℂ) +
      fromBlocks 0 Aᴴ A 0 := by
    rw [h]; exact smul_nonneg (by norm_num) (CFC.posPart_nonneg _)
  rw [abs_block, fromBlocks_add] at h0
  simpa using h0.posSemidef

/-- **Page 123, Corollaire 2, in finite dimension.** For complex square matrices `A`, `B`,
`|α_k(A + B)|² ≤ α_k(|A| + |B|) · α_k(|A*| + |B*|)` for every `k`. -/
theorem corollaire2 (A B : Matrix n n ℂ) (k : ℕ) :
    ‖alpha k (A + B)‖ ^ 2 ≤
      (alpha k (CFC.abs A + CFC.abs B)).re * (alpha k (CFC.abs Aᴴ + CFC.abs Bᴴ)).re := by
  set P := CFC.abs A + CFC.abs B
  set Q := CFC.abs Aᴴ + CFC.abs Bᴴ
  set T := A + B
  have hM : (fromBlocks P Tᴴ T Q).PosSemidef := by
    have := (block_posSemidef A).add (block_posSemidef B)
    rwa [fromBlocks_add, ← conjTranspose_add] at this
  have hP : P.PosSemidef := (CFC.abs_nonneg A).posSemidef.add (CFC.abs_nonneg B).posSemidef
  have hQ : Q.PosSemidef := (CFC.abs_nonneg Aᴴ).posSemidef.add (CFC.abs_nonneg Bᴴ).posSemidef
  -- the principal minors
  set a : Finset n → ℝ := fun s => (P.submatrix (Subtype.val : s → n) Subtype.val).det.re
  set b : Finset n → ℝ := fun s => (Q.submatrix (Subtype.val : s → n) Subtype.val).det.re
  have hdet : ∀ s : Finset n, ‖(T.submatrix (Subtype.val : s → n) Subtype.val).det‖ ≤
      √(a s) * √(b s) := by
    intro s
    have hs := hM.submatrix (Sum.map (Subtype.val : s → n) (Subtype.val : s → n))
    rw [show (fromBlocks P Tᴴ T Q).submatrix (Sum.map Subtype.val Subtype.val)
        (Sum.map Subtype.val Subtype.val) = fromBlocks (P.submatrix (Subtype.val : s → n)
          Subtype.val) (T.submatrix (Subtype.val : s → n) Subtype.val)ᴴ
          (T.submatrix Subtype.val Subtype.val) (Q.submatrix Subtype.val Subtype.val) by
      ext (i | i) (j | j) <;> rfl] at hs
    have h := norm_det_sq_le hs
    have ha := (hP.submatrix (Subtype.val : s → n)).det_nonneg
    have hb := (hQ.submatrix (Subtype.val : s → n)).det_nonneg
    rw [← Real.sqrt_mul (Complex.nonneg_iff.1 ha).1]
    refine Real.le_sqrt_of_sq_le ?_
    have h' := (Complex.le_def.1 h).1
    rw [Complex.ofReal_re, Complex.mul_re, ← (Complex.nonneg_iff.1 ha).2,
      ← (Complex.nonneg_iff.1 hb).2] at h'
    simpa [a, b] using h'
  have ha0 : ∀ s, 0 ≤ a s := fun s =>
    (Complex.nonneg_iff.1 (hP.submatrix (Subtype.val : s → n)).det_nonneg).1
  have hb0 : ∀ s, 0 ≤ b s := fun s =>
    (Complex.nonneg_iff.1 (hQ.submatrix (Subtype.val : s → n)).det_nonneg).1
  have key : ‖alpha k T‖ ≤ √((alpha k P).re) * √((alpha k Q).re) := by
    rw [alpha_eq_sum_minors, alpha_eq_sum_minors, alpha_eq_sum_minors, Complex.re_sum,
      Complex.re_sum]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s _ => hdet s).trans
      (Real.sum_sqrt_mul_sqrt_le _ ha0 hb0))
  have hPk := (Complex.nonneg_iff.1 (alpha_nonneg hP k)).1
  have hQk := (Complex.nonneg_iff.1 (alpha_nonneg hQ k)).1
  exact (pow_le_pow_left₀ (norm_nonneg _) key 2).trans_eq
    (by rw [mul_pow, Real.sq_sqrt hPk, Real.sq_sqrt hQk])

theorem norm_alpha_le (A B : Matrix n n ℂ) (k : ℕ) :
    ‖alpha k (A + B)‖ ≤ √((alpha k (CFC.abs A + CFC.abs B)).re) *
      √((alpha k (CFC.abs Aᴴ + CFC.abs Bᴴ)).re) := by
  have hP := (Complex.nonneg_iff.1 (alpha_nonneg
    ((CFC.abs_nonneg A).posSemidef.add (CFC.abs_nonneg B).posSemidef) k)).1
  rw [← Real.sqrt_mul hP]
  exact Real.le_sqrt_of_sq_le (corollaire2 A B k)

/-- **Page 124, Corollaire 3, in finite dimension**, and the geometric-mean form:
`|det(1 + A + B)| ≤ ½ [det(1 + |A| + |B|) + det(1 + |A*| + |B*|)]` and
`|det(1 + A + B)|² ≤ det(1 + |A| + |B|) · det(1 + |A*| + |B*|)`. -/
theorem corollaire3 (A B : Matrix n n ℂ) :
    ‖det (1 + (A + B))‖ ≤
        ((det (1 + (CFC.abs A + CFC.abs B))).re + (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re) / 2 ∧
      ‖det (1 + (A + B))‖ ^ 2 ≤
        (det (1 + (CFC.abs A + CFC.abs B))).re * (det (1 + (CFC.abs Aᴴ + CFC.abs Bᴴ))).re := by
  set P := CFC.abs A + CFC.abs B
  set Q := CFC.abs Aᴴ + CFC.abs Bᴴ
  have hP : P.PosSemidef := (CFC.abs_nonneg A).posSemidef.add (CFC.abs_nonneg B).posSemidef
  have hQ : Q.PosSemidef := (CFC.abs_nonneg Aᴴ).posSemidef.add (CFC.abs_nonneg Bᴴ).posSemidef
  have ha : ∀ k, 0 ≤ (alpha k P).re := fun k => (Complex.nonneg_iff.1 (alpha_nonneg hP k)).1
  have hb : ∀ k, 0 ≤ (alpha k Q).re := fun k => (Complex.nonneg_iff.1 (alpha_nonneg hQ k)).1
  have h1 : ‖det (1 + (A + B))‖ ≤ ∑ k ∈ Finset.range (Fintype.card n + 1),
      √((alpha k P).re) * √((alpha k Q).re) := by
    rw [det_one_add_eq_sum_alpha]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_alpha_le A B k)
  rw [det_one_add_eq_sum_alpha P, det_one_add_eq_sum_alpha Q, Complex.re_sum, Complex.re_sum]
  refine ⟨h1.trans ?_, ?_⟩
  · rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun k _ => ?_
    nlinarith [Real.sq_sqrt (ha k), Real.sq_sqrt (hb k), sq_nonneg (√((alpha k P).re) -
      √((alpha k Q).re))]
  · refine (pow_le_pow_left₀ (norm_nonneg _) (h1.trans
      (Real.sum_sqrt_mul_sqrt_le _ ha hb)) 2).trans_eq ?_
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun k _ => ha k),
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => hb k)]

end Fredholm

/-! ### Pages 126–139: `S_p` through the Fredholm determinant, for `0 < p < 1` -/

section Schatten

open MeasureTheory Set Real

/-- `v ↦ log(1 + c v) v^{−1−p}`, the integrand of the representation of page 128. -/
noncomputable def kernel (p c v : ℝ) : ℝ := Real.log (1 + c * v) * v ^ (-1 - p)

theorem kernel_nonneg {p c v : ℝ} (hc : 0 ≤ c) (hv : 0 < v) : 0 ≤ kernel p c v :=
  mul_nonneg (Real.log_nonneg (by nlinarith)) (rpow_nonneg hv.le _)

theorem integrableOn_kernel {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc : 0 ≤ c) :
    IntegrableOn (kernel p c) (Set.Ioi 0) := by
  have hcont : ContinuousOn (kernel p c) (Set.Ioi 0) := by
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.log (by fun_prop) fun v hv => ?_
      have : (0 : ℝ) < v := hv
      nlinarith
    · exact ContinuousOn.rpow_const continuousOn_id fun v hv => Or.inl (ne_of_gt hv)
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- near `0`: `log(1 + c v) ≤ c v`, so the integrand is `≤ c v^{−p}`
    have h0 : IntegrableOn (fun v : ℝ => v ^ (-p)) (Set.Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    have hg : IntegrableOn (fun v : ℝ => c * v ^ (-p)) (Set.Ioc 0 1) := h0.const_mul c
    refine hg.mono' ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 < v := hv.1
    rw [Real.norm_of_nonneg (kernel_nonneg hc hv0), kernel]
    have hl : Real.log (1 + c * v) ≤ c * v := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + c * v by nlinarith); linarith
    calc Real.log (1 + c * v) * v ^ (-1 - p) ≤ c * v * v ^ (-1 - p) :=
          mul_le_mul_of_nonneg_right hl (rpow_nonneg hv0.le _)
      _ = c * v ^ (-p) := by
          rw [mul_assoc, ← rpow_one_add' hv0.le (by linarith)]
          ring_nf
  · -- near `∞`: `log(1 + c v) ≤ ((1 + c) v)^{p/2} / (p/2)`
    have hε : 0 < p / 2 := by linarith
    have hg : IntegrableOn (fun v : ℝ => ((1 + c) ^ (p / 2) / (p / 2)) * v ^ (p / 2 - 1 - p))
        (Set.Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one) _
    have hcont' : ContinuousOn (kernel p c) (Set.Ioi 1) :=
      hcont.mono fun v (hv : 1 < v) => (show (0 : ℝ) < v by linarith)
    refine hg.mono' (hcont'.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    have hv1 : (1 : ℝ) < v := hv
    have hv0 : 0 < v := by linarith
    rw [Real.norm_of_nonneg (kernel_nonneg hc hv0), kernel]
    have h1 : 1 + c * v ≤ (1 + c) * v := by nlinarith
    have hl : Real.log (1 + c * v) ≤ ((1 + c) * v) ^ (p / 2) / (p / 2) :=
      (Real.log_le_rpow_div (by nlinarith) hε).trans
        (div_le_div_of_nonneg_right (rpow_le_rpow (by nlinarith) h1 hε.le) hε.le)
    calc Real.log (1 + c * v) * v ^ (-1 - p)
        ≤ ((1 + c) * v) ^ (p / 2) / (p / 2) * v ^ (-1 - p) :=
          mul_le_mul_of_nonneg_right hl (rpow_nonneg hv0.le _)
      _ = ((1 + c) ^ (p / 2) / (p / 2)) * v ^ (p / 2 - 1 - p) := by
          rw [mul_rpow (by linarith) hv0.le, show p / 2 - 1 - p = p / 2 + (-1 - p) by ring,
            rpow_add hv0]
          ring

/-- `K_p = ∫₀^∞ log(1 + t) t^{−1−p} dt`, which is `π / (p sin πp)`; only its
positivity is used. -/
noncomputable def K (p : ℝ) : ℝ := ∫ t in Set.Ioi 0, kernel p 1 t

theorem K_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < K p := by
  rw [K, setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_kernel hp0 hp1 zero_le_one)]
  · have : Function.support (kernel p 1) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      refine Set.inter_eq_right.mpr fun v (hv : 0 < v) => ?_
      refine Function.mem_support.mpr (ne_of_gt (mul_pos (Real.log_pos (by linarith))
        (rpow_pos_of_pos hv _)))
    rw [this, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun v hv => kernel_nonneg zero_le_one hv)

/-- **The representation of page 128**: `s^p · K_p = ∫₀^∞ log(1 + v s) v^{−1−p} dv`
for `s ≥ 0`, `0 < p < 1`. -/
theorem integral_kernel {p s : ℝ} (hp0 : 0 < p) (hs : 0 ≤ s) :
    ∫ v in Set.Ioi 0, kernel p s v = s ^ p * K p := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [kernel, zero_rpow hp0.ne']
  have h : ∀ v ∈ Set.Ioi (0 : ℝ), kernel p s v = s ^ (1 + p) * kernel p 1 (v * s) := by
    intro v (hv : 0 < v)
    simp only [kernel, one_mul]
    rw [mul_rpow hv.le hs.le, mul_comm v s]
    have : s ^ (1 + p) * s ^ (-1 - p) = 1 := by
      rw [← rpow_add hs, show 1 + p + (-1 - p) = 0 by ring, rpow_zero]
    calc Real.log (1 + s * v) * v ^ (-1 - p)
        = Real.log (1 + s * v) * (v ^ (-1 - p) * (s ^ (1 + p) * s ^ (-1 - p))) := by
          rw [this, mul_one]
      _ = s ^ (1 + p) * (Real.log (1 + s * v) * (v ^ (-1 - p) * s ^ (-1 - p))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_const_mul,
    integral_comp_mul_right_Ioi (kernel p 1) 0 hs, zero_mul, smul_eq_mul, K, ← mul_assoc]
  congr 1
  rw [← rpow_neg_one, ← rpow_add hs]
  ring_nf

/-- `Σᵢ sᵢ^p · K_p = ∫₀^∞ log ∏ᵢ (1 + v sᵢ) · v^{−1−p} dv`. -/
theorem sum_rpow_mul_K {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (n : ℕ) :
    (∑ i ∈ range n, a i ^ p) * K p =
      ∫ v in Set.Ioi 0, Real.log (∏ i ∈ range n, (1 + v * a i)) * v ^ (-1 - p) := by
  have h : ∀ v ∈ Set.Ioi (0 : ℝ), Real.log (∏ i ∈ range n, (1 + v * a i)) * v ^ (-1 - p) =
      ∑ i ∈ range n, kernel p (a i) v := by
    intro v (hv : 0 < v)
    rw [Real.log_prod fun i _ => by nlinarith [ha i], sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [kernel, mul_comm (a i) v]
  rw [setIntegral_congr_fun measurableSet_Ioi h,
    integral_finsetSum _ fun i _ => integrableOn_kernel hp0 hp1 (ha i), sum_mul]
  exact sum_congr rfl fun i _ => (integral_kernel hp0 (ha i)).symm

/-- **Subadditivity from the determinant inequality** (page 129): for `0 < p < 1`,
if `∏ (1 + r aᵢ) ≤ ∏ (1 + r bᵢ) ∏ (1 + r cᵢ)` for every `r ≥ 0`, then
`Σ aᵢ^p ≤ Σ bᵢ^p + Σ cᵢ^p`. -/
theorem sum_rpow_le_of_prod_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a b c : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (n : ℕ)
    (h : ∀ r : ℝ, 0 ≤ r → ∏ i ∈ range n, (1 + r * a i) ≤
      (∏ i ∈ range n, (1 + r * b i)) * ∏ i ∈ range n, (1 + r * c i)) :
    ∑ i ∈ range n, a i ^ p ≤ ∑ i ∈ range n, b i ^ p + ∑ i ∈ range n, c i ^ p := by
  have hint : ∀ d : ℕ → ℝ, (∀ i, 0 ≤ d i) → IntegrableOn
      (fun v => Real.log (∏ i ∈ range n, (1 + v * d i)) * v ^ (-1 - p)) (Set.Ioi 0) := by
    intro d hd
    refine (integrable_finsetSum (range n) fun i _ => integrableOn_kernel hp0 hp1 (hd i)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    dsimp only
    rw [Real.log_prod fun i _ => by nlinarith [hd i], sum_mul]
    exact sum_congr rfl fun i _ => by rw [kernel, mul_comm (d i) v]
  refine le_of_mul_le_mul_right ?_ (K_pos hp0 hp1)
  rw [add_mul, sum_rpow_mul_K hp0 hp1 a ha, sum_rpow_mul_K hp0 hp1 b hb,
    sum_rpow_mul_K hp0 hp1 c hc, ← integral_add (hint b hb) (hint c hc)]
  refine setIntegral_mono_on (hint a ha) ((hint b hb).add (hint c hc)) measurableSet_Ioi
    fun v (hv : 0 < v) => ?_
  have hpos : ∀ d : ℕ → ℝ, (∀ i, 0 ≤ d i) → 0 < ∏ i ∈ range n, (1 + v * d i) :=
    fun d hd => prod_pos fun i _ => by nlinarith [hd i]
  rw [← add_mul, ← Real.log_mul (hpos b hb).ne' (hpos c hc).ne']
  exact mul_le_mul_of_nonneg_right (Real.log_le_log (hpos a ha) (h v hv.le))
    (rpow_nonneg hv.le _)

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Page 129 for operators: (15) for every `r ≥ 0` gives
`Σ_{i<n} sᵢ(u + v)^p ≤ Σ_{i<n} sᵢ(u)^p + Σ_{i<n} sᵢ(v)^p`, `0 < p < 1`. -/
theorem sum_singularValues_rpow_add_le_of_prod (u v : E →ₗ[𝕜] F) (n : ℕ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (h15 : ∀ r : ℝ, 0 ≤ r → ∏ i ∈ range n, (1 + r * (u + v).singularValues i) ≤
      (∏ i ∈ range n, (1 + r * u.singularValues i)) *
        ∏ i ∈ range n, (1 + r * v.singularValues i)) :
    ∑ i ∈ range n, (u + v).singularValues i ^ p ≤
      ∑ i ∈ range n, u.singularValues i ^ p + ∑ i ∈ range n, v.singularValues i ^ p :=
  sum_rpow_le_of_prod_le hp0 hp1 _ _ _ (fun i => (u + v).singularValues_nonneg i)
    (fun i => u.singularValues_nonneg i) (fun i => v.singularValues_nonneg i) n h15

/-- Unconditionally for the first two singular values, by (15) for `n ≤ 2`. -/
theorem sum_singularValues_rpow_add_le_of_le_two (u v : E →ₗ[𝕜] F) {n : ℕ} (hn : n ≤ 2)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ i ∈ range n, (u + v).singularValues i ^ p ≤
      ∑ i ∈ range n, u.singularValues i ^ p + ∑ i ∈ range n, v.singularValues i ^ p :=
  sum_singularValues_rpow_add_le_of_prod u v n hp0 hp1 fun _ hr => prod_le_of_le_two u v hn hr

end Schatten

end Grothendieck.Folder1

/-!
## Pages 71–73: the system (16) for every `m` (finding `1-sigma-nm-system`)

For linear maps `u, v : E → F` between finite-dimensional complex inner product spaces and all
`n, m`, `sigma_system` proves `σ_n^m(u+v) ≤ ∑_{p ≤ m} σ_n^p(u) σ_n^{m-p}(v)`; this removes the
restriction `m ≤ 2` of `sigma_system_of_le_two`. Hence the product form (15) for every `n`
(`prod_one_add_singularValues_add_le`) and the subadditivity of `∑_{i<n} s_i^p`, `0 < p < 1`
(`sum_singularValues_rpow_add_le`, page 129), unconditionally.

The proof keeps the page's idea (`Λ^m` of a sum, a Cauchy–Schwarz bound on the mixed terms,
Prop. 3) but writes `Λ^m` as principal `m × m` minors, `α_m(M) = ∑_{|K| = m} det M_K`:

* with `x_j, y_j` (`j < n`) the Schmidt vectors of `T = u + v`, `σ_n^m(T) = α_m(⟪y_i, T x_j⟫)`
  (`sigma_le_alpha_compr`);
* each compression factors as `⟪y_i, w x_j⟫ = ((√S Φ)* (√S Ψ))_{ij}` through the Schmidt
  expansion of `w` (`compr_eq`), so the compression of `T` is `G* H` with `H = [√S_u Ψ_u; √S_v Ψ_v]`
  and `G` likewise (`sigma_system`);
* `α_m(G* H) = α_m(H G*)` (`alpha_mul_comm`), and each minor obeys
  `|det (H G*)_K|² ≤ det (H H*)_K · det (G G*)_K` (`norm_det_mul_sq_le`) and Fischer's inequality
  `det (H H*)_K ≤ det (P_H)_K` with `P_H` the block-diagonal part (`det_le_det_blockMask`);
  `α_m(P_H) = ∑_p α_p(·) α_{m-p}(·)` (`alpha_fromBlocks_zero`);
* the interlacing bound `α_p(Ψ* S Ψ) ≤ σ_n^p(w)` (`alpha_conj_diagonal_le`), from the min-max
  count `λ_i(Ψ* S Ψ) ≤ s_i(w)` (`eigenvalues₀_le_of_conj_diagonal`), replaces Prop. 3.

Not formalised: real scalars (the matrix lemmas are over `ℂ`; the cases `m ≤ 2` above hold over
`ℝ` too), Prop. 3 as a supremum, and compact operators on Hilbert spaces.
-/

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace Matrix Polynomial
open scoped MatrixOrder ComplexOrder ComplexConjugate

section SigmaSystemMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `α_k(A B) = α_k(B A)` for rectangular `A`, `B` (Sylvester's determinant identity). -/
theorem alpha_mul_comm {o : Type*} [Fintype o] [DecidableEq o] (A : Matrix n o ℂ)
    (B : Matrix o n ℂ) (k : ℕ) : alpha k (A * B) = alpha k (B * A) := by
  simp only [alpha, Matrix.map_mul]
  rw [← Matrix.smul_mul, det_one_add_mul_comm, Matrix.mul_smul]

/-- `α_k` of a block-diagonal matrix: `α_k(P ⊕ Q) = ∑_{p ≤ k} α_p(P) α_{k-p}(Q)`. -/
theorem alpha_fromBlocks_zero {o : Type*} [Fintype o] [DecidableEq o] (P : Matrix n n ℂ)
    (Q : Matrix o o ℂ) (k : ℕ) :
    alpha k (fromBlocks P 0 0 Q) = ∑ p ∈ range (k + 1), alpha p P * alpha (k - p) Q := by
  have h : (1 : Matrix (n ⊕ o) (n ⊕ o) ℂ[X]) + (X : ℂ[X]) • (fromBlocks P 0 0 Q).map C =
      fromBlocks (1 + (X : ℂ[X]) • P.map C) 0 0 (1 + (X : ℂ[X]) • Q.map C) := by
    rw [fromBlocks_map, fromBlocks_smul, ← fromBlocks_one, fromBlocks_add]
    simp
  simp only [alpha, h, det_fromBlocks_zero₂₁, coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (det (1 + (X : ℂ[X]) • P.map C)).coeff i *
      (det (1 + (X : ℂ[X]) • Q.map C)).coeff j) k

/-- **Fischer's inequality** for a positive semidefinite block matrix:
`det [[A, B], [B*, D]] ≤ det A · det D`. -/
theorem det_fromBlocks_le {o : Type*} [Fintype o] [DecidableEq o] {A : Matrix n n ℂ}
    {B : Matrix n o ℂ} {D : Matrix o o ℂ} (h : (fromBlocks A B Bᴴ D).PosSemidef) :
    det (fromBlocks A B Bᴴ D) ≤ det A * det D := by
  have hA : A.PosSemidef := h.submatrix Sum.inl
  have hD : D.PosSemidef := h.submatrix Sum.inr
  by_cases hA0 : det A = 0
  · obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_zero_iff.2 hA0
    have hw : star (Sum.elim v 0) ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim v 0) = 0 := by
      simp [fromBlocks_mulVec, hAv, dotProduct, Fintype.sum_sum_type]
    have hMw := (h.dotProduct_mulVec_zero_iff).1 hw
    have : det (fromBlocks A B Bᴴ D) = 0 :=
      exists_mulVec_eq_zero_iff.1 ⟨Sum.elim v 0, fun h0 => hv (by
        ext i; simpa using congrFun h0 (Sum.inl i)), hMw⟩
    rw [this, hA0, zero_mul]
  have hAd : A.PosDef := hA.posDef_iff_det_ne_zero.2 hA0
  have : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hA0)
  have hle := det_le_det_add (hAd.inv.posSemidef.conjTranspose_mul_mul_same B)
    ((PosDef.fromBlocks₁₁ B D hAd).1 h)
  rw [add_sub_cancel] at hle
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  exact mul_le_mul_of_nonneg_left hle hA.det_nonneg

/-- The block-diagonal part of a matrix along a predicate `c` on the indices. -/
def blockMask (c : n → Prop) [DecidablePred c] (M : Matrix n n ℂ) : Matrix n n ℂ :=
  of fun i j => if (c i ↔ c j) then M i j else 0

/-- **Fischer's inequality**, in mask form: `det M ≤ det (blockMask c M)` for `M ≥ 0`. -/
theorem det_le_det_blockMask (c : n → Prop) [DecidablePred c] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : det M ≤ det (blockMask c M) := by
  set e : n ≃ {i // c i} ⊕ {i // ¬ c i} := (Equiv.sumCompl c).symm
  have h1 : reindex e e M = fromBlocks (toBlocks₁₁ (reindex e e M)) (toBlocks₁₂ (reindex e e M))
      (toBlocks₁₂ (reindex e e M))ᴴ (toBlocks₂₂ (reindex e e M)) := by
    conv_lhs => rw [← fromBlocks_toBlocks (reindex e e M)]
    congr 1
    ext i j
    simpa [toBlocks₂₁, toBlocks₁₂, e] using (congrFun (congrFun hM.1 i.1) j.1).symm
  have h2 : reindex e e (blockMask c M) =
      fromBlocks (toBlocks₁₁ (reindex e e M)) 0 0 (toBlocks₂₂ (reindex e e M)) := by
    ext (i | i) (j | j) <;> simp [blockMask, e, i.2, j.2, toBlocks₁₁, toBlocks₂₂]
  have hP : (reindex e e M).PosSemidef := hM.submatrix e.symm
  rw [h1] at hP
  rw [← det_reindex_self e M, ← det_reindex_self e (blockMask c M), h2, det_fromBlocks_zero₂₁,
    h1]
  exact det_fromBlocks_le hP

/-- The determinant form of the Cauchy–Schwarz inequality:
`|det (X Y)|² ≤ det (X X*) · det (Y* Y)`. -/
theorem norm_det_mul_sq_le {o : Type*} [Fintype o] (X : Matrix n o ℂ) (Y : Matrix o n ℂ) :
    ‖det (X * Y)‖ ^ 2 ≤ (det (X * Xᴴ)).re * (det (Yᴴ * Y)).re := by
  have hW := posSemidef_self_mul_conjTranspose (fromRows X Yᴴ)
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols,
    conjTranspose_conjTranspose] at hW
  have hW' : (fromBlocks (X * Xᴴ) (Yᴴ * Xᴴ)ᴴ (Yᴴ * Xᴴ) (Yᴴ * Y)).PosSemidef := by
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]
  have h := norm_det_sq_le hW'
  have ha := (posSemidef_self_mul_conjTranspose X).det_nonneg
  have hb := (posSemidef_conjTranspose_mul_self Y).det_nonneg
  have h' := (Complex.le_def.1 h).1
  rw [Complex.ofReal_re, Complex.mul_re, ← (Complex.nonneg_iff.1 ha).2,
    ← (Complex.nonneg_iff.1 hb).2, ← conjTranspose_mul, det_conjTranspose, norm_star] at h'
  simpa using h'

end SigmaSystemMatrix

section Interlacing

variable {d : ℕ}

/-- The quadratic form of `Ψ* D Ψ`, `D = diag(s)`: `⟪z, Ψ* D Ψ z⟫ = ∑_k s_k |(Ψ z)_k|²`. -/
theorem inner_toEuclideanLin_conj_diagonal (s : ℕ → ℝ) (Ψ : Matrix (Fin d) (Fin d) ℂ)
    (z : EuclideanSpace ℂ (Fin d)) :
    ⟪z, toEuclideanLin (Ψᴴ * diagonal (fun k : Fin d => ((s k : ℝ) : ℂ)) * Ψ) z⟫_ℂ =
      ∑ k : Fin d, ((s k * ‖(Ψ *ᵥ z) k‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
  ring


/-- **Cauchy interlacing, in the form needed for (16).** Let `s` be antitone and `≥ 0`, and `Ψ` a
matrix with `‖Ψ z‖² ≤ ∑_{j < N} |z_j|²`. Then the `i`-th largest eigenvalue of `Ψ* diag(s) Ψ` is
at most `s_i` if `i < N`, and is `0` otherwise. The proof is the min-max dimension count: a
nonzero `z` orthogonal to the eigenvectors after `i` and killed by the first `i` coordinates of
`Ψ` exists. -/
theorem eigenvalues₀_le_of_conj_diagonal (s : ℕ → ℝ) (hs : Antitone s) (hs0 : ∀ k, 0 ≤ s k)
    (N : ℕ) (Ψ : Matrix (Fin d) (Fin d) ℂ)
    (hΨ : ∀ z : Fin d → ℂ, ∑ k, ‖(Ψ *ᵥ z) k‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) < N), ‖z j‖ ^ 2)
    (hA : (Ψᴴ * diagonal (fun k : Fin d => ((s k : ℝ) : ℂ)) * Ψ).IsHermitian)
    (i : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues₀ i ≤ if (i : ℕ) < N then s i else 0 := by
  set A := Ψᴴ * diagonal (fun k : Fin d => ((s k : ℝ) : ℂ)) * Ψ with hAdef
  set T := toEuclideanLin A
  have hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have hn : finrank ℂ (EuclideanSpace ℂ (Fin d)) = Fintype.card (Fin d) := finrank_euclideanSpace
  set b := hT.eigenvectorBasis hn
  set lam := hT.eigenvalues hn
  have hlam : hA.eigenvalues₀ = lam := rfl
  have hanti : Antitone lam := hT.eigenvalues_antitone hn
  have hform : ∀ z, ⟪z, T z⟫_ℂ = ∑ l, ((lam l * ‖⟪b l, z⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [← b.sum_inner_mul_inner z (T z)]
    refine sum_congr rfl fun l _ => ?_
    rw [← hT, hT.apply_eigenvectorBasis, inner_smul_left, ← inner_conj_symm z (b l)]
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [RCLike.conj_ofReal, lam, b]
    rw [show ∀ a b c : ℂ, a * (b * c) = b * (c * a) from fun a b c => by ring]
    rfl
  -- the linear conditions
  let ι' := {l : Fin (Fintype.card (Fin d)) // i < l} ⊕ {k : Fin d // (k : ℕ) < i}
  let e := (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap
  let φ : ι' → EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ := Sum.elim (fun l => innerₛₗ ℂ (b l.1))
    (fun k => if (i : ℕ) < N then LinearMap.proj k.1 ∘ₗ Ψ.mulVecLin ∘ₗ e
      else LinearMap.proj k.1 ∘ₗ e)
  have hcard : Fintype.card ι' < Fintype.card (Fin d) := by
    have h1 : Fintype.card {l : Fin (Fintype.card (Fin d)) // i < l} ≤
        Fintype.card (Fin d) - 1 - i := by
      refine (Fintype.card_le_of_injective (fun l => (⟨l.1 - i - 1, by omega⟩ :
        Fin (Fintype.card (Fin d) - 1 - i))) fun a b h => ?_).trans (by simp)
      have h' : (a.1 : ℕ) - i - 1 = b.1 - i - 1 := by simpa using congrArg Fin.val h
      have ha : (i : ℕ) < a.1 := a.2
      have hb : (i : ℕ) < b.1 := b.2
      exact Subtype.ext (Fin.ext (by omega))
    have h2 : Fintype.card {k : Fin d // (k : ℕ) < i} ≤ i := by
      refine (Fintype.card_le_of_injective (fun k => (⟨k.1, k.2⟩ : Fin i)) fun a b h => ?_).trans
        (by simp)
      exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h))
    have := i.2
    simp only [ι', Fintype.card_sum]
    omega
  have hker : LinearMap.ker (LinearMap.pi φ) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_fintype_fun_eq_card, hn]; exact hcard)
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hz : ∀ x, φ x z = 0 := fun x => by
    have := congrFun (LinearMap.mem_ker.1 hzker) x
    simpa using this
  have hz1 : ∀ l, i < l → ⟪b l, z⟫_ℂ = 0 := fun l hl => by
    simpa [φ] using hz (Sum.inl ⟨l, hl⟩)
  have hz2 : ∀ k : Fin d, (k : ℕ) < i →
      (if (i : ℕ) < N then (Ψ *ᵥ z) k else z k) = 0 := fun k hk => by
    have := hz (Sum.inr ⟨k, hk⟩)
    split_ifs at this ⊢ <;> simpa [φ, e, *] using this
  -- the two bounds on `⟪z, T z⟫`
  have hznorm : ‖z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := EuclideanSpace.norm_sq_eq z
  have hlow : lam i * ‖z‖ ^ 2 ≤ (⟪z, T z⟫_ℂ).re := by
    rw [hform, Complex.re_sum, ← b.sum_sq_norm_inner_right z, mul_sum]
    refine sum_le_sum fun l _ => ?_
    simp only [Complex.ofReal_re]
    rcases le_or_gt l i with h | h
    · exact mul_le_mul_of_nonneg_right (hanti h) (by positivity)
    · rw [hz1 l h]; simp
  have hup : (⟪z, T z⟫_ℂ).re ≤ (if (i : ℕ) < N then s i else 0) * ‖z‖ ^ 2 := by
    rw [inner_toEuclideanLin_conj_diagonal, Complex.re_sum]
    simp only [Complex.ofReal_re]
    have hb := hΨ z
    split_ifs with hiN
    · calc ∑ k : Fin d, s k * ‖(Ψ *ᵥ z) k‖ ^ 2 ≤ ∑ k : Fin d, s i * ‖(Ψ *ᵥ z) k‖ ^ 2 := by
            refine sum_le_sum fun k _ => ?_
            rcases lt_or_ge (k : ℕ) i with h | h
            · have := hz2 k h; simp only [hiN, ↓reduceIte] at this; rw [this]; simp
            · exact mul_le_mul_of_nonneg_right (hs h) (by positivity)
        _ = s i * ∑ k : Fin d, ‖(Ψ *ᵥ z) k‖ ^ 2 := by rw [mul_sum]
        _ ≤ s i * ‖z‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_left (hb.trans ?_) (hs0 _)
            rw [hznorm]
            exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    · have h0 : ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) < N), ‖z j‖ ^ 2 = 0 :=
        sum_eq_zero fun j hj => by
          have hj' : (j : ℕ) < i := by simp at hj; omega
          have := hz2 j hj'; simp only [hiN, ↓reduceIte] at this; rw [this]; simp
      rw [h0] at hb
      have hw : ∀ k, ‖(Ψ *ᵥ z) k‖ ^ 2 = 0 := fun k =>
        le_antisymm ((single_le_sum (fun k _ => by positivity) (mem_univ k)).trans hb)
          (by positivity)
      simp [hw]
  rw [hlam]
  exact le_of_mul_le_mul_right (hlow.trans hup) (by positivity)

/-- Reindexing a sum of products over the `p`-subsets along an equivalence. -/
theorem sum_powersetCard_prod_equiv {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring R] (σ : α ≃ β) (f : β → R) (p : ℕ) :
    ∑ K ∈ (univ : Finset α).powersetCard p, ∏ i ∈ K, f (σ i) =
      ∑ K ∈ (univ : Finset β).powersetCard p, ∏ j ∈ K, f j := by
  rw [← map_univ_equiv σ, powersetCard_map, sum_map]
  refine sum_congr rfl fun K _ => ?_
  simp [prod_map]

/-- Sums of products over the `p`-subsets of `Fin c` are sums over the `p`-subsets of
`range c`. -/
theorem sum_powersetCard_fin (c p : ℕ) {R : Type*} [CommSemiring R] (g : ℕ → R) :
    ∑ K ∈ (univ : Finset (Fin c)).powersetCard p, ∏ j ∈ K, g j =
      ∑ t ∈ (range c).powersetCard p, ∏ i ∈ t, g i := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, powersetCard_map, sum_map]
  refine sum_congr rfl fun K _ => ?_
  simp [prod_map]


/-- Comparing sums of products over `p`-subsets: if `f` vanishes on `A \ B` and agrees with
`g ≥ 0` on `A ∩ B`, then `∑_{t ⊆ A} ∏_t f ≤ ∑_{t ⊆ B} ∏_t g`. -/
theorem sum_powersetCard_prod_le {A B : Finset ℕ} {f g : ℕ → ℝ} (p : ℕ)
    (hg : ∀ i ∈ B, 0 ≤ g i) (hf : ∀ i ∈ A, i ∉ B → f i = 0)
    (hfg : ∀ i ∈ A, i ∈ B → f i = g i) :
    ∑ t ∈ A.powersetCard p, ∏ i ∈ t, f i ≤ ∑ t ∈ B.powersetCard p, ∏ i ∈ t, g i := by
  calc ∑ t ∈ A.powersetCard p, ∏ i ∈ t, f i
      = ∑ t ∈ (A.powersetCard p).filter (· ⊆ B), ∏ i ∈ t, f i := by
        rw [sum_filter_of_ne]
        intro t ht hne
        by_contra hsub
        obtain ⟨i, hit, hiB⟩ := not_subset.1 hsub
        exact hne (prod_eq_zero hit (hf i ((mem_powersetCard.1 ht).1 hit) hiB))
    _ = ∑ t ∈ (A.powersetCard p).filter (· ⊆ B), ∏ i ∈ t, g i := by
        refine sum_congr rfl fun t ht => prod_congr rfl fun i hi => ?_
        rw [mem_filter, mem_powersetCard] at ht
        exact hfg i (ht.1.1 hi) (ht.2 hi)
    _ ≤ ∑ t ∈ B.powersetCard p, ∏ i ∈ t, g i := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun t ht _ =>
          prod_nonneg fun i hi => hg i ((mem_powersetCard.1 ht).1 hi)
        intro t ht
        rw [mem_filter, mem_powersetCard] at ht
        exact mem_powersetCard.2 ⟨ht.2, ht.1.2⟩

/-- `α_p` of a diagonal matrix is the `p`-th elementary symmetric function of its entries. -/
theorem alpha_diagonal {n : Type*} [Fintype n] [DecidableEq n] (μ : n → ℂ) (p : ℕ) :
    alpha p (diagonal μ) = ∑ K ∈ (univ : Finset n).powersetCard p, ∏ i ∈ K, μ i := by
  rw [alpha_eq_sum_minors]
  refine sum_congr rfl fun K _ => ?_
  rw [submatrix_diagonal _ _ Subtype.val_injective, det_diagonal]
  exact prod_coe_sort K μ

/-- `α_p` of a Hermitian matrix is the `p`-th elementary symmetric function of its eigenvalues. -/
theorem alpha_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (p : ℕ) :
    alpha p A = ∑ K ∈ (univ : Finset n).powersetCard p, ∏ i ∈ K, ((hA.eigenvalues i : ℝ) : ℂ) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc, alpha_mul_comm,
    mul_assoc, Unitary.coe_star_mul_self, mul_one, alpha_diagonal]
  rfl

/-- **The interlacing bound.** For `s` antitone and `≥ 0` and `Ψ` with
`‖Ψ z‖² ≤ ∑_{j < N} |z_j|²`, `α_p(Ψ* diag(s) Ψ) ≤ e_p(s_0, …, s_{N-1})`. -/
theorem alpha_conj_diagonal_le (s : ℕ → ℝ) (hs : Antitone s) (hs0 : ∀ k, 0 ≤ s k)
    (N : ℕ) (Ψ : Matrix (Fin d) (Fin d) ℂ)
    (hΨ : ∀ z : Fin d → ℂ, ∑ k, ‖(Ψ *ᵥ z) k‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) < N), ‖z j‖ ^ 2) (p : ℕ) :
    (alpha p (Ψᴴ * diagonal (fun k : Fin d => ((s k : ℝ) : ℂ)) * Ψ)).re ≤
      ∑ t ∈ (range N).powersetCard p, ∏ i ∈ t, s i := by
  set A := Ψᴴ * diagonal (fun k : Fin d => ((s k : ℝ) : ℂ)) * Ψ
  have hPSD : A.PosSemidef :=
    PosSemidef.conjTranspose_mul_mul_same (posSemidef_diagonal_iff.2 fun k => by
      exact_mod_cast hs0 k) Ψ
  have hA := hPSD.1
  set g : ℕ → ℝ := fun k => if k < N then s k else 0
  set σ := (Fintype.equivOfCardEq (Fintype.card_fin _) :
    Fin (Fintype.card (Fin d)) ≃ Fin d).symm
  have hev : ∀ i, hA.eigenvalues i = hA.eigenvalues₀ (σ i) := fun i => rfl
  have hle : ∀ i, hA.eigenvalues i ≤ g (σ i) := fun i => by
    rw [hev]; exact eigenvalues₀_le_of_conj_diagonal s hs hs0 N Ψ hΨ hA (σ i)
  rw [alpha_eq_sum_eigenvalues hA, Complex.re_sum]
  simp only [← Complex.ofReal_prod, Complex.ofReal_re]
  calc ∑ K ∈ (univ : Finset (Fin d)).powersetCard p, ∏ i ∈ K, hA.eigenvalues i
      ≤ ∑ K ∈ (univ : Finset (Fin d)).powersetCard p, ∏ i ∈ K, g (σ i) :=
        sum_le_sum fun K _ => prod_le_prod₀ (fun i _ => hPSD.eigenvalues_nonneg i)
          fun i _ => hle i
    _ = ∑ t ∈ (range (Fintype.card (Fin d))).powersetCard p, ∏ i ∈ t, g i := by
        rw [sum_powersetCard_prod_equiv σ (fun j => g j), sum_powersetCard_fin]
    _ ≤ ∑ t ∈ (range N).powersetCard p, ∏ i ∈ t, s i :=
        sum_powersetCard_prod_le p (fun i _ => hs0 i)
          (fun i _ hi => by simp [g, mem_range.not.1 hi])
          (fun i _ hi => by simp [g, mem_range.1 hi])

end Interlacing

section Assembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The block-diagonal part of `[A; B] [A; B]*` is `A A* ⊕ B B*`. -/
theorem blockMask_fromRows_mul (A B : Matrix ι ι ℂ) :
    blockMask (fun i : ι ⊕ ι => i.isLeft = true) (fromRows A B * (fromRows A B)ᴴ) =
      fromBlocks (A * Aᴴ) 0 0 (B * Bᴴ) := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols]
  ext (i | i) (j | j) <;> simp [blockMask]

/-- **The Cauchy–Schwarz–Fischer step**: for `H, G` with rows indexed by `ι ⊕ ι`,
`|α_m(H G*)| ≤ √α_m(P_H) · √α_m(P_G)`, where `P_H` is the block-diagonal part of `H H*`. -/
theorem norm_alpha_mul_conjTranspose_le (H G : Matrix (ι ⊕ ι) ι ℂ) (m : ℕ) :
    ‖alpha m (H * Gᴴ)‖ ≤
      √(alpha m (blockMask (fun i : ι ⊕ ι => i.isLeft = true) (H * Hᴴ))).re *
        √(alpha m (blockMask (fun i : ι ⊕ ι => i.isLeft = true) (G * Gᴴ))).re := by
  set c : ι ⊕ ι → Prop := fun i => i.isLeft = true
  have key : ∀ (X : Matrix (ι ⊕ ι) ι ℂ) (K : Finset (ι ⊕ ι)),
      0 ≤ (det ((X * Xᴴ).submatrix (Subtype.val : K → ι ⊕ ι) Subtype.val)).re ∧
      (det ((X * Xᴴ).submatrix (Subtype.val : K → ι ⊕ ι) Subtype.val)).re ≤
        (det ((blockMask c (X * Xᴴ)).submatrix (Subtype.val : K → ι ⊕ ι) Subtype.val)).re := by
    intro X K
    have hP := (posSemidef_self_mul_conjTranspose X).submatrix (Subtype.val : K → ι ⊕ ι)
    have h := det_le_det_blockMask (fun i : K => c i.1) hP
    refine ⟨(Complex.nonneg_iff.1 hP.det_nonneg).1, ?_⟩
    have h' := (Complex.le_def.1 h).1
    convert h' using 3
    ext; rfl
  rw [alpha_eq_sum_minors, alpha_eq_sum_minors, alpha_eq_sum_minors, Complex.re_sum,
    Complex.re_sum]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun K _ => ?_).trans
    (Real.sum_sqrt_mul_sqrt_le _ (fun K => (key H K).1.trans (key H K).2)
      (fun K => (key G K).1.trans (key G K).2)))
  have hcs := norm_det_mul_sq_le (H.submatrix (Subtype.val : K → ι ⊕ ι) id)
    (Gᴴ.submatrix id (Subtype.val : K → ι ⊕ ι))
  have e : ∀ X : Matrix (ι ⊕ ι) ι ℂ, X.submatrix (Subtype.val : K → ι ⊕ ι) id *
      (X.submatrix (Subtype.val : K → ι ⊕ ι) id)ᴴ = (X * Xᴴ).submatrix Subtype.val Subtype.val :=
    fun X => by rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id]
  rw [← submatrix_mul _ _ _ id _ Function.bijective_id, e, ← conjTranspose_submatrix,
    conjTranspose_conjTranspose, e] at hcs
  rw [← Real.sqrt_mul ((key H K).1.trans (key H K).2)]
  refine Real.le_sqrt_of_sq_le (hcs.trans ?_)
  exact mul_le_mul (key H K).2 (key G K).2 (key G K).1 ((key H K).1.trans (key H K).2)

/-- With `α_p(A A*) ≤ a_p` and `α_p(B B*) ≤ b_p`, the block-diagonal part `P` of `[A; B][A; B]*`
has `α_m(P) ≤ ∑_{p ≤ m} a_p b_{m-p}`. -/
theorem re_alpha_blockMask_le (A B : Matrix ι ι ℂ) (a b : ℕ → ℝ)
    (ha : ∀ p, (alpha p (A * Aᴴ)).re ≤ a p) (hb : ∀ p, (alpha p (B * Bᴴ)).re ≤ b p) (m : ℕ) :
    (alpha m (blockMask (fun i : ι ⊕ ι => i.isLeft = true) (fromRows A B * (fromRows A B)ᴴ))).re
      ≤ ∑ p ∈ range (m + 1), a p * b (m - p) := by
  rw [blockMask_fromRows_mul, alpha_fromBlocks_zero, Complex.re_sum]
  refine sum_le_sum fun p _ => ?_
  have h1 := Complex.nonneg_iff.1 (alpha_nonneg (posSemidef_self_mul_conjTranspose A) p)
  have h2 := Complex.nonneg_iff.1 (alpha_nonneg (posSemidef_self_mul_conjTranspose B) (m - p))
  rw [Complex.mul_re, ← h1.2, zero_mul, sub_zero]
  exact mul_le_mul (ha p) (hb _) h2.1 (h1.1.trans (ha p))

end Assembly

section SigmaSystem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The Gram-type matrix `(⟪g_k, h_j⟫)_{k,j}` of two families. -/
noncomputable def gramMat {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {d : ℕ}
    (g h : Fin d → H) : Matrix (Fin d) (Fin d) ℂ :=
  of fun k j => ⟪g k, h j⟫_ℂ

/-- If `(g_k)` and `(h_j)` are pairwise orthogonal of norm `≤ 1` and `h_j = 0` for `j ≥ N`, then
`‖(⟪g_k, h_j⟫) z‖² ≤ ∑_{j < N} |z_j|²`. -/
theorem gramMat_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {d : ℕ}
    (g h : Fin d → H) (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫_ℂ = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1)
    (hh : ∀ j l, j ≠ l → ⟪h j, h l⟫_ℂ = 0) (hh1 : ∀ j, ‖h j‖ ≤ 1) (N : ℕ)
    (hN : ∀ j : Fin d, N ≤ j → h j = 0) (z : Fin d → ℂ) :
    ∑ k, ‖(gramMat g h *ᵥ z) k‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) < N), ‖z j‖ ^ 2 := by
  set w : H := ∑ j, z j • h j
  have hmv : ∀ k, (gramMat g h *ᵥ z) k = ⟪g k, w⟫_ℂ := fun k => by
    simp only [mulVec, dotProduct, gramMat, of_apply, w, inner_sum, inner_smul_right, mul_comm]
  simp only [hmv]
  refine (sum_norm_inner_sq_le univ g (fun k _ l _ hkl => hg k l hkl) (fun k _ => hg1 k) w).trans ?_
  have hw : ‖w‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 * ‖h j‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, sum_inner, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_sum, sum_eq_single j (fun l _ hlj => by
      rw [inner_smul_left, inner_smul_right, hh j l (Ne.symm hlj), mul_zero, mul_zero])
      (fun h => absurd (mem_univ j) h), inner_smul_left, inner_smul_right, ← mul_assoc,
      RCLike.conj_mul, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hw, sum_filter]
  refine sum_le_sum fun j _ => ?_
  split_ifs with hj
  · exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) (hh1 j))
  · rw [hN j (not_lt.1 hj)]; simp

/-- The first `n` right Schmidt vectors of `T`, completed by zeros. -/
noncomputable def xs (T : E →ₗ[ℂ] F) (n : ℕ) (j : Fin (finrank ℂ E)) : E :=
  if (j : ℕ) < n then ebasis T j else 0

/-- The first `n` left Schmidt vectors of `T`, completed by zeros. -/
noncomputable def ys (T : E →ₗ[ℂ] F) (n : ℕ) (j : Fin (finrank ℂ E)) : F :=
  if (j : ℕ) < n then fvec T j else 0

theorem inner_ebasis_of_ne (T : E →ₗ[ℂ] F) {k l : Fin (finrank ℂ E)} (h : k ≠ l) :
    ⟪ebasis T k, ebasis T l⟫_ℂ = 0 := (ebasis T).orthonormal.2 h

theorem norm_ebasis_le (T : E →ₗ[ℂ] F) (k : Fin (finrank ℂ E)) : ‖ebasis T k‖ ≤ 1 :=
  ((ebasis T).orthonormal.1 k).le

theorem inner_xs_of_ne (T : E →ₗ[ℂ] F) (n : ℕ) {k l : Fin (finrank ℂ E)} (h : k ≠ l) :
    ⟪xs T n k, xs T n l⟫_ℂ = 0 := by
  unfold xs; split_ifs <;> simp [inner_ebasis_of_ne T h]

theorem norm_xs_le (T : E →ₗ[ℂ] F) (n : ℕ) (k : Fin (finrank ℂ E)) : ‖xs T n k‖ ≤ 1 := by
  unfold xs; split_ifs; exacts [norm_ebasis_le T k, by simp]

theorem inner_ys_of_ne (T : E →ₗ[ℂ] F) (n : ℕ) {k l : Fin (finrank ℂ E)} (h : k ≠ l) :
    ⟪ys T n k, ys T n l⟫_ℂ = 0 := by
  unfold ys; split_ifs <;> simp [inner_fvec_of_ne T h]

theorem norm_ys_le (T : E →ₗ[ℂ] F) (n : ℕ) (k : Fin (finrank ℂ E)) : ‖ys T n k‖ ≤ 1 := by
  unfold ys; split_ifs; exacts [norm_fvec_le T k, by simp]

/-- The compression `(⟪y_i, w x_j⟫)_{i,j}` of `w` to the first `n` Schmidt pairs of `T`. -/
noncomputable def compr (T w : E →ₗ[ℂ] F) (n : ℕ) :
    Matrix (Fin (finrank ℂ E)) (Fin (finrank ℂ E)) ℂ :=
  of fun i j => ⟪ys T n i, w (xs T n j)⟫_ℂ

/-- `diag(√s_k(w))`. -/
noncomputable def sqrtDiag (w : E →ₗ[ℂ] F) : Matrix (Fin (finrank ℂ E)) (Fin (finrank ℂ E)) ℂ :=
  diagonal fun k => ((√(w.singularValues k) : ℝ) : ℂ)

/-- `(√S)* √S = S` for `S = diag(s_k(w))`. -/
theorem sqrtDiag_conj_mul (w : E →ₗ[ℂ] F) :
    (sqrtDiag w)ᴴ * sqrtDiag w =
      diagonal (fun k : Fin (finrank ℂ E) => ((w.singularValues k : ℝ) : ℂ)) := by
  rw [sqrtDiag, diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext k
  rw [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (w.singularValues_nonneg k)]

/-- `⟪a, w b⟫ = ∑_k ⟪a, f_k⟫ s_k ⟪e_k, b⟫`, the Schmidt expansion of `w`. -/
theorem inner_apply_eq_sum_schmidt (w : E →ₗ[ℂ] F) (a : F) (b : E) :
    ⟪a, w b⟫_ℂ = ∑ k, ⟪a, fvec w k⟫_ℂ * ((w.singularValues k : ℝ) : ℂ) * ⟪ebasis w k, b⟫_ℂ := by
  conv_lhs => rw [← (ebasis w).sum_repr' b]
  rw [map_sum, inner_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_smul, apply_ebasis_eq, inner_smul_right, inner_smul_right]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

/-- **The factorisation** `compr T w = (√S Φ)* (√S Ψ)`, with `Φ = (⟪f_k(w), y_j⟫)`,
`Ψ = (⟪e_k(w), x_j⟫)` and `S = diag(s_k(w))`. -/
theorem compr_eq (T w : E →ₗ[ℂ] F) (n : ℕ) :
    compr T w n = (sqrtDiag w * gramMat (fvec w) (ys T n))ᴴ *
      (sqrtDiag w * gramMat (ebasis w) (xs T n)) := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (sqrtDiag w)ᴴ, sqrtDiag_conj_mul]
  ext i j
  rw [mul_apply]
  simp only [compr, of_apply, diagonal_mul, conjTranspose_apply, gramMat,
    inner_apply_eq_sum_schmidt]
  refine sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, inner_conj_symm, mul_assoc]

/-- `compr T T n` is the diagonal matrix of `s_j(T)`, `j < n`. -/
theorem compr_self (T : E →ₗ[ℂ] F) (n : ℕ) :
    compr T T n = diagonal fun j : Fin (finrank ℂ E) => (((if (j : ℕ) < n then T.singularValues j else 0 : ℝ)) : ℂ) := by
  ext i j
  simp only [compr, of_apply, xs, ys, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : (i : ℕ) < n <;> simp [h, inner_fvec_apply_ebasis]
  · by_cases h1 : (i : ℕ) < n <;> by_cases h2 : (j : ℕ) < n <;>
      simp [h1, h2, hij, apply_ebasis_eq, inner_fvec_of_ne T hij]

/-- `σ_n^m(T) ≤ Re α_m(compr T T n)` (in fact equal). -/
theorem sigma_le_alpha_compr (T : E →ₗ[ℂ] F) (n m : ℕ) :
    sigma n m T ≤ (alpha m (compr T T n)).re := by
  rw [compr_self, alpha_diagonal, Complex.re_sum]
  simp only [← Complex.ofReal_prod, Complex.ofReal_re]
  rw [sum_powersetCard_fin (finrank ℂ E) m
    (fun j => if j < n then T.singularValues j else 0), sigma]
  exact sum_powersetCard_prod_le m
    (fun i _ => by split_ifs; exacts [T.singularValues_nonneg i, le_rfl])
    (fun i _ hi => T.singularValues_of_finrank_le (by simpa using hi))
    (fun i hi _ => by simp [mem_range.1 hi])

/-- The interlacing bound for the two factors of `compr T w n`:
`α_p(√S Ψ (√S Ψ)*) ≤ σ_n^p(w)`. -/
theorem re_alpha_sqrtDiag_gramMat_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w : E →ₗ[ℂ] F) (g h : Fin (finrank ℂ E) → H) (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫_ℂ = 0)
    (hg1 : ∀ k, ‖g k‖ ≤ 1) (hh : ∀ j l, j ≠ l → ⟪h j, h l⟫_ℂ = 0) (hh1 : ∀ j, ‖h j‖ ≤ 1)
    (n : ℕ) (hn : ∀ j : Fin (finrank ℂ E), n ≤ j → h j = 0) (p : ℕ) :
    (alpha p (sqrtDiag w * gramMat g h * (sqrtDiag w * gramMat g h)ᴴ)).re ≤ sigma n p w := by
  rw [alpha_mul_comm, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (sqrtDiag w)ᴴ,
    sqrtDiag_conj_mul, ← Matrix.mul_assoc]
  exact alpha_conj_diagonal_le (fun k => w.singularValues k) w.singularValues_antitone
    w.singularValues_nonneg n _ (gramMat_bound g h hg hg1 hh hh1 n hn) p

/-- **The system (16) of page 71**, for every `m` and `n`, for linear maps between
finite-dimensional complex inner product spaces:
`σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`. -/
theorem sigma_system (u v : E →ₗ[ℂ] F) (n m : ℕ) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  set T := u + v
  set H := fromRows (sqrtDiag u * gramMat (ebasis u) (xs T n))
    (sqrtDiag v * gramMat (ebasis v) (xs T n))
  set G := fromRows (sqrtDiag u * gramMat (fvec u) (ys T n))
    (sqrtDiag v * gramMat (fvec v) (ys T n))
  have hM : compr T T n = Gᴴ * H := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, ← compr_eq,
      ← compr_eq]
    ext i j
    simp [compr, T]
  have hxs : ∀ j : Fin (finrank ℂ E), n ≤ j → xs T n j = 0 := fun j hj => by
    simp [xs, not_lt.2 hj]
  have hys : ∀ j : Fin (finrank ℂ E), n ≤ j → ys T n j = 0 := fun j hj => by
    simp [ys, not_lt.2 hj]
  have bΨ : ∀ (w : E →ₗ[ℂ] F) p, (alpha p (sqrtDiag w * gramMat (ebasis w) (xs T n) *
      (sqrtDiag w * gramMat (ebasis w) (xs T n))ᴴ)).re ≤ sigma n p w := fun w p =>
    re_alpha_sqrtDiag_gramMat_le w _ _ (fun _ _ h => inner_ebasis_of_ne w h) (norm_ebasis_le w)
      (fun _ _ h => inner_xs_of_ne T n h) (norm_xs_le T n) n hxs p
  have bΦ : ∀ (w : E →ₗ[ℂ] F) p, (alpha p (sqrtDiag w * gramMat (fvec w) (ys T n) *
      (sqrtDiag w * gramMat (fvec w) (ys T n))ᴴ)).re ≤ sigma n p w := fun w p =>
    re_alpha_sqrtDiag_gramMat_le w _ _ (fun _ _ h => inner_fvec_of_ne w h) (norm_fvec_le w)
      (fun _ _ h => inner_ys_of_ne T n h) (norm_ys_le T n) n hys p
  have hH := re_alpha_blockMask_le _ _ _ _ (bΨ u) (bΨ v) m
  have hG := re_alpha_blockMask_le _ _ _ _ (bΦ u) (bΦ v) m
  set R := ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v
  have hR : 0 ≤ R := sum_nonneg fun p _ => mul_nonneg (sigma_nonneg n p u) (sigma_nonneg n _ v)
  calc sigma n m T ≤ (alpha m (compr T T n)).re := sigma_le_alpha_compr T n m
    _ ≤ ‖alpha m (compr T T n)‖ := Complex.re_le_norm _
    _ = ‖alpha m (H * Gᴴ)‖ := by rw [hM, alpha_mul_comm]
    _ ≤ _ := norm_alpha_mul_conjTranspose_le H G m
    _ ≤ √R * √R := mul_le_mul (Real.sqrt_le_sqrt hH) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = R := Real.mul_self_sqrt hR

/-- **The product form (15) of page 71, for every `n`**: for `r ≥ 0`,
`∏_{i<n} (1 + r s_i(u+v)) ≤ ∏_{i<n} (1 + r s_i(u)) · ∏_{i<n} (1 + r s_i(v))`. -/
theorem prod_one_add_singularValues_add_le (u v : E →ₗ[ℂ] F) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ range n, (1 + r * (u + v).singularValues i) ≤
      (∏ i ∈ range n, (1 + r * u.singularValues i)) *
        ∏ i ∈ range n, (1 + r * v.singularValues i) :=
  prod_le_of_sigma_system u v n (fun m _ => sigma_system u v n m) hr

/-- **Page 129, unconditionally in finite dimension**: for `0 < p < 1`,
`∑_{i<n} s_i(u+v)^p ≤ ∑_{i<n} s_i(u)^p + ∑_{i<n} s_i(v)^p`. -/
theorem sum_singularValues_rpow_add_le (u v : E →ₗ[ℂ] F) (n : ℕ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∑ i ∈ range n, (u + v).singularValues i ^ p ≤
      ∑ i ∈ range n, u.singularValues i ^ p + ∑ i ∈ range n, v.singularValues i ^ p :=
  sum_singularValues_rpow_add_le_of_prod u v n hp0 hp1 fun _ hr =>
    prod_one_add_singularValues_add_le u v n hr

end SigmaSystem

end Grothendieck.Folder1

/-!
## Pages 71–73: the system (16) over `ℝ`, and Prop. 3 as a supremum (finding `1-sigma-nm-system`)

* `sigma_system_real`: (16) for every `m` and `n` for linear maps between finite-dimensional
  *real* inner product spaces, hence (15) (`prod_one_add_singularValues_add_le_real`) and the
  subadditivity of `∑_{i<n} s_i^p`, `0 < p < 1` (`sum_singularValues_rpow_add_le_real`). The
  proof complexifies: `cplx u` is the matrix of `u` in orthonormal bases, read over `ℂ`; the
  characteristic polynomial of `(cplx u)* (cplx u)` is that of `u* u` mapped to `ℂ`
  (`charpoly_map`), so their eigenvalues, hence the singular values, agree
  (`eigenvalues_eq_of_charpoly_map`, `singularValues_cplx`), and `cplx` is additive.
* `isGreatest_norm_alpha_comp`: **Prop. 3** in finite dimension over `ℂ`: `σ_n^m(u)` is the
  largest value of `|α_m(w u)|` over the linear maps `w : F → E` with `‖w z‖ ≤ ‖z‖` and
  `rank w ≤ n` (`α_m` in any basis of `E`, `alpha_toMatrix_eq`). The upper bound
  (`norm_alpha_comp_le`) writes the matrix of `w u` in the Schmidt basis of `w*` as
  `D N`, `α_m(D N) = α_m(N D)`, and `N D` is a compression `(⟪y_i, u x_j⟫)` by families
  orthogonal, of norm `≤ 1` and zero from `n` on (`norm_alpha_cmat_le`, through the
  factorisation `cmat_eq`, Cauchy–Schwarz `norm_alpha_mul_conjTranspose_le_sqrt` and the
  interlacing bound); it is attained by `w₀ = ∑_{j<n} e_j ⟨f_j, ·⟩` (`wmax`).

Not formalised: the second form `sup α_m(|w u|)` of Prop. 3, Prop. 3 over `ℝ`, the trace-class
formula (14), compact operators, and the optimality claim of page 73.
-/

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace Matrix Polynomial
open scoped MatrixOrder ComplexOrder ComplexConjugate

section RealSigmaSystem

/-- Two self-adjoint operators, one real and one complex, whose characteristic polynomials
correspond under `ℝ → ℂ`, have the same eigenvalues. -/
theorem eigenvalues_eq_of_charpoly_map {E E' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] {T : E →ₗ[ℝ] E} {T' : E' →ₗ[ℂ] E'}
    (hT : T.IsSymmetric) (hT' : T'.IsSymmetric) {d : ℕ} (hd : finrank ℝ E = d)
    (hd' : finrank ℂ E' = d) (h : T'.charpoly = T.charpoly.map (algebraMap ℝ ℂ)) :
    hT.eigenvalues hd = hT'.eigenvalues hd' := by
  rw [← List.ofFn_inj, ← hT.sort_roots_charpoly_eq_eigenvalues, ←
    hT'.sort_roots_charpoly_eq_eigenvalues, h, hT.splits_charpoly.roots_map, Multiset.map_map]
  congr 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The complexification of a real linear map, as the complex matrix of `u` in orthonormal
bases. -/
noncomputable def cplx (u : E →ₗ[ℝ] F) :
    EuclideanSpace ℂ (Fin (finrank ℝ E)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℝ F)) :=
  toEuclideanLin ((LinearMap.toMatrix (stdOrthonormalBasis ℝ E).toBasis
    (stdOrthonormalBasis ℝ F).toBasis u).map (algebraMap ℝ ℂ))

theorem cplx_add (u v : E →ₗ[ℝ] F) : cplx (u + v) = cplx u + cplx v := by
  simp [cplx, Matrix.map_add]

theorem singularValues_cplx (u : E →ₗ[ℝ] F) : (cplx u).singularValues = u.singularValues := by
  have hd : finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E))) = finrank ℝ E :=
    finrank_euclideanSpace_fin
  have hc : (LinearMap.adjoint (cplx u) ∘ₗ cplx u).charpoly =
      (LinearMap.adjoint u ∘ₗ u).charpoly.map (algebraMap ℝ ℂ) := by
    rw [cplx, ← toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [toEuclideanLin_eq_toLin_orthonormal]
    rw [← Matrix.toLin_mul, charpoly_toLin,
      ← LinearMap.charpoly_toMatrix _ (stdOrthonormalBasis ℝ E).toBasis,
      LinearMap.toMatrix_comp _ (stdOrthonormalBasis ℝ F).toBasis, LinearMap.toMatrix_adjoint,
      ← charpoly_map]
    congr 1
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp
  ext i
  rcases lt_or_ge i (finrank ℝ E) with hi | hi
  · rw [(cplx u).singularValues_of_lt hd hi, u.singularValues_of_lt rfl hi,
      eigenvalues_eq_of_charpoly_map _ _ rfl hd hc]
  · rw [(cplx u).singularValues_of_finrank_le (hd.symm ▸ hi), u.singularValues_of_finrank_le hi]

theorem sigma_cplx (n m : ℕ) (u : E →ₗ[ℝ] F) : sigma n m (cplx u) = sigma n m u := by
  simp only [sigma, singularValues_cplx]

/-- **The system (16) of page 71 over `ℝ`**, for every `m` and `n`. -/
theorem sigma_system_real (u v : E →ₗ[ℝ] F) (n m : ℕ) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  simpa only [← cplx_add, sigma_cplx] using sigma_system (cplx u) (cplx v) n m

/-- The product form (15) over `ℝ`, for every `n`. -/
theorem prod_one_add_singularValues_add_le_real (u v : E →ₗ[ℝ] F) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) :
    ∏ i ∈ range n, (1 + r * (u + v).singularValues i) ≤
      (∏ i ∈ range n, (1 + r * u.singularValues i)) *
        ∏ i ∈ range n, (1 + r * v.singularValues i) :=
  prod_le_of_sigma_system u v n (fun m _ => sigma_system_real u v n m) hr

/-- Page 129 over `ℝ`: `∑_{i<n} s_i(u+v)^p ≤ ∑_{i<n} s_i(u)^p + ∑_{i<n} s_i(v)^p`, `0 < p < 1`. -/
theorem sum_singularValues_rpow_add_le_real (u v : E →ₗ[ℝ] F) (n : ℕ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∑ i ∈ range n, (u + v).singularValues i ^ p ≤
      ∑ i ∈ range n, u.singularValues i ^ p + ∑ i ∈ range n, v.singularValues i ^ p :=
  sum_singularValues_rpow_add_le_of_prod u v n hp0 hp1 fun _ hr =>
    prod_one_add_singularValues_add_le_real u v n hr

end RealSigmaSystem

section PropositionThree

/-- The determinant form of Cauchy–Schwarz, summed over the principal minors:
`|α_m(H G*)| ≤ √α_m(H H*) · √α_m(G G*)`. -/
theorem norm_alpha_mul_conjTranspose_le_sqrt {o ι : Type*} [Fintype o] [DecidableEq o]
    [Fintype ι] (H G : Matrix o ι ℂ) (m : ℕ) :
    ‖alpha m (H * Gᴴ)‖ ≤ √(alpha m (H * Hᴴ)).re * √(alpha m (G * Gᴴ)).re := by
  have key : ∀ (X : Matrix o ι ℂ) (K : Finset o),
      0 ≤ (det ((X * Xᴴ).submatrix (Subtype.val : K → o) Subtype.val)).re := fun X _ =>
    (Complex.nonneg_iff.1 ((posSemidef_self_mul_conjTranspose X).submatrix _).det_nonneg).1
  rw [alpha_eq_sum_minors, alpha_eq_sum_minors, alpha_eq_sum_minors, Complex.re_sum,
    Complex.re_sum]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun K _ => ?_).trans
    (Real.sum_sqrt_mul_sqrt_le _ (key H) (key G)))
  have hcs := norm_det_mul_sq_le (H.submatrix (Subtype.val : K → o) id)
    (Gᴴ.submatrix id (Subtype.val : K → o))
  have e : ∀ X : Matrix o ι ℂ, X.submatrix (Subtype.val : K → o) id *
      (X.submatrix (Subtype.val : K → o) id)ᴴ = (X * Xᴴ).submatrix Subtype.val Subtype.val :=
    fun X => by rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id]
  rw [← submatrix_mul _ _ _ id _ Function.bijective_id, e, ← conjTranspose_submatrix,
    conjTranspose_conjTranspose, e] at hcs
  rw [← Real.sqrt_mul (key H K)]
  exact Real.le_sqrt_of_sq_le hcs

/-- `α_m` of the matrix of an endomorphism does not depend on the basis. -/
theorem alpha_toMatrix_eq {E ι ι' : Type*} [AddCommGroup E] [Module ℂ E] [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Basis ι ℂ E) (b' : Basis ι' ℂ E)
    (A : E →ₗ[ℂ] E) (m : ℕ) :
    alpha m (LinearMap.toMatrix b b A) = alpha m (LinearMap.toMatrix b' b' A) := by
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b', alpha_mul_comm,
    ← Matrix.mul_assoc, b'.toMatrix_mul_toMatrix_flip, Matrix.one_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The compression `(⟪y_i, w x_j⟫)_{i,j}` of `w` by two families. -/
noncomputable def cmat (x : Fin (finrank ℂ E) → E) (y : Fin (finrank ℂ E) → F)
    (w : E →ₗ[ℂ] F) : Matrix (Fin (finrank ℂ E)) (Fin (finrank ℂ E)) ℂ :=
  of fun i j => ⟪y i, w (x j)⟫_ℂ

/-- `cmat x y w = (√S Φ)* (√S Ψ)`, with `Φ = (⟪f_k(w), y_j⟫)`, `Ψ = (⟪e_k(w), x_j⟫)`. -/
theorem cmat_eq (x : Fin (finrank ℂ E) → E) (y : Fin (finrank ℂ E) → F) (w : E →ₗ[ℂ] F) :
    cmat x y w = (sqrtDiag w * gramMat (fvec w) y)ᴴ * (sqrtDiag w * gramMat (ebasis w) x) := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (sqrtDiag w)ᴴ, sqrtDiag_conj_mul]
  ext i j
  rw [mul_apply]
  simp only [cmat, of_apply, diagonal_mul, conjTranspose_apply, gramMat,
    inner_apply_eq_sum_schmidt]
  refine sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, inner_conj_symm, mul_assoc]

/-- **The upper half of Prop. 3, for compressions**: for families `x`, `y` pairwise orthogonal,
of norm `≤ 1` and zero from the index `n` on, `|α_m(⟪y_i, u x_j⟫)| ≤ σ_n^m(u)`. -/
theorem norm_alpha_cmat_le (u : E →ₗ[ℂ] F) (x : Fin (finrank ℂ E) → E)
    (y : Fin (finrank ℂ E) → F) (hx : ∀ k l, k ≠ l → ⟪x k, x l⟫_ℂ = 0) (hx1 : ∀ k, ‖x k‖ ≤ 1)
    (hy : ∀ k l, k ≠ l → ⟪y k, y l⟫_ℂ = 0) (hy1 : ∀ k, ‖y k‖ ≤ 1) (n : ℕ)
    (hxn : ∀ j : Fin (finrank ℂ E), n ≤ j → x j = 0)
    (hyn : ∀ j : Fin (finrank ℂ E), n ≤ j → y j = 0) (m : ℕ) :
    ‖alpha m (cmat x y u)‖ ≤ sigma n m u := by
  rw [cmat_eq, alpha_mul_comm]
  refine (norm_alpha_mul_conjTranspose_le_sqrt _ _ m).trans ?_
  calc _ ≤ √(sigma n m u) * √(sigma n m u) := mul_le_mul
        (Real.sqrt_le_sqrt (re_alpha_sqrtDiag_gramMat_le u _ _
          (fun _ _ h => inner_ebasis_of_ne u h) (norm_ebasis_le u) hx hx1 n hxn m))
        (Real.sqrt_le_sqrt (re_alpha_sqrtDiag_gramMat_le u _ _
          (fun _ _ h => inner_fvec_of_ne u h) (norm_fvec_le u) hy hy1 n hyn m))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = sigma n m u := Real.mul_self_sqrt (sigma_nonneg n m u)

/-- The adjoint of a contraction is a contraction. -/
theorem norm_adjoint_apply_le {w : F →ₗ[ℂ] E} (hw : ∀ z, ‖w z‖ ≤ ‖z‖) (z : E) :
    ‖LinearMap.adjoint w z‖ ≤ ‖z‖ := by
  set a := LinearMap.adjoint w z
  have h : ‖a‖ ^ 2 ≤ ‖a‖ * ‖z‖ := by
    rw [← @inner_self_eq_norm_sq ℂ, LinearMap.adjoint_inner_right]
    calc _ ≤ ‖⟪w a, z⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖w a‖ * ‖z‖ := norm_inner_le_norm _ _
      _ ≤ ‖a‖ * ‖z‖ := mul_le_mul_of_nonneg_right (hw a) (norm_nonneg _)
  nlinarith [norm_nonneg a, norm_nonneg z]

/-- **Prop. 3 of page 72, upper bound**: for a contraction `w : F → E` of rank `≤ n`,
`|α_m(w u)| ≤ σ_n^m(u)`, `α_m` computed in any basis of `E`. -/
theorem norm_alpha_comp_le (u : E →ₗ[ℂ] F) {w : F →ₗ[ℂ] E} (hw : ∀ z, ‖w z‖ ≤ ‖z‖)
    {n : ℕ} (hn : finrank ℂ (LinearMap.range w) ≤ n) (m : ℕ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℂ E) :
    ‖alpha m (LinearMap.toMatrix b b (w ∘ₗ u))‖ ≤ sigma n m u := by
  set w' := LinearMap.adjoint w
  set t : Fin (finrank ℂ E) → ℂ := fun k => ((√(w'.singularValues k) : ℝ) : ℂ)
  have ht1 : ∀ k, ‖t k‖ ≤ 1 := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_le_one, ← norm_apply_ebasis]
    exact (norm_adjoint_apply_le hw _).trans (norm_ebasis_le w' k)
  have ht0 : ∀ k : Fin (finrank ℂ E), n ≤ k → t k = 0 := fun k hk => by
    simp [t, w'.singularValues_eq_zero_iff_le_finrank_range.2
      ((LinearMap.finrank_range_adjoint w).trans_le (hn.trans hk))]
  set D : Matrix (Fin (finrank ℂ E)) (Fin (finrank ℂ E)) ℂ := diagonal t
  set N : Matrix (Fin (finrank ℂ E)) (Fin (finrank ℂ E)) ℂ :=
    of fun i j => t i * ⟪fvec w' i, u (ebasis w' j)⟫_ℂ
  have hM : LinearMap.toMatrix (ebasis w').toBasis (ebasis w').toBasis (w ∘ₗ u) = D * N := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
      ← LinearMap.adjoint_inner_left, apply_ebasis_eq, inner_smul_left, diagonal_mul]
    simp only [N, of_apply, t, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (w'.singularValues_nonneg _)]
    simp [w']
  have hC : N * D = cmat (fun j => t j • ebasis w' j) (fun i => t i • fvec w' i) u := by
    ext i j
    simp [N, D, cmat, t]
    ring
  rw [alpha_toMatrix_eq b (ebasis w').toBasis, hM, alpha_mul_comm, hC]
  refine norm_alpha_cmat_le u _ _ (fun k l h => ?_) (fun k => ?_) (fun k l h => ?_) (fun k => ?_)
    n (fun j hj => by simp [ht0 j hj]) (fun j hj => by simp [ht0 j hj]) m
  · simp [inner_ebasis_of_ne w' h]
  · rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (norm_ebasis_le w' k)).trans (ht1 k)
  · simp [inner_fvec_of_ne w' h]
  · rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (norm_fvec_le w' k)).trans (ht1 k)

/-- The contraction `w₀ = ∑_{j<n} e_j ⟨f_j, ·⟩` of rank `≤ n` that attains Prop. 3. -/
noncomputable def wmax (u : E →ₗ[ℂ] F) (n : ℕ) : F →ₗ[ℂ] E :=
  ∑ k, (innerₛₗ ℂ (ys u n k)).smulRight (ebasis u k)

theorem inner_ebasis_wmax (u : E →ₗ[ℂ] F) (n : ℕ) (i : Fin (finrank ℂ E)) (z : F) :
    ⟪ebasis u i, wmax u n z⟫_ℂ = ⟪ys u n i, z⟫_ℂ := by
  simp [wmax, orthonormal_iff_ite.1 (ebasis u).orthonormal]

theorem norm_wmax_apply_le (u : E →ₗ[ℂ] F) (n : ℕ) (z : F) : ‖wmax u n z‖ ≤ ‖z‖ := by
  refine pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 ?_
  rw [← (ebasis u).sum_sq_norm_inner_right]
  simp only [inner_ebasis_wmax]
  exact sum_norm_inner_sq_le univ _ (fun k _ l _ h => inner_ys_of_ne u n h)
    (fun k _ => norm_ys_le u n k) z

theorem finrank_range_wmax_le (u : E →ₗ[ℂ] F) (n : ℕ) :
    finrank ℂ (LinearMap.range (wmax u n)) ≤ n := by
  classical
  set S := (univ.filter fun k : Fin (finrank ℂ E) => (k : ℕ) < n).image (ebasis u)
  have hle : LinearMap.range (wmax u n) ≤ Submodule.span ℂ (S : Set E) := by
    rintro _ ⟨z, rfl⟩
    rw [wmax, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < n
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simpa [S] using ⟨k, hk, rfl⟩))
    · simp [ys, hk]
  refine (Submodule.finrank_mono hle).trans ((finrank_span_finset_le_card S).trans
    (card_image_le.trans ?_))
  calc #(univ.filter fun k : Fin (finrank ℂ E) => (k : ℕ) < n) ≤ #(range n) :=
        card_le_card_of_injOn (fun k => (k : ℕ)) (fun k hk => by simpa using hk)
          (fun a _ b _ h => Fin.ext h)
    _ = n := card_range n

theorem toMatrix_wmax_comp (u : E →ₗ[ℂ] F) (n : ℕ) :
    LinearMap.toMatrix (ebasis u).toBasis (ebasis u).toBasis (wmax u n ∘ₗ u) = compr u u n := by
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    inner_ebasis_wmax]
  simp only [compr, of_apply, xs]
  split_ifs with hj
  · rfl
  · by_cases hij : i = j
    · subst hij; simp [ys, hj]
    · rw [apply_ebasis_eq, inner_smul_right, ys]
      split_ifs <;> simp [inner_fvec_of_ne u hij]

/-- **Prop. 3 of page 72**, in finite dimension: `σ_n^m(u)` is the largest value of
`|α_m(w u)|` over the contractions `w : F → E` of rank `≤ n` (in any basis of `E`). -/
theorem isGreatest_norm_alpha_comp (u : E →ₗ[ℂ] F) (n m : ℕ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℂ E) :
    IsGreatest {r | ∃ w : F →ₗ[ℂ] E, (∀ z, ‖w z‖ ≤ ‖z‖) ∧
      finrank ℂ (LinearMap.range w) ≤ n ∧ r = ‖alpha m (LinearMap.toMatrix b b (w ∘ₗ u))‖}
      (sigma n m u) := by
  refine ⟨⟨wmax u n, norm_wmax_apply_le u n, finrank_range_wmax_le u n, le_antisymm ?_
    (norm_alpha_comp_le u (norm_wmax_apply_le u n) (finrank_range_wmax_le u n) m b)⟩, ?_⟩
  · rw [alpha_toMatrix_eq b (ebasis u).toBasis, toMatrix_wmax_comp]
    exact (sigma_le_alpha_compr u n m).trans (Complex.re_le_norm _)
  · rintro _ ⟨w, hw, hn, rfl⟩
    exact norm_alpha_comp_le u hw hn m b

end PropositionThree

end Grothendieck.Folder1
