module

public import Mathlib

@[expose] public section


/-!
# Folder 10, pages 191–197: the indecomposables of `𝔾_a ⋊ 𝔾_m`

The modernised reading `transcripts/10/10.modern.tex` (« III. Le produit semi-direct »)
takes `G = k ⋊ k^*` over a field of characteristic `0`, `k^*` acting on `k` by
`λ ↦ λ^p`. Its Lie algebra has generators `X` (of `𝔾_a`) and `Y` (of `𝔾_m`) with
`[Y, X] = p X` (p. 191). The page classifies the indecomposable representations as the
strings `e_{n,k}` (`n ∈ ℤ`, `k ≥ 1`): `k[Z]/Z^k`, `X` the multiplication by `Z`, weights
`n, n + p, …, n + p(k - 1)`; they are pairwise inequivalent, `ě_{n,k} = e_{-n-p(k-1),k}`
(p. 194), and the ring of classes is `Λ[ξ]`, `Λ = ℤ[ℤ]`, `ξ = e_{0,2}` (p. 197), the key
being that `ξ^n` has leading term `e_{0,n+1}`. This is the reachable part of finding
`10-split-ring-ga-rtimes-gm` of `src/content/findings.ts`.

What is formalised. A representation is read as the reading reads it, through its Lie
algebra: a vector space with two endomorphisms `X`, `Y`; maps of representations are linear
maps commuting with both (`IsoRep`). The string `e_{n,k}` is `Fin k → K` with
`X zⱼ = zⱼ₊₁` (`sX`) and `Y zⱼ = (n + p j) zⱼ` (`sY`).

* `sY_sX`: `[Y, X] = p X` on every string.
* `string_end_scalar`, `string_indecomposable`: in characteristic `0` with `p ≥ 1`, an
  endomorphism of `e_{n,k}` is a scalar, so `e_{n,k}` is indecomposable.
* `string_iso_imp`: `e_{n,k} ≅ e_{n',k'}` with `k ≥ 1` forces `k = k'` and `n = n'`
  (dimension and trace of `Y`).
* `string_dual`: the dual representation `(-Xᵀ, -Yᵀ)` of `e_{n,k}` is `e_{-n-p(k-1),k}`.
* `xi_tensor_string`: `ξ ⊗ e_{n,k} ≅ e_{n,k+1} ⊕ e_{n+p,k-1}` for `k ≥ 2`, as soon as `k`
  is invertible in `K`; no hypothesis on `p`. This is the step that makes `ξ^n` triangular
  with leading coefficient `1` (`α = 0` on page 197).

Not formalised: that every indecomposable is a string (Lemmes 1 and 2), and the ring
`R(G) = Λ[ξ]` itself, which needs that classification and the Krull–Schmidt theorem,
neither in mathlib; the algebraic-group packaging.
-/

namespace Grothendieck.Folder10

open TensorProduct

variable {K : Type*} [Field K]

/-- Two representations `(V, X, Y)` and `(W, X', Y')` are isomorphic. -/
def IsoRep {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (X Y : Module.End K V) (X' Y' : Module.End K W) : Prop :=
  ∃ e : V ≃ₗ[K] W, (e : V →ₗ[K] W) ∘ₗ X = X' ∘ₗ e ∧ (e : V →ₗ[K] W) ∘ₗ Y = Y' ∘ₗ e

/-- The weight `n + p i`. -/
def wt (p : ℕ) (n : ℤ) (i : ℕ) : K := (n : K) + p * i

/-- `X` on the string of length `k`: `zⱼ ↦ zⱼ₊₁`, `z_{k-1} ↦ 0`. -/
def sX (k : ℕ) : Module.End K (Fin k → K) where
  toFun u i := if h : 0 < (i : ℕ) then u ⟨i - 1, by omega⟩ else 0
  map_add' u v := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c u := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- `Y` on the string `e_{n,k}`: `zⱼ ↦ (n + p j) zⱼ`. -/
def sY (p : ℕ) (n : ℤ) (k : ℕ) : Module.End K (Fin k → K) where
  toFun u i := wt p n i * u i
  map_add' u v := by ext i; simp only [Pi.add_apply]; ring
  map_smul' c u := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma sX_apply {k : ℕ} (u : Fin k → K) (i : Fin k) :
    sX k u i = if h : 0 < (i : ℕ) then u ⟨i - 1, by omega⟩ else 0 := rfl

lemma sY_apply (p : ℕ) (n : ℤ) {k : ℕ} (u : Fin k → K) (i : Fin k) :
    sY p n k u i = wt p n i * u i := rfl

lemma sX_single {k : ℕ} (j : Fin k) :
    sX k (Pi.single j (1 : K)) = if h : (j : ℕ) + 1 < k then Pi.single ⟨j + 1, h⟩ 1 else 0 := by
  ext i
  rw [sX_apply]
  split_ifs with h1 h2 h2 <;>
    simp only [Pi.single_apply, Fin.ext_iff, Pi.zero_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

lemma sY_single (p : ℕ) (n : ℤ) {k : ℕ} (j : Fin k) :
    sY p n k (Pi.single j (1 : K)) = (wt p n j : K) • Pi.single j (1 : K) := by
  ext i
  rw [sY_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The Lie relation `[Y, X] = p X` (p. 191) on every string. -/
theorem sY_sX (p : ℕ) (n : ℤ) {k : ℕ} (u : Fin k → K) :
    sY p n k (sX k u) = sX k (sY p n k u) + (p : K) • sX k u := by
  ext i
  simp only [sY_apply, sX_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, wt]
  split_ifs with h
  · simp only [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]; push_cast; ring
  · simp

/-! ## Endomorphisms of a string -/

/-- In characteristic `0` with `p ≥ 1`, every endomorphism of `e_{n,k}` is a scalar. -/
theorem string_end_scalar [CharZero K] {p : ℕ} (hp : p ≠ 0) (n : ℤ) {k : ℕ}
    (f : Module.End K (Fin k → K)) (hX : f ∘ₗ sX k = sX k ∘ₗ f)
    (hY : f ∘ₗ sY p n k = sY p n k ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  -- `f zⱼ = cⱼ zⱼ`
  have hdiag : ∀ j i : Fin k, i ≠ j → f (Pi.single j 1) i = 0 := by
    intro j i hij
    have h := congrArg (fun g => g (Pi.single j (1 : K)) i) hY
    simp only [LinearMap.comp_apply, sY_single, map_smul, Pi.smul_apply, smul_eq_mul,
      sY_apply] at h
    have hw : wt p n j ≠ (wt p n i : K) := by
      intro hw
      apply hij
      simp only [wt, add_right_inj, mul_eq_mul_left_iff, Nat.cast_inj,
        Nat.cast_eq_zero, hp, or_false] at hw
      exact Fin.ext hw.symm
    have h' : (wt p n j - wt p n i) * f (Pi.single j 1) i = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hw)
  have hsingle : ∀ j : Fin k, f (Pi.single j 1) = f (Pi.single j 1) j • Pi.single j 1 := by
    intro j; ext i
    by_cases h : i = j
    · subst h; simp
    · simp [h, hdiag j i h]
  -- the coefficients are constant along `X`
  have hstep : ∀ (j : ℕ) (h : j + 1 < k),
      f (Pi.single ⟨j + 1, h⟩ 1) ⟨j + 1, h⟩ = f (Pi.single ⟨j, by omega⟩ 1) ⟨j, by omega⟩ := by
    intro j h
    have e := congrArg (fun g => g (Pi.single ⟨j, by omega⟩ (1 : K)) ⟨j + 1, h⟩) hX
    simp only [LinearMap.comp_apply, sX_single, h, ↓reduceDIte] at e
    rw [e, sX_apply]
    simp
  have hconst : ∀ (j : ℕ) (h : j < k),
      f (Pi.single ⟨j, h⟩ 1) ⟨j, h⟩ = f (Pi.single ⟨0, by omega⟩ 1) ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro h; rfl
    | succ j ih => intro h; rw [hstep j h, ih]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨0, LinearMap.ext fun u => funext fun i => i.elim0⟩
  refine ⟨f (Pi.single ⟨0, hk⟩ 1) ⟨0, hk⟩, (Pi.basisFun K (Fin k)).ext fun j => ?_⟩
  rw [Pi.basisFun_apply, hsingle j, hconst j j.2]
  rfl

/-- `e_{n,k}` is indecomposable: an idempotent endomorphism is `0` or the identity. -/
theorem string_indecomposable [CharZero K] {p : ℕ} (hp : p ≠ 0) (n : ℤ) {k : ℕ}
    (f : Module.End K (Fin k → K)) (hX : f ∘ₗ sX k = sX k ∘ₗ f)
    (hY : f ∘ₗ sY p n k = sY p n k ∘ₗ f) (hf : f * f = f) : f = 0 ∨ f = 1 := by
  obtain ⟨c, rfl⟩ := string_end_scalar hp n f hX hY
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact .inl <| LinearMap.ext fun u => funext fun i => i.elim0
  have h := congrArg (fun g : Module.End K (Fin k → K) => g (Pi.single ⟨0, hk⟩ 1) ⟨0, hk⟩) hf
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
  rcases mul_eq_zero.mp (show c * (c - 1) = 0 by linear_combination h) with hc | hc
  · left; rw [hc, zero_smul]
  · right; rw [sub_eq_zero.mp hc, one_smul]; rfl

/-! ## Strings are pairwise inequivalent -/

lemma trace_sY (p : ℕ) (n : ℤ) (k : ℕ) :
    LinearMap.trace K _ (sY p n k) = ∑ i : Fin k, wt p n i := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin k)), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, sY_single]
  simp

/-- `e_{n,k} ≅ e_{n',k'}` with `k ≥ 1` forces `(n, k) = (n', k')`. -/
theorem string_iso_imp [CharZero K] (p : ℕ) {n n' : ℤ} {k k' : ℕ} (hk : 0 < k)
    (h : IsoRep (sX k) (sY p n k) (sX (K := K) k') (sY p n' k')) : k = k' ∧ n = n' := by
  obtain ⟨e, -, hY⟩ := h
  obtain rfl : k = k' := by simpa only [Module.finrank_fin_fun] using e.finrank_eq
  refine ⟨rfl, ?_⟩
  have hconj : e.conj (sY p n k) = sY p n' k := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have := congrArg (fun g => g (e.symm w)) hY
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simpa only [LinearEquiv.coe_coe] using this
  have ht := LinearMap.trace_conj' (sY p n k) e
  rw [hconj, trace_sY, trace_sY] at ht
  simp only [wt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, add_left_inj] at ht
  exact_mod_cast (mul_left_cancel₀ (by exact_mod_cast hk.ne' : (k : K) ≠ 0) ht).symm

/-! ## The dual of a string -/

/-- The dual basis `ε`, reversed and signed: `B j = (-1)^j ε_{k-1-j}`. -/
noncomputable def dualStringBasis (k : ℕ) : Module.Basis (Fin k) K (Module.Dual K (Fin k → K)) :=
  (((Pi.basisFun K (Fin k)).dualBasis).reindex Fin.revPerm).unitsSMul
    fun j => (-1 : Kˣ) ^ (j : ℕ)

lemma dualStringBasis_apply {k : ℕ} (j : Fin k) (u : Fin k → K) :
    dualStringBasis k j u = (-1) ^ (j : ℕ) * u (Fin.rev j) := by
  simp [dualStringBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    Pi.basisFun_repr, Units.smul_def]

/-- **Page 194**: the dual `(-Xᵀ, -Yᵀ)` of `e_{n,k}` is `e_{-n-p(k-1),k}`. -/
theorem string_dual (p : ℕ) (n : ℤ) (k : ℕ) :
    IsoRep (sX k) (sY p (-n - p * ((k : ℤ) - 1)) k)
      (-(sX (K := K) k).dualMap) (-(sY p n k).dualMap) := by
  let e := (Pi.basisFun K (Fin k)).equiv (dualStringBasis k) (Equiv.refl _)
  have he : ∀ j, e (Pi.single j 1) = dualStringBasis k j := fun j => by
    rw [← Pi.basisFun_apply, Module.Basis.equiv_apply]; rfl
  refine ⟨e, (Pi.basisFun K (Fin k)).ext fun j => ?_, (Pi.basisFun K (Fin k)).ext fun j => ?_⟩
  · refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, sX_single, he,
      LinearMap.neg_apply, LinearMap.dualMap_apply, dualStringBasis_apply, sX_apply]
    have hr : ((Fin.rev j : Fin k) : ℕ) = k - (j + 1) := Fin.val_rev j
    split_ifs with h1 h2 h2
    · rw [he, dualStringBasis_apply]
      have : Fin.rev (⟨j + 1, h1⟩ : Fin k) = ⟨Fin.rev j - 1, by omega⟩ := by
        ext; simp only [Fin.val_rev]; omega
      rw [this, pow_succ]; ring
    · exfalso; omega
    · exfalso; omega
    · simp
  · refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, sY_single,
      map_smul, he, LinearMap.neg_apply, LinearMap.dualMap_apply, dualStringBasis_apply,
      sY_apply, LinearMap.smul_apply, smul_eq_mul, wt]
    have hr : ((Fin.rev j : Fin k) : ℕ) = k - (j + 1) := Fin.val_rev j
    rw [hr, Nat.cast_sub (by omega)]
    push_cast
    ring

/-! ## `ξ ⊗ e_{n,k}` -/

section Tensor

variable (p : ℕ) (n : ℤ) (m : ℕ)

/-- `X` on `ξ ⊗ e_{n,m+2}`: `X ⊗ 1 + 1 ⊗ X`. -/
noncomputable def tX : Module.End K ((Fin 2 → K) ⊗[K] (Fin (m + 2) → K)) :=
  TensorProduct.map (sX 2) LinearMap.id + TensorProduct.map LinearMap.id (sX (m + 2))

/-- `Y` on `ξ ⊗ e_{n,m+2}`, `ξ = e_{0,2}`. -/
noncomputable def tY : Module.End K ((Fin 2 → K) ⊗[K] (Fin (m + 2) → K)) :=
  TensorProduct.map (sY p 0 2) LinearMap.id + TensorProduct.map LinearMap.id (sY p n (m + 2))

variable {p n m}

lemma tX_tmul (x : Fin 2 → K) (y : Fin (m + 2) → K) :
    tX m (x ⊗ₜ y) = sX 2 x ⊗ₜ y + x ⊗ₜ sX (m + 2) y := by
  simp [tX, TensorProduct.map_tmul]

lemma tY_tmul (x : Fin 2 → K) (y : Fin (m + 2) → K) :
    tY p n m (x ⊗ₜ y) = sY p 0 2 x ⊗ₜ y + x ⊗ₜ sY p n (m + 2) y := by
  simp [tY, TensorProduct.map_tmul]

lemma tY_eigen {x : Fin 2 → K} {y : Fin (m + 2) → K} {c d : K} (hx : sY p 0 2 x = c • x)
    (hy : sY p n (m + 2) y = d • y) : tY p n m (x ⊗ₜ y) = (c + d) • (x ⊗ₜ y) := by
  rw [tY_tmul, hx, hy, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]

lemma tY_tX (u : (Fin 2 → K) ⊗[K] (Fin (m + 2) → K)) :
    tY p n m (tX m u) = tX m (tY p n m u) + (p : K) • tX m u := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [tX_tmul, tY_tmul, map_add, sY_sX, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
    abel
  | add u v hu hv =>
    simp only [map_add, hu, hv, smul_add]
    abel

lemma tY_tX_pow {u : (Fin 2 → K) ⊗[K] (Fin (m + 2) → K)} {c : K} (hu : tY p n m u = c • u)
    (j : ℕ) : tY p n m ((tX (K := K) m ^ j) u) = (c + p * j) • (tX (K := K) m ^ j) u := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, tY_tX, ih, map_smul]
    push_cast
    module

lemma tX_pow_tmul {x : Fin 2 → K} (hx : sX 2 (sX 2 x) = 0) (y : Fin (m + 2) → K) (c : ℕ) :
    (tX (K := K) m ^ c) (x ⊗ₜ y) =
      x ⊗ₜ (sX (m + 2) ^ c) y + (c : K) • (sX 2 x ⊗ₜ (sX (m + 2) ^ (c - 1)) y) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, tX_tmul, tX_tmul, hx,
      TensorProduct.zero_tmul, zero_add]
    rcases c with _ | c
    · simp [pow_succ']
      abel
    · simp only [Nat.add_sub_cancel, pow_succ', Module.End.mul_apply]
      push_cast
      module

/-- The basis vectors of `ξ`: `a = z₀` (weight `0`), `b = z₁` (weight `p`). -/
abbrev va : Fin 2 → K := Pi.single 0 1
abbrev vb : Fin 2 → K := Pi.single 1 1

lemma sX_va : sX (K := K) 2 va = vb := by
  rw [sX_single]; simp

lemma sX_vb : sX (K := K) 2 vb = 0 := by
  rw [sX_single]; simp

/-- `Z c = X^c z₀` in `e_{n,m+2}`. -/
noncomputable abbrev Z (c : ℕ) : Fin (m + 2) → K := (sX (m + 2) ^ c) (Pi.single 0 1)

lemma Z_eq_single {c : ℕ} (h : c < m + 2) : Z (K := K) (m := m) c = Pi.single ⟨c, h⟩ 1 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Z, pow_succ', Module.End.mul_apply, ← Z, ih (by omega), sX_single]
    simp [h]

lemma Z_eq_zero {c : ℕ} (h : m + 2 ≤ c) : Z (K := K) (m := m) c = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero =>
    change Z (K := K) (m := m) (m + 2) = 0
    rw [Z, pow_succ', Module.End.mul_apply, ← Z, Z_eq_single (by omega), sX_single]
    simp
  | succ d ih =>
    rw [Z, ← Nat.add_assoc, pow_succ', Module.End.mul_apply, ← Z, ih (by omega), map_zero]

lemma sX_pow_Z (i c : ℕ) : (sX (m + 2) ^ i) (Z (K := K) (m := m) c) = Z (i + c) := by
  rw [Z, Z, ← Module.End.mul_apply, ← pow_add]

/-- The two strings in `ξ ⊗ e_{n,m+2}`: `vⱼ = X^j (a ⊗ z₀)` (length `m + 3`) and
`wᵢ = X^i w₀`, `w₀ = a ⊗ z₁ - (m + 1) b ⊗ z₀` (length `m + 1`). -/
noncomputable def strings : Fin (m + 3) ⊕ Fin (m + 1) → (Fin 2 → K) ⊗[K] (Fin (m + 2) → K)
  | Sum.inl j => (tX (K := K) m ^ (j : ℕ)) (va ⊗ₜ Z 0)
  | Sum.inr i => (tX (K := K) m ^ (i : ℕ)) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0))

lemma tX_pow_va (c : ℕ) (y : Fin (m + 2) → K) :
    (tX (K := K) m ^ c) (va ⊗ₜ y) =
      va ⊗ₜ (sX (m + 2) ^ c) y + (c : K) • (vb ⊗ₜ (sX (m + 2) ^ (c - 1)) y) := by
  rw [tX_pow_tmul (by rw [sX_va, sX_vb]), sX_va]

lemma tX_pow_vb (c : ℕ) (y : Fin (m + 2) → K) :
    (tX (K := K) m ^ c) (vb ⊗ₜ y) = vb ⊗ₜ (sX (m + 2) ^ c) y := by
  rw [tX_pow_tmul (by rw [sX_vb, map_zero]), sX_vb, TensorProduct.zero_tmul, smul_zero, add_zero]

lemma strings_inl (c : ℕ) :
    (tX (K := K) m ^ c) (va ⊗ₜ Z 0) = va ⊗ₜ Z c + (c : K) • (vb ⊗ₜ Z (c - 1)) := by
  rw [tX_pow_va, sX_pow_Z, sX_pow_Z]
  simp only [Nat.add_zero]

lemma strings_inr (c : ℕ) :
    (tX (K := K) m ^ c) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) =
      va ⊗ₜ Z (c + 1) + ((c : K) - (m + 1)) • (vb ⊗ₜ Z c) := by
  rw [map_sub, map_smul, tX_pow_va, tX_pow_vb, sX_pow_Z, sX_pow_Z, sX_pow_Z]
  rcases c with _ | c
  · simp only [Nat.cast_zero, zero_smul, add_zero]
    module
  · simp only [Nat.add_sub_cancel, Nat.add_zero]
    module

lemma top_le_span (hk : ((m : K) + 2) ≠ 0) :
    ⊤ ≤ Submodule.span K (Set.range (strings (K := K) (m := m))) := by
  set S := Submodule.span K (Set.range (strings (K := K) (m := m)))
  have hl : ∀ (j : ℕ) (h : j < m + 3), (tX (K := K) m ^ j) (va ⊗ₜ Z 0) ∈ S := fun j h =>
    Submodule.subset_span ⟨Sum.inl ⟨j, h⟩, rfl⟩
  have hr : ∀ (i : ℕ) (h : i < m + 1),
      (tX (K := K) m ^ i) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) ∈ S := fun i h =>
    Submodule.subset_span ⟨Sum.inr ⟨i, h⟩, rfl⟩
  have hb : ∀ c : ℕ, vb ⊗ₜ Z (K := K) (m := m) c ∈ S := by
    intro c
    rcases lt_trichotomy c (m + 1) with hc | rfl | hc
    · have e : vb ⊗ₜ Z (K := K) (m := m) c =
          ((m : K) + 2)⁻¹ • ((tX (K := K) m ^ (c + 1)) (va ⊗ₜ Z 0) -
            (tX (K := K) m ^ c) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0))) := by
        rw [strings_inl, strings_inr, Nat.add_sub_cancel,
          show (va ⊗ₜ Z (c + 1) + ((c + 1 : ℕ) : K) • (vb ⊗ₜ Z c) -
            (va ⊗ₜ Z (c + 1) + ((c : K) - (m + 1)) • (vb ⊗ₜ Z c)) : _) =
            ((m : K) + 2) • (vb ⊗ₜ Z (K := K) (m := m) c) by push_cast; module,
          smul_smul, inv_mul_cancel₀ hk, one_smul]
      rw [e]
      exact S.smul_mem _ (S.sub_mem (hl _ (by omega)) (hr _ hc))
    · have e : vb ⊗ₜ Z (K := K) (m := m) (m + 1) =
          ((m : K) + 2)⁻¹ • (tX (K := K) m ^ (m + 2)) (va ⊗ₜ Z 0) := by
        rw [strings_inl, Z_eq_zero le_rfl, TensorProduct.tmul_zero, zero_add, smul_smul,
          show m + 2 - 1 = m + 1 by omega]
        push_cast
        rw [inv_mul_cancel₀ hk, one_smul]
      rw [e]
      exact S.smul_mem _ (hl _ (by omega))
    · rw [Z_eq_zero (by omega), TensorProduct.tmul_zero]
      exact S.zero_mem
  have ha : ∀ c : ℕ, va ⊗ₜ Z (K := K) (m := m) c ∈ S := by
    intro c
    by_cases hc : c < m + 3
    · have e : va ⊗ₜ Z (K := K) (m := m) c =
          (tX (K := K) m ^ c) (va ⊗ₜ Z 0) - (c : K) • (vb ⊗ₜ Z (c - 1)) := by
        rw [strings_inl]; abel
      rw [e]
      exact S.sub_mem (hl c hc) (S.smul_mem _ (hb _))
    · rw [Z_eq_zero (by omega), TensorProduct.tmul_zero]
      exact S.zero_mem
  rw [← (Module.Basis.tensorProduct (Pi.basisFun K (Fin 2))
    (Pi.basisFun K (Fin (m + 2)))).span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, c⟩, rfl⟩
  rw [Module.Basis.tensorProduct_apply, Pi.basisFun_apply, Pi.basisFun_apply,
    ← Z_eq_single c.2]
  fin_cases i
  exacts [ha c, hb c]

variable (n p) in
/-- **Page 197, the leading term**: `ξ ⊗ e_{n,k} ≅ e_{n,k+1} ⊕ e_{n+p,k-1}` for `k = m + 2`,
whenever `k` is invertible in `K`. -/
theorem xi_tensor_string (hk : ((m : K) + 2) ≠ 0) :
    IsoRep (LinearMap.prodMap (sX (m + 3)) (sX (m + 1)))
      (LinearMap.prodMap (sY p n (m + 3)) (sY p (n + p) (m + 1)))
      (tX (K := K) m) (tY p n m) := by
  have hli : LinearIndependent K (strings (K := K) (m := m)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span hk) (by
      rw [Module.finrank_tensorProduct, Module.finrank_fin_fun, Module.finrank_fin_fun,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      ring)
  let B := Module.Basis.mk hli (top_le_span hk)
  let src := (Pi.basisFun K (Fin (m + 3))).prod (Pi.basisFun K (Fin (m + 1)))
  let e := src.equiv B (Equiv.refl _)
  have he : ∀ i, e (src i) = strings i := fun i => by
    rw [Module.Basis.equiv_apply]; exact Module.Basis.mk_apply _ _ _
  have hsrc_l : ∀ j, src (Sum.inl j) = (Pi.single j 1, 0) := fun j => by simp [src]
  have hsrc_r : ∀ i, src (Sum.inr i) = (0, Pi.single i 1) := fun i => by simp [src]
  have ea : sY p 0 2 (va (K := K)) = (0 : K) • va := by rw [sY_single]; simp [wt]
  have eb : sY p 0 2 (vb (K := K)) = (p : K) • vb := by rw [sY_single]; simp [wt]
  have e0 : sY p n (m + 2) (Z (K := K) (m := m) 0) = (n : K) • Z 0 := by
    rw [Z_eq_single (by omega), sY_single]; simp [wt]
  have e1 : sY p n (m + 2) (Z (K := K) (m := m) 1) = ((n : K) + p) • Z 1 := by
    rw [Z_eq_single (by omega), sY_single]; simp [wt]
  have hwt0 : tY (K := K) p n m (va ⊗ₜ Z 0) = (n : K) • (va ⊗ₜ Z (K := K) (m := m) 0) := by
    rw [tY_eigen ea e0, zero_add]
  have hwt1 : tY (K := K) p n m (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) =
      ((n : K) + p) • (va ⊗ₜ Z (K := K) (m := m) 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) := by
    rw [map_sub, map_smul, tY_eigen ea e1, tY_eigen eb e0]
    module
  refine ⟨e, src.ext fun i => ?_, src.ext fun i => ?_⟩
  · rcases i with j | i
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_l,
        LinearMap.prodMap_apply, map_zero, sX_single]
      split_ifs with h
      · rw [← hsrc_l, he]
        simp only [strings]
        rw [pow_succ', Module.End.mul_apply]
      · rw [show ((0 : Fin (m + 3) → K), (0 : Fin (m + 1) → K)) = 0 from rfl, map_zero]
        simp only [strings]
        rw [← Module.End.mul_apply, ← pow_succ', strings_inl, Z_eq_zero (by omega),
          Z_eq_zero (by omega), TensorProduct.tmul_zero, TensorProduct.tmul_zero, smul_zero,
          add_zero]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_r,
        LinearMap.prodMap_apply, map_zero, sX_single]
      split_ifs with h
      · rw [← hsrc_r, he]
        simp only [strings]
        rw [pow_succ', Module.End.mul_apply]
      · rw [show ((0 : Fin (m + 3) → K), (0 : Fin (m + 1) → K)) = 0 from rfl, map_zero]
        simp only [strings]
        have hi : (i : ℕ) = m := by omega
        rw [← Module.End.mul_apply, ← pow_succ', strings_inr, hi, Z_eq_zero le_rfl,
          TensorProduct.tmul_zero, zero_add]
        rw [show ((m + 1 : ℕ) : K) - (m + 1) = 0 by push_cast; ring, zero_smul]
  · rcases i with j | i
    · have hs : ((wt p n j : K) • Pi.single j (1 : K), (0 : Fin (m + 1) → K)) =
          (wt p n j : K) • src (Sum.inl j) := by rw [hsrc_l, Prod.smul_mk, smul_zero]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_l,
        LinearMap.prodMap_apply, map_zero, sY_single, hs, map_smul, he]
      simp only [strings]
      rw [tY_tX_pow hwt0]
      rfl
    · have hs : ((0 : Fin (m + 3) → K), (wt p (n + p) i : K) • Pi.single i (1 : K)) =
          (wt p (n + p) i : K) • src (Sum.inr i) := by rw [hsrc_r, Prod.smul_mk, smul_zero]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_r,
        LinearMap.prodMap_apply, map_zero, sY_single, hs, map_smul, he]
      simp only [strings]
      rw [tY_tX_pow hwt1]
      simp [wt]

end Tensor

end Grothendieck.Folder10

/-!
# Folder 10, page 65: `H²` of a norm-one torus (finding `10-numerical-character-rank-one-torus`)

Exemple 1 of page 65: `G` a one-dimensional torus split by a quadratic `Z/k`, the exact
sequence `0 → G → Z^* → 𝔾_m → 0` (`Z^* = R_{Z/k} 𝔾_m`, the norm on the right), and « par
Hilbert 90 » the kernel of `H²(k, G) → H²(k, Z^*) = Br(Z)` is zero. Formalised at a finite
Galois level `L ⊇ Z`, with `Γ = Gal(L/K)` and `χ : Γ → {±1}` the sign of `Z`:
`M` any `Γ`-module, `G = M` twisted by `χ` (`twistRep`), `Z^* = M × M` with `Γ` swapping the
factors outside `Ker χ` (`indRep`), `x ↦ (x, -x)` and `(x, y) ↦ x + y` (`torusSeq`, short exact).

* `torus_H2_injective`: `H¹(Γ, M) = 0 ⟹ H²(Γ, G) → H²(Γ, Z^*)` injective (long exact sequence).
* `norm_one_torus_H2_injective`: for `M = Lˣ`, by mathlib's Hilbert 90.
* `indShapiro`, `norm_one_torus_H2_injective_quadratic`: `H²(Γ, Z^*) ≅ H²(Gal(L/Z), Lˣ)`, and
  the composite is injective, `Z` a quadratic subextension, `quadChar` its sign.

Not formalised: the limit over `L` (Galois cohomology of `k`), the identification of
`H²(Gal(L/Z), Lˣ)` with `Br(L/Z)`, and the tannakian statement the page draws from it.
-/

namespace Grothendieck.Folder10.NormOneTorus

open CategoryTheory groupCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (χ : Γ →* ℤˣ) (M : Rep.{0} k Γ)

/-- `M` twisted by the sign `χ`: `g ⋆ x = χ(g) · g x`. For `M = Lˣ` this is the norm-one torus
`G = Ker(N : R_{Z/k} 𝔾_m → 𝔾_m)` on `L`-points, `g ⋆ x = g(x)^{χ g}`. -/
def twistRep : Representation k Γ M.V where
  toFun g := (χ g : ℤ) • M.ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

/-- The identity of `M × M` when `χ g = 1`, the swap of the two factors otherwise. -/
def swapLin (g : Γ) : M.V × M.V →ₗ[k] M.V × M.V :=
  if χ g = 1 then LinearMap.id else (LinearMap.snd k M.V M.V).prod (LinearMap.fst k M.V M.V)

lemma swapLin_apply (g : Γ) (v : M.V × M.V) :
    swapLin χ M g v = if χ g = 1 then v else (v.2, v.1) := by
  unfold swapLin; split_ifs <;> rfl

/-- `M × M` with `g · (x, y) = (g x, g y)` if `χ g = 1` and `(g y, g x)` otherwise: for
`M = Lˣ` and `χ` the sign of a quadratic `Z ⊆ L`, this is `(Z ⊗_k L)ˣ`, the `L`-points of
`R_{Z/k} 𝔾_m`, written in the basis of the two idempotents. -/
def indRep : Representation k Γ (M.V × M.V) where
  toFun g := ((M.ρ g).prodMap (M.ρ g)) ∘ₗ swapLin χ M g
  map_one' := by
    ext v <;> simp [swapLin_apply]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, swapLin_apply, map_mul, Module.End.mul_apply]
    rcases Int.units_eq_one_or (χ g) with hg | hg <;>
      rcases Int.units_eq_one_or (χ h) with hh | hh <;> simp [hg, hh]

lemma indRep_apply (g : Γ) (v : M.V × M.V) :
    indRep χ M g v = if χ g = 1 then (M.ρ g v.1, M.ρ g v.2) else (M.ρ g v.2, M.ρ g v.1) := by
  change (M.ρ g).prodMap (M.ρ g) (swapLin χ M g v) = _
  rw [swapLin_apply]; split_ifs <;> rfl

lemma twistRep_apply (g : Γ) (v : M.V) : twistRep χ M g v = (χ g : ℤ) • M.ρ g v := rfl

/-- `x ↦ (x, -x)`. -/
def torusIncl : (twistRep χ M).IntertwiningMap (indRep χ M) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (twistRep χ M) (indRep χ M)
    (LinearMap.id.prod (-LinearMap.id))
    fun g v => by
      rw [indRep_apply, twistRep_apply]
      rcases Int.units_eq_one_or (χ g) with hg | hg <;> simp [hg]

/-- `(x, y) ↦ x + y`. -/
def normMap : (indRep χ M).IntertwiningMap M.ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (indRep χ M) M.ρ
    (LinearMap.coprod LinearMap.id LinearMap.id)
    fun g v => by
      rw [indRep_apply]
      split_ifs <;> simp [add_comm]

lemma torusIncl_apply (v : M.V) : torusIncl χ M v = (v, -v) := rfl
lemma normMap_apply (v : M.V × M.V) : normMap χ M v = v.1 + v.2 := rfl

/-- `0 → G → Z^* → 𝔾_m → 0` of page 65, at the level of `Γ`-modules. -/
def torusSeq : ShortComplex (Rep.{0} k Γ) where
  X₁ := Rep.of (twistRep χ M)
  X₂ := Rep.of (indRep χ M)
  X₃ := M
  f := Rep.ofHom (torusIncl χ M)
  g := Rep.ofHom (normMap χ M)
  zero := by
    ext v
    simp [torusIncl_apply, normMap_apply]

lemma torusSeq_shortExact : (torusSeq χ M).ShortExact where
  exact := (forget₂ (Rep.{0} k Γ) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      obtain ⟨a, b⟩ := x
      refine ⟨a, ?_⟩
      change torusIncl χ M a = (a, b)
      rw [torusIncl_apply, ← eq_neg_of_add_eq_zero_right (show a + b = 0 from hx)]
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => congrArg Prod.fst h
  epi_g := (Rep.epi_iff_surjective _).2 fun x => ⟨((x, 0) : M.V × M.V), by
    change normMap χ M (x, 0) = x
    rw [normMap_apply, add_zero]⟩

/-- The long exact sequence: if `Hⁿ(G, X₃) = 0` then `Hⁿ⁺¹(G, X₁) → Hⁿ⁺¹(G, X₂)` is
injective. -/
theorem map_succ_injective {G : Type} [Group G]
    {X : ShortComplex (Rep.{0} k G)} (hX : X.ShortExact) (n : ℕ)
    (h : Subsingleton (groupCohomology X.X₃ n)) :
    Function.Injective (map (MonoidHom.id G) X.f (n + 1)).hom := by
  have : Subsingleton (mapShortComplex₁ hX (i := n) (j := n + 1) rfl).X₁ := h
  exact (ModuleCat.mono_iff_injective _).1
    ((mapShortComplex₁_exact hX (i := n) (j := n + 1) rfl).mono_g
      ((ModuleCat.isZero_of_subsingleton _).eq_of_src _ _))

/-- Page 65, abstractly: `H²(Γ, G) → H²(Γ, Z^*)` is injective as soon as `H¹(Γ, M) = 0`. -/
theorem torus_H2_injective (h : Subsingleton (groupCohomology M 1)) :
    Function.Injective (map (MonoidHom.id Γ) (A := Rep.of (twistRep χ M)) (torusSeq χ M).f 2).hom :=
  map_succ_injective (torusSeq_shortExact χ M) 1 h

section Shapiro

/-- `v ↦ (h ↦ ρ(h) v₁ if χ h = 1, ρ(h) v₂ otherwise)`. -/
def toCoindFun : M.V × M.V →ₗ[k] (Γ → M.V) :=
  LinearMap.pi fun h =>
    if χ h = 1 then M.ρ h ∘ₗ LinearMap.fst k M.V M.V else M.ρ h ∘ₗ LinearMap.snd k M.V M.V

lemma toCoindFun_apply (v : M.V × M.V) (h : Γ) :
    toCoindFun χ M v h = if χ h = 1 then M.ρ h v.1 else M.ρ h v.2 := by
  simp only [toCoindFun, LinearMap.pi_apply]
  split_ifs <;> rfl

lemma toCoindFun_mem (v : M.V × M.V) :
    toCoindFun χ M v ∈ Representation.coindV χ.ker.subtype (Rep.res χ.ker.subtype M).ρ := by
  intro s h
  have hs : χ s = 1 := s.2
  simp only [toCoindFun_apply, Subgroup.subtype_apply, map_mul, hs, one_mul, Module.End.mul_apply]
  split_ifs <;> rfl

noncomputable def toCoind :
    (indRep χ M).IntertwiningMap (Rep.coind χ.ker.subtype (Rep.res χ.ker.subtype M)).ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((toCoindFun χ M).codRestrict _ (toCoindFun_mem χ M))
    fun g v => by
      ext h
      change toCoindFun χ M (indRep χ M g v) h = toCoindFun χ M v (h * g)
      simp only [toCoindFun_apply, indRep_apply, map_mul, Module.End.mul_apply]
      rcases Int.units_eq_one_or (χ g) with hg | hg <;>
        rcases Int.units_eq_one_or (χ h) with hh | hh <;> simp [hg, hh]

lemma toCoind_apply (v : M.V × M.V) (h : Γ) : (toCoind χ M v).1 h = toCoindFun χ M v h := rfl

lemma rho_inv_apply (g : Γ) (x : M.V) : M.ρ g⁻¹ (M.ρ g x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

lemma toCoind_bijective {τ : Γ} (hτ : χ τ ≠ 1) : Function.Bijective (toCoind χ M) := by
  have hτ' : χ τ = -1 := (Int.units_eq_one_or _).resolve_left hτ
  constructor
  · intro a b hab
    have h1 : toCoindFun χ M a 1 = toCoindFun χ M b 1 := congrArg (fun f => f.1 1) hab
    have h2 : toCoindFun χ M a τ = toCoindFun χ M b τ := congrArg (fun f => f.1 τ) hab
    simp only [toCoindFun_apply, map_one, Module.End.one_apply, ite_true] at h1
    simp only [toCoindFun_apply, hτ, ite_false] at h2
    exact Prod.ext h1 (by simpa only [rho_inv_apply] using congrArg (M.ρ τ⁻¹) h2)
  · intro f
    refine ⟨(f.1 1, M.ρ τ⁻¹ (f.1 τ)), Subtype.ext (funext fun h => ?_)⟩
    change toCoindFun χ M _ h = f.1 h
    rw [toCoindFun_apply]
    split_ifs with hh
    · have := f.2 ⟨h, hh⟩ 1
      simp only [Subgroup.subtype_apply, mul_one] at this
      rw [this]; rfl
    · have hm : χ (h * τ⁻¹) = 1 := by
        rw [map_mul, map_inv, hτ', (Int.units_eq_one_or _).resolve_left hh]; rfl
      have := f.2 ⟨h * τ⁻¹, hm⟩ τ
      simp only [Subgroup.subtype_apply, inv_mul_cancel_right] at this
      rw [this]
      change M.ρ h (M.ρ τ⁻¹ (f.1 τ)) = M.ρ (h * τ⁻¹) (f.1 τ)
      rw [map_mul, Module.End.mul_apply]

/-- Shapiro (`coindIso`): when `χ` is non-trivial, `H^n(Γ, Ind) ≅ H^n(Ker χ, M)`. -/
noncomputable def indShapiro {τ : Γ} (hτ : χ τ ≠ 1) (n : ℕ) :
    groupCohomology (Rep.of (indRep χ M)) n ≅ groupCohomology (Rep.res χ.ker.subtype M) n :=
  have : IsIso (Rep.ofHom (toCoind χ M)) := by
    have hb := toCoind_bijective χ M hτ
    have : Mono (Rep.ofHom (toCoind χ M)) := (Rep.mono_iff_injective _).2 hb.1
    have : Epi (Rep.ofHom (toCoind χ M)) := (Rep.epi_iff_surjective _).2 hb.2
    exact isIso_of_mono_of_epi _
  (functor k Γ n).mapIso (asIso (Rep.ofHom (toCoind χ M))) ≪≫ coindIso _ n

/-- The composite `H²(Γ, T) → H²(Γ, Ind) ≅ H²(Ker χ, M)` is injective when `H¹(Γ, M) = 0`. -/
theorem torus_H2_injective_res {τ : Γ} (hτ : χ τ ≠ 1) (h : Subsingleton (groupCohomology M 1)) :
    Function.Injective
      ((map (MonoidHom.id Γ) (A := Rep.of (twistRep χ M)) (torusSeq χ M).f 2) ≫
        (indShapiro χ M hτ 2).hom).hom := by
  have hi : Function.Injective (indShapiro χ M hτ 2).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact fun a b hab => torus_H2_injective χ M h (hi hab)

end Shapiro

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Page 65, Exemple 1, at a finite level: by Hilbert 90 (`H1ofAutOnUnitsUnique`),
`H²(Gal(L/K), G(L)) → H²(Gal(L/K), (Z ⊗_K L)ˣ)` is injective, for every sign `χ`. -/
theorem norm_one_torus_H2_injective (χ : Gal(L/K) →* ℤˣ) :
    Function.Injective
      (map (MonoidHom.id _) (A := Rep.of (twistRep χ (Rep.ofAlgebraAutOnUnits K L)))
        (torusSeq χ (Rep.ofAlgebraAutOnUnits K L)).f 2).hom :=
  torus_H2_injective χ _ inferInstance

omit [FiniteDimensional K L] in
open Additive in
/-- On `Lˣ` the twisted action is `γ ⋆ x = γ(x)^{χ γ}`. -/
lemma twist_units_apply (χ : Gal(L/K) →* ℤˣ) (γ : Gal(L/K)) (x : Lˣ) :
    toMul (twistRep χ (Rep.ofAlgebraAutOnUnits K L) γ (ofMul x)) = (γ • x) ^ (χ γ : ℤ) := rfl

/-- The sign character of a quadratic subextension. -/
noncomputable def quadChar [IsGalois K L] (Z : IntermediateField K L)
    [Algebra.IsQuadraticExtension K Z] : Gal(L/K) →* ℤˣ :=
  have : Algebra.IsSeparable K Z := Algebra.isSeparable_tower_bot_of_isSeparable K Z L
  have hZ : Nat.card Gal(Z/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (mulEquivOfPrimeCardEq hZ (by rw [Nat.card_eq_fintype_card]; rfl)).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom Z)

lemma quadChar_eq_one_iff [IsGalois K L] (Z : IntermediateField K L)
    [Algebra.IsQuadraticExtension K Z] (γ : Gal(L/K)) :
    quadChar K L Z γ = 1 ↔ ∀ z ∈ Z, γ z = z := by
  unfold quadChar
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    IntermediateField.mem_fixingSubgroup_iff]

lemma exists_quadChar_ne_one [IsGalois K L] (Z : IntermediateField K L)
    [Algebra.IsQuadraticExtension K Z] : ∃ τ, quadChar K L Z τ ≠ 1 := by
  by_contra! h
  have hle : Z ≤ ⊥ := fun z hz => by
    rw [← IsGalois.fixedField_top (F := K) (E := L)]
    exact fun γ => (quadChar_eq_one_iff K L Z γ.1).1 (h γ.1) z hz
  have := IntermediateField.finrank_eq_one_iff.2 (le_antisymm hle bot_le)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at this
  exact absurd this (by norm_num)

omit [FiniteDimensional K L] in
open Additive in
/-- On `Lˣ` the inclusion of the torus is `x ↦ (x, x⁻¹)`. -/
lemma torusIncl_units (χ : Gal(L/K) →* ℤˣ) (x : Lˣ) :
    torusIncl χ (Rep.ofAlgebraAutOnUnits K L) (ofMul x) = (ofMul x, ofMul x⁻¹) := rfl

omit [FiniteDimensional K L] in
open Additive in
/-- On `Lˣ` the map to `𝔾_m` is `(x, y) ↦ x y`, the norm. -/
lemma normMap_units (χ : Gal(L/K) →* ℤˣ) (x y : Lˣ) :
    normMap χ (Rep.ofAlgebraAutOnUnits K L) (ofMul x, ofMul y) = ofMul (x * y) := rfl

/-- Page 65, Exemple 1, for a quadratic `Z ⊆ L` with `L/K` finite Galois: the composite
`H²(Gal(L/K), G(L)) → H²(Gal(L/K), (Z ⊗_K L)ˣ) ≅ H²(Gal(L/Z), Lˣ)` (Shapiro) is injective;
`H²(Gal(L/Z), Lˣ)` is the relative Brauer group `Br(L/Z)`. -/
theorem norm_one_torus_H2_injective_quadratic [IsGalois K L] (Z : IntermediateField K L)
    [Algebra.IsQuadraticExtension K Z] :
    Function.Injective
      ((map (MonoidHom.id _) (A := Rep.of (twistRep (quadChar K L Z) (Rep.ofAlgebraAutOnUnits K L)))
        (torusSeq (quadChar K L Z) (Rep.ofAlgebraAutOnUnits K L)).f 2) ≫
        (indShapiro (quadChar K L Z) (Rep.ofAlgebraAutOnUnits K L)
          (exists_quadChar_ne_one K L Z).choose_spec 2).hom).hom :=
  torus_H2_injective_res _ _ _ inferInstance


end Grothendieck.Folder10.NormOneTorus

namespace Grothendieck.Folder10

variable {K : Type*} [Field K]

/-! ## Every indecomposable is a string (Lemmes 1 and 2, pp. 192–194)

A finite-dimensional representation `(V, X, Y)` with `[Y, X] = p X` on which `Y` is
diagonalisable with integer weights — the restriction to `𝔾_m` of a rational representation
of `G`, semisimple by case II — and which is indecomposable (its only idempotent
endomorphisms are `0` and `1`) is a string `e_{n,k}`. The proof does not follow the chain
`E₀ → E₁ → ⋯` of the page: with `X^{k+1} = 0 ≠ X^k`, take a weight vector `v` with
`X^k v ≠ 0` and a weight functional `ψ` (`ψ ∘ Y = μ ψ`, `μ` the weight of `X^k v`) with
`ψ(X^k v) = 1`; then `ψ(X^a v) = δ_{a,k}` by weights, and
`x ↦ Σ_l ψ(X^{k-l} x) X^l v` is an idempotent endomorphism of the representation, nonzero, so
the identity, and the `X^l v` form a string. Over a field of characteristic `0` with `p ≥ 1`;
the semisimplicity of `Y` cannot be dropped (`X = 0`, `Y` a Jordan block).
-/

section Classification

variable {V : Type*} [AddCommGroup V] [Module K V] {p : ℕ} {X Y : Module.End K V}

/-- `Y X^a = X^a Y + a p X^a`, from `[Y, X] = p X`. -/
lemma Y_X_pow (hR : ∀ u, Y (X u) = X (Y u) + (p : K) • X u) (a : ℕ) (u : V) :
    Y ((X ^ a) u) = (X ^ a) (Y u) + ((a : K) * p) • (X ^ a) u := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, hR, ih, map_add, map_smul, Module.End.mul_apply]
    push_cast
    module

/-- **Lemmes 1–2, p. 194**: an indecomposable representation with `[Y, X] = p X` and a basis
of eigenvectors of `Y` with integer weights is a string `e_{n,k}`, `k ≥ 1`. -/
theorem indecomposable_is_string [CharZero K] [FiniteDimensional K V] [Nontrivial V]
    (hp : p ≠ 0) (hR : ∀ u, Y (X u) = X (Y u) + (p : K) • X u)
    {ι : Type*} (b : Module.Basis ι K V) (w : ι → ℤ) (hb : ∀ i, Y (b i) = (w i : K) • b i)
    (hind : ∀ f : Module.End K V, f ∘ₗ X = X ∘ₗ f → f ∘ₗ Y = Y ∘ₗ f → f * f = f →
      f = 0 ∨ f = 1) :
    ∃ n : ℤ, ∃ k, 0 < k ∧ IsoRep (sX k) (sY p n k) X Y := by
  classical
  have hc : ∀ i u, b.coord i (Y u) = w i * b.coord i u := fun i u => by
    have : b.coord i ∘ₗ Y = (w i : K) • b.coord i := b.ext fun j => by
      simp only [LinearMap.comp_apply, hb, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self, smul_eq_mul]
      rcases eq_or_ne j i with rfl | h <;> simp [*]
    exact congrArg (· u) this
  have heig : ∀ {u : V} {c : K}, Y u = c • u → u ≠ 0 → ∃ i, (w i : K) = c ∧ b.coord i u ≠ 0 := by
    intro u c hu hu0
    obtain ⟨i, hi⟩ : ∃ i, b.repr u i ≠ 0 := by
      by_contra! h
      exact hu0 (b.repr.injective (Finsupp.ext fun i => by simp [h]))
    refine ⟨i, mul_right_cancel₀ hi ?_, hi⟩
    simpa [hu] using (hc i u).symm
  have hXa : ∀ (a : ℕ) j, Y ((X ^ a) (b j)) = ((w j : K) + a * p) • (X ^ a) (b j) := fun a j => by
    rw [Y_X_pow hR, hb, map_smul, add_smul]
  have hN : ∃ N, X ^ N = 0 := by
    have := Module.Finite.finite_basis b
    cases nonempty_fintype ι
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, (w i).natAbs ≤ M :=
      ⟨_, fun i => Finset.single_le_sum (f := fun i => (w i).natAbs) (by simp) (Finset.mem_univ i)⟩
    refine ⟨2 * M + 1, b.ext fun j => ?_⟩
    by_contra h
    obtain ⟨i, hi, -⟩ := heig (hXa _ j) h
    have h3 : w i = w j + ((2 * M + 1 : ℕ) : ℤ) * p :=
      Int.cast_injective (α := K) (by push_cast at hi ⊢; exact hi)
    have h4 : ((2 * M + 1 : ℕ) : ℤ) ≤ ((2 * M + 1 : ℕ) : ℤ) * p :=
      le_mul_of_one_le_right (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)
    have := hM i
    have := hM j
    omega
  obtain ⟨k, hk, hk1⟩ : ∃ k, X ^ (k + 1) = 0 ∧ X ^ k ≠ 0 := by
    have hm : Nat.find hN ≠ 0 := fun h => one_ne_zero (h ▸ Nat.find_spec hN : X ^ 0 = 0)
    exact ⟨Nat.find hN - 1, by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm)]; exact Nat.find_spec hN,
      Nat.find_min hN (by omega)⟩
  obtain ⟨j, hj⟩ : ∃ j, (X ^ k) (b j) ≠ 0 := by
    by_contra! h
    exact hk1 (b.ext fun j => by simpa using h j)
  obtain ⟨i, hi, hci⟩ := heig (hXa k j) hj
  let ψ := (b.coord i ((X ^ k) (b j)))⁻¹ • b.coord i
  have hψY : ∀ u, ψ (Y u) = w i * ψ u := fun u => by simp [ψ, hc]; ring
  have hψv : ∀ a : ℕ, ψ ((X ^ a) (b j)) = if a = k then 1 else 0 := by
    intro a
    split_ifs with ha
    · subst ha; simpa [ψ] using inv_mul_cancel₀ hci
    · have h1 := hψY ((X ^ a) (b j))
      rw [hXa, map_smul, smul_eq_mul, hi] at h1
      have h2 : ((a : K) - k) * p ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast ha)) (by exact_mod_cast hp)
      exact (mul_eq_zero.mp (by linear_combination h1 :
        ((a : K) - k) * p * ψ ((X ^ a) (b j)) = 0)).resolve_left h2
  have hψX : ∀ (a : ℕ) u, ψ ((X ^ a) (Y u)) = ((w j : K) + (k - a) * p) * ψ ((X ^ a) u) := by
    intro a u
    rw [← sub_eq_of_eq_add (Y_X_pow hR a u), map_sub, hψY, map_smul, hi, smul_eq_mul]
    ring
  let e : (Fin (k + 1) → K) →ₗ[K] V :=
    ∑ l : Fin (k + 1), (LinearMap.proj l).smulRight ((X ^ (l : ℕ)) (b j))
  let g : V →ₗ[K] (Fin (k + 1) → K) := LinearMap.pi fun l : Fin (k + 1) => ψ ∘ₗ X ^ (k - l)
  have he : ∀ l, e (Pi.single l 1) = (X ^ (l : ℕ)) (b j) := by intro l; simp [e, Pi.single_apply]
  have hge : g ∘ₗ e = LinearMap.id := by
    refine (Pi.basisFun K _).ext fun l => funext fun l' => ?_
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, he, g, LinearMap.pi_apply,
      ← Module.End.mul_apply, ← pow_add, hψv, LinearMap.id_apply, Pi.single_apply, Fin.ext_iff]
    have := l.2
    have := l'.2
    split_ifs <;> first | rfl | omega
  have heX : e ∘ₗ sX (k + 1) = X ∘ₗ e := (Pi.basisFun K _).ext fun l => by
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, sX_single, he]
    split_ifs with h
    · rw [he, pow_succ', Module.End.mul_apply]
    · rw [map_zero, ← Module.End.mul_apply, ← pow_succ', show (l : ℕ) + 1 = k + 1 by omega, hk,
        LinearMap.zero_apply]
  have heY : e ∘ₗ sY p (w j) (k + 1) = Y ∘ₗ e := (Pi.basisFun K _).ext fun l => by
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, sY_single, map_smul, he, hXa, wt]
    rw [mul_comm]
  have hgX : g ∘ₗ X = sX (k + 1) ∘ₗ g := LinearMap.ext fun u => funext fun l => by
    simp only [LinearMap.comp_apply, g, LinearMap.pi_apply, sX_apply, ← Module.End.mul_apply,
      ← pow_succ]
    split_ifs with h
    · rw [show k - l + 1 = k - (l - 1) by omega]
    · rw [show k - l + 1 = k + 1 by omega, hk]; simp
  have hgY : g ∘ₗ Y = sY p (w j) (k + 1) ∘ₗ g := LinearMap.ext fun u => funext fun l => by
    simp only [LinearMap.comp_apply, g, LinearMap.pi_apply, sY_apply, hψX, wt]
    rw [Nat.cast_sub (by omega : (l : ℕ) ≤ k)]
    ring
  obtain h | h := hind (e ∘ₗ g)
    (by rw [LinearMap.comp_assoc, hgX, ← LinearMap.comp_assoc, heX, LinearMap.comp_assoc])
    (by rw [LinearMap.comp_assoc, hgY, ← LinearMap.comp_assoc, heY, LinearMap.comp_assoc])
    (by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ← LinearMap.comp_assoc g, hge,
      LinearMap.id_comp])
  · have := congrArg (fun f => (g ∘ₗ f) (b j) 0) h
    rw [← LinearMap.comp_assoc, hge] at this
    simp [g, hψv] at this
  · exact ⟨w j, k + 1, k.succ_pos, LinearEquiv.ofLinearMap e g h hge, heX, heY⟩

/-- The same, with `Y` diagonalisable with integer eigenvalues: `V = ⨁_{n ∈ ℤ} ker (Y - n)`. -/
theorem indecomposable_is_string' [CharZero K] [FiniteDimensional K V] [Nontrivial V]
    (hp : p ≠ 0) (hR : ∀ u, Y (X u) = X (Y u) + (p : K) • X u)
    (hY : ⨆ n : ℤ, Y.eigenspace (n : K) = ⊤)
    (hind : ∀ f : Module.End K V, f ∘ₗ X = X ∘ₗ f → f ∘ₗ Y = Y ∘ₗ f → f * f = f →
      f = 0 ∨ f = 1) :
    ∃ n : ℤ, ∃ k, 0 < k ∧ IsoRep (sX k) (sY p n k) X Y := by
  have h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((Module.End.eigenspaces_iSupIndep Y).comp Int.cast_injective) hY
  exact indecomposable_is_string hp hR (h.collectedBasis fun n => Module.Free.chooseBasis K _)
    Sigma.fst
    (fun a => Module.End.mem_eigenspace_iff.mp (h.collectedBasis_mem _ a)) hind

end Classification

end Grothendieck.Folder10
