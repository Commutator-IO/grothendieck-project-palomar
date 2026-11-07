module

public import Mathlib
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.FiveLemma

@[expose] public section


/-!
# Folder 22, Lemme 3.3, Corollaires 3.4, 3.5, and the obstruction of pp. 22, 24

The modernised reading `transcripts/22/22.modern.tex` (typescript page 10, his
page 25) states:

> **Lemme 3.3.** Soient `A` un anneau, `(P_i)_{i ∈ I}` une famille de
> `A`-modules, `P = ∏ P_i` leur produit, et `M` un `A`-module de présentation
> finie. Alors l'homomorphisme canonique `M ⊗_A P → ∏_i (M ⊗_A P_i)` est un
> isomorphisme.
>
> **Corollaire 3.4.** Supposons que tout `A`-module de type fini soit de
> présentation finie — par exemple `A` noethérien. Alors tout produit de
> `A`-modules plats est plat.
>
> **Corollaire 3.5.** Supposons `A` comme en 3.4, par exemple noethérien. Soit
> `P` un `A`-module isomorphe à la limite projective d'un système projectif
> *strict*, admettant un système cofinal dénombrable, de `A`-modules projectifs.
> Alors `P` est un `A`-module plat.

The rest of the folder — formal smoothness of topological algebras (3.2, 3.6),
Cohen algebras (3.7–3.12), the regular-homomorphism criterion 3.13 — needs preadic
topologies and geometric regularity, which mathlib does not have; it is not
formalised here. The discrete-topology half of the obstruction of pages 22 and 24
is (finding `22-power-series-discrete-obstruction`, issue #54): for
`k = ℚ(x_i : i ∈ I)`, `I` infinite, and `A = k[[t]]`, no derivation
`D : A → Ω_k ⊗_k A ≅ A^{(I)}` induces `d_k`, because the `dx_{i_n}`-component of
`D(Σ x_{i_n} tⁿ)` has `tⁿ`-coefficient `1` for every `n`; hence `A` is not formally
smooth over `k` for the discrete topology. The `t`-adic half (formal smoothness
for the `t`-adic topology) is not formalised.

What is proved:

* `lemme3_3` — exactly as stated: for `M` finitely presented, the canonical map
  `TensorProduct.piRightHom : M ⊗ ∏ P_i → ∏ (M ⊗ P_i)` is bijective. The proof is
  the typescript's: a presentation by free modules *of finite type* (the
  handwritten « de type fini », which the reading rightly calls essential),
  right exactness of `⊗`, exactness of products, and the five lemma.
* `corollaire3_4` — under the reading's hypothesis, verbatim.
* `corollaire3_5` — for a projective system indexed by `ℕ` with surjective
  transition maps (the reading's own reduction: « Le système cofinal
  dénombrable permet de se ramener à un système `(P_n)_{n ∈ ℕ}` dont les
  applications de transition sont surjectives — c'est ce que veut dire
  strict »). The reduction from a general countable cofinal system to `ℕ` is not
  formalised. The proof follows the reading's argument: the sequences split,
  `lim P_n ≅ P_0 × ∏ K_n` with `K_n = ker(P_{n+1} → P_n)` projective, then 3.4.
* `no_derivation` — the obstruction, abstractly: if `M` is a free `k`-module with
  basis `b`, no derivation `k⟦t⟧ → k⟦t⟧ ⊗_k M` over any base sends `aₙ` to
  `1 ⊗ b(iₙ)` for infinitely many distinct `iₙ`. The proof is the reading's, with one
  simplification: the reading first reduces to `D(t) = 0`; here `n` is chosen large
  enough that the `b(iₙ)`-coordinate of `D(t)` already vanishes, so the coordinate
  derivation `E` kills `t`, hence `E(t^{n+1}g) = t^{n+1}E(g)`, and the `tⁿ`-coefficient
  of `E(Σ a_m t^m)` is `1`, while `E(Σ a_m t^m)` is itself `0` for `n` large.
* `basisDx`, `no_derivation_extending_d` — page 22's case: `(dx_i)` is a basis of
  `Ω_{k/ℚ}` (polynomial basis, then localisation, which is formally étale), and no
  derivation `D : A → A ⊗_k Ω_{k/ℚ}` satisfies `D(c) = 1 ⊗ dc` on `k`.
* `retraction_of_formallySmooth`, `not_formallySmooth_discrete` — the conclusion the
  reading draws: if `A` were formally smooth over `k` (discrete topology, mathlib's
  `Algebra.FormallySmooth`), Jacobi–Zariski and projectivity of `Ω_{A/k}` would split
  `A ⊗_k Ω_{k/ℚ} → Ω_{A/ℚ}`, and the retraction composed with `d_A` would be such a
  `D`. So `ℚ(x_i)[[t]]` is not formally smooth over `ℚ(x_i)`.
* `not_formallySmooth_of_field`, `no_derivation_of_field` — the Proposition of page 23,
  which the second transcription pass reads in full: for a field `K` over a base `R` (the
  page's `k`) with `Ω_{K/R}` of infinite dimension, `K[[t]]` with the discrete topology is
  not formally smooth over `K`, and, « plus précisément », no derivation
  `K[[t]] → K[[t]] ⊗_K Ω_{K/R}` induces `d_{K/R}`. Neither characteristic 0 nor the
  choice of `ℚ(x_i)` is used: only a basis of `Ω` containing infinitely many `d aₙ`, which
  over a field can always be extracted from the spanning family `(da)`.
* `incl`, `proj`, `no_derivation_mv` — the page's `n > 0` variables (finding
  `22-p23-proposition-reconstruction`): no derivation
  `K⟦t₁, …, tₙ⟧ → K⟦t₁, …, tₙ⟧ ⊗_K Ω_{K/R}` induces `d_{K/R}`. Restricting along
  `t ↦ t_{i₀}` and projecting along `t_i ↦ 0` for `i ≠ i₀` (a retraction of `K`-algebras)
  turns such a derivation into one in a single variable. Its « a fortiori … sur k » rests on a
  relative notion the folder does not define and is not formalised.

**What the formalisation finds.**

* The hypothesis of 3.4, « tout `A`-module de type fini est de présentation
  finie — par exemple `A` noethérien », is not more general than Noetherian: it
  is *equivalent* to it (`hypothese_iff_noetherien`). If `A/I` is finitely
  presented, the kernel `I` of `A → A/I` is finitely generated. The « par
  exemple » suggests a wider class than there is. The wider class that the
  argument actually reaches is the rings whose *finitely generated ideals* are
  finitely presented — the coherent rings — since the proof of 3.4 only ever
  applies 3.3 to finitely generated ideals (`corollaire3_4_coherent`). That 3.4
  holds for coherent rings is Chase's theorem (1960); the typescript's
  hypothesis is strictly stronger.
* Lemme 3.3 holds over any commutative ring with no further hypothesis, as
  stated.
* The obstruction holds as the reading states it, and the step pages 22–23 carry out
  (the reduction to `D(t) = 0` through a finitely generated subfield `k_0`, or `K'`) is
  not needed. The conclusion holds for every field with infinite-dimensional `Ω`, in
  every characteristic, over any base ring, which is the page 23 Proposition. Page 24
  chooses `aₙ` with `d_{K/k} aₙ ≠ 0`, too weak for the construction; the struck
  « `D_{iₙ}(aₙ) ≠ 0` » is what `no_derivation` uses (`D(aₙ) = 1 ⊗ b(iₙ)`).
* Pages 26 and 28 (finding `22-differentials-kernel-counterexample`): the counterexample
  holds, in the page's own specialisation `a_i = 0` for `2 ≤ i ≤ p − 1`, for every prime `p`
  (`contre_exemple_page26`). With `K = 𝔽_p(x, b₀, b₁)`, `y = b₀ᵖ + b₁ᵖ x`, `k = 𝔽_p(x, y)` and
  `k' = k ∩ Kᵖ`, the element `1 ⊗ dy − a₁ ⊗ dx` of `K ⊗_k Ω_{k/k'}` is nonzero and dies in
  `Ω_{K/k'}`. The proof does not compute `k'`: it shows that `∂/∂y` kills `k'`, because
  `∂/∂x` of `K` kills `Kᵖ` and the chain rule gives `∂_x c + a₁ ∂_y c = 0` for `c ∈ k'`, while
  `a₁ ∉ k` (`a1_not_mem`, from the algebraic independence of `x, y, a₁`, `triple_injective`).
* Added 2026-10-26. The identification `Ω_{K/k'} = Ω_K` holds whenever `k'` lands in `Kᵖ`
  (`map_bijective_of_pow`, from the exact sequence `K ⊗_{k'} Ω_{k'} → Ω_K → Ω_{K/k'} → 0`, whose
  first map is zero), and the page's general example with `a₂, …, a_{p−1}` holds for every prime
  `p` (`contre_exemple_general`): for `K = 𝔽_p(x, b₀, …, b_{p−1})`, `a_i = b_iᵖ`, `y = Σ a_i xⁱ`,
  the map `Ω_{k/k'} ⊗_k K → Ω_K` is not injective, and `dy − y' dx` (`y' = Σ i a_i xⁱ⁻¹`) lies
  in the kernel of `K ⊗_k Ω_k → Ω_K` but not in the span of the `dc`, `c ∈ k'`
  (`contre_exemple_general_span`). The argument is the special case's, for any `k → K` with
  `dy = y' dx` and `y' ∉ k`; `x, y, y'` are algebraically independent because the specialisation
  `b_i ↦ 0` (`i ≥ 2`) sends them to `x, y, a₁` of the special case (`tripleG_injective`).

What this certifies is that the reading holds together at these points, not
that it is what the page says (issue #26).
-/

namespace Grothendieck.Folder22

open TensorProduct LinearMap

universe u

variable {A : Type u} [CommRing A]

section Lemme33

variable {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]

/-- The canonical homomorphism `M ⊗_A ∏ P_i → ∏ (M ⊗_A P_i)`. -/
noncomputable abbrev can (M : Type*) [AddCommGroup M] [Module A M] :
    M ⊗[A] (∀ i, P i) →ₗ[A] ∀ i, M ⊗[A] P i :=
  TensorProduct.piRightHom A A M P

/-- The product of the maps `g ⊗ P_i`. -/
noncomputable abbrev piRTensor {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (g : M →ₗ[A] N) : (∀ i, M ⊗[A] P i) →ₗ[A] ∀ i, N ⊗[A] P i :=
  LinearMap.pi fun i => g.rTensor (P i) ∘ₗ LinearMap.proj i

/-- The canonical map is natural in `M`. -/
theorem can_naturality {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (g : M →ₗ[A] N) :
    piRTensor P g ∘ₗ can P M = can P N ∘ₗ g.rTensor (∀ i, P i) :=
  TensorProduct.ext' fun m q => funext fun i => by simp

/-- A product of exact sequences is exact. -/
theorem exact_pi {M N Q : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] [∀ i, AddCommGroup (Q i)]
    [∀ i, Module A (Q i)] {f : ∀ i, M i →ₗ[A] N i} {g : ∀ i, N i →ₗ[A] Q i}
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)
      (LinearMap.pi fun i => g i ∘ₗ LinearMap.proj i) := fun y => by
  refine ⟨fun hy => ?_, fun ⟨x, hx⟩ => hx ▸ funext fun i => (h i _).2 ⟨x i, rfl⟩⟩
  choose x hx using fun i => (h i (y i)).1 (congrFun hy i)
  exact ⟨x, funext hx⟩

/-- `(Aⁿ) ⊗ N ≃ Nⁿ`. -/
noncomputable def psi (n : ℕ) (N : Type*) [AddCommGroup N] [Module A N] :
    (Fin n → A) ⊗[A] N ≃ₗ[A] (Fin n → N) :=
  (TensorProduct.comm A (Fin n → A) N).trans (TensorProduct.piScalarRight A A N (Fin n))

theorem psi_tmul (n : ℕ) {N : Type*} [AddCommGroup N] [Module A N] (f : Fin n → A) (x : N) :
    psi n N (f ⊗ₜ x) = fun j => f j • x := by
  simp [psi]

/-- Lemme 3.3 for `M = Aⁿ`, free of finite type. -/
theorem can_bijective_fin (n : ℕ) : Function.Bijective (can (A := A) P (Fin n → A)) := by
  have key : ∀ x i, psi n (P i) (can P (Fin n → A) x i) = fun j => psi n (∀ i, P i) x j i := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul f q => intro i; funext j; simp [psi_tmul]
    | add x y hx hy =>
      intro i; funext j
      simp only [map_add, Pi.add_apply, congrFun (hx i) j, congrFun (hy i) j]
  constructor
  · intro x y hxy
    apply (psi n (∀ i, P i)).injective
    funext j i
    rw [← congrFun (key x i) j, hxy, key y i]
  · intro z
    refine ⟨(psi n (∀ i, P i)).symm fun j i => psi n (P i) (z i) j, funext fun i => ?_⟩
    apply (psi n (P i)).injective
    rw [key]
    funext j
    simp

/-- **Lemme 3.3.** For `M` finitely presented, `M ⊗_A ∏ P_i → ∏ (M ⊗_A P_i)` is an
isomorphism. -/
theorem lemme3_3 (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    Function.Bijective (TensorProduct.piRightHom A A M P) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' A M
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (g.rTensor _) (f.rTensor _) (piRTensor P g) (piRTensor P f)
    (can P _) (can P _) (can P M) (can_naturality P g) (can_naturality P f)
    (rTensor_exact _ hfg hf) (exact_pi fun i => rTensor_exact _ hfg hf)
    (can_bijective_fin P m).2 (can_bijective_fin P n) (rTensor_surjective _ hf)
    (fun y => ⟨fun i => (rTensor_surjective (P i) hf (y i)).choose,
      funext fun i => (rTensor_surjective (P i) hf (y i)).choose_spec⟩)

end Lemme33

section Corollaire34

/-- The hypothesis of 3.4: every finitely generated `A`-module is finitely
presented. -/
def Hypothese (A : Type u) [CommRing A] : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module A N], Module.Finite A N → Module.FinitePresentation A N

/-- **The hypothesis of 3.4 is exactly Noetherianity.** -/
theorem hypothese_iff_noetherien : Hypothese A ↔ IsNoetherianRing A := by
  refine ⟨fun h => ⟨fun I => ?_⟩, fun _ N _ _ _ => Module.finitePresentation_of_finite A N⟩
  have := h (A ⧸ I) inferInstance
  simpa using Module.FinitePresentation.fg_ker I.mkQ I.mkQ_surjective

/-- **Corollaire 3.4**, in the form its proof uses: if every finitely generated
ideal is finitely presented (a coherent ring), any product of flat modules is
flat. -/
theorem corollaire3_4_coherent
    (hA : ∀ I : Ideal A, I.FG → Module.FinitePresentation A I)
    {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module.Flat A (P i)] : Module.Flat A (∀ i, P i) := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  have := hA I hI
  have h1 : Function.Injective (piRTensor P I.subtype) := fun x y hxy => funext fun i =>
    Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype (congrFun hxy i)
  have hinj : Function.Injective (piRTensor P I.subtype ∘ₗ can P I) := h1.comp (lemme3_3 P I).1
  rw [can_naturality P I.subtype, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- **Corollaire 3.4.** If every finitely generated `A`-module is finitely
presented, any product of flat `A`-modules is flat. -/
theorem corollaire3_4 (hA : Hypothese A) {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module.Flat A (P i)] :
    Module.Flat A (∀ i, P i) :=
  corollaire3_4_coherent (fun I hI => hA I (Module.Finite.iff_fg.2 hI)) P

end Corollaire34

section Corollaire35

/-- A product of two flat modules is flat (not in mathlib as such). -/
theorem flat_prod (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A M] [Module.Flat A N] : Module.Flat A (M × N) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have hsq : (TensorProduct.prodRight A A A M N).toLinearMap ∘ₗ I.subtype.rTensor (M × N) =
      (I.subtype.rTensor M).prodMap (I.subtype.rTensor N) ∘ₗ
        (TensorProduct.prodRight A A I M N).toLinearMap :=
    TensorProduct.ext' fun x m => by simp
  have h1 : Function.Injective ((I.subtype.rTensor M).prodMap (I.subtype.rTensor N)) :=
    fun x y hxy => Prod.ext
      (Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype
        (congrArg Prod.fst hxy))
      (Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype
        (congrArg Prod.snd hxy))
  have hinj : Function.Injective ((I.subtype.rTensor M).prodMap (I.subtype.rTensor N) ∘ₗ
      (TensorProduct.prodRight A A I M N).toLinearMap) :=
    h1.comp (TensorProduct.prodRight A A I M N).injective
  rw [← hsq, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

variable (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (π : ∀ n, P (n + 1) →ₗ[A] P n)

/-- The projective limit of `⋯ → P 2 → P 1 → P 0`, as a submodule of the product. -/
def limite : Submodule A (∀ n, P n) where
  carrier := {x | ∀ n, π n (x (n + 1)) = x n}
  add_mem' hx hy n := by simp [hx n, hy n]
  zero_mem' n := by simp
  smul_mem' c x hx n := by simp [hx n]

/-- **Corollaire 3.5** (system indexed by `ℕ`, transition maps surjective). If
every finitely generated `A`-module is finitely presented and every `P n` is
projective, the projective limit is flat. -/
theorem corollaire3_5 (hA : Hypothese A) [∀ n, Module.Projective A (P n)]
    (hπ : ∀ n, Function.Surjective (π n)) : Module.Flat A (limite P π) := by
  -- Each `P (n+1) → P n` splits.
  have hs : ∀ n, ∃ s : P n →ₗ[A] P (n + 1), π n ∘ₗ s = LinearMap.id := fun n =>
    Module.projective_lifting_property (π n) LinearMap.id (hπ n)
  choose s hs using hs
  have hs' : ∀ n x, π n (s n x) = x := fun n x => LinearMap.congr_fun (hs n) x
  let K : ∀ n, Submodule A (P (n + 1)) := fun n => LinearMap.ker (π n)
  -- `K n` is a direct summand of `P (n+1)`, hence projective.
  have hK : ∀ n, Module.Projective A (K n) := fun n =>
    Module.Projective.of_split (K n).subtype
      (LinearMap.codRestrict (K n) (LinearMap.id - s n ∘ₗ π n) fun x => by
        simp [K, hs'])
      (by ext x; simp)
  -- `lim P ≅ P 0 × ∏ K n`.
  let Φ : limite P π →ₗ[A] P 0 × ∀ n, K n :=
    { toFun := fun x => (x.1 0, fun n => ⟨x.1 (n + 1) - s n (x.1 n), by
        simp [K, hs', x.2 n]⟩)
      map_add' := fun x y => by
        ext <;> simp [map_add]; abel
      map_smul' := fun c x => by
        ext <;> simp [smul_sub] }
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      have h0 : x.1 0 = y.1 0 := congrArg Prod.fst hxy
      have hk : ∀ n, x.1 (n + 1) - s n (x.1 n) = y.1 (n + 1) - s n (y.1 n) := fun n =>
        congrArg Subtype.val (congrFun (congrArg Prod.snd hxy) n)
      apply Subtype.ext
      funext n
      induction n with
      | zero => exact h0
      | succ n ih => exact sub_left_inj.1 ((hk n).trans (by rw [ih]))
    · rintro ⟨y, k⟩
      let seq : ∀ n, P n := fun n => Nat.rec (motive := fun n => P n) y
        (fun n xn => s n xn + (k n : P (n + 1))) n
      have hseq : ∀ n, seq (n + 1) = s n (seq n) + k n := fun n => rfl
      refine ⟨⟨seq, fun n => ?_⟩, ?_⟩
      · rw [hseq, map_add, hs', (k n).2, add_zero]
      · ext n
        · rfl
        · simp [Φ, hseq]
  have : Module.Flat A (∀ n, K n) := corollaire3_4 hA _
  have := flat_prod (A := A) (P 0) (∀ n, K n)
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective Φ hΦ)

end Corollaire35

section PowerSeriesObstruction

open PowerSeries

section Obstruction

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]

/-- The `k⟦t⟧`-linear map `k⟦t⟧ ⊗_k M → k⟦t⟧`, `f ⊗ m ↦ φ(m) f`. -/
noncomputable def coordProj (φ : M →ₗ[k] k) : k⟦X⟧ ⊗[k] M →ₗ[k⟦X⟧] k⟦X⟧ :=
  (TensorProduct.AlgebraTensorModule.rid k k⟦X⟧ k⟦X⟧).toLinearMap ∘ₗ φ.baseChange k⟦X⟧

theorem coordProj_tmul (φ : M →ₗ[k] k) (f : k⟦X⟧) (m : M) : coordProj φ (f ⊗ₜ m) = φ m • f := by
  simp [coordProj]

/-- An element of `k⟦t⟧ ⊗_k M` has only finitely many non-zero coordinates. -/
theorem coordProj_eventually_zero {ι : Type*} (b : Module.Basis ι k M) (z : k⟦X⟧ ⊗[k] M) :
    ∃ s : Finset ι, ∀ i ∉ s, coordProj (b.coord i) z = 0 := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul f m =>
    refine ⟨(b.repr m).support, fun i hi => ?_⟩
    rw [coordProj_tmul, Module.Basis.coord_apply, Finsupp.notMem_support_iff.1 hi, zero_smul]
  | add x y hx hy =>
    obtain ⟨⟨s, hs⟩, t, ht⟩ := And.intro hx hy
    refine ⟨s ∪ t, fun i hi => ?_⟩
    rw [map_add, hs i (Finset.notMem_union.1 hi).1, ht i (Finset.notMem_union.1 hi).2, add_zero]

variable {R : Type*} [CommRing R] [Algebra R k]

theorem der_X_pow_mul (E : Derivation R k⟦X⟧ k⟦X⟧) (hX : E X = 0) (m : ℕ) (g : k⟦X⟧) :
    E (X ^ m * g) = X ^ m * E g := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hX]
  simp

theorem der_C_mul_X_pow (E : Derivation R k⟦X⟧ k⟦X⟧) (hX : E X = 0) (m : ℕ) (c : k) :
    E (C c * X ^ m) = E (C c) * X ^ m := by
  rw [mul_comm, der_X_pow_mul E hX, mul_comm]

/-- `Σ aₙ tⁿ = Σ_{m ≤ n} a_m t^m + t^{n+1} g`. -/
theorem mk_eq_sum_add (a : ℕ → k) (n : ℕ) :
    PowerSeries.mk a = ∑ m ∈ Finset.range (n + 1), C (a m) * X ^ m +
      X ^ (n + 1) * PowerSeries.mk fun j => a (j + (n + 1)) := by
  ext j
  rw [map_add, map_sum, coeff_X_pow_mul']
  simp only [coeff_C_mul_X_pow, coeff_mk, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hj : j < n + 1
  · simp [hj, show ¬ n + 1 ≤ j by omega]
  · simp [hj, show n + 1 ≤ j by omega, Nat.sub_add_cancel (show n + 1 ≤ j by omega)]

/-- **The obstruction (pp. 22, 24).** Let `M` be a free `k`-module with basis `b`, and
`a₀, a₁, …` elements of `k`. There is no derivation `D : k⟦t⟧ → k⟦t⟧ ⊗_k M` (over any base
`R`) with `D(aₙ) = 1 ⊗ b(iₙ)` for infinitely many distinct indices `iₙ`: the coordinate
of `D(Σ aₙ tⁿ)` along `b(iₙ)` has `tⁿ`-coefficient `1` for every `n`. -/
theorem no_derivation [Nontrivial k] {ι : Type*} (b : Module.Basis ι k M) (e : ℕ → ι)
    (he : Function.Injective e) (a : ℕ → k) (D : Derivation R k⟦X⟧ (k⟦X⟧ ⊗[k] M))
    (hD : ∀ n, D (C (a n)) = 1 ⊗ₜ b (e n)) : False := by
  classical
  obtain ⟨s, hs⟩ := coordProj_eventually_zero b (D (PowerSeries.mk a))
  obtain ⟨t, ht⟩ := coordProj_eventually_zero b (D X)
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset ((s ∪ t).preimage e he.injOn)
  rw [Finset.mem_preimage, Finset.mem_union, not_or] at hn
  let E : Derivation R k⟦X⟧ k⟦X⟧ := (coordProj (b.coord (e n))).compDer D
  have hE : ∀ z, E z = coordProj (b.coord (e n)) (D z) := fun _ => rfl
  have hX : E X = 0 := by rw [hE, ht _ hn.2]
  have hC : ∀ m, E (C (a m)) = C (if m = n then 1 else 0) := by
    intro m
    rw [hE, hD, coordProj_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, he.eq_iff]
    split_ifs <;> simp
  have h0 : E (PowerSeries.mk a) = 0 := by rw [hE, hs _ hn.1]
  have h1 := congrArg (coeff n) h0
  rw [mk_eq_sum_add a n, map_add, map_sum, der_X_pow_mul E hX, map_add, map_sum,
    coeff_X_pow_mul', ite_eq_right (by omega)] at h1
  simp only [der_C_mul_X_pow E hX, hC, coeff_C_mul_X_pow] at h1
  simp at h1

end Obstruction

section Discrete

/-- `k = ℚ(x_i : i ∈ I)`. -/
abbrev K (I : Type*) := FractionRing (MvPolynomial I ℚ)

instance (I : Type*) : Algebra.FormallyEtale (MvPolynomial I ℚ) (K I) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial I ℚ))

/-- The generator `x_i` of `k`. -/
noncomputable abbrev x {I : Type*} (i : I) : K I := algebraMap (MvPolynomial I ℚ) (K I) (.X i)

/-- The basis `(dx_i)` of `Ω_{k/ℚ}`: `Ω_k ⊗_k A ≅ A^{(I)}`, as page 22 writes. -/
noncomputable def basisDx (I : Type*) : Module.Basis I (K I) Ω[K I⁄ℚ] :=
  ((KaehlerDifferential.mvPolynomialBasis ℚ I).baseChange (K I)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ (MvPolynomial I ℚ) (K I))

-- TEMP diagnostics (CI only)
example (I : Type) : Algebra ℚ (K I) := inferInstance
example (I : Type) : Module ℚ (K I)⟦X⟧ := inferInstance
example (I : Type) : SMulCommClass (K I) ℚ (K I)⟦X⟧ := inferInstance
example (I : Type) : Module ℚ Ω[K I⁄ℚ] := inferInstance
set_option trace.Meta.synthInstance true in
example (I : Type) : Module ℚ ((K I)⟦X⟧ ⊗[K I] Ω[K I⁄ℚ]) := inferInstance

theorem basisDx_apply (I : Type*) (i : I) :
    basisDx I i = KaehlerDifferential.D ℚ (K I) (x i) := by
  simp only [basisDx, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  exact (KaehlerDifferential.mapBaseChange_tmul ..).trans
    (by rw [one_smul, KaehlerDifferential.map_D])

/-- **No derivation `D : A → Ω_k ⊗_k A` induces `d_k`** (pp. 22, 24), for `k = ℚ(x_i : i ∈ I)`,
`I` infinite, `A = k[[t]]`. -/
theorem no_derivation_extending_d (I : Type*) [Infinite I] :
    ¬ ∃ D : Derivation ℚ (K I)⟦X⟧ ((K I)⟦X⟧ ⊗[K I] Ω[K I⁄ℚ]),
      ∀ c, D (C c) = 1 ⊗ₜ KaehlerDifferential.D ℚ (K I) c := by
  rintro ⟨D, hD⟩
  let e := Infinite.natEmbedding I
  exact no_derivation (basisDx I) e e.injective
    (fun n => x (e n)) D fun n => by rw [hD, basisDx_apply]

/-- If `S` is formally smooth over `k` (discrete topology), `S ⊗_k Ω_{k/R} → Ω_{S/R}` has a
`S`-linear retraction. -/
theorem retraction_of_formallySmooth (R k S : Type*) [CommRing R] [CommRing k] [CommRing S]
    [Algebra R k] [Algebra R S] [Algebra k S] [IsScalarTower R k S]
    [Algebra.FormallySmooth k S] :
    ∃ r : Ω[S⁄R] →ₗ[S] S ⊗[k] Ω[k⁄R], r ∘ₗ KaehlerDifferential.mapBaseChange R k S =
      LinearMap.id := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R k S) :=
      (injective_iff_map_eq_zero _).mpr fun x hx => by
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k S x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have h := ((KaehlerDifferential.exact_mapBaseChange_map R k S).split_tfae').out 1 2
  exact (h.mp ⟨hinj,
    Module.projective_lifting_property _ _ (KaehlerDifferential.map_surjective R k S)⟩).2

/-- **`k⟦t⟧` is not formally smooth over `k` for the discrete topology** as soon as `Ω_{k/R}`
has a basis containing infinitely many differentials `d aₙ`. -/
theorem not_formallySmooth_of_basis (R k : Type*) [CommRing R] [CommRing k] [Nontrivial k]
    [Algebra R k] {ι : Type*} (b : Module.Basis ι k Ω[k⁄R]) (e : ℕ → ι)
    (he : Function.Injective e) (a : ℕ → k) (ha : ∀ n, KaehlerDifferential.D R k (a n) = b (e n)) :
    ¬ Algebra.FormallySmooth k k⟦X⟧ := by
  intro _
  obtain ⟨r, hr⟩ := retraction_of_formallySmooth R k k⟦X⟧
  refine no_derivation b e he a (r.compDer (KaehlerDifferential.D R k⟦X⟧)) fun n => ?_
  have h := LinearMap.congr_fun hr (1 ⊗ₜ KaehlerDifferential.D R k (a n))
  rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D, LinearMap.id_apply, ha] at h
  simpa using h

/-- **The page's example**: for `k = ℚ(x_i : i ∈ I)`, `I` infinite, `k[[t]]` is not formally
smooth over `k` for the discrete topology. -/
theorem not_formallySmooth_discrete (I : Type*) [Infinite I] :
    ¬ Algebra.FormallySmooth (K I) (K I)⟦X⟧ := by
  let e := Infinite.natEmbedding I
  exact not_formallySmooth_of_basis ℚ (K I) (basisDx I) e e.injective
    (fun n => x (e n)) fun n => (basisDx_apply I _).symm

/-- **The general form, in every characteristic**: for a field `K` and any base ring `R` with
`Ω_{K/R}` infinite-dimensional, `K[[t]]` is not formally smooth over `K` for the discrete
topology. -/
theorem not_formallySmooth_of_field (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    (h : ¬ Module.Finite K Ω[K⁄R]) : ¬ Algebra.FormallySmooth K K⟦X⟧ := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (Set.range (KaehlerDifferential.D R K))
  let b : Module.Basis s K Ω[K⁄R] := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, KaehlerDifferential.span_range_derivation])
  have : Infinite s := not_finite_iff_infinite.mp fun _ => h (.of_basis b)
  let e := Infinite.natEmbedding s
  choose a ha using fun n => hs (e n).2
  exact not_formallySmooth_of_basis R K b e e.injective a fun n => by
    rw [ha, Module.Basis.mk_apply]

/-- **The Proposition of page 23**, in the form « plus précisément » of the reading: for a
field `K` over a base `R` (the page's `k`) with `Ω_{K/R}` infinite-dimensional, no derivation
`D : K⟦t⟧ → K⟦t⟧ ⊗_K Ω_{K/R}` induces `d_{K/R}` on `K`. -/
theorem no_derivation_of_field (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    (h : ¬ Module.Finite K Ω[K⁄R]) :
    ¬ ∃ D : Derivation R K⟦X⟧ (K⟦X⟧ ⊗[K] Ω[K⁄R]),
      ∀ c, D (C c) = 1 ⊗ₜ KaehlerDifferential.D R K c := by
  rintro ⟨D, hD⟩
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (Set.range (KaehlerDifferential.D R K))
  let b : Module.Basis s K Ω[K⁄R] := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, KaehlerDifferential.span_range_derivation])
  have : Infinite s := not_finite_iff_infinite.mp fun _ => h (.of_basis b)
  let e := Infinite.natEmbedding s
  choose a ha using fun n => hs (e n).2
  exact no_derivation b e e.injective a D fun n => by
    rw [hD, ha, Module.Basis.mk_apply]

end Discrete

end PowerSeriesObstruction

/-! ### Pages 26 and 28: the counterexample `k = 𝔽_p(x, y) ⊂ K` -/

section Contre

open MvPolynomial

variable (p : ℕ)

/-- `𝔽_p(x_i)`, the field of rational functions in the variables `X i`. -/
abbrev FracF (σ : Type) := FractionRing (MvPolynomial σ (ZMod p))

instance (σ : Type) : Algebra.FormallyEtale (MvPolynomial σ (ZMod p)) (FracF p σ) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial σ (ZMod p)))

/-- The variable `X i` in `𝔽_p(X)`. -/
noncomputable abbrev var {σ : Type} (i : σ) : FracF p σ :=
  algebraMap (MvPolynomial σ (ZMod p)) (FracF p σ) (.X i)

/-- The basis `(dX_i)` of `Ω_{𝔽_p(X)/𝔽_p}`. -/
noncomputable def basisD (σ : Type) : Module.Basis σ (FracF p σ) Ω[FracF p σ⁄ZMod p] :=
  ((KaehlerDifferential.mvPolynomialBasis (ZMod p) σ).baseChange (FracF p σ)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale (ZMod p) (MvPolynomial σ (ZMod p))
      (FracF p σ))

theorem basisD_apply (σ : Type) (i : σ) :
    basisD p σ i = KaehlerDifferential.D (ZMod p) (FracF p σ) (var p i) := by
  simp only [basisD, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  exact (KaehlerDifferential.mapBaseChange_tmul ..).trans
    (by rw [one_smul, KaehlerDifferential.map_D])

/-- The partial derivative `∂/∂X_i` on `𝔽_p(X)`. -/
noncomputable def partialD {σ : Type} (i : σ) : Derivation (ZMod p) (FracF p σ) (FracF p σ) :=
  ((basisD p σ).coord i).compDer (KaehlerDifferential.D (ZMod p) (FracF p σ))

theorem partialD_var {σ : Type} [DecidableEq σ] (i j : σ) :
    partialD p i (var p j) = if j = i then 1 else 0 := by
  change (basisD p σ).coord i (KaehlerDifferential.D _ _ (var p j)) = _
  rw [← basisD_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

/-- Two derivations of `𝔽_p(X)` into a module agreeing on the variables are equal. -/
theorem derivation_ext {σ : Type} {M : Type*} [AddCommGroup M] [Module (FracF p σ) M]
    [Module (ZMod p) M] [IsScalarTower (ZMod p) (FracF p σ) M]
    {D₁ D₂ : Derivation (ZMod p) (FracF p σ) M} (h : ∀ i, D₁ (var p i) = D₂ (var p i)) :
    D₁ = D₂ := by
  have : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential :=
    (basisD p σ).ext fun i => by
      rw [basisD_apply, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D, h]
  ext c
  rw [← D₁.liftKaehlerDifferential_comp_D, this, D₂.liftKaehlerDifferential_comp_D]

/-! #### The polynomial map behind the example -/

/-- `(x, y, a₁) = (X₀, X₁ᵖ + X₂ᵖ X₀, X₂ᵖ)`: with `b₀ = X₁`, `b₁ = X₂`, `a_i = b_iᵖ` and
`y = a₀ + a₁ x`. -/
noncomputable def triple : Fin 3 → MvPolynomial (Fin 3) (ZMod p) :=
  ![X 0, X 1 ^ p + X 2 ^ p * X 0, X 2 ^ p]

/-- `x, y, a₁` are algebraically independent: `T ↦ (X₀, X₁ᵖ + X₂ᵖX₀, X₂ᵖ)` is injective. It is
the triangular automorphism `(T₀, T₁ + T₂T₀, T₂)` followed by `(T₀, T₁ᵖ, T₂ᵖ)`, which the
substitution `X₀ ↦ X₀ᵖ` turns into the injective `expand p`. -/
theorem triple_injective (hp : 0 < p) : Function.Injective (aeval (R := ZMod p) (triple p)) := by
  let ψ : MvPolynomial (Fin 3) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
    aeval ![X 0, X 1 + X 2 * X 0, X 2]
  let ψ' : MvPolynomial (Fin 3) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
    aeval ![X 0, X 1 - X 2 * X 0, X 2]
  let ε : MvPolynomial (Fin 3) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
    aeval ![X 0, X 1 ^ p, X 2 ^ p]
  let θ : MvPolynomial (Fin 3) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
    aeval ![X 0 ^ p, X 1, X 2]
  have h1 : ψ'.comp ψ = AlgHom.id _ _ := by
    ext i; fin_cases i <;> simp [ψ, ψ']
  have h2 : θ.comp ε = expand p := by
    ext i; fin_cases i <;> simp [θ, ε]
  have h3 : aeval (R := ZMod p) (triple p) = ε.comp ψ := by
    ext i; fin_cases i <;> simp [ψ, ε, triple]
  have hε : Function.Injective ε :=
    Function.Injective.of_comp (f := θ) (by rw [← AlgHom.coe_comp, h2]; exact expand_injective hp)
  rw [h3, AlgHom.coe_comp]
  exact hε.comp (Function.LeftInverse.injective (g := ψ') (DFunLike.congr_fun h1))

/-! #### The fields `k = 𝔽_p(x, y) ⊂ K = 𝔽_p(x, b₀, b₁)` and `k' = k ∩ Kᵖ` -/

variable [hp : Fact p.Prime]

instance charP_rat (σ : Type) : CharP (FracF p σ) p :=
  ⟨fun x => by
    rw [← map_natCast (algebraMap (ZMod p) (FracF p σ))]
    exact ⟨fun h => (CharP.cast_eq_zero_iff (ZMod p) p x).1
        ((algebraMap (ZMod p) (FracF p σ)).injective (h.trans (map_zero _).symm)),
      fun h => by rw [(CharP.cast_eq_zero_iff (ZMod p) p x).2 h, map_zero]⟩⟩

/-- `x, y, a₁` in `K = 𝔽_p(X₀, X₁, X₂)`. -/
noncomputable def tripleK : Fin 3 → FracF p (Fin 3) := fun i => algebraMap _ _ (triple p i)

theorem tripleK_injective : Function.Injective (aeval (R := ZMod p) (tripleK p)) := by
  have : aeval (R := ZMod p) (tripleK p) = (IsScalarTower.toAlgHom (ZMod p)
      (MvPolynomial (Fin 3) (ZMod p)) (FracF p (Fin 3))).comp (aeval (triple p)) := by
    ext i; simp [tripleK]
  rw [this, AlgHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (triple_injective p hp.out.pos)

/-- `𝔽_p[X, Y] → K`, `X ↦ x`, `Y ↦ y`. -/
noncomputable def phi : MvPolynomial (Fin 2) (ZMod p) →ₐ[ZMod p] FracF p (Fin 3) :=
  (aeval (tripleK p)).comp (rename Fin.castSucc)

theorem phi_injective : Function.Injective (phi p) :=
  (tripleK_injective p).comp (rename_injective _ (Fin.castSucc_injective 2))

/-- `k = 𝔽_p(X, Y) → K`, onto `𝔽_p(x, y)`. -/
noncomputable def iota : FracF p (Fin 2) →ₐ[ZMod p] FracF p (Fin 3) :=
  IsFractionRing.liftAlgHom (phi_injective p)

noncomputable instance : Algebra (FracF p (Fin 2)) (FracF p (Fin 3)) := (iota p).toRingHom.toAlgebra

instance : IsScalarTower (ZMod p) (FracF p (Fin 2)) (FracF p (Fin 3)) :=
  IsScalarTower.of_algebraMap_eq fun c => ((iota p).commutes c).symm

theorem algebraMap_eq_iota (z : FracF p (Fin 2)) :
    algebraMap (FracF p (Fin 2)) (FracF p (Fin 3)) z = iota p z := rfl

theorem iota_var (i : Fin 2) : iota p (var p i) = tripleK p i.castSucc := by
  simp [iota, phi]

theorem tripleK_one :
    tripleK p 1 = var p 1 ^ p + var p 2 ^ p * var p (0 : Fin 3) := by
  simp [tripleK, triple]

/-- `k' = k ∩ Kᵖ`. -/
noncomputable def kPrime : Subfield (FracF p (Fin 2)) :=
  (frobenius (FracF p (Fin 3)) p).fieldRange.comap (iota p).toRingHom

/-- In characteristic `p`, every derivation kills `p`-th powers. -/
theorem der_pow_char {R M : Type*} [CommRing R] [Algebra R (FracF p (Fin 3))] [AddCommGroup M]
    [Module (FracF p (Fin 3)) M] [Module R M]
    (D : Derivation R (FracF p (Fin 3)) M) (a : FracF p (Fin 3)) : D (a ^ p) = 0 := by
  rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul (FracF p (Fin 3)), CharP.cast_eq_zero,
    zero_smul]

/-- `D y = a₁ D x` for every derivation of `K`: the `a_i` are `p`-th powers. -/
theorem der_y {R M : Type*} [CommRing R] [Algebra R (FracF p (Fin 3))] [AddCommGroup M]
    [Module (FracF p (Fin 3)) M] [Module R M] (D : Derivation R (FracF p (Fin 3)) M) :
    D (tripleK p 1) = tripleK p 2 • D (tripleK p 0) := by
  rw [tripleK_one, map_add, D.leibniz]
  simp only [der_pow_char p D, smul_zero, add_zero, zero_add]
  simp [tripleK, triple]

/-- `a₁ ∉ k`: from the algebraic independence of `x, y, a₁`. -/
theorem a1_not_mem (z : FracF p (Fin 2)) : iota p z ≠ tripleK p 2 := by
  intro hz
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 2) (ZMod p)) z
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  rw [map_div₀] at hz
  simp only [iota, IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap] at hz
  have hφg : phi p g ≠ 0 := fun h => hg0 (phi_injective p (h.trans (map_zero _).symm))
  have key : aeval (tripleK p) (rename Fin.castSucc f) =
      aeval (tripleK p) (X 2 * rename Fin.castSucc g) := by
    rw [map_mul, aeval_X]
    change phi p f = tripleK p 2 * phi p g
    change phi p f / phi p g = _ at hz
    rw [← hz, div_mul_cancel₀ _ hφg]
  have key' := tripleK_injective p key
  let π : MvPolynomial (Fin 3) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
    aeval ![X 0, X 1, 0]
  have hπ : π.comp (rename Fin.castSucc) = rename Fin.castSucc := by
    ext i; fin_cases i <;> simp [π]
  have hf : rename Fin.castSucc f = (0 : MvPolynomial (Fin 3) (ZMod p)) := by
    have := congrArg π key'
    rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hπ] at this
    simpa [π] using this
  rw [hf, eq_comm, mul_eq_zero, or_iff_right (X_ne_zero 2)] at key'
  exact hg0 (rename_injective _ (Fin.castSucc_injective 2) (key'.trans (map_zero _).symm))

/-- The derivation `ι ∘ ∂/∂Y : k → K`. -/
noncomputable def delta0 : Derivation (ZMod p) (FracF p (Fin 2)) (FracF p (Fin 3)) :=
  (Algebra.linearMap (FracF p (Fin 2)) (FracF p (Fin 3))).compDer (partialD p 1)

/-- The chain rule along `ι`, for a derivation `D` of `K`. -/
theorem chain (D : Derivation (ZMod p) (FracF p (Fin 3)) (FracF p (Fin 3))) (c : FracF p (Fin 2)) :
    D (iota p c) = iota p (partialD p 0 c) * D (tripleK p 0) +
      iota p (partialD p 1 c) * D (tripleK p 1) := by
  let E : Derivation (ZMod p) (FracF p (Fin 2)) (FracF p (Fin 3)) :=
    D (tripleK p 0) • (Algebra.linearMap _ _).compDer (partialD p 0) +
      D (tripleK p 1) • (Algebra.linearMap _ _).compDer (partialD p 1)
  have h : D.compAlgebraMap (FracF p (Fin 2)) = E := derivation_ext p fun i => by
    fin_cases i <;> simp [E, partialD_var, algebraMap_eq_iota, iota_var]
  have := congrArg (fun F => F c) h
  simpa [E, algebraMap_eq_iota, mul_comm] using this

theorem delta0_kPrime (c : FracF p (Fin 2)) (hc : c ∈ kPrime p) : delta0 p c = 0 := by
  obtain ⟨w, hw⟩ := hc
  change frobenius _ p w = iota p c at hw
  have h := chain p (partialD p 0) (c := c)
  rw [← hw, _root_.frobenius_def, der_pow_char p, der_y] at h
  have h0 : partialD p (0 : Fin 3) (tripleK p 0) = 1 := by
    simp [tripleK, triple, partialD_var]
  rw [h0, mul_one, smul_eq_mul, mul_one] at h
  change iota p (partialD p 1 c) = 0
  by_contra hne
  refine a1_not_mem p (-(partialD p 0 c) / partialD p 1 c) ?_
  rw [map_div₀, map_neg, neg_div, eq_comm, eq_neg_iff_add_eq_zero, add_div' _ _ _ hne,
    div_eq_zero_iff]
  exact Or.inl (by linear_combination -h)

/-- `ι ∘ ∂/∂Y` as a `k'`-derivation: it kills `k' = k ∩ Kᵖ`. -/
noncomputable def delta : Derivation (kPrime p) (FracF p (Fin 2)) (FracF p (Fin 3)) where
  toFun := delta0 p
  map_add' := map_add _
  map_smul' c z := by
    rw [RingHom.id_apply, Algebra.smul_def, (delta0 p).leibniz,
      delta0_kPrime p (algebraMap _ _ c) c.2, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := (delta0 p).map_one_eq_zero
  leibniz' := (delta0 p).leibniz

/-- **The counterexample of pages 26 and 28.** For `k = 𝔽_p(x, y) ⊂ K = 𝔽_p(x, b₀, b₁)` with
`y = b₀ᵖ + b₁ᵖ x` (the page's example with `a_i = 0` for `2 ≤ i ≤ p − 1`) and
`k' = k ∩ Kᵖ`, the map `K ⊗_k Ω_{k/k'} → Ω_{K/k'}` is not injective: `dy − a₁ dx` is a
nonzero element of the kernel. -/
theorem contre_exemple_page26 :
    ¬ Function.Injective
      (KaehlerDifferential.mapBaseChange (kPrime p) (FracF p (Fin 2)) (FracF p (Fin 3))) := by
  intro hinj
  let ω : FracF p (Fin 3) ⊗[FracF p (Fin 2)] Ω[FracF p (Fin 2)⁄kPrime p] :=
    (1 : FracF p (Fin 3)) ⊗ₜ KaehlerDifferential.D _ _ (var p 1) -
      tripleK p 2 ⊗ₜ KaehlerDifferential.D _ _ (var p 0)
  have h0 :
      KaehlerDifferential.mapBaseChange (kPrime p) (FracF p (Fin 2)) (FracF p (Fin 3)) ω = 0 := by
    simp only [ω, map_sub, KaehlerDifferential.mapBaseChange_tmul,
      KaehlerDifferential.map_D, algebraMap_eq_iota, iota_var, one_smul]
    rw [Fin.castSucc_one, der_y, Fin.castSucc_zero, sub_self]
  have h1 : (delta p).liftKaehlerDifferential.liftBaseChange (FracF p (Fin 3)) ω = 1 := by
    simp only [ω, map_sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]
    change 1 • iota p (partialD p 1 (var p 1)) - tripleK p 2 • iota p (partialD p 1 (var p 0)) = 1
    simp [partialD_var]
  have hω : ω = 0 := hinj (h0.trans (map_zero _).symm)
  rw [hω, map_zero] at h1
  exact zero_ne_one h1

end Contre

/-! ### Page 23 in `n` variables -/

section SeveralVariables

open PowerSeries

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {σ : Type*} [Finite σ]
  [DecidableEq σ]

/-- `f(t) ↦ f(t_{i₀})`, from `K⟦t⟧` to `K⟦t₁, …, tₙ⟧`. -/
noncomputable def incl (i₀ : σ) : K⟦X⟧ →ₐ[K] MvPowerSeries σ K :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))
    (a := MvPowerSeries.X i₀)

/-- `t_{i₀} ↦ t`, `t_i ↦ 0` for `i ≠ i₀`. -/
noncomputable def proj (i₀ : σ) : MvPowerSeries σ K →ₐ[K] K⟦X⟧ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (a := fun s : σ => if s = i₀ then (PowerSeries.X : K⟦X⟧) else 0) fun s => by
      split_ifs
      exacts [PowerSeries.constantCoeff_X, map_zero _])

theorem proj_incl (i₀ : σ) (f : K⟦X⟧) : proj i₀ (incl i₀ f) = f := by
  simp only [proj, incl, MvPowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
      split_ifs
      exacts [PowerSeries.constantCoeff_X, map_zero _])]
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
      split_ifs
      exacts [PowerSeries.constantCoeff_X, map_zero _])]
  simp only
  exact PowerSeries.X_subst f

/-- **Page 23's Proposition in `n ≥ 1` variables**: for a field `K` over `R` with `Ω_{K/R}`
infinite-dimensional, no derivation `K⟦t₁, …, tₙ⟧ → K⟦t₁, …, tₙ⟧ ⊗_K Ω_{K/R}` induces
`d_{K/R}` on `K`. Restricting along `t ↦ t_{i₀}` and projecting along `t_i ↦ 0`, `i ≠ i₀`,
gives such a derivation in one variable, which `no_derivation_of_field` excludes. -/
theorem no_derivation_mv (i₀ : σ) (h : ¬ Module.Finite K Ω[K⁄R]) :
    ¬ ∃ D : Derivation R (MvPowerSeries σ K) (MvPowerSeries σ K ⊗[K] Ω[K⁄R]),
      ∀ c, D (MvPowerSeries.C c) = 1 ⊗ₜ KaehlerDifferential.D R K c := by
  rintro ⟨D, hD⟩
  let φ : MvPowerSeries σ K ⊗[K] Ω[K⁄R] →ₗ[K] K⟦X⟧ ⊗[K] Ω[K⁄R] :=
    LinearMap.rTensor _ (proj i₀).toLinearMap
  have hφ : ∀ (a : MvPowerSeries σ K) (t : MvPowerSeries σ K ⊗[K] Ω[K⁄R]),
      φ (a • t) = proj i₀ a • φ t := by
    intro a t
    induction t using TensorProduct.inductionOn with
    | tmul x ω => simp [φ, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  let L : K⟦X⟧ →ₗ[R] K⟦X⟧ ⊗[K] Ω[K⁄R] :=
    (φ.restrictScalars R) ∘ₗ D.toLinearMap ∘ₗ ((incl i₀).restrictScalars R).toLinearMap
  have hL : ∀ f, L f = φ (D (incl i₀ f)) := fun _ => rfl
  refine no_derivation_of_field R K h ⟨Derivation.mk' L fun f g => ?_, fun c => ?_⟩
  · rw [hL, hL, hL, map_mul, Derivation.leibniz, map_add, hφ, hφ, proj_incl, proj_incl]
  · change L (C c) = _
    rw [hL]
    have : incl i₀ (C c) = MvPowerSeries.C c := by
      have h := (incl i₀).commutes c
      rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
      rw [h, MvPowerSeries.c_eq_algebraMap]
    rw [this, hD]
    simp [φ]

end SeveralVariables

/-! ### Page 23 in `n` variables: failure of formal smoothness -/

section SeveralVariablesSmooth

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {σ : Type*} [Finite σ]
  [DecidableEq σ]

/-- **Page 23's Proposition in `n ≥ 1` variables, formal smoothness**: for a field `K` over `R`
with `Ω_{K/R}` infinite-dimensional, `K⟦t₁, …, tₙ⟧` with the discrete topology is not formally
smooth over `K`. As for `n = 1`: a formally smooth `S` would give, by Jacobi–Zariski, a retraction
`r` of `S ⊗_K Ω_{K/R} → Ω_{S/R}` (`retraction_of_formallySmooth`), and `r ∘ d_{S/R}` would be a
derivation inducing `d_{K/R}`, which `no_derivation_mv` excludes. -/
theorem not_formallySmooth_mv (i₀ : σ) (h : ¬ Module.Finite K Ω[K⁄R]) :
    ¬ Algebra.FormallySmooth K (MvPowerSeries σ K) := by
  intro _
  obtain ⟨r, hr⟩ := retraction_of_formallySmooth R K (MvPowerSeries σ K)
  refine no_derivation_mv i₀ h ⟨r.compDer (KaehlerDifferential.D R (MvPowerSeries σ K)),
    fun c => ?_⟩
  simpa [MvPowerSeries.c_eq_algebraMap] using
    LinearMap.congr_fun hr (1 ⊗ₜ KaehlerDifferential.D R K c)

end SeveralVariablesSmooth


/-! ### Pages 26 and 28: `Ω_{K/k'} = Ω_K`, and the general example with `a₂, …, a_{p−1}` -/

section ContreGeneral

open MvPolynomial

/-- In characteristic `p`, every derivation kills `p`-th powers. -/
theorem der_pow_char' (p : ℕ) {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B] [CharP B p]
    [AddCommGroup M] [Module B M] [Module R M] (D : Derivation R B M) (a : B) : D (a ^ p) = 0 := by
  rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, CharP.cast_eq_zero, zero_smul]

/-- **`Ω_{B/S} = Ω_{B/R}` when `S` lands in `Bᵖ`.** For `R → S → B` with `B` of characteristic
`p` and the image of `S` made of `p`-th powers, `Ω_{B/R} → Ω_{B/S}` is bijective: by the exact
sequence `B ⊗_S Ω_{S/R} → Ω_{B/R} → Ω_{B/S} → 0`, whose first map is zero. -/
theorem map_bijective_of_pow (p : ℕ) (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] [CharP B p]
    (h : ∀ s : S, ∃ w : B, w ^ p = algebraMap S B s) :
    Function.Bijective (KaehlerDifferential.map R S B B) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, KaehlerDifferential.map_surjective R S B⟩
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S B x).1 hx
  have h0 : KaehlerDifferential.map R R S B = 0 := by
    ext s
    obtain ⟨w, hw⟩ := h s
    simp [KaehlerDifferential.map_D, ← hw, der_pow_char' p]
  clear hx
  induction t using TensorProduct.inductionOn with
  | tmul b ω => simp [KaehlerDifferential.mapBaseChange_tmul, h0]
  | add t u ht hu => rw [map_add, ht, hu, add_zero]

/-! #### The argument for any `k = 𝔽_p(x, y) → K` with `dy = y' dx` and `y' ∉ k` -/

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [Algebra (ZMod p) K]
  [Algebra (FracF p (Fin 2)) K] [IsScalarTower (ZMod p) (FracF p (Fin 2)) K]

/-- `k' = k ∩ Kᵖ`. -/
noncomputable def kPrimeOf : Subfield (FracF p (Fin 2)) :=
  (frobenius K p).fieldRange.comap (algebraMap (FracF p (Fin 2)) K)

variable {K} (y' : K)
  (hy : ∀ {R M : Type} [CommRing R] [Algebra R K] [AddCommGroup M] [Module K M] [Module R M]
    (D : Derivation R K M),
      D (algebraMap _ K (var p (1 : Fin 2))) = y' • D (algebraMap _ K (var p (0 : Fin 2))))
  (hy' : ∀ z, algebraMap (FracF p (Fin 2)) K z ≠ y')
  (dx : Derivation (ZMod p) K K) (hdx : dx (algebraMap _ K (var p (0 : Fin 2))) = 1)

include hy hy' hdx in
/-- `∂/∂y` kills `k'`: the chain rule along `k → K` for `∂/∂x` gives `∂_x c + y' ∂_y c = 0`. -/
theorem partialD_one_kPrimeOf (c : FracF p (Fin 2)) (hc : c ∈ kPrimeOf p K) :
    algebraMap _ K (partialD p 1 c) = 0 := by
  obtain ⟨w, hw⟩ := hc
  have h : dx.compAlgebraMap (FracF p (Fin 2)) = dx (algebraMap _ K (var p (1 : Fin 2))) •
      (Algebra.linearMap _ K).compDer (partialD p (1 : Fin 2)) +
        dx (algebraMap _ K (var p (0 : Fin 2))) •
          (Algebra.linearMap _ K).compDer (partialD p (0 : Fin 2)) :=
    derivation_ext p fun i => by fin_cases i <;> simp [partialD_var]
  have h := congrArg (· c) h
  simp [← hw, _root_.frobenius_def, der_pow_char' p, hy, hdx] at h
  by_contra hne
  refine hy' (-(partialD p 0 c) / partialD p 1 c) ?_
  rw [map_div₀, map_neg, neg_div, eq_comm, eq_neg_iff_add_eq_zero, add_div' _ _ _ hne,
    div_eq_zero_iff]
  exact Or.inl (by linear_combination -h)

/-- `∂/∂y : k → K` as a `k'`-derivation. -/
noncomputable def deltaOf : Derivation (kPrimeOf p K) (FracF p (Fin 2)) K where
  toFun := (Algebra.linearMap (FracF p (Fin 2)) K).compDer (partialD p 1)
  map_add' := map_add _
  map_smul' c z := by
    rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz,
      show (Algebra.linearMap (FracF p (Fin 2)) K).compDer (partialD p 1)
          (algebraMap (kPrimeOf p K) (FracF p (Fin 2)) c) = 0 from
        partialD_one_kPrimeOf p y' hy hy' dx hdx _ c.2, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := Derivation.map_one_eq_zero _
  leibniz' := Derivation.leibniz _

include hy hy' hdx in
/-- `K ⊗_k Ω_{k/k'} → Ω_{K/k'}` is not injective: `dy − y' dx` is a nonzero element of its
kernel. -/
theorem not_injective_of :
    ¬ Function.Injective (KaehlerDifferential.mapBaseChange (kPrimeOf p K) (FracF p (Fin 2)) K) := by
  intro hinj
  let ω : K ⊗[FracF p (Fin 2)] Ω[FracF p (Fin 2)⁄kPrimeOf p K] :=
    (1 : K) ⊗ₜ KaehlerDifferential.D _ _ (var p (1 : Fin 2)) -
      y' ⊗ₜ KaehlerDifferential.D _ _ (var p (0 : Fin 2))
  have h0 : KaehlerDifferential.mapBaseChange _ _ K ω = 0 := by
    simp [ω, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hy]
  have h1 : (deltaOf p y' hy hy' dx hdx).liftKaehlerDifferential.liftBaseChange K ω = 1 := by
    simp [ω, deltaOf, partialD_var]
  rw [hinj (h0.trans (map_zero _).symm), map_zero] at h1
  exact zero_ne_one h1

include hy hy' hdx in
/-- The same, without `Ω_{k/k'}`: `dy − y' dx` lies in the kernel of `K ⊗_k Ω_k → Ω_K` but not in
the `K`-span of the `1 ⊗ dc`, `c ∈ k ∩ Kᵖ`. -/
theorem ker_not_span :
    KaehlerDifferential.mapBaseChange (ZMod p) (FracF p (Fin 2)) K
        ((1 : K) ⊗ₜ KaehlerDifferential.D _ _ (var p (1 : Fin 2)) -
          y' ⊗ₜ KaehlerDifferential.D _ _ (var p (0 : Fin 2))) = 0 ∧
      (1 : K) ⊗ₜ KaehlerDifferential.D _ _ (var p (1 : Fin 2)) -
          y' ⊗ₜ KaehlerDifferential.D _ _ (var p (0 : Fin 2)) ∉
        Submodule.span K (Set.range fun c : kPrimeOf p K =>
          (1 : K) ⊗ₜ[FracF p (Fin 2)] KaehlerDifferential.D (ZMod p) _ (c : FracF p (Fin 2))) := by
  refine ⟨by simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hy],
    fun h => ?_⟩
  let L := ((Algebra.linearMap (FracF p (Fin 2)) K).compDer
    (partialD p 1)).liftKaehlerDifferential.liftBaseChange K
  have hL : Submodule.span K (Set.range fun c : kPrimeOf p K =>
      (1 : K) ⊗ₜ[FracF p (Fin 2)] KaehlerDifferential.D (ZMod p) _ (c : FracF p (Fin 2))) ≤
        LinearMap.ker L := Submodule.span_le.2 <| Set.range_subset_iff.2 fun c => by
    simpa [L] using partialD_one_kPrimeOf p y' hy hy' dx hdx _ c.2
  simpa [L, partialD_var] using hL h

/-! #### `Ω_{K/k'} = Ω_K` -/

/-- The `𝔽_p`-algebra `k'`, with the `𝔽_p`-action it already has. -/
noncomputable instance : Algebra (ZMod p) (kPrimeOf p K) :=
  .ofModule (fun r x y => Subtype.ext (smul_mul_assoc r (x : FracF p (Fin 2)) y))
    fun r x y => Subtype.ext (mul_smul_comm r (x : FracF p (Fin 2)) y)

instance : IsScalarTower (ZMod p) (kPrimeOf p K) K :=
  .of_algebraMap_eq <| RingHom.congr_fun <| RingHom.ext_zmod (algebraMap (ZMod p) K)
    ((algebraMap (kPrimeOf p K) K).comp (algebraMap (ZMod p) (kPrimeOf p K)))

omit [IsScalarTower (ZMod p) (FracF p (Fin 2)) K] in
variable (K) in
/-- `Ω_K → Ω_{K/k'}` is bijective, `k'` consisting of `p`-th powers. -/
theorem omega_kPrimeOf_bijective :
    Function.Bijective (KaehlerDifferential.map (ZMod p) (kPrimeOf p K) K K) :=
  map_bijective_of_pow p _ _ _ fun c => c.2

variable (K) in
/-- `Ω_K ≅ Ω_{K/k'}`. -/
noncomputable def omegaEquiv : Ω[K⁄ZMod p] ≃ₗ[K] Ω[K⁄kPrimeOf p K] :=
  .ofBijective _ (omega_kPrimeOf_bijective p K)

include hy hy' hdx in
/-- **The counterexample as the page states it**: `Ω_{k/k'} ⊗_k K → Ω_K` is not injective. -/
theorem not_injective_to_omega :
    ¬ Function.Injective ((omegaEquiv p K).symm.toLinearMap.restrictScalars (FracF p (Fin 2)) ∘ₗ
      (KaehlerDifferential.mapBaseChange (kPrimeOf p K) (FracF p (Fin 2)) K).restrictScalars _) :=
  fun h => not_injective_of p y' hy hy' dx hdx fun a b hab => @h a b (by simp [hab])

end ContreGeneral

/-! #### The general example: `K = 𝔽_p(x, b₀, …, b_{p−1})`, `y = Σ a_i xⁱ`, `a_i = b_iᵖ` -/

section Generale

open MvPolynomial

variable (p : ℕ)

/-- `y = Σ b_iᵖ xⁱ` in `𝔽_p[x, b₀, …, b_{p−1}]`, the variable `none` being `x`. -/
noncomputable def yG : MvPolynomial (Option (Fin p)) (ZMod p) :=
  ∑ i : Fin p, X (some i) ^ p * X none ^ (i : ℕ)

/-- `y' = ∂y/∂x = Σ i b_iᵖ xⁱ⁻¹`. -/
noncomputable def y'G : MvPolynomial (Option (Fin p)) (ZMod p) :=
  ∑ i : Fin p, X (some i) ^ p *
    (((i : ℕ) : MvPolynomial (Option (Fin p)) (ZMod p)) * X none ^ ((i : ℕ) - 1))

/-- `(x, y, y')`. -/
noncomputable def tripleG : Fin 3 → MvPolynomial (Option (Fin p)) (ZMod p) := ![X none, yG p, y'G p]

/-- The specialisation `b₀ ↦ X₁`, `b₁ ↦ X₂`, `b_i ↦ 0` for `i ≥ 2`, which sends `(x, y, y')` to
`triple p`. -/
noncomputable def spec :
    MvPolynomial (Option (Fin p)) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
  aeval fun o => o.elim (X 0) fun i => if (i : ℕ) = 0 then X 1 else if (i : ℕ) = 1 then X 2 else 0

variable [hp : Fact p.Prime]

/-- A sum over `Fin p` of terms vanishing outside `0, 1`. -/
theorem sum_fin_two {M : Type*} [AddCommMonoid M] (f : Fin p → M)
    (hf : ∀ i : Fin p, (i : ℕ) ≠ 0 → (i : ℕ) ≠ 1 → f i = 0) :
    ∑ i, f i = f ⟨0, hp.out.pos⟩ + f ⟨1, hp.out.one_lt⟩ :=
  Finset.sum_eq_add_of_mem _ _ (Finset.mem_univ _) (Finset.mem_univ _) (by simp [Fin.ext_iff])
    fun i _ hi => hf i (fun h => hi.1 (Fin.ext h)) fun h => hi.2 (Fin.ext h)

theorem spec_comp : (spec p).comp (aeval (tripleG p)) = aeval (triple p) := by
  refine algHom_ext fun i => ?_
  fin_cases i <;> simp only [AlgHom.comp_apply, aeval_X]
  · simp [spec, tripleG, triple]
  all_goals
    simp only [tripleG, yG, y'G, Fin.reduceFinMk, Matrix.cons_val, map_sum]
    rw [sum_fin_two p]
    · simp [spec, triple]
    · intro i h0 h1
      simp only [spec, map_mul, map_pow, aeval_X, Option.elim_some, h0, h1, ↓reduceIte,
        zero_pow hp.out.ne_zero, zero_mul]

/-- `x, y, y'` are algebraically independent: specialising gives `triple p`. -/
theorem tripleG_injective : Function.Injective (aeval (R := ZMod p) (tripleG p)) :=
  .of_comp (f := spec p) (by rw [← AlgHom.coe_comp, spec_comp]; exact triple_injective p hp.out.pos)

/-- `K = 𝔽_p(x, b₀, …, b_{p−1})`. -/
abbrev KG := FracF p (Option (Fin p))

/-- `𝔽_p[X, Y] → K`, `X ↦ x`, `Y ↦ y`. -/
noncomputable def phiG : MvPolynomial (Fin 2) (ZMod p) →ₐ[ZMod p] KG p :=
  (IsScalarTower.toAlgHom _ _ _).comp ((aeval (tripleG p)).comp (rename Fin.castSucc))

theorem phiG_injective : Function.Injective (phiG p) :=
  (IsFractionRing.injective _ _).comp
    ((tripleG_injective p).comp (rename_injective _ (Fin.castSucc_injective 2)))

noncomputable instance : Algebra (FracF p (Fin 2)) (KG p) :=
  (IsFractionRing.liftAlgHom (phiG_injective p)).toRingHom.toAlgebra

instance : IsScalarTower (ZMod p) (FracF p (Fin 2)) (KG p) :=
  .of_algebraMap_eq fun c => ((IsFractionRing.liftAlgHom (phiG_injective p)).commutes c).symm

theorem algebraMap_KG (f : MvPolynomial (Fin 2) (ZMod p)) :
    algebraMap (FracF p (Fin 2)) (KG p) (algebraMap _ _ f) =
      algebraMap _ _ (aeval (tripleG p) (rename Fin.castSucc f)) :=
  IsFractionRing.lift_algebraMap (phiG_injective p) f

/-- `D y = y' D x` for every derivation of `K`: the `a_i` are `p`-th powers. -/
theorem der_yG {R M : Type} [CommRing R] [Algebra R (KG p)] [AddCommGroup M] [Module (KG p) M]
    [Module R M] (D : Derivation R (KG p) M) :
    D (algebraMap _ (KG p) (var p (1 : Fin 2))) =
      algebraMap _ (KG p) (y'G p) • D (algebraMap _ (KG p) (var p (0 : Fin 2))) := by
  simp only [algebraMap_KG, rename_X, aeval_X]
  change D (algebraMap _ (KG p) (yG p)) = algebraMap _ _ (y'G p) • D (algebraMap _ _ (X none))
  simp only [yG, y'G, map_sum, map_mul, map_pow, map_natCast, Derivation.leibniz,
    der_pow_char' p, smul_zero, add_zero, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.leibniz_pow, mul_smul, mul_smul, ← Nat.cast_smul_eq_nsmul (KG p)]

/-- `y' ∉ k`: from the algebraic independence of `x, y, y'`. -/
theorem y'G_not_mem (z : FracF p (Fin 2)) : algebraMap _ (KG p) z ≠ algebraMap _ _ (y'G p) := by
  intro hz
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 2) (ZMod p)) z
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hB : algebraMap _ (KG p) (aeval (tripleG p) (rename Fin.castSucc g)) ≠ 0 :=
    fun h => hg0 (phiG_injective p (h.trans (map_zero _).symm))
  rw [map_div₀, algebraMap_KG, algebraMap_KG, div_eq_iff hB, ← map_mul] at hz
  have key : aeval (tripleG p) (rename Fin.castSucc f) =
      aeval (tripleG p) (X 2 * rename Fin.castSucc g) := by
    apply IsFractionRing.injective (MvPolynomial (Option (Fin p)) (ZMod p)) (KG p)
    rw [hz, map_mul (aeval _), aeval_X]
    rfl
  replace key := tripleG_injective p key
  let π : MvPolynomial (Fin 3) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p) :=
    aeval ![X 0, X 1, 0]
  have hπ : π.comp (rename Fin.castSucc) = rename Fin.castSucc := by
    ext i; fin_cases i <;> simp [π]
  have hf : rename Fin.castSucc f = (0 : MvPolynomial (Fin 3) (ZMod p)) := by
    have := congrArg π key
    rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hπ] at this
    simpa [π] using this
  rw [hf, eq_comm, mul_eq_zero, or_iff_right (X_ne_zero 2)] at key
  exact hg0 (rename_injective _ (Fin.castSucc_injective 2) (key.trans (map_zero _).symm))

theorem partialD_x : partialD p (none : Option (Fin p))
    (algebraMap _ (KG p) (var p (0 : Fin 2))) = 1 := by
  simp [algebraMap_KG, tripleG, partialD_var]

/-- **The general counterexample of pages 26 and 28.** For
`K = 𝔽_p(x, b₀, …, b_{p−1})`, `a_i = b_iᵖ`, `y = Σ a_i xⁱ`, `k = 𝔽_p(x, y)` and
`k' = k ∩ Kᵖ`, the map `Ω_{k/k'} ⊗_k K → Ω_K` is not injective. -/
theorem contre_exemple_general :
    ¬ Function.Injective ((omegaEquiv p (KG p)).symm.toLinearMap.restrictScalars (FracF p (Fin 2)) ∘ₗ
      (KaehlerDifferential.mapBaseChange (kPrimeOf p (KG p)) (FracF p (Fin 2)) (KG p)).restrictScalars
        _) :=
  not_injective_to_omega p _ (der_yG p) (y'G_not_mem p) _ (partialD_x p)

/-- Equivalently, the kernel of `K ⊗_k Ω_k → Ω_K` is not generated by the `dc`, `c ∈ k ∩ Kᵖ`:
`dy − y' dx` is in it and not in their span. -/
theorem contre_exemple_general_span :
    KaehlerDifferential.mapBaseChange (ZMod p) (FracF p (Fin 2)) (KG p)
        ((1 : KG p) ⊗ₜ KaehlerDifferential.D _ _ (var p (1 : Fin 2)) -
          algebraMap _ _ (y'G p) ⊗ₜ KaehlerDifferential.D _ _ (var p (0 : Fin 2))) = 0 ∧
      (1 : KG p) ⊗ₜ KaehlerDifferential.D _ _ (var p (1 : Fin 2)) -
          algebraMap _ _ (y'G p) ⊗ₜ KaehlerDifferential.D _ _ (var p (0 : Fin 2)) ∉
        Submodule.span (KG p) (Set.range fun c : kPrimeOf p (KG p) =>
          (1 : KG p) ⊗ₜ[FracF p (Fin 2)] KaehlerDifferential.D (ZMod p) _ (c : FracF p (Fin 2))) :=
  ker_not_span p _ (der_yG p) (y'G_not_mem p) _ (partialD_x p)

end Generale

end Grothendieck.Folder22
