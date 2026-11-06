module

public import Mathlib

public section


/-!
# Folder 55, page 13: Lemme B, the identity principle and noetherianity

Page 13 of folder 55 states, without proof, a « Lemme B »: let `X` be a ringed space which is
quasi-compact (i), with coherent structure sheaf (ii), noetherian local rings (iv), and which
satisfies an *identity principle* (v): for every coherent Ideal `𝒥`, with
`Y = (Supp 𝒪_X/𝒥, 𝒪_X/𝒥)`, every `y ∈ Y` where `𝒪_{Y,y}` is a domain has an open
neighbourhood `U` in `Y` on which every section of `𝒪_Y` vanishing near `y` vanishes. Then
every increasing sequence of coherent subsheaves of a coherent sheaf is stationary; and
(corollary, with Lemme A of page 5) `A = Γ(X, 𝒪_X)` is noetherian. See the modernised reading
`transcripts/55/55.modern.tex`, section « Le lemme B ».

Mathlib has no coherent sheaves on a ringed space, so this file proves the two steps of the
argument that do not depend on them, in a model where a subsheaf is a family of sets of
sections, stable under restriction and local:

* `stationary_of_locally_stationary`: on a quasi-compact space, an increasing sequence of
  subsheaves which is eventually constant on some neighbourhood of every point is eventually
  constant (the use of (i));
* `stationary_of_germs`: if at every point the germs stabilise (what (iv) gives, the stalk of
  a coherent sheaf being a finitely generated module over a noetherian ring, see
  `germs_stabilize_of_noetherian`) and if equality of germs at `x` with a given term propagates
  to a *uniform* neighbourhood of `x` (the role the reading gives to (v)), the sequence is
  stationary — Lemme B, with (v) replaced by this uniformity;
* `isNoetherianRing_of_tilde`: the corollary — if finitely generated ideals `I` of a ring `A`
  go to members `Ĩ` of a class of objects with the ascending chain condition, monotonically and
  with `Γ(Ĩ) = I` (what Lemme A and its Corollaire 1 give), then `A` is noetherian;
* `not_stationary_without_uniformity`: the uniformity cannot be dropped — on `ℕ ∪ {∞}`, an
  increasing sequence of subsheaves whose germs stabilise everywhere but which accumulates
  at `∞` is not stationary.

Not formalised: that (v) implies the uniformity hypothesis of `stationary_of_germs` (the core of
Lemme B, which needs coherent sheaves, supports of `𝒪/𝒥` and a primary decomposition at the
stalk); the page gives no proof of it, and it is not checked here that (i)–(v) suffice for an
arbitrary ringed space.
-/

open CategoryTheory TopologicalSpace Opposite

namespace Grothendieck.Folder55

universe u

variable {X : TopCat.{u}} {F : TopCat.Presheaf (Type u) X}

/-- A subsheaf of a presheaf of types `F`: for each open `U` a set of sections over `U`,
stable under restriction, and *local* — a section lies in it as soon as it does locally. -/
structure Subsheaf (F : TopCat.Presheaf (Type u) X) where
  /-- The sections over `U` lying in the subsheaf. -/
  sections : ∀ U : Opens X, Set (F.obj (op U))
  restrict : ∀ {U V : Opens X} (h : V ≤ U) {s : F.obj (op U)},
    s ∈ sections U → F.map (homOfLE h).op s ∈ sections V
  isLocal : ∀ (U : Opens X) (s : F.obj (op U)),
    (∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ F.map (homOfLE h).op s ∈ sections V) →
      s ∈ sections U

namespace Subsheaf

@[ext]
theorem ext {S T : Subsheaf F} (h : ∀ U, S.sections U = T.sections U) : S = T := by
  cases S; cases T; congr; exact funext h

instance : PartialOrder (Subsheaf F) where
  le S T := ∀ U, S.sections U ⊆ T.sections U
  le_refl _ _ := subset_rfl
  le_trans _ _ _ h₁ h₂ U := (h₁ U).trans (h₂ U)
  le_antisymm _ _ h₁ h₂ := ext fun U => (h₁ U).antisymm (h₂ U)

theorem le_def {S T : Subsheaf F} : S ≤ T ↔ ∀ U, S.sections U ⊆ T.sections U := Iff.rfl

/-- `S` and `T` agree on the open `W`: they have the same sections over every open of `W`. -/
def AgreeOn (S T : Subsheaf F) (W : Opens X) : Prop :=
  ∀ V : Opens X, V ≤ W → S.sections V = T.sections V

/-- The germs at `x` of the sections of `S`, a subset of the stalk `F_x`. -/
def germs (S : Subsheaf F) (x : X) : Set (F.stalk x) :=
  {g | ∃ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)), s ∈ S.sections U ∧ F.germ U x hx s = g}

theorem germs_mono {S T : Subsheaf F} (h : S ≤ T) (x : X) : S.germs x ⊆ T.germs x := by
  rintro g ⟨U, hx, s, hs, rfl⟩
  exact ⟨U, hx, s, h U hs, rfl⟩

end Subsheaf

open Subsheaf

/-- **Quasi-compactness step of Lemme B.** On a quasi-compact space, an increasing sequence of
subsheaves which, near every point, is eventually constant on some open neighbourhood, is
eventually constant. -/
theorem stationary_of_locally_stationary [CompactSpace X] (S : ℕ → Subsheaf F)
    (hS : Monotone S)
    (hloc : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∃ k₀, ∀ k ≥ k₀, AgreeOn (S k) (S k₀) W) :
    ∃ k₀, ∀ k ≥ k₀, S k = S k₀ := by
  choose W hxW k hk using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨t.sup k, fun K hK => le_antisymm ?_ (hS hK)⟩
  intro U s hs
  refine (S (t.sup k)).isLocal U s fun y hy => ?_
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hkx : k x ≤ t.sup k := Finset.le_sup hxt
  refine ⟨U ⊓ W x, inf_le_left, ⟨hy, hyx⟩, ?_⟩
  exact hS hkx _ (hk x K (hkx.trans hK) _ inf_le_right ▸ (S K).restrict inf_le_left hs)

/-- **Lemme B, with the identity principle replaced by the uniformity it is meant to give.**
On a quasi-compact space, let `S` be an increasing sequence of subsheaves. Suppose that
* at every point the germs stabilise (hypothesis (iv): see `germs_stabilize_of_noetherian`);
* (uniformity) for every point `x` and every index `k`, there is an open neighbourhood `W` of
  `x` such that every later `S l` with the same germs at `x` as `S k` agrees with `S k` on `W`.
Then the sequence is stationary. -/
theorem stationary_of_germs [CompactSpace X] (S : ℕ → Subsheaf F) (hS : Monotone S)
    (hgerm : ∀ x : X, ∃ k₀, ∀ k ≥ k₀, (S k).germs x = (S k₀).germs x)
    (huniform : ∀ (x : X) (k : ℕ), ∃ W : Opens X, x ∈ W ∧
      ∀ l ≥ k, (S l).germs x = (S k).germs x → AgreeOn (S l) (S k) W) :
    ∃ k₀, ∀ k ≥ k₀, S k = S k₀ := by
  refine stationary_of_locally_stationary S hS fun x => ?_
  obtain ⟨k₀, hk₀⟩ := hgerm x
  obtain ⟨W, hxW, hW⟩ := huniform x k₀
  exact ⟨W, hxW, k₀, fun l hl => hW l hl (hk₀ l hl)⟩

/-- **Hypothesis (iv) gives the stabilisation of germs.** If the germs of the `S k` at `x` are
read off submodules `G k` of a noetherian module (the stalk of a coherent sheaf over the
noetherian ring `𝒪_{X,x}`), increasing in `k`, they stabilise. -/
theorem germs_stabilize_of_noetherian {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] (S : ℕ → Subsheaf F) (x : X) (G : ℕ → Submodule R M) (hG : Monotone G)
    (Φ : Submodule R M → Set (F.stalk x)) (hΦ : ∀ k, (S k).germs x = Φ (G k)) :
    ∃ k₀, ∀ k ≥ k₀, (S k).germs x = (S k₀).germs x := by
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance ⟨G, hG⟩
  exact ⟨n, fun k hk => by rw [hΦ, hΦ]; exact congrArg Φ (hn k hk).symm⟩

/-- **The corollary of Lemme B: `Γ(X, 𝒪_X)` is noetherian.** Let `C` be a class of objects of
a partially ordered type (the coherent subsheaves of `𝒪_X`) in which every increasing sequence
is stationary (Lemme B). If every finitely generated ideal `I` of `A` gives a member `Ĩ` of `C`,
monotonically, with `Γ(Ĩ) = I` (Lemme A and its Corollaire 1), then `A` is noetherian. -/
theorem isNoetherianRing_of_tilde {A P : Type*} [CommRing A] [PartialOrder P] (C : P → Prop)
    (hB : ∀ s : ℕ → P, Monotone s → (∀ k, C (s k)) → ∃ k₀, ∀ k ≥ k₀, s k = s k₀)
    (tilde : Ideal A → P) (Γ : P → Ideal A)
    (htilde_mono : ∀ I J : Ideal A, I.FG → J.FG → I ≤ J → tilde I ≤ tilde J)
    (htilde_mem : ∀ I : Ideal A, I.FG → C (tilde I))
    (hΓ : ∀ I : Ideal A, I.FG → Γ (tilde I) = I) :
    IsNoetherianRing A := by
  refine isNoetherian_iff_fg_wellFounded.2 (wellFoundedGT_iff_monotone_chain_condition.2 fun a => ?_)
  obtain ⟨k₀, hk₀⟩ := hB (fun k => tilde (a k).1)
    (fun i j hij => htilde_mono _ _ (a i).2 (a j).2 (a.mono hij)) (fun k => htilde_mem _ (a k).2)
  exact ⟨k₀, fun m hm => Subtype.ext <| by rw [← hΓ _ (a k₀).2, ← hΓ _ (a m).2, hk₀ m hm]⟩

/-! ### Without the uniformity, quasi-compactness and stabilisation of germs do not suffice

On the one-point compactification `ℕ ∪ {∞}` (quasi-compact), with `F` the sheaf of all
`Bool`-valued functions, let `S k` be the subsheaf of functions which are `true` only at the
points `0, …, k - 1`. The germs stabilise at every point (from `0` at `∞`, from `n + 1` at `n`),
but the sequence is strictly increasing: the subsheaves accumulate at `∞`, the situation the
identity principle (v) is there to exclude. -/

/-- The one-point compactification of `ℕ`, as a topological space. -/
abbrev Npt : TopCat := TopCat.of (OnePoint ℕ)

/-- The sheaf of all `Bool`-valued functions on `ℕ ∪ {∞}`. -/
abbrev boolFun : TopCat.Presheaf Type Npt := TopCat.presheafToTypes Npt (fun _ => Bool)

/-- `accumulating k`: the functions which are `true` only at points `n < k`. -/
def accumulating (k : ℕ) : Subsheaf boolFun where
  sections U := {f | ∀ y : U, f y = true → ∃ n < k, (y : OnePoint ℕ) = (n : OnePoint ℕ)}
  restrict h f hf y hy := hf _ hy
  isLocal U f hf y hy := by
    obtain ⟨V, hVU, hyV, hV⟩ := hf y y.2
    exact hV ⟨y, hyV⟩ hy

theorem accumulating_mono : Monotone accumulating := by
  intro k l hkl U f hf y hy
  obtain ⟨n, hn, h⟩ := hf y hy
  exact ⟨n, hn.trans_le hkl, h⟩

/-- The germs of `accumulating` stabilise at every point of `ℕ ∪ {∞}`. -/
theorem accumulating_germs (x : Npt) :
    ∃ k₀, ∀ k ≥ k₀, (accumulating k).germs x = (accumulating k₀).germs x := by
  -- an open neighbourhood `W` of `x` on which every section of every `accumulating k` lies in
  -- `accumulating k₀`
  have key : ∃ k₀, ∀ k, ∃ W : Opens Npt, x ∈ W ∧ ∀ (U : Opens Npt) (f : boolFun.obj (op U)),
      f ∈ (accumulating k).sections U →
        boolFun.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op f ∈
          (accumulating k₀).sections (U ⊓ W) := by
    induction x using OnePoint.rec with
    | infty =>
      refine ⟨0, fun k => ⟨⟨(((↑) : ℕ → OnePoint ℕ) '' Set.Iio k)ᶜ,
        ((Set.finite_Iio k).image _).isClosed.isOpen_compl⟩, ?_, ?_⟩⟩
      · rintro ⟨n, -, hn⟩
        exact OnePoint.coe_ne_infty n hn
      · intro U f hf y hy
        exfalso
        obtain ⟨n, hn, hyn⟩ := hf ⟨y, y.2.1⟩ hy
        exact y.2.2 ⟨n, hn, hyn.symm⟩
    | coe n =>
      refine ⟨n + 1, fun k => ⟨⟨{(n : OnePoint ℕ)}, ?_⟩, rfl, ?_⟩⟩
      · simpa [Set.image_singleton] using
          (OnePoint.isOpen_image_coe (s := ({n} : Set ℕ))).2 (isOpen_discrete _)
      · intro U f hf y hy
        exact ⟨n, Nat.lt_succ_self n, y.2.2⟩
  obtain ⟨k₀, hkey⟩ := key
  refine ⟨k₀, fun k hk => le_antisymm ?_ (germs_mono (accumulating_mono hk) x)⟩
  rintro g ⟨U, hx, f, hf, rfl⟩
  obtain ⟨W, hxW, hW⟩ := hkey k
  have hxUW : x ∈ U ⊓ W := ⟨hx, hxW⟩
  exact ⟨U ⊓ W, hxUW, _, hW U f hf, boolFun.germ_res_apply _ x hxUW f⟩

/-- The sequence `accumulating` is not stationary. -/
theorem accumulating_not_stationary : ¬ ∃ k₀, ∀ k ≥ k₀, accumulating k = accumulating k₀ := by
  classical
  rintro ⟨k₀, hk₀⟩
  have h := hk₀ (k₀ + 1) (Nat.le_succ k₀)
  let f : boolFun.obj (op ⊤) := fun y => decide ((y : OnePoint ℕ) = (k₀ : OnePoint ℕ))
  have hf : f ∈ (accumulating (k₀ + 1)).sections ⊤ := fun y hy =>
    ⟨k₀, Nat.lt_succ_self k₀, of_decide_eq_true hy⟩
  rw [h] at hf
  obtain ⟨n, hn, hy⟩ := hf ⟨(k₀ : OnePoint ℕ), trivial⟩ (decide_eq_true rfl)
  exact absurd (OnePoint.coe_injective hy) (Nat.ne_of_gt hn)

/-- **The identity principle cannot be dropped**: on a quasi-compact space, an increasing
sequence of subsheaves whose germs stabilise at every point need not be stationary. -/
theorem not_stationary_without_uniformity :
    ∃ (X : TopCat) (_ : CompactSpace X) (F : TopCat.Presheaf Type X) (S : ℕ → Subsheaf F),
      Monotone S ∧ (∀ x : X, ∃ k₀, ∀ k ≥ k₀, (S k).germs x = (S k₀).germs x) ∧
        ¬ ∃ k₀, ∀ k ≥ k₀, S k = S k₀ :=
  ⟨Npt, inferInstanceAs (CompactSpace (OnePoint ℕ)), boolFun, accumulating, accumulating_mono,
    accumulating_germs, accumulating_not_stationary⟩

end Grothendieck.Folder55
