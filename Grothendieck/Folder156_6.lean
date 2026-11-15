module

public import Mathlib
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section


/-!
# Folder 156-6, pages 40, 44 and 49–50: closed parts, the lemma on `φ ↦ φ⁻¹`, trivial ateliers

The modernised reading `transcripts/156-6/156-6.modern.tex` (chapter VI, « Analysis situs
(deuxième mouture) », 18–22 June 1986) works throughout with an ordered set and its *closed*
(= down-closed) parts, the closed sets of the Alexandrov topology of the order. Three statements
of the folder are proved here.

**Page 49, the Lemma.** For two ordered sets `I`, `I'`, the map `φ ↦ φ⁻¹` from increasing maps
`I → I'` to maps `𝔓_f(I') → 𝔓_f(I)` between closed parts is injective, and its image is formed
of the maps commuting with arbitrary unions and intersections. The page first wrote
« préordonnés » and struck the « pré ».

* `pull_iSup₂`, `pull_iInf₂`: `φ⁻¹` commutes with arbitrary unions and intersections.
* `pull_injective`: `φ ↦ φ⁻¹` is injective when `I'` is ordered.
* `exists_pull`: every map of closed parts commuting with arbitrary unions and intersections is
  a `φ⁻¹` — `I'` may be a mere preorder here.
* `Indisc`, `not_pull_injective_preorder`: for a preorder injectivity fails (a two-point set
  where each point is `≤` the other; the identity and the exchange have the same `φ⁻¹`). The
  struck « pré » is needed.
* `topOnly`, `topOnly_sInf`, `topOnly_sup`, `topOnly_bot`, `topOnly_ne_pull`: on `ℕ`, the map
  `𝔓_f(ℕ) → 𝔓_f(pt)` sending `ℕ` to the point and every other closed part to `∅` commutes with
  arbitrary intersections and finite unions but is no `φ⁻¹`. « Arbitrary » unions cannot be
  weakened to finite ones without passing, as the page's margin does, to the sobrification of
  `I'`: the closed part `ℕ` is irreducible without a generic point.

**Page 40, the Example.** In `𝔉 = 𝔓(I)` ordered by inclusion, a closed part is a family of parts
stable under passing to parts — an abstract simplicial complex — and it is *spécieuse* (stable
under the unions of families bounded in `𝔉`, i.e. of all families) iff it is `𝔓(I')` for a part
`I'` of `I`.

* `specious_iff`: the equivalence, for any set `I`.
* `finset_mem_of_union`, `specious_of_union`: when `I` is finite, stability under the union of
  two simplices suffices, as the page says (« la réunion de simplexes est un simplexe »).
* `finite_parts_not_specious`: for `I = ℕ` it does not; the finite parts of `ℕ` are stable
  under binary unions without being any `𝔓(I')`. The page's restriction « du moins si `I` est
  fini » is needed.

**Pages 44 and 49–50, the trivial ateliers.** Page 44 builds an atelier from any ordered set
`(𝓜, ≤)` by taking `≪ := ≤`; its lieux are then the minimal elements, and the small shadow of a
multistrate `Y` is `omb Y = {x minimal | x ≤ Y}`. The axiom of lieux At 8 (page 45) asks that
every `X` have a lieu `x ∈ omb X` lying in no `omb Y`, `Y < X`. Page 49 renders it as « `x`
minimal, `x ≤ X`, `∄ Y` with `x ≤ Y < X` » and calls it « des plus restrictives ».

* `at8_iff`, `at8_iff_discrete`: At 8 holds in a trivial atelier iff every element of `𝓜` is
  minimal, i.e. iff `≤` is equality.
* `at8Cover_not_at8`: the « successeur » reading (`x` covered by `X`: no `Y` with
  `x < Y < X`), which the page's parenthesis seems to intend, is strictly weaker; the chain
  `false < true` satisfies it and not At 8.

**What the formalisation finds.** The Lemma of page 49 holds as the reading states it, for
ordered sets, and only for them: the struck « pré » is confirmed, and the hypothesis on
arbitrary unions cannot be weakened to finite ones. Existence needs no antisymmetry on `I'`;
only uniqueness does. The Example of page 40 holds, and its restriction to a finite `I` is
needed for the binary form. At 8 forces a trivial atelier to be discrete, as the reading's
footnote says: « des plus restrictives » understates it. The ateliers themselves (At 1–At 7,
figures, `≪` on `𝔉`) are not encoded; only the ordered sets and their closed parts are.
-/

namespace Grothendieck.Folder156_6

section Lemma49

variable {I I' : Type*} [Preorder I] [Preorder I']

/-- `φ⁻¹` on closed parts, for `φ` increasing. -/
def pull (φ : I → I') (hφ : Monotone φ) (A : LowerSet I') : LowerSet I :=
  ⟨φ ⁻¹' A, A.lower.preimage hφ⟩

@[simp] theorem mem_pull {φ : I → I'} {hφ : Monotone φ} {A : LowerSet I'} {x : I} :
    x ∈ pull φ hφ A ↔ φ x ∈ A := Iff.rfl

/-- `φ⁻¹` commutes with arbitrary unions of closed parts. -/
theorem pull_iSup₂ (φ : I → I') (hφ : Monotone φ) (S : Set (LowerSet I')) :
    pull φ hφ (sSup S) = ⨆ A ∈ S, pull φ hφ A := by
  ext x; simp

/-- `φ⁻¹` commutes with arbitrary intersections of closed parts. -/
theorem pull_iInf₂ (φ : I → I') (hφ : Monotone φ) (S : Set (LowerSet I')) :
    pull φ hφ (sInf S) = ⨅ A ∈ S, pull φ hφ A := by
  ext x; simp

/-- Page 49, injectivity: for `I'` ordered, `φ` is determined by `φ⁻¹`. -/
theorem pull_injective {I' : Type*} [PartialOrder I'] {φ ψ : I → I'} (hφ : Monotone φ)
    (hψ : Monotone ψ) (h : pull φ hφ = pull ψ hψ) : φ = ψ := by
  funext x
  have h1 : φ x ∈ LowerSet.Iic (ψ x) := by
    change x ∈ pull φ hφ (LowerSet.Iic (ψ x)); rw [h]; exact LowerSet.mem_Iic_iff.2 le_rfl
  have h2 : ψ x ∈ LowerSet.Iic (φ x) := by
    change x ∈ pull ψ hψ (LowerSet.Iic (φ x)); rw [← h]; exact LowerSet.mem_Iic_iff.2 le_rfl
  exact le_antisymm (LowerSet.mem_Iic_iff.1 h1) (LowerSet.mem_Iic_iff.1 h2)

/-- Page 49, the image: a map of closed parts commuting with arbitrary unions and intersections
is `φ⁻¹` for an increasing `φ`. -/
theorem exists_pull (g : LowerSet I' → LowerSet I)
    (hsup : ∀ S : Set (LowerSet I'), g (sSup S) = ⨆ A ∈ S, g A)
    (hinf : ∀ S : Set (LowerSet I'), g (sInf S) = ⨅ A ∈ S, g A) :
    ∃ (φ : I → I') (hφ : Monotone φ), g = pull φ hφ := by
  -- `g` is increasing
  have gmono : ∀ {A B : LowerSet I'}, A ≤ B → g A ≤ g B := by
    intro A B hAB
    have : g (sInf {A, B}) = g A ⊓ g B := by rw [hinf, iInf_pair]
    rw [sInf_pair, inf_eq_left.2 hAB] at this
    rw [this]; exact inf_le_right
  -- the smallest closed part `A x` with `x ∈ g (A x)`
  let A : I → LowerSet I' := fun x => sInf {B | x ∈ g B}
  have hA : ∀ x, x ∈ g (A x) := by
    intro x
    rw [hinf]; simp
  -- `A x` is the union of the `Iic y`, `y ∈ A x`
  have hcov : ∀ B : LowerSet I', B = sSup {C | ∃ y ∈ B, C = LowerSet.Iic y} := by
    intro B; ext z
    simp only [LowerSet.coe_sSup, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · intro hz; exact ⟨_, ⟨z, hz, rfl⟩, LowerSet.mem_Iic_iff.2 le_rfl⟩
    · rintro ⟨C, ⟨y, hy, rfl⟩, hz⟩; exact B.lower (LowerSet.mem_Iic_iff.1 hz) hy
  have hex : ∀ x, ∃ y ∈ A x, x ∈ g (LowerSet.Iic y) := by
    intro x
    have h := hA x
    rw [hcov (A x), hsup] at h
    simp only [LowerSet.mem_iSup₂_iff] at h
    obtain ⟨C, ⟨y, hy, rfl⟩, hx⟩ := h
    exact ⟨y, hy, hx⟩
  choose φ hφA hφg using hex
  have key : ∀ x B, x ∈ g B ↔ φ x ∈ B := by
    intro x B
    constructor
    · intro hx
      have : A x ≤ B := sInf_le hx
      exact this (hφA x)
    · intro hy
      exact gmono (fun z hz => B.lower (LowerSet.mem_Iic_iff.1 hz) hy) (hφg x)
  have hmono : Monotone φ := by
    intro x' x hle
    have : x' ∈ g (LowerSet.Iic (φ x)) :=
      (g _).lower hle ((key x _).2 (LowerSet.mem_Iic_iff.2 le_rfl))
    exact LowerSet.mem_Iic_iff.1 ((key x' _).1 this)
  refine ⟨φ, hmono, funext fun B => ?_⟩
  ext x; exact key x B

end Lemma49

section Preorder

/-- A two-point set where each point is `≤` the other: a preorder that is not an order. -/
def Indisc : Type := Bool

instance : Preorder Indisc where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

/-- For preordered sets the Lemma's injectivity fails: the identity and the exchange of the two
points have the same `φ⁻¹`. -/
theorem not_pull_injective_preorder :
    ∃ (φ ψ : Indisc → Indisc) (hφ : Monotone φ) (hψ : Monotone ψ),
      φ ≠ ψ ∧ pull φ hφ = pull ψ hψ := by
  refine ⟨id, fun b : Bool => !b, fun _ _ _ => trivial, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h
    have := congrFun h true
    exact Bool.noConfusion this
  · funext A; ext x
    exact Iff.intro (fun h => A.lower trivial h) (fun h => A.lower trivial h)

end Preorder

section Sobrification

open scoped Classical in
/-- On `ℕ`: send the closed part `ℕ` to the point, every other closed part to `∅`. -/
noncomputable def topOnly (A : LowerSet ℕ) : LowerSet Unit := if A = ⊤ then ⊤ else ⊥

theorem topOnly_eq_top {A : LowerSet ℕ} : topOnly A = ⊤ ↔ A = ⊤ := by
  unfold topOnly
  split_ifs with h
  · simp [h]
  · refine iff_of_false (fun h' => ?_) h
    have : () ∈ (⊤ : LowerSet Unit) := LowerSet.mem_top
    rw [← h'] at this; exact LowerSet.notMem_bot this

theorem topOnly_eq_bot {A : LowerSet ℕ} (h : A ≠ ⊤) : topOnly A = ⊥ := by
  unfold topOnly; simp [h]

/-- `topOnly` commutes with arbitrary intersections. -/
theorem topOnly_sInf (S : Set (LowerSet ℕ)) : topOnly (sInf S) = ⨅ A ∈ S, topOnly A := by
  by_cases h : sInf S = ⊤
  · rw [topOnly_eq_top.2 h]
    rw [sInf_eq_top] at h
    symm; rw [iInf₂_eq_top]; intro A hA; exact topOnly_eq_top.2 (h A hA)
  · rw [topOnly_eq_bot h]
    rw [sInf_eq_top] at h; simp only [not_forall, exists_prop] at h
    obtain ⟨A, hA, hA'⟩ := h
    symm; refine le_bot_iff.1 ?_
    exact (iInf₂_le A hA).trans (topOnly_eq_bot hA').le

/-- `topOnly` commutes with binary unions. -/
theorem topOnly_sup (A B : LowerSet ℕ) : topOnly (A ⊔ B) = topOnly A ⊔ topOnly B := by
  rcases total_of (· ≤ ·) A B with h | h
  · rw [sup_eq_right.2 h]
    by_cases hA : A = ⊤
    · have hB : B = ⊤ := top_le_iff.1 (hA ▸ h)
      simp [topOnly_eq_top.2 hA, topOnly_eq_top.2 hB]
    · simp [topOnly_eq_bot hA]
  · rw [sup_eq_left.2 h]
    by_cases hB : B = ⊤
    · have hA : A = ⊤ := top_le_iff.1 (hB ▸ h)
      simp [topOnly_eq_top.2 hA, topOnly_eq_top.2 hB]
    · simp [topOnly_eq_bot hB]

/-- `topOnly` commutes with the empty union. -/
theorem topOnly_bot : topOnly ⊥ = ⊥ := topOnly_eq_bot (by
  intro h
  have : (0 : ℕ) ∈ (⊤ : LowerSet ℕ) := LowerSet.mem_top
  rw [← h] at this; exact LowerSet.notMem_bot this)

/-- `topOnly` is not a `φ⁻¹`: arbitrary unions cannot be weakened to finite ones. -/
theorem topOnly_ne_pull (φ : Unit → ℕ) (hφ : Monotone φ) : topOnly ≠ pull φ hφ := by
  intro h
  have h1 : pull φ hφ (LowerSet.Iic (φ ())) = ⊤ := by
    ext u; simp
  rw [← h, topOnly_eq_top] at h1
  have : φ () + 1 ∈ LowerSet.Iic (φ ()) := by rw [h1]; exact LowerSet.mem_top
  exact absurd (LowerSet.mem_Iic_iff.1 this) (by omega)

end Sobrification

section Example40

variable {I : Type*}

/-- A family of parts of `I` closed in `𝔓(I)`: stable under passing to parts. -/
def IsClosedFamily (K : Set (Set I)) : Prop := ∀ s ∈ K, ∀ t ⊆ s, t ∈ K

/-- *Spécieuse*: stable under the unions of families bounded in `𝔓(I)`, i.e. of all families. -/
def IsSpecious (K : Set (Set I)) : Prop := ∀ S ⊆ K, ⋃₀ S ∈ K

/-- Page 40: a closed family is spécieuse iff it is `𝔓(I')` for a part `I'` of `I`. -/
theorem specious_iff {K : Set (Set I)} (hK : IsClosedFamily K) :
    IsSpecious K ↔ ∃ J : Set I, K = 𝒫 J := by
  constructor
  · intro hS
    refine ⟨⋃₀ K, Set.Subset.antisymm (fun s hs => Set.subset_sUnion_of_mem hs) ?_⟩
    intro t ht
    exact hK _ (hS K le_rfl) t ht
  · rintro ⟨J, rfl⟩ S hS
    exact Set.sUnion_subset hS

/-- A nonempty closed family stable under binary unions contains every finite part of its
union. -/
theorem finset_mem_of_union {K : Set (Set I)} (hK : IsClosedFamily K) (hne : K.Nonempty)
    (hu : ∀ s ∈ K, ∀ t ∈ K, s ∪ t ∈ K) (T : Finset I) (hT : (T : Set I) ⊆ ⋃₀ K) :
    (T : Set I) ∈ K := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨s, hs⟩ := hne
    simpa using hK s hs ∅ (Set.empty_subset s)
  | insert a T _ ih =>
    rw [Finset.coe_insert, Set.insert_eq]
    have ha : a ∈ ⋃₀ K := hT (by simp)
    obtain ⟨s, hs, has⟩ := ha
    refine hu _ (hK s hs {a} (Set.singleton_subset_iff.2 has)) _ (ih ?_)
    exact fun z hz => hT (Finset.mem_coe.2 (Finset.mem_insert_of_mem hz))

/-- Page 40, for `I` finite: stability under the union of two simplices suffices. -/
theorem specious_of_union [Finite I] {K : Set (Set I)} (hK : IsClosedFamily K)
    (hne : K.Nonempty) (hu : ∀ s ∈ K, ∀ t ∈ K, s ∪ t ∈ K) : IsSpecious K := by
  have hJ : (⋃₀ K) ∈ K := by
    have h := finset_mem_of_union hK hne hu (Set.toFinite (⋃₀ K)).toFinset
      (by rw [Set.Finite.coe_toFinset])
    rwa [Set.Finite.coe_toFinset] at h
  have hP : K = 𝒫 (⋃₀ K) :=
    Set.Subset.antisymm (fun s hs => Set.subset_sUnion_of_mem hs) (fun t ht => hK _ hJ t ht)
  exact (specious_iff hK).2 ⟨_, hP⟩

/-- For `I = ℕ`, the finite parts form a closed family, nonempty and stable under binary unions,
which is not spécieuse. -/
theorem finite_parts_not_specious :
    IsClosedFamily {s : Set ℕ | s.Finite} ∧ ({s : Set ℕ | s.Finite}).Nonempty ∧
      (∀ s ∈ {s : Set ℕ | s.Finite}, ∀ t ∈ {s : Set ℕ | s.Finite},
        s ∪ t ∈ {s : Set ℕ | s.Finite}) ∧
      ¬ IsSpecious {s : Set ℕ | s.Finite} := by
  refine ⟨fun s hs t ht => hs.subset ht, ⟨∅, Set.finite_empty⟩,
    fun s hs t ht => hs.union ht, ?_⟩
  intro h
  have : ⋃₀ {s : Set ℕ | s.Finite} = Set.univ :=
    Set.eq_univ_of_forall fun n => ⟨{n}, Set.finite_singleton n, rfl⟩
  have hfin := h _ le_rfl
  rw [this] at hfin
  exact Set.infinite_univ hfin

end Example40

section Trivial

variable (M : Type*) [PartialOrder M]

/-- In a trivial atelier (`≪ := ≤`), the small shadow of `Y`: the minimal elements below `Y`. -/
def omb (Y : M) : Set M := {x | IsMin x ∧ x ≤ Y}

/-- At 8 (page 45) in a trivial atelier: every `X` has a lieu `x ∈ omb X` in no `omb Y`,
`Y < X`. -/
def At8 : Prop := ∀ X : M, ∃ x ∈ omb M X, ∀ Y, Y < X → x ∉ omb M Y

/-- The « successeur » reading: `x` minimal below `X` with nothing strictly between. -/
def At8Cover : Prop := ∀ X : M, ∃ x ∈ omb M X, ∀ Y, x < Y → ¬ Y < X

/-- At 8 holds in a trivial atelier iff every multistrate is minimal. -/
theorem at8_iff : At8 M ↔ ∀ X : M, IsMin X := by
  constructor
  · intro h X
    obtain ⟨x, ⟨hxmin, hxX⟩, hx⟩ := h X
    rcases hxX.lt_or_eq with hlt | rfl
    · exact absurd ⟨hxmin, le_rfl⟩ (hx x hlt)
    · exact hxmin
  · intro h X
    exact ⟨X, ⟨h X, le_rfl⟩, fun Y hY _ => (h X).not_lt hY⟩

/-- At 8 holds in a trivial atelier iff the order of `𝓜` is equality: `𝓜` is discrete. -/
theorem at8_iff_discrete : At8 M ↔ ∀ X Y : M, X ≤ Y → X = Y := by
  rw [at8_iff]
  constructor
  · intro h X Y hXY; exact le_antisymm hXY (h Y hXY)
  · intro h X Y hYX; exact (h Y X hYX).ge

/-- The « successeur » reading is strictly weaker: the chain `false < true` satisfies it and
not At 8. -/
theorem at8Cover_not_at8 : At8Cover Bool ∧ ¬ At8 Bool := by
  refine ⟨?_, ?_⟩
  · intro X
    refine ⟨false, ⟨fun b _ => Bool.false_le b, Bool.false_le X⟩, ?_⟩
    intro Y h1 h2
    revert h1 h2; revert X Y; decide
  · rw [at8_iff]
    intro h
    exact absurd (h true (Bool.false_le true)) (by decide)

end Trivial

end Grothendieck.Folder156_6
