module

public import Mathlib

@[expose] public section


/-!
# Folder 151, page 68: the gluing of tubes over covering pairs fails in depth 2

Page 68 of folder 151 (transcription `transcripts/151/batch-04.fr.tex`, modernised reading
`transcripts/151/151.modern.tex`, « Le théorème de recollement des tubes », première version)
states that a stratified space `X`, with strata `Xᵢ*` indexed by a poset `I`, is the inductive
limit of the diagram `Ĩ` built from the covering pairs `i ⋖ j` only:
`Xᵢ* → 𝒱_{i,j} ← 𝒱*_{i,j} → Xⱼ*`, where `𝒱̄_{i,j}` is a tubular neighbourhood of `Xᵢ` in `Xⱼ`,
`R_{i,j} = ⋃ {X_k | k < j, X_k ⊉ Xᵢ}`, `𝒱_{i,j} = 𝒱̄_{i,j} ∖ R_{i,j}` and
`𝒱*_{i,j} = 𝒱̄_{i,j} ∖ Ẋⱼ`.

What is modelled. The edition's counterexample `X = ℝ²` (here `ℝ × ℝ`), `X₀ = {0}`,
`X₁ = ℝ × {0}`, `X₂ = ℝ²`, which satisfies the census hypotheses of pp. 62–63. Here
`Ẋ₁ = X₀`, `Ẋ₂ = X₁`, `R_{0,1} = ∅`, `R_{1,2} = X₀`. The tubes `𝒱̄_{0,1} ⊆ X₁` and
`𝒱̄_{1,2} ⊆ ℝ²` are *arbitrary* (`Tubes`), subject only to containing their soul, so that the
arrows `Xᵢ* → 𝒱_{i,j}` exist: the result does not depend on how they are chosen.
The seven vertices of `Ĩ` are `Tubes.piece`, the six arrows `Tubes.arrows` are inclusions
(`piece_subset_of_mem_arrows`), and the colimit topology `Tubes.colimTop` on the set `ℝ²` is the
finest making the seven inclusions continuous.
* `exists_unique_desc`: `(ℝ², colimTop)` with the seven inclusions *is* the colimit of `Ĩ` in
  `Top`: every compatible family of continuous maps out of the vertices factors uniquely through
  a map `ℝ² → Z` continuous for `colimTop`;
* `isOpen_colimTop_U`, `not_isOpen_U`: `U = {(x, y) | x = 0 → y = 0}` (the plane minus the
  punctured vertical axis) is open in the colimit topology and not in `ℝ²`;
* `colimTop_ne`: so the colimit topology is not the topology of `ℝ²`, and the comparison
  `colim Ĩ → X`, a continuous bijection, is not a homeomorphism.
The reason: `0` lies only in the vertices `X₀*` and `𝒱_{0,1}`, both inside the horizontal axis;
the neighbourhood of `0` in `ℝ²` is the tube `𝒱_{0,2}` of the non-covering pair `0 < 2`.

Not formalised: the homotopy-colimit variant (its Euler characteristic is `−1`, so it is not
contractible), the general stratified setting, and the depth-one case where the statement holds.
-/

open Set Topology

namespace Grothendieck.Folder151

/-- The plane `X = X₂`. -/
abbrev P := ℝ × ℝ

/-- The closed stratum `X₁`, the horizontal axis. -/
def axis : Set P := {p | p.2 = 0}

/-- The closed stratum `X₀ = X₀* = {0}`. -/
def X0 : Set P := {0}

/-- The open stratum `X₁* = X₁ ∖ X₀`. -/
def X1s : Set P := axis \ X0

/-- The open stratum `X₂* = X₂ ∖ X₁`. -/
def X2s : Set P := axisᶜ

theorem X0_subset_axis : X0 ⊆ axis := by
  intro p hp
  rw [X0, mem_singleton_iff] at hp
  simp [axis, hp]

/-- Arbitrary choices of the closed tubes `𝒱̄_{0,1}` (of `X₀` in `X₁`) and `𝒱̄_{1,2}`
(of `X₁` in `X₂`), each containing its soul. -/
structure Tubes where
  V01bar : Set P
  V12bar : Set P
  V01bar_subset : V01bar ⊆ axis
  X0_subset : X0 ⊆ V01bar
  axis_subset : axis ⊆ V12bar

namespace Tubes

variable (T : Tubes)

/-- `𝒱_{0,1} = 𝒱̄_{0,1} ∖ R_{0,1}`, with `R_{0,1} = ∅`. -/
def V01 : Set P := T.V01bar \ ∅

/-- `𝒱*_{0,1} = 𝒱̄_{0,1} ∖ Ẋ₁`, with `Ẋ₁ = X₀`. -/
def V01s : Set P := T.V01bar \ X0

/-- `𝒱_{1,2} = 𝒱̄_{1,2} ∖ R_{1,2}`, with `R_{1,2} = X₀`. -/
def V12 : Set P := T.V12bar \ X0

/-- `𝒱*_{1,2} = 𝒱̄_{1,2} ∖ Ẋ₂`, with `Ẋ₂ = X₁`. -/
def V12s : Set P := T.V12bar \ axis

/-- The seven vertices of `Ĩ`: `X₀*, 𝒱_{0,1}, 𝒱*_{0,1}, X₁*, 𝒱_{1,2}, 𝒱*_{1,2}, X₂*`. -/
def piece : Fin 7 → Set P := ![X0, T.V01, T.V01s, X1s, T.V12, T.V12s, X2s]

/-- The six arrows of `Ĩ`, as (source, target): `X₀* → 𝒱_{0,1} ← 𝒱*_{0,1} → X₁*` and
`X₁* → 𝒱_{1,2} ← 𝒱*_{1,2} → X₂*`. -/
def arrows : List (Fin 7 × Fin 7) := [(0, 1), (2, 1), (2, 3), (3, 4), (5, 4), (5, 6)]

/-- The six arrows are inclusions. -/
theorem piece_subset_of_mem_arrows {a b : Fin 7} (h : (a, b) ∈ arrows) :
    T.piece a ⊆ T.piece b := by
  simp only [arrows, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro p hp; exact ⟨T.X0_subset hp, id⟩
  · intro p hp; exact ⟨hp.1, id⟩
  · intro p hp; exact ⟨T.V01bar_subset hp.1, hp.2⟩
  · intro p hp; exact ⟨T.axis_subset hp.1, hp.2⟩
  · intro p hp
    exact ⟨hp.1, fun h0 => hp.2 (X0_subset_axis h0)⟩
  · intro p hp; exact hp.2

/-- The colimit topology: the finest making the inclusions of the seven vertices continuous. -/
@[instance_reducible]
def colimTop : TopologicalSpace P :=
  ⨆ i, TopologicalSpace.coinduced (Subtype.val : T.piece i → P) inferInstance

/-- The vertices cover the plane: the strata alone do. -/
theorem iUnion_piece : (⋃ i, T.piece i) = univ := by
  refine eq_univ_of_forall fun p => ?_
  by_cases h0 : p ∈ X0
  · exact mem_iUnion.2 ⟨0, by simpa [piece] using h0⟩
  by_cases h1 : p ∈ axis
  · exact mem_iUnion.2 ⟨3, (⟨h1, h0⟩ : p ∈ X1s)⟩
  · exact mem_iUnion.2 ⟨6, (h1 : p ∈ X2s)⟩

/-- A map out of the plane is continuous for the colimit topology iff its restriction to each
vertex is continuous. -/
theorem continuous_colimTop_iff {Z : Type*} [TopologicalSpace Z] (f : P → Z) :
    Continuous[T.colimTop, _] f ↔ ∀ i, Continuous (fun x : T.piece i => f x) := by
  simp only [continuous_iSup_dom, continuous_coinduced_dom]
  rfl

open Classical in
/-- The stratum index of a point: `0`, `3` or `6`. -/
noncomputable def strat (p : P) : Fin 7 :=
  if p ∈ X0 then 0 else if p ∈ axis then 3 else 6

theorem mem_piece_strat (p : P) : p ∈ T.piece (strat p) := by
  by_cases h0 : p ∈ X0
  · simp only [strat, h0, ↓reduceIte]; exact h0
  by_cases h1 : p ∈ axis
  · simp only [strat, h0, h1, ↓reduceIte]; exact (⟨h1, h0⟩ : p ∈ X1s)
  · simp only [strat, h0, h1, ↓reduceIte]; exact (h1 : p ∈ X2s)

/-- A compatible family of maps out of the vertices agrees, at each point, with its value on the
point's stratum: the vertices containing a given point are joined by arrows. -/
theorem eq_strat {Z : Type*} (f : ∀ i, T.piece i → Z)
    (hf : ∀ a b, (a, b) ∈ arrows → ∀ p (ha : p ∈ T.piece a) (hb : p ∈ T.piece b),
      f a ⟨p, ha⟩ = f b ⟨p, hb⟩)
    (p : P) (i : Fin 7) (hi : p ∈ T.piece i) :
    f i ⟨p, hi⟩ = f (strat p) ⟨p, T.mem_piece_strat p⟩ := by
  have A : ∀ a b, (a, b) ∈ arrows → ∀ (ha : p ∈ T.piece a) (hb : p ∈ T.piece b),
      f a ⟨p, ha⟩ = f b ⟨p, hb⟩ := fun a b h => hf a b h p
  -- the stratum of `p`, and which vertices may contain it
  have key : ∀ (j : Fin 7) (hj : p ∈ T.piece j), f i ⟨p, hi⟩ = f j ⟨p, hj⟩ := by
    intro j hj
    by_cases h0 : p ∈ X0
    · -- here `p = 0`
      -- `0` lies only in vertices 0 and 1
      have hv : ∀ k, p ∈ T.piece k → k = 0 ∨ k = 1 := by
        intro k hk
        fin_cases k
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd h0 hk.2
        · exact absurd h0 hk.2
        · exact absurd h0 hk.2
        · exact absurd (X0_subset_axis h0) hk.2
        · exact absurd (X0_subset_axis h0) hk
      have e : ∀ (k : Fin 7) (hk : p ∈ T.piece k),
          f k ⟨p, hk⟩ = f 0 ⟨p, h0⟩ := by
        intro k hk
        rcases hv k hk with rfl | rfl
        · rfl
        · exact (A 0 1 (by simp [arrows]) _ hk).symm
      rw [e i hi, e j hj]
    by_cases h1 : p ∈ axis
    · have hs : p ∈ X1s := ⟨h1, h0⟩
      have hv : ∀ k, p ∈ T.piece k → k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
        intro k hk
        fin_cases k
        · exact absurd hk h0
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd h1 hk.2
        · exact absurd h1 hk
      have e : ∀ (k : Fin 7) (hk : p ∈ T.piece k),
          f k ⟨p, hk⟩ = f 3 ⟨p, hs⟩ := by
        intro k hk
        rcases hv k hk with rfl | rfl | rfl | rfl
        · have h2 : p ∈ T.piece 2 := ⟨hk.1, h0⟩
          rw [← A 2 1 (by simp [arrows]) h2 hk, A 2 3 (by simp [arrows]) h2 hs]
        · exact A 2 3 (by simp [arrows]) hk _
        · rfl
        · exact (A 3 4 (by simp [arrows]) _ hk).symm
      rw [e i hi, e j hj]
    · have hs : p ∈ X2s := h1
      have hv : ∀ k, p ∈ T.piece k → k = 4 ∨ k = 5 ∨ k = 6 := by
        intro k hk
        fin_cases k
        · exact absurd (X0_subset_axis hk) h1
        · exact absurd (T.V01bar_subset hk.1) h1
        · exact absurd (T.V01bar_subset hk.1) h1
        · exact absurd hk.1 h1
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have e : ∀ (k : Fin 7) (hk : p ∈ T.piece k),
          f k ⟨p, hk⟩ = f 6 ⟨p, hs⟩ := by
        intro k hk
        rcases hv k hk with rfl | rfl | rfl
        · have h5 : p ∈ T.piece 5 := ⟨hk.1, h1⟩
          rw [← A 5 4 (by simp [arrows]) h5 hk, A 5 6 (by simp [arrows]) h5 hs]
        · exact A 5 6 (by simp [arrows]) hk _
        · rfl
      rw [e i hi, e j hj]
  exact key _ _

/-- `(ℝ², colimTop)`, with the seven inclusions, is the colimit of `Ĩ` in `Top`: a family of
continuous maps out of the vertices, compatible with the six arrows, factors uniquely through a
map out of the plane continuous for `colimTop`. -/
theorem exists_unique_desc {Z : Type*} [TopologicalSpace Z] (f : ∀ i, T.piece i → Z)
    (hc : ∀ i, Continuous (f i))
    (hf : ∀ a b, (a, b) ∈ arrows → ∀ p (ha : p ∈ T.piece a) (hb : p ∈ T.piece b),
      f a ⟨p, ha⟩ = f b ⟨p, hb⟩) :
    ∃! g : P → Z, Continuous[T.colimTop, _] g ∧ ∀ i (x : T.piece i), g x = f i x := by
  refine ⟨fun p => f (strat p) ⟨p, T.mem_piece_strat p⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [continuous_colimTop_iff]
    intro i
    convert hc i using 1
    funext x
    exact (T.eq_strat f hf x.1 i x.2).symm
  · intro i x
    exact (T.eq_strat f hf x.1 i x.2).symm
  · rintro g ⟨-, hg⟩
    funext p
    exact hg _ ⟨p, T.mem_piece_strat p⟩

/-- The colimit topology is finer than that of `ℝ²`. -/
theorem le_colimTop : T.colimTop ≤ (inferInstance : TopologicalSpace P) := by
  rw [← continuous_id_iff_le]
  exact (T.continuous_colimTop_iff id).2 fun _ => continuous_subtype_val

/-- Every vertex lies in the horizontal axis or avoids `0`. -/
theorem piece_dichotomy (i : Fin 7) : T.piece i ⊆ axis ∨ (0 : P) ∉ T.piece i := by
  fin_cases i
  · left; exact X0_subset_axis
  · left; intro p hp; exact T.V01bar_subset hp.1
  · left; intro p hp; exact T.V01bar_subset hp.1
  · left; intro p hp; exact hp.1
  · right; intro h; exact h.2 rfl
  · right; intro h; exact h.2 (by simp [axis])
  · right; intro h; exact h (by simp [axis])

/-- The plane minus the punctured vertical axis. -/
def U : Set P := {p | p.1 = 0 → p.2 = 0}

theorem isOpen_preimage_U {S : Set P} (hS : S ⊆ axis ∨ (0 : P) ∉ S) :
    IsOpen ((Subtype.val : S → P) ⁻¹' U) := by
  rcases hS with hS | hS
  · convert isOpen_univ
    exact eq_univ_of_forall fun p _ => hS p.2
  · have : (Subtype.val : S → P) ⁻¹' U = Subtype.val ⁻¹' {p : P | p.1 ≠ 0} := by
      ext ⟨p, hp⟩
      simp only [mem_preimage, U, mem_ofPred_eq]
      constructor
      · intro h h1
        exact hS (by rw [show p = 0 from Prod.ext h1 (h h1)] at hp; exact hp)
      · intro h h1; exact absurd h1 h
    rw [this]
    exact (isOpen_ne_fun continuous_fst continuous_const).preimage continuous_subtype_val

/-- `U` is open in the colimit of the covering-pair diagram. -/
theorem isOpen_colimTop_U : IsOpen[T.colimTop] U := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]
  exact fun i => isOpen_preimage_U (T.piece_dichotomy i)

/-- `U` is not open in `ℝ²`: it is not a neighbourhood of `0`. -/
theorem not_isOpen_U : ¬ IsOpen U := by
  intro h
  have : IsOpen ((fun t : ℝ => ((0 : ℝ), t)) ⁻¹' U) :=
    h.preimage (continuous_const.prodMk continuous_id)
  have e : ((fun t : ℝ => ((0 : ℝ), t)) ⁻¹' U) = {0} := by
    ext t; simp [U]
  rw [e] at this
  exact not_isOpen_singleton (0 : ℝ) this

/-- The colimit topology of `Ĩ` is not the topology of `ℝ²`: the gluing theorem of page 68,
read as a colimit in `Top`, fails for `ℝ² ⊃ ℝ × {0} ⊃ {0}`, whatever the tubes. -/
theorem colimTop_ne : T.colimTop ≠ (inferInstance : TopologicalSpace P) := by
  intro h
  have := T.isOpen_colimTop_U
  rw [h] at this
  exact not_isOpen_U this

end Tubes

end Grothendieck.Folder151

/-!
## Depth one: the gluing theorem holds

For a closed stratum `X₀ ⊂ X` (two strata, `I = {0 < 1}`, one covering pair) and a tube `𝒱̄` of
`X₀` in `X` that is a neighbourhood of `X₀`, the four vertices `X₀*, 𝒱_{0,1}, 𝒱*_{0,1}, X₁*`
with their three inclusions have colimit `X` in `Top` (`DepthOne.exists_unique_desc`), and the
colimit topology is that of `X` (`DepthOne.colimTop_eq`). The point: `𝒱̄` and `X ∖ X₀` are
neighbourhoods covering `X`. Not formalised: depth one for several strata (`I` without chains
of length 2), and cone-bundle tubes.
-/

namespace Grothendieck.Folder151

namespace DepthOne

variable {X : Type*} [TopologicalSpace X] (X₀ V : Set X)

/-- The four vertices of `Ĩ` for `X ⊃ X₀`: `X₀* = X₀`, `𝒱_{0,1} = 𝒱̄` (here `R_{0,1} = ∅`),
`𝒱*_{0,1} = 𝒱̄ ∖ X₀` (here `Ẋ₁ = X₀`) and `X₁* = X ∖ X₀`. -/
def piece : Fin 4 → Set X := ![X₀, V, V \ X₀, X₀ᶜ]

/-- The three arrows `X₀* → 𝒱_{0,1} ← 𝒱*_{0,1} → X₁*`, as (source, target). -/
def arrows : List (Fin 4 × Fin 4) := [(0, 1), (2, 1), (2, 3)]

omit [TopologicalSpace X] in
/-- The three arrows are inclusions as soon as the tube contains its soul. -/
theorem piece_subset_of_mem_arrows (h₀ : X₀ ⊆ V) {a b : Fin 4} (h : (a, b) ∈ arrows) :
    piece X₀ V a ⊆ piece X₀ V b := by
  simp only [arrows, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h₀, sdiff_subset, fun _ hp => hp.2]

/-- The colimit topology: the finest making the inclusions of the four vertices continuous. -/
@[instance_reducible]
def colimTop : TopologicalSpace X :=
  ⨆ i, TopologicalSpace.coinduced (Subtype.val : piece X₀ V i → X) inferInstance

open Classical in
/-- Depth one: if `X₀` is closed and the tube `𝒱̄` is a neighbourhood of `X₀`, then `X` with the
four inclusions is the colimit of `Ĩ` in `Top`: a compatible family of continuous maps out of the
vertices factors uniquely through a continuous map out of `X`. -/
theorem exists_unique_desc (hX₀ : IsClosed X₀) (hV : X₀ ⊆ interior V)
    {Z : Type*} [TopologicalSpace Z] (f : ∀ i, piece X₀ V i → Z)
    (hc : ∀ i, Continuous (f i))
    (hf : ∀ a b, (a, b) ∈ arrows → ∀ p (ha : p ∈ piece X₀ V a) (hb : p ∈ piece X₀ V b),
      f a ⟨p, ha⟩ = f b ⟨p, hb⟩) :
    ∃! g : X → Z, Continuous g ∧ ∀ i (x : piece X₀ V i), g x = f i x := by
  let g : X → Z := fun p => if h : p ∈ X₀ then f 0 ⟨p, h⟩ else f 3 ⟨p, h⟩
  have hg : ∀ i (x : piece X₀ V i), g x = f i x := by
    have h21 := hf 2 1 (by simp [arrows]); have h23 := hf 2 3 (by simp [arrows])
    rintro (_ | _ | _ | _ | _) ⟨p, hp⟩
    · simp [g, show p ∈ X₀ from hp]
    · by_cases h : p ∈ X₀
      · simpa [g, h] using hf 0 1 (by simp [arrows]) p h hp
      · simpa [g, h] using (h23 p ⟨hp, h⟩ h).symm.trans (h21 p _ hp)
    · simpa [g, hp.2] using (h23 p hp hp.2).symm
    · simp [g, show p ∉ X₀ from hp]
    · omega
  refine ⟨g, ⟨continuous_of_cover_nhds (s := piece X₀ V) (fun p => ?_) fun i => ?_, hg⟩,
    fun g' ⟨_, hg'⟩ => funext fun p => ?_⟩
  · by_cases h : p ∈ X₀
    · exact ⟨1, mem_interior_iff_mem_nhds.1 (hV h)⟩
    · exact ⟨3, hX₀.isOpen_compl.mem_nhds h⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (funext (hg i) : (piece X₀ V i).domRestrict g = f i) ▸ hc i
  · by_cases h : p ∈ X₀
    exacts [(hg' 0 ⟨p, h⟩).trans (hg 0 ⟨p, h⟩).symm, (hg' 3 ⟨p, h⟩).trans (hg 3 ⟨p, h⟩).symm]

/-- Depth one: the colimit topology of the four vertices is the topology of `X`. -/
theorem colimTop_eq (hX₀ : IsClosed X₀) (hV : X₀ ⊆ interior V) :
    colimTop X₀ V = ‹TopologicalSpace X› := by
  refine le_antisymm (iSup_le fun i => continuous_subtype_val.coinduced_le) fun U hU => ?_
  simp only [isOpen_iSup_iff, isOpen_coinduced] at hU
  obtain ⟨W, hW, e⟩ := isOpen_induced_iff.1 (hU 1)
  obtain ⟨W', hW', e'⟩ := isOpen_induced_iff.1 (hU 3)
  have h1 p (hp : p ∈ V) : p ∈ W ↔ p ∈ U := Set.ext_iff.1 e ⟨p, hp⟩
  have h3 p (hp : p ∉ X₀) : p ∈ W' ↔ p ∈ U := Set.ext_iff.1 e' ⟨p, hp⟩
  convert (hW'.inter hX₀.isOpen_compl).union (hW.inter (isOpen_interior (s := V))) using 1
  ext p
  have := h1 p; have := h3 p; have := @interior_subset _ _ V p; have := @hV p
  simp only [mem_union, mem_inter_iff, mem_compl_iff]
  tauto

end DepthOne

end Grothendieck.Folder151
