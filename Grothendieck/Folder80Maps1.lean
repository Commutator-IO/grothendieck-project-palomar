module

public import Mathlib

@[expose] public section


/-!
# Folder 80, page 26: the « cas latticiel » — a counterexample and the correct criterion

Finding `80-lattice-criterion`. Page 26 states, without proof: the closed cells of the cell
decomposition of `ℝP²` cut out by an arrangement of pseudolines meet pairwise in the empty set or
in a single closed cell (« cas latticiel ») iff (a) no pseudoline is bigonal and (b) the
arrangement is not `II_4` (the edition's reading of b)). Page 24 says moreover that `II′_{3,2}`,
`II_5`, `III_6` are latticial.

**What the formalisation finds.** The criterion is false: `II′_{3,2}` (three pseudolines through
one point, two through another, no joining line) has no bigonal line, is not `II_4`, and is not
latticial: its two « corner » faces meet exactly in the two centres. The correct criterion,
proved here, is that the arrangement is latticial iff **no two points carry every pseudoline
between them**, i.e. iff it is none of the two-pencil types `I_N`, `I_{p,q}`, `II′_{p,q}` — exactly
the hypothesis of the Théorème of page 24. Direction (⇒) of the page survives: a bigonal line,
or `II_4`, gives two such points.

We work in the combinatorial model of the cell decomposition: the oriented-matroid covectors.
A cell of the decomposition of the sphere `S²` (the double cover of `ℝP²`) is a sign vector
`X : E → SignType`; the closed cell of `X` is the set of its conformal faces `Z ≤ X`
(`closure_cell` checks this against the topology for straight lines), and a cell of `ℝP²` is a
pair `±X`. The abstract theorem `lattice_iff` needs only that the set `L` of covectors is
symmetric and closed under composition; it therefore covers every pseudoline arrangement through
the Folkman–Lawrence representation (not formalised). For straight lines `ℓ i ∈ ℝ³` the covectors
are the sign vectors of points (`cov`), and `lattice_iff_not_twoPencil` restates the criterion.

* `lattice_iff`: `Lattice L ↔` no two nonzero covectors have disjoint supports;
* `closure_cell`: the topological closure of a cone cell is its set of conformal faces;
* `lattice_iff_not_twoPencil`: latticial iff no two points carry every line;
* `not_lattice_of_bigonal`, `not_lattice_of_four`: conditions a), b) are necessary;
* `II32_no_bigon`, `II32_nondegenerate`, `II32_not_lattice`, `lattice_criterion_false`: the
  counterexample `x = 0, x = z, x = 2z, y = 0, y = z`.
-/

namespace Grothendieck.Folder80Maps1

open Filter Topology Matrix

section SignVectors

variable {E : Type*}

/-- `Z` is a face of `X` (conformal order): `Z e ∈ {0, X e}` for all `e`. -/
def Conf (Z X : E → SignType) : Prop := ∀ e, Z e = 0 ∨ Z e = X e

/-- Composition of sign vectors. -/
def comp (X Y : E → SignType) : E → SignType := fun e => if X e = 0 then Y e else X e

/-- The closed cell of `ℝP²` of the cell `±X`: the nonzero covectors `Z ≤ ±X`. -/
def PCl (L : Set (E → SignType)) (X : E → SignType) : Set (E → SignType) :=
  {Z | Z ∈ L ∧ Z ≠ 0 ∧ (Conf Z X ∨ Conf Z (-X))}

/-- The « cas latticiel »: two closed cells meet in nothing or in a single closed cell. -/
def Lattice (L : Set (E → SignType)) : Prop :=
  ∀ X ∈ L, ∀ Y ∈ L, X ≠ 0 → Y ≠ 0 →
    PCl L X ∩ PCl L Y = ∅ ∨ ∃ W ∈ L, W ≠ 0 ∧ PCl L X ∩ PCl L Y = PCl L W

theorem conf_refl (X : E → SignType) : Conf X X := fun _ => Or.inr rfl

theorem Conf.trans {Z W X : E → SignType} (h : Conf Z W) (h' : Conf W X) : Conf Z X := fun e =>
  (h e).elim Or.inl fun h => (h' e).imp h.trans h.trans

theorem conf_neg_iff {Z X : E → SignType} : Conf Z (-X) ↔ Conf (-Z) X :=
  forall_congr' fun e => by
    simp only [Pi.neg_apply]; cases Z e <;> cases X e <;> decide

theorem Conf.ne_zero {Z X : E → SignType} (h : Conf Z X) (hZ : Z ≠ 0) : X ≠ 0 := by
  rintro rfl; exact hZ (funext fun e => (h e).elim id id)

theorem conf_comp (X Y : E → SignType) : Conf X (comp X Y) := fun e => by
  unfold comp; split_ifs with h; exacts [Or.inl h, Or.inr rfl]

theorem Conf.comp {A B X : E → SignType} (hA : Conf A X) (hB : Conf B X) :
    Conf (comp A B) X := fun e => by unfold Folder80Maps1.comp; split_ifs; exacts [hB e, hA e]

/-- A face of `X` and of `Y` and a face of `X` and of `-Y` have disjoint supports. -/
theorem disjoint_of_conf {v w X Y : E → SignType} (hvX : Conf v X) (hvY : Conf v Y)
    (hwX : Conf w X) (hwY : Conf w (-Y)) (e : E) : v e = 0 ∨ w e = 0 := by
  have h1 := hvX e; have h2 := hvY e; have h3 := hwX e; have h4 := hwY e
  revert h1 h2 h3 h4; simp only [Pi.neg_apply]
  cases v e <;> cases w e <;> cases X e <;> cases Y e <;> decide

theorem neg_ne_zero' {Z : E → SignType} (h : Z ≠ 0) : -Z ≠ 0 := fun h' => h <| by
  rw [← neg_neg Z, h']; rfl

variable {L : Set (E → SignType)}

theorem pcl_neg (X : E → SignType) : PCl L (-X) = PCl L X := by ext; simp [PCl, or_comm]

/-- Two nonzero covectors with disjoint supports break the lattice property: the cells
`v ∘ w` and `v ∘ (-w)` both contain `±v` and `±w`, and no cell lies between. -/
theorem not_lattice_of_disjoint (hL : ∀ X ∈ L, ∀ Y ∈ L, comp X Y ∈ L) {v w : E → SignType}
    (hv : v ∈ L) (hw : w ∈ L) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hN : -w ∈ L)
    (hvw : ∀ e, v e = 0 ∨ w e = 0) : ¬ Lattice L := by
  obtain ⟨e, he : v e ≠ 0⟩ := Function.ne_iff.1 hv0
  obtain ⟨f, hf : w f ≠ 0⟩ := Function.ne_iff.1 hw0
  have hvf := (hvw f).resolve_right hf
  have hvX {u} : Conf v (comp v u) := conf_comp v u
  have hwX : Conf w (comp v w) := fun e => by
    unfold comp; split_ifs with h; exacts [Or.inr rfl, Or.inl ((hvw e).resolve_left h)]
  have hwY : Conf w (-comp v (-w)) := fun e => by
    simp only [comp, Pi.neg_apply]; split_ifs with h
    exacts [Or.inr (neg_neg _).symm, Or.inl ((hvw e).resolve_left h)]
  intro hlat
  have hvXY : v ∈ PCl L (comp v w) ∩ PCl L (comp v (-w)) :=
    ⟨⟨hv, hv0, Or.inl hvX⟩, ⟨hv, hv0, Or.inl hvX⟩⟩
  have hwXY : w ∈ PCl L (comp v w) ∩ PCl L (comp v (-w)) :=
    ⟨⟨hw, hw0, Or.inl hwX⟩, ⟨hw, hw0, Or.inr hwY⟩⟩
  rcases hlat _ (hL _ hv _ hw) _ (hL _ hv _ hN) (hvX.ne_zero hv0) (hvX.ne_zero hv0) with
    h | ⟨W, hW, hW0, h⟩
  · exact h.subset hvXY
  have hWW : W ∈ PCl L (comp v w) ∩ PCl L (comp v (-w)) := h ▸ ⟨hW, hW0, Or.inl (conf_refl W)⟩
  rw [h] at hvXY hwXY
  obtain ⟨⟨-, -, h1⟩, ⟨-, -, h2⟩⟩ := hWW
  have h1' := h1.imp (fun h => And.intro (h e) (h f)) (fun h => And.intro (h e) (h f))
  have h2' := h2.imp (fun h => And.intro (h e) (h f)) (fun h => And.intro (h e) (h f))
  have hv' := hvXY.2.2.imp (· e) (· e)
  have hw' := hwXY.2.2.imp (· f) (· f)
  simp only [Pi.neg_apply, comp, he, hvf, ↓reduceIte, neg_neg] at h1' h2' hv' hw'
  revert he hf h1' h2' hv' hw'
  generalize v e = a; generalize w f = b; generalize W e = c; generalize W f = d
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- If no nonzero face of `X` is a face of `-Y`, the closed cells `±X` and `±Y` meet in nothing
or in the closed cell of the composite of all their common faces. -/
theorem pcl_inter_of [Fintype E] (hL : ∀ X ∈ L, ∀ Y ∈ L, comp X Y ∈ L)
    (hN : ∀ X ∈ L, -X ∈ L) {X Y : E → SignType}
    (hS : ∀ Z ∈ L, Z ≠ 0 → Conf Z X → ¬ Conf Z (-Y)) :
    PCl L X ∩ PCl L Y = ∅ ∨ ∃ W ∈ L, W ≠ 0 ∧ PCl L X ∩ PCl L Y = PCl L W := by
  set S := {Z | Z ∈ L ∧ Z ≠ 0 ∧ Conf Z X ∧ Conf Z Y}
  have hmem : ∀ Z, Z ∈ PCl L X ∩ PCl L Y ↔ Z ∈ L ∧ Z ≠ 0 ∧ (Z ∈ S ∨ -Z ∈ S) := fun Z => by
    constructor
    · rintro ⟨⟨hZ, hZ0, hX | hX⟩, -, -, hY | hY⟩
      · exact ⟨hZ, hZ0, Or.inl ⟨hZ, hZ0, hX, hY⟩⟩
      · exact (hS Z hZ hZ0 hX hY).elim
      · exact (hS _ (hN _ hZ) (neg_ne_zero' hZ0) (conf_neg_iff.1 hX)
          (conf_neg_iff.2 (by rwa [neg_neg]))).elim
      · exact ⟨hZ, hZ0, Or.inr ⟨hN _ hZ, neg_ne_zero' hZ0, conf_neg_iff.1 hX, conf_neg_iff.1 hY⟩⟩
    · rintro ⟨hZ, hZ0, ⟨-, -, hX, hY⟩ | ⟨-, -, hX, hY⟩⟩
      · exact ⟨⟨hZ, hZ0, Or.inl hX⟩, hZ, hZ0, Or.inl hY⟩
      · exact ⟨⟨hZ, hZ0, Or.inr (conf_neg_iff.2 hX)⟩, hZ, hZ0, Or.inr (conf_neg_iff.2 hY)⟩
  rcases S.eq_empty_or_nonempty with hE | hne
  · left; ext Z; simp [hmem, hE]
  right
  obtain ⟨M, hM, hmax⟩ := S.exists_max_image
    (fun Z => (Finset.univ.filter fun e => Z e ≠ 0).card) S.toFinite hne
  have hle : ∀ Z ∈ S, Conf Z M := by
    rintro Z ⟨hZ, hZ0, hZX, hZY⟩ e
    have hMZ : comp M Z ∈ S := ⟨hL _ hM.1 _ hZ, (conf_comp M Z).ne_zero hM.2.1,
      hM.2.2.1.comp hZX, hM.2.2.2.comp hZY⟩
    have heq := Finset.eq_of_subset_of_card_le (fun e => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp +contextual [comp]) (hmax _ hMZ)
    by_cases hZe : Z e = 0
    · exact Or.inl hZe
    have hMe : M e ≠ 0 := fun hMe => by
      have := congrArg (e ∈ ·) heq
      simp only [Finset.mem_filter] at this; simp [comp, hMe, hZe] at this
    exact Or.inr (((hZX e).resolve_left hZe).trans ((hM.2.2.1 e).resolve_left hMe).symm)
  refine ⟨M, hM.1, hM.2.1, Set.ext fun Z => (hmem Z).trans ⟨?_, ?_⟩⟩
  · rintro ⟨hZ, hZ0, h | h⟩
    exacts [⟨hZ, hZ0, Or.inl (hle Z h)⟩, ⟨hZ, hZ0, Or.inr (conf_neg_iff.2 (hle _ h))⟩]
  · rintro ⟨hZ, hZ0, h | h⟩
    · exact ⟨hZ, hZ0, Or.inl ⟨hZ, hZ0, h.trans hM.2.2.1, h.trans hM.2.2.2⟩⟩
    · have h' := conf_neg_iff.1 h
      exact ⟨hZ, hZ0, Or.inr ⟨hN _ hZ, neg_ne_zero' hZ0, h'.trans hM.2.2.1, h'.trans hM.2.2.2⟩⟩

/-- **The lattice criterion for covectors.** For a symmetric set of sign vectors closed under
composition, the closed cells of `ℝP²` meet pairwise in nothing or a single closed cell iff no two
nonzero covectors have disjoint supports. -/
theorem lattice_iff [Fintype E] (hL : ∀ X ∈ L, ∀ Y ∈ L, comp X Y ∈ L)
    (hN : ∀ X ∈ L, -X ∈ L) :
    Lattice L ↔ ¬ ∃ v ∈ L, ∃ w ∈ L, v ≠ 0 ∧ w ≠ 0 ∧ ∀ e, v e = 0 ∨ w e = 0 := by
  refine ⟨fun h ⟨v, hv, w, hw, hv0, hw0, hvw⟩ =>
    not_lattice_of_disjoint hL hv hw hv0 hw0 (hN _ hw) hvw h, fun h X _ Y _ _ _ => ?_⟩
  by_cases hm : ∃ w ∈ L, w ≠ 0 ∧ Conf w X ∧ Conf w (-Y)
  · obtain ⟨w, hw, hw0, hwX, hwY⟩ := hm
    rw [← pcl_neg Y]
    exact pcl_inter_of hL hN fun v hv hv0 hvX hvY =>
      h ⟨v, hv, w, hw, hv0, hw0, disjoint_of_conf hvX (by rwa [neg_neg] at hvY) hwX hwY⟩
  · exact pcl_inter_of hL hN fun Z hZ hZ0 hZX hZY => hm ⟨Z, hZ, hZ0, hZX, hZY⟩

end SignVectors

section Lines

/-! ### Arrangements of lines

A line of `ℝP²` is a nonzero `ℓ ∈ ℝ³`, the plane `ℓ ⬝ᵥ p = 0` of `ℝ³`. The cells of the sphere
`(ℝ³ ∖ 0)/ℝ_{>0}` are the fibres of the sign map `sgn ℓ`, and `cov ℓ` is the set of its values. -/

variable {ι : Type*} (ℓ : ι → Fin 3 → ℝ)

/-- The sign vector of a point. -/
noncomputable def sgn (p : Fin 3 → ℝ) : ι → SignType := fun i => SignType.sign (ℓ i ⬝ᵥ p)

/-- The covectors of the arrangement. -/
def cov : Set (ι → SignType) := Set.range (sgn ℓ)

/-- Two points that carry every line between them, neither on all the lines: the arrangement
is covered by two pencils (types `I_N`, `I_{p,q}`, `II′_{p,q}`). -/
def TwoPencil : Prop :=
  ∃ p q : Fin 3 → ℝ, sgn ℓ p ≠ 0 ∧ sgn ℓ q ≠ 0 ∧ ∀ i, ℓ i ⬝ᵥ p = 0 ∨ ℓ i ⬝ᵥ q = 0

variable {ℓ}

theorem sgn_eq_zero {p : Fin 3 → ℝ} {i : ι} : sgn ℓ p i = 0 ↔ ℓ i ⬝ᵥ p = 0 := sign_eq_zero_iff

theorem neg_mem_cov {X : ι → SignType} (hX : X ∈ cov ℓ) : -X ∈ cov ℓ := by
  obtain ⟨p, rfl⟩ := hX; exact ⟨-p, funext fun i => by simp [sgn, Left.sign_neg]⟩

theorem eventually_sign (a b : ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ),
    SignType.sign (a + t * b) = if SignType.sign a = 0 then SignType.sign b else SignType.sign a := by
  have hc : Tendsto (fun t : ℝ => a + t * b) (𝓝[>] 0) (𝓝 a) :=
    ((by fun_prop : Continuous fun t : ℝ => a + t * b).tendsto' 0 a (by simp)).mono_left
      nhdsWithin_le_nhds
  rcases lt_trichotomy a 0 with h | rfl | h
  · filter_upwards [hc.eventually (gt_mem_nhds h)] with t ht
    simp [sign_neg ht, sign_neg h]
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp [sign_mul, sign_pos ht]
  · filter_upwards [hc.eventually (lt_mem_nhds h)] with t ht
    simp [sign_pos ht, sign_pos h]

theorem comp_mem_cov [Finite ι] {X Y : ι → SignType} (hX : X ∈ cov ℓ) (hY : Y ∈ cov ℓ) :
    comp X Y ∈ cov ℓ := by
  obtain ⟨p, rfl⟩ := hX; obtain ⟨q, rfl⟩ := hY
  obtain ⟨t, ht⟩ := (eventually_all.2 fun i => eventually_sign (ℓ i ⬝ᵥ p) (ℓ i ⬝ᵥ q)).exists
  exact ⟨p + t • q, funext fun i => by simpa [sgn, comp, dotProduct_add] using ht i⟩

/-- **Closed cells are faces.** For a nonempty cell `X`, the topological closure of the cone
`{p | sgn ℓ p = X}` is the set of points whose sign vector is a face of `X`. -/
theorem closure_cell [Finite ι] {X : ι → SignType} (hX : X ∈ cov ℓ) :
    closure {p | sgn ℓ p = X} = {q | Conf (sgn ℓ q) X} := by
  obtain ⟨p, rfl⟩ := hX
  refine (closure_minimal (fun q hq => hq ▸ conf_refl _) ?_).antisymm fun q hq => ?_
  · simp only [Conf, Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    have hc : Continuous fun q => ℓ i ⬝ᵥ q := continuous_const.dotProduct continuous_id
    rcases lt_trichotomy (ℓ i ⬝ᵥ p) 0 with h | h | h
    · convert isClosed_le hc (continuous_const (y := (0 : ℝ))) using 1
      ext q; simp [sgn, sign_neg h, le_iff_eq_or_lt, sign_eq_neg_one_iff]
    · convert isClosed_eq hc (continuous_const (y := (0 : ℝ))) using 1
      ext q; simp [sgn, h]
    · convert isClosed_le (continuous_const (y := (0 : ℝ))) hc using 1
      ext q; simp [sgn, sign_pos h, le_iff_eq_or_lt, eq_comm (a := (0 : ℝ)),
        sign_eq_one_iff]
  · refine mem_closure_of_tendsto (f := fun t : ℝ => q + t • p) (b := 𝓝[>] 0)
      (tendsto_nhdsWithin_of_tendsto_nhds ((by fun_prop : Continuous fun t : ℝ => q + t • p).tendsto'
        0 q (by simp))) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine funext fun i => ?_
    simp only [sgn, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases hq i with h | h
    · simp [sgn_eq_zero.1 h, sign_mul, sign_pos ht]
    · have h' : SignType.sign (ℓ i ⬝ᵥ q) = SignType.sign (ℓ i ⬝ᵥ p) := h
      rcases lt_trichotomy (ℓ i ⬝ᵥ p) 0 with hp | hp | hp
      · rw [sign_neg hp, sign_eq_neg_one_iff] at h' ⊢; linarith [mul_neg_of_pos_of_neg ht hp]
      · rw [hp] at h' ⊢; simpa using h'
      · rw [sign_pos hp, sign_eq_one_iff] at h' ⊢; linarith [mul_pos ht hp]

/-- **The lattice criterion for lines.** The arrangement is latticial iff no two points carry
every line between them. -/
theorem lattice_iff_not_twoPencil [Fintype ι] : Lattice (cov ℓ) ↔ ¬ TwoPencil ℓ := by
  rw [lattice_iff (fun _ hX _ hY => comp_mem_cov hX hY) fun _ => neg_mem_cov]
  simp only [cov, Set.exists_range_iff, TwoPencil, sgn_eq_zero]

/-- The triple product `det (u, v, w)`: it vanishes iff the lines `u`, `v`, `w` are concurrent. -/
def tp {R : Type*} [CommRing R] (u v w : Fin 3 → R) : R :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- The line `w` passes through the vertex `u ⨯₃ v` of the lines `u`, `v` iff `tp u v w = 0`. -/
theorem dot_cross (u v w : Fin 3 → ℝ) : w ⬝ᵥ (u ⨯₃ v) = tp u v w := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three, tp]; ring

/-- The line `i` is bigonal (or a monogon): it carries at most two vertices, `i ∩ j` and `i ∩ k`,
every line passing through one of them. -/
def Bigonal {R : Type*} [CommRing R] (ℓ : ι → Fin 3 → R) (i : ι) : Prop :=
  ∃ j k, j ≠ i ∧ k ≠ i ∧ ∀ m, tp (ℓ i) (ℓ j) (ℓ m) = 0 ∨ tp (ℓ i) (ℓ k) (ℓ m) = 0

/-- No vertex lies on every line (so the lines are distinct and not all concurrent). -/
def NoCommonVertex {R : Type*} [CommRing R] (ℓ : ι → Fin 3 → R) : Prop :=
  ∀ i j, i ≠ j → ∃ m, tp (ℓ i) (ℓ j) (ℓ m) ≠ 0

/-- **Condition a) is necessary**: a bigonal line breaks the lattice property. -/
theorem not_lattice_of_bigonal [Fintype ι] (hnd : NoCommonVertex ℓ) {i : ι} (h : Bigonal ℓ i) :
    ¬ Lattice (cov ℓ) := by
  rw [lattice_iff_not_twoPencil, not_not]
  obtain ⟨j, k, hj, hk, h⟩ := h
  have hne : ∀ j, j ≠ i → sgn ℓ (ℓ i ⨯₃ ℓ j) ≠ 0 := fun j hj h0 => by
    obtain ⟨m, hm⟩ := hnd i j hj.symm
    exact hm (by rw [← dot_cross]; exact sgn_eq_zero.1 (congrFun h0 m))
  exact ⟨_, _, hne j hj, hne k hk, fun m => by simpa only [dot_cross] using h m⟩

/-- **Condition b) is necessary**: four lines with no three concurrent (`II_4`) are not
latticial; the two opposite vertices `0 ∩ 1` and `2 ∩ 3` carry all four lines. -/
theorem not_lattice_of_four (ℓ : Fin 4 → Fin 3 → ℝ)
    (h : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → tp (ℓ i) (ℓ j) (ℓ k) ≠ 0) : ¬ Lattice (cov ℓ) := by
  rw [lattice_iff_not_twoPencil, not_not]
  refine ⟨ℓ 0 ⨯₃ ℓ 1, ℓ 2 ⨯₃ ℓ 3, fun h0 => h 0 1 2 (by decide) (by decide) (by decide) ?_,
    fun h0 => h 2 3 0 (by decide) (by decide) (by decide) ?_, fun m => ?_⟩
  · rw [← dot_cross]; exact sgn_eq_zero.1 (congrFun h0 2)
  · rw [← dot_cross]; exact sgn_eq_zero.1 (congrFun h0 0)
  · fin_cases m <;> simp [dot_self_cross, dot_cross_self]

end Lines

section Counterexample

/-- `II′_{3,2}`: the lines `x = 0`, `x = z`, `x = 2z` (through `[0 : 1 : 0]`) and `y = 0`,
`y = z` (through `[1 : 0 : 0]`), with no line joining the two centres. -/
def L32 : Fin 5 → Fin 3 → ℤ := ![![1, 0, 0], ![1, 0, -1], ![1, 0, -2], ![0, 1, 0], ![0, 1, -1]]

/-- `L32` over `ℝ`. -/
def II32 : Fin 5 → Fin 3 → ℝ := fun i k => L32 i k

theorem tp_II32 (i j m : Fin 5) :
    tp (II32 i) (II32 j) (II32 m) = ((tp (L32 i) (L32 j) (L32 m) : ℤ) : ℝ) := by
  simp [tp, II32]

theorem II32_nondegenerate : NoCommonVertex II32 := by
  have : NoCommonVertex L32 := by unfold NoCommonVertex; decide
  intro i j hij; obtain ⟨m, hm⟩ := this i j hij; exact ⟨m, by rwa [tp_II32, Int.cast_ne_zero]⟩

/-- No line of `II′_{3,2}` is bigonal: each carries at least three vertices. -/
theorem II32_no_bigon (i : Fin 5) : ¬ Bigonal II32 i := by
  have : ∀ i, ¬ Bigonal L32 i := by unfold Bigonal; decide
  rintro ⟨j, k, hj, hk, h⟩
  exact this i ⟨j, k, hj, hk, fun m => by simpa only [tp_II32, Int.cast_eq_zero] using h m⟩

/-- The two centres carry every line. -/
theorem II32_twoPencil : TwoPencil II32 := by
  refine ⟨![0, 1, 0], ![1, 0, 0], fun h => ?_, fun h => ?_, fun i => ?_⟩
  · simpa [sgn, II32, L32, dotProduct, Fin.sum_univ_three] using congrFun h 3
  · simpa [sgn, II32, L32, dotProduct, Fin.sum_univ_three] using congrFun h 0
  · fin_cases i <;> simp [II32, L32, dotProduct, Fin.sum_univ_three]

/-- **`II′_{3,2}` is not latticial**, against page 24. -/
theorem II32_not_lattice : ¬ Lattice (cov II32) := fun h =>
  lattice_iff_not_twoPencil.1 h II32_twoPencil

/-- **The criterion of page 26 is false** in the edition's reading (b: « not `II_4` », which for
an arrangement without bigonal lines means « not four lines »): `II′_{3,2}` has five lines, no
bigonal line, and is not latticial. -/
theorem lattice_criterion_false :
    ¬ ∀ (n : ℕ) (ℓ : Fin n → Fin 3 → ℝ), NoCommonVertex ℓ →
      (Lattice (cov ℓ) ↔ (∀ i, ¬ Bigonal ℓ i) ∧ n ≠ 4) := fun h =>
  II32_not_lattice ((h 5 II32 II32_nondegenerate).2 ⟨II32_no_bigon, by decide⟩)

end Counterexample

end Grothendieck.Folder80Maps1
