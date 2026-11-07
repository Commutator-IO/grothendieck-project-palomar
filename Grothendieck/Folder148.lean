module

public import Mathlib

@[expose] public section


/-!
# Folder 148, pages 55–58: gluing two circles with `r` marked points is unique

Pages 49–60 of folder 148 (transcription `transcripts/148/batch-03.fr.tex`, modernised reading
`transcripts/148/148.modern.tex`, « D) Recollement ») define the multimarked Teichmüller
groupoid: each cutting circle `a` carries `r(a)` marked points forming a torsor `R_a` under
`ℤ/r(a)`, and two circles `a`, `a'` with `r(a) = r(a')` are glued along an orientation-reversing
homeomorphism once an anti-isomorphism of torsors `R_a → R_{a'}` is given. The page states that the
gluing is then « bien déterminé »; the reading justifies it: the orientation-reversing
homeomorphisms realising a given anti-isomorphism form a non-empty contractible space.

What is modelled. A circle with `r` marked points is `ℝ/ℤ` (oriented by `ℝ`) with the lifted
marked points `p : ℤ → ℝ`, strictly increasing with `p (k + r) = p k + 1` (`Marking r`); the
torsor `R_a` is `ℤ/r` acting by `k ↦ k + 1` (next point along the orientation), so that an
anti-isomorphism `ℤ/r → ℤ/r` is `k ↦ c - k` (`antiIso_eq`). An orientation-reversing
homeomorphism of circles is described by its lifts: continuous strictly antitone `F : ℝ → ℝ`
with `F (x + 1) = F x - 1`; two lifts of the same map differ by an integer, and the lift is
normalised by asking `F (p k) = q (c - k)` for all `k` (`c ∈ ℤ` lifting the anti-isomorphism).
The space `gluings P Q c ⊆ C(ℝ, ℝ)` carries the compact-open topology.
* `gluings_nonempty`: the space is non-empty, for arbitrary positions of the marked points
  (piecewise-linear interpolation `Marking.interpHomeomorph`);
* `convex_gluings`, `contractibleSpace_gluings`, `isPathConnected_gluings`: it is convex, hence
  contractible (straight-line homotopy) and path-connected, so two gluings are isotopic through
  gluings realising the same anti-isomorphism;
* `toHomeomorph`: each element is a homeomorphism of `ℝ`;
* `exists_antiIso`: an equivariant orientation-reversing homeomorphism mapping the marked points
  of `a` onto those of `a'` induces an anti-isomorphism `k ↦ c - k`, so the spaces `gluings P Q c`
  exhaust the gluings respecting the markings.

Not formalised: the identification of the space of lifts with a space of homeomorphisms of the
circle `AddCircle 1`, the case `r = 0` (where `Marking 0` is empty; the reading says the space
then has the homotopy type of a circle, the Dehn twist ambiguity), and the groupoid itself.
-/

open Set Filter Topology

namespace Grothendieck.Folder148

/-! ### Anti-isomorphisms of `ℤ/r`-torsors -/

/-- An anti-isomorphism of the torsor `ℤ/r` (a map with `u (x + 1) = u x - 1`) is `x ↦ u 0 - x`. -/
theorem antiIso_eq {r : ℕ} (u : ZMod r → ZMod r) (hu : ∀ x, u (x + 1) = u x - 1) (x : ZMod r) :
    u x = u 0 - x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  induction z using Int.induction_on with
  | zero => simp
  | succ m ih => push_cast at ih ⊢; rw [hu, ih]; ring
  | pred m ih =>
    have := hu (-(m : ZMod r) - 1)
    rw [sub_add_cancel] at this
    push_cast at ih ⊢
    linear_combination ih - this

/-! ### Circles with `r` marked points -/

/-- A circle `ℝ/ℤ` with `r` marked points, given by its lifted marked points: a strictly
increasing `pt : ℤ → ℝ` with `pt (k + r) = pt k + 1`. The marked point `pt k` has label
`k mod r` in the torsor `ℤ/r`. -/
structure Marking (r : ℕ) where
  /-- The lifted marked points. -/
  pt : ℤ → ℝ
  strictMono : StrictMono pt
  periodic : ∀ k, pt (k + r) = pt k + 1

namespace Marking

variable {r : ℕ} (P : Marking r)

/-- The standard marking by the points `k / r`. -/
noncomputable def std (r : ℕ) (hr : 0 < r) : Marking r where
  pt k := k / r
  strictMono a b h := div_lt_div_of_pos_right (by exact_mod_cast h) (by exact_mod_cast hr)
  periodic k := by
    have : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast; field_simp

theorem pt_add_mul (k m : ℤ) : P.pt (k + r * m) = P.pt k + m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have := P.periodic (k + r * m)
    rw [show k + r * ((m : ℤ) + 1) = k + r * m + r by ring, this, ih]; push_cast; ring
  | pred m ih =>
    have := P.periodic (k + r * (-(m : ℤ) - 1))
    rw [show k + r * (-(m : ℤ) - 1) + r = k + r * (-(m : ℤ)) by ring, ih] at this
    push_cast at this ⊢; linarith

theorem r_pos (P : Marking r) : 0 < r := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := P.periodic 0; subst h; simp at this

/-- The piecewise-linear interpolation of the marked points: `interp k = pt k`, affine on each
`[k, k + 1]`. -/
noncomputable def interp (y : ℝ) : ℝ :=
  P.pt ⌊y⌋ + Int.fract y * (P.pt (⌊y⌋ + 1) - P.pt ⌊y⌋)

theorem interp_intCast (k : ℤ) : P.interp k = P.pt k := by
  simp [interp]

theorem interp_add (y : ℝ) : P.interp (y + r) = P.interp y + 1 := by
  simp only [interp, Int.floor_add_natCast, Int.fract_add_natCast]
  rw [P.periodic, show ⌊y⌋ + (r : ℤ) + 1 = ⌊y⌋ + 1 + r by ring, P.periodic]; ring

theorem interp_eqOn (n : ℤ) :
    EqOn P.interp (fun y => P.pt n + (y - n) * (P.pt (n + 1) - P.pt n)) (Icc (n : ℝ) (n + 1)) := by
  intro y ⟨h1, h2⟩
  rcases h2.lt_or_eq with h2 | h2
  · have hf : ⌊y⌋ = n := Int.floor_eq_iff.2 ⟨h1, h2⟩
    simp only [interp, Int.fract, hf]
  · subst h2
    have := P.interp_intCast (n + 1)
    push_cast at this
    rw [this]; ring

theorem continuous_interp : Continuous P.interp := by
  have hlf : LocallyFinite (fun n : ℤ => Icc (n : ℝ) (n + 1)) :=
    locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
      (tendsto_atBot_add_const_right _ 1 (tendsto_intCast_atBot_iff.2 tendsto_id))
  refine hlf.continuous ?_ (fun _ => isClosed_Icc) fun n => ?_
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌊y⌋, Int.floor_le y, (Int.lt_floor_add_one y).le⟩
  · exact (ContinuousOn.congr (by fun_prop) (P.interp_eqOn n))

theorem strictMono_interp : StrictMono P.interp := by
  intro y z hyz
  have hΔ : ∀ k : ℤ, 0 < P.pt (k + 1) - P.pt k := fun k => sub_pos.2 (P.strictMono (by omega))
  rcases (Int.floor_mono hyz.le).lt_or_eq with h | h
  · have h1 : P.interp y < P.pt (⌊y⌋ + 1) := by
      have := mul_lt_mul_of_pos_right (Int.fract_lt_one y) (hΔ ⌊y⌋)
      simp only [interp]; linarith
    have h2 : P.pt (⌊y⌋ + 1) ≤ P.pt ⌊z⌋ := P.strictMono.monotone (by omega)
    have h3 : P.pt ⌊z⌋ ≤ P.interp z := by
      have := mul_nonneg (Int.fract_nonneg z) (hΔ ⌊z⌋).le
      simp only [interp]; linarith
    linarith
  · have hf : Int.fract y < Int.fract z := by
      simp only [Int.fract, h]; linarith
    simp only [interp, h]
    have := mul_lt_mul_of_pos_right hf (hΔ ⌊z⌋)
    linarith

theorem interp_mul (m : ℤ) : P.interp ((r : ℝ) * m) = P.pt 0 + m := by
  have := P.interp_intCast (r * m)
  push_cast at this
  rw [this, show (r : ℤ) * m = 0 + r * m by ring, P.pt_add_mul]

theorem surjective_interp : Function.Surjective P.interp := by
  intro t
  have hr : (0 : ℝ) < r := by exact_mod_cast P.r_pos
  set a := (r : ℝ) * ⌊t - P.pt 0⌋
  set b := (r : ℝ) * ⌈t - P.pt 0⌉
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (by exact_mod_cast Int.floor_le_ceil _) hr.le
  have := intermediate_value_Icc hab P.continuous_interp.continuousOn
  have ht : t ∈ Icc (P.interp a) (P.interp b) := by
    rw [P.interp_mul, P.interp_mul]
    exact ⟨by linarith [Int.floor_le (t - P.pt 0)], by linarith [Int.le_ceil (t - P.pt 0)]⟩
  obtain ⟨y, -, hy⟩ := this ht
  exact ⟨y, hy⟩

/-- The interpolation as an orientation-preserving homeomorphism of `ℝ`. -/
noncomputable def interpHomeomorph : ℝ ≃ₜ ℝ :=
  (P.strictMono_interp.orderIsoOfSurjective P.interp P.surjective_interp).toHomeomorph

@[simp] theorem interpHomeomorph_apply (y : ℝ) : P.interpHomeomorph y = P.interp y := rfl

theorem interpHomeomorph_symm_add (x : ℝ) :
    P.interpHomeomorph.symm (x + 1) = P.interpHomeomorph.symm x + r := by
  apply P.interpHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, interpHomeomorph_apply, interp_add, ← interpHomeomorph_apply,
    Homeomorph.apply_symm_apply]

theorem interpHomeomorph_symm_strictMono : StrictMono P.interpHomeomorph.symm :=
  (P.strictMono_interp.orderIsoOfSurjective P.interp P.surjective_interp).symm.strictMono

theorem interpHomeomorph_symm_pt (k : ℤ) : P.interpHomeomorph.symm (P.pt k) = k := by
  apply P.interpHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, interpHomeomorph_apply, interp_intCast]

end Marking

/-! ### The space of gluings -/

variable {r : ℕ}

/-- The gluings of `a` (marking `P`) to `a'` (marking `Q`) realising the anti-isomorphism
`k ↦ c - k` of `ℤ/r`-torsors: lifts `F` of orientation-reversing homeomorphisms of the circle
(`F` continuous, strictly antitone, `F (x + 1) = F x - 1`), normalised by `F (p k) = q (c - k)`. -/
def gluings (P Q : Marking r) (c : ℤ) : Set C(ℝ, ℝ) :=
  {F | StrictAnti F ∧ (∀ x, F (x + 1) = F x - 1) ∧ ∀ k, F (P.pt k) = Q.pt (c - k)}

/-- The space of gluings is non-empty: `F = interp_Q ∘ (c - ·) ∘ interp_P⁻¹`. -/
theorem gluings_nonempty (P Q : Marking r) (c : ℤ) : (gluings P Q c).Nonempty := by
  refine ⟨⟨fun x => Q.interp (c - P.interpHomeomorph.symm x), by
    exact Q.continuous_interp.comp (continuous_const.sub P.interpHomeomorph.symm.continuous)⟩,
    ?_, ?_, ?_⟩
  · intro x y hxy
    have := P.interpHomeomorph_symm_strictMono hxy
    exact Q.strictMono_interp (by linarith)
  · intro x
    have := Q.interp_add (c - P.interpHomeomorph.symm x - r)
    simp only [ContinuousMap.coe_mk, Marking.interpHomeomorph_symm_add, sub_add_cancel,
      ← sub_sub] at this ⊢
    linarith
  · intro k
    simp [Marking.interpHomeomorph_symm_pt, ← Q.interp_intCast]

/-- The space of gluings is convex in `C(ℝ, ℝ)`. -/
theorem convex_gluings (P Q : Marking r) (c : ℤ) : Convex ℝ (gluings P Q c) := by
  intro F ⟨hF1, hF2, hF3⟩ G ⟨hG1, hG2, hG3⟩ a b ha hb hab
  refine ⟨fun x y hxy => ?_, fun x => ?_, fun k => ?_⟩
  · simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    have h1 := hF1 hxy
    have h2 := hG1 hxy
    rcases ha.lt_or_eq with ha | ha
    · nlinarith [mul_le_mul_of_nonneg_left h2.le hb]
    · subst ha; simp at hab; subst hab; simpa using h2
  · simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hF2, hG2]
    linear_combination -hab
  · simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hF3, hG3]
    linear_combination (Q.pt (c - k)) * hab

theorem gluings_add_intCast {P Q : Marking r} {c : ℤ} {F : C(ℝ, ℝ)} (hF : F ∈ gluings P Q c)
    (x : ℝ) (m : ℤ) : F (x + m) = F x - m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih => push_cast at ih ⊢; rw [← add_assoc, hF.2.1, ih]; ring
  | pred m ih =>
    have := hF.2.1 (x + (-(m : ℝ) - 1))
    rw [show x + (-(m : ℝ) - 1) + 1 = x + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring, ih] at this
    push_cast at this ⊢; linarith

theorem surjective_of_mem_gluings {P Q : Marking r} {c : ℤ} {F : C(ℝ, ℝ)}
    (hF : F ∈ gluings P Q c) : Function.Surjective F := by
  intro t
  set a : ℝ := ((⌊F 0 - t⌋ : ℤ) : ℝ)
  set b : ℝ := ((⌈F 0 - t⌉ : ℤ) : ℝ)
  have hab : a ≤ b := by simp only [a, b]; exact_mod_cast Int.floor_le_ceil _
  have ht : t ∈ Icc (F b) (F a) := by
    rw [← zero_add a, ← zero_add b, gluings_add_intCast hF, gluings_add_intCast hF]
    exact ⟨by linarith [Int.le_ceil (F 0 - t)], by linarith [Int.floor_le (F 0 - t)]⟩
  obtain ⟨y, -, hy⟩ := intermediate_value_Icc' hab F.continuous.continuousOn ht
  exact ⟨y, hy⟩

/-- Each gluing is a homeomorphism of `ℝ` (an orientation-reversing one). -/
noncomputable def toHomeomorph {P Q : Marking r} {c : ℤ} (F : C(ℝ, ℝ)) (hF : F ∈ gluings P Q c) :
    ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (fun x => -F x) (fun _ _ h => neg_lt_neg (hF.1 h))
    (fun t => (surjective_of_mem_gluings hF (-t)).imp fun _ h => by simp [h])).toHomeomorph.trans
    (Homeomorph.neg ℝ)

@[simp] theorem toHomeomorph_apply {P Q : Marking r} {c : ℤ} (F : C(ℝ, ℝ))
    (hF : F ∈ gluings P Q c) (x : ℝ) : toHomeomorph F hF x = F x := by
  simp only [toHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_neg]
  exact neg_neg _

/-- A strictly antitone map sending the marked points of `a` onto those of `a'` induces an
anti-isomorphism `k ↦ c - k` of the labels: the spaces `gluings P Q c` exhaust the gluings
respecting the markings. -/
theorem exists_antiIso (P Q : Marking r) (F : ℝ → ℝ) (hF : StrictAnti F)
    (hmaps : ∀ k, ∃ j, F (P.pt k) = Q.pt j) (honto : ∀ j, ∃ k, F (P.pt k) = Q.pt j) :
    ∃ c : ℤ, ∀ k, F (P.pt k) = Q.pt (c - k) := by
  choose σ hσ using hmaps
  have anti : StrictAnti σ := fun k l hkl => by
    have := hF (P.strictMono hkl)
    rw [hσ, hσ] at this
    exact Q.strictMono.lt_iff_lt.1 this
  have surj : ∀ j, ∃ k, σ k = j := fun j => by
    obtain ⟨k, hk⟩ := honto j
    exact ⟨k, Q.strictMono.injective ((hσ k).symm.trans hk)⟩
  have step : ∀ k, σ (k + 1) = σ k - 1 := fun k => by
    have h1 : σ (k + 1) < σ k := anti (by omega)
    obtain ⟨l, hl⟩ := surj (σ k - 1)
    rcases le_or_gt l k with h | h
    · have := anti.antitone h; omega
    · have := anti.antitone (show k + 1 ≤ l by omega); omega
  refine ⟨σ 0, fun k => ?_⟩
  rw [hσ]
  congr 1
  induction k using Int.induction_on with
  | zero => simp
  | succ m ih => rw [step, ih]; ring
  | pred m ih =>
    have := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -m by ring, ih] at this
    omega

/-- **Uniqueness of gluing (pages 55–58).** The orientation-reversing homeomorphisms between two
circles with `r` marked points realising a given anti-isomorphism of `ℤ/r`-torsors form a
non-empty contractible space. -/
theorem contractibleSpace_gluings (P Q : Marking r) (c : ℤ) : ContractibleSpace (gluings P Q c) :=
  (convex_gluings P Q c).contractibleSpace (gluings_nonempty P Q c)

/-- Two gluings realising the same anti-isomorphism are isotopic through such gluings. -/
theorem isPathConnected_gluings (P Q : Marking r) (c : ℤ) : IsPathConnected (gluings P Q c) := by
  have := contractibleSpace_gluings P Q c
  exact isPathConnected_iff_pathConnectedSpace.2 inferInstance

end Grothendieck.Folder148

/-!
# Folder 148, pages 49 and 55–58: gluings as homeomorphisms of `AddCircle 1`; the case `r = 0`

Added after the lift model above.
* `gluingsHomeomorph`: descending a normalised lift to the circle `AddCircle 1` is a
  homeomorphism (compact-open topologies) from `gluings P Q c` onto `circleGluings P Q c`, the
  orientation-reversing homeomorphisms of the circle (bijective continuous maps with a strictly
  antitone continuous lift) sending the marked point `p k` to `q (c - k)`; hence
  `contractibleSpace_circleGluings`. The key steps: such a lift has degree `-1`
  (`lift_add_one`), it can be normalised (`exists_gluing_of_mem`), and two normalised lifts whose
  circle maps are uniformly `ε`-close are uniformly `ε`-close (`abs_sub_lt_of_dist_lt`).
* The case `r = 0`: the orientation-reversing homeomorphisms of the circle split as the image of
  `0` times those fixing `0` (`circleReversingHomeomorph`), so they have the homotopy type of the
  circle (`circleReversingHomotopyEquiv`) and fundamental group `ℤ`
  (`circleReversing_fundamentalGroup`, through `AddCircle.windingNumberIso`).
Not formalised: that the generator of this `ℤ` is the Dehn twist, the gluing for `r = 0` once a
`ℤ`-torsor of framings is given, and the groupoid itself.
-/

open scoped ContinuousMap

namespace Grothendieck.Folder148

/-! ### Normalised lifts and homeomorphisms of the circle `AddCircle 1` -/

theorem coe_eq_coe_iff {a b : ℝ} : (a : UnitAddCircle) = b ↔ ∃ n : ℤ, a - b = n := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  exact ⟨fun ⟨n, h⟩ => ⟨-n, by simp at h; push_cast; linarith⟩,
    fun ⟨n, h⟩ => ⟨-n, by simp; linarith⟩⟩

theorem dist_coe (a b : ℝ) :
    dist (a : UnitAddCircle) b = |(a - b) - round (a - b)| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]

/-- A continuous function which stays within `ε ≤ 1/2` of the integers and vanishes somewhere
stays within `ε` of `0`. -/
theorem abs_lt_of_near_int {D : ℝ → ℝ} (hD : Continuous D) {a : ℝ} (ha : D a = 0) {ε : ℝ}
    (hε : ε ≤ 1 / 2) (h : ∀ x, |D x - round (D x)| < ε) (x : ℝ) : |D x| < ε := by
  have hu : IsOpen {x | |D x| < ε} := isOpen_lt (by fun_prop) continuous_const
  have hv : IsOpen {x | 1 - ε < |D x|} := isOpen_lt continuous_const (by fun_prop)
  have hdis : Disjoint {x | |D x| < ε} {x | 1 - ε < |D x|} :=
    disjoint_left.2 fun y (h1 : |D y| < ε) (h2 : 1 - ε < |D y|) => by linarith
  have hcov : univ ⊆ {x | |D x| < ε} ∪ {x | 1 - ε < |D x|} := fun y _ => by
    by_cases h0 : round (D y) = 0
    · left; simpa [h0] using h y
    · right
      have h1 : (1 : ℝ) ≤ |(round (D y) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
      have := abs_sub_abs_le_abs_sub (round (D y) : ℝ) (D y)
      rw [abs_sub_comm] at this
      show 1 - ε < |D y|; linarith [h y]
  exact isPreconnected_univ.subset_left_of_subset_union hu hv hdis hcov
    ⟨a, trivial, by simpa [ha] using h a⟩ (mem_univ x)

/-- A continuous integer-valued function vanishing somewhere vanishes everywhere. -/
theorem eq_zero_of_intValued {D : ℝ → ℝ} (hD : Continuous D) {a : ℝ} (ha : D a = 0)
    (h : ∀ x, ∃ n : ℤ, D x = n) (x : ℝ) : D x = 0 := by
  obtain ⟨n, hn⟩ := h x
  have := abs_lt_of_near_int hD ha le_rfl (fun y => by obtain ⟨m, hm⟩ := h y; simp [hm]) x
  rw [hn] at this ⊢
  exact_mod_cast Int.abs_lt_one_iff.1 (by exact_mod_cast this.trans (by norm_num : (1 / 2 : ℝ) < 1))

/-- The map of the circle `AddCircle 1` induced by a lift `F` with `F (x + 1) = F x - 1`. -/
noncomputable def descend (F : C(ℝ, ℝ)) (hF : ∀ x, F (x + 1) = F x - 1) :
    C(UnitAddCircle, UnitAddCircle) where
  toFun := Function.Periodic.lift (f := fun x => (F x : UnitAddCircle)) (c := 1)
    fun x => by simp [hF]
  continuous_toFun := continuous_quot_lift _ (by fun_prop)

@[simp] theorem descend_coe (F : C(ℝ, ℝ)) (hF : ∀ x, F (x + 1) = F x - 1) (x : ℝ) :
    descend F hF x = F x := rfl


variable {r : ℕ}

/-- The orientation-reversing homeomorphisms `a → a'` of the circle `AddCircle 1` respecting the
markings through the anti-isomorphism `k ↦ c - k`: bijective continuous maps (homeomorphisms,
the circle being compact) admitting a strictly antitone continuous lift, sending the marked
point `p k` to `q (c - k)`. -/
def circleGluings (P Q : Marking r) (c : ℤ) : Set C(UnitAddCircle, UnitAddCircle) :=
  {f | Function.Bijective f ∧ (∃ F : ℝ → ℝ, Continuous F ∧ StrictAnti F ∧ ∀ x : ℝ, f x = F x) ∧
    ∀ k, f (P.pt k) = Q.pt (c - k)}

theorem descend_mem {P Q : Marking r} {c : ℤ} {F : C(ℝ, ℝ)} (hF : F ∈ gluings P Q c) :
    descend F hF.2.1 ∈ circleGluings P Q c := by
  refine ⟨⟨fun y z h => ?_, fun y => ?_⟩, ⟨F, F.continuous, hF.1, fun _ => rfl⟩,
    fun k => by simp [hF.2.2]⟩
  · induction y using QuotientAddGroup.induction_on
    induction z using QuotientAddGroup.induction_on
    rename_i y z
    obtain ⟨n, hn⟩ := coe_eq_coe_iff.1 h
    have : F y = F (z - n) := by
      rw [show z - (n : ℝ) = z + ((-n : ℤ) : ℝ) by push_cast; ring, gluings_add_intCast hF]
      push_cast; linarith
    exact coe_eq_coe_iff.2 ⟨-n, by push_cast; linarith [hF.1.injective this]⟩
  · induction y using QuotientAddGroup.induction_on
    obtain ⟨x, hx⟩ := surjective_of_mem_gluings hF ‹ℝ›
    exact ⟨x, by simp [hx]⟩

/-- Normalised lifts as homeomorphisms of the circle. -/
noncomputable def toCircle (P Q : Marking r) (c : ℤ) :
    gluings P Q c → circleGluings P Q c :=
  fun F => ⟨descend F F.2.2.1, descend_mem F.2⟩

theorem toCircle_injective (P Q : Marking r) (c : ℤ) : Function.Injective (toCircle P Q c) := by
  intro F G h
  have h' : ∀ x, ((F.1 x : ℝ) : UnitAddCircle) = G.1 x := fun x =>
    congrArg (fun f : circleGluings P Q c => f.1 x) h
  refine Subtype.ext (ContinuousMap.ext fun x => sub_eq_zero.1 ?_)
  exact eq_zero_of_intValued (D := fun x => F.1 x - G.1 x) (by fun_prop) (a := P.pt 0)
    (by simp [F.2.2.2, G.2.2.2]) (fun x => coe_eq_coe_iff.1 (h' x)) x


theorem coe_add_one (x : ℝ) : ((x + 1 : ℝ) : UnitAddCircle) = x :=
  coe_eq_coe_iff.2 ⟨1, by ring⟩

/-- A strictly antitone lift of a homeomorphism of the circle has degree `-1`. -/
theorem lift_add_one {f : C(UnitAddCircle, UnitAddCircle)} (hf : Function.Injective f)
    {F : ℝ → ℝ} (hc : Continuous F) (ha : StrictAnti F) (hF : ∀ x : ℝ, f x = F x) (x : ℝ) :
    F (x + 1) = F x - 1 := by
  have hper : ∀ y, ∃ n : ℤ, F (y + 1) - F y = n := fun y =>
    coe_eq_coe_iff.1 (by rw [← hF, ← hF, coe_add_one])
  have hx := eq_zero_of_intValued (D := fun y => F (y + 1) - F y - (F 1 - F 0)) (by fun_prop)
    (a := 0) (by simp) (fun y => by
      obtain ⟨m, hm⟩ := hper y; obtain ⟨l, hl⟩ := hper 0
      exact ⟨m - l, by push_cast; rw [zero_add] at hl; linarith⟩) x
  suffices F 1 = F 0 - 1 by linarith
  obtain ⟨m, hm⟩ := hper 0
  rw [zero_add] at hm
  have hm1 : m < 0 := by exact_mod_cast (by linarith [ha zero_lt_one] : (m : ℝ) < 0)
  rcases (show m < -1 ∨ m = -1 by omega) with hm2 | hm2
  · exfalso
    have hm2' : (m : ℝ) ≤ -2 := by exact_mod_cast (show m ≤ -2 by omega)
    obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := intermediate_value_Icc' zero_le_one hc.continuousOn
      (show F 0 - 1 ∈ Icc (F 1) (F 0) from ⟨by linarith, by linarith⟩)
    have h1 : f t = f (0 : ℝ) := by
      rw [hF, hF, ht]; exact coe_eq_coe_iff.2 ⟨-1, by push_cast; ring⟩
    obtain ⟨k, hk⟩ := coe_eq_coe_iff.1 (hf h1)
    have hk0 : 0 ≤ k := by exact_mod_cast (show (0 : ℝ) ≤ k by linarith)
    have hk1 : k ≤ 1 := by exact_mod_cast (show (k : ℝ) ≤ 1 by linarith)
    interval_cases k
    · simp at hk; subst hk; linarith
    · simp at hk; rw [show t = 1 by linarith] at ht; linarith
  · rw [hm2] at hm; push_cast at hm; linarith

theorem exists_gluing_of_mem {P Q : Marking r} {c : ℤ} {f : C(UnitAddCircle, UnitAddCircle)}
    (hf : f ∈ circleGluings P Q c) :
    ∃ (G : C(ℝ, ℝ)) (hG : G ∈ gluings P Q c), descend G hG.2.1 = f := by
  obtain ⟨hb, ⟨F, hc, ha, hF⟩, hk⟩ := hf
  have h1 := lift_add_one hb.1 hc ha hF
  have hm : ∀ k, ∃ m : ℤ, F (P.pt k) - Q.pt (c - k) = m := fun k =>
    coe_eq_coe_iff.1 (by rw [← hF, hk])
  choose m hm using hm
  have hstep : ∀ k, m (k + 1) = m k := fun k => by
    have hp2 : P.pt (k + 1) ≤ P.pt k + 1 := by
      rw [← P.periodic]; exact P.strictMono.monotone (by have := P.r_pos; omega)
    have hq1 : Q.pt (c - (k + 1)) < Q.pt (c - k) := Q.strictMono (by omega)
    have hq2 : Q.pt (c - k) ≤ Q.pt (c - (k + 1)) + 1 := by
      rw [← Q.periodic]; exact Q.strictMono.monotone (by have := Q.r_pos; omega)
    have hF1 : F (P.pt k + 1) ≤ F (P.pt (k + 1)) := ha.antitone hp2
    have hF2 : F (P.pt (k + 1)) < F (P.pt k) := ha (P.strictMono (by omega))
    rw [h1] at hF1
    have : m (k + 1) - m k < 1 := by
      exact_mod_cast (by linarith [hm k, hm (k + 1)] : (m (k + 1) : ℝ) - m k < 1)
    have : -1 < m (k + 1) - m k := by
      exact_mod_cast (by linarith [hm k, hm (k + 1)] : -1 < (m (k + 1) : ℝ) - m k)
    omega
  have hconst : ∀ k, m k = m 0 := fun k => by
    induction k using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep, ih]
    | pred k ih => rw [← ih, ← hstep, sub_add_cancel]
  refine ⟨⟨fun x => F x - m 0, by fun_prop⟩, ⟨fun x y h => by simpa using ha h,
    fun x => by simp [h1]; ring, fun k => ?_⟩, ?_⟩
  · simp only [ContinuousMap.coe_mk]; linarith [hconst k ▸ hm k]
  · ext y
    induction y using QuotientAddGroup.induction_on
    simp only [descend_coe, ContinuousMap.coe_mk, hF]
    exact coe_eq_coe_iff.2 ⟨-m 0, by push_cast; ring⟩

theorem toCircle_surjective (P Q : Marking r) (c : ℤ) : Function.Surjective (toCircle P Q c) :=
  fun f => let ⟨G, hG, h⟩ := exists_gluing_of_mem f.2; ⟨⟨G, hG⟩, Subtype.ext h⟩


theorem continuous_toCircle (P Q : Marking r) (c : ℤ) : Continuous (toCircle P Q c) := by
  refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
  have hq : Topology.IsQuotientMap (Prod.map id (↑) : gluings P Q c × ℝ → _ × UnitAddCircle) :=
    (IsOpenMap.id.prodMap QuotientAddGroup.isOpenMap_coe).isQuotientMap (by fun_prop)
      (Function.surjective_id.prodMap QuotientAddGroup.mk_surjective)
  refine hq.continuous_iff.2 ?_
  change Continuous fun p : gluings P Q c × ℝ => ((p.1.1 p.2 : ℝ) : UnitAddCircle)
  fun_prop

/-- Two normalised lifts whose circle maps are uniformly `ε`-close, `ε ≤ 1/2`, are uniformly
`ε`-close. -/
theorem abs_sub_lt_of_dist_lt {P Q : Marking r} {c : ℤ} (F G : gluings P Q c) {ε : ℝ}
    (hε : ε ≤ 1 / 2) (h : dist (toCircle P Q c F) (toCircle P Q c G) < ε) (x : ℝ) :
    |F.1 x - G.1 x| < ε :=
  abs_lt_of_near_int (D := fun x => F.1 x - G.1 x) (by fun_prop) (a := P.pt 0)
    (by simp [F.2.2.2, G.2.2.2]) hε (fun y => by
      rw [← dist_coe]
      exact (ContinuousMap.dist_apply_le_dist (y : UnitAddCircle)).trans_lt h) x

/-- **The normalised lifts are the homeomorphisms of the circle.** Descending to `AddCircle 1`
is a homeomorphism from the space of normalised lifts onto the space of orientation-reversing
homeomorphisms of the circle respecting the markings (compact-open topologies). -/
noncomputable def gluingsHomeomorph (P Q : Marking r) (c : ℤ) :
    gluings P Q c ≃ₜ circleGluings P Q c where
  toEquiv := Equiv.ofBijective _ ⟨toCircle_injective P Q c, toCircle_surjective P Q c⟩
  continuous_toFun := continuous_toCircle P Q c
  continuous_invFun := by
    set e := Equiv.ofBijective _ ⟨toCircle_injective P Q c, toCircle_surjective P Q c⟩
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    refine Metric.continuous_iff.2 fun ⟨f₀, x₀⟩ ε hε => ?_
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 (e.symm f₀).1.continuous x₀ (ε / 2)
      (half_pos hε)
    refine ⟨min (min (ε / 2) (1 / 2)) δ, by positivity, fun ⟨f, x⟩ h => ?_⟩
    rw [Prod.dist_eq] at h
    have h1 := abs_sub_lt_of_dist_lt (e.symm f) (e.symm f₀) (min_le_right _ _)
      (by
        rw [show toCircle P Q c (e.symm f) = f from e.apply_symm_apply f,
          show toCircle P Q c (e.symm f₀) = f₀ from e.apply_symm_apply f₀]
        exact ((le_max_left _ _).trans_lt h).trans_le (min_le_left _ _)) x
    have h2 := hδε x (((le_max_right _ _).trans_lt h).trans_le (min_le_right _ _))
    simp only [Function.uncurry_apply_pair, Real.dist_eq] at h2 ⊢
    exact ((abs_sub_le _ _ _).trans_lt (add_lt_add (h1.trans_le (min_le_left _ _)) h2)).trans_eq
      (add_halves ε)

@[simp] theorem gluingsHomeomorph_apply (P Q : Marking r) (c : ℤ) (F : gluings P Q c) (x : ℝ) :
    (gluingsHomeomorph P Q c F).1 x = F.1 x := rfl

/-- **Uniqueness of gluing on the circle (pages 55–58).** The orientation-reversing
homeomorphisms of `AddCircle 1` between two circles with `r` marked points realising a given
anti-isomorphism of `ℤ/r`-torsors form a non-empty contractible space. -/
theorem contractibleSpace_circleGluings (P Q : Marking r) (c : ℤ) :
    ContractibleSpace (circleGluings P Q c) :=
  have := contractibleSpace_gluings P Q c
  (gluingsHomeomorph P Q c).symm.contractibleSpace


/-! ### The case `r = 0`: a circle without marked points -/

/-- The orientation-reversing homeomorphisms of the circle `AddCircle 1`, with no marking. -/
def circleReversing : Set C(UnitAddCircle, UnitAddCircle) :=
  {f | Function.Bijective f ∧ ∃ F : ℝ → ℝ, Continuous F ∧ StrictAnti F ∧ ∀ x : ℝ, f x = F x}

/-- The orientation-reversing homeomorphisms fixing `0`: those respecting the single marked
point `0` on both sides. -/
abbrev circleReversing₀ : Set C(UnitAddCircle, UnitAddCircle) :=
  circleGluings (Marking.std 1 one_pos) (Marking.std 1 one_pos) 0

theorem sub_const_mem {f : C(UnitAddCircle, UnitAddCircle)} (hf : f ∈ circleReversing) :
    f - ContinuousMap.const _ (f 0) ∈ circleReversing₀ := by
  obtain ⟨hb, F, hc, ha, hF⟩ := hf
  refine ⟨(Equiv.subRight (f 0)).bijective.comp hb, ⟨fun x => F x - F 0, by fun_prop,
    fun x y h => by simpa using ha h, fun x => ?_⟩, fun k => ?_⟩
  · rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, hF, ← AddCircle.coe_zero, hF,
      AddCircle.coe_sub]
  · have : ((k : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := coe_eq_coe_iff.2 ⟨k, by ring⟩
    simp [Marking.std, this]


theorem add_const_mem {g : C(UnitAddCircle, UnitAddCircle)} (hg : g ∈ circleReversing₀)
    (a : UnitAddCircle) : g + ContinuousMap.const _ a ∈ circleReversing := by
  obtain ⟨hb, ⟨G, hc, ha, hG⟩, -⟩ := hg
  induction a using QuotientAddGroup.induction_on with | H A =>
  exact ⟨(Equiv.addRight _).bijective.comp hb, fun x => G x + A, by fun_prop,
    fun x y h => by simpa using ha h, fun x => by simp [hG]⟩

theorem apply_zero_of_mem₀ {g : C(UnitAddCircle, UnitAddCircle)} (hg : g ∈ circleReversing₀) :
    g 0 = 0 := by
  simpa [Marking.std] using hg.2.2 0

/-- An orientation-reversing homeomorphism of the circle is the image of `0` together with an
orientation-reversing homeomorphism fixing `0`. -/
noncomputable def circleReversingHomeomorph :
    circleReversing ≃ₜ UnitAddCircle × circleReversing₀ where
  toFun f := (f.1 0, ⟨_, sub_const_mem f.2⟩)
  invFun p := ⟨_, add_const_mem p.2.2 p.1⟩
  left_inv f := by ext; simp
  right_inv p := by ext <;> simp [apply_zero_of_mem₀ p.2.2]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


/-- **The case `r = 0` (page 49).** Without marked points the orientation-reversing
homeomorphisms of the circle have the homotopy type of the circle. -/
noncomputable def circleReversingHomotopyEquiv : circleReversing ≃ₕ UnitAddCircle :=
  have := contractibleSpace_circleGluings (Marking.std 1 one_pos) (Marking.std 1 one_pos) 0
  circleReversingHomeomorph.toHomotopyEquiv.trans <|
    ((ContinuousMap.HomotopyEquiv.refl _).prodCongr
      (ContractibleSpace.hequiv_unit circleReversing₀).some).trans
      (Homeomorph.prodUnique UnitAddCircle Unit).toHomotopyEquiv

/-- Hence the ambiguity of gluing along unmarked circles: the fundamental group of the space of
gluings is `ℤ` (the reading identifies its generator, the full rotation of one side, with the
Dehn twist along the glued circle). -/
noncomputable def circleReversing_fundamentalGroup (f : circleReversing) :
    FundamentalGroup circleReversing f ≃* Multiplicative ℤ :=
  MulEquiv.trans (M := FundamentalGroup circleReversing f)
    ((FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      circleReversingHomotopyEquiv).fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk f))
    (AddCircle.windingNumberIso (circleReversingHomotopyEquiv f))

end Grothendieck.Folder148
