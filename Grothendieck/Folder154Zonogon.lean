module

public import Mathlib

@[expose] public section


/-!
# Folder 154, page 153: the shadow of the `ν`-cube is a `2ν`-gon

Finding `154-cube-shadow-2nu-gon` (`src/content/findings.ts`). Page 153 writes, under the counts
`2^ν` and `ν 2^(ν−1)` of the cube of generisations, « Produit des diagonales d'un polygone convexe
d'ordre `2ν` », and draws below it a closed outline through eight points (redraw 08-23, a machine
redraw overlay-checked against the scan, not checked by a reader). The finding reads it as the
classical fact that the cube, a product of `ν` segments, projects to the plane onto a centrally
symmetric convex polygon with `2ν` vertices (a zonogon). The page states the line and draws the
figure; the statement proved here, and its proof, are the edition's.

**The statement.** A zonogon is the Minkowski sum of `ν` segments `[pᵢ, qᵢ]` of `ℝ²`; it is the image
of the cube `[−1, 1]^ν` under `a ↦ c + ∑ aᵢ vᵢ`, with centre `c = ∑ (pᵢ + qᵢ)/2` and half-directions
`vᵢ = (qᵢ − pᵢ)/2` (`sum_segment_eq`). Then:

* `zono_symm`, `sum_segment_symm`: it is centrally symmetric about `c` (no hypothesis);
* `extremePoints_zono`: in any case where the `vᵢ` are nonzero, its extreme points are the vertices
  `c + ∑ εᵢ vᵢ` of the cube's image whose sign vector `ε` is realised by a linear form (`f` with
  `εᵢ f(vᵢ) > 0` for all `i`); distinct realised sign vectors give distinct points
  (`vert_injOn`). The proof that an unrealised sign vector gives no extreme point goes through
  Gordan's alternative, obtained from the separation theorem;
* `card_R`: for `ν ≥ 1` nonzero vectors of `ℝ²`, pairwise non-parallel, exactly `2ν` sign vectors
  are realised (induction on `ν`: the new vector `w` splits exactly the two regions met by the
  line `f(w) = 0`, those of `±w^⊥`);
* `ncard_extremePoints_sum_segment`: **the Minkowski sum of `ν ≥ 1` nondegenerate segments of `ℝ²`
  with pairwise non-parallel directions has exactly `2ν` extreme points**, and is centrally
  symmetric.

Proved in general, for every `ν`; nothing was left to the case `ν ≤ 4`. Not formalised: that the
image of the `ν`-cube under a *generic* linear map to the plane is such a sum (immediate from the
definition, the generic condition being that no two images of the basis vectors are parallel), the
identification of the outline's vertices with the straight-line perturbations of page 153, and the
reading of the figure (octagon, `ν = 4`), which rests on the redraw.
-/

namespace Grothendieck.Folder154Zonogon

open Set Filter Topology Pointwise

/-- The linear form `x ↦ f₁ x₁ + f₂ x₂` on the plane. -/
def ev (f : ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ := f.1 • LinearMap.fst ℝ ℝ ℝ + f.2 • LinearMap.snd ℝ ℝ ℝ

lemma ev_apply (f x : ℝ × ℝ) : ev f x = f.1 * x.1 + f.2 * x.2 := by simp [ev]

lemma ev_neg (f x : ℝ × ℝ) : ev (-f) x = -ev f x := by
  simp only [ev_apply, Prod.fst_neg, Prod.snd_neg]; ring

/-- The determinant of two vectors: zero exactly when they are parallel. -/
def cross (u w : ℝ × ℝ) : ℝ := u.1 * w.2 - u.2 * w.1

/-- A sign, as a real number. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_mem (b : Bool) : sg b ∈ Icc (-1 : ℝ) 1 := by cases b <;> norm_num [sg]

lemma sg_injective : Function.Injective sg := by
  intro a b h; cases a <;> cases b <;> first | rfl | (norm_num [sg] at h)

variable {ι : Type*} [Fintype ι]

/-- The image of the cube `[−1, 1]^ι` under `a ↦ c + ∑ aᵢ vᵢ`. -/
def zono (c : ℝ × ℝ) (v : ι → ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ a : ι → ℝ, (∀ i, a i ∈ Icc (-1 : ℝ) 1) ∧ x = c + ∑ i, a i • v i}

/-- The image of the vertex of the cube with signs `s`. -/
def vert (c : ℝ × ℝ) (v : ι → ℝ × ℝ) (s : ι → Bool) : ℝ × ℝ := c + ∑ i, sg (s i) • v i

/-- The linear form `f` realises the sign vector `s` on the vectors `v`. -/
def Realises (f : ℝ × ℝ) (v : ι → ℝ × ℝ) (s : ι → Bool) : Prop :=
  ∀ i, 0 < sg (s i) * ev f (v i)

/-- The realised sign vectors (the regions of the central arrangement of the lines `vᵢ^⊥`). -/
def R (v : ι → ℝ × ℝ) : Set (ι → Bool) := {s | ∃ f, Realises f v s}

/-! ## The Minkowski sum and its central symmetry -/

/-- The Minkowski sum of the segments `[pᵢ, qᵢ]` is the image of the cube. -/
theorem sum_segment_eq (p q : ι → ℝ × ℝ) :
    ∑ i, segment ℝ (p i) (q i) =
      zono (∑ i, (1 / 2 : ℝ) • (p i + q i)) (fun i => (1 / 2 : ℝ) • (q i - p i)) := by
  ext x
  rw [Set.mem_fintype_sum]
  simp only [segment_eq_image', Set.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose θ hθ hgθ using hg
    refine ⟨fun i => 2 * θ i - 1, fun i => ⟨by linarith [(hθ i).1], by linarith [(hθ i).2]⟩, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hgθ i]
    module
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun i => (1 / 2 : ℝ) • (p i + q i) + a i • (1 / 2 : ℝ) • (q i - p i),
      fun i => ⟨(a i + 1) / 2, ⟨by linarith [(ha i).1], by linarith [(ha i).2]⟩, by module⟩, ?_⟩
    rw [Finset.sum_add_distrib]

lemma zono_symm_of_mem {c : ℝ × ℝ} {v : ι → ℝ × ℝ} {x : ℝ × ℝ} (hx : x ∈ zono c v) :
    (2 : ℝ) • c - x ∈ zono c v := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨fun i => -a i, fun i => ⟨by linarith [(ha i).2], by linarith [(ha i).1]⟩, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  module

/-- Central symmetry about `c`. -/
theorem zono_symm (c : ℝ × ℝ) (v : ι → ℝ × ℝ) (x : ℝ × ℝ) :
    x ∈ zono c v ↔ (2 : ℝ) • c - x ∈ zono c v :=
  ⟨zono_symm_of_mem, fun h => by simpa using zono_symm_of_mem h⟩

/-! ## The extreme points: the realised vertices -/

lemma term_le {b : Bool} {a d : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (h : 0 < sg b * d) :
    a * d ≤ sg b * d := by
  obtain ⟨h1, h2⟩ := ha
  cases b <;> simp only [sg] at h ⊢ <;> norm_num at h ⊢ <;> nlinarith

lemma term_eq {b : Bool} {a d : ℝ} (h : 0 < sg b * d) (he : a * d = sg b * d) : a = sg b := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  exact mul_right_cancel₀ hd he

lemma ev_zono (f c : ℝ × ℝ) (v : ι → ℝ × ℝ) (a : ι → ℝ) :
    ev f (c + ∑ i, a i • v i) = ev f c + ∑ i, a i * ev f (v i) := by
  simp only [map_add, map_sum, map_smul, smul_eq_mul]

/-- A linear form realising `s` is maximal on the zonogon exactly at the vertex of signs `s`. -/
theorem le_ev_vert {f c : ℝ × ℝ} {v : ι → ℝ × ℝ} {s : ι → Bool} (hf : Realises f v s)
    (a : ι → ℝ) (ha : ∀ i, a i ∈ Icc (-1 : ℝ) 1) :
    ev f (c + ∑ i, a i • v i) ≤ ev f (vert c v s) ∧
      (ev f (vert c v s) ≤ ev f (c + ∑ i, a i • v i) → a = fun i => sg (s i)) := by
  have hle : ∀ i, a i * ev f (v i) ≤ sg (s i) * ev f (v i) := fun i => term_le (ha i) (hf i)
  refine ⟨?_, fun h => ?_⟩
  · rw [vert, ev_zono, ev_zono]
    exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => hle i)
  · rw [vert, ev_zono, ev_zono] at h
    have h0 : ∑ i, (sg (s i) * ev f (v i) - a i * ev f (v i)) = 0 := by
      have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hle i
      rw [Finset.sum_sub_distrib]; linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))] at h0
    funext i
    exact term_eq (hf i) (by linarith [h0 i (Finset.mem_univ _)])

/-- A realised vertex is an extreme point. -/
theorem vert_mem_extremePoints {f c : ℝ × ℝ} {v : ι → ℝ × ℝ} {s : ι → Bool}
    (hf : Realises f v s) : vert c v s ∈ (zono c v).extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨⟨fun i => sg (s i), fun i => sg_mem _, rfl⟩, ?_⟩
  rintro x₁ ⟨a₁, ha₁, rfl⟩ x₂ ⟨a₂, ha₂, rfl⟩ ⟨α, β, hα, hβ, hαβ, hx⟩
  obtain ⟨h₁, h₁'⟩ := le_ev_vert (c := c) hf a₁ ha₁
  obtain ⟨h₂, h₂'⟩ := le_ev_vert (c := c) hf a₂ ha₂
  have he : ev f (vert c v s) =
      α * ev f (c + ∑ i, a₁ i • v i) + β * ev f (c + ∑ i, a₂ i • v i) := by
    rw [← hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hV : ev f (vert c v s) = α * ev f (vert c v s) + β * ev f (vert c v s) := by
    rw [← add_mul, hαβ, one_mul]
  have m₁ := mul_le_mul_of_nonneg_left h₁ hα.le
  have m₂ := mul_le_mul_of_nonneg_left h₂ hβ.le
  have e₁ : ev f (vert c v s) ≤ ev f (c + ∑ i, a₁ i • v i) := by
    by_contra hc
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hc) hα
    linarith
  have e₂ : ev f (vert c v s) ≤ ev f (c + ∑ i, a₂ i • v i) := by
    by_contra hc
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hc) hβ
    linarith
  rw [h₁' e₁, h₂' e₂]
  exact ⟨rfl, rfl⟩

/-- Distinct realised sign vectors give distinct vertices. -/
theorem vert_injOn (c : ℝ × ℝ) (v : ι → ℝ × ℝ) : InjOn (vert c v) (R v) := by
  rintro s ⟨f, hf⟩ t - hst
  have h := (le_ev_vert (c := c) hf (fun i => sg (t i)) fun i => sg_mem _).2
    (by rw [hst]; exact le_rfl)
  funext i
  exact sg_injective (congrFun h i).symm

/-- In an extreme point, every coordinate of the cube is `±1`. -/
theorem coeff_of_extreme {c : ℝ × ℝ} {v : ι → ℝ × ℝ} (hv : ∀ i, v i ≠ 0) {a : ι → ℝ}
    (ha : ∀ i, a i ∈ Icc (-1 : ℝ) 1) (hx : c + ∑ i, a i • v i ∈ (zono c v).extremePoints ℝ)
    (k : ι) : a k = 1 ∨ a k = -1 := by
  classical
  by_contra hk
  simp only [not_or] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hlo : -1 < a k := lt_of_le_of_ne (ha k).1 (Ne.symm hk2)
  have hhi : a k < 1 := lt_of_le_of_ne (ha k).2 hk1
  set δ := min (1 - a k) (1 + a k) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ 1 - a k := min_le_left _ _
  have hδ2 : δ ≤ 1 + a k := min_le_right _ _
  let b : ℝ → ι → ℝ := fun t i => a i + t * (if i = k then 1 else 0)
  have hsum : ∀ t, ∑ i, b t i • v i = ∑ i, a i • v i + t • v k := fun t => by
    simp [b, add_smul, Finset.sum_add_distrib, mul_ite, ite_smul]
  have hb : ∀ t, |t| ≤ δ → ∀ i, b t i ∈ Icc (-1 : ℝ) 1 := fun t ht i => by
    have := abs_le.1 ht
    by_cases hi : i = k
    · subst hi; simp only [b, ite_true, mul_one]; constructor <;> linarith
    · simp only [b, hi, ite_false, mul_zero, add_zero]; exact ha i
  rw [mem_extremePoints] at hx
  have key := hx.2 (c + ∑ i, b δ i • v i) ⟨b δ, hb δ (by rw [abs_of_pos hδ0]) , rfl⟩
    (c + ∑ i, b (-δ) i • v i) ⟨b (-δ), hb (-δ) (by rw [abs_neg, abs_of_pos hδ0]), rfl⟩
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hsum, hsum]; module⟩
  have h1 := key.1
  rw [hsum] at h1
  have : δ • v k = 0 := by
    have := congrArg (fun y => y - (c + ∑ i, a i • v i)) h1
    simpa [add_assoc] using this
  exact hv k ((smul_eq_zero.1 this).resolve_left hδ0.ne')

lemma strongDual_apply (g : StrongDual ℝ (ℝ × ℝ)) (x : ℝ × ℝ) :
    g x = x.1 * g (1, 0) + x.2 * g (0, 1) := by
  have : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The standard simplex of `ι → ℝ`. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {μ | (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1}

lemma convex_simplex (ι : Type*) [Fintype ι] : Convex ℝ (simplex ι) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 i; have := hy0 i; positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx1, hy1, mul_one, hab]

lemma isCompact_simplex (ι : Type*) [Fintype ι] : IsCompact (simplex ι) := by
  have hc : IsClosed (simplex ι) := by
    have : simplex ι = (⋂ i, {μ : ι → ℝ | 0 ≤ μ i}) ∩ {μ | ∑ i, μ i = 1} := by
      ext μ; simp [simplex]
    rw [this]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  refine (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).of_isClosed_subset hc ?_
  rintro μ ⟨h0, h1⟩
  refine ⟨fun i => h0 i, fun i => ?_⟩
  have := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  rw [h1] at this
  simpa using this

lemma single_mem_simplex [DecidableEq ι] (i : ι) : Pi.single i (1 : ℝ) ∈ simplex ι :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-- **Extreme points.** With nonzero `vᵢ`, the extreme points of the zonogon are its realised
vertices. -/
theorem extremePoints_zono (c : ℝ × ℝ) (v : ι → ℝ × ℝ) (hv : ∀ i, v i ≠ 0) :
    (zono c v).extremePoints ℝ = vert c v '' R v := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx.1
    have hpm := coeff_of_extreme hv ha hx
    set s : ι → Bool := fun i => decide (0 < a i)
    have has : a = fun i => sg (s i) := by
      funext i
      rcases hpm i with h | h <;> simp [s, sg, h]
    refine ⟨s, ?_, by rw [vert, has]⟩
    by_contra hR
    set w : ι → ℝ × ℝ := fun i => sg (s i) • v i
    let L := Fintype.linearCombination ℝ w
    by_cases h0 : (0 : ℝ × ℝ) ∈ L '' simplex ι
    · obtain ⟨μ, ⟨hμ0, hμ1⟩, hμ⟩ := h0
      rw [Fintype.linearCombination_apply] at hμ
      obtain ⟨k, hk⟩ : ∃ k, 0 < μ k := by
        by_contra h
        push Not at h
        have : ∑ i, μ i ≤ 0 := Finset.sum_nonpos fun i _ => h i
        linarith
      have hle : ∀ i, μ i ≤ 1 := fun i => hμ1 ▸
        Finset.single_le_sum (fun j _ => hμ0 j) (Finset.mem_univ i)
      let b : ι → ℝ := fun i => sg (s i) * (1 - μ i)
      have hb : ∀ i, b i ∈ Icc (-1 : ℝ) 1 := fun i => by
        have := hμ0 i; have := hle i
        cases h : s i <;> simp only [b, h, sg, Bool.false_eq_true, ↓reduceIte] <;>
          constructor <;> linarith
      have hxb : c + ∑ i, a i • v i = c + ∑ i, b i • v i := by
        have : ∑ i, b i • v i = ∑ i, a i • v i - ∑ i, μ i • w i := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [b, w, has, smul_smul]
          module
        rw [this, hμ, sub_zero]
      rw [hxb] at hx
      rcases coeff_of_extreme hv hb hx k with h | h <;>
        · have := hle k
          cases hs : s k <;> simp only [b, hs, sg, Bool.false_eq_true, ↓reduceIte] at h <;> linarith
    · have hK : Convex ℝ (L '' simplex ι) := (convex_simplex ι).linear_image L
      have hKc : IsClosed (L '' simplex ι) :=
        ((isCompact_simplex ι).image (LinearMap.continuous_of_finiteDimensional L)).isClosed
      obtain ⟨g, u, hgu, hu⟩ := geometric_hahn_banach_closed_point hK hKc h0
      rw [map_zero] at hu
      apply hR
      refine ⟨(-g (1, 0), -g (0, 1)), fun i => ?_⟩
      have hi := hgu (w i) ⟨Pi.single i 1, single_mem_simplex i, by
        simp [L, Fintype.linearCombination_apply_single]⟩
      have : g (w i) = sg (s i) * ((v i).1 * g (1, 0) + (v i).2 * g (0, 1)) := by
        simp only [w, map_smul, smul_eq_mul, strongDual_apply g (v i)]
      rw [ev_apply]
      nlinarith
  · rintro _ ⟨s, ⟨f, hf⟩, rfl⟩
    exact vert_mem_extremePoints hf

/-! ## Counting the realised sign vectors in the plane -/

omit [Fintype ι] in
lemma realises_iff (f : ℝ × ℝ) (v : ι → ℝ × ℝ) (s : ι → Bool) :
    Realises f v s ↔ (∀ i, ev f (v i) ≠ 0) ∧ s = fun i => decide (0 < ev f (v i)) := by
  constructor
  · intro h
    refine ⟨fun i hi => by simpa [hi] using h i, funext fun i => ?_⟩
    have := h i
    cases hs : s i <;> simp only [hs, sg] at this ⊢ <;> norm_num at this ⊢ <;> linarith
  · rintro ⟨h0, rfl⟩ i
    rcases lt_or_gt_of_ne (h0 i) with h | h
    · simp [sg, not_lt.2 h.le]; linarith
    · simp [sg, h]

lemma realises_cons {n : ℕ} (f : ℝ × ℝ) (v : Fin (n + 1) → ℝ × ℝ) (b : Bool)
    (t : Fin n → Bool) :
    Realises f v (Fin.cons b t : Fin (n + 1) → Bool) ↔
      0 < sg b * ev f (v 0) ∧ Realises f (Fin.tail v) t := by
  simp only [Realises, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- A small move of `f` along `w` keeps the signs it realises. -/
lemma realises_perturb {m : ℕ} {f : ℝ × ℝ} {u : Fin m → ℝ × ℝ} {t : Fin m → Bool}
    (hf : Realises f u t) (w : ℝ × ℝ) : ∀ᶠ ε in 𝓝 (0 : ℝ), Realises (f + ε • w) u t := by
  unfold Realises
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous fun ε : ℝ => sg (t i) * ev (f + ε • w) (u i) := by
    simp only [ev_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    fun_prop
  have := hc.tendsto 0
  simp only [zero_smul, add_zero] at this
  exact this.eventually (lt_mem_nhds (hf i))

lemma normSq_pos {w : ℝ × ℝ} (hw : w ≠ 0) : 0 < w.1 * w.1 + w.2 * w.2 := by
  by_contra h
  have a := mul_self_nonneg w.1
  have b := mul_self_nonneg w.2
  have e1 : w.1 * w.1 = 0 := by linarith
  have e2 : w.2 * w.2 = 0 := by linarith
  exact hw (Prod.ext (mul_self_eq_zero.1 e1) (mul_self_eq_zero.1 e2))

/-- If `f` realises `t` and vanishes on `w ≠ 0`, both extensions of `t` by a sign on `w` are
realised. -/
lemma both_of_zero {n : ℕ} {v : Fin (n + 1) → ℝ × ℝ} (hw : v 0 ≠ 0) {f : ℝ × ℝ}
    {t : Fin n → Bool} (hf : Realises f (Fin.tail v) t) (h0 : ev f (v 0) = 0) (b : Bool) :
    (Fin.cons b t : Fin (n + 1) → Bool) ∈ R v := by
  have hpos : 0 < ev (v 0) (v 0) := by rw [ev_apply]; exact normSq_pos hw
  have key : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Realises (f + (sg b * ε ^ 2) • v 0) (Fin.tail v) t ∧ ε ≠ 0 := by
    have hc : Tendsto (fun ε : ℝ => sg b * ε ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have : Continuous fun ε : ℝ => sg b * ε ^ 2 := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (hc.eventually (realises_perturb hf (v 0))).and self_mem_nhdsWithin
  obtain ⟨ε, hε, hε0⟩ := key.exists
  refine ⟨f + (sg b * ε ^ 2) • v 0, (realises_cons _ _ _ _).2 ⟨?_, hε⟩⟩
  have : ev (f + (sg b * ε ^ 2) • v 0) (v 0) = sg b * ε ^ 2 * ev (v 0) (v 0) := by
    simp only [ev_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h0 ⊢
    linear_combination h0
  rw [this]
  have hsg : sg b * sg b = 1 := by cases b <;> norm_num [sg]
  have : 0 < ε ^ 2 := by positivity
  calc (0 : ℝ) < ε ^ 2 * ev (v 0) (v 0) := by positivity
    _ = sg b * (sg b * ε ^ 2 * ev (v 0) (v 0)) := by rw [← mul_assoc, ← mul_assoc, hsg]; ring

/-- The form `x ↦ cross(w, x)`, vanishing on `w`. -/
def perp (w : ℝ × ℝ) : ℝ × ℝ := (-w.2, w.1)

lemma ev_perp (w x : ℝ × ℝ) : ev (perp w) x = cross w x := by
  simp only [ev_apply, perp, cross]; ring

/-- The two regions met by the line `f(w) = 0`. -/
noncomputable def pPlus {m : ℕ} (w : ℝ × ℝ) (u : Fin m → ℝ × ℝ) : Fin m → Bool :=
  fun i => decide (0 < ev (perp w) (u i))

noncomputable def pMinus {m : ℕ} (w : ℝ × ℝ) (u : Fin m → ℝ × ℝ) : Fin m → Bool :=
  fun i => decide (0 < ev (-perp w) (u i))

/-- If both extensions of `t` are realised, `t` is one of the two regions of `±w^⊥`. -/
lemma eq_of_both {n : ℕ} {v : Fin (n + 1) → ℝ × ℝ} (hw : v 0 ≠ 0) {t : Fin n → Bool}
    (h1 : (Fin.cons true t : Fin (n + 1) → Bool) ∈ R v)
    (h2 : (Fin.cons false t : Fin (n + 1) → Bool) ∈ R v) :
    t = pPlus (v 0) (Fin.tail v) ∨ t = pMinus (v 0) (Fin.tail v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left; funext i; exact i.elim0
  obtain ⟨f₁, hf₁⟩ := h1
  obtain ⟨f₂, hf₂⟩ := h2
  rw [realises_cons] at hf₁ hf₂
  obtain ⟨a₁, hf₁⟩ := hf₁
  obtain ⟨a₂, hf₂⟩ := hf₂
  simp only [sg, ↓reduceIte, one_mul, Bool.false_eq_true, neg_one_mul, neg_pos] at a₁ a₂
  set A := ev f₁ (v 0)
  set B := ev f₂ (v 0)
  set θ := A / (A - B)
  have hAB : 0 < A - B := by linarith
  have hθ0 : 0 < θ := div_pos a₁ hAB
  have hθ1 : θ < 1 := (div_lt_one hAB).2 (by linarith)
  set h := (1 - θ) • f₁ + θ • f₂
  have hev : ∀ x, ev h x = (1 - θ) * ev f₁ x + θ * ev f₂ x := fun x => by
    simp only [h, ev_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have hh : Realises h (Fin.tail v) t := fun i => by
    rw [hev]
    have := hf₁ i; have := hf₂ i
    have e : sg (t i) * ((1 - θ) * ev f₁ (Fin.tail v i) + θ * ev f₂ (Fin.tail v i)) =
      (1 - θ) * (sg (t i) * ev f₁ (Fin.tail v i)) + θ * (sg (t i) * ev f₂ (Fin.tail v i)) := by
      ring
    rw [e]
    have : 0 < 1 - θ := by linarith
    positivity
  have h0 : ev h (v 0) = 0 := by
    rw [hev]
    simp only [θ]
    field_simp
    ring
  -- `h` is a multiple of `perp w`
  set w := v 0
  have hww : 0 < w.1 ^ 2 + w.2 ^ 2 := by simpa [sq] using normSq_pos hw
  set μ := h.2 * w.1 - h.1 * w.2
  have hmul : ∀ x, (w.1 ^ 2 + w.2 ^ 2) * ev h x = μ * ev (perp w) x := fun x => by
    rw [ev_apply] at h0
    simp only [ev_apply, perp, μ]
    linear_combination (w.2 * x.2 + w.1 * x.1) * h0
  rw [realises_iff] at hh
  obtain ⟨hne, rfl⟩ := hh
  rcases lt_trichotomy μ 0 with hμ | hμ | hμ
  · right
    funext i
    simp only [pMinus, ev_neg]
    have := hmul (Fin.tail v i)
    apply decide_eq_decide.2
    constructor <;> intro hx <;> nlinarith
  · exfalso
    have := hmul (Fin.tail v ⟨0, hn⟩)
    rw [hμ, zero_mul] at this
    exact hne ⟨0, hn⟩ ((mul_eq_zero.1 this).resolve_left hww.ne')
  · left
    funext i
    simp only [pPlus]
    have := hmul (Fin.tail v i)
    apply decide_eq_decide.2
    constructor <;> intro hx <;> nlinarith

/-- Each region extends to at least one region when a vector is added. -/
lemma exists_cons {n : ℕ} {v : Fin (n + 1) → ℝ × ℝ} (hw : v 0 ≠ 0) {t : Fin n → Bool}
    (ht : t ∈ R (Fin.tail v)) : ∃ b, (Fin.cons b t : Fin (n + 1) → Bool) ∈ R v := by
  obtain ⟨f, hf⟩ := ht
  by_cases h0 : ev f (v 0) = 0
  · exact ⟨true, both_of_zero hw hf h0 true⟩
  · refine ⟨decide (0 < ev f (v 0)), f, (realises_cons _ _ _ _).2 ⟨?_, hf⟩⟩
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [sg, not_lt.2 h.le]; linarith
    · simp [sg, h]

lemma pPlus_mem {n : ℕ} {v : Fin (n + 1) → ℝ × ℝ}
    (hpar : ∀ i : Fin n, cross (v 0) (v i.succ) ≠ 0) :
    pPlus (v 0) (Fin.tail v) ∈ R (Fin.tail v) :=
  ⟨perp (v 0), (realises_iff _ _ _).2 ⟨fun i => by rw [ev_perp]; exact hpar i, rfl⟩⟩

lemma pMinus_mem {n : ℕ} {v : Fin (n + 1) → ℝ × ℝ}
    (hpar : ∀ i : Fin n, cross (v 0) (v i.succ) ≠ 0) :
    pMinus (v 0) (Fin.tail v) ∈ R (Fin.tail v) :=
  ⟨-perp (v 0), (realises_iff _ _ _).2
    ⟨fun i => by rw [ev_neg, ev_perp, neg_ne_zero]; exact hpar i, rfl⟩⟩

lemma pPlus_ne_pMinus {n : ℕ} (hn : 0 < n) {v : Fin (n + 1) → ℝ × ℝ}
    (hpar : ∀ i : Fin n, cross (v 0) (v i.succ) ≠ 0) :
    pPlus (v 0) (Fin.tail v) ≠ pMinus (v 0) (Fin.tail v) := by
  intro h
  have h1 := congrFun h ⟨0, hn⟩
  have h2 := hpar ⟨0, hn⟩
  simp only [pPlus, pMinus, ev_neg, ev_perp, Fin.tail] at h1
  have key := decide_eq_decide.1 h1
  rcases lt_or_gt_of_ne h2 with h3 | h3
  · have := key.2 (by linarith)
    linarith
  · have := key.1 h3
    linarith

lemma realises_of_cons {n : ℕ} {v : Fin (n + 1) → ℝ × ℝ} {b : Bool} {t : Fin n → Bool}
    (h : (Fin.cons b t : Fin (n + 1) → Bool) ∈ R v) : t ∈ R (Fin.tail v) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, ((realises_cons _ _ _ _).1 hf).2⟩

open Classical in
/-- The fibre of the restriction over `t`: two extensions over the regions of `±w^⊥`, one over
every other region. -/
lemma fibre_card {n : ℕ} (hn : 0 < n) {v : Fin (n + 1) → ℝ × ℝ} (hw : v 0 ≠ 0)
    (hpar : ∀ i : Fin n, cross (v 0) (v i.succ) ≠ 0) (t : Fin n → Bool) :
    (∑ b : Bool, if (Fin.cons b t : Fin (n + 1) → Bool) ∈ R v then 1 else 0 : ℕ) =
      (if t ∈ R (Fin.tail v) then 1 else 0) + (if t = pPlus (v 0) (Fin.tail v) then 1 else 0) +
        (if t = pMinus (v 0) (Fin.tail v) then 1 else 0) := by
  have hP := pPlus_mem hpar
  have hM := pMinus_mem hpar
  have hPM := pPlus_ne_pMinus hn hpar
  rw [Fintype.sum_bool]
  by_cases ht : t ∈ R (Fin.tail v)
  · by_cases hp : t = pPlus (v 0) (Fin.tail v) ∨ t = pMinus (v 0) (Fin.tail v)
    · have hboth : ∀ b, (Fin.cons b t : Fin (n + 1) → Bool) ∈ R v := by
        rcases hp with rfl | rfl
        · exact both_of_zero hw ((realises_iff _ _ _).2
            ⟨fun i => by rw [ev_perp]; exact hpar i, rfl⟩) (by rw [ev_perp, cross]; ring)
        · exact both_of_zero hw ((realises_iff _ _ _).2
            ⟨fun i => by rw [ev_neg, ev_perp, neg_ne_zero]; exact hpar i, rfl⟩)
            (by rw [ev_neg, ev_perp, cross]; ring)
      rcases hp with rfl | rfl
      · simp [hboth, ht, hPM]
      · simp [hboth, ht, Ne.symm hPM]
    · rw [not_or] at hp
      obtain ⟨b, hb⟩ := exists_cons hw ht
      have hnot : ¬ ((Fin.cons true t : Fin (n + 1) → Bool) ∈ R v ∧
          (Fin.cons false t : Fin (n + 1) → Bool) ∈ R v) := fun h =>
        (eq_of_both hw h.1 h.2).elim hp.1 hp.2
      cases b
      · have : (Fin.cons true t : Fin (n + 1) → Bool) ∉ R v := fun h => hnot ⟨h, hb⟩
        simp [hb, this, ht, hp.1, hp.2]
      · have : (Fin.cons false t : Fin (n + 1) → Bool) ∉ R v := fun h => hnot ⟨hb, h⟩
        simp [hb, this, ht, hp.1, hp.2]
  · have h1 : t ≠ pPlus (v 0) (Fin.tail v) := fun h => ht (h ▸ hP)
    have h2 : t ≠ pMinus (v 0) (Fin.tail v) := fun h => ht (h ▸ hM)
    have h3 : ∀ b, (Fin.cons b t : Fin (n + 1) → Bool) ∉ R v := fun b h => ht (realises_of_cons h)
    simp [h1, h2, h3, ht]

open Classical in
lemma ncard_eq_sum {m : ℕ} (S : Set (Fin m → Bool)) :
    S.ncard = ∑ s : Fin m → Bool, if s ∈ S then 1 else 0 := by
  have : S = ↑(Finset.univ.filter (· ∈ S)) := by ext; simp
  rw [this, Set.ncard_coe_finset, Finset.card_filter]
  simp

/-- **Counting.** `ν ≥ 1` nonzero, pairwise non-parallel vectors of the plane realise exactly `2ν`
sign vectors. -/
theorem card_R : ∀ (n : ℕ) (v : Fin (n + 1) → ℝ × ℝ), (∀ i, v i ≠ 0) →
    Pairwise (fun i j => cross (v i) (v j) ≠ 0) → (R v).ncard = 2 * (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro v hv _
    have : R v = univ := by
      refine eq_univ_of_forall fun s => ⟨sg (s 0) • v 0, fun i => ?_⟩
      obtain rfl : i = 0 := Fin.ext (by have := i.isLt; omega)
      have hsg : sg (s 0) * sg (s 0) = 1 := by cases s 0 <;> norm_num [sg]
      have := normSq_pos (hv 0)
      have e : sg (s 0) * ev (sg (s 0) • v 0) (v 0) =
          sg (s 0) * sg (s 0) * ((v 0).1 * (v 0).1 + (v 0).2 * (v 0).2) := by
        simp only [ev_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [e, hsg, one_mul]
      exact this
    rw [this, Set.ncard_univ]
    simp
  | succ n ih =>
    intro v hv hp
    classical
    have hpar : ∀ i : Fin (n + 1), cross (v 0) (v i.succ) ≠ 0 :=
      fun i => hp (Fin.succ_ne_zero i).symm
    have htail := ih (Fin.tail v) (fun i => hv _)
      (fun i j hij => hp (Fin.succ_injective _ |>.ne hij))
    rw [ncard_eq_sum] at htail ⊢
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Bool)
      (fun q => if (Fin.cons q.1 q.2 : Fin (n + 2) → Bool) ∈ R v then 1 else 0) _
      (fun q => rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [fibre_card (Nat.succ_pos n) (hv 0) hpar, Finset.sum_add_distrib, htail,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

/-! ## The theorem -/

/-- Central symmetry of a Minkowski sum of segments, about `∑ (pᵢ + qᵢ)/2`. -/
theorem sum_segment_symm (p q : ι → ℝ × ℝ) (x : ℝ × ℝ) :
    x ∈ ∑ i, segment ℝ (p i) (q i) ↔
      (2 : ℝ) • (∑ i, (1 / 2 : ℝ) • (p i + q i)) - x ∈ ∑ i, segment ℝ (p i) (q i) := by
  rw [sum_segment_eq]
  exact zono_symm _ _ x

/-- **The zonogon.** The Minkowski sum of `ν ≥ 1` nondegenerate segments of the plane with pairwise
non-parallel directions is centrally symmetric and has exactly `2ν` extreme points. -/
theorem ncard_extremePoints_sum_segment {ν : ℕ} (hν : 0 < ν) (p q : Fin ν → ℝ × ℝ)
    (hpq : ∀ i, p i ≠ q i) (hpar : Pairwise fun i j => cross (q i - p i) (q j - p j) ≠ 0) :
    ((∑ i, segment ℝ (p i) (q i)).extremePoints ℝ).ncard = 2 * ν ∧
      ∀ x, x ∈ ∑ i, segment ℝ (p i) (q i) ↔
        (2 : ℝ) • (∑ i, (1 / 2 : ℝ) • (p i + q i)) - x ∈ ∑ i, segment ℝ (p i) (q i) := by
  refine ⟨?_, sum_segment_symm p q⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hν.ne'
  have hv : ∀ i, (1 / 2 : ℝ) • (q i - p i) ≠ 0 := fun i =>
    smul_ne_zero (by norm_num) (sub_ne_zero.2 (hpq i).symm)
  have hv2 : Pairwise fun i j =>
      cross ((1 / 2 : ℝ) • (q i - p i)) ((1 / 2 : ℝ) • (q j - p j)) ≠ 0 := fun i j hij => by
    have := hpar hij
    have e : cross ((1 / 2 : ℝ) • (q i - p i)) ((1 / 2 : ℝ) • (q j - p j)) =
        (1 / 4) * cross (q i - p i) (q j - p j) := by
      simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    show cross _ _ ≠ 0
    rw [e]
    exact mul_ne_zero (by norm_num) this
  rw [sum_segment_eq, extremePoints_zono _ _ hv, (vert_injOn _ _).ncard_image,
    card_R n _ hv hv2]

end Grothendieck.Folder154Zonogon
