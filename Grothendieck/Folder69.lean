module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.Group

@[expose] public section


/-!
# Folder 69, pages 25–26: the automorphisms of the 27-line graph fixing a triangle

The modernised reading `transcripts/69/69.modern.tex` (§ 9, « Un triangle marqué »,
pages 25 to 31) describes the graph `C` of the twenty-seven lines of a cubic surface
(two lines joined when they meet) with a marked triangle `t`, and states as a
corollary of the description (page 26)

> `1 → Ψ̃ → W_t → 𝔖_t × 𝔖_{V*} → 1`, `card W_t = 32 · 36 = 1152 = 51 840 / 45`,

`W_t` being the group of automorphisms of `(C, t)`; page 25 gives the subgroup `W'_t`
fixing `t` pointwise, of order `192`.

This is the reachable part of finding `69-triangle-q8-baer-torsor` of
`src/content/findings.ts`: the order, by a finite computation on the graph. Proving it
says only that the count holds; whether the description by a `Q₈`-Baer torsor is in the
literature is a separate question.

What is formalised. The vertices are `Fin 27`: `aᵢ = i`, `bᵢ = 6 + i` (`0 ≤ i < 6`) and
`c_{ij} = 12 + k` for the `k`-th pair `i < j` in lexicographic order; `aᵢ` meets `bⱼ`
iff `i ≠ j`, `aᵢ` and `bᵢ` meet `c_{jk}` iff `i ∈ {j, k}`, `c_{ij}` meets `c_{kl}` iff
`{i, j} ∩ {k, l} = ∅`. The triangle is `t = {a₀, b₁, c₀₁}`.

* `card_Wt`: the permutations of the vertices preserving the graph and `t` form a group
  of order `1152`; `card_aut`: the same for the graph automorphisms `C ≃g C` preserving
  `t`.
* `card_pointwise`: those fixing `t` pointwise form a group of order `192`.
* `degree_eq` (every line meets ten others) and `isTriangle_t`.

The proof is a stabiliser chain: the base `a₀, b₁, a₁, a₂, a₃, a₄` has orbits of sizes
`3, 2, 8, 4, 3, 2` (`3 · 2 · 8 · 4 · 3 · 2 = 1152`); each orbit is contained in the set
of vertices with the same incidences with the points already fixed, and exhausted by
explicit automorphisms (`g0_7`, …, `g5_5`), checked by the kernel; an automorphism
fixing the base fixes everything, since the base separates the vertices.
-/

namespace Grothendieck.Folder69

open Equiv

/-- The fifteen pairs `i < j` of `{0, …, 5}`, in lexicographic order. -/
def pairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The pair of `c_{ij}`. -/
def cp (v : Fin 27) : ℕ × ℕ := pairs.getD (v.val - 12) (0, 0)

/-- Do two of the twenty-seven lines meet? -/
def meets (u v : Fin 27) : Bool :=
  if u.val < 12 ∧ v.val < 12 then
    (u.val < 6 ∧ 6 ≤ v.val ∧ u.val + 6 ≠ v.val) || (v.val < 6 ∧ 6 ≤ u.val ∧ v.val + 6 ≠ u.val)
  else if u.val < 12 then (cp v).1 = u.val % 6 || (cp v).2 = u.val % 6
  else if v.val < 12 then (cp u).1 = v.val % 6 || (cp u).2 = v.val % 6
  else (cp u).1 ≠ (cp v).1 ∧ (cp u).1 ≠ (cp v).2 ∧ (cp u).2 ≠ (cp v).1 ∧ (cp u).2 ≠ (cp v).2

/-- The graph `C` of the twenty-seven lines. -/
def C : SimpleGraph (Fin 27) where
  Adj u v := meets u v = true
  symm := ⟨fun u v h =>
    ((show ∀ u v : Fin 27, meets u v = meets v u by decide +kernel) u v).symm.trans h⟩
  loopless := ⟨fun u h => by
    rw [(show ∀ u : Fin 27, meets u u = false by decide +kernel) u] at h
    exact Bool.false_ne_true h⟩

instance : DecidableRel C.Adj := fun u v => inferInstanceAs (Decidable (meets u v = true))

/-- The marked triangle `t = {a₀, b₁, c₀₁}`. -/
def t : Finset (Fin 27) := {0, 7, 12}

theorem isTriangle_t : C.Adj 0 7 ∧ C.Adj 0 12 ∧ C.Adj 7 12 := by decide +kernel

theorem degree_eq (v : Fin 27) : (Finset.univ.filter (C.Adj v)).card = 10 := by
  revert v; decide +kernel

/-- `W_t`: the permutations preserving the graph and the triangle. -/
def Wt : Subgroup (Perm (Fin 27)) where
  carrier := {σ | (∀ u v, meets (σ u) (σ v) = meets u v) ∧ ∀ v, σ v ∈ t ↔ v ∈ t}
  mul_mem' := by
    rintro σ τ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun u v => (h1 _ _).trans (h3 u v), fun v => (h2 _).trans (h4 v)⟩
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  inv_mem' := by
    rintro σ ⟨h1, h2⟩
    refine ⟨fun u v => ?_, fun v => ?_⟩
    · simpa using (h1 (σ⁻¹ u) (σ⁻¹ v)).symm
    · simpa using (h2 (σ⁻¹ v)).symm

/-- The subgroup of `K` fixing `b`. -/
def fix (K : Subgroup (Perm (Fin 27))) (b : Fin 27) : Subgroup (Perm (Fin 27)) :=
  K ⊓ MulAction.stabilizer (Perm (Fin 27)) b

theorem mem_fix {K : Subgroup (Perm (Fin 27))} {b : Fin 27} {σ : Perm (Fin 27)} :
    σ ∈ fix K b ↔ σ ∈ K ∧ σ b = b := Iff.rfl

/-- Orbit–stabiliser, with the orbit given as a finset. -/
theorem card_step (K : Subgroup (Perm (Fin 27))) (b : Fin 27) (S : Finset (Fin 27))
    (h1 : ∀ σ ∈ K, σ b ∈ S) (h2 : ∀ s ∈ S, ∃ σ ∈ K, σ b = s) :
    Nat.card K = S.card * Nat.card (fix K b) := by
  have horb : MulAction.orbit K b = (S : Set (Fin 27)) := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨σ, rfl⟩; exact h1 σ σ.2
    · obtain ⟨σ, hσ, e⟩ := h2 x hx; exact ⟨⟨σ, hσ⟩, e⟩
  have h := Subgroup.card_mul_index (MulAction.stabilizer K b)
  rw [MulAction.index_stabilizer, horb, Set.ncard_coe_finset] at h
  rw [← h, mul_comm]
  congr 1
  exact Nat.card_congr
    { toFun := fun σ => ⟨σ.1.1, σ.1.2, σ.2⟩
      invFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A permutation given by its values. -/
noncomputable def ofFun (f : Fin 27 → Fin 27) (hf : Function.Injective f) : Perm (Fin 27) :=
  Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)

theorem ofFun_apply (f : Fin 27 → Fin 27) (hf : Function.Injective f) (x : Fin 27) :
    ofFun f hf x = f x := rfl

theorem ofFun_mem (f : Fin 27 → Fin 27) (hf : Function.Injective f)
    (ha : ∀ u v, meets (f u) (f v) = meets u v) (ht : ∀ v, f v ∈ t ↔ v ∈ t) :
    ofFun f hf ∈ Wt := ⟨ha, ht⟩

/-- What an element of `W_t` fixing the points of `B` does to the incidences of `b`. -/
theorem pattern {σ : Perm (Fin 27)} (hσ : σ ∈ Wt) (B : List (Fin 27)) (hB : ∀ x ∈ B, σ x = x)
    (b : Fin 27) (hb : b ∉ B) :
    (σ b ∈ t ↔ b ∈ t) ∧ ∀ x ∈ B, meets (σ b) x = meets b x ∧ σ b ≠ x := by
  refine ⟨hσ.2 b, fun x hx => ⟨?_, fun h => hb ?_⟩⟩
  · conv_lhs => rw [← hB x hx]
    exact hσ.1 b x
  · rw [← hB x hx] at h
    exact σ.injective h ▸ hx

def g0_7 : Fin 27 → Fin 27 :=
  ![7, 1, 14, 13, 16, 15, 6, 0, 18, 17, 20, 19, 12, 3,
    2, 5, 4, 9, 8, 11, 10, 26, 22, 23, 24, 25, 21]
def g0_12 : Fin 27 → Fin 27 :=
  ![12, 13, 17, 3, 4, 5, 8, 7, 6, 26, 25, 24, 0, 1,
    21, 22, 23, 2, 18, 19, 20, 14, 15, 16, 11, 10, 9]
def g1_12 : Fin 27 → Fin 27 :=
  ![0, 2, 1, 26, 25, 24, 17, 12, 13, 9, 10, 11, 7, 8,
    14, 15, 16, 6, 21, 22, 23, 18, 19, 20, 5, 4, 3]
def g2_6 : Fin 27 → Fin 27 :=
  ![0, 6, 18, 17, 20, 19, 1, 7, 14, 13, 16, 15, 12, 9,
    8, 11, 10, 3, 2, 5, 4, 26, 22, 23, 24, 25, 21]
def g2_21 : Fin 27 → Fin 27 :=
  ![0, 21, 18, 17, 4, 5, 26, 7, 8, 9, 16, 15, 12, 13,
    14, 11, 10, 3, 2, 19, 20, 1, 22, 23, 24, 25, 6]
def g2_22 : Fin 27 → Fin 27 :=
  ![0, 22, 19, 3, 17, 5, 25, 7, 8, 16, 10, 14, 12, 13,
    11, 15, 9, 4, 18, 2, 20, 21, 1, 23, 24, 6, 26]
def g2_23 : Fin 27 → Fin 27 :=
  ![0, 23, 20, 3, 4, 17, 24, 7, 8, 15, 14, 11, 12, 13,
    10, 9, 16, 5, 18, 19, 2, 21, 22, 1, 6, 25, 26]
def g2_24 : Fin 27 → Fin 27 :=
  ![0, 24, 2, 19, 18, 5, 23, 7, 16, 9, 10, 13, 12, 11,
    14, 15, 8, 17, 4, 3, 20, 21, 22, 6, 1, 25, 26]
def g2_25 : Fin 27 → Fin 27 :=
  ![0, 25, 2, 20, 4, 18, 22, 7, 15, 9, 13, 11, 12, 10,
    14, 8, 16, 17, 5, 19, 3, 21, 6, 23, 24, 1, 26]
def g2_26 : Fin 27 → Fin 27 :=
  ![0, 26, 2, 3, 20, 19, 21, 7, 14, 13, 10, 11, 12, 9,
    8, 15, 16, 17, 18, 5, 4, 6, 22, 23, 24, 25, 1]
def g3_3 : Fin 27 → Fin 27 :=
  ![0, 1, 3, 2, 4, 5, 6, 7, 9, 8, 10, 11, 12, 14,
    13, 15, 16, 18, 17, 19, 20, 21, 24, 25, 22, 23, 26]
def g3_4 : Fin 27 → Fin 27 :=
  ![0, 1, 4, 3, 2, 5, 6, 7, 10, 9, 8, 11, 12, 15,
    14, 13, 16, 19, 18, 17, 20, 24, 22, 26, 21, 25, 23]
def g3_5 : Fin 27 → Fin 27 :=
  ![0, 1, 5, 3, 4, 2, 6, 7, 11, 9, 10, 8, 12, 16,
    14, 15, 13, 20, 18, 19, 17, 25, 26, 23, 24, 21, 22]
def g4_4 : Fin 27 → Fin 27 :=
  ![0, 1, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11, 12, 13,
    15, 14, 16, 17, 19, 18, 20, 22, 21, 23, 24, 26, 25]
def g4_5 : Fin 27 → Fin 27 :=
  ![0, 1, 2, 5, 4, 3, 6, 7, 8, 11, 10, 9, 12, 13,
    16, 15, 14, 17, 20, 19, 18, 23, 22, 21, 26, 25, 24]
def g5_5 : Fin 27 → Fin 27 :=
  ![0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10, 12, 13,
    14, 16, 15, 17, 18, 20, 19, 21, 23, 22, 25, 24, 26]

/-- The stabiliser chain of the base `a₀, b₁, a₁, a₂, a₃, a₄`. -/
def K1 : Subgroup (Perm (Fin 27)) := fix Wt 0
/-- See `K1`. -/
def K2 : Subgroup (Perm (Fin 27)) := fix K1 7
/-- See `K1`. -/
def K3 : Subgroup (Perm (Fin 27)) := fix K2 1
/-- See `K1`. -/
def K4 : Subgroup (Perm (Fin 27)) := fix K3 2
/-- See `K1`. -/
def K5 : Subgroup (Perm (Fin 27)) := fix K4 3
/-- See `K1`. -/
def K6 : Subgroup (Perm (Fin 27)) := fix K5 4

theorem mem_K1 {σ : Perm (Fin 27)} : σ ∈ K1 ↔ σ ∈ Wt ∧ σ 0 = 0 := by
  simp only [K1, mem_fix]

theorem mem_K2 {σ : Perm (Fin 27)} : σ ∈ K2 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 := by
  simp only [K2, K1, mem_fix, and_assoc]

theorem mem_K3 {σ : Perm (Fin 27)} : σ ∈ K3 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 := by
  simp only [K3, K2, K1, mem_fix, and_assoc]

theorem mem_K4 {σ : Perm (Fin 27)} : σ ∈ K4 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 ∧ σ 2 = 2 := by
  simp only [K4, K3, K2, K1, mem_fix, and_assoc]

theorem mem_K5 {σ : Perm (Fin 27)} :
    σ ∈ K5 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 := by
  simp only [K5, K4, K3, K2, K1, mem_fix, and_assoc]

theorem mem_K6 {σ : Perm (Fin 27)} :
    σ ∈ K6 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = 4 := by
  simp only [K6, K5, K4, K3, K2, K1, mem_fix, and_assoc]

theorem step0 : Nat.card Wt = 3 * Nat.card K1 := by
  refine card_step Wt 0 {0, 7, 12} (fun σ hσ => ?_) (fun s hs => ?_)
  · have h := (pattern hσ [] (by simp) 0 (by simp)).1
    revert h; generalize σ 0 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g0_7 (by decide),
        ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl⟩
    · exact ⟨ofFun g0_12 (by decide),
        ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl⟩

theorem step1 : Nat.card K1 = 2 * Nat.card K2 := by
  refine card_step K1 7 {7, 12} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0⟩ := mem_K1.1 hσ
    have h := pattern hW [0] (by simp [h0]) 7 (by decide)
    revert h; generalize σ 7 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g1_12 (by decide), mem_K1.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl⟩, rfl⟩

theorem step2 : Nat.card K2 = 8 * Nat.card K3 := by
  refine card_step K2 1 {1, 6, 21, 22, 23, 24, 25, 26} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1⟩ := mem_K2.1 hσ
    have h := pattern hW [0, 7] (by simp [h0, h1]) 1 (by decide)
    revert h; generalize σ 1 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g2_6 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_21 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_22 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_23 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_24 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_25 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_26 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩

theorem step3 : Nat.card K3 = 4 * Nat.card K4 := by
  refine card_step K3 2 {2, 3, 4, 5} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1, h2⟩ := mem_K3.1 hσ
    have h := pattern hW [0, 7, 1] (by simp [h0, h1, h2]) 2 (by decide)
    revert h; generalize σ 2 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g3_3 (by decide), mem_K3.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g3_4 (by decide), mem_K3.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g3_5 (by decide), mem_K3.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl⟩, rfl⟩

theorem step4 : Nat.card K4 = 3 * Nat.card K5 := by
  refine card_step K4 3 {3, 4, 5} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1, h2, h3⟩ := mem_K4.1 hσ
    have h := pattern hW [0, 7, 1, 2] (by simp [h0, h1, h2, h3]) 3 (by decide)
    revert h; generalize σ 3 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g4_4 (by decide), mem_K4.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g4_5 (by decide), mem_K4.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl, rfl⟩, rfl⟩

theorem step5 : Nat.card K5 = 2 * Nat.card K6 := by
  refine card_step K5 4 {4, 5} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1, h2, h3, h4⟩ := mem_K5.1 hσ
    have h := pattern hW [0, 7, 1, 2, 3] (by simp [h0, h1, h2, h3, h4]) 4 (by decide)
    revert h; generalize σ 4 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g5_5 (by decide), mem_K5.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem K6_eq_bot : K6 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => Equiv.ext fun v => ?_
  obtain ⟨hW, h0, h1, h2, h3, h4, h5⟩ := mem_K6.1 hσ
  have hB : ∀ x ∈ ([0, 7, 1, 2, 3, 4] : List (Fin 27)), σ x = x := by simp [h0, h1, h2, h3, h4, h5]
  by_cases hv : v ∈ ([0, 7, 1, 2, 3, 4] : List (Fin 27))
  · exact hB v hv
  have h := pattern hW [0, 7, 1, 2, 3, 4] hB v hv
  have hsep : ∀ w u : Fin 27, u ∉ ([0, 7, 1, 2, 3, 4] : List (Fin 27)) →
      ((w ∈ t ↔ u ∈ t) ∧
        ∀ x ∈ ([0, 7, 1, 2, 3, 4] : List (Fin 27)), meets w x = meets u x ∧ w ≠ x) →
        w = u := by
    decide +kernel
  exact hsep _ _ hv h

/-- **Page 26.** `card W_t = 1152`. -/
theorem card_Wt : Nat.card Wt = 1152 := by
  rw [step0, step1, step2, step3, step4, step5, K6_eq_bot, Subgroup.card_bot]

/-- **Page 25.** The automorphisms fixing `t` pointwise form a group of order `192`. -/
theorem card_pointwise :
    Nat.card {σ : Perm (Fin 27) // σ ∈ Wt ∧ ∀ v ∈ t, σ v = v} = 192 := by
  have e : Nat.card {σ : Perm (Fin 27) // σ ∈ Wt ∧ ∀ v ∈ t, σ v = v} = Nat.card K2 := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    rw [mem_K2]
    refine ⟨fun h => ⟨h.1, h.2 0 (by decide), h.2 7 (by decide)⟩, fun ⟨hW, h0, h7⟩ => ⟨hW, ?_⟩⟩
    have h12 : σ 12 ∈ t := (hW.2 12).2 (by decide)
    have h12' : σ 12 = 12 := by
      simp only [t, Finset.mem_insert, Finset.mem_singleton] at h12
      rcases h12 with h | h | h
      · exact absurd (σ.injective (h.trans h0.symm)) (by decide)
      · exact absurd (σ.injective (h.trans h7.symm)) (by decide)
      · exact h
    intro v hv
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  rw [e, step2, step3, step4, step5, K6_eq_bot, Subgroup.card_bot]

/-- The same count for the graph automorphisms `C ≃g C` that preserve `t`. -/
theorem card_aut : Nat.card {f : C ≃g C // ∀ v, f v ∈ t ↔ v ∈ t} = 1152 := by
  rw [← card_Wt]
  refine Nat.card_congr
    { toFun := fun f => ⟨f.1.toEquiv, fun u v => ?_, f.2⟩
      invFun := fun σ => ⟨⟨σ.1, fun {u v} => ?_⟩, σ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · have := f.1.map_rel_iff (a := u) (b := v)
    simp only [C] at this
    exact Bool.eq_iff_iff.2 this
  · change meets (σ.1 u) (σ.1 v) = true ↔ meets u v = true
    rw [σ.2.1 u v]

/-! ## Problem 18 of `docs/problems/article.tex`: the group of a marked triangle

Pages 25 and 26 describe `Aut(C, t)` as an extension of `𝔖_t × 𝔖_{V*}` by a group `Ψ̃` of
order 32, the Baer product of the three pull-backs of the quaternion group `Q₈ = Ṽ` along the
projections of `Ψ(V, t) = Ker(V^t → V)`. Concretely, `Ψ̃` is the group of triples
`(q₁, q₂, q₃)` of quaternions whose product is central (so that their images in `V = Q₈/{±1}`
sum to zero), modulo the central triples `(ε₁, ε₂, ε₃)` with `ε₁ε₂ε₃ = 1`.

The statement is the `Prop` `problem18`, proved below (`problem18_holds`): `φ` is the action
on the three lines of `t` and on the three partitions `V*`, checked to be onto on explicit
elements; `H → Ker φ` is `(a, b, c) ↦ U(a) V(c) Z^s` (`b = a c s`) for a table of
seventeen automorphisms, a homomorphism by the relations between `U`, `V` and `Z` (finite
kernel computations), onto because `card H / 4 = 32 = card W_t / 36` (`card_Wt`). The rest
of the page (the reconstruction of the graph from `(t, V, P̃)`, the characterisation of `Ψ̃`
by the anisotropy conditions, the equivalence of categories) is not formalised. -/

section Problem18

/-- The quaternion group of order 8. -/
abbrev Q8 := QuaternionGroup 2

/-- Problem 18 (group part): there is a surjection `Wt → 𝔖₃ × 𝔖₃` whose kernel is the Baer
product of the three pull-backs of `Q₈`, presented as the triples with central product
modulo the central triples of product one. -/
def problem18 : Prop :=
  ∃ H : Subgroup (Q8 × Q8 × Q8),
    (∀ x : Q8 × Q8 × Q8, x ∈ H ↔ x.1 * x.2.1 * x.2.2 ∈ Subgroup.center Q8) ∧
    ∃ φ : Wt →* Perm (Fin 3) × Perm (Fin 3), Function.Surjective φ ∧
      ∃ f : H →* φ.ker, Function.Surjective f ∧
        ∀ x : H, f x = 1 ↔
          ((x : Q8 × Q8 × Q8).1 ∈ Subgroup.center Q8 ∧
            (x : Q8 × Q8 × Q8).2.1 ∈ Subgroup.center Q8 ∧
            (x : Q8 × Q8 × Q8).2.2 ∈ Subgroup.center Q8 ∧
            (x : Q8 × Q8 × Q8).1 * (x : Q8 × Q8 × Q8).2.1 * (x : Q8 × Q8 × Q8).2.2 = 1)

/-! ### Proof

`φ = (φ₁, φ₂)`: `φ₁` is the action on the three lines of `t`; `φ₂` the action on the three
partitions `{2, 3 | 4, 5}`, `{2, 4 | 3, 5}`, `{2, 5 | 3, 4}` of the four other triangles
through each line of `t` (the `V*` of page 26). They are read on the 144 ordered pairs
`(x, y)` of skew lines outside `t` meeting the same line of `t`: two such pairs are in the
same class iff the number of incidences (meeting or equal) between them is even. Writing
`b = a c s` (`s = ±1`) for `(a, b, c) ∈ H`, the map `H → Ψ̃` is `(a, b, c) ↦ U(a) V(c) Z^s`,
where `U(q)`, `V(q)`, `Z` are the images of `(q, q, 1)`, `(1, q, q)`, `(1, 1, -1)`: `U` and
`V` are homomorphisms, `Z` is central and `V(c) U(a) = U(a) V(c) Z^{[c, a] ≠ 1}`, which
makes it a homomorphism; it is onto by counting (`card_Wt`). -/

open QuaternionGroup

/-- How `W_t` moves the class of the representative `r i`. -/
def clsFun {α : Type} (act : Perm (Fin 27) → α → α) (c : α → Fin 3) (r : Fin 3 → α)
    (σ : Perm (Fin 27)) (i : Fin 3) : Fin 3 :=
  c (act σ (r i))

theorem clsFun_mul {α : Type} (act : Perm (Fin 27) → α → α)
    (hact : ∀ σ τ p, act (σ * τ) p = act σ (act τ p)) (X : α → Prop) (c : α → Fin 3)
    (r : Fin 3 → α) (hr : ∀ i, X (r i) ∧ c (r i) = i)
    (hX : ∀ σ ∈ Wt, ∀ p, X p → X (act σ p))
    (hc : ∀ σ ∈ Wt, ∀ p q, X p → X q → c p = c q → c (act σ p) = c (act σ q))
    {σ τ : Perm (Fin 27)} (hσ : σ ∈ Wt) (hτ : τ ∈ Wt) (i : Fin 3) :
    clsFun act c r (σ * τ) i = clsFun act c r σ (clsFun act c r τ i) := by
  unfold clsFun
  rw [hact]
  exact hc σ hσ _ _ (hX τ hτ _ (hr i).1) (hr _).1 (hr _).2.symm

/-- The action of `W_t` on three classes of objects, as a homomorphism. -/
def clsHom {α : Type} (act : Perm (Fin 27) → α → α)
    (hact : ∀ σ τ p, act (σ * τ) p = act σ (act τ p)) (hact1 : ∀ p, act 1 p = p)
    (X : α → Prop) (c : α → Fin 3) (r : Fin 3 → α) (hr : ∀ i, X (r i) ∧ c (r i) = i)
    (hX : ∀ σ ∈ Wt, ∀ p, X p → X (act σ p))
    (hc : ∀ σ ∈ Wt, ∀ p q, X p → X q → c p = c q → c (act σ p) = c (act σ q)) :
    Wt →* Perm (Fin 3) where
  toFun σ :=
    { toFun := clsFun act c r σ.1
      invFun := clsFun act c r σ.1⁻¹
      left_inv := fun i => by
        rw [← clsFun_mul act hact X c r hr hX hc (inv_mem σ.2) σ.2, inv_mul_cancel]
        simp [clsFun, hact1, (hr i).2]
      right_inv := fun i => by
        rw [← clsFun_mul act hact X c r hr hX hc σ.2 (inv_mem σ.2), mul_inv_cancel]
        simp [clsFun, hact1, (hr i).2] }
  map_one' := Equiv.ext fun i => by simp [clsFun, hact1, (hr i).2]
  map_mul' σ τ := Equiv.ext fun i => clsFun_mul act hact X c r hr hX hc σ.2 τ.2 i

/-- The index of a line of `t`. -/
def c1 (v : Fin 27) : Fin 3 := if v = 0 then 0 else if v = 7 then 1 else 2

/-- The lines `a₀, b₁, c₀₁` of `t`. -/
def r1 : Fin 3 → Fin 27 := ![0, 7, 12]

/-- `φ₁`: the action on the three lines of `t`. -/
def phi1 : Wt →* Perm (Fin 3) :=
  clsHom (fun σ v => σ v) (fun _ _ _ => rfl) (fun _ => rfl) (fun v => v ∈ t) c1 r1
    (by decide +kernel) (fun σ hσ p hp => (hσ.2 p).2 hp) fun _ _ p q hp hq h => by
      rw [(by decide +kernel : ∀ p q : Fin 27, p ∈ t → q ∈ t → c1 p = c1 q → p = q) p q hp hq h]

/-- The relation « meeting or equal », as bit `27 u + v`. -/
@[irreducible] def meqBits : ℕ :=
  0x1099f0c1255d141933618319b24895554521cc986170e8a2552c925 * 2 ^ 512 +
    0x3168a2b81e0c316f086156d08a336909278e10a2fe010c3d22103f52210bd922 * 2 ^ 256 +
    0x11b8e2213b03c217a007c1fb4883f05488bd06489b90388bb100f0fa1001ff81

/-- Meeting or equal, read on `meqBits`. -/
def meq (u v : Fin 27) : Bool := meqBits.testBit (27 * u.val + v.val)

theorem meq_spec : ∀ u v : Fin 27, meq u v = (meets u v || decide (u = v)) ∧
    meets u v = (meq u v && !decide (u = v)) := by decide +kernel

/-- An injective map preserving « meeting or equal » and `t` is in `W_t`. -/
theorem ofFun_mem' (f : Fin 27 → Fin 27) (hf : Function.Injective f)
    (h : ∀ u v, meq (f u) (f v) = meq u v) (ht : ∀ v, f v ∈ t ↔ v ∈ t) : ofFun f hf ∈ Wt :=
  ofFun_mem _ _ (fun u v => by simp only [(meq_spec _ _).2, h, hf.eq_iff]) ht

/-- The lines meeting or equal to `p.1` or `p.2`, but not both, as 27 bits. -/
def Sv (p : Fin 27 × Fin 27) : ℕ :=
  (meqBits >>> (27 * p.1.val) ^^^ meqBits >>> (27 * p.2.val)) % 2 ^ 27

theorem Sv_bit (p : Fin 27 × Fin 27) (v : Fin 27) :
    (Sv p).testBit v = xor (meq p.1 v) (meq p.2 v) := by
  simp only [Sv, meq, Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftRight, v.isLt,
    decide_true, Bool.true_and]

/-- Is the number of incidences of `q.1, q.2` with the bits `s` even? -/
def fS (s : ℕ) (q : Fin 27 × Fin 27) : Bool := !(xor (s.testBit q.1) (s.testBit q.2))

/-- Two pairs of lines are in the same class iff they have an even number of incidences. -/
def fpar (p q : Fin 27 × Fin 27) : Bool := fS (Sv p) q

/-- The pairs `(b₂, b₃)`, `(b₂, b₄)`, `(b₂, b₅)`: the partitions `{2, 3 | 4, 5}`,
`{2, 4 | 3, 5}`, `{2, 5 | 3, 4}`. -/
def r2 : Fin 3 → Fin 27 × Fin 27 := ![(8, 9), (8, 10), (8, 11)]

/-- The class of a pair. -/
def c2 (p : Fin 27 × Fin 27) : Fin 3 :=
  if fpar p (8, 9) then 0 else if fpar p (8, 10) then 1 else 2

/-- Ordered pairs of skew lines outside `t` meeting the same line of `t`. -/
def X2 (p : Fin 27 × Fin 27) : Prop :=
  p.1 ∉ t ∧ p.2 ∉ t ∧ meq p.1 p.2 = false ∧ ∃ l ∈ t, meq p.1 l = true ∧ meq p.2 l = true

instance : DecidablePred X2 := fun p => by unfold X2; infer_instance

/-- The twelve values of `Sv` on `X2`, by class. -/
def Sl : Fin 3 → Fin 4 → ℕ :=
  ![![0x3c6630c, 0x3d98c30, 0x4278c4e, 0x4386372], ![0x24b4a56, 0x254a56a, 0x5aaa514, 0x5b54a28],
    ![0x18d295a, 0x192c666, 0x66cc618, 0x6732924]]

theorem X2_Sv : ∀ l ∈ t, ∀ u, meq u l = true → u ∉ t → ∀ v, meq v l = true → v ∉ t →
    meq u v = false → (∃ k m, Sv (u, v) = Sl k m ∧ c2 (u, v) = k) ∧
      ∀ k m, fS (Sl k m) (u, v) = (k == c2 (u, v)) := by
  decide +kernel

theorem c2_iff {p q : Fin 27 × Fin 27} (hp : X2 p) (hq : X2 q) :
    c2 p = c2 q ↔ fpar p q = true := by
  obtain ⟨h1, h2, h3, l, hl, h4, h5⟩ := hp
  obtain ⟨h1', h2', h3', l', hl', h4', h5'⟩ := hq
  obtain ⟨k, m, e1, e2⟩ := (X2_Sv l hl _ h4 h1 _ h5 h2 h3).1
  rw [fpar, e1, (X2_Sv l' hl' _ h4' h1' _ h5' h2' h3').2, e2, beq_iff_eq]

theorem meq_inv {σ : Perm (Fin 27)} (hσ : σ ∈ Wt) (u v : Fin 27) :
    meq (σ u) (σ v) = meq u v := by
  simp only [(meq_spec _ _).1, hσ.1 u v, σ.injective.eq_iff]

theorem X2_act {σ : Perm (Fin 27)} (hσ : σ ∈ Wt) {p : Fin 27 × Fin 27} (hp : X2 p) :
    X2 (σ p.1, σ p.2) := by
  obtain ⟨h1, h2, h3, l, hl, h4, h5⟩ := hp
  exact ⟨fun h => h1 ((hσ.2 _).1 h), fun h => h2 ((hσ.2 _).1 h), (meq_inv hσ _ _).trans h3, σ l,
    (hσ.2 l).2 hl, (meq_inv hσ _ _).trans h4, (meq_inv hσ _ _).trans h5⟩

/-- `φ₂`: the action on the three partitions. -/
def phi2 : Wt →* Perm (Fin 3) :=
  clsHom (fun σ p => (σ p.1, σ p.2)) (fun _ _ _ => rfl) (fun _ => rfl) X2 c2 r2
    (by decide +kernel) (fun _ hσ _ hp => X2_act hσ hp) fun _ hσ p q hp hq h => by
      rw [c2_iff (X2_act hσ hp) (X2_act hσ hq)]
      simpa only [fpar, fS, Sv_bit, meq_inv hσ] using (c2_iff hp hq).1 h

/-- `φ = (φ₁, φ₂) : W_t → 𝔖_t × 𝔖_{V*}`. -/
def phi : Wt →* Perm (Fin 3) × Perm (Fin 3) := phi1.prod phi2

/-- Elements of `W_t` moving only one factor. -/
noncomputable def e07 : Wt :=
  ⟨_, ofFun_mem' g0_7 (by decide) (by decide +kernel) (by decide +kernel)⟩
/-- See `e07`. -/
noncomputable def e012 : Wt :=
  ⟨_, ofFun_mem' g0_12 (by decide) (by decide +kernel) (by decide +kernel)⟩
/-- See `e07`. -/
noncomputable def e112 : Wt :=
  ⟨_, ofFun_mem' g1_12 (by decide) (by decide +kernel) (by decide +kernel)⟩
/-- See `e07`. -/
noncomputable def e33 : Wt :=
  ⟨_, ofFun_mem' g3_3 (by decide) (by decide +kernel) (by decide +kernel)⟩
/-- See `e07`. -/
noncomputable def e34 : Wt :=
  ⟨_, ofFun_mem' g3_4 (by decide) (by decide +kernel) (by decide +kernel)⟩
/-- See `e07`. -/
noncomputable def e35 : Wt :=
  ⟨_, ofFun_mem' g3_5 (by decide) (by decide +kernel) (by decide +kernel)⟩

theorem phi_surj : Function.Surjective phi := by
  rintro ⟨s1, s2⟩
  obtain ⟨σ, -, hσ⟩ : ∃ σ ∈ [1, e07, e012, e112, e07 * e112, e112 * e07], phi σ = (s1, 1) := by
    revert s1; decide +kernel
  obtain ⟨τ, -, hτ⟩ : ∃ τ ∈ [1, e33, e34, e35, e33 * e34, e34 * e33], phi τ = (1, s2) := by
    revert s2; decide +kernel
  exact ⟨σ * τ, by rw [map_mul, hσ, hτ, Prod.mk_mul_mk, mul_one, one_mul]⟩

theorem card_ker_phi : Nat.card phi.ker = 32 := by
  have h := Subgroup.card_mul_index phi.ker
  have h36 : Nat.card (Perm (Fin 3) × Perm (Fin 3)) = 36 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 phi_surj, Subgroup.card_top, card_Wt,
    h36] at h
  omega

/-- `Q₈ → Q₈ / {±1} = V`. -/
def piQ : Q8 → Multiplicative (ZMod 2 × ZMod 2)
  | .a i => Multiplicative.ofAdd (0, (i.val : ZMod 2))
  | .xa i => Multiplicative.ofAdd (1, (i.val : ZMod 2))

/-- See `piQ`. -/
def piH : Q8 →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun := piQ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- `(a, b, c) ↦ ā + b̄ + c̄ ∈ V`. -/
def sumV : Q8 × Q8 × Q8 →* Multiplicative (ZMod 2 × ZMod 2) :=
  piH.comp (MonoidHom.fst _ _) * piH.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    piH.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))

/-- The triples of quaternions with central product. -/
def H18 : Subgroup (Q8 × Q8 × Q8) := sumV.ker

theorem mem_center_Q8 (z : Q8) : z ∈ Subgroup.center Q8 ↔ z = a 0 ∨ z = a 2 := by
  rw [Subgroup.mem_center_iff]; revert z; decide +kernel

theorem mem_H18' (x : Q8 × Q8 × Q8) :
    x ∈ H18 ↔ x.1 * x.2.1 * x.2.2 = a 0 ∨ x.1 * x.2.1 * x.2.2 = a 2 := by
  rw [H18, MonoidHom.mem_ker]; revert x; decide +kernel

theorem mem_H18 (x : Q8 × Q8 × Q8) : x ∈ H18 ↔ x.1 * x.2.1 * x.2.2 ∈ Subgroup.center Q8 := by
  rw [mem_center_Q8, mem_H18']

/-- The `k`-th of a list of permutations of `Fin 27` stored in five-bit fields. -/
def permBits (B k : ℕ) (v : Fin 27) : Fin 27 :=
  ⟨B / 2 ^ (5 * (27 * k + v.val)) % 32 % 27, Nat.mod_lt _ (by decide)⟩

/-- The table of `U(q)`, image of `(q, q, 1)` (`k < 8`), `V(q)`, image of `(1, q, q)`
(`k = 8 + q`), for the codes `q` of `a 0, …, a 3, xa 0, …, xa 3`, and `Z`, image of
`(1, 1, -1)` (`k = 16`). -/
@[irreducible] def tabBits : ℕ :=
  0x56d7c674520c4b5250c83dcd38693944c0ce826ada841c50e7ad8d4aa07b96 * 2 ^ 2048 +
    0x72160180eaa6b96638b9105312d5bcf6a1242c833a09ab6a1071439eb6352a81 * 2 ^ 1792 +
    0xee59c8580603aa9ae598e2e4414c4b56f3da8490b200e336b98a4945f04258a5 * 2 ^ 1536 +
    0xb5c7ad2631681ace2f6ad2728c1ee6b16a4a0e62906208038cdae6292517c109 * 2 ^ 1280 +
    0x6296d71eb498c5a06b38bdab49ca307b9ac5a928398a418820adb17cea329d1a * 2 ^ 1024 +
    0xe7c1884a967308642841ab62f9a8c452250b531cd83ce194693302b6c5f3a8ca * 2 ^ 768 +
    0x746b9f06212a59cc2190a106ad8be6a31148942d4c7360f38651a4cc0ae717b6 * 2 ^ 512 +
    0x88510d4b4258f835c70ce919181ace2f6ad2728c1ee6b16a4a0e629062082b9c * 2 ^ 256 +
    0x5eda2144352d0963e0d71c33a464606b38bdab49ca307b9ac5a928398a418820

/-- The `k`-th permutation of `tabBits`. -/
def tab (k : Fin 17) : Fin 27 → Fin 27 := permBits tabBits k

theorem tab_ok : ∀ k : Fin 17, (∀ v, tab (![0, 3, 2, 1, 6, 7, 4, 5, 8, 11, 10, 9, 14, 15, 12, 13,
    16] k) (tab k v) = v) ∧ (∀ v, tab k v ∈ t ↔ v ∈ t) ∧
      ∀ i, c1 (tab k (r1 i)) = i ∧ c2 (tab k (r2 i).1, tab k (r2 i).2) = i := by
  decide +kernel

theorem all_range {n : ℕ} {P : ℕ → Bool} (h : (List.range n).all P = true) (i : Fin n) :
    P i = true :=
  List.all_eq_true.1 h _ (List.mem_range.2 i.isLt)

theorem tab_meq : ((List.range 17).all fun k => (List.range 27).all fun u =>
    (List.range 27).all fun v => meqBits.testBit (27 * (tabBits / 2 ^ (5 * (27 * k + u)) % 32 % 27)
      + tabBits / 2 ^ (5 * (27 * k + v)) % 32 % 27) == meqBits.testBit (27 * u + v)) = true := by
  decide +kernel

/-- The `k`-th permutation of `tabBits`, as an element of `Ker φ`. -/
noncomputable def tabK (k : Fin 17) : phi.ker :=
  ⟨⟨ofFun (tab k) (Function.LeftInverse.injective (tab_ok k).1), ofFun_mem' _ _
      (fun u v => beq_iff_eq.1 (all_range (all_range (all_range tab_meq k) u) v)) (tab_ok k).2.1⟩,
    MonoidHom.mem_ker.2 <| Prod.ext (Equiv.ext fun i => ((tab_ok k).2.2 i).1)
      (Equiv.ext fun i => ((tab_ok k).2.2 i).2)⟩

/-- `U` on codes. -/
def U (i : Fin 8) : Fin 27 → Fin 27 := tab ⟨i, by omega⟩
/-- `V` on codes. -/
def V (i : Fin 8) : Fin 27 → Fin 27 := tab ⟨8 + i, by omega⟩
/-- `Z` if `e`, else the identity. -/
def W (e : Bool) : Fin 27 → Fin 27 := tab (cond e 16 0)

/-- Multiplication of `Q₈` on codes, in three-bit fields. -/
def mulBits : ℕ := 0x443d67688b3e0d19f521afac9f5443b3e21ad670d1fac688

/-- Multiplication on the codes `a 0, …, a 3, xa 0, …, xa 3 ↦ 0, …, 7`. -/
def mulT (i j : Fin 8) : Fin 8 :=
  ⟨mulBits / 2 ^ (3 * (8 * i.val + j.val)) % 8, Nat.mod_lt _ (by decide)⟩

/-- The code of a quaternion: `a 0, …, a 3, xa 0, …, xa 3 ↦ 0, …, 7`. -/
def code (q : Q8) : Fin 8 :=
  if q = a 0 then 0 else if q = a 1 then 1 else if q = a 2 then 2 else if q = a 3 then 3
  else if q = xa 0 then 4 else if q = xa 1 then 5 else if q = xa 2 then 6 else 7

theorem code_mul : ∀ p q : Q8, code (p * q) = mulT (code p) (code q) := by decide +kernel

theorem U_mul : ∀ i j v, U (mulT i j) v = U i (U j v) := by decide +kernel
theorem V_mul : ∀ i j v, V (mulT i j) v = V i (V j v) := by decide +kernel
theorem VU : ∀ i j v, V i (U j v) = U j (V i (W (mulT i j != mulT j i) v)) := by decide +kernel
theorem WU : ∀ e i v, W e (U i v) = U i (W e v) := by decide +kernel
theorem WV : ∀ e i v, W e (V i v) = V i (W e v) := by decide +kernel
theorem WW : ∀ e e' v, W e (W e' v) = W (xor e e') v := by decide +kernel

/-- `s = -1` in `b = a c s`. -/
def sb (x : Q8 × Q8 × Q8) : Bool := decide ((x.1 * x.2.2)⁻¹ * x.2.1 = a 2)

/-- `(a, b, c) ↦ U(a) V(c) Z^s`. -/
def Ff (x : Q8 × Q8 × Q8) (v : Fin 27) : Fin 27 := U (code x.1) (V (code x.2.2) (W (sb x) v))

theorem sb_mul {x y : Q8 × Q8 × Q8} (hx : x ∈ H18) (hy : y ∈ H18) :
    sb (x * y) = xor (mulT (code x.2.2) (code y.1) != mulT (code y.1) (code x.2.2))
      (xor (sb x) (sb y)) := by
  have hs : ∀ x ∈ H18, (x.1 * x.2.2)⁻¹ * x.2.1 ∈ [a 0, a 2] := fun x hx => by
    have := (mem_H18' x).1 hx; clear hx; revert x; decide +kernel
  obtain ⟨p, q, r⟩ := x
  obtain ⟨p', q', r'⟩ := y
  obtain ⟨s, h1, rfl⟩ : ∃ s ∈ [a 0, a 2], q = p * r * s := ⟨_, hs _ hx, by group⟩
  obtain ⟨s', h2, rfl⟩ : ∃ s ∈ [a 0, a 2], q' = p' * r' * s := ⟨_, hs _ hy, by group⟩
  have hc : ∀ s ∈ [a 0, a 2], ∀ g : Q8, g * s = s * g := by decide +kernel
  have e : (p * p' * (r * r'))⁻¹ * (p * r * s * (p' * r' * s')) =
      (p' * r)⁻¹ * (r * p') * s * s' := by
    calc _ = r'⁻¹ * ((p' * r)⁻¹ * r * (s * p')) * r' * s' := by group
      _ = r'⁻¹ * ((p' * r)⁻¹ * (r * p') * s * r') * s' := by rw [← hc s h1 p']; group
      _ = _ := by
        rw [← hc _ ((by decide +kernel : ∀ r p' : Q8, ∀ s ∈ [a 0, a 2],
          (p' * r)⁻¹ * (r * p') * s ∈ [a 0, a 2]) r p' s h1) r']; group
  simp only [sb, Prod.mk_mul_mk, inv_mul_cancel_left, e]
  exact (by decide +kernel : ∀ r p' : Q8, ∀ s ∈ [a 0, a 2], ∀ s' ∈ [a 0, a 2],
    decide ((p' * r)⁻¹ * (r * p') * s * s' = a 2) = xor (mulT (code r) (code p') !=
      mulT (code p') (code r)) (xor (decide (s = a 2)) (decide (s' = a 2)))) r p' s h1 s' h2

/-- The surjection `H → Ker φ`. -/
noncomputable def f18 : H18 →* phi.ker where
  toFun x := tabK ⟨code x.1.1, by omega⟩ * tabK ⟨8 + code x.1.2.2, by omega⟩ *
    tabK (cond (sb x.1) 16 0)
  map_one' := Subtype.ext (Subtype.ext (Equiv.ext (by decide +kernel)))
  map_mul' x y := Subtype.ext <| Subtype.ext <| Equiv.ext fun v => by
    change Ff (x.1 * y.1) v = Ff x.1 (Ff y.1 v)
    simp only [Ff, sb_mul x.2 y.2, Prod.fst_mul, Prod.snd_mul, code_mul, U_mul, V_mul, WU, WV,
      VU, WW]

/-- The kernel condition: central coordinates with product one. -/
def kcond (x : Q8 × Q8 × Q8) : Prop :=
  (x.1 = a 0 ∨ x.1 = a 2) ∧ (x.2.1 = a 0 ∨ x.2.1 = a 2) ∧ (x.2.2 = a 0 ∨ x.2.2 = a 2) ∧
    x.1 * x.2.1 * x.2.2 = 1

instance : DecidablePred kcond := fun x => by unfold kcond; infer_instance

theorem f18_eq_one' (x : H18) : f18 x = 1 ↔ kcond x.1 := by
  rw [← (by decide +kernel : ∀ x : Q8 × Q8 × Q8, (x.1 * x.2.1 * x.2.2 = a 0 ∨
    x.1 * x.2.1 * x.2.2 = a 2) → ((∀ v, Ff x v = v) ↔ kcond x)) x.1 ((mem_H18' _).1 x.2)]
  exact ⟨fun h v => congrArg (fun σ : phi.ker => (σ : Perm (Fin 27)) v) h,
    fun h => Subtype.ext (Subtype.ext (Equiv.ext h))⟩

theorem f18_eq_one (x : H18) : f18 x = 1 ↔
    ((x : Q8 × Q8 × Q8).1 ∈ Subgroup.center Q8 ∧
      (x : Q8 × Q8 × Q8).2.1 ∈ Subgroup.center Q8 ∧
      (x : Q8 × Q8 × Q8).2.2 ∈ Subgroup.center Q8 ∧
      (x : Q8 × Q8 × Q8).1 * (x : Q8 × Q8 × Q8).2.1 * (x : Q8 × Q8 × Q8).2.2 = 1) := by
  simpa only [mem_center_Q8, kcond] using f18_eq_one' x

theorem card_H18 : Nat.card H18 = 128 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight mem_H18'), Nat.card_eq_fintype_card]
  decide +kernel

theorem card_ker_f18 : Nat.card f18.ker = 4 := by
  rw [Nat.card_congr ((Equiv.subtypeEquivRight fun x => (MonoidHom.mem_ker).trans
      (f18_eq_one' x)).trans (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ H18) kcond)),
    Nat.card_congr (Equiv.subtypeEquivRight fun x => and_congr_left' (mem_H18' x)),
    Nat.card_eq_fintype_card]
  decide +kernel

/-- **Problem 18 (group part) holds.** -/
theorem problem18_holds : problem18 := by
  refine ⟨H18, mem_H18, phi, phi_surj, f18, ?_, f18_eq_one⟩
  have h := Subgroup.card_mul_index f18.ker
  rw [Subgroup.index_ker, card_ker_f18, card_H18] at h
  exact MonoidHom.range_eq_top.1
    (Subgroup.eq_top_of_card_eq _ ((by omega : Nat.card f18.range = 32).trans card_ker_phi.symm))

end Problem18

end Grothendieck.Folder69
