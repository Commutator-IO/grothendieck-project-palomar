module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder80Maps3

open Relation

/-- A set invariant under the generators of an equivalence closure is invariant under it. -/
theorem eqvGen_iff {α : Type*} {r : α → α → Prop} (S : α → Prop) (h : ∀ x y, r x y → (S x ↔ S y))
    {a b : α} (hab : EqvGen r a b) : S a ↔ S b :=
  (Equivalence.eqvGen_iff (r := fun x y => S x ↔ S y) ⟨fun _ => .rfl, .symm, .trans⟩).1
    (EqvGen.mono h _ _ hab)

/-- A generalised map: flags with three fixed-point-free involutions, `a0` and `a2` commuting
with `a0 a2` fixed-point-free. -/
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d

namespace GMap

variable {D : Type*} (M : GMap D)

/-- Vertices are the classes of `⟨a1, a2⟩`. -/
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x

/-- Edges are the classes of `⟨a0, a2⟩`. -/
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x

/-- Faces are the classes of `⟨a0, a1⟩`. -/
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x

/-- The vertex of a flag. -/
def vtx (d : D) : M.Vtx := Quot.mk _ d

/-- The edge of a flag. -/
def edge (d : D) : M.Edge := Quot.mk _ d

/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face

variable {M}

@[simp] theorem vtx_a1 (d : D) : M.vtx (M.a1 d) = M.vtx d := (Quot.sound (.inl rfl)).symm

@[simp] theorem vtx_a2 (d : D) : M.vtx (M.a2 d) = M.vtx d := (Quot.sound (.inr rfl)).symm

@[simp] theorem edge_a0 (d : D) : M.edge (M.a0 d) = M.edge d := (Quot.sound (.inl rfl)).symm

theorem a0_eq_iff {x y : D} : M.a0 x = y ↔ x = M.a0 y :=
  ⟨fun h => h ▸ (M.a0_a0 x).symm, fun h => h ▸ M.a0_a0 y⟩

theorem a1_eq_iff {x y : D} : M.a1 x = y ↔ x = M.a1 y :=
  ⟨fun h => h ▸ (M.a1_a1 x).symm, fun h => h ▸ M.a1_a1 y⟩

theorem a2_eq_iff {x y : D} : M.a2 x = y ↔ x = M.a2 y :=
  ⟨fun h => h ▸ (M.a2_a2 x).symm, fun h => h ▸ M.a2_a2 y⟩

/-- An edge has exactly the four flags `d, a0 d, a2 d, a0 a2 d`. -/
theorem edge_eq {d e : D} :
    M.edge e = M.edge d ↔ e = d ∨ e = M.a0 d ∨ e = M.a2 d ∨ e = M.a0 (M.a2 d) := by
  constructor
  · intro h
    refine (eqvGen_iff (fun x => x = d ∨ x = M.a0 d ∨ x = M.a2 d ∨ x = M.a0 (M.a2 d)) ?_
      (Quot.eqvGen_exact h)).2 (.inl rfl)
    rintro x y (rfl | rfl)
    · simp only [a0_eq_iff, M.a0_a0]; tauto
    · simp only [a2_eq_iff, ← M.a0_a2, M.a2_a2]; tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem edge_four (d : D) : [d, M.a0 d, M.a2 d, M.a0 (M.a2 d)].Nodup := by
  have := M.a0_ne d; have := M.a2_ne d; have := M.a02_ne d; have := M.a0_ne (M.a2 d)
  simp_all [eq_comm, a0_eq_iff, M.a0_a0]

end GMap

open GMap

/-- Every line carries at least three vertices. -/
def BigonFree {P L : Type*} (on : P → L → Prop) : Prop :=
  ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- A combinatorial pseudoline arrangement (page 60), as in `Folder80Maps2`: a generalised map
with flags labelled by lines, constant on edges; a line through a vertex has there the four
flags of two edge-ends; each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; `χ = 1`. -/
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1

namespace PseudolineMap

variable {D L : Type*} (X : PseudolineMap D L)

/-- The line `l` passes through the vertex `v`. -/
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l

variable {X}

/-- A line whose flags all sit at two vertices `u, w` is not bigon-free. -/
theorem confined (hbf : BigonFree X.On) {l : L} {u w : X.M.Vtx}
    (H : ∀ e, X.line e = l → X.M.vtx e = u ∨ X.M.vtx e = w) : False := by
  obtain ⟨p, q, r, ⟨d1, rfl, h1⟩, ⟨d2, rfl, h2⟩, ⟨d3, rfl, h3⟩, h12, h13, h23⟩ := hbf l
  rcases H _ h1 with h1 | h1 <;> rcases H _ h2 with h2 | h2 <;> rcases H _ h3 with h3 | h3 <;>
    simp_all

/-- The connected line `l` stays in a set of vertices stable under `a0` along `l`. -/
theorem confine {l : L} (Z : X.M.Vtx → Prop)
    (h : ∀ x, X.line x = l → Z (X.M.vtx x) → Z (X.M.vtx (X.M.a0 x))) {d : D} (hd : X.line d = l)
    (hZ : Z (X.M.vtx d)) {e : D} (he : X.line e = l) : Z (X.M.vtx e) := by
  refine (eqvGen_iff (fun x => X.line x = l → Z (X.M.vtx x)) ?_ (X.conn d e (hd.trans he.symm))).1
    (fun _ => hZ) he
  rintro x y (rfl | ⟨h1, h2⟩)
  · rw [X.line_a0]
    exact ⟨fun h' hx => h _ hx (h' hx), fun h' hx => by
      simpa [X.M.a0_a0] using h _ (by rwa [X.line_a0]) (h' hx)⟩
  · rw [h1, h2]

variable [Fintype D]

open Classical in
/-- The four flags of a line at a vertex. -/
theorem at_four {d x1 x2 x3 x4 : D} (hn : [x1, x2, x3, x4].Nodup)
    (hx : ∀ x ∈ [x1, x2, x3, x4], X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d) {f : D}
    (hf : X.M.vtx f = X.M.vtx d) (hl : X.line f = X.line d) : f ∈ [x1, x2, x3, x4] := by
  have h4 := X.pass d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have := Finset.eq_of_subset_of_card_le (s := [x1, x2, x3, x4].toFinset)
    (t := Finset.univ.filter fun e => X.M.vtx e = X.M.vtx d ∧ X.line e = X.line d)
    (fun x hx' => by simpa using hx _ (List.mem_toFinset.1 hx'))
    (by rw [h4, List.toFinset_card_of_nodup hn]; rfl)
  simpa [hf, hl] using (Finset.ext_iff.1 this f).2

/-- No loop: the two ends of an edge are distinct vertices. -/
theorem noLoop (hbf : BigonFree X.On) (d : D) : X.M.vtx (X.M.a0 d) ≠ X.M.vtx d := by
  intro h
  have hall : ∀ x ∈ [d, X.M.a0 d, X.M.a2 d, X.M.a0 (X.M.a2 d)],
      X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d := by
    simp [h, X.line_a0, X.line_a2, X.M.a0_a2]
  refine confined hbf (l := X.line d) (u := X.M.vtx d) (w := X.M.vtx d) fun e he => .inl ?_
  refine confine (fun t => t = X.M.vtx d) (fun x hx hxv => ?_) rfl rfl he
  have := at_four (edge_four d) hall hxv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> simp [h, X.M.a0_a0, X.M.a0_a2]

/-- At a vertex, the two flags of an edge-end are followed by flags of two different edges. -/
theorem edge_a1_a2_ne (hbf : BigonFree X.On) (u : D) :
    X.M.edge (X.M.a1 (X.M.a2 u)) ≠ X.M.edge (X.M.a1 u) := by
  intro e1
  have hn := noLoop hbf
  rcases edge_eq.1 e1 with k | k | k | k
  · exact X.M.a2_ne u (by simpa [X.M.a1_a1] using congrArg X.M.a1 k)
  · exact hn (X.M.a1 u) (by rw [← k]; simp)
  · -- `a1 a2 u = a2 a1 u`: the vertex of `u` has four flags only
    obtain ⟨e, hev, hel⟩ := X.two u
    have hS : ∀ x, X.M.vtx x = X.M.vtx u →
        x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨ x = X.M.a1 (X.M.a2 u) := fun x hx => by
      refine (eqvGen_iff (fun x => x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨
        x = X.M.a1 (X.M.a2 u)) ?_ (Quot.eqvGen_exact hx)).2 (.inl rfl)
      have k' : X.M.a2 (X.M.a1 (X.M.a2 u)) = X.M.a1 u := by rw [k, X.M.a2_a2]
      rintro x y (rfl | rfl)
      · simp only [a1_eq_iff, X.M.a1_a1]; tauto
      · simp only [a2_eq_iff, ← k, k', X.M.a2_a2]; tauto
    have hl1 : X.line (X.M.a1 u) ≠ X.line u := fun hl => hel <| by
      rcases hS e hev with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    classical
    have h4 := X.pass u
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
    have hsub : (Finset.univ.filter fun e => X.M.vtx e = X.M.vtx u ∧ X.line e = X.line u) ⊆
        {u, X.M.a2 u} := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hS x hx.1 with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  · exact hn (X.M.a2 (X.M.a1 u)) (by rw [← k]; simp)

section Chains

open Matrix

variable (X) in
/-- The vertex `v` is an end of the edge `e`. -/
def Inc (v : X.M.Vtx) (e : X.M.Edge) : Prop := ∃ d, X.M.vtx d = v ∧ X.M.edge d = e

variable (X) in
/-- The line of an edge. -/
def lineE : X.M.Edge → L :=
  Quot.lift X.line fun x _ h => h.elim (fun h => h ▸ (X.line_a0 x).symm) fun h =>
    h ▸ (X.line_a2 x).symm

omit [Fintype D] in
@[simp] theorem lineE_edge (d : D) : X.lineE (X.M.edge d) = X.line d := rfl

/-- The flags at a vertex on a given edge are `d` and `a2 d`. -/
theorem at_edge (hbf : BigonFree X.On) {d x : D} :
    X.M.vtx x = X.M.vtx d ∧ X.M.edge x = X.M.edge d ↔ x = d ∨ x = X.M.a2 d := by
  refine ⟨fun ⟨hv, he⟩ => ?_, by rintro (rfl | rfl) <;> simp⟩
  rcases edge_eq.1 he with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact (noLoop hbf _ hv).elim
  · exact .inr rfl
  · exact (noLoop hbf (X.M.a2 d) (by rw [hv, vtx_a2])).elim

omit [Fintype D] in
theorem inc_iff (d : D) (v : X.M.Vtx) :
    X.Inc v (X.M.edge d) ↔ v = X.M.vtx d ∨ v = X.M.vtx (X.M.a0 d) := by
  constructor
  · rintro ⟨x, rfl, hx⟩
    rcases edge_eq.1 hx with rfl | rfl | rfl | rfl <;> simp [X.M.a0_a2]
  · rintro (rfl | rfl)
    exacts [⟨d, rfl, rfl⟩, ⟨_, rfl, edge_a0 d⟩]

end Chains

variable (X) in
/-- The rotation `φ = a2 a1` around a vertex: from an edge-end to the next one. -/
def phi : Equiv.Perm D :=
  Function.Involutive.toPerm X.M.a2 X.M.a2_a2 * Function.Involutive.toPerm X.M.a1 X.M.a1_a1

omit [Fintype D] in
theorem phi_apply (x : D) : X.phi x = X.M.a2 (X.M.a1 x) := rfl

omit [Fintype D] in
theorem phi_inv_apply (x : D) : X.phi⁻¹ x = X.M.a1 (X.M.a2 x) :=
  (Equiv.Perm.inv_eq_iff_eq).2 (by simp [phi_apply, X.M.a1_a1, X.M.a2_a2])

omit [Fintype D] in
theorem a2_phi (x : D) : X.M.a2 (X.phi x) = X.M.a1 x := X.M.a2_a2 _

omit [Fintype D] in
/-- A function invariant under `φ` is invariant under its powers. -/
theorem zpow_inv {α : Type*} (g : D → α) (h : ∀ x, g (X.phi x) = g x) (k : ℤ) (x : D) :
    g ((X.phi ^ k) x) = g x := by
  induction k with
  | zero => simp
  | succ n ih => rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, h, ih]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, ← ih,
      ← h (X.phi⁻¹ _)]
    exact congrArg g ((Equiv.eq_symm_apply X.phi).mp rfl)

omit [Fintype D] in
@[simp] theorem vtx_phi (k : ℤ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x :=
  zpow_inv _ (fun x => by simp [phi_apply]) k x

omit [Fintype D] in
@[simp] theorem vtx_phi' (k : ℕ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x := by
  simpa using vtx_phi (X := X) k x

omit [Fintype D] in
/-- `a2 φ^k = φ^{-k} a2`. -/
theorem a2_zpow (k : ℤ) (x : D) : X.M.a2 ((X.phi ^ k) x) = (X.phi ^ (-k)) (X.M.a2 x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, a2_phi,
      show -(1 + (n : ℤ)) = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, ← ih, zpow_neg_one,
      phi_inv_apply, X.M.a2_a2]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one,
      phi_inv_apply, ← phi_apply, ih, ← Equiv.Perm.mul_apply, ← zpow_one_add]
    congr 2; ring

omit [Fintype D] in
/-- The two orbits of `φ` at a vertex are exchanged by `a2`: `a2 φ^i x ≠ φ^j x`. -/
theorem a2_ne_zpow (i j : ℤ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  intro h
  rw [a2_zpow] at h
  have h' : X.M.a2 x = (X.phi ^ (i + j)) x := by
    have := congrArg (X.phi ^ i) h
    rwa [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply,
      ← Equiv.Perm.mul_apply, ← zpow_add] at this
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' (i + j)
  · apply X.M.a2_ne ((X.phi ^ t) x)
    rw [a2_zpow, h', ht, ← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2; ring
  · apply X.M.a1_ne ((X.phi ^ t) x)
    rw [← a2_phi, ← Equiv.Perm.mul_apply, ← zpow_one_add, a2_zpow, h', ht, ← Equiv.Perm.mul_apply,
      ← zpow_add]
    congr 2; ring

omit [Fintype D] in
/-- The flags at the vertex of `x` are the `φ^k x` and the `a2 φ^k x`. -/
theorem vtx_orbit {x y : D} (h : X.M.vtx y = X.M.vtx x) :
    ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x) := by
  let S : D → Prop := fun y => ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x)
  have c1 : ∀ u, S u → S (X.M.a1 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨1 + k, .inr (by rw [zpow_one_add, Equiv.Perm.mul_apply, a2_phi])⟩
    · exact ⟨-1 + k, .inl (by rw [zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, phi_inv_apply])⟩
  have c2 : ∀ u, S u → S (X.M.a2 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨k, .inr rfl⟩
    · exact ⟨k, .inl (X.M.a2_a2 _)⟩
  refine (eqvGen_iff S ?_ (Quot.eqvGen_exact h)).2 ⟨0, .inl rfl⟩
  rintro u w (rfl | rfl)
  · exact ⟨c1 u, fun h => by simpa [X.M.a1_a1] using c1 _ h⟩
  · exact ⟨c2 u, fun h => by simpa [X.M.a2_a2] using c2 _ h⟩

open Classical in
variable (X) in
/-- The number `ν(v)` of lines through a vertex. -/
noncomputable def nu (v : X.M.Vtx) : ℕ :=
  ((Finset.univ.filter fun d => X.M.vtx d = v).image X.line).card

variable (X) in
/-- **Going straight** (page 60; (22) of page 41): half a turn around a vertex of `ν` lines,
`ν` edge-ends further, one finds the same line. -/
def Straight : Prop := ∀ d, X.line ((X.phi ^ X.nu (X.M.vtx d)) d) = X.line d

open Classical in
theorem card_vtx (x : D) :
    (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x).card = 4 * X.nu (X.M.vtx x) := by
  rw [Finset.card_eq_sum_card_image X.line, nu, Finset.sum_const_nat (m := 4), mul_comm]
  intro l hl
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hl
  have h4 := X.pass e
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  rw [Finset.filter_filter, ← h4]
  congr 1; ext a; simp [(Finset.mem_filter.1 he).2]

open Classical in
/-- A period of `φ` at a flag is at least the number `2ν` of edge-ends. -/
theorem four_nu_le (x : D) {q : ℕ} (hq : 0 < q) (h : (X.phi ^ q) x = x) :
    4 * X.nu (X.M.vtx x) ≤ 2 * q := by
  rw [← card_vtx]
  have hsub : (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x) ⊆
      ((Finset.range q) ×ˢ (Finset.univ : Finset Bool)).image
        fun p => if p.2 then X.M.a2 ((X.phi ^ p.1) x) else (X.phi ^ p.1) x := by
    intro y hy
    obtain ⟨k, hk⟩ := vtx_orbit (Finset.mem_filter.1 hy).2
    have hr : (X.phi ^ k) x = (X.phi ^ (k % q).toNat) x := by
      have h' : ((X.phi ^ (q : ℤ)) ^ (k / q)) x = x :=
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by simpa using h) _
      conv_lhs => rw [← Int.emod_add_mul_ediv k q, zpow_add, Equiv.Perm.mul_apply, zpow_mul, h']
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    have hlt : (k % q).toNat < q := by
      have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < q); omega
    rcases hk with rfl | rfl
    exacts [Finset.mem_image.2 ⟨((k % q).toNat, false), by simp [hlt], by simp [hr]⟩,
      Finset.mem_image.2 ⟨((k % q).toNat, true), by simp [hlt], by simp [hr]⟩]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [mul_comm]

omit [Fintype D] in
theorem a2_ne_pow (i j : ℕ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  simpa using a2_ne_zpow (X := X) i j x

/-- Distinct powers below `2ν` of `φ` move a flag to distinct flags. -/
theorem pow_ne (y : D) {a b : ℕ} (hab : a < b) (hb : b < 2 * X.nu (X.M.vtx y)) :
    (X.phi ^ a) y ≠ (X.phi ^ b) y := fun h => by
  have := four_nu_le ((X.phi ^ a) y) (q := b - a) (by omega) (by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hab.le, ← h])
  rw [vtx_phi'] at this
  omega

theorem straight_pow (hs : X.Straight) (y : D) (i : ℕ) :
    X.line ((X.phi ^ (i + X.nu (X.M.vtx y))) y) = X.line ((X.phi ^ i) y) := by
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]
  simpa using hs ((X.phi ^ i) y)

open Classical in
/-- The `ν` edge-ends met in half a turn around a vertex carry distinct lines. -/
theorem line_inj (hs : X.Straight) (y : D) {i j : ℕ} (hij : i < j)
    (hj : j < X.nu (X.M.vtx y)) : X.line ((X.phi ^ i) y) ≠ X.line ((X.phi ^ j) y) := by
  intro hl
  set ν := X.nu (X.M.vtx y)
  have hn : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].Nodup := by
    have p : ∀ {a b : ℕ}, a < b → b < 2 * ν → (X.phi ^ a) y ≠ (X.phi ^ b) y :=
      fun h h' => pow_ne y h h'
    have q := a2_ne_pow (X := X)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨p hij (by omega), p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i i y h.symm⟩, ⟨p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i j y h.symm⟩, ⟨p (by omega) (by omega), fun h => q i _ y h.symm⟩,
      fun h => q i _ y h.symm⟩
  have h4 := X.pass ((X.phi ^ i) y)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have hsub : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].toFinset ⊆ Finset.univ.filter fun e =>
        X.M.vtx e = X.M.vtx ((X.phi ^ i) y) ∧ X.line e = X.line ((X.phi ^ i) y) := by
    intro e he
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [ν, hl, X.line_a2, straight_pow hs y i, straight_pow hs y j]
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, h4] at this
  simp at this

section Parity

open Matrix

omit [Fintype D] in
theorem on_of_inc {w : X.M.Vtx} {e : X.M.Edge} (h : X.Inc w e) : X.On w (X.lineE e) := by
  obtain ⟨d, rfl, rfl⟩ := h; exact ⟨d, rfl, rfl⟩

omit [Fintype D] in
theorem meet_eq {l l' : L} (h : l ≠ l') {v w : X.M.Vtx} (hv : X.On v l) (hv' : X.On v l')
    (hw : X.On w l) (hw' : X.On w l') : v = w := by
  obtain ⟨u, -, hu⟩ := X.meet l l' h
  exact (hu v ⟨hv, hv'⟩).trans (hu w ⟨hw, hw'⟩).symm

end Parity

section Lift

/-- Two edge-ends adjacent around a vertex lie on different lines. -/
theorem line_a1_ne (hs : X.Straight) (d : D) : X.line (X.M.a1 d) ≠ X.line d := by
  classical
  obtain ⟨e, he, hl⟩ := X.two d
  have h2 : 1 < X.nu (X.M.vtx d) := Finset.one_lt_card.2 ⟨_, Finset.mem_image.2 ⟨d, by simp, rfl⟩,
    _, Finset.mem_image.2 ⟨e, by simp [he], rfl⟩, Ne.symm hl⟩
  exact fun h => line_inj hs d zero_lt_one h2 (by simpa [phi_apply, X.line_a2] using h.symm)

variable (X) in
/-- `e1, e, e2` are three consecutive sides of a face: the corner `(e1, e)` at one end of `e`
continued along `e` to the corner `(e, e2)` on the same side. These paths are the generalised
rotation system (19)–(21) of page 41. -/
def Path3 (e1 e e2 : X.M.Edge) : Prop :=
  ∃ d, X.M.edge (X.M.a1 d) = e1 ∧ X.M.edge d = e ∧ X.M.edge (X.M.a1 (X.M.a0 d)) = e2

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

variable (X X') in
/-- An isomorphism of the skeletons decomposed into lines: bijections of vertices, edges and
lines preserving incidence and the line of each edge (the arrangements of dimension `1` of
page 40). -/
structure SkelIso where
  fV : X.M.Vtx ≃ X'.M.Vtx
  fE : X.M.Edge ≃ X'.M.Edge
  fL : L ≃ L'
  inc : ∀ v e, X.Inc v e ↔ X'.Inc (fV v) (fE e)
  line : ∀ e, X'.lineE (fE e) = fL (X.lineE e)

/-- The inverse isomorphism of skeletons. -/
def SkelIso.symm (f : SkelIso X X') : SkelIso X' X where
  fV := f.fV.symm
  fE := f.fE.symm
  fL := f.fL.symm
  inc v e := by rw [f.inc]; simp
  line e := by rw [Equiv.eq_symm_apply, ← f.line]; simp

/-- A flag is determined by its vertex, its edge and the edge after it. -/
theorem dart_unique (hbf : BigonFree X.On) {y y' : D} (hv : X.M.vtx y' = X.M.vtx y)
    (he : X.M.edge y' = X.M.edge y) (h1 : X.M.edge (X.M.a1 y') = X.M.edge (X.M.a1 y)) :
    y' = y := by
  rcases (at_edge hbf).1 ⟨hv, he⟩ with h | rfl
  · exact h
  · exact (edge_a1_a2_ne hbf y h1).elim

omit [Fintype D'] in
theorem exists_dart (hbf : BigonFree X.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) (d : D) :
    ∃ d', X'.M.vtx d' = f.fV (X.M.vtx d) ∧ X'.M.edge d' = f.fE (X.M.edge d) ∧
      X'.M.edge (X'.M.a1 d') = f.fE (X.M.edge (X.M.a1 d)) ∧
      X'.M.edge (X'.M.a1 (X'.M.a0 d')) = f.fE (X.M.edge (X.M.a1 (X.M.a0 d))) := by
  obtain ⟨d', h1, h2, h3⟩ := hT _ _ _ ⟨d, rfl, rfl, rfl⟩
  refine ⟨d', ?_, h2, h1, h3⟩
  have iv := (f.inc _ _).1 (⟨d, rfl, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge d))
  have iw := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
  rw [← h2, inc_iff] at iv iw
  have hvw : f.fV (X.M.vtx d) ≠ f.fV (X.M.vtx (X.M.a0 d)) := fun h => noLoop hbf d (f.fV.injective h).symm
  by_contra hne
  have hw : X'.M.vtx d' = f.fV (X.M.vtx (X.M.a0 d)) :=
    (iw.resolve_right fun h' => hvw ((iv.resolve_left fun h => hne h.symm).trans h'.symm)).symm
  -- the edge after `d` would join both ends of `d`, on another line
  have : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge (X.M.a1 d)) := by
    rw [f.inc, ← h1, ← hw]; exact ⟨_, vtx_a1 d', rfl⟩
  exact noLoop hbf d (meet_eq (line_a1_ne hs d) (lineE_edge (X := X) (X.M.a1 d) ▸ on_of_inc this)
    ⟨_, rfl, X.line_a0 d⟩ ⟨_, vtx_a1 d, rfl⟩ ⟨d, rfl, rfl⟩)

/-- **The general theorem on maps, page 41.** An isomorphism of decomposed skeletons that
carries the three-edge face paths to face paths is induced by a morphism of the arrangements
(commuting with `a0, a1, a2`, over the given bijections). -/
theorem lift (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) :
    ∃ g : D → D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      (∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ∧ ∀ d, X'.line (g d) = f.fL (X.line d) := by
  choose g hv he h1 h3 using exists_dart hbf hs f hT
  have hv' : ∀ d, X'.M.vtx (X'.M.a0 (g d)) = f.fV (X.M.vtx (X.M.a0 d)) := fun d => by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
    rw [← he, inc_iff] at this
    exact (this.resolve_left fun h => noLoop hbf d (f.fV.injective (h.trans (hv d)))).symm
  refine ⟨g, fun d => ?_, fun d => ?_, fun d => ?_, hv, he, fun d => ?_⟩
  · exact dart_unique hbf' (by rw [hv, hv']) (by simp [he]) (by rw [h1, h3])
  · exact dart_unique hbf' (by simp [hv]) (by rw [he, h1]) (by rw [h1, X.M.a1_a1, X'.M.a1_a1, he])
  · exact ((at_edge hbf').1 (⟨by simp [hv], by simp [he]⟩ :
      X'.M.vtx (g (X.M.a2 d)) = X'.M.vtx (g d) ∧ X'.M.edge (g (X.M.a2 d)) = X'.M.edge (g d))
      ).resolve_left fun h => edge_a1_a2_ne hbf d (f.fE.injective (by rw [← h1, ← h1, h]))
  · rw [← lineE_edge, he, f.line]; rfl

/-- **Fullness reduces to face paths.** An isomorphism of decomposed skeletons of two bigon-free
arrangements comes from an isomorphism of the arrangements (a bijection of flags commuting with
`a0, a1, a2`) iff it preserves the three-edge face paths in both directions; the isomorphism is
then unique (`faithful`). -/
theorem lift_iff (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (f : SkelIso X X') :
    (∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ↔
    ∀ e1 e e2, X.Path3 e1 e e2 ↔ X'.Path3 (f.fE e1) (f.fE e) (f.fE e2) := by
  sorry

end Lift

end PseudolineMap

end Grothendieck.Folder80Maps3
