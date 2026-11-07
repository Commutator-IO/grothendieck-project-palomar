module

public import Mathlib
public import Grothendieck.Upstream.RatSmulMemIndivisible

@[expose] public section


/-!
# Folder 44, page 4: integrality of the Cartan numbers from the axioms

The modernised reading `transcripts/44/44.modern.tex` (Appendice II, page 4) takes a
pair `(P, Δ)`, `P` free abelian of finite rank, `Δ ⊆ P` finite, with three axioms:

* a) `Δ` generates `P`;
* b) `a ∈ Δ ⇒ -a ∈ Δ`, and `n a ∉ Δ` for `n ≠ ±1`, `n ∈ ℚ` (reduced);
* c) for each `a ∈ Δ` a « symmetry » `S_a` with `S_a a = -a` and `S_a Δ = Δ`.

Writing `S_α x = x - ⟨γ_α, x⟩ α` with `γ_α ∈ (P')^ℚ`, the leaf states that in fact
`γ_α ∈ P'`, i.e. the Cartan numbers `⟨γ_α, β⟩` are integers, because `α` is
indivisible in `P`, « pouvant faire partie d'un système fondamental de racines ».
This is finding `44-cartan-integrality-from-axioms` of `src/content/findings.ts`.

What is formalised.

* `cartan_int_of_indivisible`: if `α` is indivisible in a subgroup `P` of a
  `ℚ`-vector space and `x - f x • α ∈ P` for `x ∈ P`, then `f x ∈ ℤ`. The step
  « indivisible ⇒ integral » holds in this generality (no freeness, no finiteness).
* The axioms a)–c) do not give it. In `P = ℤ²`,
  `Δ = {±3e₁, ±3e₂, ±(e₁ + e₂), ±(e₁ - e₂)}` satisfies a) (`generates`), b)
  (`neg_mem`, `reduced`, and `reduced_rat` with `n ∈ ℚ` as on the page) and c) (`symmetries`, the four reflections of the Weyl
  group of type `B₂`); the symmetry of `3e₁` of the form `x ↦ x - f(x)·3e₁` is
  unique and `f(e₁ + e₂) = 2/3` (`cartan_eq_two_thirds`, `cartan_not_int`),
  while `3e₁ = 3 • e₁` is divisible in `P` (`divisible`).
* In that example `3e₁` is in no integral fundamental system containing
  `e₂ - e₁` (`not_integral_base`): the simple system `{3e₁, e₂ - e₁}` of the
  reflection group is one only with rational coefficients, since
  `e₁ + e₂ = (2/3)·3e₁ + (e₂ - e₁)`.
-/

namespace Grothendieck.Folder44

/-! ## Indivisible roots have integral Cartan numbers -/

/-- `α` is indivisible in `P`: whenever `α = m • y` with `y ∈ P`, `m` is a unit. -/
def Indivisible {V : Type*} [AddCommGroup V] (P : AddSubgroup V) (α : V) : Prop :=
  ∀ y ∈ P, ∀ m : ℤ, α = m • y → IsUnit m

/-- If `α ∈ P` is indivisible and `q • α ∈ P` for a rational `q`, then `q` is an
integer. -/
theorem int_of_smul_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    {P : AddSubgroup V} {α : V} (hα : α ∈ P) (hind : Indivisible P α) {q : ℚ}
    (hq : q • α ∈ P) : ∃ n : ℤ, q = n :=
  (AddSubgroup.rat_smul_mem_iff hα hind).1 hq

/-- **The step the leaf takes.** If `α ∈ P` is indivisible in `P` and the symmetry
`x ↦ x - f x • α` maps `P` into `P`, then every Cartan number `f x`, `x ∈ P`, is an
integer. -/
theorem cartan_int_of_indivisible {V : Type*} [AddCommGroup V] [Module ℚ V]
    {P : AddSubgroup V} {α : V} (hα : α ∈ P) (hind : Indivisible P α) (f : V → ℚ)
    (hS : ∀ x ∈ P, x - f x • α ∈ P) {x : V} (hx : x ∈ P) : ∃ n : ℤ, f x = n :=
  int_of_smul_mem hα hind (by simpa using P.sub_mem hx (hS x hx))

/-! ## The axioms a)–c) alone: a counterexample in `ℤ²` -/

/-- `Δ = {±3e₁, ±3e₂, ±(e₁ + e₂), ±(e₁ - e₂)}`. -/
def roots : Finset (ℤ × ℤ) :=
  {(3, 0), (-3, 0), (0, 3), (0, -3), (1, 1), (-1, -1), (1, -1), (-1, 1)}

/-- Axiom a): `Δ` generates `ℤ²`. -/
theorem generates : AddSubgroup.closure (roots : Set (ℤ × ℤ)) = ⊤ := by
  set H := AddSubgroup.closure (roots : Set (ℤ × ℤ))
  have mem : ∀ p ∈ roots, p ∈ H := fun p hp => AddSubgroup.subset_closure hp
  have e1 : ((1 : ℤ), (0 : ℤ)) ∈ H := by
    simpa using H.sub_mem (H.sub_mem (mem (3, 0) (by decide)) (mem (1, 1) (by decide)))
      (mem (1, -1) (by decide))
  have e2 : ((0 : ℤ), (1 : ℤ)) ∈ H := by simpa using H.sub_mem (mem (1, 1) (by decide)) e1
  exact eq_top_iff.2 fun ⟨a, b⟩ _ => by simpa using H.add_mem (H.zsmul_mem e1 a) (H.zsmul_mem e2 b)

/-- Axiom b), first half: `Δ = -Δ`. -/
theorem neg_mem : ∀ a ∈ roots, -a ∈ roots := by decide

/-- Axiom b), second half: `Δ` is reduced. -/
theorem reduced : ∀ a ∈ roots, ∀ n : ℤ, n • a ∈ roots → n = 1 ∨ n = -1 := by
  intro a ha n hn
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [roots, Prod.ext_iff] at hn <;> omega

/-- Axiom b) as the page writes it, with `n ∈ ℚ`: no root is a rational multiple
`q a`, `q ≠ ±1`, of a root `a`. -/
theorem reduced_rat : ∀ a ∈ roots, ∀ b ∈ roots, ∀ q : ℚ,
    (b.1 : ℚ) = q * a.1 ∧ (b.2 : ℚ) = q * a.2 → q = 1 ∨ q = -1 := by
  intro a ha b hb q h
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at ha hb
  obtain ⟨h1, h2⟩ := h
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only at h1 h2 <;> (try push_cast at h1 h2) <;> (try norm_num at h1 h2) <;>
    first | (left; linarith) | (right; linarith)

/-- The four reflections of the Weyl group of type `B₂`, as automorphisms of `ℤ²`:
`s₁ (x, y) = (-x, y)`, `s₂ (x, y) = (x, -y)`, `s₊ (x, y) = (-y, -x)`,
`s₋ (x, y) = (y, x)`. -/
def refl : Fin 4 → (ℤ × ℤ) ≃+ (ℤ × ℤ)
  | 0 => { toFun := fun p => (-p.1, p.2), invFun := fun p => (-p.1, p.2),
           left_inv := fun p => by simp, right_inv := fun p => by simp,
           map_add' := fun p q => by simp [add_comm] }
  | 1 => { toFun := fun p => (p.1, -p.2), invFun := fun p => (p.1, -p.2),
           left_inv := fun p => by simp, right_inv := fun p => by simp,
           map_add' := fun p q => by simp [add_comm] }
  | 2 => { toFun := fun p => (-p.2, -p.1), invFun := fun p => (-p.2, -p.1),
           left_inv := fun p => by simp, right_inv := fun p => by simp,
           map_add' := fun p q => by simp [add_comm] }
  | 3 => { toFun := fun p => (p.2, p.1), invFun := fun p => (p.2, p.1),
           left_inv := fun p => by simp, right_inv := fun p => by simp,
           map_add' := fun p q => by simp }

/-- Axiom c): for each root `a` there is an automorphism `S` of `ℤ²` with
`S a = -a` and `S Δ ⊆ Δ` (so `S Δ = Δ`, `Δ` being finite). -/
theorem symmetries : ∀ a ∈ roots, ∃ S : (ℤ × ℤ) ≃+ (ℤ × ℤ), S a = -a ∧ ∀ x ∈ roots, S x ∈ roots := by
  intro a ha
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨refl 0, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 0, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 1, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 1, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 2, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 2, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 3, by simp [refl], by simp [refl, roots]⟩
  · exact ⟨refl 3, by simp [refl], by simp [refl, roots]⟩

/-- The symmetry of `3e₁` is `x ↦ x - f(x) · 3e₁` with `f(x, y) = 2x/3`: it is the
reflection `s₁`. -/
theorem refl_zero_eq (p : ℤ × ℤ) :
    (((refl 0 p).1 : ℚ), ((refl 0 p).2 : ℚ)) = ((p.1 : ℚ) - (2 * p.1 / 3) * 3, (p.2 : ℚ)) := by
  simp [refl]; ring

/-- **Uniqueness and the Cartan number.** Let `f : ℤ² → ℚ` be additive and such that
`x ↦ x - f(x) · 3e₁` (computed in `ℚ²`) sends every root to a root. Then
`f(e₁ + e₂) = 2/3`. -/
theorem cartan_eq_two_thirds (f : ℤ × ℤ →+ ℚ)
    (hS : ∀ x ∈ roots, ∃ y ∈ roots, (x.1 : ℚ) - f x * 3 = y.1 ∧ (x.2 : ℚ) = y.2)
    (ha : f (3, 0) = 2) : f (1, 1) = 2 / 3 := by
  have h2 : f (2, 0) = 4 / 3 := by
    have : (3 : ℤ) • ((2 : ℤ), (0 : ℤ)) = (2 : ℤ) • ((3 : ℤ), (0 : ℤ)) := by decide
    have h := congrArg f this
    rw [map_zsmul, map_zsmul, ha, zsmul_eq_mul, zsmul_eq_mul] at h
    push_cast at h; linarith
  have hsum : f (1, 1) + f (1, -1) = 4 / 3 := by
    rw [← map_add]; simpa using h2
  have choice : ∀ x ∈ roots, x.2 = 1 ∨ x.2 = -1 → x.1 = 1 →
      f x = 0 ∨ f x = 2 / 3 := by
    intro x hx hx2 hx1
    obtain ⟨y, hy, h1, h2⟩ := hS x hx
    rw [hx1] at h1
    simp only [roots, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hx2 with h | h <;> rw [h] at h2 <;> norm_num at h1 h2 <;>
      first | (left; linarith) | (right; linarith)
  rcases choice (1, 1) (by decide) (by simp) rfl with h | h <;>
    rcases choice (1, -1) (by decide) (by simp) rfl with h' | h' <;>
    linarith

/-- The symmetry of the counterexample does satisfy the hypotheses of
`cartan_eq_two_thirds`: `f(x, y) = 2x/3`. -/
theorem cartan_exists :
    ∃ f : ℤ × ℤ →+ ℚ, f (3, 0) = 2 ∧
      ∀ x ∈ roots, ∃ y ∈ roots, (x.1 : ℚ) - f x * 3 = y.1 ∧ (x.2 : ℚ) = y.2 := by
  refine ⟨(AddMonoidHom.mulLeft (2 / 3 : ℚ)).comp
      ((Int.castAddHom ℚ).comp (AddMonoidHom.fst ℤ ℤ)), by norm_num, ?_⟩
  intro x hx
  refine ⟨refl 0 x, symmetries' x hx, ?_, by simp [refl]⟩
  simp [refl]; ring
where
  symmetries' : ∀ x ∈ roots, refl 0 x ∈ roots := by simp [refl, roots]

/-- The Cartan number `⟨(3e₁)^∨, e₁ + e₂⟩ = 2/3` is not an integer. -/
theorem cartan_not_int : ¬ ∃ n : ℤ, (2 / 3 : ℚ) = n := by
  rintro ⟨n, hn⟩
  have : (2 : ℤ) = 3 * n := by exact_mod_cast (by linarith : (2 : ℚ) = 3 * n)
  omega

/-- The root `3e₁` is divisible in `P = ℤ²`. -/
theorem divisible : ¬ Indivisible (⊤ : AddSubgroup (ℤ × ℤ)) (3, 0) := by
  intro h
  have := h (1, 0) trivial 3 (by decide)
  rw [Int.isUnit_iff] at this
  omega

/-- `{3e₁, e₂ - e₁}` is not an integral fundamental system:
`e₁ + e₂ = (2/3) · 3e₁ + (e₂ - e₁)` is no integral combination. -/
theorem not_integral_base :
    ¬ ∃ m n : ℤ, ((1 : ℤ), (1 : ℤ)) = m • ((3 : ℤ), (0 : ℤ)) + n • ((-1 : ℤ), (1 : ℤ)) := by
  rintro ⟨m, n, h⟩
  simp [Prod.ext_iff] at h
  omega

/-- **The three axioms do not give integrality.** There is a finite reduced `Δ`
generating `ℤ²`, with a symmetry for each root, whose (unique) symmetry of the form
`x ↦ x - f(x) a` has a non-integral Cartan number. -/
theorem axioms_not_integral :
    AddSubgroup.closure (roots : Set (ℤ × ℤ)) = ⊤ ∧
    (∀ a ∈ roots, -a ∈ roots) ∧
    (∀ a ∈ roots, ∀ b ∈ roots, ∀ q : ℚ,
      (b.1 : ℚ) = q * a.1 ∧ (b.2 : ℚ) = q * a.2 → q = 1 ∨ q = -1) ∧
    (∀ a ∈ roots, ∃ S : (ℤ × ℤ) ≃+ (ℤ × ℤ), S a = -a ∧ ∀ x ∈ roots, S x ∈ roots) ∧
    ∀ f : ℤ × ℤ →+ ℚ, f (3, 0) = 2 →
      (∀ x ∈ roots, ∃ y ∈ roots, (x.1 : ℚ) - f x * 3 = y.1 ∧ (x.2 : ℚ) = y.2) →
      ¬ ∃ n : ℤ, f (1, 1) = n :=
  ⟨generates, neg_mem, reduced_rat, symmetries, fun f ha hS =>
    cartan_eq_two_thirds f hS ha ▸ cartan_not_int⟩

end Grothendieck.Folder44
