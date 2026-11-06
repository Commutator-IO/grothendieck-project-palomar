module

public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs

public section


/-!
# Folder 43, pages 165–169: additive polynomials modulo `F − 1` and the perfection

The modernised reading `transcripts/43/43.modern.tex` gives on page 169, for a base `S` of
characteristic `p`,

> `Ext¹_{S-gr}(𝔾_a, ℤ/pℤ) ≅ Γ(S, 𝒪^{p^{-∞}})`,

the global sections of the perfection `colim(𝒪 → 𝒪 → ⋯, x ↦ xᵖ)`. This is finding
`43-ext-ga-zp-perfection`. The reading explains the perfection by the algebraic core: an
`Ext¹` class is an additive polynomial `Σ aᵢ t^{pⁱ}` modulo the image of `f ↦ fᵖ − f`, and
modulo that image every additive polynomial reduces to a single term. Proved here, over any
commutative `𝔽_p`-algebra `R` (the case `S = Spec R` affine):

* an additive polynomial `Σ aᵢ t^{pⁱ}` is a finitely supported sequence `a : ℕ →₀ R`
  (`toPoly`); `Fr` is left composition with `F`, `toPoly (Fr a) = (toPoly a)ᵖ` (`toPoly_Fr`),
  and `D = Fr − 1` is `f ↦ fᵖ − f`;
* `Φ (a) = Σ [aᵢ]ᵢ ∈ PerfectClosure R p`, `[a]ᵢ` the class of `(i, a)`, i.e. `a^{p^{-i}}`;
* `Φ_D`: `Φ` kills the image of `D`; `Φ_surjective`; `exists_single`: modulo the image of `D`,
  every `a` is a single term `[c]` at any level `M` large enough; `ker_Φ`: the kernel of `Φ` is
  exactly the image of `D`;
* `quotientEquiv`: `R{F} / (F − 1)R{F} ≃ PerfectClosure R p` as additive groups.

**What the formalisation finds.** The algebraic core of the formula holds over every affine
base, reduced or not, with no noetherian hypothesis: the kernel of `R → R^{p^{-∞}}` (elements
with some `x^{pᵏ} = 0`) is absorbed by `F − 1`. Not formalised: the lemma of pages 166–168
identifying `Ext¹_{S-gr}(G, Γ)` with primitive classes in `H¹(G, Γ)`, the invariance under
universal homeomorphisms, non-affine bases, and the representability by perfect pro-schemes.
-/

open Polynomial

namespace Grothendieck.Folder43

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The additive polynomial `Σ aᵢ t^{pⁱ}`. -/
noncomputable def toPoly (a : ℕ →₀ R) : R[X] := a.sum fun i c => C c * X ^ (p ^ i)

/-- Left composition with `F`: `Σ aᵢ t^{pⁱ} ↦ Σ aᵢᵖ t^{p^{i+1}}`. -/
noncomputable def Fr : (ℕ →₀ R) →+ (ℕ →₀ R) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp
    (Finsupp.mapRange.addMonoidHom (frobenius R p).toAddMonoidHom)

theorem Fr_single (i : ℕ) (c : R) :
    Fr R p (Finsupp.single i c) = Finsupp.single (i + 1) (c ^ p) := by
  simp [Fr, Finsupp.mapDomain_single, frobenius_def]

/-- `Fr` is `f ↦ fᵖ` on additive polynomials. -/
theorem toPoly_Fr (a : ℕ →₀ R) : toPoly R p (Fr R p a) = toPoly R p a ^ p := by
  induction a using Finsupp.induction_linear with
  | zero => simp [toPoly, zero_pow (Fact.out : p.Prime).ne_zero]
  | add f g hf hg =>
    rw [map_add]
    simp only [toPoly] at *
    rw [Finsupp.sum_add_index' (by simp) (by simp [add_mul]),
      Finsupp.sum_add_index' (by simp) (by simp [add_mul]), hf, hg, add_pow_char]
  | single i c =>
    rw [Fr_single]
    simp only [toPoly]
    rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), mul_pow, ← C_pow,
      ← pow_mul, pow_succ]

/-- `D = F − 1`, `f ↦ fᵖ − f`. -/
noncomputable def D : (ℕ →₀ R) →+ (ℕ →₀ R) := Fr R p - AddMonoidHom.id _

theorem toPoly_D (a : ℕ →₀ R) : toPoly R p (D R p a) = toPoly R p a ^ p - toPoly R p a := by
  have hadd : ∀ f g : ℕ →₀ R, toPoly R p (f + g) = toPoly R p f + toPoly R p g := fun f g =>
    Finsupp.sum_add_index' (by simp) (by simp [add_mul])
  have hsub : toPoly R p (Fr R p a - a) + toPoly R p a = toPoly R p (Fr R p a) := by
    rw [← hadd, sub_add_cancel]
  simp only [D, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
  rw [← toPoly_Fr, ← hsub, add_sub_cancel_right]

/-- `c ↦ [c]ᵢ`, the class of `(i, c)` in the perfection. -/
def mkHom (i : ℕ) : R →+ PerfectClosure R p where
  toFun c := PerfectClosure.mk R p (i, c)
  map_zero' := PerfectClosure.mk_zero_right R p i
  map_add' a b := by
    rw [PerfectClosure.mk_add_mk]
    simp only
    rw [← iterate_map_add]
    exact PerfectClosure.R.sound R p i i (a + b) _ rfl

/-- `Φ (a) = Σ [aᵢ]ᵢ`. -/
noncomputable def Φ : (ℕ →₀ R) →+ PerfectClosure R p := Finsupp.liftAddHom (mkHom R p)

theorem Φ_single (i : ℕ) (c : R) : Φ R p (Finsupp.single i c) = PerfectClosure.mk R p (i, c) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem Φ_Fr (a : ℕ →₀ R) : Φ R p (Fr R p a) = Φ R p a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single i c =>
    rw [Fr_single, Φ_single, Φ_single,
      PerfectClosure.R.sound R p 1 i c (c ^ p) (by simp [frobenius_def]), add_comm]

/-- **`Φ` kills `F − 1`.** -/
theorem Φ_D (a : ℕ →₀ R) : Φ R p (D R p a) = 0 := by
  simp [D, Φ_Fr]

theorem Φ_surjective : Function.Surjective (Φ R p) := fun x => by
  induction x using PerfectClosure.induction_on with
  | _ x => exact ⟨Finsupp.single x.1 x.2, Φ_single R p _ _⟩

/-- Going up: `[c]_N ≡ [c^{pᶻ}]_{N+z}` modulo the image of `D`. -/
theorem single_sub_single_mem (N z : ℕ) (c : R) :
    Finsupp.single N c - Finsupp.single (N + z) ((frobenius R p)^[z] c) ∈ (D R p).range := by
  induction z with
  | zero => simp
  | succ z ih =>
    have h : Finsupp.single (N + z) ((frobenius R p)^[z] c) -
        Finsupp.single (N + (z + 1)) ((frobenius R p)^[z + 1] c) ∈ (D R p).range := by
      refine ⟨-Finsupp.single (N + z) ((frobenius R p)^[z] c), ?_⟩
      simp [D, Fr_single, Function.iterate_succ_apply', frobenius_def, add_assoc]
      abel
    have := AddSubgroup.add_mem _ ih h
    simpa using this

/-- **Every additive polynomial is, modulo `F − 1`, a single term `c t^{p^M}`**, for every `M`
large enough. -/
theorem exists_single (a : ℕ →₀ R) :
    ∃ N, ∀ M ≥ N, ∃ c : R, a - Finsupp.single M c ∈ (D R p).range := by
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0, fun M _ => ⟨0, by simp⟩⟩
  | add f g hf hg =>
    obtain ⟨N₁, h₁⟩ := hf
    obtain ⟨N₂, h₂⟩ := hg
    refine ⟨max N₁ N₂, fun M hM => ?_⟩
    obtain ⟨c₁, hc₁⟩ := h₁ M (le_of_max_le_left hM)
    obtain ⟨c₂, hc₂⟩ := h₂ M (le_of_max_le_right hM)
    refine ⟨c₁ + c₂, ?_⟩
    have := AddSubgroup.add_mem _ hc₁ hc₂
    rwa [Finsupp.single_add, add_sub_add_comm]
  | single i c =>
    refine ⟨i, fun M hM => ⟨(frobenius R p)^[M - i] c, ?_⟩⟩
    have := single_sub_single_mem R p i (M - i) c
    rwa [Nat.add_sub_cancel' hM] at this

/-- **The kernel of `Φ` is the image of `F − 1`.** -/
theorem ker_Φ : (Φ R p).ker = (D R p).range := by
  refine le_antisymm (fun a ha => ?_) (fun _ ⟨b, hb⟩ => hb ▸ Φ_D R p b)
  obtain ⟨N, hN⟩ := exists_single R p a
  obtain ⟨c, hc⟩ := hN N le_rfl
  have hΦ : PerfectClosure.mk R p (N, c) = 0 := by
    obtain ⟨b, hb⟩ := hc
    have h1 := Φ_D R p b
    rw [hb, map_sub, AddMonoidHom.mem_ker.1 ha, Φ_single, zero_sub, neg_eq_zero] at h1
    exact h1
  rw [← PerfectClosure.mk_zero_right R p 0, PerfectClosure.mk_eq_iff] at hΦ
  obtain ⟨z, hz⟩ := hΦ
  simp only [zero_add, iterate_map_zero] at hz
  have h2 := single_sub_single_mem R p N z c
  rw [hz, Finsupp.single_zero, sub_zero] at h2
  have := AddSubgroup.add_mem _ hc h2
  rwa [sub_add_cancel] at this

/-- **`R{F} / (F − 1) R{F} ≅ R^{p^{-∞}}`** as additive groups. -/
noncomputable def quotientEquiv : ((ℕ →₀ R) ⧸ (D R p).range) ≃+ PerfectClosure R p :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_Φ R p).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (Φ_surjective R p))

theorem quotientEquiv_mk (a : ℕ →₀ R) : quotientEquiv R p a = Φ R p a := rfl

end Grothendieck.Folder43
