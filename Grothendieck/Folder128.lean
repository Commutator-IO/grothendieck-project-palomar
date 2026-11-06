module

public import Mathlib

@[expose] public section


/-!
# Folder 128, pages 12–13: the equivalence ideals of a rank-2 algebra over a field

The modernised reading `transcripts/128/128.modern.tex` (« Résultats auxiliaires sur les
relations d'équivalence », pages 12 to 18) defines, after Prop. 3 of N° 1 (pages 9–11), an
*equivalence ideal* of `A' ⊗_A A'`: an ideal `J` with
* (reflexivity) `J ⊂ Δ = Ker(A' ⊗_A A' → A')`,
* (symmetry) `J` stable under the exchange of the two factors,
* (transitivity) `p₁₃(J) ⊂ p₁₂(J) + p₂₃(J)` in `A' ⊗_A A' ⊗_A A'`, where
  `p₁₂(a ⊗ b) = a ⊗ b ⊗ 1`, `p₁₃(a ⊗ b) = a ⊗ 1 ⊗ b`, `p₂₃(a ⊗ b) = 1 ⊗ a ⊗ b`
  (the closed subscheme it defines in `Spec A' ×_A Spec A'` is then an equivalence relation).

Prop. 1 (i), page 12 (Grothendieck, page 12): if `A'/A ≅ A/𝔪` there are exactly two equivalence
relations on `Spec A'` over `Spec A`, the finest (`J = Δ`) and the coarsest (`J = 0`). Page 13
reduces it, through Prop. 3, Cor. 2 of N° 1, to `A = k` a field and `A'` a `k`-algebra of
rank `2`, treats `k × k` and stops after « `A' ≃ k[ε]` ».

This file proves that field case, for any field `k` (not only algebraically closed) and any
commutative `k`-algebra `A` with `finrank k A = 2` — so `k × k`, `k[ε]` and quadratic field
extensions alike, without classifying them first:
* `IsEquivalenceIdeal`: the three conditions above;
* `eq_bot_or_eq_ker`: an equivalence ideal of `A ⊗[k] A` is `0` or `Δ`;
* `isEquivalenceIdeal_bot`, `isEquivalenceIdeal_ker`: both are equivalence ideals.

The proof. For `x ∉ k`, `Δ = A · (1 ⊗ x − x ⊗ 1)` (from `1 ⊗ s − s ⊗ 1` spanning `Δ`). If `A`
is a field, a nonzero element of `J` is `a • δ` with `a` a unit, so `δ ∈ J`. Otherwise a
nonzero non-unit `e` satisfies `e² = r e`: if `r ≠ 0`, `f = e/r` is an idempotent and symmetry
gives `δ ∈ J` (the case `k × k`); if `e² = 0`, `J ⊂ k (e ⊗ e)` unless `δ ∈ J`, and `e ⊗ e`
fails transitivity, as `e ⊗ 1 ⊗ e` survives the map `a ⊗ b ⊗ c ↦ χ(b) a ⊗ c` (`χ(e) = 0`)
which kills `p₁₂(J)` and `p₂₃(J)` (the case `k[ε]`, the edition's).

Not formalised: the reduction to the field case (Prop. 3 and its Cor. 2, the artinian
reduction modulo `𝔪`), nor the passage from ideals to closed subschemes.
-/

open TensorProduct

namespace Grothendieck.Folder128

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

variable (k A) in
/-- `p₁₂ : a ⊗ b ↦ a ⊗ b ⊗ 1`. -/
noncomputable abbrev p12 : A ⊗[k] A →ₐ[k] (A ⊗[k] A) ⊗[k] A :=
  Algebra.TensorProduct.includeLeft

variable (k A) in
/-- `p₁₃ : a ⊗ b ↦ a ⊗ 1 ⊗ b`. -/
noncomputable abbrev p13 : A ⊗[k] A →ₐ[k] (A ⊗[k] A) ⊗[k] A :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft (AlgHom.id k A)

variable (k A) in
/-- `p₂₃ : a ⊗ b ↦ 1 ⊗ a ⊗ b`. -/
noncomputable abbrev p23 : A ⊗[k] A →ₐ[k] (A ⊗[k] A) ⊗[k] A :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id k A)

/-- An equivalence ideal of `A ⊗[k] A` (folder 128, page 11 and the reading's definition):
reflexive, symmetric and transitive. -/
structure IsEquivalenceIdeal (I : Ideal (A ⊗[k] A)) : Prop where
  /-- Reflexivity: `I ⊂ Δ = Ker(A ⊗ A → A)`. -/
  refl : I ≤ RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)
  /-- Symmetry: `I` is stable under `a ⊗ b ↦ b ⊗ a`. -/
  symm : ∀ t ∈ I, Algebra.TensorProduct.comm k A A t ∈ I
  /-- Transitivity: `p₁₃(I) ⊂ p₁₂(I) + p₂₃(I)`. -/
  trans : I.map (p13 k A) ≤ I.map (p12 k A) ⊔ I.map (p23 k A)

/-- Coordinates in the basis `1, x` when `x ∉ k`. -/
lemma coords (h2 : Module.finrank k A = 2) {x : A} (hx : ∀ c : k, c • (1 : A) ≠ x) :
    ∃ f₀ f₁ : A →ₗ[k] k, (∀ a, f₀ a • 1 + f₁ a • x = a) ∧ f₀ 1 = 1 ∧ f₀ x = 0 ∧ f₁ 1 = 0 ∧
      f₁ x = 1 := by
  have : Nontrivial A := Module.nontrivial_of_finrank_eq_succ h2
  have hli : LinearIndependent k ![(1 : A), x] := (LinearIndependent.pair_iff' one_ne_zero).2 hx
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  refine ⟨b.coord 0, b.coord 1, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · have := b.sum_repr a
    rwa [Fin.sum_univ_two, hb0, hb1] at this
  all_goals simp [← hb0, ← hb1]

/-- `Δ = A · (1 ⊗ x − x ⊗ 1)` for `x ∉ k`. -/
lemma exists_smul_delta (h2 : Module.finrank k A = 2) {x : A} (hx : ∀ c : k, c • (1 : A) ≠ x)
    {t : A ⊗[k] A} (ht : t ∈ RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)) :
    ∃ a : A, a • ((1 : A) ⊗ₜ[k] x - x ⊗ₜ 1) = t := by
  obtain ⟨f₀, f₁, hf, -⟩ := coords h2 hx
  have ht' : t ∈ Submodule.span A (Set.range fun s : A => (1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) := by
    rwa [KaehlerDifferential.submodule_span_range_eq_ideal]
  rw [← Submodule.mem_span_singleton (R := A)]
  refine Submodule.span_le.2 ?_ ht'
  rintro _ ⟨s, rfl⟩
  have : (1 : A) ⊗ₜ[k] s - s ⊗ₜ 1 = f₁ s • ((1 : A) ⊗ₜ[k] x - x ⊗ₜ 1) := by
    conv_lhs => rw [← hf s]
    simp only [tmul_add, add_tmul, tmul_smul, ← smul_tmul', smul_sub]
    abel
  simpa only [this, SetLike.mem_coe] using
    Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)

lemma smul_mem {I : Ideal (A ⊗[k] A)} (a : A) {t : A ⊗[k] A} (ht : t ∈ I) : a • t ∈ I := by
  rw [Algebra.smul_def]; exact I.mul_mem_left _ ht

/-- If `δ = 1 ⊗ x − x ⊗ 1 ∈ I` then `Δ ⊂ I`. -/
lemma ker_le (h2 : Module.finrank k A = 2) {x : A} (hx : ∀ c : k, c • (1 : A) ≠ x)
    {I : Ideal (A ⊗[k] A)} (hδ : (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 ∈ I) :
    RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A) ≤ I := fun t ht => by
  obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx ht
  exact smul_mem a hδ

lemma mem_of_smul_mem {I : Ideal (A ⊗[k] A)} {c : k} (hc : c ≠ 0) {t : A ⊗[k] A}
    (ht : c • t ∈ I) : t ∈ I := by
  simpa [smul_smul, inv_mul_cancel₀ hc] using Submodule.smul_of_tower_mem I c⁻¹ ht

/-- `a • δ` for `a = c + d e`, `e² = r e`. -/
lemma smul_delta {e : A} {r : k} (he : e * e = r • e) (c d : k) :
    (c • (1 : A) + d • e) • ((1 : A) ⊗ₜ[k] e - e ⊗ₜ 1) =
      c • ((1 : A) ⊗ₜ[k] e) + d • (e ⊗ₜ[k] e) - (c + d * r) • (e ⊗ₜ[k] (1 : A)) := by
  simp only [smul_sub, smul_tmul', smul_eq_mul, mul_one, add_mul, smul_mul_assoc, one_mul, he]
  simp only [add_tmul, ← smul_tmul', smul_smul]
  module

/-- The case of an idempotent `e ∉ k` (`A ≃ k × k`): symmetry. -/
lemma idem_case (h2 : Module.finrank k A = 2) {I : Ideal (A ⊗[k] A)} (hI : IsEquivalenceIdeal I)
    {e : A} (hx : ∀ c : k, c • (1 : A) ≠ e) (he : e * e = e) :
    I = ⊥ ∨ (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 ∈ I := by
  obtain ⟨f₀, f₁, hf, -⟩ := coords h2 hx
  refine or_iff_not_imp_left.2 fun hI0 => ?_
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx (hI.refl ht)
  obtain ⟨c, d, rfl⟩ : ∃ c d : k, c • 1 + d • e = a := ⟨_, _, hf a⟩
  have he' : e * e = (1 : k) • e := by rw [one_smul, he]
  rw [smul_delta he'] at ht ht0
  have key : ∀ w ∈ I, w - Algebra.TensorProduct.comm k A A w = (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 →
      (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 ∈ I := fun w hw h => h ▸ sub_mem hw (hI.symm w hw)
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by rintro rfl; simp at ht0
    refine key (e ⊗ₜ[k] e - e ⊗ₜ 1) (mem_of_smul_mem (c := d) (by simpa using hd) ?_) ?_
    · convert I.mul_mem_left (e ⊗ₜ[k] (1 : A)) ht using 1
      simp only [mul_sub, mul_add, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, he,
        one_mul, mul_one]
      module
    · simp only [map_sub, Algebra.TensorProduct.comm_tmul]; abel
  · refine key ((1 : A) ⊗ₜ[k] e - e ⊗ₜ e) (mem_of_smul_mem hc ?_) ?_
    · convert I.mul_mem_left ((1 : A) ⊗ₜ[k] (1 : A) - e ⊗ₜ 1) ht using 1
      simp only [sub_mul, mul_sub, mul_add, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
        he, one_mul, mul_one]
      module
    · simp only [map_sub, Algebra.TensorProduct.comm_tmul]; abel

/-- The case of `e ∉ k` with `e² = 0` (`A ≃ k[ε]`): transitivity. -/
lemma nil_case (h2 : Module.finrank k A = 2) {I : Ideal (A ⊗[k] A)} (hI : IsEquivalenceIdeal I)
    {e : A} (hx : ∀ c : k, c • (1 : A) ≠ e) (he : e * e = 0) :
    I = ⊥ ∨ (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 ∈ I := by
  obtain ⟨f₀, f₁, hf, h01, h0e, -, h1e⟩ := coords h2 hx
  have he' : e * e = (0 : k) • e := by rw [zero_smul, he]
  refine or_iff_not_imp_left.2 fun hI0 => by_contra fun hδ => ?_
  -- every element of `I` is a multiple of `e ⊗ e`
  have claim : ∀ t ∈ I, ∃ d : k, t = d • (e ⊗ₜ[k] e) := fun t ht => by
    obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx (hI.refl ht)
    obtain ⟨c, d, rfl⟩ : ∃ c d : k, c • 1 + d • e = a := ⟨_, _, hf a⟩
    rw [smul_delta he'] at ht ⊢
    by_cases hc : c = 0
    · exact ⟨d, by simp [hc]⟩
    have hee : e ⊗ₜ[k] e ∈ I := by
      refine mem_of_smul_mem hc ?_
      convert I.mul_mem_left (e ⊗ₜ[k] (1 : A)) ht using 1
      simp only [mul_sub, mul_add, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, he,
        one_mul, mul_one, zero_tmul, smul_zero]
      module
    refine absurd (mem_of_smul_mem hc ?_) hδ
    convert sub_mem ht (Submodule.smul_of_tower_mem I d hee) using 1
    module
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨d, rfl⟩ := claim t ht
  have hd : d ≠ 0 := by rintro rfl; simp at ht0
  have hee : e ⊗ₜ[k] e ∈ I := mem_of_smul_mem hd ht
  -- the character `χ(c + d e) = c`
  let χ : A →ₐ[k] k := AlgHom.ofLinearMap f₀ h01 fun a b => by
    obtain ⟨c, d, rfl⟩ : ∃ c d : k, c • 1 + d • e = a := ⟨_, _, hf a⟩
    obtain ⟨c', d', rfl⟩ : ∃ c d : k, c • 1 + d • e = b := ⟨_, _, hf b⟩
    simp [mul_add, he, h01, h0e, mul_comm]
  let F : A ⊗[k] A →ₐ[k] A :=
    (Algebra.TensorProduct.rid k k A).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k A) χ)
  let φ := Algebra.TensorProduct.map F (AlgHom.id k A)
  have hχe : χ e = 0 := h0e
  have hle : I.map (p12 k A) ⊔ I.map (p23 k A) ≤ RingHom.ker φ := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun t ht => ?_)
      (Ideal.map_le_iff_le_comap.2 fun t ht => ?_) <;>
    · obtain ⟨d, rfl⟩ := claim t ht
      simp [φ, F, hχe]
  have h0 : e ⊗ₜ[k] e = 0 := by
    simpa [φ, F, RingHom.mem_ker] using hle (hI.trans (Ideal.mem_map_of_mem (p13 k A) hee))
  have : e = 0 := by simpa [h1e] using congr(TensorProduct.rid k A (LinearMap.lTensor A f₁ $h0))
  exact hx 0 (by simp [this])

/-- **Folder 128, Prop. 1 (i), field case** (Grothendieck, page 12; the reduction to rank `2`
is page 13). For `A` a commutative algebra of rank `2` over a field `k`, an equivalence ideal
of `A ⊗[k] A` is `0` or the diagonal ideal `Δ = Ker(A ⊗[k] A → A)`. -/
theorem eq_bot_or_eq_ker (h2 : Module.finrank k A = 2) {I : Ideal (A ⊗[k] A)}
    (hI : IsEquivalenceIdeal I) :
    I = ⊥ ∨ I = RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A) := by
  suffices ∃ x : A, (∀ c : k, c • (1 : A) ≠ x) ∧ (I = ⊥ ∨ (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 ∈ I) by
    obtain ⟨x, hx, h | h⟩ := this
    exacts [Or.inl h, Or.inr (le_antisymm hI.refl (ker_le h2 hx h))]
  by_cases hf : ∀ a : A, a ≠ 0 → IsUnit a
  · obtain ⟨x, hx⟩ : ∃ x : A, ∀ c : k, c • (1 : A) ≠ x := by
      by_contra! h
      have := finrank_le_one (1 : A) h
      omega
    refine ⟨x, hx, or_iff_not_imp_left.2 fun hI0 => ?_⟩
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx (hI.refl ht)
    obtain ⟨u, rfl⟩ := hf a (by rintro rfl; simp at ht0)
    simpa [smul_smul] using smul_mem (↑u⁻¹ : A) ht
  obtain ⟨e, he0, heu⟩ : ∃ e : A, e ≠ 0 ∧ ¬IsUnit e := by simpa using hf
  have hx : ∀ c : k, c • (1 : A) ≠ e := by
    rintro c rfl
    have hc : c ≠ 0 := by rintro rfl; simp at he0
    exact heu (by rw [← Algebra.algebraMap_eq_smul_one]; exact (IsUnit.mk0 c hc).map _)
  obtain ⟨f₀, f₁, hf, -⟩ := coords h2 hx
  set s := f₀ (e * e)
  set r := f₁ (e * e)
  have hee : e * e = s • 1 + r • e := (hf _).symm
  have hs : s = 0 := by
    by_contra hs
    refine heu (IsUnit.of_mul_eq_one (s⁻¹ • (e - r • 1)) ?_)
    rw [mul_smul_comm, mul_sub, mul_smul_comm, mul_one, hee, add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ hs, one_smul]
  rw [hs, zero_smul, zero_add] at hee
  by_cases hr : r = 0
  · exact ⟨e, hx, nil_case h2 hI hx (by simp [hee, hr])⟩
  refine ⟨r⁻¹ • e, fun c h => hx (r * c) ?_, idem_case h2 hI (fun c h => hx (r * c) ?_) ?_⟩
  · rw [mul_smul, h, smul_smul, mul_inv_cancel₀ hr, one_smul]
  · rw [mul_smul, h, smul_smul, mul_inv_cancel₀ hr, one_smul]
  · rw [smul_mul_smul, hee, smul_smul, mul_assoc, inv_mul_cancel₀ hr, mul_one]

/-- `0` is an equivalence ideal (the coarsest relation, the whole fibre product). -/
theorem isEquivalenceIdeal_bot : IsEquivalenceIdeal (⊥ : Ideal (A ⊗[k] A)) where
  refl := bot_le
  symm t ht := by rw [Ideal.mem_bot.1 ht, map_zero]; exact zero_mem _
  trans := by rw [Ideal.map_bot]; exact bot_le

/-- `Δ` is an equivalence ideal (the finest relation, the diagonal). -/
theorem isEquivalenceIdeal_ker :
    IsEquivalenceIdeal (RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)) where
  refl := le_rfl
  symm t ht := RingHom.mem_ker.2 <| (LinearMap.mul'_comm (R := k) t).trans ht
  trans := by
    rw [show RingHom.ker _ = _ from (KaehlerDifferential.span_range_eq_ideal k A).symm,
      Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have : p13 k A ((1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) =
        p12 k A ((1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) + p23 k A ((1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) := by
      simp [sub_tmul]
    rw [this]
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)))

/-!
## Pages 14–18, Prop. 2: the colength criterion, field case

Prop. 2 (pages 14–18): `A` local artinian, `A'` finite over `A` with trivial residue extensions,
`J` an equivalence ideal with `A → A' ⇉ A'' = (A' ⊗_A A')/J` exact and `δ(x') = p₂(x') − p₁(x')`
generating `Δ/J` for every `x' ∉ A`; then `A'/A` has length `≤ 1`, and `A'' = A' ⊗_A A'` when it
is `1`. Here `A = k` is a field (the case both branches of the page reduce to) and `A` below is
the reading's `A'`:
* `Colength.finrank_le_two`: `dim_k A ≤ 2`, for any ideal `J ⊂ Δ` (neither symmetry nor
  transitivity is used);
* `Colength.eq_bot_of_finrank_eq_two`, `Colength.prop2`: if `dim_k A = 2`, `J = 0`.

The proof differs from the page's (radiciel / non radiciel, `A' ≃ kⁿ` or `k ⊕ V`): for a point
`χ : A → k` with ideal `𝔪_χ`, `φ_χ : a ⊗ b ↦ χ(a) b` sends `δ(x)` to `x − χ(x)`, so the hypothesis
gives `𝔪_χ ⊂ A z + φ_χ(J)` for every `0 ≠ z ∈ 𝔪_χ`. Either `φ_χ(J) = 0` for some `χ`, and then
`𝔪_χ` is a simple module, of dimension `1` (residue fields are `k`); or `𝔪_χ ⊂ φ_χ(J)` for all `χ`,
and since `f ≡ δ(φ_χ f)` modulo `𝔪_χ Δ`, `Δ ⊂ J + 𝔪 Δ` for every maximal `𝔪`, so `Δ ⊂ J` by
Nakayama and exactness gives `A = k`.

Not formalised: the reduction from `A` local artinian to `A = k` (`𝔪A' = 𝔪`, through Prop. 3 and
Cor. 2 of N° 1), and the passage from ideals to subschemes.
-/

namespace Colength

open Module

variable (k A) in
/-- `δ(x) = p₂(x) − p₁(x) = 1 ⊗ x − x ⊗ 1`, as a `k`-linear map. -/
noncomputable def delta : A →ₗ[k] A ⊗[k] A :=
  TensorProduct.mk k A A 1 - (TensorProduct.mk k A A).flip 1

lemma delta_apply (x : A) : delta k A x = (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 := rfl

variable (k A) in
/-- The augmentation ideal `Δ = Ker(A ⊗ A → A)`. -/
noncomputable abbrev diag : Ideal (A ⊗[k] A) :=
  RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)

lemma delta_mem (x : A) : delta k A x ∈ diag k A := by
  simp [delta_apply, RingHom.mem_ker]

lemma delta_algebraMap (c : k) : delta k A (algebraMap k A c) = 0 := by
  simp [delta_apply, Algebra.algebraMap_eq_smul_one]

/-- `φ_χ : a ⊗ b ↦ χ(a) b`, restriction of the first factor to the point `χ`. -/
noncomputable def phi (χ : A →ₐ[k] k) : A ⊗[k] A →ₐ[k] A :=
  (Algebra.TensorProduct.lid k A).toAlgHom.comp (Algebra.TensorProduct.map χ (AlgHom.id k A))

lemma phi_tmul (χ : A →ₐ[k] k) (a b : A) : phi χ (a ⊗ₜ b) = χ a • b := by simp [phi]

lemma phi_delta (χ : A →ₐ[k] k) (x : A) :
    phi χ (delta k A x) = x - algebraMap k A (χ x) := by
  simp [delta_apply, phi_tmul, Algebra.algebraMap_eq_smul_one]

lemma phi_smul (χ : A →ₐ[k] k) (a : A) (t : A ⊗[k] A) : phi χ (a • t) = χ a • phi χ t := by
  rw [Algebra.smul_def, map_mul, show algebraMap A (A ⊗[k] A) a = a ⊗ₜ 1 from rfl, phi_tmul,
    smul_mul_assoc, one_mul]

lemma chi_phi (χ : A →ₐ[k] k) (t : A ⊗[k] A) : χ (phi χ t) = χ (Algebra.TensorProduct.lmul' k t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [phi_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

lemma mem_span_delta {t : A ⊗[k] A} (ht : t ∈ diag k A) :
    t ∈ Submodule.span A (Set.range (delta k A)) := by
  rwa [show Set.range (delta k A) = Set.range fun s : A => (1 : A) ⊗ₜ[k] s - s ⊗ₜ 1 from rfl,
    KaehlerDifferential.submodule_span_range_eq_ideal]

/-- `f ≡ δ(φ_χ f)` modulo `𝔪_χ · Δ`, for `f ∈ Δ`. -/
lemma sub_delta_phi_mem (χ : A →ₐ[k] k) {f : A ⊗[k] A} (hf : f ∈ diag k A) :
    f - delta k A (phi χ f) ∈ RingHom.ker χ • (diag k A).restrictScalars A := by
  suffices ∀ t ∈ Submodule.span A (Set.range (delta k A)),
      t - delta k A (phi χ t) ∈ RingHom.ker χ • (diag k A).restrictScalars A from
    this f (mem_span_delta hf)
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    simp [phi_delta, delta_algebraMap]
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1; simp only [map_add]; abel
  | smul a x hx' hx =>
    have hxD : x ∈ (diag k A).restrictScalars A := by
      rw [← KaehlerDifferential.submodule_span_range_eq_ideal]; exact hx'
    have h1 : (a - algebraMap k A (χ a)) • x ∈ RingHom.ker χ • (diag k A).restrictScalars A :=
      Submodule.smul_mem_smul (by simp [RingHom.mem_ker]) hxD
    convert add_mem h1 (Submodule.smul_of_tower_mem _ (χ a) hx) using 1
    rw [phi_smul, map_smul, sub_smul, algebraMap_smul, smul_sub]
    abel

/-- Nakayama at every maximal ideal: if `N ⊂ N' + 𝔪 N` for every maximal `𝔪`, then `N ⊂ N'`. -/
lemma le_of_forall_le_sup_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} (hN : N.FG) (h : ∀ m : Ideal R, m.IsMaximal → N ≤ N' ⊔ m • N) :
    N ≤ N' := by
  suffices N'.colon N = ⊤ by
    intro n hn
    have := Submodule.mem_colon.1 (this ▸ Submodule.mem_top (x := (1 : R))) n hn
    rwa [one_smul] at this
  by_contra hC
  obtain ⟨m, hm, hCm⟩ := Ideal.exists_le_maximal _ hC
  have hle : N.map N'.mkQ ≤ m • N.map N'.mkQ := by
    rw [← Submodule.map_smul'']
    calc N.map N'.mkQ ≤ (N' ⊔ m • N).map N'.mkQ := Submodule.map_mono (h m hm)
      _ = _ := by rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _ (hN.map _) hle
  have hrC : r ∈ N'.colon N := Submodule.mem_colon.2 fun n hn => by
    have := hr0 _ (Submodule.mem_map_of_mem hn)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (hCm hrC) hr))

/-- If a nonzero `z ∈ 𝔪_χ` generates the ideal `𝔪_χ` whatever it is, `A = k ⊕ 𝔪_χ` with
`𝔪_χ` simple, hence of dimension `≤ 1`: the case where `J` does not meet the fibre of `χ`. -/
lemma finrank_le_two_of_simple [Module.Finite k A]
    (hres : ∀ m : Ideal A, m.IsMaximal → ∃ χ : A →ₐ[k] k, RingHom.ker χ = m) (χ : A →ₐ[k] k)
    (h : ∀ z ∈ RingHom.ker χ, z ≠ 0 → ∀ y ∈ RingHom.ker χ, y ∈ Ideal.span {z}) :
    finrank k A ≤ 2 := by
  have hsplit : ∀ (ψ : A →ₐ[k] k) (a : A), a - algebraMap k A (ψ a) ∈ RingHom.ker ψ :=
    fun ψ a => by simp [RingHom.mem_ker]
  by_cases hm : ∀ z ∈ RingHom.ker χ, z = 0
  · refine (finrank_le_one (1 : A) fun a => ⟨χ a, ?_⟩).trans (by norm_num)
    rw [← Algebra.algebraMap_eq_smul_one, ← sub_eq_zero, ← neg_sub, hm _ (hsplit χ a), neg_zero]
  push Not at hm
  obtain ⟨z, hz, hz0⟩ := hm
  obtain ⟨n, hn, hIn⟩ := Ideal.exists_le_maximal (LinearMap.ker (LinearMap.toSpanSingleton A A z))
    (by rw [Ne, Submodule.eq_top_iff']; push Not; exact ⟨1, by simpa using hz0⟩)
  obtain ⟨χ', rfl⟩ := hres n hn
  -- `𝔪_{χ'}` kills `z`
  have hkill : ∀ w ∈ RingHom.ker χ', w * z = 0 := fun w hw => by
    by_contra hwz
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1
      (h (w * z) (Ideal.mul_mem_left _ w hz) hwz z hz)
    have : 1 - b * w ∈ RingHom.ker χ' := hIn (by
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      rw [sub_mul, one_mul, mul_assoc, hb, sub_self])
    exact hn.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa using add_mem this (Ideal.mul_mem_left _ b hw)))
  -- so `𝔪_χ = k z`, and `(c, d) ↦ c + d z` is onto
  let f : k × k →ₗ[k] A := (LinearMap.toSpanSingleton k A 1).coprod (LinearMap.toSpanSingleton k A z)
  have hf : Function.Surjective f := fun a => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h z hz hz0 _ (hsplit χ a))
    refine ⟨(χ a, χ' b), ?_⟩
    have e : b * z = χ' b • z := by
      rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul]; exact hkill _ (hsplit χ' b)
    simp only [f, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, ← e, hb,
      ← Algebra.algebraMap_eq_smul_one, add_sub_cancel]
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top, Module.finrank_prod, Module.finrank_self] at this

/-- For `0 ≠ z ∈ 𝔪_χ` and `y ∈ 𝔪_χ`, the hypothesis `Δ ⊂ (δ z) + J` read through `φ_χ`. -/
lemma phi_decomp {J : Ideal (A ⊗[k] A)}
    (hgen : ∀ x : A, x ∉ Set.range (algebraMap k A) → diag k A ≤ Ideal.span {delta k A x} ⊔ J)
    (χ : A →ₐ[k] k) {z : A} (hz : z ∈ RingHom.ker χ) (hz0 : z ≠ 0) {y : A}
    (hy : y ∈ RingHom.ker χ) : ∃ u : A ⊗[k] A, ∃ j ∈ J, phi χ u * z + phi χ j = y := by
  have hzk : z ∉ Set.range (algebraMap k A) := by
    rintro ⟨c, rfl⟩
    exact hz0 (by simp [(by simpa [RingHom.mem_ker] using hz : c = 0)])
  obtain ⟨u, j, hj, e⟩ := Ideal.mem_span_singleton_sup.1 (hgen z hzk (delta_mem y))
  refine ⟨u, j, hj, ?_⟩
  have := congr(phi χ $e)
  rw [map_add, map_mul, phi_delta, phi_delta, (RingHom.mem_ker).1 hz,
    (RingHom.mem_ker).1 hy] at this
  simpa using this

/-- **Folder 128, Prop. 2, field case** (Grothendieck, pages 14–18). Let `A` be a finite
commutative algebra over a field `k` whose residue fields are all `k` (every maximal ideal is the
kernel of a `k`-point), and `J ⊂ Δ` an ideal of `A ⊗[k] A` such that
* (exactness of `k → A ⇉ (A ⊗ A)/J`) `δ(x) ∈ J` only for `x ∈ k`;
* (`δ(x)` generates `Δ/J` in `(A ⊗ A)/J`) `Δ ⊂ (δ(x)) + J` for every `x ∉ k`.
Then `dim_k A ≤ 2`, i.e. `A/k` has length `≤ 1`. Neither symmetry nor transitivity of `J` is
used, and there is no case split radiciel / non radiciel. -/
theorem finrank_le_two [Module.Finite k A]
    (hres : ∀ m : Ideal A, m.IsMaximal → ∃ χ : A →ₐ[k] k, RingHom.ker χ = m)
    {J : Ideal (A ⊗[k] A)} (hJ : J ≤ diag k A)
    (hexact : ∀ x : A, delta k A x ∈ J → x ∈ Set.range (algebraMap k A))
    (hgen : ∀ x : A, x ∉ Set.range (algebraMap k A) → diag k A ≤ Ideal.span {delta k A x} ⊔ J) :
    finrank k A ≤ 2 := by
  by_contra hlt
  -- at each point `χ`, either `J` misses the fibre (then `dim A ≤ 2`) or `𝔪_χ ⊂ φ_χ(J)`
  have hfib : ∀ χ : A →ₐ[k] k, ∀ y ∈ RingHom.ker χ, ∃ f ∈ J, phi χ f = y := by
    intro χ
    by_cases hK : ∃ f ∈ J, phi χ f ≠ 0
    · obtain ⟨f, hf, hf0⟩ := hK
      have hfm : phi χ f ∈ RingHom.ker χ := by
        rw [RingHom.mem_ker, chi_phi, (RingHom.mem_ker).1 (hJ hf), map_zero]
      intro y hy
      obtain ⟨u, j, hj, e⟩ := phi_decomp hgen χ hfm hf0 hy
      exact ⟨u * f + j, J.add_mem (J.mul_mem_left u hf) hj, by rw [map_add, map_mul, e]⟩
    · push Not at hK
      refine absurd (finrank_le_two_of_simple hres χ fun z hz hz0 y hy => ?_) hlt
      obtain ⟨u, j, hj, e⟩ := phi_decomp hgen χ hz hz0 hy
      rw [hK j hj, add_zero] at e
      exact Ideal.mem_span_singleton'.2 ⟨_, e⟩
  -- hence `Δ ⊂ J + 𝔪 Δ` for every maximal `𝔪`, and `Δ ⊂ J` by Nakayama
  have hD : (diag k A).restrictScalars A ≤ J.restrictScalars A := by
    have : IsNoetherian A (A ⊗[k] A) := isNoetherian_of_tower k inferInstance
    refine le_of_forall_le_sup_smul (IsNoetherian.noetherian _) fun m hm => ?_
    obtain ⟨χ, rfl⟩ := hres m hm
    intro t ht
    rw [← KaehlerDifferential.submodule_span_range_eq_ideal] at ht
    refine (Submodule.span_le.2 ?_) ht
    rintro _ ⟨x, rfl⟩
    obtain ⟨f, hf, e⟩ := hfib χ _ (show x - algebraMap k A (χ x) ∈ RingHom.ker χ by
      simp [RingHom.mem_ker])
    have : (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 = f - (f - delta k A (phi χ f)) := by
      rw [sub_sub_cancel, e, map_sub, delta_algebraMap, sub_zero, delta_apply]
    change (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 ∈ _
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hf) (Submodule.mem_sup_right (sub_delta_phi_mem χ (hJ hf)))
  -- exactness: `δ(x) ∈ Δ ⊂ J` forces `x ∈ k`, so `dim A ≤ 1`
  refine hlt ((finrank_le_one (1 : A) fun a => ?_).trans (by norm_num))
  obtain ⟨c, hc⟩ := hexact a (hD (delta_mem a))
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

/-- Prop. 2, last assertion: if `A/k` has length `1`, an exact equivalence ideal is `0`, so
`(A ⊗ A)/J = A ⊗ A` (by `eq_bot_or_eq_ker`, `J = Δ` contradicting exactness). -/
theorem eq_bot_of_finrank_eq_two (h2 : finrank k A = 2) {J : Ideal (A ⊗[k] A)}
    (hJ : IsEquivalenceIdeal J)
    (hexact : ∀ x : A, delta k A x ∈ J → x ∈ Set.range (algebraMap k A)) : J = ⊥ := by
  refine (eq_bot_or_eq_ker h2 hJ).resolve_right fun hJD => ?_
  obtain ⟨x, hx⟩ : ∃ x : A, ∀ c : k, c • (1 : A) ≠ x := by
    by_contra! h
    have := finrank_le_one (1 : A) h
    omega
  obtain ⟨c, hc⟩ := hexact x (hJD ▸ delta_mem x)
  exact hx c (by rw [← hc, Algebra.algebraMap_eq_smul_one])

/-- **Folder 128, Prop. 2, field case, as stated** (pages 14–18): for an equivalence ideal `J`
of `A ⊗[k] A` with `k → A ⇉ (A ⊗ A)/J` exact and `δ(x)` generating `Δ/J` for every `x ∉ k`,
`A/k` has length `≤ 1`, and if it is `1` then `J = 0`. -/
theorem prop2 [Module.Finite k A]
    (hres : ∀ m : Ideal A, m.IsMaximal → ∃ χ : A →ₐ[k] k, RingHom.ker χ = m)
    {J : Ideal (A ⊗[k] A)} (hJ : IsEquivalenceIdeal J)
    (hexact : ∀ x : A, delta k A x ∈ J → x ∈ Set.range (algebraMap k A))
    (hgen : ∀ x : A, x ∉ Set.range (algebraMap k A) → diag k A ≤ Ideal.span {delta k A x} ⊔ J) :
    finrank k A ≤ 2 ∧ (finrank k A = 2 → J = ⊥) :=
  ⟨finrank_le_two hres hJ.refl hexact hgen, fun h2 => eq_bot_of_finrank_eq_two h2 hJ hexact⟩

end Colength

end Grothendieck.Folder128


/-!
## Pages 4–9: effective descent along a nilpotent conductor

The reading (« Descente effective le long d'un conducteur nilpotent », Prop. 2 and Cor. 1):
`A → S` a ring map (the page's `A → A'`), `I` an ideal of `A` mapped injectively onto an ideal
of `S` (`IsConductorIdeal`: `I` lies in the conductor, and `A = S ×_{S/IS} A/I` is a Milnor
square), `I` nilpotent. Descent data are written as comodules over the coring `S ⊗_A S`
(`DescentDatum`: an `S`-linear `ψ : E → S ⊗_A E`, `ψ(e) = φ(1 ⊗ e)` for the gluing `φ`, with
counit and cocycle conditions); `DescentDatum.invariants` is `H⁰`, `DescentDatum.IsEffective`
says the invariants are flat and `S ⊗_A E^ψ → E` is bijective, `DescentDatum.reduce` is the
datum induced on `E₀ = S/IS ⊗_S E` relative to `A/I → S/IS`, and `IsEffectiveDescentFlat`
is « morphisme de descente effective pour les modules plats » (`IsDescentFlat`: `M ≅ H⁰` for
`M` flat, plus every datum on a flat `S`-module effective).

* `flat_of_isNilpotent`: the local flatness criterion for a nilpotent ideal, which the page uses
  unnamed (`M/IM` flat over `A/I` and `I ⊗ M → M` injective ⇒ `M` flat), with no Noetherian
  hypothesis;
* `DescentDatum.isEffective_of_reduce` (Prop. 2): a datum on a flat `S`-module whose reduction
  modulo `I` is effective is effective;
* `isEffectiveDescentFlat_of_quotient` (Cor. 1): if `Spec S/IS → Spec A/I` is an effective
  descent morphism for flat modules, so is `Spec S → Spec A`.

The proof is not the page's induction on the nilpotency order, nor its long exact sequence.
(1) `e` is invariant iff its reduction is (`mem_invariants_iff`): if `ψ(e) − 1 ⊗ e` lies in
`IS · (S ⊗ E)`, it is `1 ⊗ y` with `y ∈ I E` (`I` is an ideal of `S`), and the counit gives
`y = 0`; this is page 5's computation, which needs neither `I² = 0` nor flatness. So
`E^ψ → E₀^{ψ₀}` is onto with kernel `I E`. (2) Hence `E = S · E^ψ + I E`, and `E^ψ` spans `E`
by Nakayama for the nilpotent `IS` (`span_invariants_eq_top`). (3) `S ⊗_A E^ψ → E` is
injective: an element of its kernel reduces to `0`, so lies in `IS · (S ⊗ E^ψ) = 1 ⊗ I E^ψ`,
where the map is injective. (4) `E^ψ / I E^ψ ≅ E₀^{ψ₀}` is flat over `A/I`, and
`I ⊗_A E^ψ ≅ I ⊗_S E → E` is injective since `E` is flat over `S` — the only use of the
flatness of `E`; the local criterion concludes. Neither `A ≅ H⁰(S/A)` nor `H¹(S/A) = 0` is used.

Not formalised: Cor. 2 and Cor. 3 (preschemes, and the stability under flat base change), and
the example « `S/IS` faithfully flat over `A/I` », since mathlib has faithfully flat descent of
modules only as comonadicity; Cor. 1 is proved with its hypothesis as stated.
-/

namespace Grothendieck.Folder128.Descent

universe u

section LocalCriterion

variable {A : Type*} [CommRing A] (I : Ideal A) {M : Type*} [AddCommGroup M] [Module A M]

variable (G : Type*) [AddCommGroup G] [Module A G]

/-- `I ⊗ G → G`, `λ ⊗ g ↦ λ g`. -/
noncomputable def smulMap : I ⊗[A] G →ₗ[A] G :=
  TensorProduct.lift ((LinearMap.lsmul A G).comp I.subtype)

@[simp] lemma smulMap_tmul (r : I) (g : G) : smulMap I G (r ⊗ₜ g) = (r : A) • g := rfl

lemma range_smulMap : LinearMap.range (smulMap I G) = I • (⊤ : Submodule A G) := by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun r hr g _ => ⟨⟨r, hr⟩ ⊗ₜ g, rfl⟩)
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul r g => exact Submodule.smul_mem_smul r.2 trivial
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

variable {I G}

/-- For `G` flat and `I ⊗ M → M` injective, `(I ⊗ G) ⊗ M → G ⊗ M` is injective. -/
lemma rTensor_smulMap_injective [Module.Flat A G]
    (h1 : Function.Injective (I.subtype.rTensor M)) :
    Function.Injective ((smulMap I G).rTensor M) := by
  have hμ : Function.Injective ((TensorProduct.lid A M).toLinearMap ∘ₗ I.subtype.rTensor M) := by
    rw [LinearMap.coe_comp]; exact (TensorProduct.lid A M).injective.comp h1
  have e : (smulMap I G).rTensor M = ((TensorProduct.lid A M).toLinearMap ∘ₗ I.subtype.rTensor M).lTensor G ∘ₗ
      (TensorProduct.assoc A G I M).toLinearMap ∘ₗ
        (TensorProduct.comm A I G).toLinearMap.rTensor M := by
    refine TensorProduct.ext_threefold fun r g m => ?_
    simp [TensorProduct.smul_tmul]
  rw [e]
  refine (Module.Flat.lTensor_preserves_injective_linearMap _ hμ).comp
    ((TensorProduct.assoc A G I M).injective.comp ?_)
  rw [← LinearEquiv.coe_rTensor]
  exact (LinearEquiv.rTensor M (TensorProduct.comm A I G)).injective

/-- Tensoring with `M` an injective map of `A/I`-modules stays injective when `M/IM` is flat
over `A/I`. -/
lemma rTensor_injective_of_quotient (h0 : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    {X Y : Type*} [AddCommGroup X] [Module (A ⧸ I) X] [Module A X] [IsScalarTower A (A ⧸ I) X]
    [AddCommGroup Y] [Module (A ⧸ I) Y] [Module A Y] [IsScalarTower A (A ⧸ I) Y]
    (v : X →ₗ[A ⧸ I] Y) (hv : Function.Injective v) :
    Function.Injective ((v.restrictScalars A).rTensor M) := by
  let cX := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) X M
  let cY := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) Y M
  have e : ((v.restrictScalars A).rTensor M) =
      (cY.toLinearMap.restrictScalars A) ∘ₗ (v.rTensor ((A ⧸ I) ⊗[A] M)).restrictScalars A ∘ₗ
        (cX.symm.toLinearMap.restrictScalars A) := by
    refine TensorProduct.ext' fun x m => ?_
    simp [cX, cY]
  rw [e]
  exact cY.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _ hv).comp
    cX.symm.injective)

/-- `Tor₁(G/L, M) = 0` for `G` flat and `I G ⊂ L ⊂ G`: `L ⊗ M → G ⊗ M` is injective. -/
lemma rTensor_subtype_injective_of_flat [Module.Flat A G]
    (h0 : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    (h1 : Function.Injective (I.subtype.rTensor M)) (L : Submodule A G)
    (hIL : I • (⊤ : Submodule A G) ≤ L) :
    Function.Injective (L.subtype.rTensor M) := by
  -- the image `L̄` of `L` in `G / I G`, an `A/I`-submodule
  let Lb : Submodule (A ⧸ I) (G ⧸ (I • ⊤ : Submodule A G)) :=
    { carrier := (I • ⊤ : Submodule A G).mkQ '' L
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, L.add_mem hx hy, map_add _ _ _⟩
      zero_mem' := ⟨0, L.zero_mem, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨c • x, L.smul_mem c hx, (Module.Quotient.mk_smul_mk G I c x).symm⟩ }
  let r : L →ₗ[A] Lb :=
    { toFun := fun x => ⟨(I • ⊤ : Submodule A G).mkQ x, x, x.2, rfl⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul _ c (x : G)) }
  have hr : Function.Surjective r := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hrange : ∀ t, smulMap I G t ∈ L := fun t =>
    hIL (by rw [← range_smulMap]; exact ⟨t, rfl⟩)
  let φL : I ⊗[A] G →ₗ[A] L := (smulMap I G).codRestrict L hrange
  have hex : Function.Exact φL r := by
    intro y
    constructor
    · intro hy
      have : ((y : G) : G) ∈ (I • ⊤ : Submodule A G) := by
        have := congr_arg Subtype.val hy
        simpa [r, Submodule.Quotient.mk_eq_zero] using this
      rw [← range_smulMap] at this
      obtain ⟨t, ht⟩ := this
      exact ⟨t, Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      refine Subtype.ext ?_
      simp only [r, φL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.codRestrict_apply,
        Submodule.mkQ_apply, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero]
      rw [← range_smulMap]; exact ⟨t, rfl⟩
  have hcomp : (Lb.subtype.restrictScalars A) ∘ₗ r = (I • ⊤ : Submodule A G).mkQ ∘ₗ L.subtype := rfl
  have hφ : L.subtype ∘ₗ φL = smulMap I G := rfl
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hry : r.rTensor M y = 0 := by
    apply rTensor_injective_of_quotient h0 Lb.subtype (Submodule.injective_subtype _)
    rw [map_zero, ← LinearMap.rTensor_comp_apply, hcomp, LinearMap.rTensor_comp_apply, hy,
      map_zero]
  obtain ⟨z, rfl⟩ := (rTensor_exact M hex hr y).1 hry
  obtain rfl : z = 0 := by
    apply rTensor_smulMap_injective h1
    rw [map_zero, ← hφ, LinearMap.rTensor_comp_apply, hy]
  rw [map_zero]

/-- `Tor₁(F/K, M) = 0` whenever `I F ⊂ K`: for `u : K → F` injective with `I F ⊂ u(K)`,
`K ⊗ M → F ⊗ M` is injective (reduction to a free module mapping onto `F`). -/
lemma rTensor_injective_of_smul_le (h0 : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    (h1 : Function.Injective (I.subtype.rTensor M)) {K F : Type*} [AddCommGroup K] [Module A K]
    [AddCommGroup F] [Module A F] (u : K →ₗ[A] F) (hu : Function.Injective u)
    (hIu : I • (⊤ : Submodule A F) ≤ LinearMap.range u) :
    Function.Injective (u.rTensor M) := by
  let p : (F →₀ A) →ₗ[A] F := Finsupp.linearCombination A id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective A F
  let L : Submodule A (F →₀ A) := (LinearMap.range u).comap p
  have hIL : I • (⊤ : Submodule A (F →₀ A)) ≤ L :=
    Submodule.smul_le.2 fun c hc g _ => by
      show p (c • g) ∈ LinearMap.range u
      rw [map_smul]; exact hIu (Submodule.smul_mem_smul hc trivial)
  let e := LinearEquiv.ofInjective u hu
  let q : L →ₗ[A] K := e.symm.toLinearMap ∘ₗ p.restrict (p := L) (q := LinearMap.range u) fun (x : F →₀ A) (h : x ∈ L) => h
  have huq : u ∘ₗ q = p ∘ₗ L.subtype := by
    ext x
    simp only [q, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    exact congr_arg Subtype.val (e.apply_symm_apply _)
  have hq : Function.Surjective q := by
    intro k
    obtain ⟨g, hg⟩ := hp (u k)
    refine ⟨⟨g, ⟨k, hg.symm⟩⟩, hu ?_⟩
    rw [← LinearMap.comp_apply, huq]; exact hg
  have hker : LinearMap.ker p ≤ L := fun g hg => by
    show p g ∈ LinearMap.range u
    simp [LinearMap.mem_ker.1 hg]
  let ι := Submodule.inclusion hker
  have hqι : q ∘ₗ ι = 0 := by
    ext x
    apply hu
    rw [← LinearMap.comp_apply u, ← LinearMap.comp_assoc, huq]
    simp [ι, LinearMap.mem_ker.1 x.2]
  have hLinj := rTensor_subtype_injective_of_flat h0 h1 L hIL
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective M hq x
  have h2 : p.rTensor M (L.subtype.rTensor M y) = 0 := by
    rw [← LinearMap.rTensor_comp_apply, ← huq, LinearMap.rTensor_comp_apply, hx]
  have hex2 := rTensor_exact (M := LinearMap.ker p) (N := F →₀ A) (P := F)
    (f := (LinearMap.ker p).subtype) (g := p) M (LinearMap.exact_subtype_ker_map p) hp
  obtain ⟨w, hw⟩ := (hex2 _).1 h2
  have : y = ι.rTensor M w := by
    apply hLinj
    rw [← hw, ← LinearMap.rTensor_comp_apply]
    rfl
  rw [this, ← LinearMap.rTensor_comp_apply, hqι, LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- **Local flatness criterion for a nilpotent ideal** (no Noetherian hypothesis). If `I` is
nilpotent, `M/IM` is flat over `A/I` and `I ⊗ M → M` is injective, then `M` is flat. -/
theorem flat_of_isNilpotent (hI : IsNilpotent I)
    (h0 : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    (h1 : Function.Injective (I.subtype.rTensor M)) : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  have key : ∀ k : ℕ, Function.Injective ((J ⊔ I ^ k).subtype.rTensor M) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      have : (⊤ : Ideal A).subtype = (Submodule.topEquiv : (⊤ : Ideal A) ≃ₗ[A] A).toLinearMap :=
        rfl
      rw [this, ← LinearEquiv.coe_rTensor]
      exact (LinearEquiv.rTensor M _).injective
    | succ k ih =>
      have hle : J ⊔ I ^ (k + 1) ≤ J ⊔ I ^ k := sup_le_sup_left (Ideal.pow_le_pow_right k.le_succ) _
      have : (J ⊔ I ^ (k + 1)).subtype = (J ⊔ I ^ k).subtype ∘ₗ Submodule.inclusion hle := rfl
      rw [this, LinearMap.rTensor_comp]
      refine ih.comp (rTensor_injective_of_smul_le h0 h1 _ (Submodule.inclusion_injective hle) ?_)
      refine Submodule.smul_le.2 fun c hc x _ => ⟨⟨c * x, ?_⟩, Subtype.ext rfl⟩
      have hx : c * (x : A) ∈ I * (J ⊔ I ^ k) := Ideal.mul_mem_mul hc x.2
      rw [Ideal.mul_sup, ← pow_succ'] at hx
      exact (sup_le_sup_right (Ideal.mul_le.2 fun a _ b hb => J.mul_mem_left a hb) _ : I * J ⊔ I ^ (k + 1) ≤ J ⊔ I ^ (k + 1)) hx
  obtain ⟨n, hn⟩ := hI
  have := key n
  rwa [hn, Ideal.zero_eq_bot, sup_bot_eq] at this

end LocalCriterion

section Defs

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A descent datum on an `S`-module `E` relative to `R → S` (Grothendieck, page 4), written as
a comodule over the coring `S ⊗_R S`: an `S`-linear `ψ : E → S ⊗_R E` (`ψ(e) = φ(1 ⊗ e)` for
the gluing isomorphism `φ`), with counit `Σ bᵢ eᵢ = e` and the cocycle condition. -/
structure DescentDatum (E : Type u) [AddCommGroup E] [Module S E] [Module R E]
    [IsScalarTower R S E] where
  /-- The coaction `e ↦ Σ bᵢ ⊗ eᵢ`. -/
  ψ : E →ₗ[S] S ⊗[R] E
  /-- Counit: `Σ bᵢ eᵢ = e`. -/
  counit : ∀ e, LinearMap.liftBaseChange S (LinearMap.id : E →ₗ[R] E) (ψ e) = e
  /-- Cocycle: `Σ bᵢ ⊗ ψ(eᵢ) = Σ bᵢ ⊗ 1 ⊗ eᵢ`. -/
  coassoc : ∀ e, (ψ.restrictScalars R).lTensor S (ψ e) =
    (TensorProduct.mk R S E 1).lTensor S (ψ e)

variable {R S}

namespace DescentDatum

variable {E : Type u} [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]

/-- The invariants `{e | ψ(e) = 1 ⊗ e}` (the `H⁰` of the descent complex). -/
def invariants (d : DescentDatum R S E) : Submodule R E :=
  LinearMap.eqLocus (d.ψ.restrictScalars R) (TensorProduct.mk R S E 1)

lemma mem_invariants (d : DescentDatum R S E) {e : E} :
    e ∈ d.invariants ↔ d.ψ e = 1 ⊗ₜ e := Iff.rfl

/-- The datum is effective: its invariants `E₀` are flat and `S ⊗_R E₀ → E` is bijective, so the
datum is isomorphic to the canonical one on `S ⊗_R E₀`. -/
def IsEffective (d : DescentDatum R S E) : Prop :=
  Module.Flat R d.invariants ∧
    Function.Bijective (LinearMap.liftBaseChange S d.invariants.subtype)

end DescentDatum

variable (R S) in
/-- The canonical descent datum on `S ⊗_R M`, `b ⊗ m ↦ b ⊗ 1 ⊗ m`. -/
noncomputable def canonical (M : Type u) [AddCommGroup M] [Module R M] :
    DescentDatum R S (S ⊗[R] M) where
  ψ := (TensorProduct.mk R S M 1).baseChange S
  counit x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy]
  coassoc x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp
    | add x y hx hy => simp only [map_add, hx, hy]

variable (R S) in
/-- `Spec S → Spec R` is a descent morphism for flat modules: for `M` flat, `M → S ⊗_R M` is
injective with image the invariants of the canonical datum (`M ≅ H⁰(S/R, M)`). -/
def IsDescentFlat : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M],
    Function.Injective (TensorProduct.mk R S M 1) ∧
      (canonical R S M).invariants ≤ LinearMap.range (TensorProduct.mk R S M 1)

variable (R S) in
/-- `Spec S → Spec R` is an effective descent morphism for flat modules: a descent morphism, and
every descent datum on a flat `S`-module is effective. -/
def IsEffectiveDescentFlat : Prop :=
  IsDescentFlat R S ∧
    ∀ (E : Type u) [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]
      [Module.Flat S E] (d : DescentDatum R S E), d.IsEffective

end Defs

section Reduction

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]

variable (S) in
/-- `I` is an ideal of `A` mapped injectively onto an ideal of `S` (Grothendieck, page 1): `I`
lies in the conductor, and `A → S`, `A/I → S/IS` is a Milnor square. -/
structure IsConductorIdeal (I : Ideal A) : Prop where
  inj : ∀ x ∈ I, algebraMap A S x = 0 → x = 0
  ideal : ∀ x ∈ I, ∀ b : S, ∃ y ∈ I, b * algebraMap A S x = algebraMap A S y

variable {I : Ideal A}

lemma IsConductorIdeal.mem_map (h : IsConductorIdeal S I) {r : S} :
    r ∈ I.map (algebraMap A S) ↔ ∃ x ∈ I, algebraMap A S x = r := by
  refine ⟨fun hr => ?_, by rintro ⟨x, hx, rfl⟩; exact Ideal.mem_map_of_mem _ hx⟩
  let J : Ideal S :=
    { carrier := {r | ∃ x ∈ I, algebraMap A S x = r}
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, I.add_mem hx hy, map_add _ _ _⟩
      zero_mem' := ⟨0, I.zero_mem, map_zero _⟩
      smul_mem' := by
        rintro b _ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, e⟩ := h.ideal x hx b
        exact ⟨y, hy, e.symm⟩ }
  exact (Ideal.map_le_iff_le_comap.2 (fun x hx => ⟨x, hx, rfl⟩) : I.map (algebraMap A S) ≤ J) hr

lemma isNilpotent_map (hI : IsNilpotent I) : IsNilpotent (I.map (algebraMap A S)) := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

variable (I) {N : Type u} [AddCommGroup N] [Module A N]
  {M₀ : Type u} [AddCommMonoid M₀] [Module (A ⧸ I) M₀] [Module A M₀]
  [IsScalarTower A (A ⧸ I) M₀]

/-- Reduction modulo `I`: `S ⊗_A N → S₀ ⊗_{A₀} M₀`, `b ⊗ n ↦ b̄ ⊗ g(n)`. -/
noncomputable def red (g : N →ₗ[A] M₀) :
    S ⊗[A] N →ₗ[S] (S ⧸ I.map (algebraMap A S)) ⊗[A ⧸ I] M₀ :=
  LinearMap.liftBaseChange S
    ((TensorProduct.mk (A ⧸ I) (S ⧸ I.map (algebraMap A S)) M₀ 1).restrictScalars A ∘ₗ g)

variable {I}

lemma red_tmul (g : N →ₗ[A] M₀) (b : S) (n : N) :
    red I g (b ⊗ₜ n) = Ideal.Quotient.mk _ b ⊗ₜ g n := by
  simp [red, TensorProduct.smul_tmul', Algebra.smul_def]

/-- In `S ⊗_A N`, `I S · (S ⊗ N) = 1 ⊗ I N`. -/
lemma exists_tmul_of_mem_smul (h : IsConductorIdeal S I) {z : S ⊗[A] N}
    (hz : z ∈ (I.map (algebraMap A S) • ⊤ : Submodule S (S ⊗[A] N))) :
    ∃ y ∈ (I • ⊤ : Submodule A N), z = 1 ⊗ₜ y := by
  refine Submodule.smul_induction_on (p := fun z => ∃ y ∈ (I • ⊤ : Submodule A N), z = 1 ⊗ₜ y)
    hz (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · clear ‹x ∈ ⊤›
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      obtain ⟨x, hx, e⟩ := h.mem_map.1 (Ideal.mul_mem_right b _ hr)
      refine ⟨x • n, Submodule.smul_mem_smul hx trivial, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, ← e, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨u, hu, eu⟩ := hx
      obtain ⟨v, hv, ev⟩ := hy
      exact ⟨u + v, add_mem hu hv, by rw [smul_add, eu, ev, TensorProduct.tmul_add]⟩
  · obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨u + v, add_mem hu hv, (TensorProduct.tmul_add _ _ _).symm⟩

/-- The kernel of the reduction: if `g` is onto with kernel in `I N`, then `red g z = 0` forces
`z ∈ I S · (S ⊗ N)`. The proof builds `β : S₀ ⊗_{A₀} M₀ → (S ⊗ N)/I S (S ⊗ N)` with
`β ∘ red g` the projection. -/
lemma mem_smul_of_red_eq_zero (g : N →ₗ[A] M₀)
    (hg : Function.Surjective g) (hk : ∀ a b, g a = g b → a - b ∈ (I • ⊤ : Submodule A N))
    {z : S ⊗[A] N}
    (hz : red I g z = 0) :
    z ∈ (I.map (algebraMap A S) • ⊤ : Submodule S (S ⊗[A] N)) := by
  set P := (I.map (algebraMap A S) • ⊤ : Submodule S (S ⊗[A] N))
  let _ : Module (A ⧸ I) (S ⊗[A] N ⧸ P) :=
    Module.compHom _ (algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S)))
  have : IsScalarTower (A ⧸ I) (S ⧸ I.map (algebraMap A S)) (S ⊗[A] N ⧸ P) :=
    ⟨fun a b q => by
      show (a • b) • q = algebraMap _ (S ⧸ I.map (algebraMap A S)) a • b • q
      rw [Algebra.smul_def, mul_smul]⟩
  have hfx : ∀ (x : A) (q : S ⊗[A] N ⧸ P),
      (Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S x)) • q = x • q := by
    intro x q
    obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, Module.Quotient.mk_smul_mk, algebraMap_smul,
      Submodule.Quotient.mk_smul]
  have : IsScalarTower A (A ⧸ I) (S ⊗[A] N ⧸ P) :=
    ⟨fun x a q => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      show algebraMap _ (S ⧸ I.map (algebraMap A S)) (x • Ideal.Quotient.mk I a) • q =
        x • algebraMap _ (S ⧸ I.map (algebraMap A S)) (Ideal.Quotient.mk I a) • q
      rw [Algebra.smul_def, map_mul, mul_smul]
      exact hfx x _⟩
  let h₁ : N →ₗ[A] S ⊗[A] N ⧸ P := P.mkQ.restrictScalars A ∘ₗ TensorProduct.mk A S N 1
  have hker : ∀ n ∈ (I • ⊤ : Submodule A N), h₁ n = 0 := fun n hn => by
    refine Submodule.smul_induction_on (p := fun n => h₁ n = 0) hn
      (fun x hx n _ => ?_) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    simp only [h₁, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      LinearMap.coe_restrictScalars, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← TensorProduct.smul_tmul, ← algebraMap_smul S x, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hx) trivial
  have key : ∀ a b, g a = g b → h₁ a = h₁ b := fun a b hab => by
    rw [← sub_eq_zero, ← map_sub]; exact hker _ (hk a b hab)
  let h₂ : M₀ →ₗ[A] S ⊗[A] N ⧸ P :=
    { toFun := fun m => h₁ (Function.surjInv hg m)
      map_add' := fun m m' => by
        rw [← map_add]
        exact key _ _ (by rw [map_add, Function.surjInv_eq hg, Function.surjInv_eq hg,
          Function.surjInv_eq hg])
      map_smul' := fun c m => by
        rw [RingHom.id_apply, ← map_smul]
        exact key _ _ (by rw [map_smul, Function.surjInv_eq hg, Function.surjInv_eq hg]) }
  have h₂g : ∀ n, h₂ (g n) = h₁ n := fun n => key _ _ (Function.surjInv_eq hg _)
  let h₃ : M₀ →ₗ[A ⧸ I] S ⊗[A] N ⧸ P :=
    h₂.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let β := LinearMap.liftBaseChange (S ⧸ I.map (algebraMap A S)) h₃
  have hβ : ∀ t, β (red I g t) = P.mkQ t := fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul b n =>
      rw [red_tmul, LinearMap.liftBaseChange_tmul]
      show (Ideal.Quotient.mk _ b) • h₂ (g n) = _
      rw [h₂g]
      simp only [h₁, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, Submodule.mkQ_apply]
      rw [Module.Quotient.mk_smul_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have := hβ z
  rwa [hz, map_zero, eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

/-- Combining the two: `red g z = 0` gives `z = 1 ⊗ y` with `y ∈ I N`. -/
lemma exists_tmul_of_red_eq_zero (h : IsConductorIdeal S I) (g : N →ₗ[A] M₀)
    (hg : Function.Surjective g) (hk : ∀ a b, g a = g b → a - b ∈ (I • ⊤ : Submodule A N))
    {z : S ⊗[A] N}
    (hz : red I g z = 0) : ∃ y ∈ (I • ⊤ : Submodule A N), z = 1 ⊗ₜ y :=
  exists_tmul_of_mem_smul h (mem_smul_of_red_eq_zero g hg hk hz)

end Reduction

section Reduce

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {I : Ideal A}
  {E : Type u} [AddCommGroup E] [Module S E] [Module A E] [IsScalarTower A S E]

/-- `lTensor` along a base ring is linear over it. -/
lemma lTensor_smul_apply {R B X Y : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (b : B)
    (t : B ⊗[R] X) : f.lTensor B (b • t) = b • f.lTensor B t := by
  rw [← LinearMap.baseChange_eq_lTensor, map_smul]

variable (I) in
/-- `π : E → E₀ = S₀ ⊗_S E`, `e ↦ 1 ⊗ e` (the reduction `E → E/IE`). -/
noncomputable abbrev proj : E →ₗ[S] (S ⧸ I.map (algebraMap A S)) ⊗[S] E :=
  TensorProduct.mk S (S ⧸ I.map (algebraMap A S)) E 1

omit [Module A E] [IsScalarTower A S E] in
lemma proj_surjective : Function.Surjective (proj I : E →ₗ[S] _) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s e =>
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine ⟨s • e, ?_⟩
    rw [TensorProduct.mk_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, map_add _ _ _⟩

omit [Module A E] [IsScalarTower A S E] in
lemma mem_ker_proj {e : E} :
    proj (S := S) I e = 0 ↔ e ∈ (I.map (algebraMap A S) • ⊤ : Submodule S E) := by
  have h := LinearMap.congr_fun (TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ (M := E)
    (I.map (algebraMap A S))) e
  rw [proj, ← h, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

lemma mem_smul_iff (h : IsConductorIdeal S I) {e : E} :
    e ∈ (I.map (algebraMap A S) • ⊤ : Submodule S E) ↔ e ∈ (I • ⊤ : Submodule A E) := by
  constructor
  · intro he
    refine Submodule.smul_induction_on (p := fun e => e ∈ (I • ⊤ : Submodule A E)) he
      (fun r hr e _ => ?_) (fun _ _ => add_mem)
    obtain ⟨x, hx, rfl⟩ := h.mem_map.1 hr
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hx trivial
  · intro he
    refine Submodule.smul_induction_on (p := fun e => e ∈ (I.map (algebraMap A S) • ⊤ :
      Submodule S E)) he (fun x hx e _ => ?_) (fun _ _ => add_mem)
    rw [← algebraMap_smul S x e]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hx) Submodule.mem_top

variable (I) in
/-- `ρ : S ⊗_A E → S₀ ⊗_{A₀} E₀`, the reduction of `S ⊗ E`. -/
noncomputable abbrev redE :
    S ⊗[A] E →ₗ[S] (S ⧸ I.map (algebraMap A S)) ⊗[A ⧸ I] ((S ⧸ I.map (algebraMap A S)) ⊗[S] E) :=
  red I ((proj I).restrictScalars A)

namespace DescentDatum

variable (I) in
/-- **The reduction of a descent datum modulo `I`**: on `E₀ = S₀ ⊗_S E`, relative to
`A₀ = A/I → S₀ = S/IS`, `ψ₀(s ⊗ e) = s · ρ(ψ(e))`. -/
noncomputable def reduce (d : DescentDatum A S E) :
    DescentDatum (A ⧸ I) (S ⧸ I.map (algebraMap A S)) ((S ⧸ I.map (algebraMap A S)) ⊗[S] E) where
  ψ := LinearMap.liftBaseChange _ (redE I ∘ₗ d.ψ)
  counit x := by
    have key : ∀ t : S ⊗[A] E, LinearMap.liftBaseChange (S ⧸ I.map (algebraMap A S))
        (LinearMap.id : ((S ⧸ I.map (algebraMap A S)) ⊗[S] E) →ₗ[A ⧸ I] _) (redE I t) =
        proj I (LinearMap.liftBaseChange S (LinearMap.id : E →ₗ[A] E) t) := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul b e =>
        rw [red_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
        simp only [LinearMap.coe_restrictScalars, TensorProduct.mk_apply, LinearMap.id_apply,
          map_smul, TensorProduct.smul_tmul']
        rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    induction x using TensorProduct.inductionOn with
    | tmul s e =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.comp_apply, key, d.counit]
      rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  coassoc x := by
    set ψ₀ : (S ⧸ I.map (algebraMap A S)) ⊗[S] E →ₗ[S ⧸ I.map (algebraMap A S)] _ :=
      LinearMap.liftBaseChange _ (redE I ∘ₗ d.ψ)
    let ρ₂ := red (S := S) I ((redE (S := S) I (E := E)).restrictScalars A)
    have L1 : ∀ t : S ⊗[A] E, (ψ₀.restrictScalars (A ⧸ I)).lTensor _ (redE I t) =
        ρ₂ ((d.ψ.restrictScalars A).lTensor S t) := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul b e =>
        rw [red_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, red_tmul]
        simp only [ψ₀, LinearMap.coe_restrictScalars, TensorProduct.mk_apply,
          LinearMap.liftBaseChange_one_tmul, LinearMap.comp_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    have L2 : ∀ t : S ⊗[A] E,
        (TensorProduct.mk (A ⧸ I) (S ⧸ I.map (algebraMap A S)) _ 1).lTensor _ (redE I t) =
        ρ₂ ((TensorProduct.mk A S E 1).lTensor S t) := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul b e =>
        rw [red_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, red_tmul]
        simp only [LinearMap.coe_restrictScalars, TensorProduct.mk_apply, red_tmul,
          map_one]
      | add x y hx hy => simp only [map_add, hx, hy]
    induction x using TensorProduct.inductionOn with
    | tmul s e =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, lTensor_smul_apply,
        lTensor_smul_apply, L1, d.coassoc, L2]
    | add x y hx hy => simp only [map_add, hx, hy]

end DescentDatum

end Reduce

section Main

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {I : Ideal A}
  {E : Type u} [AddCommGroup E] [Module S E] [Module A E] [IsScalarTower A S E]

lemma proj_restrict_surjective :
    Function.Surjective ((proj (S := S) I).restrictScalars A : E →ₗ[A] _) :=
  proj_surjective (S := S) (E := E)

lemma ker_proj_le (h : IsConductorIdeal S I) :
    LinearMap.ker ((proj (S := S) I).restrictScalars A : E →ₗ[A] _) ≤ I • ⊤ := fun _ he =>
  (mem_smul_iff h).1 (mem_ker_proj.1 he)

namespace DescentDatum

/-- **Step 1** (the square-zero computation of page 5, which needs no nilpotence): `e` is
invariant iff its reduction is. So the invariants of `E₀` are the image of those of `E`, and
every `e ∈ I E` is invariant. -/
lemma mem_invariants_iff (h : IsConductorIdeal S I) (d : DescentDatum A S E) (e : E) :
    e ∈ d.invariants ↔ proj I e ∈ (d.reduce I).invariants := by
  have hψ : (d.reduce I).ψ (proj I e) = redE I (d.ψ e) := LinearMap.liftBaseChange_one_tmul _ _ _
  have h1 : redE (S := S) I ((1 : S) ⊗ₜ[A] e) = 1 ⊗ₜ proj I e := by
    rw [red_tmul, map_one]; rfl
  rw [mem_invariants, mem_invariants, hψ, ← h1]
  refine ⟨fun he => by rw [he], fun he => ?_⟩
  rw [← sub_eq_zero, ← map_sub] at he
  obtain ⟨y, -, hy⟩ := exists_tmul_of_red_eq_zero h _ (proj_restrict_surjective (S := S) (E := E))
    (fun a b hab => ker_proj_le (S := S) (E := E) h
      (by rw [LinearMap.mem_ker, map_sub, hab, sub_self])) he
  have := congr_arg (LinearMap.liftBaseChange S (LinearMap.id : E →ₗ[A] E)) hy
  rw [map_sub, d.counit, LinearMap.liftBaseChange_one_tmul, LinearMap.id_apply,
    LinearMap.liftBaseChange_one_tmul, LinearMap.id_apply, sub_self] at this
  rw [← sub_eq_zero, hy, ← this, TensorProduct.tmul_zero]

/-- **Step 2** (Nakayama for the nilpotent ideal `IS`): if the reduction is effective, the
invariants generate `E` over `S`. -/
lemma span_invariants_eq_top (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    (d : DescentDatum A S E) (h₀ : (d.reduce I).IsEffective) :
    Submodule.span S (d.invariants : Set E) = ⊤ := by
  set P := Submodule.span S (d.invariants : Set E)
  set I' := I.map (algebraMap A S)
  have hstep : ⊤ ≤ P ⊔ I' • ⊤ := by
    intro e _
    obtain ⟨t, ht⟩ := h₀.2.2 (proj I e)
    have hmem : proj I e ∈ P.map (proj I) := by
      have hr : proj I e ∈ LinearMap.range
          (LinearMap.liftBaseChange (S ⧸ I') (d.reduce I).invariants.subtype) := ⟨t, ht⟩
      rw [LinearMap.range_liftBaseChange, Submodule.range_subtype] at hr
      have hr' : proj I e ∈ (Submodule.span (S ⧸ I') ((d.reduce I).invariants :
          Set ((S ⧸ I') ⊗[S] E))).restrictScalars S := hr
      rw [Submodule.restrictScalars_span S (S ⧸ I') Ideal.Quotient.mk_surjective] at hr'
      refine (Submodule.span_le.2 ?_) hr'
      intro x hx
      obtain ⟨y, rfl⟩ := proj_surjective (I := I) x
      exact ⟨y, Submodule.subset_span ((mem_invariants_iff h d y).2 hx), rfl⟩
    obtain ⟨p, hp, hpe⟩ := hmem
    have : e - p ∈ I' • (⊤ : Submodule S E) := by
      rw [← mem_ker_proj, map_sub, hpe, sub_self]
    rw [show e = p + (e - p) by abel]
    exact Submodule.add_mem_sup hp this
  have key : ∀ k : ℕ, ⊤ ≤ P ⊔ I' ^ k • ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
    | succ k ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc I' ^ k • (⊤ : Submodule S E) ≤ I' ^ k • (P ⊔ I' • ⊤) := Submodule.smul_mono le_rfl hstep
        _ = I' ^ k • P ⊔ (I' ^ k * I') • ⊤ := by rw [Submodule.smul_sup, Submodule.mul_smul]
        _ ≤ P ⊔ I' ^ (k + 1) • ⊤ := by
          rw [← pow_succ]; exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨n, hn⟩ := isNilpotent_map (S := S) hI
  have := key n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_le_iff.1 this

/-! The invariants are handled through an injective `ι : N → E` onto them, `N` any module
(in the end `N = E^ψ`, `ι` the inclusion). -/

variable {N : Type u} [AddCommGroup N] [Module A N]

/-- `I S · E ⊂ ι(I N)` once the invariants span `E`. -/
lemma exists_of_mem_smul (h : IsConductorIdeal S I) (ι : N →ₗ[A] E)
    (hspan : Submodule.span S (Set.range ι) = ⊤) {e : E}
    (he : e ∈ (I.map (algebraMap A S) • ⊤ : Submodule S E)) :
    ∃ y ∈ (I • ⊤ : Submodule A N), e = ι y := by
  have key : ∀ x ∈ Submodule.span S (Set.range ι), ∀ r ∈ I.map (algebraMap A S),
      ∃ y ∈ (I • ⊤ : Submodule A N), r • x = ι y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro r hr
      obtain ⟨n, rfl⟩ := hx
      obtain ⟨c, hc, rfl⟩ := h.mem_map.1 hr
      exact ⟨c • n, Submodule.smul_mem_smul hc trivial, by rw [algebraMap_smul, map_smul]⟩
    | zero => exact fun r _ => ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro r hr
      obtain ⟨u, hu, eu⟩ := hx r hr
      obtain ⟨v, hv, ev⟩ := hy r hr
      exact ⟨u + v, add_mem hu hv, by rw [smul_add, eu, ev, map_add]⟩
    | smul b x _ hx =>
      intro r hr
      rw [smul_smul]
      exact hx _ (Ideal.mul_mem_right _ _ hr)
  refine Submodule.smul_induction_on (p := fun (e : E) => ∃ y ∈ (I • ⊤ : Submodule A N),
    e = ι y) he (fun r hr x _ => key x (hspan ▸ Submodule.mem_top) r hr) ?_
  rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  exact ⟨u + v, add_mem hu hv, (map_add _ _ _).symm⟩

variable (I) in
/-- The reduction `N ≅ E^ψ → E₀^{ψ₀}` of the invariants. -/
noncomputable def projInv (h : IsConductorIdeal S I) (d : DescentDatum A S E) (ι : N →ₗ[A] E)
    (hrange : ∀ n, ι n ∈ d.invariants) : N →ₗ[A] (d.reduce I).invariants where
  toFun n := ⟨proj I (ι n), (mem_invariants_iff h d _).1 (hrange n)⟩
  map_add' _ _ := Subtype.ext (by simp only [map_add, Submodule.coe_add])
  map_smul' c n := Subtype.ext (by
    simp only [map_smul, RingHom.id_apply, Submodule.coe_smul_of_tower]
    exact ((proj I).restrictScalars A).map_smul c (ι n))

lemma projInv_surjective (h : IsConductorIdeal S I) (d : DescentDatum A S E) (ι : N →ₗ[A] E)
    (hrange : ∀ n, ι n ∈ d.invariants) (hrange' : ∀ e ∈ d.invariants, ∃ n, ι n = e) :
    Function.Surjective (projInv I h d ι hrange) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := proj_surjective (I := I) x
  obtain ⟨n, rfl⟩ := hrange' y ((mem_invariants_iff h d y).2 hx)
  exact ⟨n, rfl⟩

lemma mem_smul_of_proj_eq_zero (h : IsConductorIdeal S I) (ι : N →ₗ[A] E)
    (hι : Function.Injective ι) (hspan : Submodule.span S (Set.range ι) = ⊤) {n : N}
    (hn : proj (S := S) I (ι n) = 0) : n ∈ (I • ⊤ : Submodule A N) := by
  obtain ⟨_, hy, e⟩ := exists_of_mem_smul h ι hspan (mem_ker_proj.1 hn)
  rwa [hι e]

/-- The core of Prop. 2, for any `ι : N → E` injective onto the invariants. -/
theorem flat_and_bijective_of_reduce (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    [Module.Flat S E] (d : DescentDatum A S E) (h₀ : (d.reduce I).IsEffective)
    (ι : N →ₗ[A] E) (hι : Function.Injective ι) (hrange : ∀ n, ι n ∈ d.invariants)
    (hrange' : ∀ e ∈ d.invariants, ∃ n, ι n = e) :
    Module.Flat A N ∧ Function.Bijective (LinearMap.liftBaseChange S ι) := by
  have hspan : Submodule.span S (Set.range ι) = ⊤ := by
    rw [← span_invariants_eq_top h hI d h₀]
    congr 1
    ext e
    exact ⟨by rintro ⟨n, rfl⟩; exact hrange n, hrange' e⟩
  set g := projInv I h d ι hrange
  have hg := projInv_surjective h d ι hrange hrange'
  have hg0 : ∀ n, proj (S := S) I (ι n) = 0 → n ∈ (I • ⊤ : Submodule A N) := fun _ =>
    mem_smul_of_proj_eq_zero h ι hι hspan
  set α := LinearMap.liftBaseChange S ι
  have hsurj : Function.Surjective α := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange]
    exact hspan
  -- `α₀ ∘ red g = π ∘ α`
  have hcomm : ∀ t, LinearMap.liftBaseChange (S ⧸ I.map (algebraMap A S))
      (d.reduce I).invariants.subtype (red (S := S) (M₀ := (d.reduce I).invariants) I g t) =
        proj I (α t) := fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul b x =>
      rw [red_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
      simp only [Submodule.subtype_apply, g, projInv, LinearMap.coe_mk, AddHom.coe_mk,
        map_smul, TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h0 : red (S := S) (M₀ := (d.reduce I).invariants) I g t = 0 :=
      h₀.2.1 (by rw [hcomm, ht, map_zero, map_zero])
    have hk : ∀ a b, g a = g b → a - b ∈ (I • ⊤ : Submodule A N) := fun a b hab => by
      refine hg0 _ ?_
      have : proj I (ι a) = proj I (ι b) := congr_arg Subtype.val hab
      rw [map_sub, map_sub, this, sub_self]
    have := exists_tmul_of_red_eq_zero (M₀ := (d.reduce I).invariants) (z := t) h g hg hk
    obtain ⟨y, -, rfl⟩ := this h0
    obtain rfl : y = 0 := hι (by simpa [α] using ht)
    rw [TensorProduct.tmul_zero]
  refine ⟨flat_of_isNilpotent hI ?_ ?_, hinj, hsurj⟩
  · -- `A/I ⊗_A N ≅ E₀^{ψ₀}`, flat over `A/I`
    let φ := LinearMap.liftBaseChange (A ⧸ I) g
    have hφ : Function.Bijective φ := by
      refine ⟨?_, fun x => ?_⟩
      · rw [injective_iff_map_eq_zero]
        intro t ht
        obtain ⟨n, rfl⟩ : ∃ n, (1 : A ⧸ I) ⊗ₜ[A] n = t := by
          obtain ⟨q, rfl⟩ := (TensorProduct.quotTensorEquivQuotSMul N I).symm.surjective t
          obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective _ q
          exact ⟨n, rfl⟩
        rw [LinearMap.liftBaseChange_one_tmul] at ht
        have hn := hg0 n (congr_arg Subtype.val ht)
        rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.map_eq_zero_iff,
          Submodule.Quotient.mk_eq_zero]
        exact hn
      · obtain ⟨n, rfl⟩ := hg x
        exact ⟨1 ⊗ₜ n, LinearMap.liftBaseChange_one_tmul _ _ _⟩
    have : Module.Flat (A ⧸ I) (d.reduce I).invariants := h₀.1
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective φ hφ)
  · -- `I ⊗_A N ≅ I ⊗_S (S ⊗_A N) ≅ I ⊗_S E → E` is injective, `E` being flat over `S`
    set I' := I.map (algebraMap A S)
    let j : I →ₗ[A] I' :=
      { toFun := fun x => ⟨algebraMap A S x, Ideal.mem_map_of_mem _ x.2⟩
        map_add' := fun x y => Subtype.ext (map_add _ _ _)
        map_smul' := fun c x => Subtype.ext (by simp [Algebra.smul_def]) }
    have hj : Function.Bijective j := by
      refine ⟨fun x y hxy => ?_, fun r => ?_⟩
      · have : algebraMap A S ((x : A) - y) = 0 := by
          rw [map_sub, sub_eq_zero]; exact congr_arg Subtype.val hxy
        exact Subtype.ext (sub_eq_zero.1 (h.inj _ (I.sub_mem x.2 y.2) this))
      · obtain ⟨x, hx, e⟩ := h.mem_map.1 r.2
        exact ⟨⟨x, hx⟩, Subtype.ext e⟩
    let αe := LinearEquiv.ofBijective α ⟨hinj, hsurj⟩
    let Φ : I ⊗[A] N →ₗ[A] E :=
      (TensorProduct.lid S E).toLinearMap.restrictScalars A ∘ₗ
        (I'.subtype.rTensor E).restrictScalars A ∘ₗ
          (αe.toLinearMap.lTensor I').restrictScalars A ∘ₗ
            (AlgebraTensorModule.cancelBaseChange A S S I' N).symm.toLinearMap.restrictScalars A ∘ₗ
              j.rTensor N
    have hΦ : Φ = (ι ∘ₗ (TensorProduct.lid A N).toLinearMap) ∘ₗ I.subtype.rTensor N := by
      refine TensorProduct.ext' fun x n => ?_
      simp only [Φ, αe, α, j]
      simp [algebraMap_smul]
      exact congr_arg _ (LinearMap.liftBaseChange_one_tmul _ _ _)
    have hΦinj : Function.Injective Φ := by
      have h1 : Function.Injective (j.rTensor N) :=
        (LinearEquiv.rTensor N (LinearEquiv.ofBijective j hj)).injective
      have h3 : Function.Injective (αe.toLinearMap.lTensor I') :=
        (LinearEquiv.lTensor I' αe).injective
      have h4 : Function.Injective (I'.subtype.rTensor E) :=
        Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
      exact (TensorProduct.lid S E).injective.comp (h4.comp (h3.comp
        ((AlgebraTensorModule.cancelBaseChange A S S I' N).symm.injective.comp h1)))
    rw [hΦ, LinearMap.coe_comp] at hΦinj
    exact hΦinj.of_comp

/-- **Folder 128, Prop. 2** (Grothendieck, pages 4–7). Let `I` be a nilpotent ideal of `A`
mapped isomorphically onto an ideal of `S`, and `E` a flat `S`-module with a descent datum
relative to `A → S` whose reduction modulo `I` (relative to `A/I → S/IS`) is effective. Then the
datum is effective: the invariants `E^ψ` are flat over `A` and `S ⊗_A E^ψ → E` is bijective.
Neither `A ≅ H⁰(S/A)` nor `H¹(S/A) = 0` is needed. -/
theorem isEffective_of_reduce (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    [Module.Flat S E] (d : DescentDatum A S E) (h₀ : (d.reduce I).IsEffective) :
    d.IsEffective := by
  exact flat_and_bijective_of_reduce h hI d h₀ (N := d.invariants)
    d.invariants.subtype Subtype.val_injective (fun n => n.2) (fun e he => ⟨⟨e, he⟩, rfl⟩)

end DescentDatum

/-- `M → M₀ = A/I ⊗ M` is onto, with kernel `I M`. -/
lemma mk_quot_surjective (M : Type u) [AddCommGroup M] [Module A M] :
    Function.Surjective (TensorProduct.mk A (A ⧸ I) M 1) := fun t => by
  obtain ⟨q, rfl⟩ := (TensorProduct.quotTensorEquivQuotSMul M I).symm.surjective t
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective _ q
  exact ⟨n, rfl⟩

lemma mk_quot_eq_zero {M : Type u} [AddCommGroup M] [Module A M] {m : M} :
    TensorProduct.mk A (A ⧸ I) M 1 m = 0 ↔ m ∈ (I • ⊤ : Submodule A M) := by
  rw [TensorProduct.mk_apply, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- **Folder 128, Cor. 1** (Grothendieck, page 7). Let `I` be a nilpotent ideal of `A` mapped
isomorphically onto an ideal of `S` (`I` in the conductor). If `Spec S/IS → Spec A/I` is an
effective descent morphism for flat modules, so is `Spec S → Spec A`. -/
theorem isEffectiveDescentFlat_of_quotient (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    (h₀ : IsEffectiveDescentFlat (A ⧸ I) (S ⧸ I.map (algebraMap A S))) :
    IsEffectiveDescentFlat A S := by
  refine ⟨fun M _ _ _ => ?_, fun E _ _ _ _ _ d =>
    DescentDatum.isEffective_of_reduce h hI d (h₀.2 _ (d.reduce I))⟩
  obtain ⟨hinj₀, hinv₀⟩ := h₀.1 ((A ⧸ I) ⊗[A] M)
  let gM : M →ₗ[A] (A ⧸ I) ⊗[A] M := TensorProduct.mk A (A ⧸ I) M 1
  have hgM : Function.Surjective gM := mk_quot_surjective M
  have hk : ∀ a b, gM a = gM b → a - b ∈ (I • ⊤ : Submodule A M) := fun a b hab => by
    rwa [← mk_quot_eq_zero, map_sub, sub_eq_zero]
  have hred1 : ∀ m, red (S := S) I gM (1 ⊗ₜ m) = 1 ⊗ₜ gM m := fun m => by
    rw [red_tmul, map_one]
  constructor
  · -- `M → S ⊗ M` is injective
    rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : gM m = 0 := hinj₀ (by
      rw [map_zero]
      have := hred1 m
      rw [show (1 : S) ⊗ₜ[A] m = 0 from hm, map_zero] at this
      exact this.symm)
    obtain ⟨t, rfl⟩ : m ∈ LinearMap.range (smulMap I M) := by
      rw [range_smulMap]; exact mk_quot_eq_zero.1 h1
    let ν : I ⊗[A] M →ₗ[A] S ⊗[A] M := (Algebra.linearMap A S ∘ₗ I.subtype).rTensor M
    have hν : Function.Injective ν := Module.Flat.rTensor_preserves_injective_linearMap _
      (fun x y hxy => Subtype.ext (sub_eq_zero.1 (h.inj _ (I.sub_mem x.2 y.2)
        (by rw [map_sub, sub_eq_zero]; exact hxy))))
    have he : TensorProduct.mk A S M 1 ∘ₗ smulMap I M = ν := by
      refine TensorProduct.ext' fun x n => ?_
      simp [ν, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have : ν t = 0 := by rw [← he, LinearMap.comp_apply]; exact hm
    rw [hν (this.trans (map_zero ν).symm), map_zero]
  · -- the invariants of `S ⊗ M` come from `M`
    intro x hx
    rw [DescentDatum.mem_invariants] at hx
    let ρ₂ := red (S := S) I ((red (S := S) I gM).restrictScalars A)
    have L1 : ∀ t, (canonical (A ⧸ I) (S ⧸ I.map (algebraMap A S)) ((A ⧸ I) ⊗[A] M)).ψ
        (red I gM t) = ρ₂ ((canonical A S M).ψ t) := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul b m =>
        simp only [canonical, red_tmul, LinearMap.baseChange_tmul, TensorProduct.mk_apply, ρ₂,
          LinearMap.coe_restrictScalars, map_one]
      | add x y hx hy => simp only [map_add, hx, hy]
    have L2 : ∀ t, (1 : S ⧸ I.map (algebraMap A S)) ⊗ₜ[A ⧸ I] red I gM t =
        ρ₂ ((1 : S) ⊗ₜ[A] t) := fun t => by
      rw [red_tmul, map_one]; rfl
    have hx₀ : red (S := S) I gM x ∈
        (canonical (A ⧸ I) (S ⧸ I.map (algebraMap A S)) ((A ⧸ I) ⊗[A] M)).invariants := by
      rw [DescentDatum.mem_invariants, L1, hx, ← L2]
    obtain ⟨m₀, hm₀⟩ := hinv₀ hx₀
    obtain ⟨m, rfl⟩ := hgM m₀
    have hz : red (S := S) I gM (x - 1 ⊗ₜ m) = 0 := by
      rw [map_sub, hred1, sub_eq_zero]; exact hm₀.symm
    obtain ⟨y, -, hy⟩ := exists_tmul_of_red_eq_zero h gM hgM hk hz
    exact ⟨m + y, by rw [TensorProduct.mk_apply, TensorProduct.tmul_add, ← hy,
      add_sub_cancel]⟩

end Main

end Grothendieck.Folder128.Descent


/-!
## Pages 19–29: descent along the infinitesimal neighbourhoods — what is proved

The reading (« Descente le long des voisinages infinitésimaux ») states a Théorème (page 25):
for `A` semi-local noetherian with radical `𝔪`, `A'` finite over `A`, `A_n = A/𝔪^{n+1}`,
`A'_n = A' ⊗ A_n`, the conditions `H¹(A'_n/A_n) = 0`, `H¹(A'_n/A_n, Gl_r)` trivial and
« `Spec A'_n → Spec H⁰(A'_n/A_n)` is an effective descent morphism for flat modules », for all
`n`, are equivalent, and imply effective descent of flat modules of finite type along
`Spec A' → Spec H⁰(A'/A)`. Its proof (pages 26–29) rests on Lemme 1 (pages 19–20), whose proof
the reading finds wrong (the multiplicative coboundary is a logarithmic derivative), on
Cor. 2–3 (pages 21–22), on Lemme 2 (pages 23–24), and on an unwritten passage to the limit.
The theorem itself is **not** formalised here. This section proves the parts of its proof that
hold as written, or in a stronger form:

* `lemme2` (Lemme 2, page 23, with the edition's observation that hypothesis (i) is superfluous):
  `C` integral over `B` with finitely many maximal ideals, distinct maximal ideals of `C` lying
  over distinct ideals of `B`, purely inseparable residue extensions. Then every `u ∈ M_n(C)` has
  a `v ∈ M_n(B)` with `u + v` invertible. No infinite residue field is assumed: a finite
  residue field is perfect, so the radicial extension is trivial and `v = 1 − u` works there;
  over an infinite residue field `v` is a scalar `t`, `t` avoiding the roots of the monic
  `det(t + u)`. The Chinese remainder theorem glues the residue fields.
  `exists_isUnit_add_map` is the same with « infinite or `B → C/𝔫` onto » as hypothesis.
* `exists_isUnit_add`: the case `n = 1`, the N.B. of Lemme 1 (page 19), `C = C^* + B` for
  `C = H⁰(A'_0/A_0)` over the image of `B = H⁰(A'/A)`, under the same hypotheses (that
  `Spec C → Spec B` is radicial is asserted on the page and not proved, here or there).
* `tensorEquiv`, `bijective_mapOfCompatibleSMul`, `mem_H0_iff` (the bracket of pages 26–27):
  for `A → B → S` with `B` mapping into `H⁰(S/A) = {s | s ⊗ 1 = 1 ⊗ s}`, the tensor products
  `S ⊗_A E` and `S ⊗_B E` coincide for every `S`-module `E`; so descent data and Amitsur
  complexes relative to `S/A` and to `S/H⁰(S/A)` are the same, and `H⁰(S/B) = H⁰(S/A)`.
* `coboundary_mul_eq`: the identity behind the reading's objection to Lemme 1, page 20:
  `p₂(u) p₁(u)⁻¹ = 1 + p₁(u)⁻¹ (p₂(u) − p₁(u))`, so the multiplicative coboundary is
  `u⁻¹ ∂(u)`, not `∂(u)`.

Not formalised: Amitsur cohomology `H¹(A'/A)` and the non-abelian `H¹(A'/A, Gl_r)` (mathlib has
neither), Lemme 1 and its corollaries (unproved in the folder), the induction on `n`, the
Mittag-Leffler and Artin–Rees passage to the limit of b), and c).
-/

namespace Grothendieck.Folder128.Infinitesimal

section Lemme2

open Matrix Polynomial Function



/-- Over an infinite ring `R` injected into a domain `K`, every `u ∈ M_n(K)` becomes
nonsingular after adding a scalar `f(t)`: `det(t + u)` is the monic `charpoly(−u)` at `t`. -/
lemma exists_det_ne_zero_of_infinite {R K : Type*} [CommRing R] [CommRing K] [IsDomain K]
    (f : R →+* K) (hf : Function.Injective f) [Infinite R]
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n K) :
    ∃ t : R, (u + Matrix.scalar n (f t)).det ≠ 0 := by
  by_contra! h
  have hp : (-u).charpoly = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem hf fun t => ?_
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, eval_charpoly, sub_neg_eq_add, add_comm]
    exact h t
  exact (charpoly_monic (-u)).ne_zero hp

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra B C]

/-- `B → C/𝔫`. -/
abbrev resMap (𝔫 : MaximalSpectrum C) : B →+* C ⧸ 𝔫.asIdeal :=
  (Ideal.Quotient.mk 𝔫.asIdeal).comp (algebraMap B C)

/-- The kernel of `B → C/𝔫` is `𝔫 ∩ B`. -/
lemma ker_resMap (𝔫 : MaximalSpectrum C) :
    RingHom.ker (resMap (B := B) 𝔫) = 𝔫.asIdeal.comap (algebraMap B C) := by
  ext b
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The residue-field step of Lemme 2: at a maximal ideal `𝔫` of `C` whose residue field is
reached by an infinite `B/(𝔫 ∩ B)` or onto from `B`, every matrix over `C/𝔫` becomes nonsingular
after adding a matrix of `B`. -/
lemma exists_det_ne_zero_residue (𝔫 : MaximalSpectrum C)
    (h : Infinite (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) ∨ Function.Surjective (resMap (B := B) 𝔫))
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n (C ⧸ 𝔫.asIdeal)) :
    ∃ w : Matrix n n B, (u + w.map (resMap 𝔫)).det ≠ 0 := by
  have := 𝔫.isMaximal
  rcases h with h | h
  · have e := Ideal.quotEquivOfEq (ker_resMap (B := B) 𝔫).symm
    have : Infinite (B ⧸ RingHom.ker (resMap (B := B) 𝔫)) :=
      Infinite.of_injective (⇑e) e.injective
    have : IsDomain (C ⧸ 𝔫.asIdeal) := Ideal.Quotient.isDomain _
    obtain ⟨t, ht⟩ := exists_det_ne_zero_of_infinite (RingHom.kerLift (resMap (B := B) 𝔫))
      (RingHom.kerLift_injective _) u
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨Matrix.scalar n t, ?_⟩
    convert ht using 3
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]
  · choose g hg using h
    refine ⟨Matrix.of fun i j => g ((1 - u) i j), ?_⟩
    have : u + (Matrix.of fun i j => g ((1 - u) i j)).map (resMap 𝔫) = 1 := by
      ext i j
      rw [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hg, Matrix.sub_apply, add_sub_cancel]
    rw [this, Matrix.det_one]; exact one_ne_zero

/-- **Folder 128, Lemme 2, general form** (Grothendieck, page 23). `C` integral over `B` with
finitely many maximal ideals, distinct maximal ideals of `C` lying over distinct (maximal) ideals
of `B`, and at each `𝔫` either `B/(𝔫 ∩ B)` infinite or `B → C/𝔫` onto. Then for every
`u ∈ M_n(C)` there is `v ∈ M_n(B)` with `u + v` invertible. -/
theorem exists_isUnit_add_map [Algebra.IsIntegral B C] [Finite (MaximalSpectrum C)]
    (hinj : ∀ 𝔫 𝔫' : MaximalSpectrum C,
      𝔫.asIdeal.comap (algebraMap B C) = 𝔫'.asIdeal.comap (algebraMap B C) → 𝔫 = 𝔫')
    (hres : ∀ 𝔫 : MaximalSpectrum C, Infinite (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) ∨
      Function.Surjective (resMap (B := B) 𝔫))
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n C) :
    ∃ v : Matrix n n B, IsUnit (u + v.map (algebraMap B C)) := by
  choose w hw using fun 𝔫 => exists_det_ne_zero_residue 𝔫 (hres 𝔫) (u.map (Ideal.Quotient.mk _))
  let I : MaximalSpectrum C → Ideal B := fun 𝔫 => 𝔫.asIdeal.comap (algebraMap B C)
  have hmax : ∀ 𝔫, (I 𝔫).IsMaximal := fun 𝔫 => by
    have := 𝔫.isMaximal; exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) 𝔫.asIdeal
  have hcop : Pairwise (IsCoprime on I) := fun 𝔫 𝔫' hne => by
    have := hmax 𝔫; have := hmax 𝔫'
    exact Ideal.isCoprime_of_isMaximal fun h => hne (hinj 𝔫 𝔫' h)
  have hcrt : ∀ i j, ∃ x : B, ∀ 𝔫, x - w 𝔫 i j ∈ I 𝔫 := fun i j => by
    obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop
      (fun 𝔫 => Ideal.Quotient.mk (I 𝔫) (w 𝔫 i j))
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨x, fun 𝔫 => ?_⟩
    rw [← Ideal.Quotient.eq]
    exact congrFun hq 𝔫
  choose v hv using hcrt
  refine ⟨Matrix.of v, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  by_contra hu
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  let 𝔫 : MaximalSpectrum C := ⟨𝔪, h𝔪⟩
  apply hw 𝔫
  have hmap : (Ideal.Quotient.mk 𝔪).mapMatrix (u + (Matrix.of v).map (algebraMap B C)) =
      u.map (Ideal.Quotient.mk _) + (w 𝔫).map (resMap 𝔫) := by
    ext i j
    have := hv i j 𝔫
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply,
      map_add, RingHom.comp_apply]
    congr 1
    rw [Ideal.Quotient.eq]
    simpa [I, ← map_sub] using this
  rw [← hmap, ← RingHom.map_det, Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

/-- **Folder 128, Lemme 2** (Grothendieck, page 23), without hypothesis (i). Let `C` be integral
over `B` with finitely many maximal ideals, two distinct maximal ideals of `C` lying over
distinct ideals of `B`, and every residue extension `k(𝔫)/k(𝔪)` purely inseparable (`C` finite
and radicial over `B`). Then for every `u ∈ M_n(C)` there is `v ∈ M_n(B)` with `u + φ(v)`
invertible. A finite residue field is perfect, so there the radicial extension is trivial. -/
theorem lemme2 [Algebra.IsIntegral B C] [Finite (MaximalSpectrum C)]
    (hinj : ∀ 𝔫 𝔫' : MaximalSpectrum C,
      𝔫.asIdeal.comap (algebraMap B C) = 𝔫'.asIdeal.comap (algebraMap B C) → 𝔫 = 𝔫')
    (hrad : ∀ 𝔫 : MaximalSpectrum C,
      IsPurelyInseparable (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) (C ⧸ 𝔫.asIdeal))
    {n : Type*} [Fintype n] [DecidableEq n] (u : Matrix n n C) :
    ∃ v : Matrix n n B, IsUnit (u + v.map (algebraMap B C)) := by
  refine exists_isUnit_add_map hinj (fun 𝔫 => ?_) u
  rcases finite_or_infinite (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) with hfin | hinf
  · right
    have := 𝔫.isMaximal
    have : (𝔫.asIdeal.comap (algebraMap B C)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) 𝔫.asIdeal
    let := Ideal.Quotient.field (𝔫.asIdeal.comap (algebraMap B C))
    let := Ideal.Quotient.field 𝔫.asIdeal
    have := hrad 𝔫
    intro c
    obtain ⟨b', hb'⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable
      (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) (C ⧸ 𝔫.asIdeal) c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
    exact ⟨b, hb'⟩
  · exact Or.inl hinf

/-- **Folder 128, N.B. of Lemme 1** (Grothendieck, page 19): under the hypotheses of `lemme2`,
`C = C^* + B`, every `c ∈ C` is a unit up to an element of `B`. -/
theorem exists_isUnit_add [Algebra.IsIntegral B C] [Finite (MaximalSpectrum C)]
    (hinj : ∀ 𝔫 𝔫' : MaximalSpectrum C,
      𝔫.asIdeal.comap (algebraMap B C) = 𝔫'.asIdeal.comap (algebraMap B C) → 𝔫 = 𝔫')
    (hrad : ∀ 𝔫 : MaximalSpectrum C,
      IsPurelyInseparable (B ⧸ 𝔫.asIdeal.comap (algebraMap B C)) (C ⧸ 𝔫.asIdeal))
    (c : C) : ∃ b : B, IsUnit (c + algebraMap B C b) := by
  obtain ⟨v, hv⟩ := lemme2 hinj hrad (Matrix.of fun _ _ : Fin 1 => c)
  refine ⟨v 0 0, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique] at hv
  simpa using hv


end Lemme2

section Tensor

open TensorProduct



variable (A B S : Type*) [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra B S]
  [Algebra A S] [IsScalarTower A B S]

/-- `H⁰(S/A) = {s ∣ s ⊗ 1 = 1 ⊗ s}`, the equalizer of `S ⇉ S ⊗_A S` (the page's `B`). -/
def H0 : Subalgebra A S where
  carrier := {s | s ⊗ₜ[A] (1 : S) = 1 ⊗ₜ s}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    have : (x * y) ⊗ₜ[A] (1 : S) = (x ⊗ₜ[A] (1 : S)) * (y ⊗ₜ 1) := by simp
    rw [this, hx, hy]; simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_tmul, tmul_add, hx, hy]
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one, smul_tmul]

variable {A B S}

omit [Algebra A B] [IsScalarTower A B S] in
/-- `(b s) ⊗ e = s ⊗ (b e)` in `S ⊗_A E` for `b` mapping into `H⁰(S/A)`. -/
lemma compatibleSMul (hB : ∀ b : B, algebraMap B S b ∈ H0 A S)
    (E : Type*) [AddCommGroup E] [Module A E] [Module B E] [Module S E] [IsScalarTower A S E]
    [IsScalarTower B S E] : CompatibleSMul A B S E := by
  constructor
  intro b s e
  have h1 := congrArg (fun t => (s ⊗ₜ[A] (1 : S)) * t) (hB b)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h1
  have h2 := congrArg (LinearMap.lTensor S ((LinearMap.toSpanSingleton S E e).restrictScalars A)) h1
  simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, one_smul] at h2
  rw [Algebra.smul_def, mul_comm, h2, algebraMap_smul]


/-- **Folder 128, page 20: the multiplicative coboundary is a logarithmic derivative.** For a
unit `u` of `S`, `p₂(u) p₁(u)⁻¹ = 1 + p₁(u)⁻¹ (p₂(u) − p₁(u))` in `S ⊗_A S`, with
`p₁(u) = u ⊗ 1` and `p₂(u) = 1 ⊗ u`: the class `∂_m(u)` is `u⁻¹ ∂_a(u)`, which is why the
square of page 20 does not commute. -/
theorem coboundary_mul_eq (u : Sˣ) :
    ((1 : S) ⊗ₜ[A] (u : S)) * ((↑u⁻¹ : S) ⊗ₜ[A] (1 : S)) =
      1 + ((↑u⁻¹ : S) ⊗ₜ[A] (1 : S)) * ((1 : S) ⊗ₜ[A] (u : S) - (u : S) ⊗ₜ[A] (1 : S)) := by
  simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Units.inv_mul,
    ← Algebra.TensorProduct.one_def]
  abel

/-- `S ⊗_B E ≃ S ⊗_A E` when `B` maps into `H⁰(S/A)` (folder 128, pages 26–27). -/
noncomputable def tensorEquiv (hB : ∀ b : B, algebraMap B S b ∈ H0 A S)
    (E : Type*) [AddCommGroup E] [Module A E] [Module B E] [Module S E] [IsScalarTower A S E]
    [IsScalarTower B S E] [IsScalarTower A B E] : S ⊗[B] E ≃ₗ[S] S ⊗[A] E :=
  haveI := compatibleSMul hB E
  TensorProduct.equivOfCompatibleSMul A B S S E

@[simp] lemma tensorEquiv_tmul (hB : ∀ b : B, algebraMap B S b ∈ H0 A S)
    (E : Type*) [AddCommGroup E] [Module A E] [Module B E] [Module S E] [IsScalarTower A S E]
    [IsScalarTower B S E] [IsScalarTower A B E] (s : S) (e : E) :
    tensorEquiv hB E (s ⊗ₜ e) = s ⊗ₜ e := rfl

/-- **Folder 128, pages 26–27** (the page's bracket, justified by the edition). If `A → B → S`
and `B` maps into `H⁰(S/A)`, the canonical map `S ⊗_A E → S ⊗_B E` is bijective for every
`S`-module `E`: descent data relative to `S/A` and to `S/B` are the same. -/
theorem bijective_mapOfCompatibleSMul (hB : ∀ b : B, algebraMap B S b ∈ H0 A S)
    (E : Type*) [AddCommGroup E] [Module A E] [Module B E] [Module S E] [IsScalarTower A S E]
    [IsScalarTower B S E] [IsScalarTower A B E] :
    Function.Bijective (TensorProduct.mapOfCompatibleSMul B A S S E) :=
  (tensorEquiv hB E).symm.bijective

/-- With `B` mapping into `H⁰(S/A)`, `H⁰(S/B) = H⁰(S/A)`. -/
theorem mem_H0_iff (hB : ∀ b : B, algebraMap B S b ∈ H0 A S) (s : S) :
    s ∈ H0 B S ↔ s ∈ H0 A S := by
  change s ⊗ₜ[B] (1 : S) = 1 ⊗ₜ s ↔ s ⊗ₜ[A] (1 : S) = 1 ⊗ₜ s
  rw [← (tensorEquiv hB S).injective.eq_iff, tensorEquiv_tmul, tensorEquiv_tmul]

end Tensor

end Grothendieck.Folder128.Infinitesimal


/-!
## Pages 14–18, Prop. 2 over a local base: the reduction to `A = k`

The remainder of Prop. 2 (`Colength` above treats the field case only): `A` local artinian with
maximal ideal `𝔪` and residue field `k`, `A'` finite over `A` with trivial residue extensions,
`J` an equivalence ideal with `A → A' ⇉ (A' ⊗_A A')/J` exact and `δ(x')` generating `Δ/J` for
`x' ∉ A`. Here `B` is the reading's `A'`, and the base only needs to be noetherian, with `𝔪` any
maximal ideal under which all the points of `B` lie (`hres`):
* `ColengthLocal.map_le_range`: `𝔪B ⊂ A`, i.e. `𝔪A' = 𝔪`;
* `ColengthLocal.colength_le_one`: moreover `B/A` has length `≤ 1` (`Module.length`), for any
  ideal `J ⊂ Δ`;
* `ColengthLocal.eq_bot_of_length_eq_one`: if `J` is an equivalence ideal (`IsEquivIdeal`) and the
  length is `1`, then `J = 0`;
* `ColengthLocal.prop2`: the three together for `A` local noetherian (so local artinian);
* `ColengthLocal.prop1_i` (Prop. 1 (i), pages 12–13): over any commutative ring `A`, if `A → B`
  is injective and `B/A ≅ A/𝔪`, the equivalence ideals of `B ⊗_A B` are exactly `0` and `Δ`
  (`isEquivIdeal_bot`, `isEquivIdeal_diag`).

The proof does not follow the page's split (radiciel / non radiciel, `J` nilpotent, `Ω = Δ/Δ²`).
(1) `𝔪A' ⊂ A`: if `x ∈ 𝔪A'` were not in `A`, `δ(x) ∈ 𝔪Δ ⊂ 𝔫Δ` for every maximal `𝔫` of `A'`, so
`Δ ⊂ (δx) + J ⊂ J + 𝔫Δ` and `Δ ⊂ J` by Nakayama on `A'`, against exactness. (2) The field
argument of `Colength.finrank_le_two`, run in `B₀ = B/𝔪B` through
`φ_χ : a ⊗ b ↦ χ(a) b̄ : B ⊗_A B → B₀` (`phi`), gives `dim_k B₀ ≤ 2` or `Δ ⊂ J`
(`finrank_le_two_or`); every `t ∈ Δ` is `δ(s)` modulo `𝔫Δ` (`exists_sub_dl_mem`), which replaces
the field case's `t ≡ δ(φ_χ t)`. Then `B/A ≅ B₀/k` has length `≤ 1`. (3) For the last assertion,
the reduction `Θ : B ⊗_A B → B₀ ⊗_k B₀` (`theta`, through `equivOfCompatibleSMul`) has kernel
inside `𝔪(B ⊗_A B)` (right exactness), whose elements are `1 ⊗ μ(t)` since `𝔪B ⊂ A`, so `Θ` is
injective on `Δ` (`eq_zero_of_theta`: Prop. 3 of N° 1 for `I = 𝔪`); `Θ(J)` is an equivalence
ideal (`isEquivalenceIdeal_map`: Cor. 2 in the direction used), `dim_k B₀ = 2`, and
`eq_bot_or_eq_ker` concludes.

Not formalised: Prop. 3 and its corollaries for a general nilpotent conductor ideal `I` (only
`I = 𝔪` with `𝔪A' ⊂ A`, and only the injectivity on `Δ` and the transport of equivalence ideals
from `A'` to `A'₀`, are proved), Prop. 1 (ii) and (iii), and the passage from ideals to closed
subschemes.
-/

namespace Grothendieck.Folder128.ColengthLocal

open Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (𝔪 : Ideal A)

variable (A B) in
/-- `δ(x) = 1 ⊗ x − x ⊗ 1`, `A`-linear. -/
noncomputable def dl : B →ₗ[A] B ⊗[A] B :=
  TensorProduct.mk A B B 1 - (TensorProduct.mk A B B).flip 1

lemma dl_apply (x : B) : dl A B x = (1 : B) ⊗ₜ[A] x - x ⊗ₜ 1 := rfl

variable (A B) in
/-- `Δ = Ker(B ⊗_A B → B)`. -/
noncomputable abbrev diag : Ideal (B ⊗[A] B) :=
  RingHom.ker (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B)

lemma dl_mem (x : B) : dl A B x ∈ diag A B := by
  simp [dl_apply, RingHom.mem_ker]

lemma dl_algebraMap (c : A) : dl A B (algebraMap A B c) = 0 := by
  simp [dl_apply, Algebra.algebraMap_eq_smul_one]

lemma mem_span_dl {t : B ⊗[A] B} (ht : t ∈ diag A B) :
    t ∈ Submodule.span B (Set.range (dl A B)) := by
  rwa [show Set.range (dl A B) = Set.range fun s : B => (1 : B) ⊗ₜ[A] s - s ⊗ₜ 1 from rfl,
    KaehlerDifferential.submodule_span_range_eq_ideal]

/-- A point `χ : B → A/𝔪` kills `𝔪B`. -/
lemma map_le_ker (χ : B →ₐ[A] A ⧸ 𝔪) : 𝔪.map (algebraMap A B) ≤ RingHom.ker χ := by
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.2 hm]

/-- `φ_χ : a ⊗ b ↦ χ(a) b̄ ∈ B/𝔪B`. -/
noncomputable def phi (χ : B →ₐ[A] A ⧸ 𝔪) : B ⊗[A] B →ₐ[A] B ⧸ 𝔪.map (algebraMap A B) :=
  Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom A (A ⧸ 𝔪) _).comp χ)
    (Ideal.Quotient.mkₐ A _) fun _ _ => Commute.all _ _

lemma phi_tmul (χ : B →ₐ[A] A ⧸ 𝔪) (a b : B) :
    phi 𝔪 χ (a ⊗ₜ b) = algebraMap (A ⧸ 𝔪) _ (χ a) * Ideal.Quotient.mk _ b := by
  simp [phi]

lemma phi_dl (χ : B →ₐ[A] A ⧸ 𝔪) (x : B) :
    phi 𝔪 χ (dl A B x) = Ideal.Quotient.mk _ x - algebraMap (A ⧸ 𝔪) _ (χ x) := by
  simp [dl_apply, phi_tmul]

lemma phi_smul (χ : B →ₐ[A] A ⧸ 𝔪) (a : B) (t : B ⊗[A] B) :
    phi 𝔪 χ (a • t) = algebraMap (A ⧸ 𝔪) _ (χ a) * phi 𝔪 χ t := by
  rw [Algebra.smul_def, map_mul, show algebraMap B (B ⊗[A] B) a = a ⊗ₜ 1 from rfl, phi_tmul,
    map_one, mul_one]

/-- `χ̄ : B/𝔪B → A/𝔪`, as an `A/𝔪`-algebra map. -/
noncomputable def chibar (χ : B →ₐ[A] A ⧸ 𝔪) : B ⧸ 𝔪.map (algebraMap A B) →ₐ[A ⧸ 𝔪] A ⧸ 𝔪 :=
  AlgHom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (Ideal.Quotient.liftₐ _ χ fun _ ha => map_le_ker 𝔪 χ ha)

lemma chibar_mk (χ : B →ₐ[A] A ⧸ 𝔪) (b : B) : chibar 𝔪 χ (Ideal.Quotient.mk _ b) = χ b := rfl

lemma chibar_phi (χ : B →ₐ[A] A ⧸ 𝔪) (t : B ⊗[A] B) :
    chibar 𝔪 χ (phi 𝔪 χ t) = χ (Algebra.TensorProduct.lmul' A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [phi_tmul, chibar_mk]
  | add s t hs ht => simp only [map_add, hs, ht]


/-- Every `t ∈ Δ` is `δ(s)` modulo `𝔫 Δ`, for `𝔫 = Ker χ` (residue field `A/𝔪`). -/
lemma exists_sub_dl_mem (χ : B →ₐ[A] A ⧸ 𝔪) {t : B ⊗[A] B} (ht : t ∈ diag A B) :
    ∃ s : B, t - dl A B s ∈ RingHom.ker χ • (diag A B).restrictScalars B := by
  suffices ∀ t ∈ Submodule.span B (Set.range (dl A B)),
      ∃ s : B, t - dl A B s ∈ RingHom.ker χ • (diag A B).restrictScalars B from
    this t (mem_span_dl ht)
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact ⟨s, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx; obtain ⟨s', hs'⟩ := hy
    exact ⟨s + s', by convert add_mem hs hs' using 1; simp only [map_add]; abel⟩
  | smul a x hx' hx =>
    obtain ⟨s, hs⟩ := hx
    have hxD : x ∈ (diag A B).restrictScalars B := by
      rw [← KaehlerDifferential.submodule_span_range_eq_ideal]; exact hx'
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (χ a)
    have hn : a - algebraMap A B c ∈ RingHom.ker χ := by
      simp [RingHom.mem_ker, ← hc]
    refine ⟨c • s, ?_⟩
    have h1 := Submodule.smul_mem_smul hn hxD
    have h2 := Submodule.smul_of_tower_mem _ c hs
    convert add_mem h1 h2 using 1
    rw [map_smul, sub_smul, algebraMap_smul, smul_sub]
    abel

/-- `φ_χ` kills `𝔫 Δ`. -/
lemma phi_eq_zero (χ : B →ₐ[A] A ⧸ 𝔪) {t : B ⊗[A] B}
    (ht : t ∈ RingHom.ker χ • (diag A B).restrictScalars B) : phi 𝔪 χ t = 0 := by
  refine Submodule.smul_induction_on ht (fun r hr n _ => ?_) fun x y hx hy => ?_
  · rw [phi_smul, (RingHom.mem_ker).1 hr, map_zero, zero_mul]
  · rw [map_add, hx, hy, add_zero]

/-- `δ(𝔪B) ⊂ 𝔫 Δ`. -/
lemma dl_mem_smul (χ : B →ₐ[A] A ⧸ 𝔪) {w : B} (hw : w ∈ 𝔪.map (algebraMap A B)) :
    dl A B w ∈ RingHom.ker χ • (diag A B).restrictScalars B := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at hw
  refine Submodule.smul_induction_on hw (fun m hm b _ => ?_) fun x y hx hy => ?_
  · rw [map_smul, ← algebraMap_smul B m (dl A B b)]
    exact Submodule.smul_mem_smul (map_le_ker 𝔪 χ (Ideal.mem_map_of_mem _ hm)) (dl_mem b)
  · rw [map_add]; exact add_mem hx hy


/-- The hypothesis `Δ ⊂ (δ z) + J` read in `B/𝔪B` through `φ_χ`. -/
lemma phi_decomp {J : Ideal (B ⊗[A] B)}
    (hgen : ∀ x : B, x ∉ Set.range (algebraMap A B) → diag A B ≤ Ideal.span {dl A B x} ⊔ J)
    (χ : B →ₐ[A] A ⧸ 𝔪) {z : B ⧸ 𝔪.map (algebraMap A B)} (hz : z ∈ RingHom.ker (chibar 𝔪 χ))
    (hz0 : z ≠ 0) {y : B ⧸ 𝔪.map (algebraMap A B)} (hy : y ∈ RingHom.ker (chibar 𝔪 χ)) :
    ∃ u : B ⊗[A] B, ∃ j ∈ J, phi 𝔪 χ u * z + phi 𝔪 χ j = y := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, chibar_mk] at hz hy
  have hzk : z ∉ Set.range (algebraMap A B) := by
    rintro ⟨c, rfl⟩
    apply hz0
    rw [← Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [AlgHom.commutes] at hz
    have hc : Ideal.Quotient.mk 𝔪 c = 0 := hz
    rw [hc, map_zero]
  obtain ⟨u, j, hj, e⟩ := Ideal.mem_span_singleton_sup.1 (hgen z hzk (dl_mem y))
  refine ⟨u, j, hj, ?_⟩
  have := congr(phi 𝔪 χ $e)
  rw [map_add, map_mul, phi_dl, phi_dl, hz, hy] at this
  simpa using this

/-- The residue fields of `B/𝔪B` are `A/𝔪` when those of `B` are. -/
lemma exists_chibar
    (hres : ∀ n : Ideal B, n.IsMaximal → ∃ χ : B →ₐ[A] A ⧸ 𝔪, RingHom.ker χ = n)
    (m : Ideal (B ⧸ 𝔪.map (algebraMap A B))) (hm : m.IsMaximal) :
    ∃ ψ : B ⧸ 𝔪.map (algebraMap A B) →ₐ[A ⧸ 𝔪] A ⧸ 𝔪, RingHom.ker ψ = m := by
  obtain ⟨χ, hχ⟩ := hres _ (Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (𝔪.map (algebraMap A B))) Ideal.Quotient.mk_surjective (K := m) (H := hm))
  refine ⟨chibar 𝔪 χ, Ideal.ext fun c => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [RingHom.mem_ker, chibar_mk, ← RingHom.mem_ker, hχ, Ideal.mem_comap]

/-- Nakayama on `B`: if `Δ ⊂ J + 𝔫 Δ` at every point, `Δ ⊂ J`. -/
lemma diag_le_of [Module.Finite A B] [IsNoetherianRing A]
    (hres : ∀ n : Ideal B, n.IsMaximal → ∃ χ : B →ₐ[A] A ⧸ 𝔪, RingHom.ker χ = n)
    {J : Ideal (B ⊗[A] B)} (h : ∀ χ : B →ₐ[A] A ⧸ 𝔪, (diag A B).restrictScalars B ≤
      J.restrictScalars B ⊔ RingHom.ker χ • (diag A B).restrictScalars B) :
    diag A B ≤ J := by
  have : IsNoetherian A (B ⊗[A] B) := isNoetherian_of_isNoetherianRing_of_finite A _
  have : IsNoetherian B (B ⊗[A] B) := isNoetherian_of_tower A inferInstance
  have hD := Colength.le_of_forall_le_sup_smul (IsNoetherian.noetherian _) fun n hn => by
    obtain ⟨χ, rfl⟩ := hres n hn
    exact h χ
  exact fun t ht => hD ht

/-- `𝔫 Δ` is an ideal of `B ⊗ B`. -/
lemma mul_mem_smul (χ : B →ₐ[A] A ⧸ 𝔪) (u : B ⊗[A] B) {t : B ⊗[A] B}
    (ht : t ∈ RingHom.ker χ • (diag A B).restrictScalars B) :
    u * t ∈ RingHom.ker χ • (diag A B).restrictScalars B := by
  refine Submodule.smul_induction_on ht (fun r hr n hn => ?_) fun x y hx hy => ?_
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr (Ideal.mul_mem_left _ u hn)
  · rw [mul_add]; exact add_mem hx hy

/-- `𝔪B ⊂ A`: an `x ∈ 𝔪B` outside `A` would have `δ(x) ∈ 𝔫 Δ` at every point, so `Δ ⊂ J` by
Nakayama, and exactness would put `x` in `A`. -/
theorem map_le_range [Module.Finite A B] [IsNoetherianRing A]
    (hres : ∀ n : Ideal B, n.IsMaximal → ∃ χ : B →ₐ[A] A ⧸ 𝔪, RingHom.ker χ = n)
    {J : Ideal (B ⊗[A] B)}
    (hexact : ∀ x : B, dl A B x ∈ J → x ∈ Set.range (algebraMap A B))
    (hgen : ∀ x : B, x ∉ Set.range (algebraMap A B) → diag A B ≤ Ideal.span {dl A B x} ⊔ J)
    {w : B} (hw : w ∈ 𝔪.map (algebraMap A B)) : w ∈ Set.range (algebraMap A B) := by
  by_contra hwA
  refine hwA (hexact w (diag_le_of 𝔪 hres (fun χ t ht => ?_) (dl_mem w)))
  obtain ⟨u, j, hj, e⟩ := Ideal.mem_span_singleton_sup.1 (hgen w hwA ht)
  rw [← e]
  exact add_mem (Submodule.mem_sup_right (mul_mem_smul 𝔪 χ u (dl_mem_smul 𝔪 χ hw)))
    (Submodule.mem_sup_left hj)


/-- The field-case argument run in `B/𝔪B`: either `dim_{A/𝔪} B/𝔪B ≤ 2`, or `Δ ⊂ J`. -/
theorem finrank_le_two_or [𝔪.IsMaximal] [Module.Finite A B] [IsNoetherianRing A]
    (hres : ∀ n : Ideal B, n.IsMaximal → ∃ χ : B →ₐ[A] A ⧸ 𝔪, RingHom.ker χ = n)
    {J : Ideal (B ⊗[A] B)} (hJ : J ≤ diag A B)
    (hgen : ∀ x : B, x ∉ Set.range (algebraMap A B) → diag A B ≤ Ideal.span {dl A B x} ⊔ J) :
    finrank (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) ≤ 2 ∨ diag A B ≤ J := by
  refine or_iff_not_imp_left.2 fun hC => diag_le_of 𝔪 hres fun χ => ?_
  have : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  -- at each point, `J` meets the fibre, so `𝔫_χ/𝔪B ⊂ φ_χ(J)`
  have hfib : ∀ y ∈ RingHom.ker (chibar 𝔪 χ), ∃ f ∈ J, phi 𝔪 χ f = y := by
    by_cases hK : ∃ f ∈ J, phi 𝔪 χ f ≠ 0
    · obtain ⟨f, hf, hf0⟩ := hK
      have hfm : phi 𝔪 χ f ∈ RingHom.ker (chibar 𝔪 χ) := by
        rw [RingHom.mem_ker, chibar_phi, (RingHom.mem_ker).1 (hJ hf), map_zero]
      intro y hy
      obtain ⟨u, j, hj, e⟩ := phi_decomp 𝔪 hgen χ hfm hf0 hy
      exact ⟨u * f + j, J.add_mem (J.mul_mem_left u hf) hj, by rw [map_add, map_mul, e]⟩
    · push Not at hK
      refine (hC ?_).elim
      let := Ideal.Quotient.field 𝔪
      refine Colength.finrank_le_two_of_simple (k := A ⧸ 𝔪) (A := B ⧸ 𝔪.map (algebraMap A B))
        (exists_chibar 𝔪 hres) (chibar 𝔪 χ)
        fun z hz hz0 y hy => ?_
      obtain ⟨u, j, hj, e⟩ := phi_decomp 𝔪 hgen χ hz hz0 hy
      rw [hK j hj, add_zero] at e
      exact Ideal.mem_span_singleton'.2 ⟨_, e⟩
  -- so `δ(x) ∈ J + 𝔫 Δ` for every `x`
  intro t ht
  rw [Submodule.restrictScalars_mem, ← Submodule.restrictScalars_mem B,
    ← KaehlerDifferential.submodule_span_range_eq_ideal] at ht
  refine (Submodule.span_le.2 ?_) ht
  rintro _ ⟨x, rfl⟩
  obtain ⟨f, hf, e⟩ := hfib (Ideal.Quotient.mk _ x - algebraMap (A ⧸ 𝔪) _ (χ x))
    (by simp [RingHom.mem_ker, chibar_mk])
  obtain ⟨s, hs⟩ := exists_sub_dl_mem 𝔪 χ (hJ hf)
  have e2 : phi 𝔪 χ (dl A B s) = phi 𝔪 χ (dl A B x) := by
    rw [phi_dl 𝔪 χ x, ← e, ← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, phi_eq_zero 𝔪 χ hs,
      neg_zero]
  rw [phi_dl, phi_dl] at e2
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (χ x - χ s)
  have hw : x - s - algebraMap A B c ∈ 𝔪.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub,
      ← Ideal.Quotient.algebraMap_quotient_map_quotient, hc, map_sub]
    linear_combination (-1 : B ⧸ 𝔪.map (algebraMap A B)) * e2
  have : (1 : B) ⊗ₜ[A] x - x ⊗ₜ 1 = f - (f - dl A B s) + dl A B (x - s - algebraMap A B c) := by
    rw [map_sub, map_sub, dl_algebraMap, dl_apply, dl_apply]; abel
  change (1 : B) ⊗ₜ[A] x - x ⊗ₜ 1 ∈ _
  rw [this]
  exact add_mem (sub_mem (Submodule.mem_sup_left hf) (Submodule.mem_sup_right hs))
    (Submodule.mem_sup_right (dl_mem_smul 𝔪 χ hw))


/-- `1, z̄` are independent in `B/𝔪B` over `A/𝔪` when `z ∉ A` and `𝔪B ⊂ A`. -/
lemma linearIndependent_one_mk [𝔪.IsMaximal]
    (hI : ∀ w ∈ 𝔪.map (algebraMap A B), w ∈ Set.range (algebraMap A B))
    {z : B} (hz : z ∉ Set.range (algebraMap A B)) :
    let := Ideal.Quotient.field 𝔪
    LinearIndependent (A ⧸ 𝔪) ![1, Ideal.Quotient.mk (𝔪.map (algebraMap A B)) z] := by
  let := Ideal.Quotient.field 𝔪
  have hz' : ∀ c : A ⧸ 𝔪, algebraMap (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) c ≠
      Ideal.Quotient.mk (𝔪.map (algebraMap A B)) z := by
    intro c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq] at hc
    obtain ⟨b, hb⟩ := hI _ hc
    exact hz ⟨a - b, by rw [map_sub, hb]; abel⟩
  have hnt : Nontrivial (B ⧸ 𝔪.map (algebraMap A B)) :=
    ⟨⟨0, Ideal.Quotient.mk _ z, by simpa using hz' 0⟩⟩
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact ⟨(map_eq_zero_iff _ (algebraMap (A ⧸ 𝔪) _).injective).1 hst, rfl⟩
  · refine (hz' (-(t⁻¹ * s)) ?_).elim
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hinv : algebraMap (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) t⁻¹ *
        algebraMap (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) t = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ht, map_one]
    rw [map_neg, map_mul]
    linear_combination (-algebraMap (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) t⁻¹) * hst +
      Ideal.Quotient.mk (𝔪.map (algebraMap A B)) z * hinv

/-- `B = A + A z` for every `z ∉ A`, once `𝔪B ⊂ A` and `dim_{A/𝔪} B/𝔪B ≤ 2`. -/
lemma exists_sub_smul_mem [𝔪.IsMaximal]
    (hI : ∀ w ∈ 𝔪.map (algebraMap A B), w ∈ Set.range (algebraMap A B))
    [Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B))]
    (h2 : finrank (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) ≤ 2)
    {z : B} (hz : z ∉ Set.range (algebraMap A B)) (y : B) :
    ∃ a : A, y - a • z ∈ Set.range (algebraMap A B) := by
  let := Ideal.Quotient.field 𝔪
  have mk_alg (a : A) : Ideal.Quotient.mk (𝔪.map (algebraMap A B)) (algebraMap A B a) =
      algebraMap (A ⧸ 𝔪) _ (Ideal.Quotient.mk 𝔪 a) :=
    (Ideal.Quotient.algebraMap_quotient_map_quotient a).symm
  have hli := linearIndependent_one_mk 𝔪 hI hz
  have htop : Submodule.span (A ⧸ 𝔪) (Set.range ![1, Ideal.Quotient.mk (𝔪.map (algebraMap A B)) z])
      = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact h2
  have hy := htop ▸ Submodule.mem_top (x := Ideal.Quotient.mk (𝔪.map (algebraMap A B)) y)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
  rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero] at hc
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (c 0)
  obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (c 1)
  refine ⟨a₁, ?_⟩
  have hw : y - a₁ • z - algebraMap A B a₀ ∈ 𝔪.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, ← hc, ← ha₀, ← ha₁, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, map_mul, mk_alg, mk_alg, mul_one]
    ring
  obtain ⟨b, hb⟩ := hI _ hw
  exact ⟨b + a₀, by rw [map_add, hb]; abel⟩


/-- **Folder 128, Prop. 2, first assertion, over a noetherian base** (Grothendieck, pages
14–18). Let `𝔪` be a maximal ideal of a noetherian ring `A`, `B` a finite `A`-algebra (the page's
`A'`) every maximal ideal of which is the kernel of an `A`-algebra map `B → A/𝔪` (all lie over
`𝔪`, with trivial residue extensions), and `J ⊂ Δ` an ideal of `B ⊗_A B` such that
* (exactness of `A → B ⇉ (B ⊗_A B)/J`) `δ(x) ∈ J` only for `x ∈ A`;
* (`δ(x)` generates `Δ/J`) `Δ ⊂ (δ(x)) + J` for every `x ∉ A`.
Then `𝔪B ⊂ A` (so `𝔪B = 𝔪` when `A → B` is injective) and `B/A` has length `≤ 1`.
Neither symmetry nor transitivity of `J` is used. -/
theorem colength_le_one [𝔪.IsMaximal] [Module.Finite A B] [IsNoetherianRing A]
    (hres : ∀ n : Ideal B, n.IsMaximal → ∃ χ : B →ₐ[A] A ⧸ 𝔪, RingHom.ker χ = n)
    {J : Ideal (B ⊗[A] B)} (hJ : J ≤ diag A B)
    (hexact : ∀ x : B, dl A B x ∈ J → x ∈ Set.range (algebraMap A B))
    (hgen : ∀ x : B, x ∉ Set.range (algebraMap A B) → diag A B ≤ Ideal.span {dl A B x} ⊔ J) :
    (∀ w ∈ 𝔪.map (algebraMap A B), w ∈ Set.range (algebraMap A B)) ∧
      Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≤ 1 := by
  have hI := fun w (hw : w ∈ 𝔪.map (algebraMap A B)) => map_le_range 𝔪 hres hexact hgen hw
  refine ⟨hI, ?_⟩
  have : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  -- `B = A + A z` for every `z ∉ A`
  have key : ∀ z : B, z ∉ Set.range (algebraMap A B) → ∀ y : B,
      ∃ a : A, y - a • z ∈ Set.range (algebraMap A B) := by
    rcases finrank_le_two_or 𝔪 hres hJ hgen with h2 | hD
    · exact fun z hz y => exists_sub_smul_mem 𝔪 hI h2 hz y
    · exact fun z hz => (hz (hexact z (hD (dl_mem z)))).elim
  set Q := B ⧸ LinearMap.range (Algebra.linearMap A B)
  have hmem (x : B) : x ∈ LinearMap.range (Algebra.linearMap A B) ↔
      x ∈ Set.range (algebraMap A B) := by simp [Set.mem_range]
  by_cases hQ : Subsingleton Q
  · rw [Module.length_eq_zero_iff.2 hQ]; exact zero_le_one
  rw [not_subsingleton_iff_nontrivial] at hQ
  have : IsSimpleOrder (Submodule A Q) := ⟨fun N => by
    refine or_iff_not_imp_left.2 fun hN => ?_
    obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hz : z ∉ Set.range (algebraMap A B) := fun h =>
      hq0 ((Submodule.Quotient.mk_eq_zero _).2 ((hmem z).2 h))
    refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨a, ha⟩ := key z hz y
    have : Submodule.Quotient.mk (p := LinearMap.range (Algebra.linearMap A B)) y =
        a • Submodule.Quotient.mk z := by
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, ← neg_sub, neg_mem_iff]
      exact (hmem _).2 ha
    rw [this]
    exact N.smul_mem a hq⟩
  have : IsSimpleModule A Q := ⟨⟩
  rw [Module.length_eq_one_iff.2 this]

/-!
### Prop. 2, last assertion: reduction modulo `𝔪` (Prop. 3 and Cor. 2 of N° 1)
-/

variable (A B) in
/-- `p₁₂ : a ⊗ b ↦ a ⊗ b ⊗ 1`, over `A`. -/
noncomputable abbrev q12 : B ⊗[A] B →ₐ[A] (B ⊗[A] B) ⊗[A] B :=
  Algebra.TensorProduct.includeLeft

variable (A B) in
/-- `p₁₃ : a ⊗ b ↦ a ⊗ 1 ⊗ b`, over `A`. -/
noncomputable abbrev q13 : B ⊗[A] B →ₐ[A] (B ⊗[A] B) ⊗[A] B :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft (AlgHom.id A B)

variable (A B) in
/-- `p₂₃ : a ⊗ b ↦ 1 ⊗ a ⊗ b`, over `A`. -/
noncomputable abbrev q23 : B ⊗[A] B →ₐ[A] (B ⊗[A] B) ⊗[A] B :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id A B)

/-- An equivalence ideal of `B ⊗_A B` over any commutative ring `A` (as `IsEquivalenceIdeal`
over a field). -/
structure IsEquivIdeal (I : Ideal (B ⊗[A] B)) : Prop where
  /-- Reflexivity: `I ⊂ Δ`. -/
  refl : I ≤ diag A B
  /-- Symmetry: `I` is stable under `a ⊗ b ↦ b ⊗ a`. -/
  symm : ∀ t ∈ I, Algebra.TensorProduct.comm A B B t ∈ I
  /-- Transitivity: `p₁₃(I) ⊂ p₁₂(I) + p₂₃(I)`. -/
  trans : I.map (q13 A B) ≤ I.map (q12 A B) ⊔ I.map (q23 A B)

/-- Scalars of `A/𝔪` pass across `⊗_A` on `B/𝔪B`. -/
instance compatibleSMul : CompatibleSMul A (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B))
    (B ⧸ 𝔪.map (algebraMap A B)) where
  smul_tmul c m n := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    change (algebraMap A (A ⧸ 𝔪) a • m) ⊗ₜ n = m ⊗ₜ (algebraMap A (A ⧸ 𝔪) a • n)
    rw [algebraMap_smul, algebraMap_smul, smul_tmul]

/-- Reduction modulo `𝔪`: `Θ : B ⊗_A B → B₀ ⊗_k B₀`, `B₀ = B/𝔪B`, `k = A/𝔪`. -/
noncomputable def theta : B ⊗[A] B →ₐ[A]
    (B ⧸ 𝔪.map (algebraMap A B)) ⊗[A ⧸ 𝔪] (B ⧸ 𝔪.map (algebraMap A B)) :=
  (Algebra.TensorProduct.equivOfCompatibleSMul (A ⧸ 𝔪) A A _ _).toAlgHom.comp
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A _) (Ideal.Quotient.mkₐ A _))

lemma theta_tmul (a b : B) :
    theta 𝔪 (a ⊗ₜ b) = Ideal.Quotient.mk _ a ⊗ₜ Ideal.Quotient.mk _ b := rfl

/-- `Θ₃ : B ⊗_A B ⊗_A B → B₀ ⊗_k B₀ ⊗_k B₀`. -/
noncomputable def theta3 : (B ⊗[A] B) ⊗[A] B →ₐ[A]
    ((B ⧸ 𝔪.map (algebraMap A B)) ⊗[A ⧸ 𝔪] (B ⧸ 𝔪.map (algebraMap A B))) ⊗[A ⧸ 𝔪]
      (B ⧸ 𝔪.map (algebraMap A B)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft (R := A ⧸ 𝔪) (S := A ⧸ 𝔪)).restrictScalars A).comp
      (theta 𝔪))
    (((Algebra.TensorProduct.includeRight (R := A ⧸ 𝔪)).restrictScalars A).comp
      (Ideal.Quotient.mkₐ A _))
    fun _ _ => Commute.all (S := ((B ⧸ 𝔪.map (algebraMap A B)) ⊗[A ⧸ 𝔪]
      (B ⧸ 𝔪.map (algebraMap A B))) ⊗[A ⧸ 𝔪] (B ⧸ 𝔪.map (algebraMap A B))) _ _

lemma theta_surjective : Function.Surjective (theta 𝔪 : B ⊗[A] B → _) :=
  (Algebra.TensorProduct.equivOfCompatibleSMul (A ⧸ 𝔪) A A _ _).surjective.comp
    (Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective
      Ideal.Quotient.mk_surjective)

lemma theta_comm (t : B ⊗[A] B) : theta 𝔪 (Algebra.TensorProduct.comm A B B t) =
    Algebra.TensorProduct.comm (A ⧸ 𝔪) _ _ (theta 𝔪 t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add s t hs ht => simp only [map_add, hs, ht]

lemma theta_lmul (t : B ⊗[A] B) : Algebra.TensorProduct.lmul' (A ⧸ 𝔪) (theta 𝔪 t) =
    Ideal.Quotient.mk _ (Algebra.TensorProduct.lmul' A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [theta_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- `Ker Θ ⊂ 𝔪 (B ⊗_A B)` (right exactness of `⊗`). -/
lemma ker_theta_le {t : B ⊗[A] B} (ht : theta 𝔪 t = 0) :
    t ∈ 𝔪.map (algebraMap A (B ⊗[A] B)) := by
  have h0 : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A (𝔪.map (algebraMap A B)))
      (Ideal.Quotient.mkₐ A (𝔪.map (algebraMap A B))) t = 0 :=
    (Algebra.TensorProduct.equivOfCompatibleSMul (A ⧸ 𝔪) A A _ _).injective (by
      rw [map_zero]; exact ht)
  rw [← RingHom.mem_ker, Algebra.TensorProduct.map_ker _ _ Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective] at h0
  have hIK (f : B →ₐ[A] B ⊗[A] B) :
      𝔪.map (algebraMap A B) ≤ (𝔪.map (algebraMap A (B ⊗[A] B))).comap f :=
    Ideal.map_le_iff_le_comap.2 fun m hm => by
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hm
  refine (sup_le (Ideal.map_le_iff_le_comap.2 fun b hb => hIK _ ?_)
    (Ideal.map_le_iff_le_comap.2 fun b hb => hIK _ ?_)) h0 <;>
    exact Ideal.Quotient.eq_zero_iff_mem.1 hb

/-- Prop. 3 of N° 1 for `I = 𝔪`: when `𝔪B ⊂ A`, every `t ∈ 𝔪 (B ⊗_A B)` is `1 ⊗ μ(t)`, so
`Δ ∩ 𝔪 (B ⊗_A B) = 0`. -/
lemma eq_tmul_lmul (hI : ∀ w ∈ 𝔪.map (algebraMap A B), w ∈ Set.range (algebraMap A B))
    {t : B ⊗[A] B} (ht : t ∈ 𝔪.map (algebraMap A (B ⊗[A] B))) :
    t = 1 ⊗ₜ Algebra.TensorProduct.lmul' A t := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at ht
  refine Submodule.smul_induction_on ht (fun m hm s hs => ?_) fun x y hx hy => ?_
  · clear hs
    induction s using TensorProduct.inductionOn with
    | tmul a b =>
      have hma : m • a ∈ 𝔪.map (algebraMap A B) := by
        rw [Algebra.smul_def]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm)
      obtain ⟨c, hc⟩ := hI _ hma
      rw [smul_tmul', ← hc, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.algebraMap_eq_smul_one,
        smul_tmul, smul_mul_assoc, one_mul]
    | add s₁ s₂ h₁ h₂ => rw [smul_add, map_add, tmul_add, ← h₁, ← h₂]
  · rw [map_add, tmul_add, ← hx, ← hy]

/-- `Θ` is injective on `Δ` once `𝔪B ⊂ A` (Prop. 3 of N° 1: `Δ ≅ Δ₀`). -/
lemma eq_zero_of_theta (hI : ∀ w ∈ 𝔪.map (algebraMap A B), w ∈ Set.range (algebraMap A B))
    {t : B ⊗[A] B} (htD : t ∈ diag A B) (ht : theta 𝔪 t = 0) : t = 0 := by
  rw [eq_tmul_lmul 𝔪 hI (ker_theta_le 𝔪 ht), (RingHom.mem_ker).1 htD, tmul_zero]

section Field

variable [𝔪.IsMaximal]

attribute [local instance] Ideal.Quotient.field

lemma theta_dl (x : B) :
    theta 𝔪 (dl A B x) = Colength.delta (A ⧸ 𝔪) _ (Ideal.Quotient.mk _ x) := by
  rw [dl_apply, map_sub, theta_tmul, theta_tmul, map_one, Colength.delta_apply]

lemma theta3_q12 (t : B ⊗[A] B) : theta3 𝔪 (q12 A B t) = p12 (A ⧸ 𝔪) _ (theta 𝔪 t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [theta3, theta_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

lemma theta3_q13 (t : B ⊗[A] B) : theta3 𝔪 (q13 A B t) = p13 (A ⧸ 𝔪) _ (theta 𝔪 t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [theta3, theta_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

lemma theta3_q23 (t : B ⊗[A] B) : theta3 𝔪 (q23 A B t) = p23 (A ⧸ 𝔪) _ (theta 𝔪 t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [theta3, theta_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- Cor. 2 of N° 1 in the direction used: the reduction `Θ(J)` of an equivalence ideal is an
equivalence ideal of `B₀ ⊗_k B₀`. -/
lemma isEquivalenceIdeal_map {J : Ideal (B ⊗[A] B)} (hJ : IsEquivIdeal J) :
    IsEquivalenceIdeal (J.map (theta 𝔪)) where
  refl := Ideal.map_le_iff_le_comap.2 fun j hj => by
    rw [Ideal.mem_comap, RingHom.mem_ker, theta_lmul, (RingHom.mem_ker).1 (hJ.refl hj), map_zero]
  symm t ht := by
    obtain ⟨j, hj, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ (theta_surjective 𝔪)).1 ht
    rw [← theta_comm]
    exact Ideal.mem_map_of_mem _ (hJ.symm j hj)
  trans := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Ideal.mem_comap, ← theta3_q13]
    have h := Ideal.mem_map_of_mem (theta3 𝔪) (hJ.trans (Ideal.mem_map_of_mem (q13 A B) hj))
    refine (Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)) h <;>
      refine Ideal.map_le_iff_le_comap.2 fun i hi => ?_ <;>
      rw [Ideal.mem_comap, Ideal.mem_comap]
    · rw [theta3_q12]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hi))
    · rw [theta3_q23]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hi))

/-- **Folder 128, Prop. 2, last assertion, over a noetherian base** (pages 14–18): under the
hypotheses of `colength_le_one`, if `J` is moreover an equivalence ideal and `B/A` has length
`1`, then `J = 0`, i.e. `(B ⊗_A B)/J = B ⊗_A B`. The proof is the page's reduction: `𝔪B ⊂ A`, so
`Θ : B ⊗_A B → B₀ ⊗_k B₀` is injective on `Δ` (Prop. 3 of N° 1), `Θ(J)` is an equivalence ideal
(Cor. 2), `dim_k B₀ = 2`, and `eq_bot_or_eq_ker` leaves `Θ(J) = 0` or `Θ(J) = Δ₀`; the second
would put `δ(z)` in `J` for some `z ∉ A`. -/
theorem eq_bot_of_length_eq_one [Module.Finite A B] [IsNoetherianRing A]
    (hres : ∀ n : Ideal B, n.IsMaximal → ∃ χ : B →ₐ[A] A ⧸ 𝔪, RingHom.ker χ = n)
    {J : Ideal (B ⊗[A] B)} (hJ : IsEquivIdeal J)
    (hexact : ∀ x : B, dl A B x ∈ J → x ∈ Set.range (algebraMap A B))
    (hgen : ∀ x : B, x ∉ Set.range (algebraMap A B) → diag A B ≤ Ideal.span {dl A B x} ⊔ J)
    (h1 : Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) = 1) : J = ⊥ := by
  have hI := fun w (hw : w ∈ 𝔪.map (algebraMap A B)) => map_le_range 𝔪 hres hexact hgen hw
  obtain ⟨z, hz⟩ : ∃ z : B, z ∉ Set.range (algebraMap A B) := by
    by_contra! h
    have : Subsingleton (B ⧸ LinearMap.range (Algebra.linearMap A B)) :=
      subsingleton_of_forall_eq 0 fun q => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        obtain ⟨c, hc⟩ := h y
        exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, hc⟩
    rw [Module.length_eq_zero_iff.2 this] at h1
    exact zero_ne_one h1
  have : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have h2 : finrank (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) = 2 := by
    rcases finrank_le_two_or 𝔪 hres hJ.refl hgen with h | hD
    · refine le_antisymm h ?_
      simpa using (linearIndependent_one_mk 𝔪 hI hz).fintype_card_le_finrank
    · exact absurd (hexact z (hD (dl_mem z))) hz
  rcases eq_bot_or_eq_ker h2 (isEquivalenceIdeal_map 𝔪 hJ) with h0 | hD0
  · refine eq_bot_iff.2 fun j hj => (Ideal.mem_bot).2 (eq_zero_of_theta 𝔪 hI (hJ.refl hj) ?_)
    rw [← Ideal.mem_bot, ← h0]
    exact Ideal.mem_map_of_mem _ hj
  · have hzJ : theta 𝔪 (dl A B z) ∈ J.map (theta 𝔪) := by
      rw [hD0, theta_dl]; exact Colength.delta_mem _
    obtain ⟨j, hj, e⟩ := (Ideal.mem_map_iff_of_surjective _ (theta_surjective 𝔪)).1 hzJ
    have := eq_zero_of_theta 𝔪 hI (sub_mem (hJ.refl hj) (dl_mem z)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero] at this
    exact (hz (hexact z (this ▸ hj))).elim

end Field

/-- **Folder 128, Prop. 2, as stated** (Grothendieck, pages 14–18), for `A` local noetherian (in
particular local artinian) with maximal ideal `𝔪` and residue field `k = A/𝔪`, `B` (the page's
`A'`) a finite `A`-algebra with trivial residue extensions, and `J` an equivalence ideal of
`B ⊗_A B` such that `A → B ⇉ (B ⊗_A B)/J` is exact and `δ(x)` generates `Δ/J` for every
`x ∉ A`: `𝔪B ⊂ A`, `B/A` has length `≤ 1`, and if the length is `1` then `J = 0`. -/
theorem prop2 [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A B]
    (hres : ∀ n : Ideal B, n.IsMaximal →
      ∃ χ : B →ₐ[A] A ⧸ IsLocalRing.maximalIdeal A, RingHom.ker χ = n)
    {J : Ideal (B ⊗[A] B)} (hJ : IsEquivIdeal J)
    (hexact : ∀ x : B, dl A B x ∈ J → x ∈ Set.range (algebraMap A B))
    (hgen : ∀ x : B, x ∉ Set.range (algebraMap A B) → diag A B ≤ Ideal.span {dl A B x} ⊔ J) :
    (∀ w ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B), w ∈ Set.range (algebraMap A B)) ∧
      Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≤ 1 ∧
      (Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) = 1 → J = ⊥) :=
  have h := colength_le_one _ hres hJ.refl hexact hgen
  ⟨h.1, h.2, eq_bot_of_length_eq_one _ hres hJ hexact hgen⟩

end Grothendieck.Folder128.ColengthLocal

namespace Grothendieck.Folder128.ColengthLocal

open Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (𝔪 : Ideal A)

/-- `0` is an equivalence ideal of `B ⊗_A B`. -/
theorem isEquivIdeal_bot : IsEquivIdeal (⊥ : Ideal (B ⊗[A] B)) where
  refl := bot_le
  symm t ht := by rw [Ideal.mem_bot.1 ht, map_zero]; exact zero_mem _
  trans := by rw [Ideal.map_bot]; exact bot_le

/-- `Δ` is an equivalence ideal of `B ⊗_A B`. -/
theorem isEquivIdeal_diag : IsEquivIdeal (diag A B) where
  refl := le_rfl
  symm t ht := RingHom.mem_ker.2 <| (LinearMap.mul'_comm (R := A) t).trans ht
  trans := by
    rw [show diag A B = _ from (KaehlerDifferential.span_range_eq_ideal A B).symm,
      Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    rw [show q13 A B ((1 : B) ⊗ₜ[A] s - s ⊗ₜ 1) =
        q12 A B ((1 : B) ⊗ₜ[A] s - s ⊗ₜ 1) + q23 A B ((1 : B) ⊗ₜ[A] s - s ⊗ₜ 1) by
      simp [sub_tmul]]
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)))

section Field

variable [𝔪.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/-- **Folder 128, Prop. 1 (i)** (Grothendieck, pages 12–13), over any commutative ring: if
`A → B` is injective and `B/A ≅ A/𝔪` as `A`-modules, the equivalence ideals of `B ⊗_A B` are
exactly `0` and `Δ`. The page's reduction: `𝔪B ⊂ A`, `Θ` is injective on `Δ` (Prop. 3 of N° 1),
`Θ(J)` is an equivalence ideal of `B₀ ⊗_k B₀` with `dim_k B₀ = 2` (Cor. 2), and
`eq_bot_or_eq_ker` is the case `A = k`. -/
theorem prop1_i (e : (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≃ₗ[A] A ⧸ 𝔪)
    {J : Ideal (B ⊗[A] B)} : IsEquivIdeal J ↔ J = ⊥ ∨ J = diag A B := by
  refine ⟨fun hJ => ?_, by rintro (rfl | rfl); exacts [isEquivIdeal_bot, isEquivIdeal_diag]⟩
  have hmem : ∀ x : B, x ∈ LinearMap.range (Algebra.linearMap A B) ↔
      x ∈ Set.range (algebraMap A B) := fun x => by simp [Set.mem_range]
  have hmk : ∀ x : B, e (Submodule.Quotient.mk x) = 0 → x ∈ Set.range (algebraMap A B) :=
    fun x hx => (hmem x).1 ((Submodule.Quotient.mk_eq_zero _).1
      (e.injective (hx.trans (map_zero e).symm)))
  -- `𝔪B ⊂ A`, since `𝔪` kills `B/A ≅ A/𝔪`
  have hI : ∀ w ∈ 𝔪.map (algebraMap A B), w ∈ Set.range (algebraMap A B) := by
    intro w hw
    rw [← hmem]
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at hw
    refine Submodule.smul_induction_on hw (fun m hm b _ => (hmem _).2 (hmk _ ?_))
      fun x y hx hy => add_mem hx hy
    rw [Submodule.Quotient.mk_smul, map_smul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hm, zero_mul]
  obtain ⟨z, hz1⟩ := Submodule.Quotient.mk_surjective _ (e.symm 1)
  have hz1' : e (Submodule.Quotient.mk z) = 1 := by rw [hz1, e.apply_symm_apply]
  have hz : z ∉ Set.range (algebraMap A B) := fun h => by
    have := hz1'
    rw [(Submodule.Quotient.mk_eq_zero _).2 ((hmem z).2 h), map_zero] at this
    exact zero_ne_one this
  -- `B₀ = k ⊕ k z̄`
  have hli := linearIndependent_one_mk 𝔪 hI hz
  have hsp : ⊤ ≤ Submodule.span (A ⧸ 𝔪)
      (Set.range ![1, Ideal.Quotient.mk (𝔪.map (algebraMap A B)) z]) := by
    intro q _
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk y))
    obtain ⟨c, hc⟩ := hmk (y - a • z) (by
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hz1', ← ha,
        Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, sub_self])
    rw [show y = algebraMap A B c + a • z by rw [hc]; abel, map_add, Algebra.smul_def, map_mul,
      ← Ideal.Quotient.algebraMap_quotient_map_quotient,
      ← Ideal.Quotient.algebraMap_quotient_map_quotient, Algebra.algebraMap_eq_smul_one,
      ← Algebra.smul_def]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bas := Basis.mk hli hsp
  have : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) := Module.Finite.of_basis bas
  have h2 : finrank (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) = 2 := by
    rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]
  rcases eq_bot_or_eq_ker h2 (isEquivalenceIdeal_map 𝔪 hJ) with h0 | hD0
  · refine Or.inl (eq_bot_iff.2 fun j hj => (Ideal.mem_bot).2
      (eq_zero_of_theta 𝔪 hI (hJ.refl hj) ?_))
    rw [← Ideal.mem_bot, ← h0]
    exact Ideal.mem_map_of_mem _ hj
  · refine Or.inr (le_antisymm hJ.refl fun d hd => ?_)
    have hdJ : theta 𝔪 d ∈ J.map (theta 𝔪) := by
      rw [hD0, RingHom.mem_ker, theta_lmul, (RingHom.mem_ker).1 hd, map_zero]
    obtain ⟨j, hj, hjd⟩ := (Ideal.mem_map_iff_of_surjective _ (theta_surjective 𝔪)).1 hdJ
    have := eq_zero_of_theta 𝔪 hI (sub_mem hd (hJ.refl hj)) (by rw [map_sub, hjd, sub_self])
    rw [sub_eq_zero] at this
    exact this ▸ hj

end Field

end Grothendieck.Folder128.ColengthLocal

/-!
## Page 7: the example « `S/IS` faithfully flat over `A/I` »

The reading's example for Cor. 1: if `S/IS` is faithfully flat over `A/I`, then
`Spec S → Spec A` is an effective descent morphism for flat modules. What is needed is faithfully
flat descent of modules, proved here directly on the comodules `DescentDatum`, not through
mathlib's comonadicity (`ModuleCat.comonadicExtendScalars`).

* `DescentDatum.bijective_of_flat`: for `R → S` flat, `S ⊗_R E^ψ → E` is bijective for every
  datum. By the cocycle condition `ψ(e)` lies in the kernel of `S ⊗ (ψ − 1 ⊗ ·)`, which is
  `S ⊗ E^ψ` since `S` is flat; this factors `ψ` through `S ⊗ E^ψ ↪ S ⊗ E`, and the counit makes
  the factorisation inverse to `S ⊗ E^ψ → E`;
* `isEffectiveDescentFlat_of_faithfullyFlat`: a faithfully flat `R → S` is an effective descent
  morphism for flat modules (`E^ψ` is flat by descent of flatness,
  `Module.Flat.of_flat_tensorProduct`; `M → S ⊗ M` is injective, and onto the invariants by the
  previous point applied to the canonical datum);
* `isEffectiveDescentFlat_of_quotient_faithfullyFlat`: the example, by Cor. 1.
-/

namespace Grothendieck.Folder128.Descent

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {E : Type u} [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]

namespace DescentDatum

/-- For `R → S` flat, `S ⊗_R E^ψ → E` is bijective for every descent datum. -/
theorem bijective_of_flat [Module.Flat R S] (d : DescentDatum R S E) :
    Function.Bijective (LinearMap.liftBaseChange S d.invariants.subtype) := by
  set j := d.invariants.subtype.lTensor S
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hex : Function.Exact j ((d.ψ.restrictScalars R - TensorProduct.mk R S E 1).lTensor S) :=
    Module.Flat.lTensor_exact S fun e => by simp [sub_eq_zero, mem_invariants]
  refine ⟨fun x y hxy => hj ?_, fun e => ?_⟩
  · have key : ∀ t, j t = d.ψ (LinearMap.liftBaseChange S d.invariants.subtype t) := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul b x => simp [j, (mem_invariants d).1 x.2, smul_tmul']
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [key, key, hxy]
  · have hμ : ∀ t, LinearMap.liftBaseChange S d.invariants.subtype t =
        LinearMap.liftBaseChange S LinearMap.id (j t) := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul b x => simp [j]
      | add x y hx hy => simp only [map_add, hx, hy]
    obtain ⟨t, ht⟩ := (hex (d.ψ e)).1 (by simp [d.coassoc])
    exact ⟨t, (hμ t).trans ((congrArg _ ht).trans (d.counit e))⟩

end DescentDatum

/-- If `S ⊗ ι` has an injective left inverse and `S` is faithfully flat, `ι` is onto. -/
lemma surjective_of_section [Module.FaithfullyFlat R S] {M P : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] (ι : M →ₗ[R] P) (θ : S ⊗[R] P → S ⊗[R] M)
    (hθ : Function.Injective θ) (h : ∀ y, θ (ι.lTensor S y) = y) : Function.Surjective ι :=
  (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S ι).1
    fun z => ⟨θ z, hθ (h (θ z))⟩

/-- **Faithfully flat descent of modules.** A faithfully flat `R → S` is an effective descent
morphism for flat modules. -/
theorem isEffectiveDescentFlat_of_faithfullyFlat [Module.FaithfullyFlat R S] :
    IsEffectiveDescentFlat R S := by
  refine ⟨fun M _ _ _ => ⟨Module.FaithfullyFlat.tensorProduct_mk_injective M, ?_⟩,
    fun E _ _ _ _ _ d => ⟨?_, d.bijective_of_flat⟩⟩
  · intro x hx
    let ι : M →ₗ[R] (canonical R S M).invariants := (TensorProduct.mk R S M 1).codRestrict _
      fun m => by simp [DescentDatum.mem_invariants, canonical]
    obtain ⟨m, hm⟩ := surjective_of_section (S := S) (M := M)
      (P := (canonical R S M).invariants) ι _ (canonical R S M).bijective_of_flat.1
      (fun y => by
        induction y using TensorProduct.inductionOn with
        | tmul b m =>
          change b • ((1 : S) ⊗ₜ[R] m) = _
          rw [smul_tmul', smul_eq_mul, mul_one]
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]) ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · have := Module.Flat.of_linearEquiv (LinearEquiv.ofBijective _ d.bijective_of_flat)
    exact Module.Flat.of_flat_tensorProduct R _ S

/-- **Folder 128, the example of Cor. 1** (Grothendieck, page 7). Let `I` be a nilpotent ideal of
`A` mapped isomorphically onto an ideal of `S`. If `S/IS` is faithfully flat over `A/I`, then
`Spec S → Spec A` is an effective descent morphism for flat modules. -/
theorem isEffectiveDescentFlat_of_quotient_faithfullyFlat {A S : Type u} [CommRing A]
    [CommRing S] [Algebra A S] {I : Ideal A} (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    [Module.FaithfullyFlat (A ⧸ I) (S ⧸ I.map (algebraMap A S))] : IsEffectiveDescentFlat A S :=
  isEffectiveDescentFlat_of_quotient h hI isEffectiveDescentFlat_of_faithfullyFlat

end Grothendieck.Folder128.Descent
