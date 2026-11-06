module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section


/-!
# Folder 125: the chain of equivalences of feuillet 2, and the lemma of feuillet 3

The modernised reading `transcripts/125/125.modern.tex` is a map, not a proof:
feuillet 2 lists statements joined by double arrows, and almost everything on
it lives in the cohomology of projective varieties, their formal completions
and Serre duality, none of which mathlib has. What can be checked is the part
of the map that is *formal*, and one lemma of the annotated typescript. This
file is therefore a **partial** formalisation, and says so statement by
statement.

## 1. Premier étage ⇔ deuxième étage (feuillet 2)

The reading states, from the long exact sequence of local cohomology
`⋯ → H^p_Y(X,F) → H^p(X,F) → H^p(X-Y,F) → H^{p+1}_Y(X,F) → ⋯`:

> **Premier étage.** `H^p(X - Y, F) = 0` pour `p ⩾ m`.
>
> **Deuxième étage.** `H^p_Y(X,F) → H^p(X,F)` bijectif pour `p > m`,
> surjectif pour `p = m`. C'est le premier étage lu à travers la suite exacte.

`etage1_iff_etage2` proves that the two are equivalent for **any** long exact
sequence indexed by `ℕ`, with exactly these bounds. Nothing about `X`, `Y` or
`F` is used: "lu à travers la suite exacte" is literally true.

## 2. Deuxième étage ⇔ troisième étage (the arrow marked « dualité »)

> **Troisième étage.** `Ext^q(F̂, Ω̂^r) ← Ext^q(F, Ω^r)` bijectif pour `q < r - m`,
> injectif pour `q = r - m`. … Les bornes se répondent comme il faut :
> `p ⩾ m` d'un côté, `q < r - m` de l'autre, et `p + q = r`.

Serre duality itself is out of reach. Taking it as given — the Ext map in
degree `q = r - p` is the transpose of `H^p_Y → H^p` — `etage2_iff_etage3`
proves the correspondence of bounds over any field. It pins down which bounds
answer which: `p > m` (bijective) ↔ `q < r - m` (bijective), and `p = m`
(surjective) ↔ `q = r - m` (injective).

**What this finds (a slip in the gloss, not in the map).** The reading's
sentence pairs `p ⩾ m` with `q < r - m`. Under `p + q = r` these do not
correspond: `p ⩾ m` is `q ⩽ r - m`. The first étage's range `p ⩾ m` matches
the *whole* range of the third étage, its bijective part `q < r - m` together
with its injective boundary `q = r - m`. The displayed statements of the three
étages are consistent with each other; only the sentence about them is off by
the boundary case.

## 3. The lemma of feuillet 3 (typescript III-18)

> si un homomorphisme de faisceaux cohérents induit un isomorphisme sur les
> germes en un point, il en induit un sur tout un voisinage. … `u : A^n → B` …
> il existe un voisinage ouvert `V` de `y` tel que la restriction `u|V` soit un
> isomorphisme … puisque `Y` est noethérien et `B` de type fini par hypothèse.

`lemme_III18` is the affine form: `Y = Spec R`, `R` Noetherian, `B` a finite
`R`-module, `u : Rⁿ → B` bijective at the prime `𝔭`; then `u` is bijective over
a basic open `D(f) ∋ 𝔭`. This is the statement on an affine neighbourhood of
`y`, which is where the typescript's argument takes place. The passage from
there to a sheaf on a Noetherian scheme is not formalised.

**What this finds.** The lemma is already in mathlib, as
`Module.FinitePresentation.exists_notMem_bijective`, in a more general form:
the source need only be finite and the target *finitely presented*, over any
commutative ring. The marginal annotation is exactly the right justification —
Noetherian plus finite type is what makes `B` finitely presented
(`Module.finitePresentation_of_finite`), which is what makes the kernel of `u`
coherent — and it is used for nothing else. `lemme_III18_general` records the
general form.

What this certifies is that the reading holds together at these points, not
that it is what the pages say (issue #26).
-/

namespace Grothendieck.Folder125

section LongExactSequence

/-! ### The long exact sequence of local cohomology, abstractly

`L p` stands for `H^p_Y(X,F)`, `G p` for `H^p(X,F)`, `C p` for `H^p(X-Y,F)`;
`a`, `b`, `δ` are the three maps of the sequence, exact at every term. -/

variable {L G C : ℕ → Type*} [∀ p, AddCommGroup (L p)] [∀ p, AddCommGroup (G p)]
  [∀ p, AddCommGroup (C p)]
  (a : ∀ p, L p →+ G p) (b : ∀ p, G p →+ C p) (δ : ∀ p, C p →+ L (p + 1))

/-- **Premier étage ⇔ deuxième étage.** In a long exact sequence
`⋯ → L p → G p → C p → L (p+1) → ⋯`, the terms `C p` vanish for all `p ⩾ m` if and
only if `L p → G p` is bijective for `p > m` and surjective for `p = m`. -/
theorem etage1_iff_etage2
    (exG : ∀ p, Function.Exact (a p) (b p))
    (exC : ∀ p, Function.Exact (b p) (δ p))
    (exL : ∀ p, Function.Exact (δ p) (a (p + 1))) (m : ℕ) :
    (∀ p, m ≤ p → ∀ c : C p, c = 0) ↔
      (∀ p, m < p → Function.Bijective (a p)) ∧ Function.Surjective (a m) := by
  -- Surjectivity of `a p` for `p ⩾ m` follows from `C p = 0`.
  have surj (h : ∀ p, m ≤ p → ∀ c : C p, c = 0) (p : ℕ) (hp : m ≤ p) :
      Function.Surjective (a p) := fun y => (exG p y).1 (h p hp _)
  constructor
  · intro h
    refine ⟨fun p hp => ⟨?_, surj h p hp.le⟩, surj h m le_rfl⟩
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨c, rfl⟩ := (exL q x).1 hx
    rw [h q (by omega) c, map_zero]
  · rintro ⟨hbij, hsurj⟩ p hp c
    have hsurj' : Function.Surjective (a p) :=
      hp.lt_or_eq.elim (fun hp => (hbij p hp).2) fun e => e ▸ hsurj
    -- `δ p c` is killed by the injective map `a (p+1)`, so `c` comes from `G p` …
    have hδ : δ p c = 0 :=
      (hbij (p + 1) (by omega)).1 (((exL p _).2 ⟨c, rfl⟩).trans (map_zero _).symm)
    obtain ⟨y, rfl⟩ := (exC p c).1 hδ
    -- … and `G p` is the image of `L p`, which `b p` kills.
    obtain ⟨x, rfl⟩ := hsurj' y
    exact (exG p _).2 ⟨x, rfl⟩

end LongExactSequence

section Duality

/-! ### The duality arrow

Over a field `k`, with `Ext^{r-p}` identified with the dual of `H^p` (Serre
duality, taken as given), the Ext comparison map in degree `q = r - p` is the
transpose `(a p).dualMap`. -/

variable {k : Type*} [Field k] {L G : ℕ → Type*} [∀ p, AddCommGroup (L p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module k (L p)] [∀ p, Module k (G p)]
  (a : ∀ p, L p →ₗ[k] G p)

/-- **Deuxième étage ⇔ troisième étage.** For `m ⩽ r`: `a p` is bijective for
`m < p ⩽ r` and surjective for `p = m` if and only if its transpose, which sits in
degree `q = r - p`, is bijective for `q < r - m` and injective for `q = r - m`. -/
theorem etage2_iff_etage3 {m r : ℕ} (hmr : m ≤ r) :
    ((∀ p, m < p → p ≤ r → Function.Bijective (a p)) ∧ Function.Surjective (a m)) ↔
      ((∀ q, q < r - m → Function.Bijective (a (r - q)).dualMap) ∧
        Function.Injective (a (r - (r - m))).dualMap) := by
  have hm : r - (r - m) = m := by omega
  rw [hm, LinearMap.dualMap_injective_iff]
  refine and_congr_left fun _ => ⟨fun h q hq => ?_, fun h p hp hpr => ?_⟩
  · exact LinearMap.dualMap_bijective_iff.2 (h _ (by omega) (by omega))
  · have := h (r - p) (by omega)
    rwa [LinearMap.dualMap_bijective_iff, show r - (r - p) = p by omega] at this

/-- The correspondence of bounds under `p + q = r`: the first étage's range
`p ⩾ m` is `q ⩽ r - m`, not `q < r - m`. The strict inequality on the Ext side
answers `p > m`. -/
theorem bornes {m r p q : ℕ} (hmr : m ≤ r) (hpq : p + q = r) :
    (m ≤ p ↔ q ≤ r - m) ∧ (m < p ↔ q < r - m) := by
  omega

end Duality

section FeuilletIII18

variable {R : Type*} [CommRing R]

/-- The general form, in mathlib: over any commutative ring, a map from a finite
module to a finitely presented one that is bijective at a prime `𝔭` is bijective
over some `D(f)` with `f ∉ 𝔭`. -/
theorem lemme_III18_general {M B : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup B] [Module R B] [Module.Finite R M] [Module.FinitePresentation R B]
    (u : M →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) :=
  Module.FinitePresentation.exists_notMem_bijective u p
    (LocalizedModule.mkLinearMap p.primeCompl M) (LocalizedModule.mkLinearMap p.primeCompl B)
    hu

/-- **Feuillet 3 (III-18), affine form.** `R` Noetherian, `B` of finite type,
`u : Rⁿ → B` an isomorphism on the germs at `𝔭`: then `u` is an isomorphism over
a neighbourhood `D(f)` of `𝔭`. -/
theorem lemme_III18 [IsNoetherianRing R] {B : Type*} [AddCommGroup B] [Module R B]
    [Module.Finite R B] {n : ℕ} (u : (Fin n → R) →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) :=
  have := Module.finitePresentation_of_finite R B
  lemme_III18_general u p hu

end FeuilletIII18

end Grothendieck.Folder125
