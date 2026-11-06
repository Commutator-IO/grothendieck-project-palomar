module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Sober

public section


/-!
# Folder 41, Proposition 1 (page 11): continuity of the generic section and openness

The modernised reading `transcripts/41/41.modern.tex` (manuscript page 11) states:

> **Proposition 1.** Soit `f : X → Y` un morphisme de type fini dont les fibres
> sont irréductibles et non vides, et soit `φ(y)` le point générique de `X_y`.
> On considère les conditions :
> (i) `φ : Y → X` est continue ;
> (ii) `f` est ouvert ;
> (iii) `y ∈ \overline{\{y'\}} ⟹ φ(y) ∈ \overline{\{φ(y')\}}` ;
> (iii bis) pour tous `y ∈ \overline{\{y'\}}` et `x` au-dessus de `y`, il existe
> `x'` au-dessus de `y'` tel que `x ∈ \overline{\{x'\}}`.
> Alors (i) ⟺ (ii) sans autre hypothèse, et (ii) ⟹ (iii) ⟺ (iii bis) ; si `f`
> est localement de présentation finie — par exemple `Y` localement noethérien —,
> les quatre conditions sont équivalentes.
>
> *Démonstration.* … `φ⁻¹(U) = f(U)` …

What is proved, as the reading states it:

* `SectionGenerique f φ` encodes « `φ(y)` est le point générique de la fibre
  irréductible non vide `X_y` » on the underlying spaces: `φ(y)` lies over `y`
  and specialises to every point of `f⁻¹(y)`. `sectionGenerique_iff` checks that
  this is exactly: `φ(y)` is a generic point of the fibre `f⁻¹(y)` with its
  induced topology. (The fibre of a morphism of schemes is homeomorphic to this
  subspace; that identification is not re-proved here.)
* `preimage_eq_image` — the page's formula `φ⁻¹(U) = f(U)` for `U` open.
* `i_iff_ii`, `i_imp_iii`, `iii_iff_iiibis` — « (i) ⟺ (ii) sans autre
  hypothèse, et (ii) ⟹ (iii) ⟺ (iii bis) », for arbitrary topological spaces:
  no hypothesis on `f` at all, not even continuity.
* `proposition1` — for a morphism of schemes locally of finite presentation, the
  four conditions are equivalent. The one step that needs the hypothesis,
  (iii bis) ⟹ (ii), is mathlib's `AlgebraicGeometry.isOpenMap_of_generalizingMap`
  (Stacks 01U1, the reading's EGA IV 1.10.4); the rest is the topology above.
* `iiibis_not_imp_ii` — the finiteness hypothesis is not decoration: already for
  topological spaces, (iii bis) does not imply (ii). The identity map from `ℕ`
  discrete to `ℕ` with the cofinite topology has singleton fibres, lifts
  generizations (both spaces are T1), and is not open.

**What the formalisation finds.** Nothing false and no missing hypothesis. The
reading places the finiteness hypothesis exactly where it is needed, and « sans
autre hypothèse » is true in the strongest sense: (i) ⟺ (ii) and
(i) ⟹ (iii) ⟺ (iii bis) hold for any map of topological spaces with a
generic-point section. The rest of the folder (monogenic sections,
representability of the space of components, the theorem of page 8) is not
formalised: mathlib has neither geometric irreducibility of fibres nor the
valuative criteria in the form used.

What this certifies is that the reading holds together at this point, not that
it is what the page says (issue #26).
-/

namespace Grothendieck.Folder41

open Topology

section Topologie

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `φ(y)` is the generic point of the (irreducible, non-empty) fibre `f⁻¹(y)`:
it lies over `y` and specialises to every point over `y`. -/
def SectionGenerique (f : X → Y) (φ : Y → X) : Prop :=
  ∀ y, f (φ y) = y ∧ ∀ x, f x = y → φ y ⤳ x

omit [TopologicalSpace Y] in
/-- The encoding is faithful: `φ(y)` is a generic point of the fibre `f⁻¹(y)`
with its induced topology. -/
theorem sectionGenerique_iff (f : X → Y) (φ : Y → X) :
    SectionGenerique f φ ↔ ∀ y, ∃ h : f (φ y) = y,
      IsGenericPoint (⟨φ y, h⟩ : f ⁻¹' {y}) Set.univ := by
  simp only [SectionGenerique, isGenericPoint_iff_specializes, subtype_specializes_iff,
    Set.mem_univ, iff_true, Subtype.forall, Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun h y => ⟨(h y).1, (h y).2⟩, fun h y => ⟨(h y).1, (h y).2⟩⟩

variable {f : X → Y} {φ : Y → X} (hφ : SectionGenerique f φ)
include hφ

omit [TopologicalSpace Y] in
/-- **The page's formula** `φ⁻¹(U) = f(U)`, for `U` open. -/
theorem preimage_eq_image {U : Set X} (hU : IsOpen U) : φ ⁻¹' U = f '' U := by
  refine Set.ext fun y => ⟨fun hy => ⟨φ y, hy, (hφ y).1⟩, ?_⟩
  rintro ⟨x, hx, rfl⟩
  exact ((hφ (f x)).2 x rfl).mem_open hU hx

/-- **(i) ⟺ (ii).** `φ` is continuous if and only if `f` is open. -/
theorem i_iff_ii : Continuous φ ↔ IsOpenMap f := by
  rw [continuous_def]
  exact ⟨fun h U hU => preimage_eq_image hφ hU ▸ h U hU,
    fun h U hU => (preimage_eq_image hφ hU).symm ▸ h U hU⟩

omit hφ in
/-- **(i) ⟹ (iii).** A continuous map preserves specialisation. -/
theorem i_imp_iii (h : Continuous φ) : ∀ y y', y' ⤳ y → φ y' ⤳ φ y :=
  fun _ _ hy => hy.map h

/-- **(iii) ⟺ (iii bis).** `φ` preserves specialisation if and only if `f`
lifts generizations. -/
theorem iii_iff_iiibis : (∀ y y', y' ⤳ y → φ y' ⤳ φ y) ↔ GeneralizingMap f := by
  refine ⟨fun h x y' hy' => ⟨φ y', (h _ _ hy').trans ((hφ (f x)).2 x rfl), (hφ y').1⟩,
    fun h y y' hy' => ?_⟩
  obtain ⟨x', hx', hfx'⟩ := h (show y' ⤳ f (φ y) by rw [(hφ y).1]; exact hy')
  exact ((hφ y').2 x' hfx').trans hx'

end Topologie

section Schemas

open AlgebraicGeometry

/-- **Proposition 1.** For a morphism of schemes locally of finite presentation
whose fibres are irreducible and non-empty with generic points `φ(y)`, the four
conditions (i), (ii), (iii), (iii bis) are equivalent. -/
theorem proposition1 {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (φ : Y → X)
    (hφ : SectionGenerique f φ) :
    List.TFAE [Continuous φ, IsOpenMap f, ∀ y y', y' ⤳ y → φ y' ⤳ φ y, GeneralizingMap f] := by
  tfae_have 1 ↔ 2 := i_iff_ii hφ
  tfae_have 1 → 3 := i_imp_iii
  tfae_have 3 ↔ 4 := iii_iff_iiibis hφ
  tfae_have 4 → 2 := isOpenMap_of_generalizingMap f
  tfae_finish

end Schemas

section Contreexemple

/-- **The finiteness hypothesis is needed.** For topological spaces, (iii bis)
does not imply (ii): the identity from `ℕ` (discrete) to `ℕ` with the cofinite
topology has singleton fibres, lifts generizations, and is not open. -/
theorem iiibis_not_imp_ii :
    SectionGenerique (CofiniteTopology.of : ℕ → CofiniteTopology ℕ) CofiniteTopology.of.symm ∧
      GeneralizingMap (CofiniteTopology.of : ℕ → CofiniteTopology ℕ) ∧
      ¬ IsOpenMap (CofiniteTopology.of : ℕ → CofiniteTopology ℕ) := by
  refine ⟨fun y => ⟨by simp, fun x hx => by rw [← hx]; simp⟩, fun x y' hy' => ?_, fun h => ?_⟩
  · exact ⟨x, specializes_rfl, (specializes_iff_eq.1 (hy' : y' ⤳ CofiniteTopology.of x)).symm⟩
  · have hopen := h {0} (isOpen_discrete _)
    rw [Set.image_singleton, CofiniteTopology.isOpen_iff'] at hopen
    have : Infinite (CofiniteTopology ℕ) :=
      Infinite.of_injective _ CofiniteTopology.of.injective
    rcases hopen with h0 | hfin
    · exact Set.singleton_ne_empty _ h0
    · exact (Set.finite_singleton _).infinite_compl hfin

end Contreexemple

end Grothendieck.Folder41
