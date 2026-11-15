module

public import Mathlib
public import Grothendieck.Folder94
public import StacksFrontier.RingTheory.Koszul.Regular

@[expose] public section


/-!
# Folder 94, pages 8–9: the Koszul step of Lemme 6

Finding `94-generic-tor-regular-sequences`. Lemme 6 of the reading asks for a dense open
`U ⊆ Spec A` such that `Tor_i^A(R, A_𝔭/(t)) = 0` for `i > 0`, `𝔭 ∈ U` and every `A_𝔭`-regular
sequence `t`. `Grothendieck/Folder94.lean` proves the regularity half
(`exists_isOpen_dense_isWeaklyRegular'`: `t` is then `R_𝔭`-weakly regular) and leaves the
Koszul step — from `R`-regularity to the vanishing of the higher homology — unformalised, since
mathlib has no Koszul complexes of sequences.

This file supplies that step with the vendored AxiomMath/Stacks files
`StacksFrontier/RingTheory/Koszul/Defs.lean` and `.../Koszul/Regular.lean`: the Koszul complex
`K_•(t)` of a finite sequence `t : Fin r → B` (with `K_i = ⋀ⁱ Bʳ`), the notions
`Koszul.IsKoszulRegularOn t M` (`H_i(K_•(t) ⊗ M) = 0` for `i ≠ 0`, Stacks tag 062E (1)) and
`Koszul.IsKoszulRegular t` (`H_i(K_•(t)) = 0` for `i ≠ 0`, tag 062E (3)), and the theorem that an
`M`-weakly regular sequence is `M`-Koszul-regular (`isKoszulRegularOn_and_isKoszulRegular_of_regular`,
tag 062F).

**What is proved.**
* `exists_isOpen_dense_isKoszulRegularOn` (Lemme 6, Koszul form): for `A` noetherian, `J`
  nilpotent with `A/J` reduced and `R` a finite `A`-module, there is a dense open `U ⊆ Spec A`
  such that for `𝔭 ∈ U` and every sequence `t` of `A_𝔭` weakly regular on `A_𝔭`, both
  `H_i(K_•(t)) = 0` and `H_i(K_•(t) ⊗ R_𝔭) = 0` for all `i > 0`.

Since `K_•(t)` is a complex of finite free `A_𝔭`-modules with `H_0 = A_𝔭/(t)` and, by the first
vanishing, no higher homology, it is a free resolution of `A_𝔭/(t)`; the groups
`H_i(K_•(t) ⊗ R_𝔭)` are therefore `Tor_i^{A_𝔭}(R_𝔭, A_𝔭/(t))`, and the second vanishing is the
statement of the page. That last identification with mathlib's derived-functor `Tor` (and
`H_0(K_•(t)) ≅ A_𝔭/(t)`) is not formalised here; the vanishing is stated for Koszul homology.
-/

namespace Grothendieck.Folder94Koszul

open RingTheory.Sequence Grothendieck.Folder94

variable {A : Type*} [CommRing A] [IsNoetherianRing A] {J : Ideal A}

/-- **Lemme 6, the Koszul step.** On the dense open `U` of `exists_isOpen_dense_isWeaklyRegular'`,
every sequence `t` of `A_𝔭` that is weakly regular on `A_𝔭` has an acyclic Koszul complex, and
its Koszul complex on `R_𝔭` has no homology in positive degrees: `Tor_i(R_𝔭, A_𝔭/(t)) = 0` for
`i > 0`, read through the Koszul resolution. -/
theorem exists_isOpen_dense_isKoszulRegularOn {n : ℕ} (hn : J ^ n = ⊥) [IsReduced (A ⧸ J)]
    (R : Type*) [AddCommGroup R] [Module A R] [Module.Finite A R] :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ Dense U ∧
      ∀ 𝔭 ∈ U, ∀ (r : ℕ) (t : Fin r → Localization.AtPrime 𝔭.asIdeal),
        IsWeaklyRegular (Localization.AtPrime 𝔭.asIdeal) (List.ofFn t) →
          Koszul.IsKoszulRegular t ∧
            Koszul.IsKoszulRegularOn t (LocalizedModule 𝔭.asIdeal.primeCompl R) := by
  obtain ⟨U, hU, hd, H⟩ := exists_isOpen_dense_isWeaklyRegular' hn R
  refine ⟨U, hU, hd, fun 𝔭 h𝔭 r t ht => ⟨?_, ?_⟩⟩
  · exact (Koszul.isKoszulRegularOn_self_iff t).mp
      ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (M := Localization.AtPrime 𝔭.asIdeal) (f := t)).1 ht)
  · exact (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
      (M := LocalizedModule 𝔭.asIdeal.primeCompl R) (f := t)).1 (H 𝔭 h𝔭 _ ht)

end Grothendieck.Folder94Koszul

#print axioms Grothendieck.Folder94Koszul.exists_isOpen_dense_isKoszulRegularOn
