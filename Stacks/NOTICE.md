# Vendored files from AxiomMath/Stacks

The Lean files under `StacksCore/` and `StacksFrontier/` in this directory are copied from
**AxiomMath/Stacks**, <https://github.com/AxiomMath/Stacks>, a Lean formalization of the Stacks
Project built on Mathlib.

- Licence: Licensed under the Apache License 2.0; not covered by this repository's CC0 waiver.
  The licence text is in `LICENSE` next to this file, copied verbatim from the upstream
  repository.
- Date of the copy: 2026-11-15, from the upstream default branch. The copy was taken without its
  git history, so it does not record its commit; the head of the default branch reported by
  `git ls-remote https://github.com/AxiomMath/Stacks HEAD` on that day was
  `c496df0d9beea9deaeabcea8492605f9a0a2313b`.
- Upstream pins Lean v4.35.0 and Mathlib v4.35.0. This project builds the copies against its own
  pin (Lean v4.35.0-rc4, Mathlib `715a03a90adf491de40fbec8b456c179a623435f`).

## What is copied

Only the import closure of the declarations used by this project's proofs, at the upstream module
paths, so that `import StacksCore.…` and `import StacksFrontier.…` resolve (libraries
`StacksCore` and `StacksFrontier` in `lean/lakefile.toml`, with `srcDir = "Stacks"`). Sixteen
files:

| File | Used for |
|---|---|
| `StacksCore/Tactic/StacksAttribute.lean`, `StacksCore/Tactic/EgaSgaAttribute.lean` | the `@[stacks]`, `@[ega]`, `@[sga]` attributes and `add_to_stacks`, kept rather than stripped |
| `StacksFrontier/RingTheory/FormallySmooth/Topological.lean` | `RingHom.FormallySmoothNAdic` (tag 07NI) |
| `StacksFrontier/RingTheory/MvPowerSeries/HomExt.lean` | `powerSeries_hom_ext` |
| `StacksFrontier/CategoryTheory/Triangulated/KGroup/Defs.lean` | `Pretriangulated.K0` (tag 0FCN) |
| `StacksFrontier/CategoryTheory/Abelian/GrothendieckGroup.lean` | `KZero` (tag 02MU) |
| `StacksCore/CategoryTheory/Abelian/SerreClass/Basic.lean`, `.../SerreClass/Weak.lean` | imported by the next file |
| `StacksFrontier/Algebra/Homology/DerivedCategory/KGroup.lean` | `DerivedCategory.Bounded.exists_addEquiv_K0` (tag 0FCP) |
| `StacksFrontier/RingTheory/Koszul/Defs.lean`, `Relations.lean`, `Cone.lean`, `HomotopyCofiber.lean`, `Regular.lean` | Koszul complexes, `IsKoszulRegularOn`, `IsKoszulRegular` (tag 062E), `isKoszulRegularOn_and_isKoszulRegular_of_regular` (tag 062F) |
| `StacksFrontier/LinearAlgebra/ExteriorAlgebra/Prod.lean`, `StacksFrontier/LinearAlgebra/SymmetricPower/Presentation.lean` | imported by the Koszul files |

The users are `lean/Grothendieck/Folder22Adic.lean`, `lean/Grothendieck/Folder94Koszul.lean` and
`lean/Grothendieck/IhesSGA6_2_3Db.lean`.

## Modifications

None. Every copied file is byte-identical to its upstream version: all of them elaborate
against this project's Mathlib pin without change, and the attribute files are vendored, so no
attribute had to be stripped. If a file is ever changed here, it must carry at its top the line
`-- Modified from AxiomMath/Stacks (<path>), <date>: <what changed>. Apache-2.0.` and be listed
in this section.
