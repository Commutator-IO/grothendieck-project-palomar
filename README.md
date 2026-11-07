# The tangent line at a marked point on M_{0,n}: Lean proofs

Lean 4 formalization, prepared for the [Palomar Registry](https://palomar-registry.org/), of the
two theorems cited by the article « The tangent line at a marked point on M_{0,n}/S_{n-1}, after
a table of Grothendieck » (Michel Hua, submitted to Hexagon on 7 November 2026). They belong to
the Lean appendix of the paper [Hua, 2026, Hexagon 2611.00125](https://hexagonmath.org/2611.00125v1),
« Grothendieck Montpellier. Énoncés des lectures modernisées démontrés. ».

The Challenge states, in a homogeneous model of M_{0,n} (configurations of n vectors of K² giving
distinct points of the projective line, and functions of weight on them), that the line bundle
L = L_1 ⊗ … ⊗ L_n has order n − 1 for the action of the symmetric group S_n (`trivL_iff`), and
that the tangent line L_n at the last marked point has order (n − 1)(n − 2) for the action of
S_{n−1} (`trivLi_iff`), over any field with the relevant primitive roots of unity.

- `Challenge.lean`: the two statements, `Grothendieck.Folder146.trivL_iff` and `Grothendieck.Folder146.trivLi_iff`, with their definitions, in a single file that imports only Mathlib; `CHALLENGE.md` describes them.
- `Solution.lean` and `Grothendieck/Folder146.lean`: the proofs; the other files of `Grothendieck/` are the other proofs of the paper, built with them.
- `comparator.json`, `formalization.yaml`: the Comparator configuration and the metadata.

The question comes from the table of page 70 of folder 146 of the working notes of Alexandre
Grothendieck (University of Montpellier), which gives these orders for four points and only
guesses for five and six. Submissions to the registry go through https://submit.palomar-registry.org/.

Part of the work of the project
[grothendieck-project](https://github.com/Commutator-IO/grothendieck-project), whose Lean files
are under CC0; this repository is under Apache-2.0.
