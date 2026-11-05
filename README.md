# Bigon-free dichotomy for combinatorial pseudoline arrangements

Lean 4 formalization, prepared for the [Palomar Registry](https://palomar-registry.org/).

A combinatorial arrangement of pseudolines in the real projective plane (a generalised map with
flags labelled by lines) in which no line carries fewer than three vertices is four lines in
general position, or contains five lines in general position, a pencil of three and a pencil of
two without the line joining their centres, or the complete quadrangle.

- `Challenge.lean`: the statement, `BigonFreeDichotomy.PseudolineMap.map_dichotomy`, with its definitions.
- `Solution.lean` and `BigonFreeDichotomy/Dichotomy.lean`: the proof, with the same definitions.
- `comparator.json`, `formalization.yaml`: the Comparator configuration and the metadata.

The statement is the boxed one of page 24 of folder 80 of the working notes of Alexandre
Grothendieck (University of Montpellier). The proof is the one of the section on pseudoline
arrangements in [Hua, 2026](https://hexagonmath.org/2611.00125v1). Submissions to the registry
go through https://submit.palomar-registry.org/.

Part of the work of the project
[grothendieck-project](https://github.com/Commutator-IO/grothendieck-project), whose Lean files
are under CC0; this repository is under Apache-2.0.
