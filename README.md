# Lean proofs of the statements of Grothendieck's working notes

Lean 4 formalization, prepared for the [Palomar Registry](https://palomar-registry.org/), of the
paper [Hua, 2026, Hexagon 2611.00125](https://hexagonmath.org/2611.00125v1), « Énoncés des notes
de travail de Grothendieck démontrés en Lean 4, et questions ouvertes ». The library has one
file per folder of the working notes of Alexandre Grothendieck kept at the University of
Montpellier, and the general lemmas they use, in `Grothendieck/Upstream/`.

Palomar compares one statement per entry. The Challenge is a headline statement of the paper:
a combinatorial arrangement of pseudolines in the real projective plane (a generalised map with
flags labelled by lines) in which no line carries fewer than three vertices is four lines in
general position, or contains five lines in general position, a pencil of three and a pencil of
two in which none of these five lines joins the two centres, or the complete quadrangle.

- `Challenge.lean`: the statement, `Grothendieck.Folder80Maps2.PseudolineMap.map_dichotomy`, with its definitions.
- `Solution.lean` and `Grothendieck/Folder80Maps2.lean`: the proof of the Challenge; the other files of `Grothendieck/` are the other proofs of the paper, built with it.
- `comparator.json`, `formalization.yaml`: the Comparator configuration and the metadata.

The statement is the boxed one of page 24 of folder 80 of the working notes of Alexandre
Grothendieck (University of Montpellier). The proof is the one of the section on pseudoline
arrangements in [Hua, 2026](https://hexagonmath.org/2611.00125v1). Submissions to the registry
go through https://submit.palomar-registry.org/.

Part of the work of the project
[grothendieck-project](https://github.com/Commutator-IO/grothendieck-project), whose Lean files
are under CC0; this repository is under Apache-2.0.
