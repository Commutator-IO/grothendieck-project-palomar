# Lean proofs of the statements of Grothendieck's working notes

Lean 4 formalization, prepared for the [Palomar Registry](https://palomar-registry.org/), of the
paper [Hua, 2026, Hexagon 2611.00125](https://hexagonmath.org/2611.00125v1), « Grothendieck
Montpellier. Énoncés des lectures modernisées démontrés. ». The library has one
file per folder of the working notes of Alexandre Grothendieck kept at the University of
Montpellier, and the general lemmas they use, in `Grothendieck/Upstream/`.

The Challenge has one headline statement per folder file, listed in `CHALLENGE.md`. The one that
names the entry is the bigon-free dichotomy: a combinatorial arrangement of pseudolines in the real projective plane (a generalised map with
flags labelled by lines) in which no line carries fewer than three vertices is four lines in
general position, or contains five lines in general position, a pencil of three and a pencil of
two in which none of these five lines joins the two centres, or the complete quadrangle.

- `Challenge.lean`: one headline theorem per file of `Grothendieck/`, stated with `sorry` together with the definitions it depends on, copied verbatim, in a single file that imports only Mathlib; `CHALLENGE.md` lists the choices, and the section from `Folder80Maps2` is the dichotomy above.
- `Solution.lean` and `Grothendieck/`: the proofs of the challenged theorems, one file per folder, with the general lemmas in `Grothendieck/Upstream/`.
- `comparator.json`, `formalization.yaml`: the Comparator configuration and the metadata.

The dichotomy is the boxed statement of page 24 of folder 80 of the working notes of Alexandre
Grothendieck (University of Montpellier). The proof is the one of the section on pseudoline
arrangements in [Hua, 2026](https://hexagonmath.org/2611.00125v1). Submissions to the registry
go through https://submit.palomar-registry.org/.

Part of the work of the project
[grothendieck-project](https://github.com/Commutator-IO/grothendieck-project), whose Lean files
are under CC0; this repository is under Apache-2.0.
