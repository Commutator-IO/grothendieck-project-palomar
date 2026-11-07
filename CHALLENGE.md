# The Challenge: the bigon-free dichotomy

The Challenge states the theorem of `Grothendieck/Folder80Maps2.lean` cited by the article
« A bigon-free dichotomy for pseudoline arrangements, after a note of Grothendieck » (submitted
to Hexagon on 7 November 2026), which belongs to the Lean appendix of
[Hua, 2026](https://hexagonmath.org/2611.00125v1).

`Challenge.lean`, a single file that imports only Mathlib so that it compiles on its own, copies
verbatim and under the same names the definitions and structures the statement depends on and
states the theorem with `sorry`; `Solution.lean` imports `Grothendieck.Folder80Maps2`, which
proves it, and `comparator.json` lists the theorem and the definitions that Comparator checks.

| File | Lean name | Statement | Source |
|---|---|---|---|
| `Folder80Maps2.lean` | `Grothendieck.Folder80Maps2.PseudolineMap.map_dichotomy` | A bigon-free combinatorial pseudoline arrangement is II_4 or contains II_5, II'_{3,2} or the complete quadrangle III_6 | folder 80, pages 20 and 24, boxed statement; main theorem of the article |

## The model

A combinatorial arrangement of pseudolines (`PseudolineMap`) is a generalised map (`GMap`:
flags with three fixed-point-free involutions `a0`, `a1`, `a2`, `a0` and `a2` commuting, `a0 a2`
fixed-point-free) with flags labelled by lines, constant on edges; a line through a vertex has
there the four flags of two edge-ends; each line is connected; every vertex is on two lines; two
lines meet at exactly one vertex; the Euler characteristic is `1`. `BigonFree` says every line
carries at least three vertices; `IsII4`, `HasII5`, `HasII32` and `HasIII6` are the four
configurations of the conclusion. The map axioms are weaker than the page's (going straight
through a vertex is not assumed), so the theorem is stronger than the page's. Not formalised:
the ordering of the pseudolines, the near-pencil corollary, and the passage from a topological
arrangement to its map.
