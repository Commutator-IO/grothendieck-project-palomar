# The Challenge: the orders of the tangent line bundles on M_{0,n}

The Challenge states the two theorems of `Grothendieck/Folder146.lean` cited by the article
« The tangent line at a marked point on M_{0,n}/S_{n-1}, after a table of Grothendieck »
(submitted to Hexagon on 7 November 2026), which belong to the Lean appendix of
[Hua, 2026](https://hexagonmath.org/2611.00125v1).

`Challenge.lean`, a single file that imports only Mathlib so that it compiles on its own, copies
verbatim and under the same names the definitions the statements depend on (`br`, `lin`, `Conf`,
`TrivL`, `TrivLi`) and states the two theorems with `sorry`; `Solution.lean` imports
`Grothendieck.Folder146`, which proves them, and `comparator.json` lists the theorems and the
definitions that Comparator checks.

| File | Lean name | Statement | Source |
|---|---|---|---|
| `Folder146.lean` | `Grothendieck.Folder146.trivL_iff` | Over a field with a primitive (n − 1)-th root of unity, n ≥ 2, L^{⊗m} (L = L_1 ⊗ … ⊗ L_n) has an S_n-equivariant trivialisation on M_{0,n} iff (n − 1) divides m | folder 146, page 70, the column for L; elementary version of Theorem 1 (2) of the article |
| `Folder146.lean` | `Grothendieck.Folder146.trivLi_iff` | Over a field with primitive roots of unity of orders n − 1 and n − 2, n ≥ 3, L_n^{⊗m} has an S_{n−1}-equivariant trivialisation on M_{0,n} iff (n − 1)(n − 2) divides m | folder 146, page 70, the column for L_i; elementary version of Theorem 1 (1) of the article |

## The model

A point of the projective line over K is a nonzero vector of K² up to a scalar; n vectors give
n distinct points iff all the brackets [v_i v_j] = v_i1 v_j2 − v_i2 v_j1, i ≠ j, are nonzero
(`Conf`). An equivariant trivialisation of L^{⊗m} (`TrivL`) is a function F of such
configurations, nowhere zero, of weight t_i^{2m} when v_i is multiplied by t_i, of weight
det(g)^{mn} under g in GL_2(K), and invariant under relabelling the points. For L_n^{⊗m}
(`TrivLi`), the n-th point p is singled out, the weights are s^{2m} in p, t_i^{2m} in the
others and det(g)^m, and F is invariant under the permutations of the other n − 1 points. The
function F is not required to be regular. Not formalised: the dictionary between equivariant
line bundles on M_{0,n} and such functions, that is, the identification of the equivariant
Picard group with the first cohomology of the symmetric group with values in the units.
