# GST finite multi-center blowup: exact Hodge defect conservation

- **Date:** 2026-10-20
- **Kind:** constructive-geometry discriminator; proved rational linear algebra; canonical geometry conditional on the genuine blowup comparison
- **Research program:** rational Hodge classes on every arbitrary original smooth projective complex X
- **Source commit:** `6bab60dd552204b4d1771430b38ed9a735edf3dc`
- **Kernel verification:** GitHub Actions `39406055021`, success at descendant `985f6ff14b155032f6388de0f19e81209da2a3a8`; Graph V2 CM NM Geometry Upgrade compiled `GSTGraphV2SelfExpandingCosmology` among the Lean roots
- **Review:** exact algebra and self-audit; no independent classical scheme-level formalization claim

## Construction and exact statement

Given a rational-linear canonical cycle-class map `b : N_B → H_B` on an actual smooth projective base and one `c : N_Y → H_Y` for each copy of a smooth center, an r-center blowup with pairwise disjoint centers and matching shifted source/target types has its canonical comparison in the genuinely split Chow/Betti coordinates

\[
 b_r=b\oplus c^{\oplus r}:
 N_B\oplus N_Y^{\oplus r}\longrightarrow
 H_B\oplus H_Y^{\oplus r}.
\]

The new Lean definitions and theorems `blowupManyCanonicalCycleBlock`,
`blowupManyCanonicalCycleBlock_surjective_iff`, and
`blowupManyCounterexample_iff_base_or_center` prove for every r>0:

\[
 b_r\text{ surjective}\iff b\text{ surjective and }c\text{ surjective},
\]
\[
 \exists \beta\notin\operatorname{im}(b_r)
 \iff(\exists u\notin\operatorname{im}(b))
     \lor(\exists v\notin\operatorname{im}(c)).
\]

At the rational linear level, the natural isomorphism of cokernels is

\[
 \operatorname{coker}(b_r)\cong
 \operatorname{coker}(b)\oplus\operatorname{coker}(c)^{\oplus r}.
\]

This is a complete multi-center **defect classification**. For different center types and different codimension shifts, replace the repeated `c` by the corresponding individual maps; the ordinary direct-sum argument applies to each block. The current Lean code formalizes the same-type finite family, not the full geometric scheme-level isomorphism construction for arbitrary center families.

In particular, if B and all centers have canonical rational cycle-class surjectivity, their blowup has no rational Hodge counterexample. If a prescribed residual is missing downstairs, ordinary split exceptional births alone cannot erase that defect. This does not preclude an independently constructed nonsplit algebraic input on the *original* X.

## Two genuinely distinct blowup modes

1. **Actual interacting feedback:** The already established `2026-10-20-gst-interacting-blowups-connected-arbitrary-rank.md` constructs positive exceptional Chern/K0 feedback and arbitrary finite primitive ranks in connected dimensions. Here those classes are native and their Gram matrix genuinely invertible; this is a positive source generator on that family.
2. **Exact original-X Hodge coverage:** For arbitrary original X and primitive alpha, a blowup can contribute only cycles from its base and centers. To reach an alpha absent from the algebraic source image of X, a new source must be constructed on X (or a geometric input whose canonical return produces it). This is the precise discriminating operation, not a no-go theorem for GST.

## Independent exact computations

Wolfram Language evaluator (stateless, exact rational arithmetic) tested direct-sum ranks for 1<=r<=6:

- A base map of rank 1 into a two-dimensional Hodge channel with invertible one-dimensional center source has rank 1+r into 2+r, so the original defect remains 1 for each r.
- With surjective base and zero center map, the cokernel dimension becomes r.

The existing GST connected blowup `r=2` primitive Gram was independently recomputed from its original formulas:

\[
G_2=\begin{pmatrix}
133/75&2/3&2/3\\
2/3&33/4&1/4\\
2/3&1/4&33/4
\end{pmatrix},\quad
\det G_2=25532/225>0.
\]

Wolfram returned the exact inverse

\[
G_2^{-1}=
\begin{pmatrix}
3825/6383&-300/6383&-300/6383\\
-300/6383&12767/102128&1/102128\\
-300/6383&1/102128&12767/102128
\end{pmatrix},
\qquad G_2G_2^{-1}=I_3.
\]

For general r the same previous connected-blowup data give the positive Schur complement

\[
 \frac{r(105+411r+596r^2+384r^3)}{36(1+2r)^2}>0\quad(r>0).
\]
Wolfram verified algebraic identity to the prior closed formula with difference exactly zero.

**Scope:** These computations verify the given exact rational matrices, not the universal existence of a Chow cycle for arbitrary original X. They do NOT produce a rational Hodge counterexample. The Lean kernel verifies the source-level many-center linear-algebra theorems under the actual typed maps; the geometric Chow/Betti comparison is a separately stated input.

## First unproved implication and concrete continuation

For arbitrary original X,p and nonzero primitive residual r, construct a **specific algebraic perfect complex E_r** on original X, or a smooth GST incidence center returning its genuine Chow class, and prove
\[
 Q\!\left(r,\operatorname{cl}^{canonical}_X
  \left([\operatorname{ch}(\mathcal P_f^K(E_r))\operatorname{td}(T_f)]_p\right)\right)\ne 0.
\]
The current smooth-center construction turns *any independently algebraic source* into a center and returns its period exactly; it does not itself construct E_r for an arbitrary r. An alternative genuine counterexample requires a specified nonalgebraic rational Hodge class with verified canonical-image exclusion, not merely a new exceptional algebraic class.

Existing relevant sources: `GSTGraphV2SelfExpandingCosmology.lean`, `GSTActualXHodgeResidualProjection.lean`, `GSTUniversalResolvedSupportHodge.lean`, the October 20 interacting-blowup and smooth-incidence records.
