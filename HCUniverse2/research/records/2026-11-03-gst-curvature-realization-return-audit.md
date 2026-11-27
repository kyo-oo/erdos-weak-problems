# Curvature proof audit and the higher realization subconstruction

Date: 3 November 2026, Asia/Calcutta. Base checkpoint:
`6c78f4d57fcad0e2309cc0bba3417952a58f4d5b`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

**The curvature proof is established in its stated fold family.** Its exact
equation is `delta^1 = rank(sum K_e)`, with the entire canonical Hodge
structure restored exactly when the total central curvature is zero.
The stronger finite pure-model normal form and relative classification
retain their stated scopes too. This is a self-reviewed mathematical
proof status; the owner has retained Lean compilation.

This continuation directly tests the outstanding higher prescribed-class
realization instead of treating a successful curvature calculation as an
unconstructed algebraic source. It derives a general projective return,
executes the alpha-dependent nullhomotopy construction, proves its direct
projective realization impossible when alpha is nonzero, and completes
the exact cycle extraction for an admissible open algebraic boundary.

[Hand derivation](../derivations/GST_curvature_projective_retraction_boundary_2026_11_03.tex)
was written before the Lean changes. No independent reviewer, Lean-kernel
verification or historical-novelty claim is made.

## The completed mathematical subresults

For **any** surjective morphism `f:Y -> X` between smooth projective
varieties, not just a principal torus bundle, choose a very ample class
h on Y and let r be the dimension difference. Its actual generic
multisection degree d is positive and

`f_*(h^r) = d[X]`.

Consequently the actual rational Chow operation

`R(B) = f_*(h^r B)/d`

satisfies `R f^* = identity`, with the canonical Betti comparison in
every degree. The fibers need not be smooth, flat or connected. This
constructs the missing return in much greater geometric generality than
the earlier torsor theorem. The Hodge/cycle-image quotient for X is
a split summand of that for Y. The construction composes through every
finite sequence of these maps.

The exact source used for the projection formula is the Stacks Project,
[Lemma 43.27.1, tag 0B2X](https://stacks.math.columbia.edu/tag/0B2X),
checked 3 November 2026. Its nonsingular-projective hypotheses match
both varieties, and part (3) supplies the arbitrary-morphism formula.
The generic hyperplane multisection and Betti return are derived in the
hand proof. The chosen return depends on h; its cycle-class map remains
the canonical one. No fetched source text is copied into the repository.

Next, start with the actual arbitrary `(X,p,alpha)` and form the homotopy
fiber `T_alpha -> X` of its classifying map into `K(Q,2p)`. Its marked
pullback kills the prescribed input class: `t^*alpha=0`; in the
cochain model `du=alpha`. This is an executed alpha-dependent construction.
If it had a compatible smooth projective surjective realization over X,
the return above would give `alpha=R(t^*alpha)=0`. For nonzero alpha this
is a contradiction, including after finite projective surjections,
smooth blowups or smooth projective alterations. Thus **direct projective
algebraization of this nullifying model is ruled out**, even when alpha
already is algebraic. This is a route obstruction, not a Hodge counterexample.

The open alternative has an explicit positive result. If an actual
algebraic boundary `D subset Y` has codimension at least p and the lifted
class vanishes on `Y minus D`, then

`f^*alpha = sum_i b_i cl[D_i]`,

where the D_i are the actual codimension-p irreducible components and
the b_i are rational. The actual original-X cycle is

`Z_alpha = sum_i b_i f_*(h^r [D_i])/d`.

Its canonical Betti class is exactly alpha. The support proof includes
singular and reducible boundaries: remove higher-codimension singular
strata, use the Thom generators of the disjoint smooth top strata,
and apply the supports exact sequence. The coefficient images may be
dependent. Different coefficient solutions can return distinct Chow
classes with the same Betti class.

The threshold is sharp: if the boundary has codimension strictly greater
than p, its degree-2p support cohomology vanishes, so it cannot kill a
nonzero alpha. Four projective-space controls test the stated cutoff,
without substituting a special-family research program for arbitrary X.

## Audit of the actual proof obligation

| Claim and required input | Verdict | Reason |
| --- | --- | --- |
| Central-fold curvature/opposedness theorem | Proved as written at hand-proof level | Actual complex quotient, full cochain comparison, filtered representatives and exact missing-mode sequence |
| Torsion principal-torus projective subconstruction | Proved as written at hand-proof level | Earlier finite cover, projective quotient and actual normalized multisection |
| Return for every smooth projective surjective fold | Proved as written at hand-proof level | Positive generic hyperplane degree and projection formula |
| Projective realization of the nonzero-alpha nullifying homotopy fiber | Refuted under the stated over-X compatibility | Pullback injectivity contradicts `t^*alpha=0` |
| Actual cycle extraction from a supplied codimension-at-least-p algebraic boundary | Proved as written at hand-proof level | Top support generators and the explicit proper return |
| Every prescribed alpha has such an algebraic boundary | Incomplete | No construction of that boundary from arbitrary alpha is supplied |
| A general compactification boundary divisor satisfies the higher-p theorem | False inference | Its codimension is 1, which is below p for p>1 |
| Universal canonical original-X Chow proof | Incomplete | The independent prescribed-alpha source still has not been constructed |

This audit reconstructs the curvature construction's complex coordinates,
central lattice, de Rham comparison and filtered degree-one argument from
its current derivation. Zero curvature supplies an actual projective
product; positive rank gives the nonzero opposedness quotient. The
cochain comparison identifies all cohomological degrees, while degree
one alone certifies failure of the whole canonical pure structure in
the nonzero-curvature case. It is not a classification of all GST spaces.

Existence of the open boundary above is equivalent to alpha's algebraicity:
the explicit return proves one implication, while a cycle for alpha gives
the converse by taking Y=X and removing its support. This equivalence is
recorded as the anti-circularity gate; it is not counted as a new source
constructor. The exact branch Gysin-image equivalence remains in force.

## Lean edits and exact evidence

Two existing modules are edited, with no new wrapper or library root.
`GSTCausalFoldDefect.lean` gains **12 theorem drafts** for normalized
transfers, injectivity, the nonzero-curvature/nullifier contradiction,
compositions, the split projector, source-image reflection and actual
boundary-combination returns. `GSTSpatialFoldResearch.lean` checks their
integration. These are algebraic consequences of explicitly supplied maps;
the geometric construction of the maps is the hand theorem, not a hidden
Lean structure field claiming Hodge surjectivity.

```sh
python research/experiments/gst_curvature_return_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_curvature_return_20261103.manifest.json --root .
```

Python Fraction arithmetic and independent Wolfram exact matrix operations
each pass **21 targeted assertions**, with all six shared result tables
matching. These are fixture checks, not a proof of projectivity, support
purity, algebraic existence or universal Hodge algebraicity.

The fixtures comprise one non-diagonal degree-six transfer, a degree-thirty
composition, a deficient cycle-image comparison with four retained target
vectors, two distinct cycles returning the same Betti class, the inconsistent
equation `R*0=identity`, and four sharp boundary controls on P4. Python
implements rational elimination directly; Wolfram uses MatrixRank. The boundary
controls use a cohomology restriction matrix in Python and polynomial
remainder in Wolfram. This
deliberately small suite tests the actual new distinctions rather than
increasing unrelated case counts.

The Wolfram kernel is 15.0.1 for Linux x86 (64-bit), July 2, 2026. It
passed the final complete execution. After the initial matrix suite passed,
strengthening the boundary controls exposed a symbolic-predicate bug:
Wolfram left a nonzero polynomial's equality to zero unevaluated. A minimal
probe verified the actual remainder, and structural comparison to exact
zero fixed the predicate. Both zero and nonzero controls and the entire
suite then passed. The failed input, raw response and diagnostic probe
are retained; this was not a mathematical counterexample.
Remote runtime and process exit
status are not exposed and are null. The context call initially used an
incorrect parameter name, then the corrected lookup supplied no relevant
mathematical result; no proof depends on that lookup. The full evaluator
input, raw result, parsed JSON, before/after source hashes and observed
Python exit zero are retained. The manifest validates against current inputs.

Changed-source proof-escape checks, the 748-node parsed import graph,
LaTeX environment balance and whitespace checks pass. Three preexisting
lexical anomalies are unchanged from the base. This is not a semantic
review of every module, Lean compilation or LaTeX typesetting.

[Exact output](../computations/gst_curvature_return_20261103.output.json),
[remote raw evidence](../computations/gst_curvature_return_wolfram_20261103.output.json),
[current-source manifest](../computations/gst_curvature_return_20261103.manifest.json).
Historical manifests remain historical after the current Lean edits.

## Continuation checkpoint

The direct higher-curvature **projective nullifier** route is closed by
the uniform contradiction, rather than deferred as an easy algebraization
lemma. The open boundary extraction is completed for the stated actual
input data; universal boundary existence remains open. Ordinary divisorial
compactifications require higher boundary cohomology and a new independent
source argument, and are not covered by the top-support theorem. Other
selected/excess and integrable-source routes retain their existing open
status; this work neither solves nor refutes them. A resumption must change
the actual geometric source step, not reapply curvature restoration to the
same nullifying model.
