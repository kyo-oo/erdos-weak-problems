# GST whole-space proof plan: the complete dependency chain

Date: 3 November 2026, Asia/Calcutta. Starting revision:
`2b678dc20beb81807a2c576e2d95c639900171ae`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

**Owner-corrected experimental outcome from `ef1a452` (3 November 2026):**
[Constructed whole-space central folds and complete decision equations](records/2026-11-03-gst-requested-whole-space-fold-results.md).
The provisional experiment is now executed on actual all-X central-torus
realizations using the custom GST modules: total-curvature rank is exactly
the canonical first-Hodge opposedness defect; zero curvature restores the
whole projective Hodge spectrum. Independent product and shared-base fusion
give different, calculated outcomes. The full cohomology and geometric
dimension-reducing quotient are derived, with six existing Lean modules
upgraded. This result belongs to the requested experiment of Sections 2--6;
it is not another attempt to substitute Section 7's cycle-source problem.

**Executed continuation from `feb0a99` (3 November 2026):**
[Full mathematical derivation](derivations/GST_selected_block_excess_and_integrability_2026_11_03.tex)
and [proof audit / evidence](records/2026-11-03-mathbox-plan-to-mathematics-selected-block.md).
The filtered nerve comparison of Section 4 now has an actual good-cover
realization. Section 7 now has a proved matched-factor coherent-source
construction, exact local-block and global-package return coefficients,
root-transitive cancellation, a nonzero-Hodge-input descent obstruction,
and calculated polarized excess and nonlinear integrability tests. None
forces the independent algebraic source for every prescribed input; the
universal proof remains incomplete at that implication. No Lean work or
compilation is claimed by this continuation.

This is the requested **entire proof plan**, organized around the owner's
sequence: arbitrary X; provisional Hodge assumption; emergent N dimensions;
spatial folds; graph complex; causality; full N-cohomology; preserving or
breaking equations; and the return to the original X. It corrects the prior
response's substitution of a conjecture-status report for that deliverable.
It is a dependency and execution specification, not a claim that its research
obligations have already been proved. Existing derivations remain evidence
with their original scopes; this document does not overwrite their history.

## 1. Fix the two questions before doing the fold

The input throughout is an arbitrary smooth projective complex X, an integer
0 <= p <= dim X, and a prescribed rational Hodge class
alpha in H^(2p)(X,Q) intersect H^(p,p)(X,C).

**Whole-space experiment requested by the owner.** Provisionally assume
rational Hodge algebraicity for every smooth projective realization used in
the experiment. Derive what a specified GST fold does to the *full marked
class*, and determine exactly when it preserves or changes its Hodge type.
This provisional assumption is allowed in this experiment. It is not a
conclusion inferred from the experiment.

**Conjecture-ending proof.** Construct an actual Z_alpha in CH^p(X)_Q with
canonical Betti class alpha. Every use of the provisional assumption in the
experimental argument must have been replaced by an independent geometric
construction before that argument is an unconditional proof.

These are related tasks with different hypotheses. A class leaving (p,p)
under a deformation is a marked-class type change. It does not mean the
smooth projective fiber has lost its Hodge structure, and it is not a
nonalgebraic rational (p,p) class on that fiber.

## 2. The complete GST input, without collapsing its coordinates

For each realized world v retain the following data separately:

| Layer | Exact object to retain | Existing entry point |
| --- | --- | --- |
| General Space | Points, typed paths, composition | `GSTGeneralSpace.lean` |
| Emergent dimension | Actual scheme/manifold realization and its observed dimension | `GSTGeneralSpaceSchemeDimensionObservation.lean` |
| Graph and causality | Realized edges, path transport and the relations being imposed | `GSTGraphV2GeneralSpaceRealization.lean`, `GSTCausalFoldDefect.lean` |
| N-cohomology | Every hole/world index and every rational amplitude | `waves/GSTNCohomologyV3.lean` |
| Hodge data | Degree, weight, full filtration/bigrading, period/extension data | `GSTFoldPeriodDescent.lean` and its hand derivation |
| Geometry of the fold | Actual space, map/correspondence, integrability and projectivity | `GSTFoldRotation.lean`, `GSTFoldPolarization.lean`, `GSTVariableFoldIntegrability.lean` |
| Cycle semantics | Actual Chow/native cycle carrier and canonical Betti map | `GSTActualXHodgeResidualProjection.lean`, `GSTClassicalHodgeExactClayStatement.lean` |

For m participating N-hole worlds the coordinate index is

$$I=\prod_{i=1}^{m}\operatorname{Fin}(n_i),\qquad V_N=\mathbb Q^I,
\qquad \dim V_N=\prod_{i=1}^{m}n_i.$$

Keep the entire coefficient function c:I -> Q. One separated tensor has
coefficients c(i_1,...,i_m)=product_j a_j(i_j). In genuine multifactor sectors
this can be a proper rank-one locus; at arity one every vector is already
one tensor. Use finite sums and the actual delta basis to retain the whole
fiber. The empty product is the one-dimensional vacuum; a zero
hole count makes the corresponding nonempty product index empty.
An N-hole count, graph-coherence degree and scheme dimension remain distinct
observations. A realization/comparison theorem must connect them when needed.

## 3. Write the preserving/breaking equation on the full state

On a pure realized H^(2q)(Y,C), define the **charge operator** Q_Y to act by
a-b on H^(a,b). Then

$$\ker Q_Y=H^{q,q}(Y),$$

because a+b=2q and a-b=0 force a=b=q. This checks Hodge type on the full
complex vector; rationality is an additional retained condition. The charge
operator need not be rational in a chosen rational basis. The geometric
instance must supply its actual complex Hodge decomposition.

For mixed worlds retain the weight filtration as well: membership in an
appropriate weight-graded (q,q) piece is not a substitute for the full
filtration and extension conditions on a purported pure projective return.
On a pure rational degree-2q class the equivalent filtration test is
membership in F^q and its conjugate. In a mixed realization the corresponding
filtered conditions and the comparison to the return must be specified.

For a realized edge e:v -> w, with operator T_e and any explicitly recorded
Tate degree shift, define

$$D_e=Q_wT_e-T_eQ_v.$$

Equal Tate shifts in both Hodge indices do not change charge. If the input
state x has Q_v x=0, its output is Hodge precisely when

$$D_e x=0.$$

This is a **state-specific** condition. D_e=0 is the stronger condition of
preserving every charge eigenspace. A nonzero operator D_e can still kill
the particular input x; do not classify that input as broken merely because
some unrelated vector is changed.

For a path gamma=(e_1,...,e_k), write T_gamma=T_k...T_1. Direct telescoping
gives the exact varying-world identity

$$Q_kT_\gamma-T_\gamma Q_0
=\sum_{j=1}^{k}T_k\cdots T_{j+1}D_{e_j}T_{j-1}\cdots T_1.$$

Proof: substitute D_(e_j)=Q_j T_j-T_j Q_(j-1). Every intermediate
T_k...T_(j+1) Q_j T_j...T_1 cancels the adjacent negative term; only the
two endpoints remain. Empty paths have identity transport and zero defect.

Thus the right-hand side applied to alpha is the exact **endpoint** break
test. To require safety at *every intermediate world*, test every prefix.
An endpoint cancellation does not certify that every edge was safe.
The existing constant-world word law is a special case of this equation.

## 4. Execute the graph-complex and higher-causality part

Assign a cochain complex C_v to every realized world and a cochain map T_e
to each admissible edge. First prove d_w T_e=T_e d_v; otherwise there is
no induced transport on cohomology. For a two-cell identifying paths gamma
and eta, construct the actual homotopy h with

$$T_\gamma-T_\eta=d h+h d.$$

For a closed cochain x, the two outputs differ by the exact cochain d(hx),
so they give the same cohomology class. Higher relations must be supplied
at the coherence degree used; mere endpoint reachability supplies none.

Now compare the computed graph/N-cohomology complex to the actual Betti or
mixed-Hodge complex of the realized geometry. Prove the comparison respects
the differential, full multiplicity coordinates and filtrations. Use a
quasi-isomorphism only when it has been established. Without such a
comparison, the graph calculation remains a calculation in its graph model.

Apply the charge equation from Section 3 to the induced cohomology maps.
For homotopic paths between the same worlds it is a cohomology-level test;
cochain charge representatives require their own compatibility with d.
Record the dimension/weight changes and the canonical original-X comparison
for each new birth or singular/open realization.

## 5. Use the already derived period equations as exact first realizations

The current branch has executed the following smooth projective realization,
not merely assigned Hodge labels to graph addresses. For two elliptic
handles and the complete cross-coordinate vector

$$v=Aa_1a_2+Ba_1b_2+Cb_1a_2+Db_1b_2,$$

the exact Hodge equation is

$$\Phi_v=A\tau_1\tau_2-B\tau_1-C\tau_2+D=0.$$

For tau_i=n_i z+u_i, the all-family condition is exactly

$$A=0,\qquad n_1B+n_2C=0,\qquad D=Bu_1+Cu_2.$$

The first two monodromy conditions omit the third extension equation.
For a nonzero rational solution one needs
n_2 u_1-n_1 u_2 in Q. Compatible handles have actual constructed
isogeny-graph divisors, with pairing -2 n_1 n_2. The incompatible
(i,i+sqrt(2)) control changes the marked cross vector's type.

For synchronized handles, the three charge tests at i, 2i and 1+i determine
the flat invariant tensor block at every finite arity. Pairing-graph cycles
span that block, keeping the tensor/exterior sign dictionary. These results
are in the [extension-sensitive derivation](derivations/GST_extension_sensitive_causal_folds_2026_11_03.tex).
Their all-arity statements are hand proofs; the Lean modules contain the
specified algebraic drafts. They do not identify this block with the entire
Hodge fiber of an arbitrary X or of an isolated special period.

Use these realized equations to test the general mechanism. Do not restart
the same finite handle census or assume the three-test equation controls
every variation of Hodge structure. The next general realization needs its
own full period/filtration equations.

## 6. Run the owner's provisional Hodge assumption all the way through

Take an actual smooth projective folded realization Y_gamma, a rational
Hodge class beta_gamma constructed from the marked input, and an actual
algebraic return correspondence R_gamma of the required degree. Compute

$$R_{\gamma,B}(\beta_\gamma)=m_\gamma\alpha,
\qquad m_\gamma\in\mathbb Q\setminus\{0\}.$$

Under the provisional Hodge assumption on Y_gamma, choose an actual
Z_gamma with cl_Y^can(Z_gamma)=beta_gamma. Then the *cycle itself* is

$$Z_\alpha=m_\gamma^{-1}R_{\gamma,CH}(Z_\gamma),$$

and canonical functoriality proves cl_X^can(Z_alpha)=alpha. This completes
the deduction **under the stated provisional assumption**; it is not a
failed deduction just because that assumption is provisional.

The synchronized product example already has this exact return: with its
constructed divisor W and w=cl(W), beta=alpha external-product w on
X x E x E, cup with W and push to X give -2 alpha. All degree shifts and
the scalar are explicit. Algebraicity of beta and alpha are equivalent
for this construction. Consequently it is a verified transport example
for the experiment, not an independent discharge of its Hodge premise.

If a fold fails its full Hodge equation, do not apply the provisional
assumption to that marked class. Recompute the class/fold or change the
realization. Retain the failure equation as information about that route.

## 7. The geometric work that turns the experiment into a proof

The [executed selected-block derivation](derivations/GST_selected_block_excess_and_integrability_2026_11_03.tex)
implements these routes: a matched root factor returns a genuine cycle even
with resultant boundary; a component package returns the explicit binomial
coefficient sum, which vanishes under root-transitive monodromy; correlated
excess and its projective polarization are computed; and the specified
first-order source direction has a nonzero second-order obstruction.
The unproved existence of a suitable source is retained below. A completed
conditional construction is not substituted for that existence statement.

Keep every explicit construction and return from Section 6. Replace the
single use of provisional Hodge algebraicity by a proved geometric source
construction. This is the central research task, with the following live
routes and distinct decisive tests; none is asserted to succeed in advance.

| Route | Actual construction to execute | First decisive obligation | Existing boundary |
| --- | --- | --- | --- |
| Selected or excess incidence | Start with the alpha-selected near-projector on the genuine Jouanolou J -> X; form its actual invariant-subspace incidence; construct an algebraically defined selected component or excess cycle | Prove global selection/descent, then compute its *actual* pushforward character and canonical coupling to the prescribed residual | The complete regular incidence has zero positive tautological Chow return; a local contour choice alone is not a global algebraic component |
| Integrable source from the spatial fold | Use the prescribed-alpha topological source to construct a specific integrable algebraic bundle, complex or determinantal ideal with its actual equations | Derive the integrability/algebraicity equations from independent geometric input and prove they have a solution for this input | Square equations, positivity, Stein holomorphic realization and cohomological causal invariance alone do not solve algebraic descent |
| Genuine deformation of source-bearing geometry | Construct a deformation of the actual space/source pair, keeping the prescribed transported class and the canonical return | Prove source deformation, effectivity/compactification and descent for the *same* class, with the required period and obstruction equations | A variation of Hodge type or an auxiliary product alone does not manufacture the cycle being transported |

For the selected-incidence route the execution order is concrete:

1. Retain the actual alpha-dependent local cluster on its detecting compact
   core and the explicit algebraic matrix/section data on J.
2. Compute the real monodromy action on root subsets/flags. A proposed
   selected component must be an actual orbit or another proved algebraic
   subscheme, not a chosen sheet that continuation permutes away.
3. Construct its closure as a proper source over J, including discriminant
   fibers. In an excess case distinguish the actual component cycle from
   the virtual top-Chern cycle, and derive the excess contribution.
4. Compute the total returned class, including every sheet in the orbit and
   all boundary terms. Test its restriction on the detecting core against
   the prescribed class; do not infer it from one preferred local sheet.
5. Return through the genuine affine-bundle Chow comparison to original X
   and compute the canonical Betti coupling. A zero coupling closes that
   candidate; a proved nonzero coupling supplies a real source increment.

The general regular full-incidence calculation from the
[selected-cluster record](records/2026-11-03-gst-selected-cluster-rational-fiber.md)
is not to be rerun under a new name. Likewise, auxiliary products with the
known inverse return remain valid operations, but do not discharge the
source-construction obligation.

## 8. Exact finite closure once genuine new sources are constructed

Use a finite-dimensional rational Hodge fiber H with its *verified* rational
positive polarization form B, and a finite-dimensional span W of classes
of actual constructed original-X cycles. Compute the B-orthogonal projection
pi_W(alpha) by the rational Gram matrix of a basis of W. Set

$$r=\alpha-\pi_W(\alpha).$$

The projection is onto this **explicit finite source span**, not an assumed
algorithm for the full canonical Chow image. If r=0, its rational
coefficients already construct Z_alpha from the retained source cycles.

If r != 0, execute a geometric route in Section 7 to obtain an actual cycle
z with

$$B(r,\operatorname{cl}^{can}_X z)\ne0.$$

Then cl(z) is outside W: every element of W pairs to zero with r. Adjoining
it strictly increases dim W. Recompute the exact rational projection and
repeat. If a source-construction rule supplies such a cycle whenever this
prescribed residual is nonzero, this process terminates after at most
dim H - dim W initial source increments, and the retained rational cycle
combination has canonical class alpha.

This finite closure argument is a proved linear-algebra implication. The
universal nonzero-coupling source rule is a theorem to be derived by actual
geometry, not an available hypothesis that may be renamed a GST law. Indeed,
with positive B, universal Hodge algebraicity would supply such a rule by
choosing a cycle for r and using B(r,r)>0. The converse is the termination
argument. This equivalence is recorded to prevent circular use of the plan.

## 9. Full proof assembly and verification order

1. Keep arbitrary X,p,alpha throughout; choose the exact realized GST route
   and retain its complete N-coordinate vector.
2. Prove the cochain comparisons, edge relations and needed higher
   coherences. Compute every degree/weight change and full Hodge defect.
3. Solve the route's actual period, integrability, global-selection and
   source equations. Exhibit the scheme/sheaf/complex/cycle itself.
4. Compute its canonical class or nonzero residual coupling, including
   discriminant, excess, Todd/GRR and descent terms where the route uses them.
5. Construct the rational original-X cycle by exact return and, where
   needed, the finite source-enlargement argument of Section 8.
6. Prove cl_X^can(Z_alpha)=alpha with the genuine canonical comparison;
   numerical intersection identities alone do not replace this equation.
7. Translate the established mathematics into Lean. Match the actual target
   `GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic`,
   inspect all quantified hypotheses and prove the canonical semantics of
   any Stage-2G interface used. Do not replace the target by a source-span
   predicate or add its surjectivity as a structure field.
8. Perform a mathematical dependency audit, checking that the provisional
   Hodge premise has disappeared from every proof leaf. Preserve the owner's
   instruction to handle Lean compilation; no build or CI result is implied
   by this plan or by the existing uncompiled drafts.

## 10. What is available at this checkpoint, and what to execute

| Proof component | Evidence at starting revision | Required work |
| --- | --- | --- |
| Full finite N-coordinate reconstruction | Existing V3 algebraic proofs/drafts, with rank-one distinction | Build the comparison for any newly chosen realized geometry |
| Causal composition defect | Existing constant-world/Graph-V2 drafts; varying-world telescoping proved in Section 3 | Instantiate actual filtration/charge and transport on the selected spaces |
| Extension-sensitive preserving/breaking examples | Existing hand derivation, constructed divisor geometry and scoped exact checks | Derive the next realization's actual equations; do not extrapolate from handles |
| Provisional-Hodge deduction to original X | Explicit conditional cycle-return argument in Section 6 | Carry the premise visibly while running the requested thought experiment |
| Independent source construction | Three routes with separate first uncertain implications in Section 7 | Execute the geometric selection/integrability/deformation step, computing its class |
| Finite source closure | Exact argument in Section 8, conditional on independently generated increments | Retain actual cycles and prove every demanded increment rather than assuming coverage |
| Final canonical Lean theorem | Existing target/interface, not certified by this document | Instantiate geometry, discharge premises and let the owner compile |

The immediate source-bearing continuation is the selected/excess incidence
construction in Section 7, beginning with monodromy and the actual closure
of a target-dependent component. The experimental whole-space analysis and
the unconditional source construction remain separate work products in this
one plan. This supplies the requested route from the GST input all the way
to the final canonical equation, while identifying precisely what each
proposed proof must establish.

Review provenance: focused mathematical self-review of the dependency plan,
its telescoping identity, type distinctions, conditional canonical return
and finite-rank closure argument. No new external theorem, new computation,
independent reviewer, Lean compilation or universal proof is claimed here.
