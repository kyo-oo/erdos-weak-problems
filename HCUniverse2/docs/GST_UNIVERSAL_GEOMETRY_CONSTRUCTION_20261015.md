# GST universal geometry construction — Mathbox research checkpoint

**Date:** 2026-10-15
**Attribution:** Personal name withheld at the contributor's request.
**Working branch:** `mathbox/bd23-single-operator-charge-wedge`
**Mathematical target:** the unchanged classical rational Hodge conjecture
for every smooth projective complex variety, not only conditional Stage-2G
data and not merely passing Lean compilation.

## Exact problems attacked

1. **Actual correspondences:** construct finite-closed geometric
   correspondence operators on the rational Hodge fibers that span
   enough native algebraic-cycle directions, without assuming a
   matrix-unit lift or target Hodge representative.
2. **Geometric source:** derive a nonzero genuine cycle-class
   measurement from projective geometry, with coefficients genuinely
   descending to Q and without choosing a free zeta scalar to force
   an equality.
3. **Dimension correctness and semantics:** avoid claims of nonzero
   codimension-p algebraic cycles beyond the dimension of X, and
   do not identify a free Betti endomorphism with the canonical
   cohomological action of a scheme correspondence.

## Route A — universal minimal geometric orbit

`GSTResearchUniversalOrbitClosureLaw.lean`
**CI: 38623626850 — SUCCESS**

Constructed a real native algebraic-cycle orbit from finite words of
actual Hodge-compatible closed correspondences. Proved unconditionally,
relative to the existing actual geometry interface:

- the generated orbit is the SMALLEST invariant Hodge subspace
  containing its genuine seed;
- its being the full Hodge fiber is EXACTLY equivalent to the
  **local geometric cyclicity** criterion for that one seed;
- cyclicity gives an actual native cycle representative for
  any rational Hodge state at the weight;
- global irreducibility of all geometric correspondences is
  sufficient but is stronger than local seed cyclicity.

The theorem of orbit minimality is genuinely universal as a structural
conclusion: there is no assumption that the orbit already spans Hodge.
By contrast the full-span conclusion still requires a cyclicity proof
from real geometry for the selected carrier.

`GSTResearchLocalCyclicityHodge.lean`
**CI: 38624241411 — SUCCESS**

All-weights rational Hodge statement now follows under the reduced,
per-active-weight existence of one cyclic native seed. The earlier
extra hypotheses of an arbitrary zeta multiplier and global
operator irreducibility have been removed from this criterion.

## Route B — fixed corrected zeta source (not free normalization)

`GSTResearchFixedZetaGeometricSource.lean`
**CI: 38623934984 — SUCCESS**

At codimension zero, constructs the canonical geometric fundamental
cycle and a half-degree functional, deriving the EXACT corrected
indexed infinite-sum measurement with fixed scalar -1/2
(zeta(0)'s classical special value), **provided** that the true
cycle-class map has a normalized degree readout equal to 1 on the
fundamental cycle. The normalized-degree field is an input that
must come from actual geometric intersection/Borel–Moore
fundamental-class theory, not an automatic consequence of the
arbitrary Stage-2G cycleClass linear map.

`GSTResearchUniversalMassZetaSource.lean`
**CI: 38625514599 — SUCCESS**

Mechanically extends the fixed numerical source to all weights
when the older `NativeMassCycleClassBridge` exists. **Important:
this conditional result is not a viable universal existence
theorem for finite-dimensional projective varieties**, because
its unrestricted mass-bridge hypotheses have geometric
obstructions described in Route C. Do not merge this statement as
the final universal Hodge proof.

## Route C — prove and correct the mass-law defects

`GSTResearchGeometricMassSemanticAudit.lean`
**CI: 38625663787 — SUCCESS** (earlier repaired run 38625365341 also green)

The current native mass is UNWEIGHTED SUM of rational coefficients
in native point normal form. Proved:

- if two true native algebraic cycles have equal cycle classes
  but unequal raw coefficient masses, an unrestricted native-mass
  cycle-class bridge cannot exist;
- the zero-class Stage-2G countermodel cannot support the bridge
  when an actual codimension-p point exists;
- a degree readout defined by evaluating a cohomological functional
  on the cycle class IS invariant under cohomological equivalence
  by construction.

Concrete standard geometric sanity check (NOT Lean formalized
as an actual `P²` cycle-class instance): in projective plane,
a smooth conic and twice a line are cohomologous as divisors,
but their raw coefficient sums are 1 versus 2.
This makes unrestricted raw coefficient-count mass unsuited
to the genuine projective cohomology bridge.

`GSTResearchGeometricWeightBoundaryAudit.lean`
**CI: 38625637598 — SUCCESS**

Proved: if there is ANY weight p whose native codimension-p
cycle module vanishes, an everywhere-nonzero conserved
spine charge and the old unrestricted mass bridge cannot
be inhabited. In actual finite-dimensional projective
varieties, codimension-p cycles vanish for p>dim X.
Thus claims of nonzero algebraic cycle classes at all
natural-number p are invalid without a finite-weight cutoff.

## Route D — repaired dimension-bounded geometric law

`GSTResearchFiniteWeightGeometricDegree.lean`
**Verified CI: 38626403600 — SUCCESS**, after fixing missing successor-scalar namespace. Earlier 38625865055 failed at elaboration.

New bounded input `BoundedGeometricDegreeCharge G d` uses:
a native rational-linear degree, an ambient rational Betti
degree readout, exact cycle-class compatibility, nonzero
degree of the fundamental component cycle and a principal-cut
transport law **only for p<d**.

It DERIVES conservation and a genuinely nonzero native
spine cohomology class for **p<=d**, with no nonzero-cycle claim
outside the dimension window. The geometric degree fields
and transport identities remain separately verifiable,
unproved geometric inputs; they are not replaced by axioms.

`GSTResearchDimensionCorrectedHodgeSynthesis.lean`
**Dedicated CI: 38626768532 — SUCCESS**. The earlier 38626143207 failed because it built the pre-repair dependent finite-degree module.

Wires finite-weight geometric degree and local cyclicity of actual
Hodge-compatible closed correspondences to the original all-weight
rational Hodge conclusion, with zero Hodge fibers beyond d.
Its hypotheses are explicit and in the geometrically appropriate
finite-dimensional range.

## Status of the original full Hodge conjecture

**NOT PROVED.** The source construction is valid for normalized
degree data at codimension zero and under a bounded degree input
in higher weights. The all-weight cyclicity theorem is conditional.
No Lean theorem constructs adequate geometric correspondence
operators or proves local cyclicity on arbitrary smooth projective
varieties without an additional assumption.

The existing full `HodgeConjecture.lean` CI run 38605997725
terminated with GitHub runner exit code **143** during the
expensive root build after all five focused upstream modules passed.
This is an infrastructure shutdown, not a success or a mathematical
counterexample.

## Exact next construction targets

- Build CANONICAL Betti actions from actual algebraic
  correspondences through fundamental classes, cup product,
  pushforward/Gysin and intersection, rather than supplying
  arbitrary endomorphisms constrained only on native classes.
- Prove positive/nonzero projective intersection degrees on
  genuine native cycles **within p<=dim X** using the real
  embedding/polarization, and verify the degree transport law.
- Prove, rather than assume, the LOCAL cyclicity criterion for
  a selected actual native seed at each Hodge fiber.
  The user's corrected coordinate and indexed zeta formulas
  can become detectors only after a real geometric comparison
  identity and rational descent are established.
- Audit each proposed universal claim against the already
  kernel-verified zero-cycleClass semantic countermodel, and
  against vanishing codimension groups at p>dim X.

This record preserves useful green proofs without promoting
conditional or structurally obstructed hypotheses into facts.

## Verified audit and mass-theorem safety notice

The source `GSTResearchGeometricWeightBoundaryAudit.lean`
passed **38625637598**. The native mass audit passed **38625663787**.
The conditional unlimited mass/zeta theorem also compiled in
**38625514599**, but it MUST NOT be cited as a universal existence
result: its old unrestricted mass bridge cannot exist when any
codimension cycle module vanishes.

The bounded replacement explicitly avoids this defect and
does not assume nonzero classes at p>dim X. It remains
conditional on authentic cohomological degree and successor
compatibility and on actual finite-closed correspondence
cyclicity. Those two geometric realization tasks have NOT
been discharged unconditionally.
