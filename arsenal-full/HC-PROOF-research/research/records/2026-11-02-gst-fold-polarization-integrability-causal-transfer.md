# GST spatial folds: polarization, integrability and constructed causal cycles

Date: 2 November 2026. Initial checkout: `c6b81801058958b6b8237970932313391933e752`.
Reconciled publication base: `05a27588a17d3f611d2219b5e0b496272a28816a`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

The owner's proposed experiment is executed as three routes below. Universal
Hodge truth is permitted as an explicit conditional thought experiment, never
used as evidence for itself. The unconditional original-X target remains the
one in AGENTS.md. Mathbox research-program, literature-check, proof-audit and
computation-audit protocols were applied. Wolfram was actually executed; there
is no separate computational Mathbox engine API exposed in this environment.

## Exact results

**A. A constant integral rotation produces projective geometry.**
For any finite free integral lattice and integral `J` with `J²=-I`, choose any
positive integral symmetric form `b` and construct

`g_J(x,y)=b(x,y)+b(Jx,Jy)`, `E_J(x,y)=g_J(Jx,y)`.

This gives positive `E_J(x,Jx)=g_J(x,x)` and an integral alternating form.
The actual torus `(Lambda_R,J)/Lambda` is projective and isomorphic to a
power of `E_i`. Every rational Hodge class there is a rational combination of
actual divisor products in every codimension. The hand derivation constructs
the `s²` coordinate/diagonal/CM-graph divisor generators and proves their full
span by exterior algebra, supplying the geometric character expansion at this
torus for the existing CM native-word/coefficient-descent pipeline.

This strengthens Round 31's lattice-skeleton scope by constructing a *chosen*
polarization. It does not force a preassigned geometric polarization to work.
The projectivity and elliptic-power Hodge theorems are known; no global novelty
claim is made. No universal domination of arbitrary X by these tori is claimed.

**B. A variable positive fold can fail the differential integrability test.**
On the actual compact four-torus take `f(x1)=2+sin(2*pi*x1)` and

`J d1=d2`, `J d2=-d1`, `J d3=f*d4`, `J d4=-d3/f`.

The square equation holds, and the fixed closed symplectic form is positive
on `(v,Jv)`. Nevertheless

`N_J(d1,d3)=(f'/f)*d3`, with coefficient `pi` at `x1=0`.

Within this ansatz integrability holds exactly when f is constant on the
connected periodic circle. For constant f the actual projective complex
torus is `E_i x E_(i/f)`. External deformation parameters and spatial
coordinates are distinct. Products with every original X retain the nonzero
Nijenhuis component, in every larger stabilized dimension. This is a genuine
smooth almost-Kaehler fold, outside complex-projective Hodge geometry; it is
not an HC counterexample.

**C. Causal defects have an exact propagation equation, and actual cycles can
be constructed along compatible paths.**

`D_(J,L)(S*T)=D_(K,L)(S)*T+S*D_(J,K)(T)`.

The full word law sums the transported edge defects. Safe edges give safe
paths; endpoint safety can occur by cancellation of unsafe edges. A reflection
gives a concrete nonzero edge defect but its square is the identity. The
Graph V2 General Space realization now uses this exact equation on actual
forward-path compositions.

`nativeCycleTower` constructs a seed cycle's full transported expression;
`nativeCycleTower_class` derives its class at every finite depth from actual
naturality. The new `GSTLawStackRound51Actual.rides_always_gives_constructively`
uses this construction. The old explicitly labelled shape record is retained
for provenance but supplies no premise to the new proof. The realization and
actual seed remain inputs; the theorem does not assert their universal coverage.

## Actual arbitrary-X attempt and its calculated return

For the prescribed `(X,p,alpha)`, the doubled rotation `J(x,y)=(-y,x)` exists
on every cohomology carrier, and `(J-I)(y-x,-x-y)=2(x,y)`. It has the rational
inverse `-(J+I)/2`, with the exact integral parity door.

There is a genuine algebraic realization on `Y=X disjoint_union X`: the signed
swap graph correspondence. It acts on both actual Chow and Betti classes by
the same rotation and commutes with the canonical class map. Component
inclusion/return gives `(alpha,0) algebraic on Y iff alpha algebraic on X`.
Thus the bare rotation-operator existence question is closed on a doubled
realization for every original X. Its original-X source defect is preserved.
Here J is an endomorphism of the existing Hodge structure, not a new weight-one
complex structure on X. Reassigning its eigenvalues to Hodge bidegrees changes
the realization and cannot be silently used in the return.

A target-sensitive actual auxiliary divisor was also constructed: after
clearing denominators in alpha's Betti coordinates a, use
`f_+(z)=z0+sum(a_j*z_j)` and `f_-(z)=z0-sum(a_j*z_j)` on `E_i^(r+1)`.
Their point-divisor pullback difference has matrix
`2*(e0*a^*+a*e0^*)`, exactly linear in a. This creates a genuine algebraic
encoding of the target in the folded space. It encodes non-Hodge Betti vectors
as well, so its existence cannot itself detect original-X algebraicity.
An algebraic return matching arbitrary prescribed alpha was not constructed.
That continuation remains open; it is not relabelled as an easy existence lemma.

## Source and branch reconciliation

The initial checkout had 725 tracked Lean files and 86 tracked LaTeX files.
Fetching revealed the branch had advanced through Round 51. Those commits were
fast-forwarded and the local work reapplied, preserving every upstream change.
The reconciled base contains **744 Lean files and 105 LaTeX files**. These
counts are an inventory, not a semantic review of every proof.

Actual source reviewed includes General Space ontology, cohomology/native path
realization, Graph V2 realization and recursive state causality, the relevant
higher-causality sections, scheme dimension observation, dimension-corrected
Hodge synthesis, the all-N fold API, CM native divisor-word/descent interfaces,
the prior binary-decision/causal alignment audits, Round 31's emergence result,
and the latest Round 50/51 records and Round 51 Lean source. The new theorem
does not treat Round 51's address-orbit coverage as coverage of every class
vector: two independent divisors on P1 x P1 already share one Hodge address.

## External theorem verification

Checked author-hosted primary sources on 2 November 2026:

- J. S. Milne, *Abelian Varieties*, v2.00 (March 2008), Chapter I,
  Lemma 2.4 and Theorems 2.8--2.9, printed pp. 13--14.
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>.
  Verified: an integral positive Riemann form gives an algebraic complex torus,
  and analytic homomorphisms between such tori are algebraic. Milne's form
  convention has `E(Jx,x)>0`; our form is its negative. The sign translation
  is explicit in both the derivation and executable matrix checks.
- J. S. Milne, *Shimura varieties and moduli*, author-hosted Handbook chapter,
  printed p. 519, Step 1. <https://www.jmilne.org/math/xnotes/svhIP.pdf>.
  Verified: rational Hodge classes on powers of an elliptic curve are generated
  by divisor classes. Our explicit CM divisor calculation also proves the
  needed special instance directly. Overlap label: known after translation.

No new OpenAI-paper theorem was imported or represented as a new axiom in this
update. Earlier pinned source analysis remains historical evidence only.

## Evidence, commands and proof status

- Five new Lean modules (four mathematical APIs and one integration entry),
  two existing modules strengthened; **38 new theorem declarations**, all drafts.
- `python research/experiments/gst_spatial_fold_run.py`: complete local run,
  exit 0. Independent Python exact arithmetic versus actual Wolfram execution:
  all 15 rotation/polarization rows, 20 exterior rows, 28 causal rows and 16
  variable-jet rows agree. Wolfram: **442 assertions**, kernel runtime
  **0.901588 seconds**, kernel **15.0.1 Linux x86 (64-bit)**. Remote process
  exit status is not exposed and is recorded as null.
- Local bounds: complex rotation ranks 1--5, three explicit unimodular
  conjugates each; all 81 targets in [-4,4]^2, brute integral witnesses in
  [-8,8]^2; actual exterior/divisor spans on E_i^s for s=0--4 and all
  p=0--s+1; matrix sizes 1--4 and causal word lengths 0--6; 16 first jets and
  all 81 energy vectors in {-1,0,1}^4 for each jet. No extrapolation from these
  ranges is used as a universal proof.
- Changed-module escape scan, explicit root registration and parsed local
  import acyclicity pass. Three pre-existing lexical header anomalies
  (the two Comparator smoke files and upstream Round 40) were verified
  byte-identical to `05a2758` and preserved.
- `python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py
  research/computations/gst_spatial_fold_20261102.manifest.json --root .`:
  actual Mathbox v2 manifest validator passes with current input/output hashes.
- `git diff --check` passes. No local Lean installation, build, kernel axiom
  audit, fresh CI result or LaTeX render is claimed. Owner entry point:
  `lake build GSTSpatialFoldUpgrade`.

The raw evidence records one invalid Wolfram source attempt: a missing closing
bracket in the nested exterior-product function. Held parsing and a local
bracket scan isolated it; the complete corrected program was rerun. An initial
Python import-name mismatch was also fixed against the actual existing lexer.
These implementation failures are not mathematical counterexamples or positive
evidence. Author-side algebra review corrected an early sign/order error in the
door witness before the successful exact runs.

**Proof-audit provenance: self-review**, not independent-agent review.
Constant-fold polarization and the stated torus theorem: proved at hand level,
with the external projectivity implication verified. Variable-fold obstruction
and causal equations: proved at hand level. Finite assertions: computationally
verified only in the stated ranges. Lean: uncompiled drafts. The original-X
constructor: not obtained; universal rational HC is neither proved nor refuted.

Next concrete open route: construct an original-X-compatible algebraic return
for a target-sensitive folded source without defining its action to be alpha.
The doubled signed-swap route alone is closed as a source-birth mechanism;
the differential-fold route remains open only with a new integrable geometry
and an independently justified canonical return.
