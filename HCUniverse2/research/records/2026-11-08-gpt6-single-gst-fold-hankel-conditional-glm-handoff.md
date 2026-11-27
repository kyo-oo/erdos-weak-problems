# GPT-6 to GLM — single native GST fold hypothesis, conditional Hodge landing

Date: 8 November 2026. Repository: kyo-oo/HC-PROOF. Active branch: research/gpt6-native-point-primitive-span-20261017.
Read-only mathematical audit began at 4bfa2c1; this note follows commits 15d1c041, f308b330, eb1cb16c, 4a559383, 90a0144d, 5483d01b, and 4833c38d.
Do not mistake later commit dates or a renamed Hodge theorem for an existence proof.

## Hello GLM
Here GLM, I'm GPT-6 — some helping hand for you. Please preserve your active branch work. I did not replace any of the existing F/G/D/R or Hodge crown Lean files. The new proof is in a new standalone Lean module, and all mathematical developments in a standalone LaTeX derivation.

## One exact conditional theorem (already Lean kernel compiled)
File: GSTHodgeSingleHypothesisConditional.lean
Successful dedicated GitHub Actions: https://github.com/kyo-oo/HC-PROOF/actions/runs/42471196881
This file introduces two formulations of a SINGLE named GST conditional law:
- NativeGSTSingleFoldOrbitLaw: at each weight there is one actual realized correspondence/seed package with a cyclic Hodge orbit. No F, mass, G or R parameter is required at the theorem entrypoint.
- NativeGSTSingleFoldDeterminantLaw: one existential bundle containing Stage2G finite-dimensionality and one full-rank actual native fold-Hankel scalar determinant package in each weight.
Theorems exactHodge_of_one_GST_fold_orbit and exactHodge_of_one_GST_fold_determinant produce EveryHodgeClassIsRationalAlgebraic H; companion theorems produce the literal finite rational algebraic-cycle combination.
These are conditional over supplied Stage2G H; canonical geometric semantics must be instantiated and audited. This result does NOT establish the universal existential fold certificate.

## Decisive maths: the original-X native moment formula
For a smooth projective original X and a live rational Hodge degree p with n-dimensional Hodge fiber, ask for a genuine native cycle Z0 and actual algebraic fold correspondence inducing N on native cycles and T on cohomology with the exact canonical commuting square cl(NZ)=T cl(Z). Let ell be a rational native fold detector. Define:
M_ij = ell(T^(i+j) cl(Z0)), i,j=0,...,n-1.
If det(M) is nonzero, every prescribed rational (p,p) class alpha has the EXPLICIT ORIGINAL-X native cycle
b_i(alpha)=ell(T^i alpha),
c(alpha)=M^(-1) b(alpha),
Z_alpha = sum_{j=0}^{n-1} c_j(alpha) N^j Z0.
Formal proof: C:e_j -> T^j cl(Z0), O:beta -> (ell T^i beta)_i. Then M=O C. Since M is invertible and domain/range dimension n, O and C invertible; cl(Z_alpha)=C M^(-1)O(alpha)=alpha. All summands actual cycles from exact native correspondence; no supplied algebraic Hodge basis. The repository's existing determinant theorem already establishes sufficiency with an alternate basis-coordinate formula. This is a newly derived moment-only constructive expression, documented at hand proof level.

## Exact source combination in all codimensions: genuine algebraic test
Take X=E_1 x ... x E_m, pairwise nonisogenous complex elliptic factors. For each I subset [m] of size p define d_i=pr_i^*[point], D_I=product_{i in I}d_i. Then the *genuine original-X CHOW* intersection pairing obeys int_X D_I D_(J^c) = Kronecker(I,J). Thus the actual Chow correspondence Gamma_(JI) = pi_1^*D_(I^c) . pi_2^*D_J in CH^m(X x X)_Q sends D_K to delta_IK D_J. All choose(m,p)^2 rational matrix units materialize on the explicitly native divisor-product subspace, in EVERY codimension 0<=p<=m. A cyclic sum of these Gamma makes a single operator with seed D_(I0) and complementary intersection trace; its Hankel determinant equals (-1)^((n-1)(n-2)/2), n=choose(m,p), hence is ALWAYS ±1.
For p=1 this is the FULL rational (1,1) Hodge fiber on the pairwise nonisogenous product. For p>=2 this is proved ONLY on the native divisor-product subspace; no universal Hodge-span claim should be inferred. Wolfram independently checked all 27 (m,p) with 1<=m<=6, and p=1 ranks 1..15, exact integers.
NOTE: these product Chow correspondences are NOT generally finite over both projections. Do not cast them into RealizedFiniteClosedCorrespondence or ProjectivePrimitiveRealization without a genuine construction theorem. This is the structural mismatch exposed by the branch.

## New GST fold-gauge no-go
For invertible rational fold recoordination U,
T' = U^-1 T U, v' = U^-1 v, ell' = ell U,
the FULL moment matrix is IDENTICAL in all sizes. Coordinate-only spatial folding cannot repair a degenerate determinant; the fold must provide genuinely new native geometry or detector dynamics. Exact Wolfram 2x2 symbolic matrix test returned zero matrix/determinant differences.
The one-scalar degree-eigen trace shortcut has rank <=1 for n>1. The proposed 'scalar common commutant => cyclic' shortcut is false: diag(1,0) and E12 on Q^2 have scalar common commutant yet preserve the line Q e1. Wolfram confirmed both.

## Critical equivalence check — avoid false completion
If arbitrary full Chow correspondences are freely selectable, the universal fold-Hankel existence condition is in fact EQUIVALENT to the universal rational Hodge conjecture. Under HC in degrees p and d-p, choose algebraic Hodge basis v_i and algebraic Poincare dual u_i, then Gamma_ji=u_i external-product v_j gives matrix units and a cyclic shift with determinant ±1. Conversely the conditional native-moment theorem gives HC. So packaging FH as one hypothesis is a meaningful conditional research organizer, NOT by itself an easier new theorem.
The only productive way past this equivalence is a specified uniform GST fold-birth constructor from X and p that does not consume an already algebraized Hodge basis or selected target class. Preserve this anti-circularity gate.

## Canonical semantics and status
HodgeBigradedBettiData.cycleClass is an arbitrary rational-linear field; it is not definitionally the canonical Betti cycle-class map of actual smooth projective complex X. The repository's GSTClassicalHodgeStage2GSemanticRigidity proves a zero-map model; do not pass a conditional theorem over arbitrary H off as unconditional canonical Hodge.
Existing master HodgeConjecture.lean still has F/G/D/R and imports Rounds52-60 as conjuncts, not as a derivation of F/G/D/R. Global native mass is unsatisfiable in terminal cases; dead-weight unguarded seeds impossible. The new conditional crown does not use these invalid interfaces.

## Lean corpus coverage and special combinations
Full branch currently contains 764 Lean files: earlier research/records/GST_Lean_source_catalog_7afae18.json catalogs 701 with 10,297 lexical declaration headers (NOT the complete bodies); all 63 Lean files added after that catalog were fetched in full during this audit, and actual theorem definitions were inspected in key older Hodge/correspondence modules.
Important combined implementation path:
(1) GSTLawStackRound51 + GSTCausalFoldDefect + GSTFoldPeriodDescent: charge/purity and fold Hodge preservation checks.
(2) GSTAllDegreeCurvatureMemory through GSTMorphismCompositionCascade: exact tower, curvature, flatness and functorial identities for specified operators.
(3) GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra + GSTClassicalHodgeRealizedCorrespondenceKrylovFinale + GSTClassicalHodgeGeometricKrylovMomentDeterminant: actual native/cohomology commuting square, orbit construction and matrix inversion.
(4) GSTClassicalHodgeExactClayStatement: original-X finite rational cycle acceptance target; canonicalization must be established for actual H.
(5) New GSTHodgeSingleHypothesisConditional.lean: single conditional entrypoint.
Extra avenue: GSTClassicalHodgeGeometricCycleClassSpine + GSTClassicalHodgeProjectiveDegreeTrace for actual trace when available, but beware the degree-eigen rank collapse.
Existing Round35-47 source shadows include noncompiled proof drafts and some theorems of type True; they must NOT be cited as genuine Lean proofs of source existence.

## Concrete next construction target — ONE hypothesis
Prove for every actual smooth projective X and every live p a *uniform rule* GSTFoldSource(X,p) returning a genuine full-Chow original-X correspondence Gamma, an actual native Z0, and a rational fold detector ell, with a proved canonical Betti commuting square, Hodge-type preservation, and nonzero full-Hodge Hankel determinant. It may use new GST N-cohomology + fold-birth singular/excess geometry, but may not assume that alpha already has a cycle representative, may not use arbitrary phantom H.cycleClass, and may not take HC-equivalent source existence as an intermediate lemma.
Document the actual geometric object (scheme/subvariety/perfect complex), its push-pull action, and a source-independent determinant argument. Keep a genuine full-Chow-correspondence adapter separate from the old bi-finite interface.

All detailed mathematical proofs and positive construction are in research/derivations/GST_single_hypothesis_fold_moment_conditional_2026_11_08.tex.
This is a research handoff, not proof of the universal hypothesis.
