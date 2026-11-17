# GST Hodge: one-hypothesis mathematical compression and exact fold-moment audit

**Date:** 9 November 2026  
**Repository:** kyo-oo/HC-PROOF  
**Work branch:** research/gpt6-native-point-primitive-span-20261017  
**Scope:** new mathematical reduction, adversarial source-geometry audit, and GLM handoff. This document neither asserts unconditional HC nor makes unverified Lean claims.  
**Companion native Lean module:** `GSTHodgeFoldGaugeMomentRigidity.lean` (kernel-compiled on pinned Lean, GitHub Actions run 42520460148, SUCCESS).  
**Existing kernel-green conditional root:** `GSTHodgeSingleHypothesisConditional.lean` (run 42471196881).

## 1. The exact single GST hypothesis, with its genuine geometry boundary

For a connected, pure-dimensional smooth projective complex original variety X of dimension d and a codimension p, put

\[
W_p(X)=H^{2p}(X,\mathbb Q)\cap H^{p,p}(X,\mathbb C),\qquad
A_p(X)=\operatorname{im}\bigl(\mathrm{cl}^{\mathrm{can}}_{X,p}\bigr)\subseteq W_p(X).
\]

The *candidate single geometric target* is **GST Canonical Native Fold Orbit Birth**:

> For every such X and p with nonzero W_p(X), the fixed, independently specified GST geometric fold-birth procedure constructs: (i) a genuinely algebraic cycle S in CH^p(X)_Q; (ii) an actual algebraic correspondence \Gamma in CH^d(X×X)_Q of degree zero, with a canonical whole-Betti operator T_\Gamma obtained from the push-pull kernel and the genuine native operator N_\Gamma on rational algebraic cycles; and (iii) an orbit with \operatorname{span}_{\mathbb Q}\{T_\Gamma^j\mathrm{cl}^{can}(S):j\ge0\}=W_p(X). The procedure must not take a previously known algebraic representative of the desired Hodge class or a pre-existing algebraic Hodge basis as an input.

For zero Hodge fibers the zero cycle is the complete answer; a nonzero seed is not required. For disconnected or non-equidimensional smooth projective schemes, handle the finitely many connected pure-dimensional components separately. A full semantic adapter must identify the *actual canonical* cycle class with the historical Stage-2G supplied `H.cycleClass` before this is promoted to a statement about classical Hodge geometry.

This is ONE named universal GST construction law, but it is *not yet proved*. Its orbit saturation content is necessarily HC-strength without a restrictive, independently defined geometric construction procedure. A rename does not make the logical implication easier.

**Conditional exact output.** Suppose the canonical GST law holds. Let n=dim_Q W_p(X). Select any rational linear functional ell on W for which the n×n fold Hankel moment matrix is nonsingular:

\[
M_{ij}=\ell(T_\Gamma^{i+j}v),\quad v=\mathrm{cl}^{can}(S),\quad 0\le i,j<n.
\]

Define b_i(alpha)=ell(T_\Gamma^i alpha), c=M^{-1}b, and the **actual original-X native cycle**

\[
\boxed{Z_\alpha=\sum_{j=0}^{n-1}c_jN_\Gamma^jS.}
\]

The true native/cohomology square proves \mathrm{cl}^{can}(N_\Gamma^jS)=T_\Gamma^jv. Let C:\mathbb Q^n\to W map e_j to T_\Gamma^j v and O:W\to\mathbb Q^n map beta to (ell(T_\Gamma^i beta))_i. Then M=OC. Invertible M implies both C,O are isomorphisms (n-dimensional). Hence \mathrm{cl}^{can}(Z_\alpha)=C M^{-1}O alpha=alpha. This is an exact constructive conditional proof; it uses neither a target-specific preimage hypothesis nor assumed Hodge basis cycles as inputs.

## 2. NEW exact equivalence: arbitrary detector exists iff the orbit is cyclic

Let W be any n-dimensional rational vector space, T:W→W linear, v∈W.

**Theorem (anti-triangular GST detector).** If v,Tv,...,T^(n−1)v are a basis, define ell by
ell(T^jv)=delta_{j,n−1} for 0≤j<n. Then the Hankel M_ij=ell(T^(i+j)v) satisfies M_ij=0 for i+j<n−1 and M_ij=1 for i+j=n−1. The entries beyond that anti-diagonal can be arbitrary. Multiplying M by the reversing permutation matrix produces a triangular matrix with diagonal 1; therefore

\[
\boxed{\det M=(-1)^{n(n-1)/2}\ne0.}
\]

Conversely, if any ell yields det M≠0, the vectors v,Tv,...,T^(n−1)v must be linearly independent: if a nonzero vector of coefficients c has ∑_j c_j T^jv=0, then M c=0 because each i-th row applies ell∘T^i. Since the vectors are n in an n-dimensional space, they form a basis.

Therefore
\[
\boxed{\text{cyclic orbit }(T,v)\ \Longleftrightarrow\
       \exists\,\ell\in W^*: \det[\ell(T^{i+j}v)]_{i,j<n}\ne0.}
\]

The freely chosen detector does not supply an independent geometric gain; it only tests existing cyclicity. For n=0 the target is zero and is handled separately. A detector fixed independently by genuine GST geometric trace/curvature data would be a *stronger and potentially more useful* construction problem than an arbitrary dual-basis detector.

**Wolfram exact test:** for symbolic companion matrices of ranks 2, 3, and 4 and the last-coordinate detector, the determinants were respectively −1, −1, +1, with no numerical tolerance. These cases verify the algebra; the preceding proof establishes the all-n statement.

## 3. Exact gauge no-go and detector no-go, recorded in Lean

For a rational invertible GST coordinate fold U, consistently transport the triple by
\[
T'=U^{-1}TU,\quad v'=U^{-1}v,\quad \ell'=\ell U.
\]
Then \ell'((T')^k v')=\ell(T^kv) for every k. In particular
\[
M(T',v',\ell')=M(T,v,\ell),\quad \det M'=\det M.
\]

The new `GSTHodgeFoldGaugeMomentRigidity.lean` implements and proves this identity over arbitrary rational modules, along with the following obstruction:

If \ell(Tx)=lambda\,\ell(x) for all x, then \ell(T^kv)=lambda^k\ell(v). The 2×2 moment minor satisfies
\[
m_0m_2-m_1^2=0.
\]
Thus a degree trace acting as a left eigenfunctional cannot by itself certify cyclicity of a Hodge fiber of dimension at least two.

**Implication for GST spatial folds:** an invertible recoordination of existing native algebraic sources and a fixed degree-eigencharacter detector cannot increase the moment rank. Any successful fold mechanism must add new **actual geometric source/mixing data**, not simply a new presentation of the same native image.

## 4. Load-bearing modules — exact combination and what they supply

| GST root | Valid supplied ingredient | Do not silently infer |
| --- | --- | --- |
| `GSTClassicalHodgeExactClayStatement` + `GSTGeometricRealizationStage2G` | exact rational Hodge target in supplied Stage-2G data | canonical analytification, actual Hodge decomposition or canonical Betti class maps automatically constructed |
| `GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra` | genuine left-finite closed correspondence carrier, native point operators and specified Betti actions | the Betti action is forced on off-algebraic classes by the point equality alone |
| `GSTClassicalHodgeCorrespondenceSemanticFirewall` | internal countermodel to falsely free Betti action | that a chosen action is canonical |
| `GSTClassicalHodgeAmbientCorrespondenceKernelAction` + `GSTClassicalHodgeStrictCorrespondenceGeometricTransferFinale` | kernel action from full Betti cup and Gysin, with explicit intersection/point-class inputs | construction of those inputs for every arbitrary X inside the pinned Mathlib or all Chow correspondences supported by finite-fiber API |
| `GSTClassicalHodgeRealizedCorrespondenceKrylovFinale` + `GSTClassicalHodgeGeometricKrylovMomentDeterminant` | exact native orbit, conditional span and moment-matrix inversion | universal geometric cyclicity/nonzero moment |
| `GSTHodgeSingleHypothesisConditional` | **kernel-green** conditional exact-Hodge and finite-sum theorem | unconditional Hodge |
| `GSTCausalFoldDefect`, `GSTFoldPeriodDescent`, `GSTSpatialFoldResearch` | charge, full period and fold-defect compatibility tests | algebraic source birth from formal Hodge purity |
| `GSTFoldTowerSquare` + `GSTInfiniteTowerCurvatureCascade` + `GSTCarrierAlgebraFlatComplex` + `GSTMorphismCompositionCascade` | all-order differential/curvature and functoriality machinery | target-dependent canonical Chow source |
| `GSTClassicalHodgeGradedFiniteClosedCorrespondence` | graded native point transport | a full Chow correspondence push-pull package |
| `GSTClassicalHodgeStage2GSemanticRigidity` | formal zero-cycle-class countermodel | an unconditional classical theorem over arbitrary Stage-2G H |

The older global native-mass branch has a terminal-successor counterexample; unguarded nonzero seeds demand nonzero Hodge fibers at dead weights; the self-map-only two-generator action is too narrow. The new single-fold target requires NONE of those as separate assumptions.

## 5. Exact geometry adapter gap (not a fresh HC hypothesis)

For X=∏_{i=1}^m E_i (pairwise nonisogenous elliptic curves), the existing 2026-11-08 LaTeX derivation computes actual Chow correspondences of codimension m:

\[
\Gamma_{JI}=\pi_1^*D_{I^c}\cdot\pi_2^*D_J,\qquad
(\Gamma_{JI})_*D_K=\delta_{IK}D_J.
\]

Here I,J,K index p-subsets and D_I are genuine products of factor point divisors. This realizes the GST matrix units on the explicit native sector of rank binomial(m,p) and yields a cyclic orbit with nonsingular Hankel matrix **for that sector**. It does not claim to exhaust every rational Hodge direction at p>1.

The product correspondences generally fail the branch's finite-left-fiber interface. Do not treat them as `FiniteClosedCorrespondence` or `SchemeBiFiniteClosedCorrespondence`. A real full-Chow adapter requires:
1. a source type of genuine rational codimension-d cycles on X×X, including products of cycles;
2. construction of native Chow push-pull on every codimension-p cycle, not only point-finite incidence;
3. the corresponding *whole-Betti* action induced by the same geometric class with correct degree;
4. a commuting square with the canonical Betti cycle map;
5. extraction of the Hodge-compatible operator and exact Krylov native iteration.

These are **typed implementation/geometry tasks**, not five new HC-strength assumptions. The claim that this adapter is already Lean-complete would be false. Older incidence and Gysin packets remain useful ingredients.

## 6. Falsifiable critical-path target

**ONLY HC-strength target (GST-FOLD-BIRTH):** develop one specified GST fold source-birth construction on arbitrary original smooth projective X whose output is an actual Chow correspondence and actual native seed with a cyclic Hodge orbit, without assuming an algebraic Hodge basis or preimages for the prescribed target. Its canonical Betti action must be forced by the genuine geometric kernel; finiteness of cohomology and standard canonical semantics are setup, not disguised Hodge assumptions.

**Cheapest decisive first test:** test the construction on a genuine Hodge sector of rank >1 not generated by the universally available ample-power class, and compute the full canonical native-vs-Betti coupling, before lifting to all X. A nonzero determinant for the explicit divisor-product sector does not resolve this test.

**Mathematical pass:** a standalone proof constructs the actual fold cycle operator and verifies cyclicity for all relevant original X, with no target-algebraic input. **Mathematical fail:** one explicit admissible X,p whose available fold source is confined to a proper invariant subspace, or a correspondence which is not an actual Chow geometric correspondence despite claimed origin. Bounded Wolfram cases and Lean statements with the orbit law as a hypothesis count neither as a universal pass nor as evidence that no construction can exist.

## 7. Verification and source-integrity record

- Existing isolated one-hypothesis conditional Lean root: **GitHub Actions run 42471196881 SUCCESS**, separate from this note.
- Companion fold-gauge and eigen-detector Lean module: **GitHub Actions run 42520460148 SUCCESS** at commit `7327f8e10d82cb0e8fd764de38a91a3643384757`. The job completed its kernel compilation step and its `sorryAx`/`sorry` guard; the retrieved job log explicitly reports `LEAN PASSED: GSTHodgeFoldGaugeMomentRigidity`.
- Wolfram symbolic companion-vector tests: dimension 2 determinant −1, dimension 3 determinant −1, dimension 4 determinant +1.
- Corpus mapping: GLM's `research/records/2026-11-08-gpt6-hc-764-lean-module-inventory.md` inventories **all 764 tracked Lean paths**, using prior 701-file lexical catalog plus 63 post-catalog full-source fetches. This is NOT an independent line-by-line review of all 764 proof bodies.
- No changes to GLM's active files or original universal-Hodge public root were made in this audit. All new arguments are isolated in new artifacts.
