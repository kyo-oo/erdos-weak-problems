# GST full-connection attack: wave/cosmology, CM, curvature, n-cohomology, and the single-fold hypothesis

**Date:** 2026-11-09. **Repo:** kyo-oo/HC-PROOF, branch `research/gpt6-native-point-primitive-span-20261017`. **Starting revision:** `7d1428e6d44a508848a62dc87a5dbf4aeb9683ef`. **Research contract:** for every smooth projective complex original X and rational (p,p) Hodge class alpha, construct a rational algebraic codimension-p cycle on that X with canonical cycle class alpha. This route attacks the existing single-native-fold orbit hypothesis, *without substituting a new surrogate target*.

**Inputs authenticated in the branch:**
- Dimensionless 7-axis arithmetic: `GSTCanonicalSevenAxisBridge`, `GSTGraphV2ProductionLaws`, `GSTGraphV2InformationRecovery`, `GSTGraphV2GeneralRadixConservation`, `GSTGraphV2OmegaWaveLaw` and `GSTGraphV2CanonicalNWave`.
- Unlimited cosmological events: `GSTGraphV2OmniversalCore`, `GSTGraphV2SelfExpandingCosmology`, `GSTGraphV2CausalComponents`, `GSTGraphV2CMNMCoupledUniverse`; the older 3-sector and arithmetic observations are non-dimensional.
- N-shaped arbitrary channel counts and cohomology: `waves/GSTNCohomologyV2`, `GSTMultiChannelHodgeCosmology`, `GSTGlobalPureHodgeCosmology`, `GSTUniversalLefschetzCosmology`.
- Original-X genuine source and wave-CM compatibility: `GSTClassicalHodgeCycleOperatorNaturality`, `GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra`, `GSTGraphV2NativeCurvatureBirth`, `GSTCMQuadraticNativeRankForcing`, `GSTClassicalHodgeCMGSTNativeBasisCompiler`.
- Infinite fold memory: `GSTFoldFourthOrderMemoryTower`, `GSTFoldTowerSquare`, `GSTInfiniteTowerCurvatureCascade`.
- The fixed all-X hypothesis and consequence: `GSTHodgeSingleHypothesisConditional`, `GSTClassicalHodgeRealizedCorrespondenceKrylovFinale`.

## A. Strongest NEW constructive model from combining the existing laws

The actual 12-state dimensionless carry/trit shuffle F has `F^5=id`, and its rational permutation representation on Q^12 has characteristic polynomial

\[
\boxed{(x-1)^4\,(x^4+x^3+x^2+x+1)^2}.
\]

This is a precise new representation-theoretic decomposition of the original wave/carry law: 4 invariant rational directions and an 8-dimensional moving sector, itself two isomorphic 4-dimensional cyclotomic summands. The rational projector on the four invariant directions is

\[
P_{\rm inv} = \tfrac15(I+F+F^2+F^3+F^4),\qquad
\operatorname{rank}_{\mathbb Q}P_{\rm inv}=4.
\]

The full eight-dimensional moving sector is a natural place to couple a rational CM complex structure. Use the 4x4 rational companion matrix C of the fifth cyclotomic polynomial \(\Phi_5(x)=x^4+x^3+x^2+x+1\). Set

\[
S=\begin{pmatrix}C&0\\0&C\end{pmatrix},\qquad
J=\begin{pmatrix}0&-I_4\\I_4&0\end{pmatrix},\qquad
\boxed{T=S+J}.
\]

The exact laws \(S^5=I_8\), \(J^2=-I_8\), \(SJ=JS\) hold. With \(v=e_1\in Q^8\), the 8x8 Krylov determinant is

\[
\boxed{\det(v,Tv,\dots,T^7v)=541\ne0.}
\]

The single-fold operator T therefore has one 8-dimensional **cyclic** orbit. Its characteristic polynomial, exactly checked by Wolfram, is

\[
x^8+2x^7+7x^6+10x^5+16x^4+10x^3-2x^2-4x+1
\]

and is irreducible over Q. Thus this is stronger than a random matrix-rank experiment: it is the representation of multiplication by \(\zeta_5+i\) on the field \(\mathbb Q(\zeta_5,i)\), which has degree eight. The eight conjugates \(\zeta_5^a\pm i\) for a=1,..,4 are pairwise distinct: within each sign set the root is distinct, and equality across signs would require two fifth roots of unity to differ by a complex number of modulus 2 (they would be antipodal), impossible for fifth roots. Thus the degree-eight primitive-element mechanism has a full elementary mathematical proof.

**This is an actual proof of one cyclicity mechanism in the dimensionless-wave/CM representation**, not an assertion that the 8-dimensional field representation is already the primitive Hodge space on arbitrary X.

The model exhibits an important conceptual separation. It is entirely **commuting** (\([S,J]=0\)); curvature birth is not required to get its 8-dimensional orbit. The independently developed noncommutative-curvature route is valuable **when** genuinely geometric A,B do not commute. Do not merge the two into a false commutator claim.

## B. Direct integration into the ORIGINAL-X Hodge cycle calculus

New Lean module `GSTGraphV2IntegratedWaveCMGate.lean` imports the real project geometry, curvature construction and original single-fold conditional theorem. It defines:
- `Mode`: information-wave, CM, native curvature;
- `nativeStep/hodgeStep`: type-correct actions of **genuine** original-X `CycleClassOperatorPair` objects;
- `nativeWord/hodgeWord`: every finite causal mixed word, independent of its length;
- `word_cycleClass`: the **exact naturality theorem** \(cl_X(N_wZ)=T_w(cl_XZ)\) for ALL finite wave/CM/curvature words, proven by induction;
- `originalX_cycle_of_prescribed_reachable_target`: the explicit native witness from any prescribed alpha actually reached;
- `combinedWaveCM`: the single fold \(N_A+N_B\) on native cycles and \(T_A+T_B\) on rational cohomology, with the exact cycle-class compatibility square;
- `combinedWaveCM_iterated_cycleClass`: EVERY Krylov power of that one fold is genuinely native on original X.

These are not invented arbitrary linear operators: the data comes from supplied genuine native operators. The import of `GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra` supplies the existing finite-closed geometric realization path, although a particular seven-axis F realization as a Chow correspondence must still be constructed (not assumed from F^5=id).

This is the exact typed bridge from the 8-dimensional rational model to the preexisting single-fold target. The finite computation motivates **which** actual operator to seek; the new Lean theorems handle **what follows once actual geometric realization exists**.

## C. Strongest exact source-birth gate: global image is invariant

`word_in_cycleClass_range` proves, for every finite mixed word w and actual seed Z,

\[
\boxed{T_w\,cl_X(Z)\ \in\operatorname{im} cl_X.}
\]

The corresponding combined single fold \(T_A+T_B\) has every iterate in the same image. This is useful **source conservation**, and the exact point at which arbitrary n-cohomology channels cannot simply be identified with algebraic geometry.

Let \(W_p=H^{2p}(X,Q)\cap H^{p,p}(X,C)\), and \(A_p=\operatorname{im}(cl_X)\subseteq W_p\). All genuinely native correspondence operations preserve A_p. Therefore they induce operations on the quotient

\[
\boxed{Q_p=W_p/A_p.}
\]

An algebraic seed has zero quotient class, so no finite wave/CM/curvature word applied to that seed can have nonzero image in Q_p. This **does not** show Q_p is nonzero, but it proves that no amount of syntactic branching or infinite event indexing is *by itself* a source of a missing primitive class. If the full orbit is to be everything, the actual wave/CM geometric operators must have sufficient original-X algebraic orbits; deriving this is the hypothesis itself.

An exact 9-dimensional abstract stress test makes the limitation vivid. Extend the Q^8 model by one independent direction with the combined fold acting as zero on the new component; keep the same original seed in Q^8. The orbit still has rank 8, but the ambient rank is 9. No polynomial in the fold can reach the ninth direction. This is a **countermodel to a proposed universal implication from S^5,J^2,SJ=JS to all-space cyclicity**, **NOT a counterexample to the rational Hodge conjecture**.

## D. Non-negotiable CM parity and geometric-wave landing restrictions

- `GSTMathboxCMGeometricComplexStructure.complex_structure_moves_nonzero_off_line` proves that \(J^2=-I\) has no rational eigenline. New `cm_complex_structure_impossible_on_rational_line` specializes this to a one-dimensional rational space. Consequently CM cannot be imposed as an operator squaring to -I on the entire rank-one p=0 Hodge fiber of a connected X. The universal GST fold must admit non-CM/trivial blocks and use CM only on compatible even-dimensional sectors.
- The local F^5=id is a permutation of **carry/trit** cells. The original arithmetic-world event graph has horizontal time/depth increment arrows; F^5 does **not** imply these geometric events return to the same original arithmetic node or produce a degree-preserving algebraic correspondence on X. A bridge translating the local permutation to a canonical algebraic operator is required.
- The operator in `GSTUniversalLefschetzCosmology` is a nilpotent **rectangular WorldCoef digit/carry** map. It is an algebraic model for a Lefschetz-like world operator, **not yet** the canonical cup product by an ample divisor on arbitrary smooth projective X. Likewise, `GSTMultiChannelHodgeCosmology` reconstructs a coordinate module indexed by abstract NShape channels, not a proven basis of \(H^{p,p}(X,Q)\). The exact missing comparison is from these channel spaces to canonical Hodge cohomology preserving rational structure, cup products, primitive polarization, and actual cycle-class images.

## E. The correct n-dimensional extension of the low-dimensional Hodge proof

The classical dimension ≤3 proof uses the actual Lefschetz (1,1) theorem for divisor classes and hard Lefschetz. For a d-dimensional smooth projective X, with an ample algebraic h, Lefschetz decomposition reduces every rational Hodge class of degree 2p to a finite sum of \(h^r\beta_r\), where the \(\beta_r\) are rational **primitive** Hodge classes of lower degree (subject to the standard Lefschetz index restrictions). Every \(h^r\) is an actual algebraic cycle. Consequently the genuinely new source-birth work may target the primitive Hodge sectors, letting algebraic Lefschetz multiplication supply the descendants.

In d=3 and p=2, \(L:H^2(X,Q)\stackrel{\sim}{\longrightarrow}H^4(X,Q)\) reduces to divisor classes. In d=4, p=2, the primitive middle \(H^{2,2}_{prim}\) is an independent geometric source question; the rectangular GST nilpotent map does not automatically instantiate this primitive part.

**Sharper target derived:** construct genuine native GST wave/CM operators on X and seed classes such that their combined fold orbit, after projection to the primitive rational Hodge parts, spans every primitive direction. Compare these actual primitive classes through canonical Betti/de Rham realizations. This is a smaller *structural domain* for the birth mechanism, though not a solved existence theorem.

## F. External papers authenticated through alphaXiv

1. Salvatore Floccari and Lie Fu, *The Hodge conjecture for Weil fourfolds with discriminant 1 via singular OG6-varieties*, arXiv:2504.13607v2 (2026-02-10), https://arxiv.org/abs/2504.13607. **Page 2** explicitly notes generic Hodge–Weil middle-degree classes not obtainable as combinations of intersections of divisors. **Page 3** explains the actual geometric bridge via an OG6 singular locus and algebraic cycles inducing Kuga–Satake correspondences. Project lesson: independent geometric source geometry, not only invariant tensor algebra, is required for exotic primitive classes; the paper's domain is specified Weil abelian fourfolds and their powers.
2. Ziyang Gao and Emmanuel Ullmo, *Hodge cycles and quadratic relations between holomorphic periods on CM abelian varieties*, arXiv:2411.12249v2 (2025-09-15), https://arxiv.org/abs/2411.12249. **Pages 2–4:** the paper constructs explicit quadratic relations among CM periods for A×B with B built from A, but distinguishes Hodge cycles, de Rham–Betti relations and genuinely algebraic cycles. This is mathematical evidence that period/CM relations alone do not certify the required Chow source.
3. Maximiliano Miranda, Hossein Movasati, Lucas Rufino and Roberto Villaflor, *Lengths of Hodge characters in Fermat varieties*, arXiv:2609.27301v2 (2026-09-26), https://arxiv.org/abs/2609.27301. **Pages 1–3:** uses finite character-module operations (join, deletion, permutation, lift) **with geometrically justified preservation of algebraicity** to reduce cases; the claimed theorem concerns degrees <65 excluding 44,51,52, all dimensions in this specified family. This gives a rigorous comparative blueprint for turning the GST n-wave/graph moves into geometric operations, including their exceptional primitive-source cases.

All sources were read through actual alphaXiv PDF pages rather than relying on search headlines. The three results are NOT theorems about the user's new arbitrary-X GST fold.

## G. Outcome and exact next verification task

**Produced:** a full structural 12-state rational decomposition, an explicit field-theoretic degree-8 primitive single-fold cyclic mechanism with determinant 541, an actual original-X Lean operator bridge from ANY finite mixed wave/CM/curvature word and the one-fold sum, a CM rank-one impossibility boundary, and a precise primitive-Hodge/reachable-image geometric test. The Wolfram packet `research/computations/gst_cm_wave_single_fold_cyclotomic8_20261109.wl` was fetched back and executed in exact rationals, verifying all stated finite results.

**The geometric hypothesis is not fully derived from these inputs.** The first missing arrow is not the formal cyclicity calculation; it is a *canonical functorially constructed wave or CM native correspondence* on arbitrary X (including its non-CM primitive sectors), with an actual off-image primitive-birth property independent of already knowing the desired representative. The largest available meaningful test is now to construct that on a chosen primitive sector not spanned by divisors, via actual algebraic correspondences from new auxiliary geometry, and prove source-return to X.

**Status evidence:** read the targeted Lean workflow https://github.com/kyo-oo/HC-PROOF/actions/workflows/gst-integrated-wave-cm-gate.yml and its most recent completed run. Only a completed green run supports the newly edited declarations; the earlier initial-version run 42662296814 was observed **SUCCESS**.
