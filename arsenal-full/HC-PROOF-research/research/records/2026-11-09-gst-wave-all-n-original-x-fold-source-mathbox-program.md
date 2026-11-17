# GST Mathbox synthesis — all-N wave cyclicity and geometric source construction
Date 2026-11-09. Branch research/gpt6-native-point-primitive-span-20261017. Starting commit c41e7b98866e0f6183f4fa36c177aa0350967269.

## Exact typed research target

Connect the user's dimensionless seven-axis x4/base3 information graph, actual Wave-I SURVIVE current, Wave-II hole/cosmology, the CM mirror J, arbitrary-order curvature, canonical rational cohomology, and original-X algebraic-cycle construction. The result must have an independently constructed original-X cycle class, not an arbitrary reverse Hodge-to-Chow map.

## 1. Actual dependency chain

GSTCanonicalSevenAxisBridge + GSTGraphV2InformationRecovery: on physical cell (carry,trit) in Fin4 x Fin3, the GST information shuffle is reversible, U^5=id. These are information coordinates, not seven spatial dimensions.

waves/GSTWaveCohomology + GSTGraphV2CMWaveFusion: original discrete Gauss equation mixedDensity = horizontalCoboundary + verticalCoboundary + 56*SURVIVE; Wave-I current M(s)=surviveI(s), with values M(1,1)=1, M(2,2)=1, M(3,2)=2, others 0. A rational CM mirror phase J on the original 12 cells satisfies J^2=-I and UJ=JU. Combined Wave-I+CM+information fold T=U+J+M.

waves/GSTNCohomology + GSTGraphV2WaveNShapeCompiler: arbitrarily many independent N-hole wave channels, each with a wave fold T_s(u)_i=(T+10*channel(i) I)u_i. NShape channels are mathematically injective by definition. This is emergent algebraic rank, not a metric dimension.

GSTFoldTowerSquare + GSTInfiniteTowerCurvatureCascade + GSTGraphV2CMInfiniteCurvatureBridge: curvature at all formal jet orders, original [J,M] defect and exact order-sensitive holonomy. GSTGraphV2NativeCurvatureBirth: actual algebraic commutator cycle N_A N_B Z-N_B N_A Z and canonical Betti class equation. GSTHodgeGSTWaveGeometricCompiler: old native wave compiler previously assumed source-intertwining.

GSTUniversalCodimensionTwoPrimitiveExtraction: actual Hard Lefschetz divisor correction for arbitrary X and p2, leaving a rational primitive input. GSTHodgeSingleHypothesisConditional: from an actual original-X cyclic native orbit covering Hodge fiber to rational cycle representative.

## 2. Wave-I matter changes cyclic rank

Exact rational Wolfram of the EXISTING original 12-cell wave operator from the original mixed axial/rotating seed gives rank Krylov(U+J) = 10 and rank Krylov(U+J+M) = 12. The latter 12x12 determinant is -1149656584000. The CM parity defect [J,M] has rank six. Since U^5=I, J^2=-I, UJ=JU, the source-free operator U+J satisfies the degree-ten resultant polynomial of y^5−1 and (t−y)^2+1. Adding the genuinely defined Wave-I matter M breaks this degeneracy and supplies two extra independent wave directions. This is a rigorous finite wave-space statement, not a geometric Chow algebraicity claim.

## 3. Sixfold geometric quotient obstruction and finite-prefix repair

Original GLM sixfold X=E1x...xE6, p2 has 15 independent divisor-product cycles and rank9 primitive divisor-product subspace. Previously projected GST wave orbit had rank9. For the specific projection Q:Q^12->Q^9, rank Q=9, rank stack(Q,Q T)=12: kernel Q is not invariant, so a full 12→9 T-equivariant geometric fold does not exist. Stronger: char_T=(t−2)^2*q10(t), irreducible q10 of degree10, so no rational T-invariant 9-dimensional quotient.

Correct repair: choose first nine wave-generated independent algebraic primitive cycle classes K:Q^9->Q^15, rational geometric dual L with LK=I, and a nine-cycle permutation C. New genuine Chow-correspondence operator N=K C L matches the first nine wave-generated orbit cycles, is primitive-preserving, and has anti-diagonal moment Hankel determinant +1. This does NOT claim N matches T on the whole 12d wave space. Exact committed and executed: research/computations/gst_wave_sixfold_native_cycle_fold_completion_2026_11_09.wl. The general native cyclic fold and canonical class commuting square are Lean verified in GSTHodgeWaveFiniteCyclicCompletion.lean (CI 42658764537 SUCCESS).

## 4. Sevenfold full 24d-wave-to-14d-original-Chow intertwiner

Take X=E1x...xE7 CM elliptic product; D_I=product point divisor classes for |I|=2 form a 21d rational algebraic sector. The ample h=sum d_i gives genuine primitive correction P=I−L (L^5)^{-1} L^4 of rank14. There are 14 independent primitive rational algebraic cycle classes; all duals are rational intersection pairings.

For two independent N-hole wave channels, set T24=diag(T,T+10I). Its second channel admits a 2d invariant quotient Q2 from the left generalized eigenspace of (T−2I)^2, and Q14=diag(I12,Q2) gives a genuine rank14 equivariant quotient Q14 T24=B14 Q14.

Take actual 14 independent primitive Chow vectors K:Q^14->CH^2(X)_Q and their geometric dual D:CH^2(X)_Q->Q^14 with DK=I. Define Phi=KQ14 and original-X fold N_X=K B14 D, representable by genuine CH^7(XxX)_Q matrix-unit correspondences pr1^*D_(I^c) pr2^*D_J.

Then for ALL original 24 wave inputs, N_X Phi=Phi T24 exactly. Exact rational Wolfram verifies primitive rank14, full wave intertwining True, native cyclic orbit rank14, no primitive leakage, and anti-diagonal geometric Hankel determinant -1. Reproducible committed script research/computations/gst_wave_cm_two_hole_sevenfold_full_native_intertwiner_2026_11_09.wl fetched and executed unchanged.

## 5. All-N source eigenfunctional: strongest general result

Original fixed information cells c0=(0,0) and cInfinity=(3,2) give the natural rational wave readout

  ell(u)=u(c0)-u(cInfinity).

Directly from the ORIGINAL U,J,Wave-I M operators,

  ell(T u)=2 ell(u), and ell(seed)=1.

For ANY NShape s with n holes and pairwise distinct channels a_i, define Q_s(u)_i=ell(u_i). This is a surjective rational linear quotient (explicit lift supported at c0) and for the ENTIRE original N-hole fold,

  Q_s(T_s u)_i = (2+10 a_i) Q_s(u)_i.

Thus ker(Q_s) is invariant. The uniform Wave-I source has orbit signature Q_s(T_s^k seed)_i=(2+10a_i)^k. Its n-by-n rational Vandermonde determinant is

  product_{i<j}(10 a_j−10 a_i) = 10^[n(n−1)/2] product_{i<j}(a_j−a_i) != 0,

for every n≥1. n=0 is a trivial zero module. Hence an arbitrary finite number of N-hole wave channels has a single cyclic source with a genuinely invariant quotient. Canonical channels i=0,...,n−1 yield determinant 10^[n(n−1)/2]*product_{k=1}^{n−1} k!.

Lean GSTHodgeWaveAllNHoleReadout.lean proves the actual eigen-readout, all-N wave intertwiner, surjectivity, fixed source, eigenvalue injection, orbit formula and kernel stability; CI 42661044006 SUCCESS. The Vandermonde determinant uses the exact classical algebraic formula (paper derivation); it was not separately kernel-proved in that module. Exact Wolfram tests n=1..10 all passed using committed research/computations/gst_all_n_wave_vandermonde_primitive_chow_2026_11_09.wl.

GSTHodgeWaveAllNGeometricLanding.lean synthesizes actual native/Betti operators, their class naturality, and entire wave-input intertwining from *given genuine native cycle frames and geometric Betti-dual functionals*. It constructs the earlier WaveNativeCompiler instead of taking its intertwining field as a supplied hypothesis. Its distinct source-frame data still must arise independently from actual geometry on X.

## 6. Arbitrarily high codimension-two geometric rank

For m≥4 choose X_m=product of m pairwise nonisogenous CM elliptic curves. The rational algebraic divisor-product codim2 sector has dimension C(m,2). Cup by ample h=sum d_i from divisor classes is injective for m≥3 because its coefficient on d_i d_j is c_i+c_j, and three indices imply c_i=0 for all i. The Hard Lefschetz primitive projector P=I−L (L^{m−2})^{-1} L^{m−3} has primitive rank

  r_m=C(m,2)−m=m(m−3)/2.

The polarized primitive (2,2) intersection pairing ∫_X x y h^{m−4} is rational and nondegenerate on this algebraic sector (Hodge-Riemann), hence supplies actual algebraic duals to a selected frame.

For EVERY n finite, choose m=n+4 so r_m≥n and select n primitive independent algebraic source cycles and their genuine duals. The all-N GST wave quotient can be realized by Chow correspondences on this X_m in a genuine n-dimensional primitive cycle sector. This is an all-rank FAMILY construction for *some* smooth projective X_m, not a declaration about an arbitrary prescribed X. Wolfram exact tests m=4..9 show primitive ranks 2,5,9,14,20,27, idempotent projector, primitive Lefschetz test=0 and nondegenerate Gram matrices (same committed all-N WL script).

## 7. Which geometric source input the combined engine needs next

Fix arbitrary original X, codimension p, prescribed rational Hodge class alpha. Hard Lefschetz/Lefschetz (1,1) builds the known algebraic descendant/correction; focus the new wave/CM curvature apparatus on the primitive remainder alpha_primitive.

The spectral/hole rank of an abstract wave does NOT independently construct a Chow class outside the image of the canonical cycle map of that original X. An actual cycle-preserving fold necessarily keeps its iterates in the known canonical Chow image. The missing independently geometric input is an alpha-sensitive algebraic incidence, CM native basis packet, genuinely geometric world-birth event, or deformation/specialization cycle whose actual class provides new coverage of the prescribed primitive Hodge direction. The precise type is a new original-X CH^p source with canonical period coupling and actual geometric correspondence operator (not an assumed inverse cycle class).

The relevant existing interfaces are GSTClassicalHodgeCMGSTNativeBasisCompiler.CMGSTNativeSheetProgram, GSTGraphV2SelfExpandingCosmology.NativeGeometryBirth.GeometricCycleBirthRealization and the now constructed GSTHodgeWaveAllNGeometricLanding. The remaining task is to produce and verify real geometric packets for original-X primitive targets, NOT to prove another finite wave Vandermonde theorem.

## 8. External mathematical source checks by alphaXiv

Mauro Varesco, Hodge similarities, algebraic classes, and Kuga-Satake varieties, arXiv:2304.02519v3: algebraicity of certain Hodge similarities when Kuga-Satake geometric conditions hold, not a universal correspondence from all X.
Katzarkov/Kontsevich/Pantev/Yu, Birational Invariants from Hodge Structures and Quantum Multiplication, arXiv:2508.05105v2: Hodge atoms and spectral blowup formula, not universal Hodge cycle manufacture.
Pedro Magalhaes, Products in absolute Hodge cohomology and mixed Hodge formality, arXiv:2609.21034v1: mixed Hodge formality and Deligne-Beilinson Massey obstruction, not cycle-class surjectivity.
Miranda/Movasati/Rufino/Villaflor, Lengths of Hodge characters in Fermat varieties, arXiv:2609.27301v2: explicit algebraic join/deletion/lift operations for stated Fermat families. Especially useful source-generating benchmark, not arbitrary X.

## 9. Verification and source provenance

All symbolic and sixfold/sevenfold calculations use exact integers and rationals and are reproducible in the committed WL files above. New cyclic Lean CI 42658764537 SUCCESS; original wave geometrical compiler CI 42653636415 SUCCESS; all-N wave quotient CI 42661044006 SUCCESS. The final all-N readout AND native geometric landing both passed targeted Lean kernel build in GitHub Actions run [42662133254](https://github.com/kyo-oo/HC-PROOF/actions/runs/42662133254) at commit 528c6b220e2c50105f88caa12449b202cd6e3187, job 129317557679, with explicit log confirmations LEAN PASSED: GSTHodgeWaveAllNHoleReadout and LEAN PASSED: GSTHodgeWaveAllNGeometricLanding. The interface's naturality and full wave-source intertwining are actual Lean theorems, while existence of the geometric source frame on arbitrary original X remains a separately typed input. This is a Mathbox self-audit, not independent referee confirmation. No new axioms of algebraic target representation are introduced by these constructions.
