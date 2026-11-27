# Mathbox — native residual Euler kernel, complete alterations, and the exact linear-source leaf

- Date: 2026-10-20 (session date).
- Original goal: every rational Hodge class on every original smooth projective complex X has an actual rational algebraic cycle on that same X with its canonical Betti class.
- User-directed scope: identify the actual remaining implication and attack it by mathematical derivation using the repository's GST constructions and Wolfram. No web/literature search, new Lean implementation, or agent delegation.
- Base: c2479cac309ce2379c47e77b912f93183923e9b2 on research/gpt6-native-point-primitive-span-20261017. Fresh branch inspection found no intervening user commits.
- New mathematical artifact: [full LaTeX derivation](../derivations/GST_native_residual_Euler_kernel_and_alteration.tex), 505 lines.
- Exact computation: [Wolfram source](../computations/GST_native_residual_Euler_kernel_2026-10-20.wl), [raw output](../computations/GST_native_residual_Euler_kernel_2026-10-20.output.txt), [manifest](../computations/GST_native_residual_Euler_kernel_2026-10-20.manifest.json).

## What was already proved, and where the actual source input occurs

The preceding finite Chern–Segre–Newton normalizer and native inverse-index reconstruction remain proved in their stated scope. Their four recorded Lean gates remain historical GREEN evidence; this note neither changes those Lean files nor claims a new kernel compilation.

Checked the actual source contracts at the base revision:

| Module | Actual geometric input still explicit |
| --- | --- |
| GSTClassicalHodgeNativeArsenalRepresentation.lean | NativeArsenalRepresentation.operator and hodge_action must realize the Hodge matrix units by actual native-compatible operators. The global theorem takes this representation. |
| GSTClassicalHodgeMinimalNativeGeometricCore.lean | FullGSTPlaneCompleteness asks for actual GradedCorrespondenceProgram witnesses reaching every requested Hodge basis vector. hodge_of_fullGSTPlane consumes it. |
| GSTClassicalHodgeCMGSTNativeBasisCompiler.lean | CMGSTNativeSheetProgram.basisPeriodExpansion specifies the target expansion in actual source-program periods; CMGSTNativeBasisProgramSupply requires these packets to exist. |
| GSTClassicalHodgeActualNoncommutativeNativeFrame.lean | The actual word-frame theorem consumes a nonzero determinant of genuinely realized source words. |
| GSTCMQuadraticNativeRankForcing.lean | Rank-two forcing requires a realized correspondence satisfying the CM polynomial, rank two, and a genuinely nonzero native seed. |
| GSTClassicalHodgePlaneCompletenessTheorem.lean | Intrinsic coordinate/causal plane completeness is unconditional; the file itself proves the separation from native geometric landing. |
| GSTUniversalCMArithmeticObstruction.lean | The final special-Weil assembly still takes Hilbert local nonemptiness, closed/spread conditions, canonical cycle-class comparisons, and the fixed secant-character comparison. It is not an arbitrary-X source constructor. |

This does not say that the laws fail. Their conclusions follow from their inputs. A compiler accepting an actual algebraic source is different from a theorem constructing that source on every X.

Prior proofs of generic source conservation, finite-degree descent, blowup defect splitting, and rank reconstruction were inspected to avoid presenting those old reductions as new theorems.

## Route A — actual native residual kernel (proved)

For dim X = 2p, let V be the rational primitive (p,p) sector, with positive form Q(x,y)=(-1)^p integral_X xy. Given any independently constructed native primitive frame v_i, lift it by the established normalizer to actual algebraic pure-middle K-classes C_i on Y=Bl_X(P^(2M)).

Let G_ij=chi(C_i,C_j), let alpha_0 be the actual Gram projection of the prescribed alpha onto this native frame, and r=alpha-alpha_0. Define genuine rational algebraic perfect-kernel classes on Y×Y:

P = sum_ij (G^-1)_ji C_i^dual external C_j,
Qker = O_diagonal - P.

The manuscript proves at the algebraic K_0-kernel level, using convolution, that P²=P and Qker²=Qker, and proves

T_Qker(A_alpha)=A_r,
-chi_(Y×Y)(A_alpha external A_(J alpha), Qker)=Q(r,r).

Here J alpha=(-1)^p alpha, and A denotes the existing normalized pure-middle topological packet. This is an actual algebraic kernel and a strictly positive index whenever the prescribed residual is nonzero. Empty frames are covered by the actual diagonal alone. No algebraic lift of alpha was assumed.

Outcome: successful universal quadratic detector in the stated primitive sector. It is a mathematical proof, with exact Wolfram consistency checks, not a new Lean theorem.

## Route B — complete alterations (proved with exact degree)

For any actual smooth proper generically finite f:X'→X of degree e>0, use the pulled-back native frame on X' and build its separately normalized blowup world Y'. The Gram is eG, the projection coefficients stay unchanged, and

-chi_(Y'×Y')(A'_(f*alpha) external A'_(f*J alpha), Qker') = e Q(r,r).

The proof explicitly does not assume that f*alpha is primitive for a polarization on X'. Positivity is restricted to the subspace f*V and follows from the degree formula. Different normal bundles are canceled by the already established GST normalization.

Outcome: complete alteration and blowup transport preserve the detector and its nonzero period; the theorem holds for every positive degree, not just the tested model.

## Route C — native partial trace as a candidate source (exact limitation proved)

T_Qker(D) is actual algebraic whenever D is actual algebraic. However, for every such D,

chi(A_r,T_Qker(D))=chi(A_r,D).

The equality also holds after middle Adams filtering. Thus this kernel cannot improve the residual period of the input catalogue. The filtered unit partial trace has zero residual period, because Pi_M(O_Y)=0 and every correction is in the known C_i span.

Actual skyscraper inputs give T_Qker(O_y)=O_y but Pi_M(O_y)=0. Therefore even a kernel that is nonzero on every actual point object need not provide a middle primitive source.

Contracting instead with the prescribed A_alpha returns A_r in topological KU; its membership in algebraic K_0 is exactly the algebraization still being sought. The nonzero doubled-world index in Route A is not a single-world native source for the linear index compiler.

Outcome: the specific attempted diagonal/residual partial-trace construction does not close universal algebraization. This is an exact type and period computation, not an obstruction to every possible GST geometric construction.

## Exact original-X return, if an independently constructed linear detector is found

For a genuine algebraic middle-filtered source E on Y', let a'(ch_M E) be the existing finite Chow Chern–Segre return followed by inverse native normalization. Set z'_E equal to its codimension-p component and Z_E=e^-1 f_* z'_E. The derivation proves

(-1)^p integral_X r cl(Z_E)
 = (-1)^(M+p+1) e^-1 chi_Y'(A'_(f*r), real E).

Thus any independently constructed actual E with nonzero right side supplies a genuine original-X cycle detecting the prescribed residual. Primitivity of that returned cycle is not asserted without an actual purification argument.

For the full rational Hodge packet in arbitrary dimension, the exact missing source statement is: every nonzero x admits an actual algebraic F on its blowup world with chi(A_x,real(Pi_M F))≠0. Perfectness of the full Hodge pairing proves that universal statement equivalent to surjectivity of the canonical cycle-class map. Allowing complete alterations preserves that equivalence by proper pushforward. This is the unresolved geometric leaf, not an extra algebraic simplification left in the normalizer.

## Reproducible exact computation

Wolfram Language 15.0.1, exact rational arithmetic only; no random sampling or floating tolerance. Positive form diag(3,5,7), frame (1,1,0),(0,1,1), target (a,b,c), and symbolic alteration degree e. Gram [[8,5],[5,12]] has determinant 71. Residual norm is exactly 105(a-b+c)^2/71.

Eight projector/Schur checks, three symbolic alteration checks, and both partial-trace checks returned True. All 18 parity instances p=1..6 and M=2p+1..2p+3 returned True. The norm-21, M=5 scalar K3 discriminator has doubled diagonal index -21. Full-frame residual is zero; the outside-frame vector (1,0,0) has residual norm 105/71.

The universal claims rely on the written proofs. These finite and symbolic checks validate the implemented signs and matrix formulas only.

## Self-review and continuation

- Self-review only; no independent agent review was requested or performed.
- Checked primitive positivity only where justified, no standard-conjecture nondegeneracy of all algebraic cycles assumed.
- Checked duality sign in each factor, convolution orientation, rational perfect classes versus integral objects, empty/full frames, and canonical original-X returns.
- No new Lean claims or compilation. Existing four green gates are not evidence that these new geometric arguments are already formalized.
- Static TeX checks passed: balanced braces and environments, paired inline math, unique display tags 1–17, and no external TeX inputs. No TeX engine/PDF compilation is claimed.
- Original all-X Hodge goal remains open in this checkpoint; no counterexample is claimed.
- Next decisive action: construct a genuinely new algebraic perfect source/actual incidence center with nonzero *linear* residual Euler period, independently of the unknown target lift. The residual diagonal kernel, its unit/point partial traces, old native matrix reconstruction, and degree transfer have now been calculated explicitly and do not supply that source.
