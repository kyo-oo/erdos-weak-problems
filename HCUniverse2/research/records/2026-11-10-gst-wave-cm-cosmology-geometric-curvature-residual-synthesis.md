# GST integrated wave/CM/cosmology/curvature → primitive-Hodge residual elimination

Date: 2026-11-10 (IST). Repo `kyo-oo/HC-PROOF`, branch `research/gpt6-native-point-primitive-span-20261017`. Original task: **connect**, do not rebuild, the original dimensionless seven-axis graph, all-N waves/cohomology, self-expanding cosmology, imaginary-CM and true Chow correspondences, and the infinite fold-curvature memory to attack the single-birth Hodge hypothesis. Starting HEAD verified as `fdf3ce47f7a52efbd23432d98dbe8fac3bdb6554`; the branch already contained 779 Lean files when starting.

## A. One source→target dictionary, with the exact mathematical types

1. **Dimensionless GST information:** `GSTCanonicalSevenAxisBridge` is the actual x4/base3 arithmetic graph; `GSTGraphV2InformationRecovery.shuffleEquiv` is the invertible local `Fin 4 × Fin 3` permutation, `F^5=id`, extended pointwise to `Nat→Cell`. This is not a five-dimensional manifold or an algebraic morphism.
2. **Actual GST wave current:** `GST2DMixedEmergence`, `waves/GSTWaveCohomology` / `V2`, `GSTGraphV2OmegaWaveLaw` and `GSTGraphV2CanonicalNWave` expose signed information coboundaries plus the actual BIG2/SURVIVE source. The source is genuinely nonzero in the original finite arithmetic model.
3. **Wave-II n-cohomology:** `waves/GSTNCohomologyV3` replaces the earlier constant-index pseudo-basis with actual independent N-hole coordinates, arbitrary products, and a basis-wise curvature detection map. The rank of these coordinates is an information-channel count, not by definition an Hodge number of a complex variety.
4. **CM source parity on waves:** `GSTGraphV2CMWaveFusion` defines the 12-state U,J,M, proves U^5=I, J²=-I, UJ=JU and a genuine nonzero `[J,M]`. `GSTGraphV2WaveNShapeCompiler` and `GSTHodgeWaveAllNHoleReadout` give indexed finite-N signal folds, geometrically independent hole readouts and Vandermonde-type wave coefficients; `GSTGraphV2CMInfiniteCurvatureBridge` gives full noncommutative CM odd/even parity and exact curvature identities at all finite word orders.
5. **Unlimited cosmology:** `GSTGraphV2OmniversalCore`, `GSTGraphV2SelfExpandingCosmology`, `GSTGraphV2CausalComponents`, `GSTGraphV2CMNMCoupledUniverse` and `GSTGraphV2UnboundedHigherCausality` supply arbitrary event paths/world births and causality. A certified geometric realization must satisfy the real native-cycle and Hodge assembly laws; a Cartesian-product arithmetic event leaves the geometry unchanged.
6. **All-order fold memory:** `GSTFoldFourthOrderMemoryTower`, `GSTFoldTowerSquare.JetTowerInf`, and `GSTInfiniteTowerCurvatureCascade` prove the formal all-index square/convolution curvature tower. Each coefficient is an exact finite expression; no analytic convergence requirement was silently added.
7. **Canonical geometric landing:** `GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair` and `GSTGraphV2NativeCurvatureBirth.nativeCurvatureCycle` define actual rational algebraic original-X cycle operators and the exact commuting square `cl_X([N_A,N_B]Z)=[T_A,T_B]cl_X(Z)`. `GSTHodgeWaveAllNGeometricLanding.GeometricWaveFrame` defines actual independently algebraic frame cycles and geometric intersection readouts; `GSTHodgeGSTWaveGeometricCompiler` constructs a primitive wave seed and primitive curvature cycle under true primitive-preserving operations.
8. **Low-dimensional Hodge bridge:** `GSTUniversalCodimensionTwoPrimitiveExtraction` already implements the correct Lefschetz divisor correction for p=2 and isolates the primitive remainder; `GSTHodgeGSTUnifiedPrimitiveWaveRank` gives the original-X wave-born algebraic part plus the primitive residual. The classical d=3 case is discharged by the divisor theorem and actual hard Lefschetz, not by artificially choosing N wave holes.
9. **New composite residual-elimination mathematics:** `GSTHodgeWaveCurvatureResidualStep.lean` derives an explicit second native correction and proves the residual is annihilated both by all old wave coordinates and by the genuinely geometric curvature detector. `GSTHodgePrimitiveWaveCurvatureLanding.lean` instantiates this to native primitive codimension-two Chow cycles on the original X and the existing wave+CM+primitive curvature constructor. The abstract module is Lean-green at [42679545127](https://github.com/kyo-oo/HC-PROOF/actions/runs/42679545127). The primitive original-X landing passed the pinned Lean kernel at GitHub Actions [42680885128](https://github.com/kyo-oo/HC-PROOF/actions/runs/42680885128), after resolving missing namespace imports, with no sorryAx.

## B. Exact NEW transformed proof equation, beyond the previous wave-only residual

Fix the actual rational (p,p) Hodge fiber `B`, native Chow group `A` and canonical cycle class `cl:A→B`. An actual `GeometricWaveFrame` has algebraic cycles `Z_i` and genuine geometric duals `D_i:B→Q`. Define the source map and readout map:

\[
C(v)=\sum_{i=1}^{n}v_i\operatorname{cl}(Z_i),
\qquad D(x)=(D_i(x))_i,\qquad DC=I_n.
\]

The existing wave-only residual is `r_0(x)=(I-CD)x`, with `D(r_0)=0`. Now take a **genuine original-X commutator cycle**

\[
z=[N_A,N_B]z_0= N_A N_B z_0-N_B N_A z_0\in CH^p(X)_{\mathbb Q}
\]

with geometric class `g=cl(z)`, and a **fixed geometrically realized** rational readout `ell:B→Q` obeying

\[
\ell(Cv)=0\ (\forall v),\qquad \ell(g)\ne0.
\]

The corrected curvature-born cycle removes overlap with the old frame:

\[
z_\perp=z-\sum_i D_i(g) Z_i,\quad
\operatorname{cl}(z_\perp)=(I-CD)g,\quad
D(\operatorname{cl}(z_\perp))=0,\quad
\ell(\operatorname{cl}(z_\perp))=\ell(g).
\]

**The NEW explicit transformed native source:**

\[
\boxed{
Z_{\mathrm{wave+curv}}(\alpha)=
\sum_i D_i(\alpha) Z_i+
\frac{\ell((I-CD)\alpha)}{\ell(g)}\,z_\perp.
}
\]

Thus, for **every** `alpha∈B`, with `r_1=alpha-cl(Z_wave+curv(alpha))`,

\[
\boxed{\alpha=\operatorname{cl}(Z_{\mathrm{wave+curv}}(\alpha))+r_1,\quad
D(r_1)=0,\quad\ell(r_1)=0.}
\]

No Chow preimage of `alpha` was assumed; the formula uses existing actual original-X native sources `Z_i,z` and geometric detectors, and makes the residual strictly smaller whenever `ell(g)≠0`. If the combined detector `(D,ell)` separates every vector in `B`, then `r_1=0`; this is a precise verifiable geometric rank criterion, **not** a conclusion obtained from the abstract graph alone.

### Primitive codimension-two on arbitrary original X

Apply the existing real geometric Hard Lefschetz/divisor construction to an arbitrary rational Hodge (2,2) class alpha:

\[
\alpha=\operatorname{cl}(Z_{L}(\alpha))+\beta_\alpha,\qquad
\beta_\alpha\in\ker L^{d-3}
\]

for d≥4. Treat the restricted canonical cycle class on genuine primitive source cycles. The new `primitiveWaveCurvatureCycle` is

\[
z= [N_A,N_B](Z_{\mathrm{primitive\ wave}})\in
\ker(L^{d-3}\circ cl_X)
\]

provided both real native operator pairs preserve the primitive kernel, with the primitive property proved by `GSTHodgeGSTWaveGeometricCompiler.primitiveBornCurvature_test`.

The resulting integrated cycle is

\[
\boxed{Z_\alpha=Z_L(\alpha)+Z_{\mathrm{wave+curv}}(\beta_\alpha)}
\]

and the remaining **primitive** residual has zero readouts for all old N-wave coordinates and the additional curvature probe. This makes the d=2,3 classical case a source of the actual lower-degree geometry in the same construction, not a metaphoric dimensional analogy.

## C. EXACT geometric computation on a 6-dimensional projective complex variety

`X=(P^1_C)^6`; let `d_i` be hyperplane divisor classes, `D_I=∏_{i∈I}d_i`, and `h=∑d_i`. In codimension 2, the 15 divisor-product cycles form an actual full rational Hodge basis. The map `L^3:H^4(X,Q)→H^{10}(X,Q)` has its 6×15 integer incidence matrix with entry 6 if `I⊂J`. Exact nullspace has rank **9**, the actual primitive `(2,2)` dimension. Its basis `K_1,..,K_9` consists of genuine rational combinations of algebraic cycles, and all dual readouts `D_i` are rational combinations of complementary-class actual intersection numbers.

Take old wave frame `K_1,K_2`, actual rank-one Chow projectors `A=K_1⊗D_1`, `B_3=K_3⊗D_1`, each realized by `CH^6(X×X)_Q` matrix units. Then

\[
\boxed{[A,B_3]K_1=-K_3,\qquad
D_1(-K_3)=D_2(-K_3)=0,\quad D_3(-K_3)=-1.}
\]

The exact wave+curvature representative removes a third genuinely algebraic primitive direction. The original first-three detectors all vanish on the residual. **Rational rank grows 2→3**. This is reproducible in `research/computations/gst_wave_curvature_primitive_sixfold_residual_20261110.wl` and checked by executing the exact committed file in Wolfram.

**Stronger full sixfold construction:** take `B_j=K_j⊗D_1` for every `j=3,..,9` and the same `A=K_1⊗D_1`. Each native commutator `[A,B_j]K_1=-K_j` and each fixed geometric detector `D_j` removes exactly its independent primitive residual. The computed independent-source ranks are

\[
\boxed{2\to3\to4\to5\to6\to7\to8\to9,}
\]

with **zero final primitive residual for any alpha in the explicitly known sixfold primitive sector** because the exact rational dual matrix obeys `D K = I_9`. The executed full-rank reproducible script is `research/computations/gst_wave_curvature_full_primitive_sixfold_ladder_20261110.wl`. The tested specific coefficients produce a zero final residual, and the exact matrix identity establishes the universal assertion **within that nine-dimensional sector**.

Unlike an abstract rank-9 companion matrix this is a geometric Chow-representable construction on a true projective sixfold; unlike a new solution of a general primitive Hodge problem, all its primitive cycles were already explicitly algebraic divisor-product classes. The original GST axis information dimensions have not been reinterpreted as manifold dimensions.

## D. Comparison with authenticated external geometric sources (alphaXiv)

- Floccari–Fu, [arXiv:2504.13607v2](https://arxiv.org/abs/2504.13607), pages 1–3: for Weil fourfolds of discriminant 1 and powers, Hodge–Weil middle classes are algebraic even when generic ones cannot be linear combinations of intersections of divisors. Their actual geometric birth uses singular OG6 moduli varieties, K3 surfaces, a fixed-locus cycle and algebraic Kuga–Satake correspondences. **This is a demanding realistic target for GST curvature birth beyond the already divisor-algebraic sixfold.**
- Amini–Huh–Larson, [arXiv:2511.02026v2](https://arxiv.org/abs/2511.02026), pages 1–2,7,13: Lefschetz modules satisfy formal PD/HL/HR, but Example 2.5 gives an abstract module impossible as Kähler/projective geometry. Therefore `GSTNCohomology` N-hole rank and `GSTUniversalLefschetzCosmology` world operators require a **genuine geometric realization preserving the entire cohomology package**, not merely shared numeric dimensions.
- Miranda–Movasati–Rufino–Villaflor, [arXiv:2609.27301v2](https://arxiv.org/abs/2609.27301), pages 1–3: Fermat Hodge classes for all degrees <65 except 44,51,52 reduce using explicit **geometry-preserving** join, deletion, permutation, and lift operations. Their exceptional character quotient is a useful analogue of the GST residual: the proof succeeds by checking actual source operations and a finite residual rank, not by declaring every abstract character an algebraic class.

## E. Rigorous status of the universal GST birth hypothesis after fusion

The *actual proof obligation* remains geometric, not arithmetic. The new theorem reduces the primitive residual by one whenever the GST wave/CM/native-correspondence program supplies a **new actual** algebraic curvature cycle detected outside the old wave frame. The original fold hypothesis will follow once a finite sequence of such genuinely produced original-X primitive sources (plus the Lefschetz descendants) spans all primitive Hodge directions, and the resulting finite geometric frame is compiled into one native cyclic fold using the already verified `GSTHodgeWaveFiniteCyclicCompletion` construction.

This is a typed and now tested **iterative constructive attack**, rather than an ungrounded `Hodge→Chow` selector. The prior `GSTGraphV2IntegratedWaveCMGate.word_in_cycleClass_range` simultaneously proves that replaying only old Chow correspondences cannot escape the *entire* algebraic-cycle image; the birth process must really supply fresh geometrically constructed source cycles in previously uncovered Hodge directions. No mathematical law says the source program cannot exist; proving independent geometric nonvanishing/coverage for arbitrary X is the exact next task.

**Route cards and discrimination:**
- R1 wave/CM representation and N-holes: exact finite source cyclicity and all-N quotient proved in existing branch; preserves information but no universal geometric lift.
- R2 native curvature+Lefschetz: succeeds in the new generic one-step theorem and explicit sixfold source; extends old frame under an independently nonzero geometric detector.
- R3 recursive world-birth: `GSTGraphV2SelfExpandingCosmology.NativeGeometryBirth` already gives conditional native assembly; needs actual `allHodgeFromSources` on a concrete original-X birational/moduli source and an algebraic correspondence return.
- R4 falsification: nongeometric (Q^{n+1}) with source image (Q^n) admits all internal wave operators on the first n directions but leaves an extra residual untouched. The original-X wave algebra is not enough alone to imply coverage; this is a countermodel to *that inference*, not a counterexample to the Hodge conjecture.

**Next discriminating geometric experiment:** a Weil CM abelian fourfold with a known Hodge–Weil class **not in the divisor-generated algebra**. Try deriving a GST wave/CM-curvature native cycle and its canonical period pairing **without inputting a known exceptional cycle**; compare against the independent OG6/Kuga–Satake source. If a genuine nonzero exceptional pairing is constructed, it supplies the first new primitive-birth test beyond known divisor-product sectors and can enter the exact residual theorem above.

## F. Reproducibility/verification

- Lean kernel **green**: `GSTHodgeWaveCurvatureResidualStep.lean` checked [CI 42679545127](https://github.com/kyo-oo/HC-PROOF/actions/runs/42679545127). The code explicitly constructs the native wave+curvature cycle and proves both residual detectors vanish for any rational linear geometry.
- Primitive specialization: `GSTHodgePrimitiveWaveCurvatureLanding.lean` maps the generic theorem to actual `codimensionCycles`, primitive corrected native wave seeds and `primitiveBornCurvature`. Verify its **latest** GitHub Actions run: do not rely on the filename or a submitted workflow alone.
- Wolfram exact scripts: `research/computations/gst_wave_curvature_primitive_sixfold_residual_20261110.wl` and `research/computations/gst_wave_curvature_full_primitive_sixfold_ladder_20261110.wl`. Both were fetched back after commit and executed unchanged in Wolfram; all exact booleans true, no floating arithmetic.
- Source audit: exact authenticated primary PDF pages from alphaXiv for the three arXiv preprints named above. Application to arbitrary projective original X remains the specified correspondence-realization question.

## G. Rank-plus-one source completeness and true single-fold connection (subsequent burst)

The enhanced `GSTHodgeWaveCurvatureResidualStep.lean` now proves that the augmented detector

\[
R:B\longrightarrow\mathbb Q^n\oplus\mathbb Q,\qquad
R(\alpha)=(D(\alpha),\ell(\alpha))
\]

is **surjective** from an independently generated actual native curvature class with \(\ell(g)\ne0\) and the existing genuine wave frame. If \(\dim_{\mathbb Q}B=n+1\), rank-nullity forces \(R\) injective, so the exact residual vanishes for **every** target. The Lean theorem is `waveCurvature_exact_of_rank_succ`, verified in [Actions 42682777206](https://github.com/kyo-oo/HC-PROOF/actions/runs/42682777206). This replaces the earlier abstract residual separation field by a checkable actual Betti rank equality.

The strengthened `GSTHodgePrimitiveWaveCurvatureLanding.lean` then specializes this rank equality to the **actual primitive original-X codimension-two Hodge fiber**, without requiring `hSeparate`; it uses the native Hard Lefschetz divisor correction. The stronger original-X codimension-two rank-based theorem `originalX_primitive_wave_curvature_complete_of_rank_succ` passed pinned Lean kernel checking at [42683458742](https://github.com/kyo-oo/HC-PROOF/actions/runs/42683458742).

A new **one-fold construction** `GSTHodgeWaveCurvatureCyclicAugmentation.lean` uses Mathlib `Fin.snoc` to extend the *true original geometric dual frame* by the corrected curvature cycle, adds a normalized geometric dual readout, proves all old-new and new-old cross pairings zero, then applies the PRE-EXISTING `GSTHodgeWaveFiniteCyclicCompletion.GeometricCyclicFrame` to get **one cyclic native operator** and a Betti-compatible action. This supplies the proper structural arrow

\[
\boxed{\text{n actual wave atoms + one detected native curvature atom}
\longrightarrow \text{n+1 dual Chow frame}
\longrightarrow \text{one genuine cyclic source fold}.}
\]

The required element is a geometrically realized new source, not the mere cardinality of an N-hole wave channel.

### Exact closed-loop single-fold test on a projective sixfold

On \(X=(\mathbb P^1)^6\), construct 9 actual primitive cycles K₁,...,K₉ as in Section C: K₁,K₂ are the old wave frame; K₃,...,K₉ are seven genuine original-X geometric commutator products. The actual rational complementary-intersection dual matrix D obeys DK=I₉. Define the cyclic shift S on \(\mathbb Q^9\), and the *single original-X Chow-representable* cohomological/native operator

\[
\boxed{T=KSD\quad\text{on the primitive middle-degree sector}.}
\]

The full 15×15 matrix T is not invertible on all H⁴, but its restricted 9×9 action is cyclic and preserves the primitive kernel. Take seed K₁, then

\[
\boxed{\operatorname{span}_{\mathbb Q}\{K_1,TK_1,\dots,T^8K_1\}
=\ker(L^3),}
\quad
\det\bigl(D[K_1,TK_1,\dots,T^8K_1]\bigr)=1.
\]

The actual last-coordinate intersection detector has a 9×9 Hankel moment determinant **1**. All identities, including `T K = K S`, were checked by exact rational Wolfram arithmetic and saved as `research/computations/gst_sixfold_curvature_born_nine_cycle_single_fold_20261110.wl`, fetched from GitHub and re-executed verbatim.

This is a **full nine-direction original-X primitive geometric instance of the one-fold route** for that projective sixfold, not just a numerical abstract cyclic model. It is not a novel exceptional Hodge class: toric projective products have an independently known algebraic basis, and the K_i were constructed using it.

### Remaining original-X source gate

For genuinely exceptional rational primitive Hodge directions (e.g. Hodge–Weil classes on generic Weil fourfolds) `GSTGraphV2CMWaveFusion` supplies rational wave information and the above curvature mechanism supplies **correct algebraic push-pull conditional on actual geometric input**. The current construction does not produce the needed exceptional primitive Chow cycle or fixed geometric detector independently of one already-known via OG6/Kuga–Satake geometry. This is the live, sharply localized geometric birth test for the universal GST hypothesis, not a reason to repeat generic graph laws.

### Verified one-fold geometric augmentation (final CI)

The new `GSTHodgeWaveCurvatureCyclicAugmentation.lean` was compiled and verified by the pinned Lean kernel in [GitHub Actions run 42683986245](https://github.com/kyo-oo/HC-PROOF/actions/runs/42683986245), after correcting a finite-index disjointness proof. The module's actual theorems construct the old native wave duals plus a new independently detected curvature atom as a `GeometricCyclicFrame` and prove `nativeSingleFold_cycleClass`, `nativeSingleFold_cycles_orbit`, and `augmented_cyclic_fold_constructs_all_classes_of_rank`. The latter combines one native cyclic fold, true Betti compatibility, finite-dimensional rank equality, and an explicit Chow-group representative for every target in the **supplied geometric fiber**.

**Geometric semantics note:** an `A→ₗ[ℚ]A` operator on native Chow cycles is a mathematically legitimate native fold but not automatically exhibited by an actual Chow correspondence `Γ∈CH^d(X×X)_ℚ`. This stronger assertion is demonstrated in the explicit projective sixfold computation through algebraic matrix-unit cycles, and must be instantiated independently for arbitrary original X. Likewise `HodgeBigradedBettiData` carries supplied structures; canonical whole-Betti realization must be checked for that X.

**Reproducibility:** `research/computations/gst_sixfold_curvature_born_nine_cycle_single_fold_20261110.wl` was committed to GitHub and fetched back and run unchanged in the Wolfram evaluator. It checked a genuine original-X rational Chow matrix-unit correspondence with primitive orbit rank **9**, dual orbit determinant **1**, Hankel moment determinant **1**, full primitive preservation and exact cyclic operator; all booleans were True. The script uses `Nest` instead of `MatrixPower[T,0]` because the full 15-dimensional ambient operator is singular outside the 9-dimensional primitive sector; the latter is invertible/cyclic.

New actual original-X rank-certified primitive Hodge reconstruction [42683458742](https://github.com/kyo-oo/HC-PROOF/actions/runs/42683458742) and original-X one-curvature residual [42680885128](https://github.com/kyo-oo/HC-PROOF/actions/runs/42680885128) are independently green in their targeted Lean workflows. The single universal birth mechanism still calls for an independent geometric source outside previously known divisor/Tate sectors on an arbitrarily prescribed X; the Weil-fourfold example is the exact next discriminating experiment rather than an automatic consequence of abstract cosmology.
