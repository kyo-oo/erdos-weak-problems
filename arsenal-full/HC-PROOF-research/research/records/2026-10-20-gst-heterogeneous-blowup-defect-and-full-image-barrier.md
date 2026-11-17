# Mathbox GST: heterogeneous blowup defect theorem and full-native-image source barrier

- Date: 2026-10-20
- Kind: corrected universal source-construction contract and exact blowup obstruction
- Branch: `research/gpt6-native-point-primitive-span-20261017`
- Base: `3550be348715bbbe1a1c7c7457ba771d8f5bd132`
- Lean construction A: `GSTActualXHodgeResidualProjection.lean` at `3796be289a8be93e2c89cb5d5d80bbab664b9d89`
- Lean construction B: `GSTGraphV2SelfExpandingCosmology.lean` at `fde0200ba3666ef7ccf4489ea60a3cbf864c2a1b`
- Verification: Graph V2 #39415938430 GREEN and pinned integration #39415938443 GREEN at `fde0200`; original-X focused #39415835958 started on earlier source commit `3796be2` (its final result requires separate checking).
- Review: Mathbox proof-audit self-review, geometric scheme-level comparison not fully formalized in Lean.

## Exact question answered

Can iterated GST blowups produce a new rational Hodge counterexample, and does their failure to do so establish rational Hodge for arbitrary X?

**Answer:** a smooth blowup with fully algebraic base and center cannot create a new rational Hodge counterexample. But blowing up a Hodge-counterexample center (if one exists) preserves that missing class; therefore no unconditional no-counterexample theorem for all arbitrary smooth centers can be proved from the blowup formula without already resolving the rational Hodge conjecture. This is a mathematically sharp distinction, not a question of number of blowup iterations.

## 1. Geometric full-grade defect decomposition

Let B and Z be smooth projective complex varieties, Z ⊂ B a smooth center of complex codimension c ≥ 2, π: Y=Bl_Z(B)→B the smooth blowup, E=P(N_{Z/B}) its exceptional divisor j:E→Y, q:E→Z, and ξ=c1(O_E(1)).

For every p, the Chow and rational Hodge decompositions (conventions: the i-th exceptional channel is j_*(ξ^{i-1} q^*(-)) and carries the shift (-i)) give

$$
CH^p(Y)_{\mathbf Q}\cong CH^p(B)_{\mathbf Q}\oplus\bigoplus_{i=1}^{c-1} CH^{p-i}(Z)_{\mathbf Q},
$$

$$
\mathrm{Hdg}^p(Y)_{\mathbf Q}\cong\mathrm{Hdg}^p(B)_{\mathbf Q}\oplus\bigoplus_{i=1}^{c-1}\mathrm{Hdg}^{p-i}(Z)_{\mathbf Q}.
$$

Under the **genuine canonical Betti cycle class map** and its Gysin/pullback comparison, the map is block diagonal: cl_Y^p ≅ cl_B^p ⊕ ⊕_{i=1}^{c-1}cl_Z^{p-i}. Thus

$$
\boxed{\mathrm{coker}(cl_Y^p)\cong\mathrm{coker}(cl_B^p)\oplus\bigoplus_{i=1}^{c-1}\mathrm{coker}(cl_Z^{p-i}).}
$$

These are isomorphisms of rational vector spaces; their use in Lean requires the actual scheme/Hodge comparison, which is not obtained by passing arbitrary linear maps as parameters. If c=1 the blowup of a Cartier divisor is isomorphic to B and the exceptional direct sum is empty. If p-i<0 the corresponding graded Hodge and Chow terms vanish.

Therefore a missing rational Hodge class on Y exists if and only if a relevant missing class existed on B or in one shifted Hodge group of Z. The converse maps a missing center class to its canonical exceptional channel. Induction applies to any finite tower of smooth blowups using the actual graded center data. It follows that any tower whose initial varieties and ALL newly introduced smooth centers satisfy rational Hodge remains Hodge-complete. Arbitrary centers are not automatically Hodge-complete.

Important application: any smooth projective X can be embedded into P^N with codimension c≥2. The ambient blowup Bl_X(P^N) is smooth projective rational. Hence a genuine nonalgebraic rational Hodge class on X, if one exists, would yield a nonalgebraic exceptional class on a smooth projective rational variety. Contrapositively, if ALL smooth projective rational varieties satisfy rational Hodge then ALL smooth projective varieties do. This is an equivalence reduction, not a proof of either property.

## 2. GST heterogeneous two-center formal upgrade

The existing finite-r blowup block theorem only addressed repeated identical center module types. We now construct a two-step birth with *different* independent Chow and Hodge types: maps b:NB→HB, c1:NC1→HC1, c2:NC2→HC2, nested block map (b⊕c1)⊕c2. Its exact rational surjectivity law is

$$
\mathrm{Surj}((b\oplus c_1)\oplus c_2)\iff\mathrm{Surj}(b)\land\mathrm{Surj}(c_1)\land\mathrm{Surj}(c_2).
$$

The existential missing-class theorem is the corresponding disjunction of failures in b,c1,c2. A separate theorem constructs witnesses for every Hodge class of the born block when all three native maps are onto. Source is the *existing* `GSTGraphV2SelfExpandingCosmology.lean`, definitions `blowupTwoDistinctCentersCanonicalCycleBlock`, `blowupTwoDistinctCenters_surjective_iff`, `blowupTwoDistinctCenters_missing_iff_old_missing`, `blowupTwoDistinctCenters_no_counterexample_of_complete_inputs`. Geometric instantiation remains explicitly required; these are not clandestine assertions of universal Hodge.

## 3. The adversarial check on the proposed universal exceptional source

Let H_X^p be the rational Hodge space on the ORIGINAL X and A_X^p=im(cl_X:CH^p(X)_Q→H_X^p) the **entire** original-X algebraic image, not an incompletely enumerated finite GST frame A_old. The new GST original-X return sends every algebraic perfect complex F on Y to an actual rational Chow class S_p(F)∈CH^p(X)_Q. Consequently

$$
\boxed{\mathrm{im}(cl_X\circ S_p)\subseteq A_X^p.}
$$

For ANY rational linear functional ell that annihilates A_X^p,

$$
\boxed{\ell(cl_X(S_p(F)))=0\quad\text{for every genuinely algebraic }F\in K_0(Y)_{\mathbf Q}.}
$$

This is UNCONDITIONAL as a typed statement once S_p is an actual algebraic Chow-valued map. It does not require an intersection pairing, positivity or a Gram determinant. The same applies to every finite GST target-selected GRR packet. Thus the earlier proposed test 'find independently algebraic F whose return pairs nontrivially with r, while r annihilates the FULL algebraic image' is **logically impossible**: such F is already in the algebraic image by construction.

This does NOT negate prior verified GST source-rank births, because the residual in those theorems is taken relative to an **incomplete finite old-native frame**, not the full Chow image. Those theorems can and do find independent genuinely algebraic directions beyond the chosen finite frame; they do not establish that no unrepresented Hodge direction survives in the full cokernel.

Lean added to existing `GSTActualXHodgeResidualProjection.lean`:

- `exceptionalReturnGRR_range_le_full_native_image`: submodule containment for all-X, all-p actual native Chow cycles.
- `full_native_annihilator_kills_exceptionalGRR`: annihilator kills every born perfect-complex return.
- `exceptional_coupling_refutes_full_annihilation`: a nonzero pairing disproves full-image annihilation, not the existence of a Hodge counterexample.
- `full_native_annihilator_kills_exceptional_packet`: every target-selected finite packet shares the same barrier.

These results make a formerly tacit gap mathematically explicit and protect the genuine GST theorems from an invalid universal interpretation.

## 4. Point-by-point remaining work, by the repository's OWN proof contract

1. Gate 1: instantiate genuine analytification/fundamental class, Hodge decomposition and canonical Betti cycle-class comparison (the repo's supplied `H.cycleClass` is not a proof of canonicality by itself).
2. Gate 3 priority: construct an independently justified family of algebraic geometric sources for prescribed primitive targets ON THE ORIGINAL X, beyond an incomplete finite frame; and prove the family exhausts the entire genuine Hodge target, not merely the characteristic subring or a selected K3/CM/Fermat family. An existence assumption that already forces a nonzero period against every full-image annihilator is equivalent in finite-dimensional nondegenerate settings to the wanted algebraicity and cannot be treated as an independently proved GST law.
3. Gate 2: instantiate rational Hard Lefschetz and geometric hyperplane cup/products to lift actual primitive Chow representatives to arbitrary rational Hodge classes.
4. Gate 4: assemble and audit the exact quantified Clay-style theorem without assuming surrogate cycle maps, preimage selectors, hidden Hodge-complete source worlds or unrelated formal axioms.

Existing GST arsenal retained: arbitrary-arity world birth (`GSTGraphV2SelfExpandingCosmology`), actual X residual duality (`GSTActualXHodgeResidualProjection`), rational Gram descent (`GSTPolarizedHodgeResidualEnergy`), pure K0/GRR and single smooth-center conversion (`GSTUniversalResolvedSupportHodge`), mixed blowup and Clifford/Fermat geometric sources (`GSTMaximalLinearHypersurfacePrimitive`), CM/Weil & deformation attempts (`GSTUniversalCMArithmeticObstruction`), exceptional Chow/Gysin returns and Chern-Segre inverses, and exact full target (`GSTClassicalHodgeExactClayStatement`). The existing 701-module overview maps the full repository; this note is not a renewed audit of every proof body.

## 5. Status and decision

The no-new-counterexample theorem is proved for ordinary genuine blowups *under Hodge-complete base and centers*, and the full algebraic-image return barrier is proved structurally for arbitrary original X. These do not settle universal rational Hodge. More connected blowup iterations alone do not improve the universal source-existence obligation. The correct next genuinely mathematical breakthrough requires proving a non-circular geometric operation that yields native algebraic representatives for the residual Hodge quotient, not merely returning cycles that already lie in the native algebraic image.

**Mathbox verdict:** blowup stability proved in the specified scope; universal conjecture remains incomplete, with the independent actual-X primitive source construction and canonical scheme-to-Betti realization as exact unproved implications.
