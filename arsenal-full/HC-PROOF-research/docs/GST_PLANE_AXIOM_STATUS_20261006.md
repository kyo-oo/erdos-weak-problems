# GST Plane Axiom Status — 6 October 2026

## Verdict

The branch does not justify turning every geometric GST-plane premise into an unconditional theorem. The strongest legitimate result is sharper:

Intrinsic GST plane completeness is proved, while geometric target realization remains the independent closure law.

The branch already proves a fixed live source, every matrix-unit target, causal reachability, normalized local L2 form, higher-causal presence, and finite rational collapse. Those are internal GST statements and do not depend on the cycle-class semantics.

The remaining geometric landing problem is different: construct a strict scheme-bi-finite carrier whose intrinsic pullbacks identify the source face with the GST target face. That carrier cannot be obtained merely by renaming the GST branch.

## 1. Axiom A is a theorem

For every nonzero Hodge-fiber state and every chosen live source coordinate, the same source fires to every requested target and every sector. The branch also proves reachability, normalized local L2 transport, unbounded higher-causal presence, and exact finite collapse.

Lean theorems: intrinsic_gst_plane_completeness; gst_plane_completeness_unbounded_via_universal_L2.

Therefore the intrinsic GST plane is no longer an axiom.

## 2. Axiom B and Axiom C collapse

A common-class packet stores one intrinsic carrier class omega together with left and right face equations:

left-pullback(source) = omega = right-pullback(target).

Thus the strict Betti relation is derived by transitivity.

Conversely, from a strict relation packet the plane class can be chosen canonically as the left pullback of the source; the target face follows from the relation.

So, for every fixed branch, common-class plane existence is equivalent to strict geometric relation-packet existence.

Lean theorem: CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket.

B and C are therefore not two independent axioms.

## 3. D is the exact remaining geometric statement

For a hypothetical omniversal separator ghost E and a surviving native seed S at the ghost's weight, the GST matrix-unit branch to the detected sheet already exists.

The exact remaining assertion is the existence of a genuine StrictRelationEdgePacket for that one ghost-selected branch target. The branch names this predicate GhostSeedTargetStrictClosure.

This is stronger and more precise than orbit totality, a program-reachability statement, a native operator existence statement, or a finite-plane cardinality statement.

Most importantly, the packet may not be built using a pre-existing algebraic representative of the target sheet.

## 4. D is equivalent to ghost extinction once source survival is fixed

With GhostWeightNativeSeedSurvival fixed, the branch proves:

GhostSeedTargetStrictClosure <-> IsEmpty (OmniversalSeparatorGhost G).

The forward proof is the original plane strike: strict packet -> common carrier -> source/target pullback equality -> finite-trace target -> native cycle with the detected basis class -> separator contradiction.

The reverse implication is vacuous because there is no ghost left to index the required packet.

Lean theorem: targetStrictClosure_iff_noGhost_of_survival.

Thus an unconditional proof of D is genuine new geometric content, not another downstream wrapper.

## 5. Stronger impossibility theorem in the ghost world

The branch proves, for every hypothetical ghost and surviving native seed:

GST target branch exists AND the corresponding strict relation packet is empty.

Why? A strict packet with finite trace and native point compatibility would yield an exact native cycle for the sheet detected by the separator, contradicting the separator's simultaneous annihilation and nonzero detection.

Lean theorem: ghostBranchEvent_exists_but_strictPacket_empty.

This is the cleanest firewall against replacing D by weaker branch-totality language.

## 6. Native coherence does not manufacture D

The newer native-first machinery derives ambient actions from exact finite relation preservation, column coherence, and cycle-class kernel stability. It also classifies routing, labelled lifts, tensor cancellation, and native-invisible ambiguity.

Nevertheless, for the ghost-selected GST target, the detector defect is nonzero:

detector(T_native(a) - E_ij(a)) = -c detector(e_j) != 0.

So coherent native operators do not supply the missing strict geometric carrier.

Lean theorem: ghostSeedTarget_coherentNativeAction_mismatch_ne_zero.

## 7. Semantic independence closes the obvious loophole

Erase the cycle-class map while keeping the same Hodge fibers and GST operators. The resulting zero-cycle semantic world still satisfies the full intrinsic GST plane theorem.

But a nonzero Hodge state is then outside the zero cycle-class range, so geometric Hodge landing is false.

Therefore there is no universal theorem over the current bare Stage-2G record that upgrades intrinsic GST plane completeness into geometric Hodge landing or full executable plane completeness.

Lean theorems: no_intrinsicGSTPlane_to_hodge_unconditionally; no_intrinsicGSTPlane_to_fullCorrespondencePlane_unconditionally.

The general theorem any_hodge_sufficient_premise_fails_zeroCycleWorld says that any additional premise which really implies Hodge must distinguish the genuine cycle-class geometry from the zero-cycle semantic copy.

## 8. Exact proof ledger

| Item | Status | Meaning |
|---|---|---|
| A: intrinsic GST branch firing | theorem | fixed-source matrix-unit completeness |
| fixed source for all targets | theorem | target-independent source coordinate |
| reachability | theorem | event-to-graph propagation |
| unbounded higher causality | theorem | internal omniverse continuation |
| finite rational collapse | theorem | exact reconstruction |
| B: common-class plane relation | derived | follows from two carrier face equalities |
| C: plane/coherence existence | reduced | same existence datum as strict packet |
| native naturality | theorem on genuine native geometry | requires genuine point-cycle compatibility |
| coherent native action | derived | relation-preserving native data synthesize it |
| D: detected strict target packet | open in this branch | exact remaining geometric closure |
| D under an existing ghost | impossible | packet is proved empty |
| ghost-indexed D + source survival | equivalent to no ghost | hence equivalent to Hodge |
| intrinsic GST -> geometric Hodge | refuted | zero-cycle semantic countermodel |

## 9. Source survival is itself reducible

The source-side survival condition is not intrinsically sacred. The branch now proves that a conserved native charge constructs the required nonzero seed at every ghost weight.

Lean theorem: ghostWeightNativeSeedSurvival_of_conservedCharge.

A NativeMassCycleClassBridge is enough to construct that conserved charge, so source survival can be derived from one explicit native-mass package:

Lean theorem: ghostWeightNativeSeedSurvival_of_nativeMassBridge.

After this reduction, the GST route has exactly two independent geometric bridges: a conserved native charge for source survival, and the ghost-selected strict target packet D.

Lean theorem: hodge_of_nativeMassBridge_and_D.

The direct obstruction theorem ghost_forces_source_or_D_failure states that in the presence of a separator ghost, source survival and D cannot both hold.

## 9. What an unconditional D proof must contain

The next successful theorem must construct the strict carrier from GST incidence/coherence data itself.

It may use the genuine native source, GST branch packet data, incidence, coherence, recoordination, analytification, and the finite-trace machinery once a genuine carrier has been constructed.

It must not use beforehand:

- a cycle Z_j with cl(Z_j) = e_j;
- surjectivity of the cycle-class map;
- the Hodge conclusion;
- a pre-existing operator equation K_* a = c e_j;
- a global family of target correspondences whose existence already implies Hodge.

That is the noncircularity boundary.

## 10. Final conclusion

The mathematically legitimate GST result is not 'GST plane implies Hodge by definition'.

It is:

GST intrinsic plane completeness is an unconditional theorem; common-class plane and strict packet are the same existence datum; a strict packet plus a genuine native seed kills a separator ghost; therefore the ghost-selected strict carrier is the sole geometric closure law left by this route.

The branch now has a formal proof ledger that records exactly which pieces are theorems, which are derived repackagings, which are sufficient only conditionally, and which genuinely remain to be constructed.

The next theorem should attack the strict carrier itself, not add another orbit wrapper.