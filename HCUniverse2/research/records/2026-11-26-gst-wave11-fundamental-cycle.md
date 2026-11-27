# 2026-11-26 — WAVE 11: THE CENTER-RADIAL FUNDAMENTAL CYCLE — the correction BOSS ordered after the point-arithmetic audit

Written by the commander (the correction round) at HEAD `26e0c81`,
branch `research/gpt6-gst-hypothesis-part1-chow-square-20261110`.

## BOSS's order (three questions, one command)

1. **Sum it all** — the campaign state, Tasks 1-6, both fronts.
2. **Check the original GST hypothesis** — is it now proved
   unconditionally?
3. **Check the point-arithmetic weakness** — "I heard it does not give
   us topology structure; it is a weak thing?" — if yes, correct that
   task and continue the work.

## The summation verdict (questions 1 and 2)

The original GST hypothesis — the single-fold orbit law (a realized
correspondence word and a seed cycle whose orbit spans the rational
Hodge fiber at every weight) realized on a CONSTRUCTED world family at
honest Hodge data — is DISCHARGED, not assumed:

* `native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree`
  (GSTFiniteLinePointsGateDischarge.lean:206): for every M ≥ 1 and
  every family index ω, the law holds at the honest data —
  kernel-certified green (run 45780735883 at `00463dc`, all eight
  lanes green at `2152f70`).
* The consequence chain (GSTHodgeSingleHypothesisConditional.lean):
  the law implies the exact-Hodge statement and the finite rational
  combination (Clay) wording at the data — green.
* The 8-conjunct master with the exact ω-fence: green, instantiated
  at any nonzero degree-two sphere class (the exists-flip).

## The point-arithmetic verdict (question 3): CONFIRMED, and now UNDER CORRECTION

What the point arithmetic DOES give (real, certified): the point
classes are honest singular cohomology classes with the proven section
property (`inclᵢ* pᵢ(ω) = ω`); weight-one independence at a nonzero
index; the weight-zero component machine with proven spanning.

What it does NOT give (the weakness, disclosed in the corpus's own
honesty ledger, GSTFiniteLineGeneralMLaw:705):

* (i) the point classes SPAN H²(⊔M S²; ℚ) at ω ≠ 0 — true, unproven
  (the ω = 0 degeneration forbids the unconditional ∀ω form);
* (ii) H^{2p}(⊔M S²; ℚ) = 0 for p ≥ 2 — true, unproven (the stash
  assigns dead fibers without proving the ambient groups vanish).

Both reduce to the fence (Ω): H²(S²; ℚ) ≠ 0.  The wave-10 camera
route to a witness is CLOSED by the route correction
(`tetraCycle = d₃(tetraGen)` — the projected solid is an honest
singular 3-chain, so the projected boundary bounds;
`not_TetraSeparator` FALSE).

## THE CORRECTION (the command): wave 11 — GSTSphereFundamentalCycle.lean

The corrected route's first certified half — the classical H₂(S²; ℚ)
generator CONSTRUCTED in the honest singular chain complex:

* **The face data**: the four alternating-tetrahedron vertices
  (`tetraW`) have the origin as barycenter — the sphere's own center.
  Face i's vertices are `tetraW ∘ succAbove i` (the increasing
  enumeration skipping i).
* **The rank-three nonvanishing** (`face_indep`): any three of the
  four vertices are linearly independent — each face's coordinate
  matrix is a ±1 matrix with determinant ±4; four `linarith` cases
  from three coordinate readings each.
* **The center misses every face** (`tetraFaceBary_ne_zero`): the
  convex combinations on each closed face are nonzero — the origin is
  interior, exactly the structural difference that makes the camera
  cycle bound and this one not.
* **The center-radial face maps** (`faceMap`, `faceMap_continuous`):
  `sphereNormalize` of the face barycentric image — the staged
  composition pattern (the wave-10-B-REPAIR-IV named-argument
  discipline).
* **The affine coface calculus** (`faceBary_coface`): the
  pushed-forward point's coordinates are the fiber sums of the pinned
  `stdSimplex.map` (def verified at the pin, StdSimplex.lean:317 =
  `FunOnFinite.linearMap`); the collapse by `Finset.sum_eq_single`.
* **The edge pairing** (`edgeSimplex_eq`, `edgeChain_pair`): two
  face-coface composites visiting the same vertices with the same
  weights give EQUAL singular 1-simplices (the
  `toSSetObj₂_face` + proof-irrequality route).
* **THE CYCLE LAW** (`fundCycle_d`): `d₂(fundCycle) = 0` by the
  twelve-term edge cancellation — every tetrahedron edge appears in
  exactly two faces with opposite total sign AND the same
  parametrized 1-simplex (six `decide`-verified vertex pairings:
  (1,0)=(0,0), (2,0)=(0,1), (3,0)=(0,2), (2,1)=(1,1), (3,1)=(1,2),
  (3,2)=(2,2)); `abel` closes the regroup.
* **The corrected separator shape** (`FundSeparator`): the shape the
  route correction proved false at the camera cycle, restated at the
  genuinely non-bounding candidate.
* **The consistency receipt** (`no_separator_of_boundary`): if the
  fundamental cycle bounded, the shape would be false — the shape
  lives exactly as long as the cycle is non-bounding.
* **The frozen next wave** (not claimed): the realization
  `exists_nonzero_sphere_cohomology_two_of_fundseparator` — every
  separator is a cocycle whose class is nonzero (a coboundary reads
  ψ(d₂ fundCycle) = ψ 0 = 0 by the cycle law) — the NZC-2/3/4 seams
  re-pointed at the corrected cycle.

Infrastructure: `GSTSphereFundamentalCycleLib` added to the lakefile;
the fence-discharge lane's Ladder 5/5 added (FUNDAMENTAL-CYCLE
GREEN/RED + the sorryAx audit); the paths filter extended; YAML
validated; the module sweeps clean (zero sorry/admit/native_decide/
axiom, comment-stripped).

THE VERDICT (updated after the cascade): **ALL FIVE LADDERS GREEN at
`9261e74`, run 45889388303** — TETRAHEDRON GREEN, SEPARATOR GREEN,
FENCE-DISCHARGE GREEN, ROUTE-CORRECTION GREEN, FUNDAMENTAL-CYCLE
GREEN (20:15:07), zero sorryAx in the lane log, and the axiom
receipts the standard three (propext, Classical.choice, Quot.sound)
for face_indep, tetraFaceBary_ne_zero, faceMap_continuous,
faceBary_coface, edgeSimplex_eq, faceChain_d, fundCycle_d,
no_separator_of_boundary.  The cascade took nine CI-arbitrated strikes
(26e0c81 the Finset/Fin namespace + six seams; c4100e4 the
normalization table attempt; ebde97a the table + calc ascriptions;
baa7585 the literal-decision route; 7bc520b the keys+exact atom-kill;
1c1c239 the trans-chain rebuild; cdacdcd the rfl-bridge; b18151c the
definitional-distribution deletion; 9261e74 the rw-chain endgame).
The paper's §10.1 states the construction; the frozen realization
(the separator-to-class step, the NZC-2/3/4 seams) is the designated
next wave.

## The classical background (paper §10, unchanged)

H₂(S²; ℚ) ≅ ℚ by the ∂Δ³ computation (ker ∂₂ = ℚ·(1,−1,1,−1), C₃ =
0), transported along the radial homeomorphism; UCT over ℚ gives
H²(S²; ℚ) ≅ ℚ.  The wave-11 cycle is the Lean-side transcription of
exactly this generator, at the tetrahedron whose barycenter is the
sphere's center.

## Honest ledger

The wave-11 module is kernel-certified green at `9261e74` (run
45889388303, Ladder 5/5, zero sorryAx).  The frozen realization (the
separator-to-class step) is the designated next wave — NOT claimed
here.  Everything else stated is certified at the cited green runs
(45780735883 at `00463dc`; 45788422947 and the eight-lane sweep at
`2152f70`).
