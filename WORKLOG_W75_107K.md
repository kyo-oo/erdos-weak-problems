# WORKLOG — W75-107K (lane 107K, THEOREM F5: f(5) = 9)

Worktree /home/z/waves/w75-107k, branch w75-107k, base da24660.
Mission: /home/z/erdos-weak-problems/W75_BRIEFS/107K.md — prove f(5)=9 in-package:
THEOREM F5 (every 9 GP points contain 5 in convex position) + banked 8-point
witness (lower side). Hull-case decomposition, exhaustive machine certification,
arsenal citations (>= 6 laws, plucker_four at orientation steps).

## Events

- E00 [session start] Brief read. Banked package read (ES_PACKAGE_PROOF.md:
  MS/CC/U/L + GP-ELIM + H107; witness w5 = 8 exact-integer points, machine-verified
  no convex 5 => f(5) >= 9). Arsenal laws located: plucker_four
  [HC-PROOF-research/GSTCausalPairingGraphs.lean:37], bracket/bracket_skew/
  bracket_self/bracket_transform/bracket_shear/graph_transform
  [GSTCausalPairingGraphs.lean:15,19,23,27,33,50], two_pow_pos [CardinalWorlds.lean:419],
  two_pow_ge2 [CardinalWorlds.lean:431], three_pow_odd [CardinalWorlds.lean:438],
  mod_mod_mul [CardinalWorlds.lean:143], mul_add_div_lemma [CardinalWorlds.lean:146],
  cubic_expansion [ErdosTernary2.lean:293], two_pow_factored [ErdosTernary2.lean:885],
  sq_sub_one [ErdosTernary2.lean:908], digitCount3_monotone [ErdosTernary2.lean:2097].
- E01 [audit of the brief's own lemma] The brief's "6-point lemma" (triangle
  hull + 3 interior points => convex 5) checked BY HAND with exact fractions
  (concentric triangles A(0,10) B(-9,-8) C(9,-8), u(0,10/3) v(-3,-8/3) w(3,-8/3)):
  all 6 five-subsets have hull of size 3 or 4 — NO convex 5. The lemma is FALSE.
  Consequence: the brief's hull=4 / hull=3 case trees (as sketched) do not close;
  the true case tree must use the additional points (D, the second cell, the
  outer vertices). Engine will confirm and rebuild. This is exactly the
  "CAREFUL" the brief flagged; the derivation must be done here.
- E02 [engine build] engine107f5.py started: exact Fraction/int core (orient,
  GP check, convex-position by TWO independent methods: (a) hull-peeling
  monotone chain, (b) Caratheodory subset-scan C(n,5) x triangle-membership),
  order-type machinery (84-sign chirotope, canonical form under relabeling,
  line-arrangement cells by exact slab sampling, insertion enumeration).
  Master plan: COMPLETE ORDER-TYPE ENUMERATION of 9-point GP sets
  (hull-vertex-deletion recursion; expected counts 2,3,16,135,3315,158817 at
  n=4..9 — count match = completeness certificate), then: every 9-point order
  type contains convex 5 = machine proof of THEOREM F5 upper side. Plus
  structured lanes (2-2-1, quad-split), random doubter battery, witness recheck.
