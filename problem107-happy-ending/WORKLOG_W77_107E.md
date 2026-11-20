# WORKLOG — W77-107E (the all-n + infinite lane)

- Lane opened fresh (worktree @ 06fe8b8; the prior session left only
  empty placeholders — nothing lost).
- Engine written: engine107alln.py, stages s1-s9, exact integer/Fraction
  arithmetic, two-method law throughout, chunk-safe (no daemons — the
  watchdog order wiped all of them; in-process only).
- S1 ROTATION: 400 sets, 11,459 triple checks under 9 det=1 transforms,
  zero sign changes. bracket_transform certified on real data.
- S2: two hull codes (monotone chain vs gift-wrap) 300/300 agreement.
- S3: cup/cap DP == brute force on all n<=6; 2,734 chains convex-position
  by both codes. Composition certified.
- S4: label-pair injectivity REFUTED on our own engine (924/1200) —
  consistent with the W74 audit (263/300). 10 exemplars saved. The
  classical-memory injectivity route is dead; multiplicity is the truth.
- DERIVATION ENGINE DISCOVERY: the tight bound's true spine is the LABEL
  MULTIPLICITY LAW M(i,j) <= C(i+j-4, i-2). Verified: n=4: 69,068
  exhaustive; n=5: 5,415,016 exhaustive (81-point grid!); n=6: 14,552
  exhaustive; n=7: 624 exhaustive; 8,000 random n<=14. ZERO violations.
  (Two grid-sizing defects found and fixed on the way: 5-column grids
  cannot host 7 distinct-x points; C(81,6)=321M raw combinations blew the
  10-min ceiling — right-sized to 25/36-point and 7-column grids.)
- S4c: AVOID LAW discovered and certified: P_ij never contains an i-cup
  or j-cap (3,322 classes, zero occurrences). (i+1)/(j+1) avoidance
  PROVEN trivially (label absoluteness). L-AVOID is the single stone
  between the certified tight M-law and its proof.
- U-BIS BORN: the proven leg M(i,j) <= C(i+j-2,i-1) + label decomposition
  + hockey-stick (closed form derived and verified: G(n) = C(2n-2,n-1) -
  2n + 3) gives a SECOND complete all-n theorem: f(n) <= C(2n-2,n-1) -
  2n + 4. Independent of the banked X/Y-split instrument.
- ES-INF PROVEN: every infinite GP set has m convex for every m >= 3
  (finite-input composition of banked Theorem U). The infinite-chain
  stretch documented (needs infinite Ramsey on triple signs — the
  omega-layer is the natural arsenal home; not extracted this round).
- S6: (a,b)-forcing re-certified independently (see ALLN_PROOF.md table;
  exhaustive rows at (3,3)..(4,4), random at (4,5)..(6,6), all zero
  violations).
- S7: binomial table n=3..30 exact; banked cross-checks green;
  hockey-stick identity verified 3<=a,b<=12; U-BIS >= U at every n.
- S8: composition batteries 7->4 / 21->5 / 71->6 all green (two routes).
- S9: ES-INF certificate.
- Deliverables written: ALLN_PROOF.md (the package), NEW_LAWS_107.md,
  NEW_CLAIMS.md (5 claims), this worklog. Arsenal laws cited:
  bracket_transform, bracket_shear, bracket_skew, plucker_four,
  cubic_expansion, sum_le_sum_of_forall, two_pow_ge2, two_pow_factored,
  digitCount3_monotone, mod_mod_mul, noTernaryTwo_eq_struct (11 distinct,
  read-before-cite).
- Pushed at milestone. The engine never stops; it never lies.
