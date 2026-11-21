# WORKLOG W78-107K — #107 THE f(5)=9 CERTIFICATE — STAGE 2/3 (n=9)

Branch w78-107k (from campaign @ 278fab7). English only. The engine never stops; it never lies.

## Session start (W78, lane 107K)

STATE INHERITED (W77-107K bank, merged at 8a55210 / campaign 2d331c6):
- n=8 CLOSED: ot8_v2.pkl = 6405 RD types with exact realizations,
  225 self-mirror, 3315/3315 mirror-identified (anchor OK) — receipts107f5_v2.txt.
- engine107f5v3.py chunkot8 COMPLETE (242/242 parents; cells=39204,
  conc_crossed=12243, par_crossed=20209, sweep_grabs=0, walk_cfgs=674).
- 6-point lemma DEAD — never used. chunkouter + hull8 never ran.

## Round 1 — read the bank + measure
- Brief + W77 worklog + receipts + v1/v2/v3 engines read. Anchor table
  confirmed: 158,817 = the FULL n=9 mirror-identified count (OT_MIRROR_IDENTIFIED;
  NEW_CLAIMS.md: "The n=9 full certificate (158,817 anchor)"). The W78 brief's
  "hull<=4 expected count" label is the same anchor — the full enumeration is
  the certificate; hull>=5 strata trivially positive, hull<=4 strata the
  checked part.
- [hull8] n=8 hull census (RD): h=3:2296, h=4:2862, h=5:1081, h=6:156,
  h=7:9, h=8:1 — total 6405, hull<=4 = 5158 parents, chi-vs-coordinate
  cross-check GREEN (ot8_hull.json written).
- MEASURED (python, 2 cores): v2 full parent job on ONE n=8 parent = 15.3-16.8s
  (287 cells = the line-arrangement formula 1+28+8*6+210 EXACTLY;
  conc walls 2520 combos, par 840; sweep_grabs=0; walk found +133/+157 NEW
  children on the two probe parents — the walk is ESSENTIAL, the cell set is
  realization-dependent at n=8 parents exactly as the W75 law says).
  => python full n=9 (6405 parents) ≈ 27h single-core: PYTHON GRINDS.
  => the C port (brief: sweepk.c accelerator pattern) is MANDATORY.
- Toolchain: gcc 14.2 + libgmp (mpq_t exact rationals — zero overflow risk).
- PLAN: engine107f9.c = faithful C port of the v2 machinery (S1 slab cells
  with the per-parent formula check + S2 conc/par wall sweep + S3 walk +
  C canon), general-n; driver engine107f5v4.py chunks batches of parents,
  absorbs + checkpoints + commits + pushes after every chunk.
  Validation ladder: C re-enumerates n=4..8 from the banked caches —
  SET EQUALITY vs the python bank at every level (the two-code law) —
  then the full n=9 run against the anchor 158,817.
  Python certification layer: every emitted type chi-verified from coords,
  canon-verified (full python canonical_key), mirror closure, hull census,
  convex-5 two-code (chi A/B on all hull<=4; coordinate A/B on a certified
  sample + witness); python v2 full-machinery comparison on a random parent
  sample; deletion-dual sampling.
