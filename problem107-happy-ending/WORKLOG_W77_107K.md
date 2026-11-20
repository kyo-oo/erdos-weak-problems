# WORKLOG W77-107K — #107 f(5) = 9 COMPLETION LANE

Branch w77-107k. ENGINE_CHARTER.md binding. English only. The engine never stops; it never lies.

## Session start (W77, lane 107K)

STATE INHERITED (W76-107K bank, merged at 916c963):
- engine107f5.py (v1) + engine107f5v2.py (S1 cells + S2 wall sweep + S3 walk),
  caches ot3-ot7_v2 certified (1, 2, 3, 16, 135 mirror-identified — anchors OK).
- n=8: the W75 baseline (cells + perturbation diversity) = 3313/3315 with
  1 mirror orphan (receipts_ot8fix.txt: 6402 reflection-distinguished, 225
  self-mirror, exactly ONE closure failure). Gap arithmetic: the full set is
  6405 reflection-distinguished = 3315 identified; missing from baseline =
  exactly 3 types (the orphan's mirror + the members of 2 absent classes,
  with m + m_selfmirror = 2).
- The v2 run (S1+S2+S3) was grinding when the machine died; ot8_v2.pkl never
  existed. receipts107f5_v2.txt holds only the certified prelude.
- 6-point lemma DEAD (concentric-triangle counterexample) — never used.

ARSENAL READ-BEFORE-CITE (verified this session at arsenal-full/):
bracket_skew [HC-PROOF-research/GSTCausalPairingGraphs.lean:19],
bracket_transform [:27], bracket_shear [:33], plucker_four [:38],
worldMap_monotone [HC-PROOF-research/GSTGraphV2CausalComponents.lean:127],
digit3_mod_pow [HC-PROOF-research/GSTBladeWave.lean:56],
digit3_congr [GSTBladeWave.lean:72],
cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283],
two_pow_factored [:425], two_pow_ge2 [:431],
sum_le_sum_of_forall [erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean:117],
sq_sub_one [CardinalWorlds.lean:448] (spare). 12 laws located and read.

PLAN:
- STAGE 1: engine107f5v3.py `chunkot8` — the v2 machinery, chunked +
  checkpointed (progress JSON + partial pickle), push every chunk. Anchor 3315.
- STAGE 1b: `chunkouter` (outer-insertion independent cross-check) + witness.
- STAGE 2: hull8 classification; n=9 hull<=4 strata by TWO methods
  (M1: interior insertion from hull<=4 8-parents — the interior-deletion
  lemma; M2: full n=9 generation filtered) — C accelerator (engine107f9.c)
  for the 6432-parent scale.
- STAGE 3: F5 certificate — every hull<=4 9-type convex-5-positive by TWO
  codes; hull>=5 trivial; witness re-verified; 10^5 random battery.
- Deliverables: F5_PROOF.md, NEW_LAWS_107.md, NEW_CLAIMS.md, receipts.

## Round 1
- Read brief + charter; inventoried the bank; read receipts + caches.
- Benchmark: v2 parent job ~3.0-3.9 s/parent on n=7 parents (162 cells,
  conc walls 30-55/630 crossed, par walls 39-85/420, walk 1-3 configs).
  Full 242-parent pass ≈ 400-500 s on 2 cores — chunked in v3.
- engine107f5v3.py written (chunkot8 / chunkouter / hull8 / status).
