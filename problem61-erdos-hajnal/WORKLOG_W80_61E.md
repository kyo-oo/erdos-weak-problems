# WORKLOG_W80_61E.md — THE FINISHER WAVE (W80-61E-F)

## The salvage story (this lane)
- Dispatch W80-61E built engine61c5.py (the C5 endgame engine: two-code
  classifiers, exhaustive n<=7, the W8 rung, substitution package, the
  hom-3 frontier hunt n=8..12), ran it, EDITED the engine (removing the
  expectation-carrying ok() conjuncts of the first harness), launched a
  verification re-run, committed the checkpoint 73f782a at 11:45:13 — and
  DIED. The committed receipts (41 PASS / 6 FAIL, wall 238.8s) were the
  output of the EARLIER harness version; the engine's re-run (launched
  ~11:42:57, right after the last engine edit at 11:42:54) finished at
  11:46:17, landing its 47/0 receipts in the working tree AFTER the commit.

## What the finisher did (in order)
1. READ the salvage: receipts61c5.txt, engine61c5.py, CLOSURE_MAP.md,
   NEW_LAWS_61.md, FIVEVERTEX_PROOF.md §2 (C5-DICH + the named core
   frontier), W78-61K worklog (the 32/34 world map), arsenal laws
   (pow_mul_rule / pow_pow_rule / pow_mono / pow_le at
   erdosternary2/ErdosTernary2.lean:2075-2087 — read before cite).
2. RERAN the committed engine (foreground, wall 190.3s): SUMMARY
   PASS=47 FAIL=0 — NOT the checkpoint's 41/6. Discovered the working
   tree already held a THIRD completed run (the dispatcher's posthumous
   re-run, 47/0, wall 199.2s, mtime 11:46:17): preserved as
   receipts61c5_postrun.txt; my rerun as receipts61c5_rerun.txt.
   The 6 checkpoint FAILs are stale-harness expected-value mismatches
   (S1 core-count definitional mismatch 60/12840-vs-420/18840; S3 battery
   count threshold while all 206 substitutions were clean; S4 hom/ladder
   expectations) — every one explained in the receipts appendix; the
   committed engine passes all 47.
3. WROTE verify61c5_witness.py — independent from-scratch verification,
   two assumption-free induced-C5 detectors (subset scan: all induced
   degrees == 2; canonical walk chase with chord masks), brute alpha/omega,
   branch&bound MIS with clique-cover bound, own substitution + formulas,
   own battery. RESULT (receipts61c5_verify.txt, 64/3):
   * THE MATERIAL FINDING — WITNESS CORRUPTION: the checkpoint's S4
     witnesses at n=10/11/12 are NOT C5-free (2/10/9 induced C5s counted,
     both codes agree with the engine's own code on re-run); their
     alpha/omega/core values match — an old-harness witness-NOTING bug
     (a post-mutation adjacency was noted instead of the verified best).
     n=8/9 checkpoint witnesses genuine; ALL rerun + postrun witnesses
     (n=8..12, hom 3,3,3,4,4) GENUINE.
   * h_C5(10) = 3 EXACT: verified rerun witness (C5-free core,
     alpha=omega=3) + R(3,3)=6 floor certified exhaustively (all 32,768
     six-vertex graphs; C5 the tightness witness). THE LADDER BREAKS.
   * h(11)<=3 RETRACTED: corrupt witness; both fresh hunts top out at
     hom 4; exhaustive 2x1024 one-vertex extension probe of BOTH verified
     n=10 hom-3 witnesses finds no n=11 hom-3 graph. h_C5(11) in [3,4].
   * X_2 = W8[W8×8]: FULL exhaustive 7,624,512-subset scan clean (both
     codes), alpha=omega=9 by B&B = substitution formula, constructive
     9-set exhibits; X_3 (512 vertices) sampled clean, formula 27=3^3;
     150-instance fresh substitution battery clean, formulas exact.
   * CAP arithmetic: c <= log3/log8 = 0.528321, tower tight, t=1..8.
4. WROTE THE FOUR LAWS into NEW_LAWS_61.md (complete proofs): C61-C5-SUBST
   (substitution closure; the projection proof), C61-C5-CAP (c <= 0.52832,
   with the alpha/omega substitution formulas), C61-C5-HTABLE (exact
   n<=10; [3,4] at 11/12), C61-C5-LADDER-BREAK (h^2>=n false at n=10, in
   the core stratum; C5-DICH restated honestly).
5. UPDATED CLOSURE_MAP.md: the C5 section enriched (measured frontier,
   capped exponent, broken ladder) — status line kept at 32/34 closed
   in-frame; EH(C5) NOT claimed.

## Commits
- 8fd8e6e — verification + audit appendix + the four laws.
- (this commit) — CLOSURE_MAP update + this worklog.

## Honest state of the lane
EH(C5) OPEN. Banked: closure/reduction/dich + SUBST + CAP + HTABLE +
LADDER-BREAK. The kill needs a core-stratum exponent in (0, 0.52832] (or a
refutation); next named probes: the h(11)/h(12) hom-3 cells, the
core-stratum floor. The engine never stops; it never lies.
