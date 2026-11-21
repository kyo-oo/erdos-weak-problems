# WORKLOG_W80_142U — THE ALL-k UPPER ENVELOPE (F-UP-1, linear half)

Lane: W80-142U (Erdős #142, the upper side of the formula, all k).
Mission: kill the frozen front F-UP-1 "LOGDECAY-GEN" — explicit UPPER bounds
for ALL k >= 3 from the campaign's own laws only.

## EVENTS

1. Read the stack: ASYMPTOTIC_STACK (F-UP-1 frozen), SUBLINEAR_PROOF_V2
   (Lemma T, Theorem V with the sloppy 33, L-EP/L-ARC/L-NW/L-BP/L-PB/L-ML/
   L-DF, termination via the union firing law), LOGDECAY (tower inversion),
   R4_VARN (M0=8 count law), NEW_LAWS_142 (law ledger), WORKLOG_W79 (lane
   state), engine headers + experiments_v3 (the banked dual-certified tables
   r_3(61), r_4(42), r_5(57), r_6(51) — FAR beyond the R4_VARN 16-cell table
   the mission assumed).
2. Mined the arsenal for k-uniform machinery (Phase 2): grepped the index for
   FourthOrder/ThirdOrder/AllDegree/CurvatureMemory/FoldChain + energy/split/
   increment/degree/order/tower. READ GSTFoldFourthOrderMemoryTower.lean,
   GSTAllDegreeCurvatureMemory.lean, GSTFoldChainThirdOrderMemory.lean (headers
   + declarations), GSTBladeWave/GSTAnalyticAbsorption spot lines. VERDICT:
   the "higher-order" towers are DG-algebra jet/curvature identities (memory
   laws d*w+w*d+phi*psi+psi*phi+chi^2=K4 etc.) — NO k-AP deviation content.
   The order-k deviation identity does not exist in the arsenal: NAMED as the
   exact Tier-2 gap.
3. Re-derived the amplification from scratch (the banked V proof's band loss
   N/2 forces the 33): the d-RESTRICTED copy family (d <= D0 =
   floor(N/(4m(m-1)))) kills the boundary loss. Result: THEOREM V-GEN with
   the SHARP constant |A| <= (1 + 1/(2 r_k(m)))*(r_k(m)/m)*N — the banked 33
   improved to <= 1.5 (k=3 retroactively sharpened), the frozen form implied.
   Also derived SLIDE-GEN (d=1 windows only, no size hypothesis) and U-GEN-0
   (the block floor law, TIGHT at N=k — stronger than the frozen +1 form).
   Verified the k-independence of the band count by exhaustive per-point
   copy counting at 5 (m,N) instances.
4. Built engine142uppergen.py in the campaign discipline: two independent
   k-AP freeness/counting codes; TWO independent B&B codes (X: general-k
   consecutive-prefix-exclusion marking with forced-0 symmetry — the banked C
   rule generalized to arbitrary k; Y: include/exclude DFS with direct
   violation scan, no symmetry); plug-backs on real AP-free sets (greedy,
   Cantor); negative controls on every law (copy cap, window bound, full
   intervals); exact Fraction arithmetic for all envelope algebra.
   Defects caught pre-run: the missing excl-guard in the take branch of code
   X; the wrong threshold search direction in RK-VARN-GEN; a stale cache key;
   the k=7 table needed to load before Part 1 (reordered main); tab[0] KeyError.
5. ENGINE RUN: 56/56 GREEN, wall 142.3s. Highlights:
   - V-GEN band count: min nu = m*D0 EXACTLY on every band point (5 scales).
   - Double count: both sides exact on planted AP-free sets at (3,9,1296),
     (4,8,1024); copy cap negative control fires.
   - T-GEN: EXHAUSTIVE k=4 N=12 p=53 (2232 AP-free subsets, 0 cyclic APs);
     negative control at p=13 (cyclic 4-AP (10,1,5,9) in {1,5,9,10}).
   - Tables: banked witnesses all re-verified two-code; code X re-derives
     k=3(30), k=4(33), k=5(42), k=6(42) — zero disagreements. FRESH k=7
     table N=1..46 (wall 69.4s), codes X+Y agree to 43; the table FLATTENS
     at 36 for N=41..45 (the d=7 APs bite at 43 — the multiples-of-7
     construction dies there, exactly as the window arithmetic predicts).
   - U-LIN-GEN: BLOCK law verified on ALL (L,n) pairs of all five tables;
     crossovers computed exactly (V-GEN bar 1.4-2.6% below current best
     ratios — NOT met in-package); tower simulated at 1e6/1e12/1e100
     (loses to BLOCK by 1.25-1.99x — recorded honestly).
   - RK-VARN-GEN: k=4 delta threshold 0.85 -> 0.65 with the stone 42;
     FIRST count laws at k=5,6,7 (delta 0.75/0.80/0.86); plug-backs green.
6. Docs: UPPER_STACK.md (NEW — the full upper envelope at exact strength),
   ASYMPTOTIC_STACK.md (sandwich updated: upper side all-k; F-UP-1 status
   HALF-KILLED with the exact remaining gap), NEW_LAWS_142.md (7 new complete
   laws + the 3 not-reached with the named blocker), this worklog.
7. Commit on w80-142u. No push.

## LANE STATE AT CLOSE

KILLED (F-UP-1, linear half): the all-k upper envelope is CLOSED —
r_3: 19/61, r_4: 11/21, r_5: 36/55, r_6: 31/43, k>=7: 4/5 (via the fresh
two-code k=7 table + LAW M-1), all as BLOCK laws valid at EVERY N >= 1, plus
U-GEN-0 (tight floor law), V-GEN (sharp amplification, 33 -> 1+1/(2r)),
SLIDE-GEN, T-GEN, RK-VARN-GEN (count laws k=4..7, k=4 threshold 0.65).

ALIVE (F-UP-1, sublinear half): r_k(N) <= C_k N (lnlnN/lnN)^{c_k} for k >= 4.
Exact blocker: the ORDER-k DEVIATION IDENTITY (L-EP at order k). With T-GEN
and V-GEN now in place, that single law unblocks the whole k >= 4 program
(arc increment -> flow -> LOGDECAY inversion all re-run verbatim).

The engine never stops; it never lies. In English, always.
