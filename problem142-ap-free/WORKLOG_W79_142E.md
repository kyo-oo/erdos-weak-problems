# WORKLOG_W79_142E — THE ALL-k LOWER LAW (BEHREND-GEN)

Lane: W79-142E (Erdős #142, the general-k lower side of the formula).
Mode: COMMANDER-ABSORBED (dispatch channel dead 5th time — all five W79
sub-agent dispatches reported context-deadline; one landed a bank-read
commit on 107e, one left an uncommitted draft here, the rest empty).

## EVENTS

1. Recon: W78-142E/W78-142K lanes NEVER EXECUTED (branches still at the
   arm commit 278fab7) — the all-k lower law was the purest execution
   debt of the campaign. W79 dispatch attempted (5 lanes); dead.
2. Found the dead agent's uncommitted draft problem142-ap-free/BEHREND_GEN.md
   (401 lines): Theorem BG statement, the general-k no-carry lemma
   (interior second differences digitize in base 2m for every k at once),
   the digit-power identity, the two-parity kill, the census, the explicit
   optimization (C_k = 2√((k+1)ln2)+1, k=3 reproducing the banked 2.8853),
   the §8 sum-classifier ceiling with the Rankin front named.
3. COMMANDER AUDIT of the draft (before trusting a dead agent's math):
   - no-carry chaining: verified independently (consecutive triples ⟹
     A_i = A_0 + iE; no division by k-1 — correct for all k);
   - the kill, h odd: reconstructed and closed independently (A_0 vanishes
     on supp E via the second coefficient; E >= 0 since A_1 = E is in the
     box; ΣE_j^h = 0 with E >= 0 forces E = 0) — the draft's Case 2 matches;
   - the optimization algebra: F(d) = d ln2 + kL/d + 2 ln d + O(1),
     d* = √(kL/ln2), F* = (2√(k ln2) + o(1))√L — verified;
   - NO overclaims found: the draft does NOT claim the Rankin shape; it
     names it as the front with the ceiling analysis. Clean.
4. Built engine142behrendgen.py per the §7 spec: three independent
   k-AP-freedom codes (A endpoints+divisibility, B first-two-pair walk,
   C bit-parallel shift-AND), general-k identity checks, the plug-back
   grid, the banked k=3 byte-equality reproduction, negative controls,
   the banked 18-law battery re-run. Three defects caught and fixed
   pre-run: (i) the raw-integer rejection-sampling in NOCARRY would starve
   (probability (m/B)^{dk} ~ 0) — rebuilt digitwise with independent
   digits_of recomputation; (ii) PLUGBACK-REAL window logic (box cap 2^14,
   code guards for the 3432-element binary cell); (iii) bit-parallel
   witness branch simplified.
5. ENGINE RUN: 9/9 GREEN, wall 67.6s (receipts142behrendgen.txt,
   BEHREND_GEN_ENGINE_GREEN=1). Highlights: 80 instances k=3..10 three-code
   verified; 0/1321 kill-contrapositive violations; plug-back 45,847
   points/k, min margins 7.56-9.45; real sets k=3..8 (k=9,10
   arithmetic-only — no enumerable recipe window, NAMED); k=3 byte-equal
   to the banked engine; 18/18 laws.
6. Docs: BEHREND_GEN.md corrected to the engine's actuals (45,847 grid
   points; the real-window table; the 9/9 header). LOWER_STACK.md written
   (the complete lower envelope + comparison laws + F-LOW-1).
   ASYMPTOTIC_STACK.md written (the two-sided sandwich at exact strength:
   lower all-k NEW + upper k=3 banked + the ladder + fronts F-UP-1
   LOGDECAY-GEN all-k upper, F-LOW-1 Rankin shape, F-UP-2 constants).
   NEW_LAWS_142.md + NEW_CLAIMS.md appended (C142-BEHREND-GEN,
   C142-LADDER).
7. Commit + push branch w79-142e; commander merges to campaign.

## LANE STATE AT CLOSE

KILLED: THEOREM BG (the all-k lower law) — complete, certified, universal
in k. The exponent-1 law r_k(N) >= N·exp(-C_k√(ln N)) now holds at EVERY
rung of the ladder, in-package, explicit constants.

NEXT FRONTS (named): F-UP-1 LOGDECAY-GEN (the all-k upper — the W78-142K
unexecuted lane; target statement frozen in ASYMPTOTIC_STACK.md);
F-LOW-1 Rankin shape (k >= 4, non-sum-type classifier; §8 dead-end ledger).

The engine never stops; it never lies. In English, always.
