# MISSION W67-61D — Erdős #61 DOUBTER/ENGINE LANE (Task ID: W67-61D)

## YOUR DISPOSITION: DOUBTER — break the family design or certify it.
Work in /home/z/waves/w67-p61d (branch w67-p61d). You do NOT author the kernel.
Artifacts land in problem61-erdos-hajnal/engine61/doubter/.

## THE FROZEN STATEMENT
"For any graph H is there some c=c(H)>0 such that every graph G on n vertices
that does not contain H as an induced subgraph contains either a complete graph
or independent set on ≥ n^c vertices?" (Erdős–Hajnal conjecture, erdosproblems.com/61)

## YOUR ATTACKS (python + z3 + gmpy2 armed; 2 cores; cap runs ≤ 15 min)

1. **THE BREAK HUNT — the sharp-form question**: enumerate ALL graphs on
   n ≤ 7 vertices (2^21 ≈ 2M at n=7 — use bitmask enumeration; if too slow,
   n ≤ 6 fully + n = 7 via structure). For each H-family class:
   - P4-free graphs: is max(ω,α) ≥ ⌊√n⌋ TRUE? (The KILLER's sharp form.)
     Find the minimal max(ω,α)/√n ratio over ALL P4-free graphs n ≤ 7 —
     if any graph has max(ω,α) < ⌊√n⌋, the sharp form is DEAD and the safe
     form ⌈√n/2⌉ must be used. BANK THE EXACT CENSUS VERDICT.
   - Same for P3-free, K3-free, K̄3-free classes.
   - THE FLOOR: for general graphs, the Ramsey floor — max(ω,α) for random
     graphs ~ 2 log n — the family classes must beat this; verify the family
     classes do (they should: ~√n).

2. **THE COGRAPH/SEINSCHE CENSUS**: verify Seinsche's lemma on ALL graphs
   n ≤ 6: every P4-free graph with ≥ 2 vertices is disconnected or has
   disconnected complement (equivalently: connected + co-connected → has a P4).
   Also verify the inductive arithmetic: √a + √b ≥ √(a+b) (exact integer
   versions: ⌈√a/2⌉ + ⌈√b/2⌉ ≥ ⌈√(a+b)/2⌉ — is this TRUE? CHECK IT — if false,
   the induction needs regrouping — this is a REAL potential break in the
   KILLER's induction design. Verify for all a,b ≤ 10^4.)

3. **THE COMPLEMENT-INVARIANCE AUDIT**: the family F's complement pairs
   (K3 ↔ K̄3, P3 ↔ P̄3 = K1∪K2, K2 ↔ K̄2, P4 ↔ P4): verify the ω/α statement
   is complement-symmetric (ω(G) = α(Ḡ)) — the kernel's complement lemmas
   must be sound. Census n ≤ 6.

4. **THE FRONTIER MAP (honest-scope intel)**: enumerate ALL unlabeled graphs
   H on 4 vertices (there are 11). For each: is H ∈ the KILLER's family F?
   (Only P4 is.) For the OTHER 10 (K4, K̄4, 2K2, C4, K1,3 claw, paw/K1∪P3,
   diamond, K3∪K̄1, K4-minus-edge...): run the adversarial census — what is
   the true best max(ω,α) bound over H-free graphs n ≤ 6? Which of them look
   poly-bounded (EH-conjecture-true) vs which have Ramsey-like floor
   (max(ω,α) ~ 2 log n — H-free does NOT help)? Bank
   doubter/frontier_map.json — this is the honest-scope table for the
   COMPLETE_PROOF.md.

5. **THE z3 CROSS-CHECK**: encode "∃ graph on n vertices, H-free, with
   ω < k and α < k" as a SAT instance (z3.Bool overflow — vertices × pairs
   booleans + no-clique-k constraints as... this is NP — for n ≤ 8 it's
   feasible via direct enumeration instead; use z3 only if it helps).
   OPTIONAL — the enumeration census is the primary weapon.

6. **THE MIRROR BATTERY on CI**: add a doubter job (kills.yml in YOUR
   worktree: paths entry problem61-erdos-hajnal/** + job running
   python3 problem61-erdos-hajnal/engine61/doubter/mirror_battery.py —
   exit nonzero on any check failure) — CI certifies your verification.

## LAWS
- Dual method on every census (two independent engines — bitmask and
  adjacency-hash — must agree exactly).
- English only. Bank all artifacts, commit, push w67-p61d (token:
  /home/z/my-project/skill-bag/extracted/erdos-zipbag/secrets/ghtoken.txt).

## REPORT BACK: the sharp-form verdict (⌊√n⌋ vs ⌈√n/2⌉ — THE critical intel),
## the Seinsche census verdict, the induction-arithmetic verdict, the
## frontier map (4-vertex H honest scope), CI verdict, any BREAK with exact
## reproduction.
