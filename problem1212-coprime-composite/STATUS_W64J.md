# STATUS — W64-J round (P1212, branch w63-d2-p1212)

## STATE RESUMED (W64-E's in-flight work, never restarted blind)
- ckpt1212_lane2310.json: next_i = 6930/6930, found = null — the round-4
  monotone M=2310 lane EXHAUSTED (all 6930 (d0, u) bases, DP depth ≤ 14):
  no monotone periodic block.
- engine1212_round5 (strip snake): no block file on disk — the box-confined
  snake design did not produce a witness in its budget.
- engine1212_round6_columnverdict: 5 dead columns at M=2310 (a ≡ 0, 105,
  525, 630, 1050 mod 1155), 15 at M=30030 — the column obstruction
  DISCOVERED; its second method originally showed 1164 "disagreements"
  (a bug: parity-violating X-even hubs were tested).
- engine1212_round6e: witness1212_extended.json — p103 extended by
  (302, 10205), (303, 10205) → the 105-vertex witness.
- engine1212_round6d (phase DFS): empty phases — the giant phase-ladder
  did not assemble at (203, 10201) in budget.

## W64-J THIS ROUND — THE COLUMN OBSTRUCTION KILL (the lane-1 result)
1. engine1212_round6_columnverdict.py FIXED (W64-J): second method now
   parity-aware (odd-odd hubs only) → 0 disagreements on BOTH moduli —
   the column verdict is honestly dual-verified.
2. engine1212_round7.py (output engine1212_round7_output.txt, ALL GREEN):
   (A) the anti-diagonal carrierless law — exhaustive 4620-residue census
       × 3 lifts, 0 violations + 20000 random large samples, 0 failures;
   (B) the crossing law (discrete IVT) — 2000 random dip-allowed walks
       (net (M, M)), all attain a hub with (X+Y) % 4620 = 0 (direct scan);
       second method: 2000 random ±1 j-walks 0→2310, 0 missing values;
   (C) the wall census — exhaustive over the class with real gcd/carriers
       (odd-odd), 0 coprime carried hubs: THE CLASS IS THE WALL;
   (D) p105 dual verification (rebuild-from-p103 match + full habitat
       recheck) GREEN.
3. Erdos1212.lean §11–§13 (Kernel 65 extension, zero sorry, CI-verdict):
   - e1212_antidiag (moduli-free): q ∣ X + Y → q ∣ X → q ∣ Y.
   - e1212_ivt (all-Nat discrete IVT): a ±2-step walk from a to b covers
     every value of the step parity between (induction on walk length).
   - e1212_periodic_kill_2310 / _210 / _30030: NO hub walk with net
     translation (M, M) has all hubs coprime AND carrier-certified (some
     q ≥ 3, q ∣ M, q ∣ X or Y) — the walk must cross (X+Y) % 2M = 0
     (IVT), where any carrier is shared by both coordinates (antidiag),
     killing coprimality. HONEST SCOPE: this closes the PERIODIC
     CARRIER-CERTIFIED design lane unconditionally (the round-3/4/5/6
     engine designs) for M = 210, 2310, 30030 — no box/band/monotonicity
     assumptions needed. The #1212 question itself remains open: a
     non-periodic path or one relying on non-carrier compositeness is
     not excluded.
   - p105_valid / p105_shape: the 105-vertex extended two-phase witness
     (203,10201) → (303,10205), both endpoint coordinates composite,
     coordinate sum grows by 104 — the campaign's longest certified
     simple G-walk.
   - e1212_column_board: the 7-conjunct master board.
4. kills.yml: kernel-65 guard extended with the new theorem-name greps.

## NEXT-ROUND PATHS
- The phase-calculus non-periodic route (round-2 DERIVATION.md): the
  rough-composite selection lemma (short intervals with all prime factors
  large) — now the ONLY constructive lane left (periodic is closed).
- The column obstruction generalization: any even M (the general-modulus
  form needs manual emod lemmas; the three campaign moduli are certified).
- p105 extension: the DFS of round-6e stalled at 105 vertices; deeper
  budgets or the phase ladder with better restore choices.

## W65-C — THE KERNEL REPAIR ROUND (branch w65-c-p1212, from cf51699)
Baseline: CI run 43612317953 FAILURE — kernel65 step red, 7 errors / 3
families, ALL in the §11 column-obstruction block (§1–§10 + §12–§13 boards
elaborated clean, zero sorryAx in the receipt for the green half). The
live log pulled, error set mapped to lines, deterministic per-family
root-kill:

1. FAMILY 1 — `Nat.dvd_sub'` unknown constant (line 546, e1212_antidiag):
   the toolchain pin does not carry it (known campaign law, WORKLOG 2179;
   the green K-family pattern from Erdos411/Erdos394). FIX: private
   `dvd_sub_local` (verbatim from the CI-green #411 kernel: rcases both
   witnesses, Nat.mul_le_mul_left case split, Dvd.intro) + the antidiag
   proof now routes through it.
2. FAMILY 2 — four omega failures in e1212_ivt's descending branch
   (585:18/585:29/586:18/586:40): the branch passes the new base point
   as `f 1` while the step hypothesis speaks of `f (0 + 1)` — omega treats
   the two as DISTINCT atoms (the CI counterexample lists both), so
   `f 1 ≤ b`, `f (0+1) = f 1`, `f 1 ≤ v`, `v % 2 = f 1 % 2` are all
   unprovable. FIX: pass `(f (0 + 1))` as the base — the goal
   `(fun k => f (k+1)) 0 = f (0+1)` beta-reduces to a syntactic
   reflexivity and every side goal connects through h1/hfa.
3. FAMILY 3 — application type mismatch at the three kill theorems
   (616/660/704): hfstep's second disjunct was stated Eq-flipped
   (`S' + 2 = S`) while e1212_ivt requires `S = S' + 2`. FIX: flip the
   disjunct to the IVT's orientation (proof unchanged, `<;> omega` closes
   either orientation). HARDENING of the never-elaborated tail (it sat
   behind the family-3 elaboration abort): the IVT target value
   `X0+Y0+(M'-(X0+Y0)%M')%M'` (nested mod — omega-hostile) → the
   division form `M' * ((X0 + Y0) / M' + 1)` (next multiple above the
   start; plain div-atom goals, the Erdos885/CardinalWorlds-certified
   omega family); `hclass`+`by omega`-on-dvd deleted — hfk IS the
   divisibility witness (`⟨(X0+Y0)/M'+1, hfk⟩`, anonymous constructor);
   `Nat.dvd_trans hqm (by decide)` → `Nat.dvd_trans hqm ⟨2, by omega⟩`
   (explicit witness, no Decidable-instance dependence);
   `(Nat.add_comm ...) ▸ hsum` → obtain/witness form (no ▸ motive risk).

Statements UNCHANGED (only proofs repaired): e1212_antidiag, e1212_ivt,
e1212_periodic_kill_210/2310/30030, e1212_column_board — the banked
mathematics stands; zero sorry/admit/sorryAx; all lemma names green-
certified in campaign kernels (Nat.dvd_trans/gcd/one via 291/677/700/961,
the dvd_sub_local body via 411, anonymous-ctor-on-dvd via 711).
CI verdict: run <TO_FILL> on branch w65-c-p1212.
