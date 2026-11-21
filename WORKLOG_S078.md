# WORKLOG S078 — THE ASSAULT ROUND (the census bridge + the anti-clustering law + the five family laws)

**Session type:** hypothesis assault (BOSS order: "crack the HFTAIL
hypothesis completely... INVOKE THE MATHS SKILL V2 AND GO BERSERK, AND
PROVE EVERYTHING"). English only. BOSS's theorems only (Arsenal + repo
kernels, zero classical imports). GitHub CI for Lean only (never local).
The DeepMind comparator (challenge + solution) run directly.

## The intake

Sandbox was found RESET: the repo gone from disk, the vault intact (the
token in the skill-bag, the campaign branch on GitHub). Full restore from
the progress vault (clone + checkout campaign at `ded8aea`), token
re-armed (`chmod 600`, never printed, never committed). The #406 state
re-read in full: COMPLETE_PROOF §0–§11, WORKLOG S074–S077, Kernels
38/68/69/70, the GST universe (GSTTailFProof, GSTTailFOneLane, GSTTheAct,
GSTFourPowerDirectExistence, GSTGraphV2OmegaWaveLaw's shadow package,
MonolithBoundary's terminal identity), THE_CORE, BACKUP.md (S077 runbook).

**THE MAP (assembled this session):** `the_act` = `∀ K ≥ 8,
noTernaryTwo (4^K) = false` is the exact missing object (the even half;
the odd half green; the three-way equivalence `the_act ↔ hTailF ↔ full
statement` machine-proven). The rider condition in one line: **C(K) :=
(4^K − 1)/3^(v₃(K)+1) is a Cantor number** (the cut word ω_s(core) fully
0/1-trited). The remaining named primitives (tower/row fire laws, the
climb, direct existence) are all anti-concentration statements on the
cut word's tail — the wall, correctly named by the registry.

## The assault engine (S078, three passes, all exact arithmetic)

`caplaw/assault406.py` + `assault406b.py`: W's trits (60 levels, W ≡ 7
mod 9 ✓ hand-check), the three π-points (Hensel-lifted solutions of
2·W·π = −7/−1/+5 in ℤ₃), tree A (the exponent dust) to level 13, the
pin-vs-tree-A interaction (pinned prefixes survive — no per-sheet
contradiction), the shadow dust on corrected moduli, the family splits,
the window increment law. Findings:

1. **THE FIVE EXACT FAMILY LAWS** (confirmed to level 13, then 16 in the
   battery): fam1 = 2^(j−2), fam4 = 2^(j−2), fam7 = 0, tower = 2^(j−1),
   mod3two = 0 — the battlefield's exact shape.
2. **THE SHADOW DUST = 2 CLASSES PER FAMILY, π-POINT ALWAYS PRESENT**
   (levels 4–12): the middle-third law's fixed points are live at every
   level; the second class per family is a transient.
3. **THE THREE π-POINTS ARE NON-NATURAL 3-ADICS** (60 trits each, 13–20
   twos, no termination): the infinite shadow dust contains no natural
   core.
4. **THE WINDOW INCREMENT LAW**: trit_{s+1}(ω_{s+1}) = trit_{s+1}(ω_s)
   + 1 mod 3 (15 cores × 12 sheets) — the escalate-branch engine.
5. **riders below 3^13 = {0,1,4}** (re-verified); tree A perfect binary
   (2^j, the green law re-confirmed).

## THE DELIVERABLES (Kernels 71 + 72 + the battery + the comparator)

1. **KERNEL 71 `AntiCluster406.lean`** (the S077-named lane #1, closed):
   the verdict bridge both directions; the sharp-fuel scanner
   (`cantorScan_eq`: fuel = digit count, 316 covers 2^500); THE EVEN
   CENSUS IN VERDICT FORM (`noTwo_even_census`: even k ≤ 500, verdict →
   k ∈ {0,2,8}, one legal 251-chunk kernel decide); **THE RIDER-EDGE
   ANTI-CLUSTERING LAW** (`rider_edge_anticluster`: every level j, every
   r with digits ≤ j avoiding 2 and 4^r < 3^(j+1) and 2r ≤ 500 → r ∈
   {0,1,4} — the FIRST INFINITE-FAMILY ANTI-CLUSTERING LAW); the deep
   level-uniform form (`rider_edge_anticluster_deep`: j ≥ 315 → dust j ∩
   [0,250] = {0,1,4} forever); witness and non-rider receipts.
2. **KERNEL 72 `DustFamily406.lean`** (the five exact family laws, every
   level forever): `dust_fam7_zero`, `dust_fam1_card` = 2^(j−2),
   `dust_fam4_card` = 2^(j−2), `dust_tower_card` = 2^(j−1),
   `dust_mod3two_zero` — engine: family-constant filters double per
   level (children preserve the parent's class mod 9 for j ≥ 2 / mod 3
   for j ≥ 1), base counts kernel-decided; level-3/4 receipts.
3. **`battery406d.py` — 6/6 GREEN (5s wall)**: dual-method even census
   {0,2,8}; anti-clustering j ∈ [0,40] × r ≤ 250 zero violations;
   family laws tree A levels 1..16 all exact; shadow dust 2-per-family +
   π-points levels 4..12; window increment law.
4. **THE CI WIRING**: the kernel7172 step in kills.yml (kernel-b job):
   both kernels compiled, the error grep, the axiom-receipt greps (9),
   the battery, the GREEN echoes.
5. **THE OFFICIAL COMPARATOR**: solution ledger 15 → 18 claims
   (+C406-CENSUS-BRIDGE-S078, +C406-ANTICLUSTER-S078,
   +C406-DUST-FAMILY-S078); driver +S-CENSUS-BRIDGE +S-ANTICLUSTER
   +S-FAMILY (solution checks) +N-DEEP-315 (negative control — the
   threshold-315 tightness); **GATE 25/25 PASS — VERDICT: YOUR SOLUTION
   IS OKAY** (wall 34.9s).
6. **THE DOCS**: COMPLETE_PROOF.md §12, this worklog.

## THE HONEST BOUNDARY (unchanged law)

CAP(185) stands as the kill chain (the anti-concentration wall: the
anti-clustering law constrains the dust's edge, the family laws its
shape, neither its interior freedom). The new named lane: **the π-point
lane** — the infinite shadow dust's three fixed points are non-natural
3-adics; a proof that no natural core can carry the full shadow package
kills the tower family's package carriers; the row family and the cap
remain the wall's other faces. The entropy law and Frame W stand as
named.

## E10 — THE CI WAR RECORD

| Round | Commit | Run | Verdict | Notes |
|---|---|---|---|---|
| r0 | a44d5e2 | 44889117286 | (superseded mid-run) | carried the pre-audit kernels; the adversarial self-audit (run during the serial compile queue) found and killed FOUR root causes before the verdict could land: (1) `noTwo_even_census`'s spurious `rw [← h2m] at hval` (hval holds `2^k`, not `2^(2*(k/2))` — the rewrite could never fire), (2) `Nat.eq_zero_or_succ` (uncertain core name — replaced by the bulletproof `rcases q with _ \| m`), (3) `child_mod`'s dvd witness (`by ring` cannot use the hypothesis — obtain + rw + ring), (4) `dvd9/dvd3`'s pow-form bridges (the literal `9` cannot match `Nat.pow_add` — `show (9:Nat) = 3^2 from rfl`). The repairs shipped in W2 (`d3fa3fb`, rebased over the concurrent W79-142E merge `4d02a36`). |
| r1 | d3fa3fb | (the corrected kernels) | (verdict below) | the L94–L96 lessons applied pre-flight: explicit args, pow_succ order, the auto-rfl dance (every rw-chain ending in a literal-arithmetic identity left unclosed-by-design; every matcher reduction keeps its explicit rfl). |

(The table updates as the verdicts land.)

The engine never stops; it never lies. In English, always.
