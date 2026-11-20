# WORKLOG S076 — THE RIDER-CONSTRAINT-LAW ROUND (the five new laws + the census extension + the protection system)

**Session type:** hypothesis assault continuation (BOSS order: "TARGET #406
ONLY... crack the HFTAIL hypothesis completely... read the commit history...
build a system that protects the sandbox even if we completely reset it").
English only. BOSS's theorems only. GitHub CI for Lean only (never local).
The DeepMind comparator (challenge + solution) run directly.

## The intake

The Drive bag recovered (token restored, campaign re-synced from `9aadfb0`
to the live HEAD `ee2b2c5` — the W76 correction-wave commit, six lane briefs,
none touching #406). The #406 history re-read in full: COMPLETE_PROOF.md
§1–§10, WORKLOG_S074/S075, Kernel 38/68, DustLaw406, the DeepMind
Challenge/Solution pair, the Arsenal readers (`noTernaryTwo`, `v2r`,
`ternaryLog3`, `mul_add_div_lemma`).

## The war council (MATHS §6, Mode B run internally — the sub-agent dispatch
channel was down this session, probed twice; all three dispositions argued in
structured succession with forced contradiction)

- **DOUBTER**: no counterexample construction exists (the MITM blocks
  saturate at M+4; no infinite ascent); CAP(C) survives attack — TRUE but
  hard. The 63% fractional cut is real (verified: 63.09% of [200001, 10^6]).
- **ATTACKER**: every proof route dies at the same wall — the MIDDLE DIGITS
  of `4^K` (positions `[log₃K, 1.26K]`), where neither magnitude (the
  fixpoint obstruction), nor 3-adic structure (the dust tree's fresh zone),
  nor 2-adic structure (the moment ladder) reaches.
- **STRATEGIST**: the bank-able content is the NEW necessary-condition laws —
  each sharpens every future census and constrains every hypothetical rider.

**BREAKTHROUGH (the actual truth of this round): every named surface of the
hypothesis — `hTailF`, `the_act`, CAP(185), the dust anti-clustering — is
ONE object: the middle-digit wall. The five new laws extracted below attack
it from five previously-unbanked sides.**

## THE FIVE NEW UNCONDITIONAL LAWS (Kernel 69, ExtraLaws406.lean)

1. **L1 THE HALF-LINE LAW** (`cantor_half_line`, `rider_half_line`,
   `erdos406_half_line_kill`): every positive 0/1-ternary `n` satisfies
   `2·n < 3^(ternaryLog3 n + 1)` — the Cantor number sits strictly in the
   lower half of its leading range. Rider form: `{K·log₃4} < 1 − log₃2 ≈
   0.36907`. **The kill form eliminates every exponent `K` with
   `3^(ternaryLog3(4^K)+1) ≤ 2·4^K` — an infinite family, battery-certified
   63.09% density on [200001, 10^6].** Proof: strong induction of the digit
   recursion against the repunit bound.
2. **L2 THE TAIL LAW** (`noTernaryTwo_div_pow3`, `rider_tail_law`):
   `⌊4^K/3^(K+1)⌋ = ⌊(4/3)^K/3⌋` is itself 0/1-ternary for every rider —
   the new necessary condition on the carry-only top 0.26K digits.
3. **L3 THE ADJACENT-ONES KILL LAW** (`adjacent_ones_kill`): if `u`'s
   ternary digits at positions `j−1, j` are both 1, then `4u+1` owns the
   digit 2 at position j — DEAD. The digit-exact form of the repunit
   no-carry law: for 0/1-ternary `u`, the ternary digits of `4u+1` are
   `e_0 = d_0+1`, `e_i = d_i + d_{i−1}` with NO carries (every `e_i ≤ 2 <
   3`), so every adjacent 1-pair produces the dead digit. (Discovered this
   session: the no-carry addition `4u+1 = 3u + (u+1)` has no carries
   position-wise.)
4. **L4/L5 THE MOD-9 CYCLE + CONSECUTIVE-RIDER LAWS** (`pow4_mod9`,
   `rider_mod3_ne_two`, `no_three_consecutive_riders`,
   `consecutive_riders_mod3_gap`): `4^r mod 9` is 1, 4, 7 as `r ≡ 0, 1, 2
   (mod 3)`; every rider has `r ≢ 2 (mod 3)`; no three consecutive riders;
   consecutive riders force `r ≡ 0 (mod 3)`.
5. **THE CANTOR T²-LAW** (`cantor_T2_mod3`): for every 0/1-ternary `u`, not
   both `4u+1` and `16u+5` are 0/1-ternary — pure mod-3 arithmetic
   (`4u+1 ≡ u+1`, `16u+5 ≡ u+2 (mod 3)`).

Plus the **LX CONJECTURE recorded** (unproven, evidenced): `v₂(cantor n) ≤
2·popcount₃(n)` — holds with zero excess through 3^12 (exhaustive), TIGHT at
both known extremals (256: |S|=4, v₂=8; the M=14 extremal: |S|=8, v₂=16).
The next session's target: a Lean proof would be the first popcount-side cap
law — a new route class for CAP.

## THE CENSUS EXTENSION (battery406b.py, ALL GREEN)

The certified no-rider range extended from **200,000 to 1,000,000** (the
n-range [20002, 2·10^6]): stage 1 the L1 pre-filter (float theta with a
1e-8 exact-integer boundary zone; 63.09% killed by magnitude arithmetic
alone), stage 2 the 61-digit modular deep check on every survivor (one
modular pow `4^K mod 3^61` + digit extraction with early exit — **every
survivor died within 61 digits; zero survivors of stage 2**). Dual-method
throughout.

## THE OFFICIAL COMPARATOR (BOSS's order: challenge + solution, directly)

`official_gate.py 406`: **16/16 PASS — VERDICT: YOUR SOLUTION IS OKAY**
(wall 28.7s). New checks: O-CHAL-1M (the census extension re-derived live),
S-EXTRALAWS (battery406b.py subprocess), S-HALFLINE (the receipts +
ExtraLaws406.lean symbol table), N-HALFLINE (the kill-boundary control: the
law kills K=6, spares K=5 — necessary, not sufficient). The solution ledger:
8 → 11 claims (+C406-EXTRALAWS-S076, +C406-CENSUS-1M-S076,
+C406-HALFLINE-RECEIPTS-S076).

## THE SANDBOX PROTECTION SYSTEM (BOSS's order, rebuilt on the fresh machine)

- `/home/z/my-project/BACKUP.md` — the master restore runbook (anchored at
  my-project root + download/ + the repo + the sandbox-vault branch).
- `/home/z/my-project/backup/backup.sh` — the engine: seals ALL uncommitted
  work, pushes campaign, force-refreshes the `sandbox-vault` branch.
- Cron guardian **539956** (fixed_rate 8h) — automated backup turns even
  if a session forgets.
- Token: `.secrets/ghtoken.txt` (chmod 600, NEVER in git — the repo is
  PUBLIC); the Drive bag preserved at `upload/erdos-zipbag.zip` (the token
  vault).
- The drive link (recovered from the shared chat by the batch-messages API
  after the page render):
  `https://drive.google.com/file/d/1ZCY5hbZyId7AWeBD-o0yOiRFlxGmKnW-/view`

## The honest boundary (unchanged law)

CAP(C) is NOT proven for any C at unbounded range — the middle-digit wall
stands (every route this session confirmed the S074/S075 verdict
independently). What IS delivered: the five new machine-checked
necessary-condition laws, the 50x census extension, the comparator gate
extension, and the constraint-set sharpening for every future assault. The
named remaining fronts: (a) CAP(C) at any explicit constant; (b) the LX
popcount-cap conjecture (the new route class discovered this round); (c)
the middle-digit equidistribution-free structure.

The engine never stops; it never lies. In English, always.

---

## E10 — THE CI WAR RECORD (the full honesty ledger)

The Kernel 69 compile war (the campaign's standard 4-round pattern, executed over
7 CI rounds):

| Round | Run | State | Root-causes killed |
|---|---|---|---|
| r1 | 44773862691 | 15 errors | the strongRecOn motive structure (hypotheses into goals), the div_pow3 generalizing-n induction, the by_contra Bool conversions, the WF-dec-block (struct-eval receipts), the Mathlib drift in CapLaw406's pow_lt_mono_base |
| r2 | 44780760384 | 4 errors | the ih argument order, the zero-case idioms (if_pos rfl from the campaign's own CardinalWorlds:191), the linear_combination sign (the residual 8u-72W-32 was exactly twice the mis-signed combination) |
| r3 | 44788154275 | 2 errors | Nat has no Neg: -4 * hq restated as 4 * hq.symm; the free-variable decide -> omega |
| r4 | 44794078616 | 1 error | **KERNEL 69 CI-GREEN** (ERDOS406_EXTRALAWS_KERNEL_GREEN=1, zero sorryAx across all 13 theorems); CapLaw's a=0 case split needed (a < b admits a = 0) |
| r5-r7 | 44800094096-44812340800 | CapLaw healing | Nat.zero_pow_succ does not exist (pow_succ + mul_zero decomposition); Nat.mul_le_mul_right drift (e289-style self-contained); THE STRUCTURAL ROOT-KILL: the by_cases neg-branch never closed its goal (h2+calc stranded at the outer level) |
| r8 | 44816882584 | CapLaw GREEN | DustLaw406 exposed (never CI-verified in S075) — 14 sites |

**THE DEEP LEARNINGS (L-fresh, for the adaptive ledger):**
- L-DUST1: omega CANNOT abstract through `digit3`'s internal division by
  `3^(j+1)` (a VARIABLE divisor breaks its model — every counterexample
  report shows consistent atoms). Never omega near a digit3-term; use
  absurd/explicit-congruence/dvd forms.
- L-DUST2: `rw [Nat.add_zero]` rewrites only the FIRST instantiated
  pattern — the t=0 branch's RHS `(A+0)%3` survived the r-side
  normalization; a second rw needed.
- L-DUST3: the new Mathlib's `simp only [List.mem_cons, List.mem_singleton]`
  normalizes self-eq disjuncts to True — `Or.inl rfl` sites become
  `simp` sites.
- L-DUST4: the anonymous-constructor defeq unification fails on the
  `1*3^j` vs `3^j` factor — omega bridges (`by omega` for the witness).
- L-DUST5: the match TACTIC needs dot-patterns (`.zero`/`.succ q`), and
  rcases never accepts tactic-blocks in its `with` clause.
- L-DUST6: `Nat.mod_eq_zero_of_dvd ⟨witness, by ring⟩` — the omega-free
  zero-mod route for 3-multiples.

**The remaining DustLaw406 map (the next session's entry point — 8 sites,
all in the dustStep_spec/dust_spec region): 180 (h0's omega — the digit3
abstraction), 266/268 (the t=0 d=2 branch's omega + the absurd type), 286/303
(the t=1/t=2 hdig branches), 385/393/414 (the dust_spec succ-case's witness
unifications). The pattern: every failing omega sits near a digit3-term —
L-DUST1 applies.**

The engine never stops; it never lies. In English, always.
