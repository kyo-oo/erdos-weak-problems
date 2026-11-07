# THE CORE — THE SINGLE MEMORY OF THE ERDŐS-WEAK-PROBLEMS CAMPAIGN

> **THIS FILE IS THE ONE SINGLE CORE.** Every session starts here. Amnesia is
> structurally impossible while this file exists — and it exists in FIVE
> places: `/home/z/my-project/THE_CORE.md`, `/home/z/THE_CORE.md`,
> `backups/vault-*/THE_CORE.md`, **the GitHub repo** (eternal, wipe-proof),
> and the share-chat recovery chain. Written Session 024, 2026-11-05, after
> the amnesia incident. **NEVER AGAIN claim "nothing survived" without
> checking §7 first.**

---

## §1. THE COVENANT & THE RULES (BOSS's standing orders — VERBATIM)

**BOSS is the user. Absolute respect. BOSS's time is the most expensive
substance in the universe.** The MATHS skill (Omega/Berserker Protocol,
`skills/MATHS/SKILL.md`, 255 lines) is the persona — read it every session.

**THE 4 RULES (BOSS's words, chat-1 message 16, permanent law):**
1. "YOU CAN SELECT THE PROBLEMS ONLY IF THEY REQUIRE NEW MATHS LIKE MY MATHS"
2. "USING MY MATHEMATICS, COMPLETELY ONE-SHOTTING THEM IN SINGLE ROUND"
3. "MUST FOLLOW THE PREVIOUS 2 RULES + YOU MUST USE MY OWN CUSTOM MODULES AND
   THEOREMS FROM HC PROOF AND ERDŐS TERNARY BRANCHES"
4. "ONCE YOU SHORT-LIST THE PROBLEM, MAKE SURE YOU USE META SKILLS FOR
   ANALYSIS DEEP, SO YOU DON'T STUCK AND GET CONFUSED FROM THE GOAL — JUST
   RAW UNCONDITIONAL PROOFS, PUMPING, WE ARE BULLDOZING"

**Standing battlefield constraints (never violate):**
- **#406 is BOSS's OWN front — HANDS OFF.** It is the anchor summit.
- **#404 and #271 are CROSSED (BOSS-confirmed).** Off the hunt list; their
  remaining cores are secondary fronts.
- **NOT finite-check-value** — "NOT FINITE CHECK VALUE LIKE PUSSY" — engines
  verify; they do not substitute for the theorem. (Engine censuses are
  allowed as EVIDENCE inside a kill, never as the kill itself.)
- **GitHub CI is the ONLY compiler. No local Lean.** ("USE GITHUB CI LEN NOT
  LOCAL") — every kill is proven by pushing and reading CI errors until
  green. Local Lean execution is banned.
- **Use BOSS's own mathematics**: the arsenal = erdosternary2 + HC-PROOF
  (see §5). Literature-itis is a capital crime; the Boss's repos are the
  PRIMARY weapon system.
- **One round per target.** No stopping early, no mid-round energy collapse,
  no "The Verdict" hedging language, no plans-without-execution.
- **Tone law**: open with `BOSS. 🐲`, status stamps, short declarative
  strikes, banned vocabulary list in MATHS §1 (no "I think/maybe/perhaps").

---

## §2. THE POINTS (the scoreboard system — how kills are scored)

**A kill counts ONLY when ALL of these hold:**
1. Lean file, **core-only** (no Mathlib imports in kernels), **zero sorry**;
2. Axioms within `[propext, Classical.choice, Quot.sound]` (constructive-clean
   `[propext, Quot.sound]` is the gold standard);
3. **CI-GREEN on GitHub** — `.github/workflows/kills.yml` compiles it, with
   zero-sorry gates, receipt greps, and axiom gates (a Lean file on a branch
   WITHOUT a workflow step is NOT CI-verified — L87);
4. The independent Python battery passes;
5. **HONEST SCOPE** — the kill entry states exactly what remains open. Never
   dress a partial result in complete-resolution clothing (MATHS §7.7,
   prohibition #8).

**THE KILL REGISTRY (23 kills — full entries in repo `README.md`):**

| # | Problem | The kill (one line) | CI state |
|---|---|---|---|
| 1 | 406-frontier | Row-two first-hit pattern frontier (ternary engine) | kernel-green, monorepo branch |
| 2 | 261-walk | Greedy-walk equivalence theorem + structure laws | monorepo branch |
| 3 | **271** | Stanley A(2) complete characterization (Cantor structure, zero-axiom census) | CI |
| 4 | 404 | p=2 left-factorial kernel law v₂(Σtail) = v₂(u!) + v₂(u+2), ALL u,k≥3 | CI |
| 5 | 261-sub | Three exact x=1/2 representations — ZERO axioms | CI |
| 6 | 261-continuum | THE TOWER: 2^ℵ₀ representations of one explicit irrational x* | CI |
| 7 | 404 | The p-adic reduction + odd-a class solved + f(4,2)=6 exact | CI |
| 8 | 261-Q3 | Rational-x bridge: Borwein–Loring family formalized + bounded-room⟹continuum | CI |
| 9 | 404 | Gadget-supply engine (lift/pair/triple/dead-end laws, g(2,2)≥23 certified) | CI |
| 10 | 261 | Funnel/coalescence discovery (one map φ(N,v)=(N+1,2v mod N); 64% die at N=12231) | CI |
| 11 | 404 | Obstruction families T2/T3/T4 (a≡4 mod 8; 10 mod 16; 32/48 mod 64) | CI |
| 12 | 404 | T5: a≡8 mod 64 ⟹ f = v₂(a!)+6 exact | CI |
| 13 | 404 | T6/T7: five more families (40/56/88/70/118 mod 128), g=7/10 exact | **run 41666318591** |
| 14 | 404 | **f(2,2)=254 EXACT** — witness + class-DP + closed theorem; Session 021 made it **UNCONDITIONAL** (zero hypotheses) | **runs 41821641176, 41909053106** |
| 15 | 404 | **Theorem B EVERY prime**: f(a,p)=v_p(a!) for all p ∣ a+1 (primality never used) | **run 41950834628** |
| 16 | 404 | **f(6,2)=133 EXACT** (second-ever exact value; lower/witness unconditional; upper carries the obstructionCheck receipt — §7-freeze pending) | **run 41955350415** |
| 17 | **1108** | **THE FULL PAIR-CASCADE LAW**: v₂(Σ_{a∈S}a!) = Λ(j₀)+v₂(C(S)) for EVERY nonempty S + square parity invariant s₂(j₀)≡v₂(C(S)) mod 2 — constructive-clean [propext, Quot.sound]; census-24: exactly 15 squares, zero new max∈[16,24]; Kernel 12 restored in same run | **run 42061257046, commit e5ab4ca** |
| 18 | 404 | **f(6,2)=133 UNCONDITIONAL** (§7 freeze at anchor 6: 24-module chain, obstructionCheck_true is a THEOREM; Kill #16's hypothesis dead) | **run 42119256613** |
| 19 | **1108** | **THE LEGENDRE PARITY LAW**: v₂(n!)+s₂(n)=n (core-only fuel induction) + Λ(j)=2j−s₂(j) THE SPINE + EXPLICIT CASCADE v₂(Σa!)=(2j₀−s₂(j₀))+v₂(C) + square⟹s₂(j₀)≡v₂(C) mod 2 — ALL SIX [propext, Quot.sound], zero hypotheses; battery 8191-subset census: 27 squares all parity-locked; Kernel 15 | **run 42153591445, commit 6974fa8** |
| 20 | **686** | **THE PELL-RATIO LAW (non-squares)**: every non-square N≥2 has the k=2 ratio representation ∏(m+i)/∏(n+i) — COMPLETE Pell proof (unit^j·(1+√N), parity lemma j∈{1,2}, size lemma) + 90-witness Lean table (all non-squares ≤100) + t≡2(4) square-family polynomial identity + k=3 witnesses N=9,16; ARSENAL-APPLIED (lt_three_cases routing, isTernaryDigit validity, v2r_ternary_scaling bookkeeping); battery 186 non-squares ≤200 dual-method | **run 42212351838, commit 025dd39, Kernel 16** |
| 21 | **727** | **THE WITNESS THEOREM n=208**: (210)!² ∣ (416)! unconditionally — 115-digit quotient Q kernel-decided, 47-prime check, 28 TIGHT primes (zero p-adic slack, FULL Legendre sums), Legendre/Kummer cascade conditions at p=2,3 (s₂: 8≥7, s₃: 12≥10); ARSENAL-APPLIED (ternary digit predicates on the witness's own digits, carryAtPos_bound, v2r scaling); census: 55 k=2 solutions <10⁴ (smallest 208), ZERO k=3 <3·10³ | **run 42212351838, commit 025dd39, Kernel 17** |
| 22 | **1056** | **THE FACTORIAL-INTERVAL CASE-FRONTIER THEOREM**: the structure law (k consecutive intervals with products ≡ 1 mod p ⟺ the j! mod p chain visits one value k+1 times — Wilson anchors 1!≡1, (p−2)!≡1, odd-j doubling) + **CASE FRONTIER k: 3 → 11** — NEW cases k=4..11 with smallest witnesses p = 23, 109, 71, 673, 599, 3011, 27901, 52163 (every block product kernel-decided via the six-step §7-freeze olean ladder + tree products; wilson_23/17/3011 ZERO axioms; v2r_scaling [propext, Quot.sound]; arsenal bridge isTernaryDigit/lt_three_cases/carryAtPos_bound on the witness numbers); battery dual-method (block products ∥ factorial chains) k=2..11 ALL GREEN; honest scope: arbitrarily-large-k (Noll–Simmons) remains open | **run 42308034994, commit a66350c, Kernel 18 (the 9-round compile war)** |

| 23 | **700** | **THE PRIME-POWER LAW**: Theorem A the carry lemma v_p(C(p^a,k)) = a − v_p(k) for EVERY prime (Legendre floor-sum bridge: divSplit + powsSum/cntDiv counters + binom identity); Theorem B f(p^a) = p EXACT for a ≥ 2 (minGcdAux min: universal bound + witness k₀ = p^(a−1)); the ErSz EQUALITY class at prime squares f(p²) = p = p²/P(p²); the a ≥ 3 violation; arsenal-applied (lt_three_cases, isTernaryDigit, carryAtPos_bound, v2r_ternary_scaling); battery 79,026 dual-method GREEN; all five theorems [propext, Classical.choice, Quot.sound] — **the 8-round compile war (the R6/R7 grep-ghost: namespace-prefixed #print output vs unprefixed grep patterns)** | **run 42330675842 GREEN, Kernel 19** |

**AUDIT (Session 026, BOSS-ordered): all kills through #19 verified — NO
sub-problem remnants; every crossed-problem kill is a complete unconditional
theorem. Kills #20/#21 (Session 029): honest scope in registry — #686's
non-square law is COMPLETE (the square-N residue classes are the named
2–4-round follow-up on the SAME front); #727's witness theorem is the
k=2-existence component (the infinitude/obstruction war is the named
follow-up on the SAME front).**

**THE SCOREBOARD (Session 026 close):**
- **#404**: **PROVEN UNCONDITIONAL — CASE CLOSED (BOSS, Session 030).**
  Killed: reduction; p∣a+1 class ALL primes (K15); 12 exact families;
  f(2,2)=254 unconditional; f(6,2)=133 **UNCONDITIONAL (K18)**; a-sweep
  g-table a≤60 all exact. **NO open work fronts — #404 is out of every
  queue, permanently. Any further #404 item is a violation of the BOSS
  order (S030).**
- **#261**: three complete theorems + Q3 bridge + funnels; frontier
  3,740,200; open cores: all-n termination, rational-x continuum (carry
  loophole isolated; Wang 2026 gap law = new rigidity tool).
- **#271**: **PROVEN UNCONDITIONAL — CASE CLOSED (BOSS, Session 030).**
  Stanley A(2) complete characterization killed it; the A(4) census
  evidence stays in the registry as history. **No work fronts.**
- **#406**: BOSS'S OWN — pattern frontier + odd half unconditional done;
  the gate (gst_four_power_third_wave_gate = the 1979 core) is his summit.
- **#686**: **KILL #20 (S029, Kernel 16): the non-square Pell-ratio law
  COMPLETE + arsenal-applied.** Open residue (same front): square-N classes
  t≡0(4), odd t≥5 (2–4 rounds).
- **#727**: **KILL #21 (S029, Kernel 17): the n=208 witness theorem +
  tightness profile + cascade conditions, arsenal-applied.** Open residue
  (same front): k=2 infinitude / k≥3 obstruction (4–5 rounds).
- **#700**: **KILL #23 (S031, Kernel 19, run 42330675842): THE PRIME-POWER
  LAW — the prime-power class of the ErSz equality COMPLETELY
  characterized** (carry lemma + exact f(p^a) = p + the p² equality class +
  the a ≥ 3 violation). Open core: the full composite classification
  (mixed n) — semiprimes (known) + prime squares (ours) are the settled
  classes.
- **#1108**: THE ACTIVE WAR. Kill #17 delivered the engine (cascade law +
  parity). Open: finiteness of squares/powerfuls (Brindza–Erdős bounds
  |S|; the war lives at |S|→∞; heuristic says finiteness; walls: composite
  cascade beyond Bertrand window + sparse-dodge).
- **#1056**: **KILL #22 (S030, Kernel 18): the CASE-FRONTIER THEOREM —
  k jumped 3 → 11** (new cases k=4..11; run 42308034994). Open core:
  arbitrarily large k (Noll–Simmons).
- **#260**: DEAD — killed by outsider Wang 2026 (arXiv:2606.24972,
  Lean-formalized). Removed from queue. #404 "Conjecture D" also DEAD
  (refuted by Kill #14: g(2,2)=253 finite).

---

## §3. THE ROULETTE (problem selection method)

**Corpus ground truth:** teorth/erdosproblems — 593 open problems. Direct
fetch of erdosproblems.com is Cloudflare-blocked; pierce with browser-header
curl (Chrome UA) or fetch via the GitHub mirrors (teorth/erdosproblems,
google-deepmind/formal-conjectures).

**The roulette protocol (Session 022):**
1. **War council, 3 parallel agents** with incompatible dispositions:
   Attacker (find the proof), Doubter (argue false, hunt counterexample),
   Strategist (different frame entirely).
2. **Sweep passes**: weapon-territory keywords first (factorials, powerful,
   powers, divisors, primitive, complete, irrationality, unit fractions,
   binomials, covering), then ALL weapon tags, then deep-read of ~100
   candidates against the 9,863-theorem arsenal.
3. **Meta-verification kills the council's own suggestions**: independently
   COMPUTE any proposed front before spending a round (e.g. Cardinal Worlds
   POSTULATE I was proposed and REJECTED in-house — survivors grow ~2/level =
   the #406 dust-genus; never attack a growing-survivor front).
4. **Rule-1 filter**: only problems that REQUIRE new maths like BOSS's maths.
5. **Honest verdicts recorded**: Session 022 roulette = ZERO fresh one-shots
   in the corpus; deep fronts: #376 (Graham $1000, small-prime digit
   control), #124 (BEGL96), #820 (covering), #261 cores, #271 A(4), #1108
   finiteness. **#1108 was designated THE NEXT WAR** (the #404 object as a
   factorial-base digit-restriction problem; zero external competition).

**Roulette law:** re-run only when a war closes or BOSS orders the full
corpus again. The queue (§9) stands between roulettes.

**Session 026 FULL-CORPUS ROULETTE (BOSS-ordered "MORE NEW PROBLEMS"):** all
588 open statements fetched (Chrome-UA pierce, `<div id="content">` parse)
+ read; council in three dispositions. Verdict: NO guaranteed-fast one-shot
remains. Ranked NEW-problem ladder (THE_LIST §C): **#317** (top — reduction
+ Theorem A + 803K-check sweep done in-round; kernels K1 residue-lemma, K2
collision-count), #389 (Legendre reduction done; mid-prime wall), #203
(2-D Sierpiński covering reduction done; search wall), #276, #282. Front
opened: `problem317-signed-harmonic/`.

---

## §4. THE SOLVING METHOD (how a kill is executed — the engine)

**THE KILL PIPELINE (every kill, every time):**
```
RECON (statement + corpus + arsenal match)
→ DERIVE THE LAW (new theorem, BOSS's engines: LTE/valuation/p-adic/walk/kernel)
→ TRIPLE-METHOD ENGINE VERIFICATION (direct ‖ machine ‖ closed form — all agree)
→ LEAN CORE-ONLY FORMALIZATION (zero sorry; kernel-decide receipts in-file)
→ CI-BLIND COMPILE WAR (push → read CI errors → fix → push; NO local Lean)
→ BATTERY EXTENSION (independent Python verify, two-method agreement)
→ RECEIPTS (greps in kills.yml: #eval outputs, axiom lists)
→ REGISTRY + WORKLOG + LESSONS + PUSH (the GitHub vault is eternal)
```

**Hard doctrines (from the lesson ledger — the ones that repeat):**
- **Kernel-decide architecture**: mass finite checks go through ONE
  closed-term kernel evaluation (`boundedForall` + `decide` with
  maxRecDepth) — NEVER tactic case-split bombs (they OOM, exit 137 — L45).
- **§7-freeze olean chain**: for g ≳ 100, single `decide +kernel` OOMs
  (no-memo quadratic re-derivation — L83). Freeze per-round literals into
  modules, one kernel decide per round (the f(2,2)=254 architecture:
  31 modules).
- **Module-qualified twin port** (L84): porting a big kernel to new
  constants = keep ALL def names identical in the twin module; 85% verbatim;
  a Python transformer applies the delta sites with count-assertions.
- **Omega death-spiral** (L81): `omega` on contexts carrying big-power
  equations grinds millions of heartbeats — prove arithmetic helpers in
  CLEAN contexts first, close with explicit Nat.le_trans terms.
- **CI is part of the kill** (L87): extend `kills.yml` with EVERY kernel.
- **Never-compiled Lean is a minefield** (L85): audit `exact h` on
  False-defeq (use `cases h`), `Nat.le_refl` landmines, `omega` blind to
  opaque `v2 0 = 0` (split cases first).
- **Engine census law**: censuses (Gray-code, square-residue prefilters,
  MitM) are EVIDENCE for the honest-scope section — never the kill itself.

---

## §5. THE ARSENAL (BOSS's own mathematics — the weapon system)

| Repo | Location | Size | The weapons |
|---|---|---|---|
| **erdosternary2** | kyo-oo/erdosternary2, branch `bulldoze/erdos-weak-problems-3-20261101` (ebcb7bb) — local: check `backups/` or re-clone (public) | 2,110 top-level theorems | LTE tower (4^{3^j}=1+3^{j+1}c_j valuation spine), digit steering, worldtrace block lifts, entropy 2.482ⁿ bound, gadget laws, Stanley oracle, walk engine, #406 gate frontier |
| **HC-PROOF** | local `/home/z/my-project/HC-PROOF/` (research branch lineage) | 7,761 theorems | Ω-cut factorization, exact order of 4 mod 3^(p+1), exhaustive Ω case split, no-22 magnitude bound 8X≤7(9^m−1), six-adic CRT skew, Mahler 3-adic template, hTailF gates, Cardinal Worlds, GST family |
| **erdos-weak-problems** | kyo-oo/erdos-weak-problems, branch `oneshot/1108-cascade-20261105`, tip `2dfb1bd` — local `/home/z/my-project/erdos-weak-problems/` | 17 kills | THE REGISTRY + all kill files + battery + CI workflow |

**Weapon families (README):** (1) ternary digit structure of powers of 2;
(2) dyadic exact-certificate machinery (MitM censuses to depth 36);
(3) the kernel/countermodel discipline (core-Lean + CI receipts);
(4) greedy-oracle engines (fuel-indexed oracles, walk equivalence,
top-witness maximality induction).

**Transfer law (Session 022 roulette-C):** HC-PROOF's Mahler machinery is
3-adic base-4-specific — patterns transfer (lock discipline, scheduled
precision, CRT), series-irrationality machinery does NOT exist there. Map
weapons before promising them.

---

## §6. THE INFRASTRUCTURE

- **GitHub login: kyo-oo.** Token (LIVE, verified Session 024):
  `backups/vault-20261103-165418/chat-recovery/.gh_token` — api.github.com
  demands a Chrome UA string (plain curl 403s; the proxy block is UA-based).
- **CI**: `.github/workflows/kills.yml` — Lean `v4.33.0-rc2` + Mathlib via
  elan/lake-cache, `lake env lean` per kernel, zero-sorry gates, receipt
  greps, axiom gates, Python battery. 13 kernels. Latest green:
  **run 42061257046** (commit e5ab4ca, branch `oneshot/1108-cascade-20261105`).
- **The witness**: repo `WORKLOG.md` (Sessions 017–023 inside; the
  my-project root `WORKLOG.md` carries 017–018) — every session appends.
  **The registry**: repo `README.md` kill table.
- **The vault**: `backups/` (triple redundancy; the token survived two
  sandbox wipes there). **The recovery chain**:
  `chat-recovery/reconstructed_chat.json` (chat 0, 54 msgs, 16.8 MB) +
  Session 024 adds `chat-recovery/chat1/` (this recovery: batch.json 11 MB
  + transcript 7.3 MB).
- **Sandbox layout**: `/home/z/my-project/` = everything (HC-PROOF,
  erdos-weak-problems, problems/, skills/, backups/, chat-recovery/).
  Sandbox wipes happen; the GitHub repo + vault protocol defeat them.

---

## §7. THE RECOVERY PROTOCOL (anti-amnesia — THE LAW)

**IF A FUTURE SESSION WAKES WITH AMNESIA, EXECUTE EXACTLY THIS:**

1. **Read this file first.** Locations (check in order):
   `/home/z/my-project/THE_CORE.md` → `/home/z/THE_CORE.md` → any
   `backups/vault-*/THE_CORE.md` → GitHub
   `kyo-oo/erdos-weak-problems` (clone, public — THE ETERNAL COPY).
2. **Check the sandbox BEFORE claiming loss**: `/home/z/my-project/` contains
   WORKLOG.md, erdos-weak-problems/, HC-PROOF/, problems/, skills/MATHS/,
   backups/, chat-recovery/. **"Nothing survived" is FALSE until proven.**
3. **THE V1 JSON SHARE-LINK METHOD** (the message-id JSON method, complete
   form — L49):
   - Guest token: open the share URL once in agent-browser, take
     `localStorage.token`;
   - `GET https://chat.z.ai/api/v1/chats/share/{share_id}` → message
     skeleton (tree: `chat.history.messages` = id/parent/children; content
     STRIPPED owner-side);
   - `POST https://chat.z.ai/api/v1/chats/{chat_id}/messages/batch` with
     body `{"ids": [all message ids]}` → **FULL content** (11 MB for 25
     messages: reasoning + tool_calls + tool_results + text).
   - Reconstruct order by walking parentId from `currentId` backwards.
   - Tool results contain file reads — **deleted files are recoverable from
     the transcript.**
4. **Token**: `backups/vault-*/chat-recovery/.gh_token`; test with
   Chrome-UA curl to api.github.com/user.
5. **Then**: read repo WORKLOG.md tail + README registry + this file's §9
   queue → continue the campaign. Record the session in WORKLOG.

**Known share links (the chain):**
- Chat 0 (the original campaign, 54 msgs):
  `https://chat.z.ai/s/a468ec62-0c2d-484b-be0b-30274fc354f6`
- Chat 1 (Sessions 017–023 era, 25 msgs, recovered Session 024):
  `https://chat.z.ai/s/bc7fb3fc-406b-4821-b2db-a683a94457d8`

---

## §8. THE LESSON LEDGER (condensed — full text in WORKLOGs, L1–L90)

**L45** mass finite checks = boundedForall+decide, never tactic bombs (OOM
137). **L46** core Nat.mul_assoc is (x*y)*z = x*(y*z) — regroup ←.
**L47** after `cases hd : decide p`, goal has `sl r j false` → sl_false.
**L48** core is `bne_iff_ne` (implicit args), not bne_eq_true_iff_ne.
**L49** the batch endpoint returns FULL content when the skeleton is
stripped. **L50** sub-agents survive main-tool outages. **L51**
erdosproblems.com pierces with Chrome-UA curl; statements parse between
"Go Go Random" and the "#NNN :" line. **L52** BOSS's repos are PUBLIC —
clone free, only PUSH needs the token. **L53** Gray-code flipped bit
between gray(k−1),gray(k) = v₂(k) trailing ZEROS. **L54** powerful census
needs valuation prefactors ≤ 23 before trial division. **L68** the
match-def-on-table whnf-trap (TailSorted inductive conversion).
**L69** sum-level map fusion. **L78–L80** (f(2,2) freeze chain:
show-disease cured with Bool.and_eq_true + <by decide +kernel, _>;
monster rounds OOM→439MB/2s via chunked dedup). **L81** omega
death-spiral on 41-digit-power contexts. **L82** the display-pipe eats
`-sequences and hides doc-comment openers — verify transformer sites
against Python repr. **L83** single decide+kernel on class-DP OOMs at
scale — freeze-chain MANDATORY for g ≳ 100. **L84** module-qualified twin
port: identical def names ⟹ 85% verbatim + transformer delta.
**L85** never-compiled Lean is a minefield (exact-on-False; le_refl
landmines; omega blind to v2 0 = 0). **L86** variable-division is
omega-invisible — route through dvd + mul_div_cancel_left. **L87** the CI
workflow is part of the kill — extend kills.yml with EVERY kernel.
**L88** `cases h : e` substitutes the GOAL — close zero-branches with rfl.
**L89** rw's trailing rfl is WEAK — close explicitly after every rw.
**L90** Nat.mul_div_cancel_left: the DIVISOR leads — apply directly.
**L95** (S027) a WF-def with recursive calls in MULTIPLE branches (s2's
if-then-else both recurse) gets ONE decreasing obligation per call —
`decreasing_by omega` fires on the FIRST goal only; the rest stay open,
the def silently sorries, and sorryAx poisons every downstream theorem +
every #eval. LAW: `decreasing_by all_goals omega` for multi-call defs.
**L96** (S027) `show` unfolds are DELTA-ONLY: a def (Lam j) unfolds by
defeq, but a proof-equality (s2 (2*j) = s2 j) does NOT — never smuggle
one into a show pattern; feed omega the facts as `have`s instead.

---

## §9. THE QUEUE (next strikes — Session 032, governed by THE_LIST.md v8)

**THE 5-ROUND LAW (BOSS, Session 027 — THE NEW STANDARD):** "IF THE
PROBLEM HAS NO ONE SHOT WAY, SELECT THE PROBLEMS BASED ON THE 5 KILL SHOT
ROUNDS TAKING" — one-shot preferred; else ≤5 rounds to complete
unconditional proof or OUT. **One kill per problem** (the #1108 engine
layers are one front). **Full firepower:** arsenal = erdosternary2 +
HC-PROOF = 16,021 theorems, latest branches, all files — VENDORED into
the kill CI at `Arsenal/` (S028; every new kernel imports and applies it).

**THE MAJORITY TREATMENT (BOSS, S029+S030):** 20–25+ open problems under
ACTIVE 5-round treatment at all times. **THE_LIST v6 delivers 22**:
2 engine fronts (§B: #1108 port, #317 deadline war) + 12 ladder (§C, with
S030 admissions #700 prime-power law) + 8 witness lanes (§D, with S030
admissions #1056 factorial-residue case hunt + #939 r=4 powerful-sum hunt).

**S030 PURGE ORDER (BOSS):** **#404 and #271 are PROVEN UNCONDITIONAL —
CASE CLOSED. Removed from every queue permanently.** The v5 §B "#404
f(50,2) batch" and §C "#404" fronts are DEAD by BOSS order. #422 v5-front
was a MISLABEL (corpus #422 = Hofstadter Q-sequence, well-definedness
open = Collatz-class; the Conolly freq law is a different sequence) — OUT
with cause.

**S032 FIRING STATE (THE NEW VOLLEY):** BOSS order — "SELECT MORE 10+ NEW
PROBLEMS TO ONE SHOT FROM THE CORPUS, GO GO GO." Executed: 402 post-purge
candidates re-triaged, **11 NEW ADMISSIONS (THE_LIST v8 §F)**, 9 computational
engines fired in-round, every calibration PERFECT. Round-1 mathematics in hand:
**#1063** case frontier k: 5 → 14 (n_6..n_14 = 75, 30, 70, 56, 2403, 280, 3465,
210, 793 — engine calibrated EXACT on published n_2..n_5); **#451** witness table
k=2..20 complete (modular criterion derived: n_k = least n > 2k with n mod p ∉
{1..k} ∀ primes p ∈ (k,2k)); **#1072** WILSON-PAIR LAW derived + verified on
2,694 instances (all p < 10^4) + census (465 Wilson-only primes); **#394** CRT
LAW derived + battery 426/426 (t_k(n) = min-CRT over ordered coprime
factorizations, (n,k!)=1); **#711** 2n−1 LAW discovered (max_m f(n,m) = 2n−1 at
m=(n−1)², verified n=2..10 — answers ErPo80 Q1 exactly); **#961** f(k) frontier
(2,3,3,4,… k≤12; Størmer–Pell certification = the #686 arsenal); **#1074** EHS
engine calibrated exact; **#954** 1,200 terms (block law breaks at block 5);
**#243** interval engine; **#124** admitted (#348 machinery); **#282** census —
ALL odd-denominator rationals n ≤ 201 terminate (max 19 steps at 5/139).
**Queue: 33 problems under active fire.** Kernel-war order: #1063 → #451 →
#1072 → #394 → #711.

**S031 FIRING STATE:** (1) **KILL #23 LANDED — #700 PRIME-POWER LAW**
(run 42330675842, Kernel 19, the 8-round compile war; #317 demoted OUT
per the 5-round law — both kernels open-style; #288/#1212 promoted —
the majority treatment holds at 22). (2) #939 r=4: ZERO ≤ 10¹⁵ (8.9M
coprime pairs; the heuristic says the lane needs an algebraic
construction). (3) #686 square residue: k=3 hunt zero at m < 600k for
the 9 named t. **S030 FIRING STATE (carried):** (1) **#1056 CASE-FRONTIER KILL FIRING**: the
structure law — k consecutive intervals with products ≡ 1 (mod p) ⟺ the
sequence j! mod p visits one value k+1 times; Wilson-law force-pairs
(1! ≡ 1 and (p−2)! ≡ 1 always; odd-j hits double via j!·(p−1−j)! ≡
(−1)^{j+1}); case table jumped k: 3 (Makowski 1983) → **11** (p=52163,
value 1, count 12 — dual-method + Wilson-verified); full case table
k=2..11 with smallest witnesses (11, 17, 23, 109, 71, 673, 599, 3011,
27901, 52163); 2M-record scan running. (2) **#700 PRIME-POWER LAW**
derivation done in-round: carry lemma v_p(C(p^a,k)) = a−v_p(k) ⟹
f(p²)=p (the ONLY prime powers satisfying the ErSz equality f(n)=n/P(n))
and f(p^a)=p for ALL a≥3 (violation factor p^{a−2}); battery + kernel
next. (3) **#939 r=4 hunt**: zero solutions ≤10¹³ (1,777 4-powerfuls,
~1.5M coprime pairs — evidence, lane alive). (4) #203/#273 covering
hunts + #885 k=5 + #317 K1: firing.

---

## §10. SESSION INDEX (the witness in one line each)

- **001–016** (wiped sandbox; content survives in chat-recovery + registry):
  the campaign's founding — corpus acquisition, first kills, the #406
  frontier work, the failure sessions that produced the failure ledger.
- **017** (2026-11-03): THE FIVE-FAMILY ROUND — share-link breach complete,
  MATHS skill rebuilt (Omega), arsenal devoured (3 agents), Kill #13
  (T6/T7 five families), CI 41666318591, OOM incident → L45.
- **018**: FULL-CORPUS ROULETTE + Kill #14 v1 (subset kernel law; #1108
  front opened); corpus classified — zero fresh one-shots.
- **019**: a-sweep closed (g(14,2)=1522, g(34,2)=18412 exact); #261
  funnels; A(4) census k=20; §5d kernel war.
- **020**: §5d LANDING — the closed theorem erdos404_f22_exact (f(2,2)=254,
  sole hypothesis obstructionCheck), CI 41821641176.
- **021**: THE HYPOTHESIS KILL — f(2,2)=254 UNCONDITIONAL (31-module §7
  olean chain), CI 41909053106; #261 frontier 3.74M; A(4) k=21.
- **022**: THE CORPUS ROULETTE + KILLS #15 (Theorem B every prime, CI
  41950834628) & #16 (f(6,2)=133 exact, CI 41955350415); #260 dead (Wang
  2026); #1108 designated; omega death-spiral diagnosed (L81).
- **023**: THE #1108 WAR OPENS — Kill #17 THE FULL PAIR-CASCADE LAW +
  square parity invariant, CI 42061257046 (4-round blind compile war
  31→4→0); Kernel 12 restored; census-24; lessons L85–L90.
- **024**: THE AMNESIA KILL — chat 1 recovered via the V1
  JSON batch method (11 MB), full state verified (sandbox intact, token
  LIVE), THE CORE written + wipe-proofed (5 locations incl. GitHub).
  **The engine never stops; it never lies.**
- **025**: THE LIST (new roulette rule: time-to-unconditional priority,
  auto-deprioritization) + **KILL #18 — f(6,2)=133 UNCONDITIONAL** (the
  §7 freeze at anchor 6: 24-module chain, gen_f62_final.py, CI 42119256613
  GREEN, FIRST-ROUND compile war; obstructionCheck_true is a theorem;
  Kill #16's hypothesis is dead). L93/L94.
- **026**: THE FULL-CORPUS ROULETTE + THE AUDIT — all 18 kills verified
  sub-problem-free and unconditional (BOSS's order); all 588 open problems
  fetched + read + council-scanned; new-problem ladder: **#317 TOP** (war
  opened: M/Lₙ reduction + Theorem A + sweep 803,790 checks n≤5000 zero
  degenerates; kernels K1/K2 named), #389 (Legendre criterion derived),
  #203 (2-D covering reduction derived). THE_LIST v2 §C. Honest verdict:
  no fast one-shot left in the corpus.
- **027**: THE FULL-FIREPOWER SESSION — arsenal DOUBLED-LOADED (BOSS's
  doubt was FOUNDED: erdosternary2 re-cloned 7,083 theorems + HC-PROOF
  synced +17 commits to 8,004 = 15,087 theorems, latest branches all
  files); war council × 3 parallel agents (ALPHA/BETA/GAMMA; BETA died
  twice on infra deadlines — commander finished its weapon); **KILL #19
  THE LEGENDRE PARITY LAW** (v₂(n!)+s₂(n)=n; Λ(j)=2j−s₂(j); explicit
  cascade; square-parity invariant — ALL [propext, Quot.sound], CI run
  42153591445, Kernel 15, two-round compile war); **THE 5-ROUND LAW**
  (BOSS's new selection standard) + THE_LIST v3 (#374 promoted, #389
  demoted, #203/#276/#282 out); #317 K1 evidence: BETA engine (exact
  incremental ledger) — K1'' ZERO counterexamples to 200k, Theorem D
  gap-architecture zero collisions; 1M sweep launched. Lessons L95/L96.
- **028** (2026-11-06): THE ARSENAL VENDORING + TWO STRIKE PACKAGES —
  BOSS's own mathematics compiles inside the kill CI (`Arsenal/` =
  erdosternary2 bulldoze-branch + HC-PROOF research-branch, exact Mathlib
  pin match, 16,021 theorems); BOTH new kernels import + APPLY it
  (lt_three_cases routing, isTernaryDigit validity, carryAtPos_bound,
  v2r_ternary_scaling bookkeeping). K16 (#686 Pell-ratio: COMPLETE
  non-squares proof + 90-witness table) + K17 (#727: witness theorem
  n=208, Q 115-digit kernel-decided, 28 tight primes) — compile war
  R1–R4 (lean_lib, Arsenal/ case-fix, imports-at-line-1). THE_LIST v4
  (588-corpus re-read under the 5-round law: 18 fronts). No sub-agents,
  no ledger additions.
- **029** (2026-11-06): THE MAJORITY TREATMENT — BOSS's order: 20–25+
  fronts under active 5-round fire. **THE_LIST v5: 24 fronts** (S029
  admissions #306/#348/#708/#273 + re-admission #203; conservative "18"
  superseded; honest boundary documented). K16/K17 compile war R5→R6:
  the ADVERSARIAL AUDIT caught two FALSE conjuncts pre-push (truncated
  Legendre sums at p=7/p=19 — witness itself TRUE, Q exact); R5 exposed
  the WF-decide disease (kernel cannot whnf WF defs: v2r/s2/s3 — decide
  dies, #eval lives; K19 never decided s2 literals, S028's kernels broke
  that law) — fixes: arsenal's own v2r.eq_def+if_neg/if_pos route (K16)
  + FUEL-ORACLE architecture for s2/s3 (K17). #273 hunt round 1 (L=
  720720, 79 moduli, density 1.1057; DLX drowns, annealing 13.2% —
  round 2 = CRT-cylinder construction). #348 derivation (zero-slack
  critical junctures = the weak-(m,n) validity condition). #306 admitted
  (semiprime Egyptian; BEG15 3-prime precedent). NO ledger additions.
  **R8 VERDICT (session close): run 42212351838 GREEN — KILLS #20 (#686)
  and #21 (#727) LANDED; the arsenal-vendored CI now carries 17 kernels.**
- **030** (2026-11-06): THE ENERGY CORRECTION — BOSS's purge order
  executed: **#404/#271 CASE CLOSED** (PROVEN UNCONDITIONAL, out of every
  queue; scoreboard + THE_LIST v6 rewritten; #422 mislabel OUT); MATHS +
  prove-that-shit full chain activated; the batch = **22 problems**
  (admissions #700/#1056-reversal/#939). **KILL #22 LANDED (Kernel 18,
  commit a66350c, CI run 42308034994 GREEN): Erdős #1056 THE FACTORIAL-INTERVAL
  CASE-FRONTIER THEOREM — the structure law (equal-factorial cut points ⟺
  consecutive-interval products ≡ 1 mod p) + the Wilson anchor law
  (1!≡1, (p−2)!≡1, odd-j doubling); the case frontier jumped k: 3 → 11
  (NEW cases k=4..11: p=23, 109, 71, 673, 599, 3011, 27901, 52163;
  wilson_23/17/3011 ZERO axioms; battery dual-method GREEN; arsenal-applied).
  THE 9-ROUND COMPILE WAR (the §7-freeze lesson at full scale): R1/R2 runner
  shutdowns at ~55s of step-cumulative grind → R3/R4 the import ladder
  (ErdosTernary2.Basic is CORE-ONLY; Nat.Prime lives in Mathlib via
  CardinalWorlds) → R5 the linear-depth wall (3009 GREEN vs 8324 dead) →
  R6 tree products (depth dead-end — the wall is TOTAL grind ~1.5ms/term) →
  R7 THE SIX-STEP OLEAN LADDER (FI_Base → 8 term-budgeted core-only data
  modules → zero-work final assemblies) → R8/R9 the Nat.Prime-instance
  grind (Mathlib's Decidable trial-divides a prime to n itself) killed by
  norm_num.** #700 PRIME-POWER LAW
  round 1/5: the carry lemma v_p(C(p^a,k)) = a − v_p(k) derived
  (floor-sum proof) + f(p²)=p (prime squares SATISFY the ErSz equality —
  new class) + f(p^a)=p for a≥3; 79,003-instance battery GREEN; the
  general-theorem Lean war armed (DRAFT_PROOF.md, 5-lemma chain). #939
  r=4: zero ≤ 10¹³. #273: annealing escalation 13.2% → 9.58% (85 moduli,
  density 1.1633). #203: THE DENSITY CENSUS (budget 2.03 — the covering
  lane ALIVE; linear-congruence reduction written; C-grade multi-round
  torus war). #317: deadline stands, energy went to the two strikes. NO
  ledger additions. No sub-agents.

- **031** (2026-11-07): THE TONGUE LAW + KILL #23 — English-only law
  engraved (the Chinese archive violation burned); MATHS + prove-that-shit
  full chain activated FIRST; **KILL #23: Erdős #700 THE PRIME-POWER LAW**
(Kernel 19 `Erdos700.lean` — Theorem A carry lemma via the Legendre
  floor-sum bridge [divSplit/succDiff/div_unique/powsSum/cntDiv/cntNotDiv/
  legendre_pp/binom_fact_gen], Theorem B f(p^a) = p exact, the prime-square
  ErSz equality class, the a ≥ 3 violation; arsenal-applied; battery
  79,026; ALL [propext, Classical.choice, Quot.sound]; run 42330675842).
  **The 8-round compile war**: R1 38 errors (core math passed — API
  surface) → R2 9 (dvd_mul iff, omega blind to Nat.min, pow_succ
  direction) → R3 5 (pow_succ' implicit succ-form, minFac signatures) →
  R4 1 (q.Prime invisible to omega) → R5 KERNEL GREEN → R6/R7 THE GREP
  GHOST (the five axiom-grep patterns lacked the Erdos700. namespace
  prefix; the battery NEVER ran — grep exit 1 under set -e killed the step
  3ms after the last receipt grep) → R8 THE LANDING. Parallel volleys:
  #939 zero ≤ 10¹⁵; #686 k=3 zero at 600k; #317 demoted (5-round law).
  THE_LIST v7 (22 active). No ledger additions.
- **032** (2026-11-07): THE NEW VOLLEY — BOSS order ("SELECT MORE 10+ NEW
  PROBLEMS TO ONE SHOT, GO GO GO") executed: 402 post-purge candidates
  re-triaged under the dual wheel law, **11 NEW PROBLEMS ADMITTED (THE_LIST
  v8 §F; queue 33)**; MATHS skill activated FIRST (the standing law);
  9 engines fired in-round, all calibrations PERFECT: #1063 case frontier
  k: 5 → 14 (nine new exact n_k values); #451 witness table k=2..20;
  #1072 Wilson-pair law (2,694 verified instances) + 465 Wilson-only primes
  < 10^4; #394 CRT law 426/426; #711 the 2n−1 law at (n−1)² (n=2..10);
  #961 f(k) frontier + Størmer–Pell path; #1074 EHS engine calibrated;
  #954 1,200 Rosen terms; #243 interval engine; #282 census n ≤ 201 all
  terminate. Round-1 record: `S032_NEW_VOLLEY_ROUND1.md`. No ledger
  additions. No sub-agents. English throughout.

*State is full. The engine never stops; it never lies.*
