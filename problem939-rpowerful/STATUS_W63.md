# STATUS_W63 — Erdős #939 (r-powerful sums), r=4 lane — THE TRUE BOX HUNT, W63-B1

**Task W63-B1 (Wave 1, agent 2/12). Worktree /home/z/waves/w63-b1-p939, branch
w63-b1-p939. One-line verdict: the W62 hunt engine is repaired, dual-method
validated, and the TRUE 4-powerful pairwise-coprime box is certified ZERO all
the way to the engine ceiling c ≤ 10^19 — plus zero coverage of the four
algebraic families far beyond the box, plus two new Lean zero-box anchor rows
(CI verdict pending at write time). No witness: the Q1 lottery stays open.**

---

## 1. THE RESULTS (complete, unconditional, python-certified finite checks)

**THE BOX THEOREM (the mission):** there is NO triple (a, b, c) of pairwise-
coprime 4-powerful numbers (every prime divisor p satisfies p^4 | n, the K60
`rpow 4` definition — 1 included vacuously per `rpow 4 1 = true`) with

    a + b = c,   c <= 10^19,

and a fortiori none with c ≤ 10^13, 10^14, ..., 10^18. This is an exhaustive
finite check over ALL 449,087 four-powerful values ≤ 10^19 (and over every
candidate pair in the three sound-and-complete lanes below). Prior GENUINE
coverage of this problem: none (the W62 audit — AUDIT939_prior_hunt_bug.md —
retracted every prior r=4 zero-claim as FLT-void: those engines enumerated
FOURTH POWERS, i.e. swept x^4+y^4=z^4). The new certified frontier is therefore
10^19 — vs. the K60 kernel's honest "no raw pair below 16" and the 10^15
bracket row: **the frontier moved from 16 (fully certified) / 10^15 (bracketed)
to a fully certified 10^19**, a 10,000,000,000,000,000,000× extension of the
certified zero region.

**The certificate table** (machine receipts: `ck939_box<e>_done.json`, full
non-coprime sum-hit censuses in `ck939_box<e>_[eo|oo].json.gz`; inline logs in
`hunt939d_output.txt.gz`, `hunt939e_output.txt.gz`):

| box | 4-powerful ≤ limit | even E | odd O | CON pairs (a=1) | EO checks | OO checks | sum-hits | coprime hits | witnesses | wall |
|----|----|----|----|----|----|----|----|----|----|----|
| ≤ 10^13 | 11,653 | 8,567 | 3,086 | 0 | 920,491 | 396,753 | 3,868 | 0 | 0 | 0.2 s |
| ≤ 10^14 | 21,660 | 15,979 | 5,681 | 0 | 3,047,913 | 1,375,686 | 8,062 | 0 | 0 | 0.5 s |
| ≤ 10^15 | 40,048 | 29,645 | 10,403 | 0 | 10,037,900 | 4,709,248 | 16,351 | 0 | 0 | 1.5 s |
| ≤ 10^16 | 73,698 | 54,720 | 18,978 | 0 | 32,932,488 | 15,920,864 | 32,544 | 0 | 0 | 4.3 s |
| ≤ 10^17 | 135,058 | 100,537 | 34,521 | 0 | 107,549,510 | 53,291,773 | 64,433 | 0 | 0 | 14.8 s |
| **≤ 10^18** | **246,652** | 184,012 | 62,640 | 0 | **350,129,827** | **177,485,256** | 126,511 | **0** | **0** | 44.9 s |
| **≤ 10^19** | **449,087** | 335,682 | 113,405 | 0 | **1,136,219,675** | **587,169,988** | 246,243 | **0** | **0** | 293.5 s |

Every one of the 246,243 sum-hits at 10^19 (and 126,511 at 10^18, etc.) is a
NON-coprime triple (gcd(a,b) > 1; pairwise coprimality reduces to gcd(a,b)=1
because c = a+b). `WITNESS939.md` was never created — no witness exists in the
swept region.

**THE FAMILY THEOREMS (beyond the box, zero):**
- **L1 (diff-of-fourth-powers, opposite parity):** a = x^4, c = z^4,
  gcd(x,z)=1, x,z opposite parity; b = z^4−x^4 = u·v·w with u = z−x, v = z+x
  (odd, coprime) and w = (u²+v²)/2 — b 4-powerful forces u, v, w pairwise
  coprime 4-powerful. Swept: ALL odd coprime 4-powerful u, v ≤ 10^13 with
  w ≤ 10^26 (4,760,155 pair checks, W-list = 528,650 values) — **0 w-hits,
  0 witnesses** → no such triple with z+x ≤ 10^13 and z²+x² ≤ 10^26
  (c = z^4 reaches ~10^52 in this family). 12.0 s.
- **L2 (same family, x,z both odd):** b = 8·s·t·(s²+t²), s = 2^α·s′ with s′, t
  odd 4-powerful coprime, v₂(b) = 3+α ≥ 4. Swept to the same bounds:
  45,164,502 checks — **0 candidates, 0 witnesses**. 62.5 s.
- **SG (Sophie–Germain):** a = x^4, b = 64·z^4 (x odd, gcd(x,z)=1),
  c = x^4+64z^4 = u·v with u = x²−4xz+8z², v = x²+4xz+8z² coprime 4-powerful
  (Sophie–Germain identity; v−u = 8xz; disc ≥ 0 forces v/u ∈ (3−2√2, 3+2√2)).
  Full (u,v) sweep with uv ≤ 10^26: 596,621 disc-checks, 70 square discs —
  **0 witnesses**. 2.0 s.
- **R2 (quartic twist, the Z[i] kernel route):** X^4+Y^4 4-powerful with
  gcd(X,Y)=1, X,Y opposite parity (both-odd dies by the mod-16 obstruction);
  X²+iY² = γ·δ^4, N(γ) = c = the 4th-power-free kernel (primes ≡ 1 mod 8,
  exponents 1–3), δ = u+iv. Swept ALL 360 (c, γ) kernels with N(γ) = c ≤ 4096
  (316 c-values) × all δ with u,v ≤ 400 (δ⁴ table: 160,801 entries; both
  conjugate signs): **115,776,720 checks, 0 candidates, 0 witnesses** — covers
  X^4+Y^4 ≤ ~4.3·10^25. 145.9 s.

**THE LEAN ANCHOR ROWS (new in Erdos939R4.lean; CI is the verdict):**
`LIST4P7` (the exhaustive 234-value 4-powerful list below 10^7) +
`box939_r4_1e7_pairs` (no two COPRIME members of LIST4P7 sum back into the
list — closed native_decide goal per the S059 proof-route law) +
`box939_r4_1e7_succ` (no member's successor is a member — the a=1 lane).
Together with the python completeness certificate (below) these are: no
pairwise-coprime 4-powerful triple with c ≤ 10^7, anchored INSIDE the kernel
module — the same hybrid (list-completeness in python, closed fold in Lean)
as the campaign's census-row pattern, scaled to the zero-box.

## 2. WHY THE W62 RUN DIED, AND THE REPAIR (hunt939d.py)

The W62 engine died at 355 output bytes. Two defects, both fixed:
1. `REPO` was hard-coded to the dead machine's main-repo path — the engine
   wrote its log OUTSIDE the worktree (violating the push discipline) and the
   path no longer exists here. REPO is now the script's own directory.
2. No resume machinery: any L75 reaper kill lost the whole run. The box lanes
   (CON/EO/OO) now write atomic per-lane JSON checkpoints every ≤45 s /
   20,000 iterations (`ck939_box<e>_[con|eo|oo].json`), and every invocation
   resumes from them; witnesses are gcd-checked and dual-method verified THE
   MOMENT they land (never held for a lane end a reaper might eat). Phases are
   generic (`PHASES=B13,B14,...,B19` — sub-boxes are the incremental bounded
   theorems). `hunt939e.py` (the queued 10^19 wrapper with dead-machine paths)
   is superseded by `PHASES=B19 LOGFILE=hunt939e_output.txt` — run and
   completed this round.

## 3. DUAL-METHOD VALIDATION RECEIPTS (before the grind — the law)

`validate939.py` → `validate939_output.txt`; Phase A → `hunt939d_output.txt.gz`.
1. **M1 (the DFS enumerator `gen4`, exponents 4,5,6,... freely) at 10^4
   reproduces the K60 Lean census row (`Erdos939R4.census_r4_members`, 25
   values incl. 1) exactly — 24/24.**
2. **M2 (a completely independent numpy rad-sieve: rad(n) computed for EVERY
   n ≤ 10^7 by prime-slice multiplication; n 4-powerful ⟺ rad(n)^4 | n via
   four exact divisions) reproduces the same K60 census row at 10^4 — 24/24.**
3. **M2 == M1 exact element-by-element set equality at 10^7 (234 values).**
4. **The bucketed box lanes == brute-force reference at 10^7** (all (a,b)
   pairs, a<b, a+b ≤ 10^7, sum in list): 25 mixed/odd sum-hits both ways.
5. Audit anchors: 32 = 2^5, 2592 = 2^5·3^4, 3888 = 2^4·3^5, 614656 = 2^8·7^4,
   1594323 = 3^13 — all present (the values the prior fourth-power engines
   missed); factorization receipts in validate939_output.txt.
6. TRUE counts re-derived: 11,653 ≤ 10^13, 40,048 ≤ 10^15, 73,698 ≤ 10^16,
   135,058 ≤ 10^17, 246,652 ≤ 10^18, 449,087 ≤ 10^19 (matches the W62 audit
   rows; generator timings 0.0–0.5 s).

**Lane soundness & completeness (why the box sweep misses nothing):** a
pairwise-coprime triple (a,b,c) all 4-powerful, a+b=c, c ≤ L, a ≤ b, has:
- (a,b) both even → gcd ≥ 2: dead (never swept, correctly).
- a = b → gcd(a,b)=a > 1 (a=1 gives c=2, not 4-powerful): dead.
- a = 1 → c = b+1: consecutive 4-powerful pair (CON lane; 0 pairs ≤ 10^19).
- (e,o,c) mixed parity → c odd; e even 4-powerful ⇒ 16 | e ⇒ c ≡ o (mod 16):
  the EO lane sweeps every same-bucket (o,c) pair with e = c−o tested against
  the even list (16 | e enforced by the bucket congruence).
- (a,b,c) all odd → c even 4-powerful ⇒ 16 | c (the certified K60
  `mod16_obstruction`) ⇒ b ≡ −a (mod 16): the OO lane sweeps every
  complementary-bucket (a,b) pair, a < b, a+b ≤ L, sum tested against the even
  list.
Every candidate found by either lane is gcd-filtered (pairwise coprimality =
gcd(a,b) = 1 when c = a+b); a surviving candidate is dual-method verified
(sympy.factorint vs gmpy2 trial-division-to-n^(1/4) + Pollard-rho, agreement
required) and written to WITNESS939.md — none occurred.

## 4. WHAT REMAINS OPEN + THE NEXT-ROUND PATH

1. **The witness lottery (Q1 for r=4) stays open** — zero coprime triples
   through 10^19 and through the four algebraic families. Next escalation:
   the box engine's uint64 ceiling is 1.8·10^19; **10^20+ needs a big-int lane
   (bisect-based membership on Python int lists, or 2×32-bit split words) —
   the natural next round of this hunt** (est. |L(10^20)| ≈ 800k, |O| ≈ 200k;
   EO+OO ≈ 6·10^9 pair-checks, ~15–30 min chunked).
2. Family lanes can push their own bounds (LANE_B beyond 10^13 — the u,v list
   is the W62 bottleneck design; SG_C beyond 10^26; R2_CMAX beyond 4096 /
   R2_UVMAX beyond 400 — R2's cost is ~c_gs·2·(uvmax+1)² and 4096/400 already
   covers X^4+Y^4 ≤ 4.3·10^25).
3. The Lean anchor pattern (LIST4P7 at 10^7) extends to 10^8/10^9 lists
   (~450/~900 literals) — native_decide fold cost grows as |L|³; 10^7 is
   comfortably green, 10^8 is the next safe rung (est. seconds-to-a-minute of
   IR evaluation) — decide-budget it before pushing.
4. The sub-box zero theorems ≤ 10^13..10^19 are ready for Lean `native_decide`
   encoding only via the list-membership hybrid (full `List.range` scans are
   infeasible > 10^4); the python certificates are the primary artifacts this
   round, exactly as briefed.

## 5. FILE MAP (this round's additions in problem939-rpowerful/)

- `hunt939d.py` — repaired engine (resumable box, generic B<n> phases, CON
  lane, append-mode chunk history).
- `validate939.py` / `validate939_output.txt` — the dual-method enumerator
  validation receipts.
- `hunt939d_output.txt.gz` — Phase A + B13..B18 + L1/L2/SG/R2 logs.
- `hunt939e_output.txt.gz` — the B19 run (the queued hunt939e, completed).
- `ck939_box<e>_done.json` (e = 13..19) — machine-readable box certificates.
- `ck939_box<e>_[eo|oo].json.gz` — full non-coprime sum-hit censuses (the
  re-derivable receipts; every hit with its gcd).
- `Erdos939R4.lean` — the two new zero-box anchor rows + LIST4P7 + memNat.
- `gen_lean_row939.py` — the deterministic generator of the Lean rows (from
  the validated list; rerun-safe).
- `STATUS_W63.md` — this report.

No WITNESS939.md — the lottery did not hit this round.

*The engine never stops; it never lies.*
