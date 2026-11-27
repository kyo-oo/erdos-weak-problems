# THE DOUBTER'S FRONTIER REPORT (S094) — v₂* recomputed, extended, and the +10 earthquake

**Method:** uniform exact-integer meet-in-the-middle (low/high half subset
sums as exact Python ints; per-level residue-set membership: v₂*(M) ≥ t
⟺ ∃ nonempty S ⊆ [0,M] with Σ3^i ≡ 0 mod 2^t; monotone in t — first
failure caps the curve). Third method, independent of the campaign's
enum (M ≤ 21) and MITM-on-2^64 (M = 22..34).

## §1 THE THIRD-METHOD VERIFICATION — FULL AGREEMENT

The campaign's `caplaw/v2star_table.json` (v2*(M), M = 0..34): **ZERO
MISMATCHES** against this round's recomputation. Every jump point
verified: M=1 → 2 (witness 4 = 2²), M=5 → 8 (256 = 2⁸), M=14 → 16,
M=23 → 25, M=31 → 35.

## §2 THE EXTENSION (M = 35..44) — THE +4 CEILING IS DEAD

| M | 35 | 36 | **37** | 38 | 39 | 40 | 41 | 42 | 43 | 44 |
|---|---|---|---|---|---|---|---|---|---|---|
| v₂*(M) | 35 | 37 | **47** | 47 | 47 | 47 | 47 | 47 | 47 | 47 |
| excess | 0 | +1 | **+10** | +9 | +8 | +7 | +6 | +5 | +4 | +3 |

**THE M=37 JUMP: v₂* = 47, EXCESS +10** — double the campaign's maximum
(+4 at M=31). THE WITNESS, verified three ways (MITM reconstruction,
direct evaluation, exact-odd-part check):

```
S = {0,4,5,7,10,11,13,15,17,19,20,21,23,24,26,28,29,31,34,35,36,37}   (22 digits)
Σ 3^i = 667,799,382,246,031,360 = 2^47 × 4745   (4745 odd)
⌊log₃ Σ⌋ = 37;   v₂ = 47;   excess = +10;   t=48 FAILS (the jump is exact)
```

**THE L91 LAW STRUCK AGAIN:** the campaign's "+4 ceiling" held through
M=34 and died at M=37 — three levels past the table's end. Every cap
constant **C ≤ 9 IS REFUTED** by this witness. (The Postulate-II
successor structure, the LX-corrected bounds at small constants — all
dead below C = 10.)

## §3 THE BUG THAT ALMOST LIED (the verification law's catch)

A first extension run reported v₂* = 56/57/58 at M = 42/43/44 (excess
+14!) — **a stale-modulus bug** (B-side residues carried mod 2^(t−1)
into the level-t check). The two-method verification law caught it: an
independent witness search at (M=42, t=56) found NOTHING. The clean
re-run (fresh residues per level) gives the true 47/47/47 — recorded
here so the bug can never resurrect. **The verified numbers are §2's.**

## §4 THE HONEST FRONTIER LAWS

1. The jump positions: M = 1, 5, 14, 23, 31, 37 — jump excesses
   **1, 3, 2, 2, 4, 10** — noisy, trending UP at the frontier.
2. Between jumps the excess DECAYS (M=37: +10 → M=44: +3) — the ceiling
   is a staircase, not a ramp.
3. **CAP(185): ALIVE, with 18× headroom** (max observed excess +10).
   The kill needs +185. No evidence yet of the growth rate that would
   deliver it — but the +10 jump (double the previous max) is the
   strongest warning yet: the block constructions are improving.
4. **THE RIDER MARGIN: −22.7 at M=44** (the extremal sits 22.7 below
   the rider line 1.585·M) — Erdős #406's conjectural truth remains
   empirically comfortable at the frontier.
5. The machine-readable curve: `S094_v2star_recomputed.json`
   (M = 0..44, all clean-method).

## §5 THE VERDICT

The doubter's kill list: C ≤ 9 caps (dead, witnessed); the campaign's
"+4 ceiling" belief (dead); the buggy +14 readings (dead on arrival,
caught). The survivor: CAP(185) — wounded by the trend, alive by the
margin. The doubter's advice to the campaign: **the cap lane is the
weaker leg — the Mahler diagonal lane (the non-periodicity of the
frozen diagonal) is where the kill lives.**

The engine never stops; it never lies. In English, always.
