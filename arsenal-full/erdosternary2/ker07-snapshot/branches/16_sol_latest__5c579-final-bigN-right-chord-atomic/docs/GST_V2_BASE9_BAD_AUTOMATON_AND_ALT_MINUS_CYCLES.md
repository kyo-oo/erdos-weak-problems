<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1103 / 1132
<!--    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/docs/GST_V2_BASE9_BAD_AUTOMATON_AND_ALT_MINUS_CYCLES.md
<!--    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
<!--    First-commit : 2026-08-17 22:06:13 +0530  (deea9a0)
<!--    Last-commit  : 2026-08-17 22:06:13 +0530  (deea9a0)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 22:06:13 +0530  deea9a0  (ker07-dev)
<!--        surgery: lock 5c579 with full BIG-N right-chord research monolith
<!-- ====================================================================== -->

# GST Graph V2 — Base-9 Bad Automaton and Exact ALT− Cycles

## Status

Exact finite-state consequences of the 6²-aligned two-row GST block. This is supporting mathematics, not a claim that the global prefix-one crossing is complete.

---

## 1. Two-row bad-language automaton

Group two ternary digits into one base-nine block

`w = d0 + 3*d1`, with `0 ≤ w < 9`.

For an incoming GST carry `C<4`, define the aligned block mass

`m = C + 4*w`.

The output base-nine block and next carry are

`e = m % 9`,
`C' = m / 9`.

A block is physically Happy if either of its two ternary rows is a Happy Gate.

The complete **physically bad** base-nine input sets are:

- carry `0`: `w ∈ {0,1,3,4,7}`;
- carry `1`: `w ∈ {0,1,2,3,4,5,7}`;
- carry `2`: `w ∈ {0,1,2,3,4,5,7}`;
- carry `3`: `w ∈ {0,1,3,4,6,7}`.

The corresponding next-carry map is obtained from `C'=(C+4w)/9`.

This is exactly the two-row compression of the four-state ternary bad automaton.

---

## 2. One-row regular bad-language recursion

Let `B_C` denote the set of natural ternary words that are completely GST-bad when entered with seed/carry `C`.

The exact one-trit recursion is:

### Seed 0

`B_0 = 3*B_0 ∪ (1 + 3*B_1)`.

Digit `2` is forbidden immediately.

### Seed 1

`B_1 = 3*B_0 ∪ (1 + 3*B_1) ∪ (2 + 3*B_3)`.

### Seed 2

`B_2 = 3*B_0 ∪ (1 + 3*B_2) ∪ (2 + 3*B_3)`.

### Seed 3

`B_3 = 3*B_1 ∪ (1 + 3*B_2)`.

Digit `2` is forbidden immediately.

These equations are exact restatements of the carry table

- `0: 0→0, 1→1, 2→Happy`,
- `1: 0→0, 1→1, 2→3`,
- `2: 0→0, 1→2, 2→3`,
- `3: 0→1, 1→2, 2→Happy`.

They are useful because any proposed global separation theorem can be checked against the actual regular bad language rather than against an invented mirror law.

---

## 3. Proper 7-multiple aligned orbits are CREATE/DESTROY-only

The 6² aligned re-coordinate rotates masses by

`m -> 4m (mod 35)`.

The two proper nonzero 7-multiple cycles are:

### Cycle A

`28 <-> 7`.

The mass-28 state is

`(C,w)=(0,7)`.

Since `7=(21)_3` in ordinary MSD notation, its LSB-first two-row digits are `(1,2)`.

The event sequence is:

- first row: NEITHER;
- second row: DESTROY.

The rotated mass-7 state is

`(C,w)=(3,1)`,

whose LSB-first digits are `(1,0)`.

Its event sequence is:

- first row: NEITHER;
- second row: CREATE.

Therefore

`boxed: (0,7) --rotate--> (3,1) --rotate--> (0,7)`

is an exact **DESTROY ↔ CREATE ALT− cycle with no SURVIVE**.

### Cycle B

`21 <-> 14`.

The mass-21 state is `(1,5)` and contains a DESTROY realization.

The mass-14 state is `(2,3)` and contains a CREATE realization.

Again the orbit alternates CREATE/DESTROY without a SURVIVE realization.

Thus the proper multiples of seven are not just numerically exceptional. They are precisely the two aligned subspace cycles in which BIG2 can alternate between CREATE and DESTROY without ever appearing as SURVIVE.

---

## 4. The fixed maximum mass is SURVIVE

Mass `35` is the fixed state

`(C,w)=(3,8)`.

Here `w=8=(22)_3`, so both ternary rows are digit two and the incoming carry is GST+ (`3`).

Thus the only nonzero multiple of `35` in the legal state interval is itself a fixed **SURVIVE/SURVIVE** state.

This gives the aligned decomposition:

- `m=0`: zero-information NULL state;
- proper `7`-multiples `7,14,21,28`: CREATE/DESTROY-only ALT− cycles;
- `m=35`: fixed SURVIVE state;
- every other nonzero aligned orbit: contains at least one SURVIVE realization.

---

## 5. The canonical c-tower lies exactly in Cycle A

The stable canonical coefficient satisfies

`c_s % 9 = 7`

for every active level `s≥1`.

Therefore its first aligned two-row block, entered from NULL carry zero, is exactly

`(C,w)=(0,7)`,

mass `28`.

So the low c-tower prefix lies in the exact DESTROY side of the aligned ALT− 2-cycle.

Because

`c_s = 1 + 3*z_s`,

stripping its forced first digit `1` exposes the prefix-one offset `z_s`, whose first ternary digit is `2`.

This gives a precise geometric interpretation of the canonical prefix injection:

> the hard prefix-one offset is obtained by cutting into the canonical c-tower while its equal-scale block is sitting in the DESTROY half of the 7-multiple ALT− orbit.

The opposite aligned subspace reading is CREATE.

This is exactly the CREATE/DESTROY dual realization described in PATTERN, now derived from the finite GST arithmetic rather than imposed as a mirror axiom.

---

## 6. Three re-coordinates introduce the bridge factor 6

For the aligned mass map

`m -> 4m mod35`,

three rotations give

`4^3*m = 64m ≡ -6m (mod35)`.

Hence

`F^3(m) ≡ -6m (mod35)`.

A second three-rotation circuit gives

`F^6(m) ≡ 36m ≡ m (mod35)`.

Thus the 6² cell has an exact six-fold alignment cycle, with one three-step half-cycle carrying the explicit bridge factor `-6`.

The half-cycle fixed masses satisfy

`-6m ≡ m (mod35)`,

or equivalently

`7m ≡0 (mod35)`.

Thus the half-cycle fixed sectors are exactly the multiples of `5`.

The all-subspace no-SURVIVE sectors are the proper multiples of `7`.

Their nonzero intersection inside `[0,35]` is only

`m=35`,

which is the fixed SURVIVE state.

This is a sharp algebraic intersection pattern:

- phase-half-cycle alignment selects factor `5`;
- CREATE/DESTROY-only ALT− selects factor `7`;
- simultaneous nonzero alignment selects `5*7=35`, which is SURVIVE.

The missing global theorem must still justify why the canonical physical phase crossing forces the relevant block to satisfy both alignment conditions. The arithmetic intersection itself is exact.

---

## 7. Why this is promising but not yet the comparator closure

The 36-state re-coordinate orbit describes all subspace readings of an equal-scale block. Physical parent badness forbids SURVIVE only in the physical phase-one orientation; it does not automatically forbid a SURVIVE realization in every alternate orientation.

Therefore one may **not** infer `7 | m` merely from physical parent badness.

To finish the proof from this layer, one must derive the missing orientation theorem from the canonical glued surface / renormalization:

- either show that the phase-one `6^k` intersection identifies the physical orientation with the half-cycle aligned orientation;
- or show that indefinite physical avoidance transports the BIG2 packet into the proper 7-multiple cycle and then forces a half-cycle intersection;
- or derive an equivalent recursive statement under `F_s^3(3Y)=3F_(s+1)(Y)`.

Until this orientation step is proved, the factor-5/factor-7 intersection is a powerful exact structure, not the final contradiction.