# THE DUST-TREE CENSUS + DEEP-RIDER SCAN (S074 session record)

## The survivor dust tree (the feedback tree of GSTTheActConstruction)

Built level by level: alive[0] = {0}; alive[j+1] = {r + t*3^j : r in
alive[j], t in {0,1,2}, (noise_j(r) + t) % 3 != 2} where noise_j(r) =
digit3(4^r, j+1) (computed via pow(4, r, 3^(j+2))).

| level j | modulus 3^j | |alive[j]| |
|---|---|---|
| 1..12 | 3..531441 | 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096 |

EXACT DOUBLING at every level (machine-verified; matches the repo's
`unique_dead_child` law: every node owns exactly one dead child).
The witnesses 0, 1, 4 are alive at every level, as they must be.

## The deep census (K in [0, 200000])

Riders found: {0, 1, 4} — no counterexample. (Extends the repo's
[8, 5000] climb-truth scan and the [0, 250] kernel census forty-fold.)

## The death-depth distribution (the 1015 level-13 survivors below 200000)

depth 13: 333 K's | depth 14: 225 | 15: 159 | 16: 103 | 17: 59 | 18: 45
| 19: 30 | 20: 19 | 21: 13 | 22: 10 | 23: 4 | 24: 2 | 25: 3 | 26: 2
| 27: 1 | 28: 1 | 30: 1 | 31: 1 | 35: 1 (K = 124984) | full: 3 (0, 1, 4)

The depth grows only logarithmically — the extreme-value scale of the
Cantor (2/3)-per-level decay.  No structure suggests infinite survival.
