# CAP-LAW FRONT ARTIFACTS (S074, W75)

Sealed: 2026-11-19 · Branch: `campaign` · Front: `problem406-ternary-powers/CapLaw406.lean` (Kernel 68)

## What is in this folder

```
caplaw/
├── MANIFEST.md            ← this file
├── battery_caplaw.py      ← the dual-method engine battery (CI-run, Kernel 68)
├── v2star_table.json      ← the exact extremal 2-adic curve v2*(M), M=0..34
└── dust_census.md         ← the dust-tree census + deep-rider scan record
```

## The extremal 2-adic curve (the cap law's empirical backbone)

`v2*(M) := max{ v2(Σ_{i∈S} 3^i) : ∅ ≠ S ⊆ [0, M] }` — computed by two
independent methods: exhaustive subset enumeration (M ≤ 21) and
meet-in-the-middle on residues mod 2^64 with nonempty-flag tracking
(M = 22..34).  The kill line is `2K vs M = ⌊log₃ 4^K⌋`, i.e. the ratio
`2/log₃4 = 1.58496...`; a rider needs `v2*(M) ≥ 1.5849·M − 1`.

The verdict (full table in `v2star_table.json`): the ONLY line-touchers
in all computed history are the actual witnesses — `{0,1}` at M=1
(v2 = 2, sum 4 = 2²) and `{0,1,2,5}` at M=5 (v2 = 8, sum 256 = 2⁸).
From M=6 onward the margin grows: at M=34 the extremal v2* = 35 sits
THIRTY below the kill line 53.9.  The cap `v2* ≤ M + 4` holds
throughout [0, 34], with the excess peaking at +4 (M=31), +3 (M=5, 32),
+2 (M=14, 23, 27).

The jump-point extremal sets (verified by hand):
- M=1:  S = {0,1} → 1+3 = 4 = 2²·1
- M=5:  S = {0,1,2,5} → 1+3+9+243 = 256 = 2⁸·1
- M=14: S = {0,3,5,9,10,11,12,14} → 271 + 3⁹·283 = 5570560 = 2¹⁶·85
  (the MITM-block construction: a low block A and a shifted block B with
  Σ(A) ≡ −3⁹·Σ(B) mod 2¹⁶ exactly — the extremals are meet-in-the-middle
  solutions, NOT self-similar substitutions; shifts preserve neither the
  excess nor the value, so no infinite ascent is known)

## The dust-tree census (this session)

- Survivor tree doubling: |alive[j]| = 2^j verified exactly for j ≤ 12
  (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096 classes mod 3^j).
- Deep census K ∈ [0, 200000]: riders = {0, 1, 4} (divmod first-2 scan).
- Death-depth distribution of the 1015 level-13 survivors below 200000:
  max death depth 35 (K = 124984) — the depth grows only logarithmically,
  exactly the Cantor heuristic (2/3 per level decay).

## The retargeting doctrine (the strategic content)

The source monolith's POSTULATE II (C = 3) is certified only below 3⁹
(monolith receipt) and below 3²¹ (the Strategist's independent census,
this session); the universal case is the monolith's stalled seam.  The
Kernel-68 reduction (`erdos406_no_riders_above_250_of_cap`) shows the
campaign needs only C ≤ 185 — SIXTY TIMES weaker — because
62·250 = 15500 < 15540 = 84·185 < 15562 = 62·251: the weak cap lands
exactly inside the Kernel-38 census range.  Any provable explicit cap
constant C ≤ 185 closes Erdős #406 outright through the composition
theorem `erdos406_classification_of_cap_and_census`.
