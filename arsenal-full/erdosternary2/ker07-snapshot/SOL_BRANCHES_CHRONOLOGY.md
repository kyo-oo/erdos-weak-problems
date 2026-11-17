# SOL Branches — Chronological Naming

Generated: 2026-08-18T00:16:09+00:00

All 16 SOL branches from the ker07-dev repository, sorted by their
**tip commit date** (most recent commit on each branch) and renamed
with time-based descriptors in strict chronological order.

## Naming format

```
NN_sol_<time_word>__<original-branch-name>/
```

Where:
- `NN` — chronological rank (01 = earliest, 16 = latest)
- `sol_<time_word>` — time descriptor (origin → ancient → oldest → older →
  old → early → former → past → prior → historic → recent → present →
  current → modern → new → latest)
- `<original-branch-name>` — preserved for traceability

## Chronological ranking

| Rank | Time Word | Tip Date (IST/+05:30) | Original Branch | Total Commits | Unique Commits | Tip Message |
|---|---|---|---|---|---|---|
| 01 | sol_origin | 2026-08-15 05:12:01 +0530 | `origin/sol/engineering-repair-run62` | 104 | 51 | Harden CI source integrity before Lean builds |
| 02 | sol_ancient | 2026-08-16 17:05:03 +0530 | `origin/sol/run264-atomic-final` | 298 | 245 | Rerun comparator after atomic integration syntax fix |
| 03 | sol_oldest | 2026-08-16 14:01:10 +0000 | `origin/sol/phase-crossing-red-test` | 306 | 253 | Fix monolithic carry normalization and residual lift call |
| 04 | sol_older | 2026-08-16 20:46:05 +0530 | `origin/sol/comparator-surgery` | 325 | 272 | Export corrupt bridge notes for exact inspection |
| 05 | sol_old | 2026-08-17 00:18:29 +0530 | `origin/sol/phase-crossing-surgery-2` | 308 | 255 | Add isolated RED harness for phase crossing surgery |
| 06 | sol_early | 2026-08-17 00:30:42 +0530 | `origin/sol/phase-crossing-surgery` | 316 | 263 | Compile canonical trap reduction before crossing RED |
| 07 | sol_former | 2026-08-17 12:47:10 +0530 | `origin/sol/right-chord-firepower-base` | 392 | 339 | Record pathwise BIG1 projector grand-chord experiment |
| 08 | sol_past | 2026-08-17 13:50:53 +0530 | `origin/sol/physical-phase-crossing-surgery-plan` | 393 | 340 | docs: lock prefix-one phase crossing surgery design |
| 09 | sol_prior | 2026-08-17 13:55:35 +0530 | `origin/sol/physical-phase-crossing-implementation` | 394 | 341 | docs: add prefix-one phase crossing implementation plan |
| 10 | sol_historic | 2026-08-17 14:31:15 +0530 | `origin/sol/global-flux-surgery` | 402 | 349 | Compile exact historical seam reduction |
| 11 | sol_recent | 2026-08-17 21:03:12 +0530 | `origin/sol/5c579-big1-chord-surgery` | 314 | 261 | Tighten BIG1 chord surgery binding contract |
| 12 | sol_present | 2026-08-17 21:05:12 +0530 | `origin/sol/one-error-chord-surgery` | 313 | 260 | test: pin prefix-one child-gate survive closure |
| 13 | sol_current | 2026-08-17 21:16:02 +0530 | `origin/sol/5c579-big1-two-digit-surgery` | 316 | 263 | Begin 5c579 prefix-one two-digit chord surgery |
| 14 | sol_modern | 2026-08-17 21:32:57 +0530 | `origin/sol/5c579-right-chord-surgery` | 406 | 353 | Attach scoped two-digit right chord to historical Omega chil |
| 15 | sol_new | 2026-08-17 21:34:52 +0530 | `origin/sol/physical-phase-crossing-surgery` | 396 | 343 | Add physical scoped two-digit 22/35 contradiction |
| 16 | sol_latest | 2026-08-18 01:39:21 +0530 | `origin/sol/5c579-final-bigN-right-chord-atomic` | 317 | 264 | surgery: force ordinary origin trits from canonical parent b |

## Time-word progression (oldest → latest)

| # | Time Word | Meaning |
|---|---|---|
| 01 | origin | the very beginning of SOL work |
| 02 | ancient | very early exploratory work |
| 03 | oldest | early phase |
| 04 | older | maturing early work |
| 05 | old | established early work |
| 06 | early | early-to-middle period |
| 07 | former | previous iteration |
| 08 | past | past work, somewhat dated |
| 09 | prior | predecessor to current |
| 10 | historic | historically significant |
| 11 | recent | recent past |
| 12 | present | current iteration |
| 13 | current | active current work |
| 14 | modern | modern approach |
| 15 | new | newest iteration |
| 16 | latest | the most recent (tip) |

## Directory mapping

| Old Directory | → | New Directory |
|---|---|---|
| `branches/sol_engineering-repair-run62/` | → | `branches/01_sol_origin__engineering-repair-run62/` |
| `branches/sol_run264-atomic-final/` | → | `branches/02_sol_ancient__run264-atomic-final/` |
| `branches/sol_phase-crossing-red-test/` | → | `branches/03_sol_oldest__phase-crossing-red-test/` |
| `branches/sol_comparator-surgery/` | → | `branches/04_sol_older__comparator-surgery/` |
| `branches/sol_phase-crossing-surgery-2/` | → | `branches/05_sol_old__phase-crossing-surgery-2/` |
| `branches/sol_phase-crossing-surgery/` | → | `branches/06_sol_early__phase-crossing-surgery/` |
| `branches/sol_right-chord-firepower-base/` | → | `branches/07_sol_former__right-chord-firepower-base/` |
| `branches/sol_physical-phase-crossing-surgery-plan/` | → | `branches/08_sol_past__physical-phase-crossing-surgery-plan/` |
| `branches/sol_physical-phase-crossing-implementation/` | → | `branches/09_sol_prior__physical-phase-crossing-implementation/` |
| `branches/sol_global-flux-surgery/` | → | `branches/10_sol_historic__global-flux-surgery/` |
| `branches/sol_5c579-big1-chord-surgery/` | → | `branches/11_sol_recent__5c579-big1-chord-surgery/` |
| `branches/sol_one-error-chord-surgery/` | → | `branches/12_sol_present__one-error-chord-surgery/` |
| `branches/sol_5c579-big1-two-digit-surgery/` | → | `branches/13_sol_current__5c579-big1-two-digit-surgery/` |
| `branches/sol_5c579-right-chord-surgery/` | → | `branches/14_sol_modern__5c579-right-chord-surgery/` |
| `branches/sol_physical-phase-crossing-surgery/` | → | `branches/15_sol_new__physical-phase-crossing-surgery/` |
| `branches/sol_5c579-final-bigN-right-chord-atomic/` | → | `branches/16_sol_latest__5c579-final-bigN-right-chord-atomic/` |

## Files inside each branch directory

Each branch directory contains the files UNIQUE to that branch (i.e., not on `main`).
All `.lean` files retain their CHRONOLOGICAL LABEL header with `[ref: origin/sol/<branch-name>]`
(the original git ref, for traceability).

Total branch-unique files across all 16 SOL branches: see CHRONOLOGY_INDEX.md