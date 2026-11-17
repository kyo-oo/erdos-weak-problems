# erdosternary2 — Lean Erdős Ternary-2 Workspace

> **Main base file:** `ErdosTernary2.lean` (401,200 bytes, 0 sorries, 2 errors remained)
> Source: `sol/5c579-final-bigN-right-chord-atomic` branch from `kerokero0/erdos-ternary2-proof`
> Status: `"Erdős Ternary-2 Conjecture: PROVEN"` (file header, line 3)

## Repo structure

```
erdosternary2/
├── ErdosTernary2.lean       ★ MAIN BASE FILE (401 KB, 0 sorries, 2 errors remained)
│                              — pulled from sol/5c579-final-bigN-right-chord-atomic
│                              — chronologically labeled #1133 / 1133
│
├── modules/                 ★ All other Lean modules in CHRONOLOGICAL ORDER
│   ├── README.md            (chronological index of all modules)
│   ├── 0001_*.lean          (earliest module)
│   ├── 0002_*.lean
│   ├── ...
│   └── 0049_*.lean          (latest module)
│
├── ker07-snapshot/          (full reference snapshot, untouched)
│   ├── CHRONOLOGY_INDEX.md  (1132-file chronological index)
│   ├── GIT_HISTORY.md       (per-file detailed commit history)
│   ├── COMPARATOR_RUNS.md   (41 comparator-related commits)
│   ├── PACKAGE_LAYOUT.md
│   ├── (root files from main)
│   └── branches/            (1085 unique files from 19 sol/codex/verify branches)
│
├── lakefile.toml            (kyo-oo's original)
├── lean-toolchain           (kyo-oo's original)
├── Main.lean                (kyo-oo's original entry point)
├── ErdosTernary2/           (kyo-oo's original Lean module directory)
├── scripts/                 (kyo-oo's original scripts)
├── .devcontainer/           (kyo-oo's original)
└── .github/                 (kyo-oo's original)
```

## Main base file — verified properties

| Property | Value |
|---|---|
| Path | `ErdosTernary2.lean` (repo root) |
| Source branch | `origin/sol/5c579-final-bigN-right-chord-atomic` |
| Size | 401,200 bytes |
| Lines | 8,724 |
| SHA256 | `2b370e16f4c5dcc087f581a166bd1eb8a448e5b6b6bc92341100ef34b4f8fa9d` |
| Sorries (real code) | **0** |
| Admits (real code) | 1 |
| Status (line 3) | `"Erdős Ternary-2 Conjecture: PROVEN"` |
| Errors remained | 2 |
| Chronological rank | #1133 / 1133 |

## Chronological label format

Every annotatable file in this repo starts with a chronological label header:

```lean
/- ======================================================================
/- 🌟 CHRONOLOGICAL LABEL — MAIN BASE FILE — #XXXX / 1133
/-    Path         : ErdosTernary2.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : YYYY-MM-DD HH:MM:SS +0530  (sha)
/-    Last-commit  : YYYY-MM-DD HH:MM:SS +0530  (sha)
/-    Total commits: N
/- ======================================================================
/- 0 sorries · 2 errors remained · 'Erdős Ternary-2 Conjecture: PROVEN'
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/N] YYYY-MM-DD HH:MM:SS +0530  sha  (ker07-dev)
/-        commit message
/- ====================================================================== -/
```


## SOL branches — chronological naming

All 16 SOL branches in `ker07-snapshot/branches/` are renamed with chronological time-word descriptors:

| Rank | Time word | Original branch | Tip commit |
|---|---|---|---|
| 01 | `sol_origin` | `origin/sol/engineering-repair-run62` | 2026-08-15 05:12:01 +0530 |
| 02 | `sol_ancient` | `origin/sol/run264-atomic-final` | 2026-08-16 17:05:03 +0530 |
| 03 | `sol_oldest` | `origin/sol/phase-crossing-red-test` | 2026-08-16 14:01:10 +0000 |
| 04 | `sol_older` | `origin/sol/comparator-surgery` | 2026-08-16 20:46:05 +0530 |
| 05 | `sol_old` | `origin/sol/phase-crossing-surgery-2` | 2026-08-17 00:18:29 +0530 |
| 06 | `sol_early` | `origin/sol/phase-crossing-surgery` | 2026-08-17 00:30:42 +0530 |
| 07 | `sol_former` | `origin/sol/right-chord-firepower-base` | 2026-08-17 12:47:10 +0530 |
| 08 | `sol_past` | `origin/sol/physical-phase-crossing-surgery-plan` | 2026-08-17 13:50:53 +0530 |
| 09 | `sol_prior` | `origin/sol/physical-phase-crossing-implementation` | 2026-08-17 13:55:35 +0530 |
| 10 | `sol_historic` | `origin/sol/global-flux-surgery` | 2026-08-17 14:31:15 +0530 |
| 11 | `sol_recent` | `origin/sol/5c579-big1-chord-surgery` | 2026-08-17 21:03:12 +0530 |
| 12 | `sol_present` | `origin/sol/one-error-chord-surgery` | 2026-08-17 21:05:12 +0530 |
| 13 | `sol_current` | `origin/sol/5c579-big1-two-digit-surgery` | 2026-08-17 21:16:02 +0530 |
| 14 | `sol_modern` | `origin/sol/5c579-right-chord-surgery` | 2026-08-17 21:32:57 +0530 |
| 15 | `sol_new` | `origin/sol/physical-phase-crossing-surgery` | 2026-08-17 21:34:52 +0530 |
| 16 | `sol_latest` | `origin/sol/5c579-final-bigN-right-chord-atomic` | 2026-08-18 01:39:21 +0530 |

**Time-word progression:** `origin → ancient → oldest → older → old → early → former → past → prior → historic → recent → present → current → modern → new → latest`

Example: `branches/16_sol_latest__5c579-final-bigN-right-chord-atomic/` is the most recent SOL branch.

See `ker07-snapshot/SOL_BRANCHES_CHRONOLOGY.md` for the full chronological table.
