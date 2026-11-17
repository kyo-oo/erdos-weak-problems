<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0005 / 1132
<!--    Path         : README.md
<!--    Ref          : main
<!--    First-commit : 2026-08-14 14:07:06 +0530  (0c7bf9b)
<!--    Last-commit  : 2026-08-14 14:35:23 +0530  (d235c2b)
<!--    Total commits: 2
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/2] 2026-08-14 14:07:06 +0530  0c7bf9b  (ker07-dev)
<!--        chore: add README.md
<!-- [02/2] 2026-08-14 14:35:23 +0530  d235c2b  (ker07-dev)
<!--        fix: replace placeholder README with GST comparator workspace
<!-- ====================================================================== -->

# Erdős Ternary-2 — GST Ω∞ comparator workspace

Private Lean workspace for the Erdős ternary-2 formalization and its comparator audit.

## Mathematical architecture

The source basis is the completed GST Ω∞ paradox/mirror separation:

```text
exact GST transition
→ CREATE / DESTROY / SURVIVE / NEITHER
→ mirror: CREATE ↔ DESTROY, SURVIVE ↔ SURVIVE
→ ACTIVE + mirror-fixed ↔ SURVIVE
→ SURVIVE ↔ Happy Gate
→ canonical Ω∞ paradox/mirror recurrence
→ active mirror-fixed intersection
→ Happy Gate / Navigation
→ existing perfect-power downstream chain
→ erdos_ternary_2_universal
```

The complete recovered derivation is preserved under `docs/`.

## Comparator

```bash
bash scripts/setup-comparator.sh
bash scripts/audit.sh
bash scripts/run-comparator.sh
```

`comparator_config.json` permits only:

- `propext`
- `Quot.sound`
- `Classical.choice`

and checks theorem `erdos_ternary_2` from `Challenge` against `Solution`.

## Workbench

`workbench/` contains the compiler-green Sol Ω/event/transfer modules and monolithic integration artifacts used for the final source transplant.
