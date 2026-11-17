#!/usr/bin/env python3
from pathlib import Path

PATH = Path('ErdosTernary2.lean')
START = '/- QUARANTINED LEGACY RESIDUAL OMEGA START'
END = 'QUARANTINED LEGACY RESIDUAL OMEGA END -/'
ACTIVE_START = '-- REACTIVATED RESIDUAL OMEGA START'
ACTIVE_END = '-- REACTIVATED RESIDUAL OMEGA END'

s = PATH.read_text(encoding='utf-8')

if s.count(START) != 1:
    raise SystemExit(f'expected exactly one residual Omega quarantine start, found {s.count(START)}')
if s.count(END) != 1:
    raise SystemExit(f'expected exactly one residual Omega quarantine end, found {s.count(END)}')

s = s.replace(START, ACTIVE_START, 1)
s = s.replace(END, ACTIVE_END, 1)

if START in s or END in s:
    raise SystemExit('residual Omega quarantine marker survived reactivation')

# `gst_omega` is defined in GSTTactic before the monolith-local Omega
# declarations exist. Its quoted simplifier identifiers therefore become
# hygienic dead names at these three old call sites. Elaborate the identical
# simplifier explicitly here, where the declarations are actually in scope.
start = s.index(ACTIVE_START)
end = s.index(ACTIVE_END, start)
block = s[start:end]
old = '  gst_omega\n'
if block.count(old) != 3:
    raise SystemExit(f'expected exactly three residual gst_omega calls, found {block.count(old)}')
explicit = '''  simp_all (config := { maxSteps := 1000000 }) only [\n    GSTResidualBoundary, GSTOmegaChildZeroSet, GSTOmegaBadSet,\n    GSTOmegaBadBlock, GSTSeededAffineBadTrace, Set.mem_setOf_eq]\n  <;> first | contradiction | omega\n'''
block = block.replace(old, explicit)
s = s[:start] + block + s[end:]

# The point of this probe is to expose the actual theorem to Lean, not merely
# make its name visible in commented source.
needle = 'theorem gst_residual_navigation_lift : GSTResidualNavigationLift :='
if s.count(needle) != 1:
    raise SystemExit(f'expected exactly one residual navigation theorem after reactivation, found {s.count(needle)}')
if '  gst_omega\n' in block:
    raise SystemExit('residual gst_omega call survived theorem-site elaboration surgery')

PATH.write_text(s, encoding='utf-8')
print('RESIDUAL_OMEGA_REACTIVATED=1')
print('RESIDUAL_OMEGA_THEOREM_SITE_SIMPLIFIERS=3')
