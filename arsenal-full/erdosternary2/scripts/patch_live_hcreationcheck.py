#!/usr/bin/env python3
from pathlib import Path
import textwrap

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

creation_marker = 'theorem gst_four_power_creation_certificate_inline'
next_marker = '\ntheorem mul4_lift_gst_duality'
helper_marker = 'theorem gst_h_creation_full_power_navigation_atomic'
helper_next = 'theorem gst_full_power_navigation_descends_atomic'
live_stamp = '-- SOL56 LIVE GENERAL H_CREATION REACTIVATED\n'

helper_start = s.index(helper_marker)
helper_end = s.index(helper_next, helper_start)
helper = s[helper_start:helper_end]
required_call = 'gst_four_power_creation_certificate_inline k hk5 hk7'
if required_call not in helper:
    raise SystemExit('atomic adapter call changed')

# Extract the quarantined theorem body, but install a genuinely new declaration
# whose recursion is owned by Nat.strongRecOn.  Applying hk5/hk7 outside the
# recursor avoids the former accidental P -> P result.
qstart = s.index(creation_marker)
qend = s.index(next_marker, qstart)
source_decl = s[qstart:qend].rstrip() + '\n'
proof_anchor = ':= by\n'
head, body = source_decl.split(proof_anchor, 1)
recursive_old = '    have hih := gst_four_power_creation_certificate_inline (k - 1) hk1 hk1_7\n'
recursive_new = '    have hih := ih (k - 1) (by omega) hk1 hk1_7\n'
if recursive_old not in body:
    raise SystemExit('quarantined recursive call shape changed')
body = body.replace(recursive_old, recursive_new, 1)

motive = '''5 ≤ k → k ≠ 7 →
      ∃ p, 1 ≤ p ∧
        4 ^ k / 3 ^ p % 3 = 2 ∧
        (4 * (4 ^ k % 3 ^ p) / 3 ^ p % 3 = 0 ∨
          4 * (4 ^ k % 3 ^ p) / 3 ^ p % 3 = 1 ∧
          4 ^ k / 3 ^ (p + 1) % 3 = 2)'''
live_decl = (
    head + proof_anchor +
    '  exact (Nat.strongRecOn (motive := fun k =>\n'
    '    ' + motive.replace('\n', '\n    ') + ') k (by\n'
    '    intro k ih hk5 hk7\n' +
    textwrap.indent(body, '  ') +
    '  )) hk5 hk7\n\n'
)

if live_stamp in s:
    stamp_at = s.index(live_stamp)
    live_start = stamp_at + len(live_stamp)
    if s.startswith(creation_marker, live_start):
        old_live_end = s.index(helper_marker, live_start)
        s = s[:live_start] + live_decl + s[old_live_end:]
    else:
        s = s[:live_start] + live_decl + s[live_start:]
else:
    s = s[:helper_start] + live_stamp + live_decl + s[helper_start:]

helper_start = s.index(helper_marker, s.index(live_stamp))
helper_end = s.index(helper_next, helper_start)
helper_old = '''    have hnext := gstCarry_forward_exact (4^k) p hp1
    rw [hC, hd] at hnext
    norm_num [gstStepCarry] at hnext
'''
helper_new = '''    have hnext := gstCarry_forward_exact (4^k) p hp1
    have hdDigit : gstDigit (4^k) p = 2 := by
      simpa [gstDigit] using hd
    rw [hC, hdDigit] at hnext
    norm_num [gstStepCarry] at hnext
'''
live_helper = s[helper_start:helper_end]
if helper_old in live_helper:
    s = s[:helper_start] + live_helper.replace(helper_old, helper_new, 1) + s[helper_end:]
elif 'rw [hC, hdDigit] at hnext' not in live_helper:
    raise SystemExit('atomic carry-one adapter rewrite shape changed')

live_start = s.index(live_stamp) + len(live_stamp)
live_helper = s.index(helper_marker, live_start)
live_slice = s[live_start:live_helper]
if live_slice.count(creation_marker) != 1:
    raise SystemExit('expected exactly one live creation theorem')
if 'Nat.strongRecOn (motive := fun k =>' not in live_slice:
    raise SystemExit('new strong-recursion theorem missing')
if 'have hih := ih (k - 1) (by omega) hk1 hk1_7' not in live_slice:
    raise SystemExit('recursive call was not redirected to induction hypothesis')
if required_call not in s[live_helper:s.index(helper_next, live_helper)]:
    raise SystemExit('atomic adapter lost the live theorem call')

p.write_text(s, encoding='utf-8')
print('NEW_FULL_H_CREATION_STRONG_RECURSION_INSTALLED=1')
print('FORMER_P_TO_P_WRAPPER_REMOVED=1')
print('GSTDIGIT_RC2_REPAIR=1')
print('UNBOUNDED_U2D_CREATION_ADAPTER_PRESERVED=1')
