#!/usr/bin/env python3
from pathlib import Path
import re

MONOLITH = Path('ErdosTernary2.lean')
MIN_MONOLITH_BYTES = 300_000
TARGET = 'theorem gst_prefix_one_information_bad_descends_inline\n'
TARGET_END = '\n/-- Corrected information-wave closure:'

s = MONOLITH.read_text(encoding='utf-8')
original_bytes = len(s.encode('utf-8'))
if original_bytes < MIN_MONOLITH_BYTES:
    raise SystemExit(
        f'refusing seam surgery into truncated ErdosTernary2.lean: {original_bytes} bytes'
    )
if s.count(TARGET) != 1:
    raise SystemExit(f'expected exactly one production theorem start, found {s.count(TARGET)}')

packet_marker_re = re.compile(r'(?m)^-- (?:BEGIN|END) ATTACHED [^\n]+$')
packet_markers_before = packet_marker_re.findall(s)

start = s.index(TARGET)
end = s.find(TARGET_END, start)
if end < 0:
    raise SystemExit('production theorem end marker not found')

replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  -- BEGIN SOL56 FINAL ATOMIC SEAM SURGERY
  let T : Nat := gstNavigationConstant (s+1) n
  let A : Nat := 4^(3^s)
  let z : Nat := gstCanonicalPrefixOffsetS s
  let H : Nat := z + A*T

  have hchildT : GSTNavigationWitness T := by
    simpa [T] using hchild

  have hparent : GSTSeededBadTraceS 1 H := by
    intro j
    have hj := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad j
    simpa [H, T, A, z, gstPrefixOneUPotentialTailS,
      gstCanonicalPrefixOffsetS] using hj

  have hchildGate : ∃ q, GSTSeededHappyS 0 T q := by
    obtain ⟨q, hd, hspace⟩ := hchildT
    have hmod : gstCarry T q % 3 = 0 :=
      gstGoodSpace_carry_mod3_zero T q hspace
    have hlt : gstCarry T q < 4 := by
      simpa [gstCarry, gstAffineMulCarryS] using
        (gst_affine_carry_lt_multiplierS 4 0 T q (by decide) (by decide))
    have hcarry : gstCarry T q = 0 ∨ gstCarry T q = 3 := by
      omega
    refine ⟨q, ?_⟩
    constructor
    · simpa [T, gstDigitS, gstDigit] using hd
    · simpa [T, gstAffineMulCarryS, gstCarry] using hcarry

  have hApos : 0 < A := by
    dsimp [A]
    positivity

  have hAunit :
      A = 1 + 3^(s+1) * gstNavigationConstant s 1 := by
    dsimp [A]
    simpa using (gst_navigation_decomposition s 1 hs)

  have hunitPrefix :
      gstNavigationConstant s 1 = 1 + 3*z := by
    simpa [z] using gst_navigation_constant_unit_prefixS s hs

  have hz1 : 1 + 4*z < A := by
    have hD9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    rw [hAunit, hunitPrefix]
    nlinarith

  have htrap : GSTCanonicalRightChordTrapS A z T :=
    gst_canonical_right_chord_trapS A z T hApos hz1 hparent hchildGate

  obtain ⟨q, hgate, hparentSuffix, hchildSuffix, hC,
    hlocal, hclass3, hclass2, hshared, hW⟩ := htrap

  let D : Nat := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
  let Z : Nat := gstAffineMulCarryS A z T (q+1)
  let W : Nat := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
  let C : Nat := gstAffineMulCarryS 4 0 T (q+1)
  let Y : Nat := T / 3^(q+1)

  have hparentSuffix' : GSTSeededBadTraceS D (Z + A*Y) := by
    simpa [D, Z, Y] using hparentSuffix
  have hchildSuffix' : GSTSeededBadTraceS C Y := by
    simpa [C, Y] using hchildSuffix
  have hC' : C = 2 ∨ C = 3 := by
    simpa [C] using hC
  have hshared' : D + 4*Z = W + A*C := by
    simpa [D, Z, W, C] using hshared
  have hW' : W < A := by
    simpa [W] using hW

  have hDlt : D < 4 := by
    dsimp [D]
    exact gst_affine_carry_lt_multiplierS 4 1 (z + A*T) (q+1)
      (by decide) (by decide)

  obtain ⟨a, b, e, Wmid, hDb, hCe, ha, hb, he, hWmid,
      hmid, hlow⟩ :=
    gst_shared_x4_binary_factor_last_gate_high_bitS
      A D Z W C hApos hDlt hC' hW' hshared'

  -- Exact all-Nat RED frontier: no finite-support/future-zero hypothesis.
  trace_state
  contradiction
  -- END SOL56 FINAL ATOMIC SEAM SURGERY
'''

s2 = s[:start] + replacement + s[end:]

if s2[:start] != s[:start]:
    raise SystemExit('prefix outside target theorem changed')
new_end = s2.find(TARGET_END, start)
if new_end < 0 or s2[new_end:] != s[end:]:
    raise SystemExit('suffix outside target theorem changed')
if s2.count(TARGET) != 1:
    raise SystemExit('post-surgery theorem multiplicity check failed')
if re.search(r'(?m)^\s*gst_end\s*$', s2):
    raise SystemExit('gst_end survived final theorem surgery')
if packet_marker_re.findall(s2) != packet_markers_before:
    raise SystemExit('historical attached-packet structure changed; refusing non-atomic surgery')

region = s2[start:new_end]
for forbidden in (
    'gst_four_power_creation_certificate_inline',
    'gst_residual_navigation_lift',
    'canonical_perfect_power_block_collision',
    'let r := v3 n',
    'have hboundary : GSTResidualBoundary',
    'have hResidualBad : GSTOmegaInfiniteBadTrace s k m',
    'gst_prefix_one_bigN_future_zero_inline',
):
    if forbidden in region:
        raise SystemExit(f'forbidden legacy path survived target theorem: {forbidden}')

MONOLITH.write_text(s2, encoding='utf-8')
written = MONOLITH.read_text(encoding='utf-8')
if written != s2:
    raise SystemExit('post-write monolith integrity check failed')

print(f'ATOMIC_INPUT_BYTES={original_bytes}')
print(f'ATOMIC_OUTPUT_BYTES={len(written.encode("utf-8"))}')
print(f'ATOMIC_CHANGED_REGION_BYTES={len(replacement.encode("utf-8"))}')
print(f'ATOMIC_BASELINE_PACKET_MARKERS={len(packet_markers_before)}')
for i, line in enumerate(written.splitlines(), 1):
    if 'theorem gst_prefix_one_information_bad_descends_inline' in line:
        print(f'ATOMIC_TARGET_START={i}')
    if 'Exact all-Nat RED frontier' in line:
        print(f'ATOMIC_RED_FRONTIER={i}')
print('ATOMIC_SURGERY=ONE_THEOREM_ONLY')