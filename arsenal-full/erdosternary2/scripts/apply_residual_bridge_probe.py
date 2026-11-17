#!/usr/bin/env python3
from pathlib import Path
import re

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

start = s.find('theorem gst_prefix_one_information_bad_descends_inline\n')
if start < 0:
    raise SystemExit('target theorem start not found')
end_marker = '\n/-- Corrected information-wave closure:'
end = s.find(end_marker, start)
if end < 0:
    raise SystemExit('target theorem end marker not found')

replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  -- Direct Aug-23 whole-theorem transplant.  This deliberately replaces the
  -- later residual classifier/probe split rather than extending it.
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

  have hfuture0 : T / 3^T = 0 := by
    simpa [T] using gst_prefix_one_bigN_future_zero_inline s n hs

  -- Single remaining post-transplant seam.  Keep the exact recovered context
  -- intact so the compiler exposes only the final consumer mismatch.
  trace_state
  contradiction
'''

s2 = s[:start] + replacement + s[end:]
p.write_text(s2, encoding='utf-8')

lines = s2.splitlines()
print(f'WHOLE_THEOREM_TRANSPLANT lines={len(lines)}')
for i, line in enumerate(lines, 1):
    if 'theorem gst_prefix_one_information_bad_descends_inline' in line:
        print(f'WHOLE_THEOREM_TRANSPLANT target_start={i}')
    if 'Single remaining post-transplant seam.' in line:
        print(f'WHOLE_THEOREM_TRANSPLANT red_frontier={i}')
if re.search(r'(?m)^\s*gst_end\s*$', s2):
    raise SystemExit('gst_end survived whole-theorem transplant')
print('installed recovered Aug23 whole-theorem transplant')
