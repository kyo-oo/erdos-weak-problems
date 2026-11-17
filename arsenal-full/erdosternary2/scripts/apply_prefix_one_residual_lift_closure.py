#!/usr/bin/env python3
from pathlib import Path

MONOLITH = Path('ErdosTernary2.lean')
TARGET = 'theorem gst_prefix_one_information_bad_descends_inline\n'
TARGET_END = '\n/-- Corrected information-wave closure:'
COLLISION_IMPORT = 'import GSTGraphV2PerfectPowerBlockCollision\n'
HELPER_DOC = '/-- Direct modern U2D/perfect-power collision.\n'
TARGET_DOC = '/-- Exact remaining information-descent seam.'

s = MONOLITH.read_text(encoding='utf-8')

# The first-stage normalizer currently injects the unfinished collision helper.
# Remove that transient dependency completely: the replacement below closes the
# seam from the kernel-tested residual navigation theorem instead.
s = s.replace(COLLISION_IMPORT, '')

if HELPER_DOC in s:
    helper_start = s.index(HELPER_DOC)
    target_doc_start = s.find(TARGET_DOC, helper_start)
    if target_doc_start < 0:
        raise SystemExit('target doc-comment not found after transient collision helper')
    s = s[:helper_start] + s[target_doc_start:]

if s.count(TARGET) != 1:
    raise SystemExit(f'expected exactly one target theorem, found {s.count(TARGET)}')

target_start = s.index(TARGET)
end = s.find(TARGET_END, target_start)
if end < 0:
    raise SystemExit('target end marker not found')

replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  -- Omega badness already excludes the exact prefix-one parent witness.
  have hnoParent :
      ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_prefix_one_no_parent_navigation_of_omega_bad_atomic
      s n hs hn hBad

  -- Normalize the natural origin n = 3^r * m with m genuinely 3-free.
  let r : Nat := v3 n
  let m : Nat := n / 3^r
  have hnpos : 0 < n := by omega
  have hdiv : 3^r ∣ n := by
    dsimp [r]
    exact pow_v3_dvd n hnpos
  have hmod : n % 3^r = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hnshape : n = 3^r * m := by
    have hsplit := Nat.mod_add_div n (3^r)
    rw [hmod, Nat.zero_add] at hsplit
    simpa [m] using hsplit.symm
  have hm3 : m % 3 ≠ 0 := by
    dsimp [m, r]
    exact v3_maximal n hnpos
  have hm0 : m ≠ 0 := by
    intro hmzero
    have hnzero : n = 0 := by
      calc
        n = 3^r * m := hnshape
        _ = 0 := by rw [hmzero, Nat.mul_zero]
    omega
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0

  -- Strip the same forced ternary-zero prefix from the certified child gate.
  have hscale :
      gstNavigationConstant (s+1) n =
        3^r * gstNavigationConstant ((s+1)+r) m := by
    rw [hnshape]
    exact gst_navigation_constant_mul3_pow_atomic
      (s+1) r m (by omega)
  have hchildScaled :
      GSTNavigationWitness
        (3^r * gstNavigationConstant ((s+1)+r) m) := by
    rw [← hscale]
    exact hchild
  have hchildNorm0 :
      GSTNavigationWitness (gstNavigationConstant ((s+1)+r) m) :=
    gstNavigationWitness_of_mul_three_pow_atomic
      r (gstNavigationConstant ((s+1)+r) m) hchildScaled
  have hidx : (s+1)+r = s+(r+1) := by omega
  have hchildNorm :
      GSTNavigationWitness (gstNavigationConstant (s+(r+1)) m) := by
    rw [← hidx]
    exact hchildNorm0

  -- Every normalized residual origin is already covered: explicitly closed
  -- origins have their certified witness; every other origin is handled by
  -- the residual Omega termination/navigation lift.
  have hparentNorm :
      GSTNavigationWitness
        (gstNavigationConstant s (1 + 3^(r+1)*m)) := by
    by_cases hclosed : GSTOriginClosed s (r+1) (m % 3)
    · exact gst_navigation_constant_origin_closed_witness
        s (r+1) m (m % 3) hs hm hm3 rfl hclosed
    · exact gst_residual_navigation_lift
        s (r+1) m hs (by omega) hm hm3 hclosed hchildNorm

  have harg : 1 + 3^(r+1)*m = 1 + 3*n := by
    rw [Nat.pow_succ, hnshape]
    ring
  have hparent :
      GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) := by
    rw [← harg]
    exact hparentNorm
  exact hnoParent hparent
'''

s2 = s[:target_start] + replacement + s[end:]

# Structural checks may inspect the transformed monolith. These names would be
# active artifacts introduced by the first-stage collision splice and must be
# gone completely.
for forbidden in (
    'theorem gst_prefix_one_u2d_atomic_collision_inline',
    'GSTGraphV2PerfectPowerBlockCollision.canonical_perfect_power_block_collision',
):
    if forbidden in s2:
        raise SystemExit(f'forbidden active collision dependency survived: {forbidden}')

# Legacy creation names occur inside historical block comments in this large
# monolith. What matters for this surgery is that the NEW live replacement does
# not depend on them; scanning all historical text produced false failures.
for forbidden in (
    'gst_four_power_creation_certificate_inline',
    'gst_h_creation_full_power_navigation_atomic',
    'gst_full_power_navigation_descends_atomic',
):
    if forbidden in replacement:
        raise SystemExit(f'forbidden legacy dependency entered live replacement: {forbidden}')

if COLLISION_IMPORT in s2:
    raise SystemExit('unfinished perfect-power collision import survived')
if s2.count(TARGET) != 1:
    raise SystemExit('target theorem multiplicity changed')
if 'gst_residual_navigation_lift' not in replacement:
    raise SystemExit('residual lift closure did not land')
if 'gstNavigationWitness_of_mul_three_pow_atomic' not in replacement:
    raise SystemExit('3-adic witness normalization did not land')

MONOLITH.write_text(s2, encoding='utf-8')
print('PREFIX_ONE_RESIDUAL_LIFT_CLOSURE=1')
print('COLLISION_HELPER_REMOVED=1')
print('LIVE_LEGACY_H_CREATION_DEPENDENCY=0')
