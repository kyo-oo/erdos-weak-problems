#!/usr/bin/env python3
from pathlib import Path
import re

MONOLITH = Path('ErdosTernary2.lean')
MIN_MONOLITH_BYTES = 300_000
TARGET = 'theorem gst_prefix_one_information_bad_descends_inline\n'
TARGET_END = '\n/-- Corrected information-wave closure:'
INFINITE_IMPORT = 'import GSTGraphV2InfiniteControl\n'
CORE_IMPORT = 'import GSTNavigationCore\n'
COLLISION_IMPORT = 'import GSTGraphV2PerfectPowerBlockCollision\n'
STALE_UNUSED_IMPORTS = (
    'import GSTPrefixOnePhaseIncidenceControl\n',
    'import GSTPrefixOneSpacetimeIncidenceControl\n',
)

# After direct attached-module imports are removed, these five packets are
# still supplied transitively by the surviving production imports. The live
# compiler proved they are duplicate-declaration owners. Keep the imported
# compiled copies and remove only their redundant inline packets.
TRANSITIVE_ATTACHED_DUPLICATES = (
    'OriginTransducerScratch',
    'PurePowerCarrierScratch',
    'CanonicalPrefixScratch',
    'InformationDescentScratch',
    'CanonicalOriginModulusScratch',
)

# These six declarations are now owned by GSTNavigationCore so standalone
# Graph-V2 modules and the monolith share the same concrete Navigation objects.
CORE_DECLARATIONS = (
    '''inductive GSTSpace where
  | gstPlus
  | altMinus
  | null
  deriving DecidableEq, Repr
''',
    '''def gstCarry (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p
''',
    '''def gstDigit (R p : Nat) : Nat := R / 3^p % 3
''',
    '''def gstSpaceAt (R p : Nat) : GSTSpace :=
  if gstCarry R p = 0 then .null
  else if gstCarry R p = 3 then .gstPlus
  else .altMinus
''',
    '''def gstNavigationConstant (s b : Nat) : Nat :=
  4^(3^s * b) / 3^(s+1)
''',
    '''def GSTNavigationWitness (R : Nat) : Prop :=
  ∃ j, gstDigit R j = 2 ∧
    (gstSpaceAt R j = .gstPlus ∨ gstSpaceAt R j = .null)
''',
)


def remove_decl_with_immediate_doc(source: str, declaration: str) -> str:
    count = source.count(declaration)
    if count != 1:
        first_line = declaration.splitlines()[0]
        raise SystemExit(
            f'expected exactly one monolith core declaration {first_line!r}, found {count}'
        )
    decl_start = source.index(declaration)
    decl_end = decl_start + len(declaration)
    prefix = source[:decl_start]
    doc_start = prefix.rfind('/--')
    if doc_start < 0:
        raise SystemExit(f'missing doc-comment before {declaration.splitlines()[0]!r}')
    doc_end = prefix.find('-/', doc_start)
    if doc_end < 0 or prefix[doc_end + 2:].strip():
        raise SystemExit(
            f'core declaration does not have one immediate doc-comment: {declaration.splitlines()[0]!r}'
        )
    return source[:doc_start] + source[decl_end:]


def remove_attached_packet(source: str, module: str) -> str:
    begin = f'-- BEGIN ATTACHED {module}.lean\n'
    end_marker = f'-- END ATTACHED {module}.lean'
    if source.count(begin) != 1 or source.count(end_marker) != 1:
        raise SystemExit(
            f'expected exactly one attached packet for {module}: '
            f'begin={source.count(begin)} end={source.count(end_marker)}'
        )
    start = source.index(begin)
    end = source.index(end_marker, start) + len(end_marker)
    if end < len(source) and source[end] == '\n':
        end += 1
    return source[:start] + source[end:]


s = MONOLITH.read_text(encoding='utf-8')
original_bytes = len(s.encode('utf-8'))
if original_bytes < MIN_MONOLITH_BYTES:
    raise SystemExit(
        f'refusing seam surgery into truncated ErdosTernary2.lean: {original_bytes} bytes'
    )

anchor = 'import Mathlib.Tactic.Ring\n'
if anchor not in s:
    raise SystemExit('import anchor not found')
for required_import in (INFINITE_IMPORT, CORE_IMPORT, COLLISION_IMPORT):
    if required_import not in s:
        s = s.replace(anchor, anchor + required_import, 1)

# These two detached incidence imports pull circular historical packages into
# the transient build but are unused by the live prefix-one seam.
removed_stale_imports = 0
for stale_import in STALE_UNUSED_IMPORTS:
    count = s.count(stale_import)
    if count != 1:
        raise SystemExit(
            f'expected exactly one stale incidence import {stale_import.strip()!r}, found {count}'
        )
    s = s.replace(stale_import, '', 1)
    removed_stale_imports += 1

# Remove direct imports that duplicate literal BEGIN/END ATTACHED packets.
attached_modules = sorted(set(re.findall(
    r'(?m)^-- BEGIN ATTACHED ([A-Za-z_][A-Za-z0-9_]*)\.lean\s*$', s
)))
removed_attached_imports = 0
removed_attached_modules = []
for module in attached_modules:
    import_line = f'import {module}\n'
    count = s.count(import_line)
    if count:
        s = s.replace(import_line, '')
        removed_attached_imports += count
        removed_attached_modules.append(module)

# These compiled modules remain transitively imported, so delete only their
# redundant inline packets. This also removes the obsolete active
# gst_four_power_creation_certificate_inline copy instead of resurrecting it.
removed_transitive_packets = 0
for module in TRANSITIVE_ATTACHED_DUPLICATES:
    s = remove_attached_packet(s, module)
    removed_transitive_packets += 1

removed_core_declarations = 0
for declaration in CORE_DECLARATIONS:
    s = remove_decl_with_immediate_doc(s, declaration)
    removed_core_declarations += 1

if s.count(TARGET) != 1:
    raise SystemExit(f'expected exactly one production theorem start, found {s.count(TARGET)}')
if 'theorem gst_prefix_one_u2d_atomic_collision_inline' in s:
    raise SystemExit('U2D collision helper already exists before atomic transplant')

packet_marker_re = re.compile(r'(?m)^-- (?:BEGIN|END) ATTACHED [^\n]+$')
packet_markers_before = packet_marker_re.findall(s)

target_start = s.index(TARGET)
end = s.find(TARGET_END, target_start)
if end < 0:
    raise SystemExit('production theorem end marker not found')

# Preserve the public target's existing doc-comment with the target itself.
prefix = s[:target_start]
target_doc_start = prefix.rfind('/--')
if target_doc_start < 0:
    raise SystemExit('target theorem doc-comment not found')
target_doc_end = prefix.find('-/', target_doc_start)
if target_doc_end < 0 or prefix[target_doc_end + 2:].strip():
    raise SystemExit('target theorem does not have one immediate doc-comment')
target_doc = s[target_doc_start:target_start]

# Modern direct U2D collision.  The certified child Navigation witness is
# projected to a literal Happy cell on the left side of the canonical
# perfect-power block.  The Omega bad trace gives an all-depth bad right side.
# The already-green perfect-power block collision theorem closes the two.
helper = r'''/-- Direct modern U2D/perfect-power collision.
The child witness is used on the canonical left sheet; no legacy full-power
creation theorem, finite search, or reconstructed parent witness is involved. -/
theorem gst_prefix_one_u2d_atomic_collision_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  let E : Nat := 4^(3^(s+1) * n)
  let N : Nat := 3^s
  let B : Nat := 3^(s+2)
  let P1 : Nat := 1 + 3^(s+1)
  let H : Nat := gstPrefixOneUPotentialTailS s n
  let T : Nat := gstNavigationConstant (s+1) n

  obtain ⟨q, hdT, hspaceT⟩ := hchild

  have hCarryT : gstCarry T q = 0 ∨ gstCarry T q = 3 := by
    by_cases hq0 : q = 0
    · subst q
      left
      simp [gstCarry]
    · have hq1 : 1 ≤ q := by omega
      have hmod : gstCarry T q % 3 = 0 :=
        gstGoodSpace_carry_mod3_zero T q hspaceT
      have hlt : gstCarry T q < 4 := gstCarry_lt_four T q hq1
      omega

  have hE0 : E = 1 + B*T := by
    dsimp [E, B, T]
    simpa [Nat.add_assoc] using
      (gst_navigation_decomposition (s+1) n (by omega : 1 ≤ s+1))

  have hB27 : 27 ≤ B := by
    dsimp [B]
    have hpow : 3^3 ≤ 3^(s+2) :=
      Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have hseed0 : (4 * 1) / B = 0 := Nat.div_eq_of_lt (by omega)

  have hChild :
      GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E 0 (s+2+q)).seven.carry
        (GSTGraphV2InfiniteControl.graph E 0 (s+2+q)).seven.digit := by
    apply (GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
      E 0 (s+2) 1 T q (by simpa [B] using hE0) (by simpa [B] using (show 1 < B by omega))).2
    rw [show (4 * 1) / 3^(s+2) = 0 by simpa [B] using hseed0]
    constructor
    · simpa [GSTCanonicalSevenAxisBridge.digit3, gstDigit, T] using hdT
    · simpa [GSTGraphV2InfiniteControl.seededCarry, gstCarry, T] using hCarryT

  have hc3 : c s % 3 = 1 := c_mod3 s hs
  have hcshape : c s = 1 + 3 * (c s / 3) := by
    have hcdiv := Nat.mod_add_div (c s) 3
    rw [hc3] at hcdiv
    omega
  have hA : 4^(3^s) = 1 + 3^(s+1) * c s := lte_identity s hs
  have hE1raw := gst_canonical_phase1_energy_shape_surgeryS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    s n (c s) (c s / 3) hs hA hcshape
  have hE1 : 4^N * E = P1 + B*H := by
    dsimp [N, E, P1, B, H, gstPrefixOneUPotentialTailS]
    rw [show 3^(s+2) = 3 * 3^(s+1) by
      rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]; ac_rfl]
    simpa [Nat.mul_assoc] using hE1raw

  let X : Nat := 3^(s+1)
  have hX9 : 9 ≤ X := by
    dsimp [X]
    have hpow : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have hBshape : B = 3 * X := by
    dsimp [B, X]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hP1shape : P1 = 1 + X := by rfl
  have hP1 : P1 < B := by
    rw [hBshape, hP1shape]
    omega
  have hP1lo : B ≤ 4 * P1 := by
    rw [hBshape, hP1shape]
    omega
  have hP1hi : 4 * P1 < 2 * B := by
    rw [hBshape, hP1shape]
    omega
  have hBpos : 0 < B := by omega
  have hseed1lo : 1 ≤ (4 * P1) / B :=
    (Nat.le_div_iff_mul_le hBpos).2 (by simpa using hP1lo)
  have hseed1hi : (4 * P1) / B < 2 :=
    (Nat.div_lt_iff_lt_mul hBpos).2 (by simpa using hP1hi)
  have hseed1 : (4 * P1) / B = 1 := by omega

  have hseeded := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad
  have hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.digit := by
    intro j hHappy
    have hTail :=
      (GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
        E N (s+2) P1 H j hE1 hP1).1 hHappy
    rw [hseed1] at hTail
    have hbadj := hseeded j
    apply hbadj
    simpa [GSTBadPairS, GSTCanonicalSevenAxisBridge.digit3,
      GSTGraphV2InfiniteControl.seededCarry,
      gstAffineMulCarryS, gstDigitS] using hTail

  exact GSTGraphV2PerfectPowerBlockCollision.canonical_perfect_power_block_collision
    s n q hs hn
    (by simpa [E, GSTGraphV2PerfectPowerBlock.canonicalEnergy] using hChild)
    (by
      intro j
      simpa [E, N, GSTGraphV2PerfectPowerBlock.canonicalEnergy,
        GSTGraphV2PerfectPowerBlock.canonicalWidth] using hRightBad j)

'''

if 'gst_four_power_creation_certificate_inline' in helper:
    raise SystemExit('legacy h_creation linkage reintroduced into modern collision helper')
if 'gst_h_creation_full_power_navigation_atomic' in helper:
    raise SystemExit('legacy full-power creation adapter reintroduced')
if 'gst_full_power_navigation_descends_atomic' in helper:
    raise SystemExit('legacy full-power descent adapter reintroduced')

target_replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  exact gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad
'''

s2 = s[:target_doc_start] + helper + target_doc + target_replacement + s[end:]

if s2.count(TARGET) != 1:
    raise SystemExit('post-surgery target theorem multiplicity check failed')
if s2.count('theorem gst_prefix_one_u2d_atomic_collision_inline') != 1:
    raise SystemExit('post-surgery U2D collision theorem multiplicity check failed')
if 'gst_h_creation_full_power_navigation_atomic' in s2:
    raise SystemExit('legacy full-power creation adapter survived/reappeared')
if 'gst_full_power_navigation_descends_atomic' in s2:
    raise SystemExit('legacy full-power descent adapter survived/reappeared')
public_lift_count = len(re.findall(r'(?m)^theorem gst_prefix_one_navigation_lift\b', s2))
if public_lift_count != 1:
    raise SystemExit(f'public prefix-one theorem multiplicity changed: {public_lift_count}')
if packet_marker_re.findall(s2) != packet_markers_before:
    raise SystemExit('surviving historical attached-packet structure changed')
for stale_import in STALE_UNUSED_IMPORTS:
    if stale_import in s2:
        raise SystemExit(f'stale circular import survived: {stale_import.strip()}')
for module in attached_modules:
    if f'import {module}\n' in s2:
        raise SystemExit(f'attached duplicate direct import survived: {module}')
for module in TRANSITIVE_ATTACHED_DUPLICATES:
    if f'-- BEGIN ATTACHED {module}.lean' in s2 or f'-- END ATTACHED {module}.lean' in s2:
        raise SystemExit(f'transitively imported duplicate packet survived: {module}')
for declaration in CORE_DECLARATIONS:
    if declaration in s2:
        raise SystemExit(f'extracted core declaration survived: {declaration.splitlines()[0]}')
for required_import in (CORE_IMPORT, COLLISION_IMPORT):
    if required_import not in s2:
        raise SystemExit(f'required import missing after surgery: {required_import.strip()}')

new_target = s2.index(TARGET)
new_end = s2.find(TARGET_END, new_target)
region = s2[new_target:new_end]
if re.search(r'(?m)^\s*gst_end\s*$', region):
    raise SystemExit('gst_end survived target theorem surgery')
if 'gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad' not in region:
    raise SystemExit('minimal U2D collision application missing from target theorem')
for forbidden in (
    'trace_state',
    'contradiction',
    'GSTResidualBoundary',
    'gst_prefix_one_bigN_future_zero_inline',
    'let r := v3 n',
):
    if forbidden in region:
        raise SystemExit(f'legacy proof path survived target theorem: {forbidden}')

MONOLITH.write_text(s2, encoding='utf-8')
written = MONOLITH.read_text(encoding='utf-8')
if written != s2:
    raise SystemExit('post-write monolith integrity check failed')

print(f'ATOMIC_INPUT_BYTES={original_bytes}')
print(f'ATOMIC_OUTPUT_BYTES={len(written.encode("utf-8"))}')
print('ATOMIC_MODERN_COLLISION_HELPERS=1')
print('ATOMIC_TARGET_SIGNATURE_PRESERVED=1')
print('ATOMIC_PUBLIC_LIFT_MULTIPLICITY=1')
print('ATOMIC_LEGACY_H_CREATION_DEPENDENCY=0')
print('ATOMIC_PERFECT_POWER_COLLISION=1')
print(f'ATOMIC_STALE_CIRCULAR_IMPORTS_REMOVED={removed_stale_imports}')
print(f'ATOMIC_ATTACHED_DUPLICATE_IMPORTS_REMOVED={removed_attached_imports}')
print(f'ATOMIC_ATTACHED_DUPLICATE_MODULES_REMOVED={len(removed_attached_modules)}')
print(f'ATOMIC_TRANSITIVE_ATTACHED_PACKETS_REMOVED={removed_transitive_packets}')
print(f'ATOMIC_NAVIGATION_CORE_DECLARATIONS_REMOVED={removed_core_declarations}')
print('ATOMIC_SURGERY=MODERN_CHILD_TO_PERFECT_POWER_COLLISION_PLUS_ONE_THEOREM_BODY')
for i, line in enumerate(written.splitlines(), 1):
    if 'theorem gst_prefix_one_u2d_atomic_collision_inline' in line:
        print(f'ATOMIC_COLLISION_START={i}')
    if 'theorem gst_prefix_one_information_bad_descends_inline' in line:
        print(f'ATOMIC_TARGET_START={i}')
