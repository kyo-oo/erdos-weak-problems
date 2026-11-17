from pathlib import Path

p = Path("ErdosTernary2.lean")
lakefile = Path("lakefile.toml")
s = p.read_text(encoding="utf-8")

import_anchor = "import GSTFinalPurePowerResidueTransplant\n"
needed_imports = [
    "import GSTPrefixOneU2DCollisionProof\n",
]
if any(x not in s for x in needed_imports):
    if import_anchor not in s:
        raise SystemExit("production import anchor not found")
    insertion = "".join(x for x in needed_imports if x not in s)
    s = s.replace(import_anchor, import_anchor + insertion, 1)

begin = "  -- BEGIN SOL56 FINAL ATOMIC SEAM SURGERY\n"
end = "  -- END SOL56 FINAL ATOMIC SEAM SURGERY\n"
if begin not in s or end not in s:
    raise SystemExit("production surgery markers not found")
i = s.index(begin)
j = s.index(end, i) + len(end)

replacement = r'''  -- BEGIN SOL56 FINAL ATOMIC SEAM SURGERY
  -- SOL56 STEP6 CERTIFIED PRODUCTION TRANSPLANT
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

  have hunitPrefix :
      gstNavigationConstant s 1 = 1 + 3*z := by
    simpa [z] using gst_navigation_constant_unit_prefixS s hs

  obtain ⟨q, hq⟩ := hchildGate

  have hT :
      T = GSTPrefixOneU2DCollisionProof.childTail s n := by
    simp [T, gstNavigationConstant,
      GSTPrefixOneU2DCollisionProof.childTail,
      GSTPrefixOneU2DCollisionProof.childEnergy, Nat.add_assoc]

  have hH :
      H = GSTPrefixOneU2DCollisionProof.rightTail s n z := by
    simp [H, A, GSTPrefixOneU2DCollisionProof.rightTail, hT]

  have hChildCanonical :
      GSTU2DEventTransport.HappyCell
        (GSTCanonicalSevenAxisBridge.carry4
          (GSTPrefixOneU2DCollisionProof.childTail s n) q)
        (GSTCanonicalSevenAxisBridge.digit3
          (GSTPrefixOneU2DCollisionProof.childTail s n) q) := by
    rw [← hT]
    simpa [GSTU2DEventTransport.HappyCell, GSTSeededHappyS,
      GSTCanonicalSevenAxisBridge.carry4,
      GSTCanonicalSevenAxisBridge.digit3,
      gstAffineMulCarryS, gstDigitS] using hq

  have hBadCanonical : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.seededCarry 1
          (GSTPrefixOneU2DCollisionProof.rightTail s n z) j)
        (GSTCanonicalSevenAxisBridge.digit3
          (GSTPrefixOneU2DCollisionProof.rightTail s n z) j) := by
    intro j
    have hj := hparent j
    rw [← hH]
    simpa [GSTU2DEventTransport.HappyCell, GSTBadPairS,
      GSTGraphV2InfiniteControl.seededCarry,
      GSTCanonicalSevenAxisBridge.digit3,
      gstAffineMulCarryS, gstDigitS] using hj

  have hLTE :
      4^(3^s) = 1 + 3^(s+1) * gstNavigationConstant s 1 := by
    simpa using (gst_navigation_decomposition s 1 hs)

  exact GSTPrefixOneU2DCollisionProof.canonical_prefix_one_u2d_collision
    s n (gstNavigationConstant s 1) z q hs hn
    hLTE hunitPrefix hChildCanonical hBadCanonical
  -- END SOL56 FINAL ATOMIC SEAM SURGERY
'''

s = s[:i] + replacement + s[j:]
p.write_text(s, encoding="utf-8")

# Keep the imported certified Step6 modules in the same local Lake closure as
# the monolith.  This must happen in the same checkout as the import surgery;
# otherwise Lean sees the import before the corresponding .olean is built.
lake = lakefile.read_text(encoding="utf-8")
if '"GSTGraphV2PerfectPowerBlockCollision"' not in lake:
    anchor = '  "GSTGraphV2PerfectPowerBlockProbe",\n'
    if anchor not in lake:
        raise SystemExit("lake perfect-power anchor not found")
    lake = lake.replace(anchor, anchor + '  "GSTGraphV2PerfectPowerBlockCollision",\n', 1)
if '"GSTPrefixOneU2DCollisionProof"' not in lake:
    anchor = '  "GSTPrefixOneOntologicalEscape",\n'
    if anchor not in lake:
        raise SystemExit("lake prefix-one anchor not found")
    lake = lake.replace(anchor, anchor + '  "GSTPrefixOneU2DCollisionProof",\n', 1)
lakefile.write_text(lake, encoding="utf-8")

out = p.read_text(encoding="utf-8")
if "trace_state\n  contradiction" in out:
    raise SystemExit("old RED frontier survived transplant")
if out.count("-- SOL56 STEP6 CERTIFIED PRODUCTION TRANSPLANT") != 1:
    raise SystemExit("transplant marker multiplicity is not exactly one")
if '"GSTGraphV2PerfectPowerBlockCollision"' not in lake or '"GSTPrefixOneU2DCollisionProof"' not in lake:
    raise SystemExit("certified Step6 Lake roots missing after transplant")
print("STEP6_PRODUCTION_TRANSPLANT_APPLIED=1")
print("STEP6_PRODUCTION_ROOTS_REGISTERED=1")
