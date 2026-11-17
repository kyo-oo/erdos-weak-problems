from pathlib import Path

MONO = Path("ErdosTernary2.lean")
LAKE = Path("lakefile.toml")

text = MONO.read_text(encoding="utf-8")

# 1) Make the certified standalone collision theorem visible to the monolith.
imp = "import GSTPrefixOneU2DCollisionProof\n"
if imp not in text:
    anchor = "import GSTFinalPurePowerResidueTransplant\n"
    if anchor not in text:
        raise SystemExit("import anchor not found")
    text = text.replace(anchor, anchor + imp, 1)

# 2) Replace only the known RED theorem. Everything before/after remains byte-for-byte.
start_marker = "/-- Exact remaining information-descent seam."
end_marker = "/-- Corrected information-wave closure:"
start = text.index(start_marker)
end = text.index(end_marker, start)

replacement = r'''/-- Exact information-descent closure. Parent Ω-badness is converted to the
    canonical seed-one bad right edge, while the supplied child Navigation
    witness supplies a genuine Happy gate of the canonical child tail. The
    certified standalone U2D perfect-power collision closes the sheet. -/
theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

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

  have hAunit :
      A = 1 + 3^(s+1) * gstNavigationConstant s 1 := by
    dsimp [A]
    simpa using (gst_navigation_decomposition s 1 hs)

  have hunitPrefix :
      gstNavigationConstant s 1 = 1 + 3*z := by
    simpa [z] using gst_navigation_constant_unit_prefixS s hs

  obtain ⟨q, hgate⟩ := hchildGate

  have hChildStandalone :
      GSTU2DEventTransport.HappyCell
        (GSTCanonicalSevenAxisBridge.carry4
          (GSTPrefixOneU2DCollisionProof.childTail s n) q)
        (GSTCanonicalSevenAxisBridge.digit3
          (GSTPrefixOneU2DCollisionProof.childTail s n) q) := by
    simpa [GSTSeededHappyS, gstDigitS, gstAffineMulCarryS,
      GSTU2DEventTransport.HappyCell,
      GSTCanonicalSevenAxisBridge.carry4,
      GSTCanonicalSevenAxisBridge.digit3,
      GSTPrefixOneU2DCollisionProof.childTail,
      GSTPrefixOneU2DCollisionProof.childEnergy,
      T, gstNavigationConstant, Nat.add_assoc] using hgate

  have hParentStandalone : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.seededCarry 1
          (GSTPrefixOneU2DCollisionProof.rightTail s n z) j)
        (GSTCanonicalSevenAxisBridge.digit3
          (GSTPrefixOneU2DCollisionProof.rightTail s n z) j) := by
    intro j
    have hj := hparent j
    simpa [GSTBadPairS, gstAffineMulCarryS, gstDigitS,
      GSTU2DEventTransport.HappyCell,
      GSTGraphV2InfiniteControl.seededCarry,
      GSTCanonicalSevenAxisBridge.digit3,
      GSTPrefixOneU2DCollisionProof.rightTail,
      GSTPrefixOneU2DCollisionProof.childTail,
      GSTPrefixOneU2DCollisionProof.childEnergy,
      H, A, T, gstNavigationConstant, Nat.add_assoc] using hj

  exact GSTPrefixOneU2DCollisionProof.canonical_prefix_one_u2d_collision
    s n (gstNavigationConstant s 1) z q hs hn
    (by simpa [A] using hAunit)
    hunitPrefix
    hChildStandalone
    hParentStandalone

'''

text = text[:start] + replacement + text[end:]
MONO.write_text(text, encoding="utf-8")

# 3) The monolith now imports the certified collision module, so register its
# local roots in the explicit Lake closure.
lake = LAKE.read_text(encoding="utf-8")
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
LAKE.write_text(lake, encoding="utf-8")

# Atomic rerun marker: the workflow compiles monolith + closure before committing.
print("STEP6_TRANSPLANT_OK")
