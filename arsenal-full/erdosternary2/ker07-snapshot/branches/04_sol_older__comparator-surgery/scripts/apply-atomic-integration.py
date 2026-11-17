from pathlib import Path

p = Path("ErdosTernary2.lean")
s = p.read_text(encoding="utf-8")

if "import InformationDescentScratch\n" not in s:
    needle = "import Mathlib.Tactic.Ring\n"
    assert needle in s
    s = s.replace(needle, needle + "import InformationDescentScratch\n", 1)

start = s.index("theorem gst_shared_information_carry_equation\n")
end = s.index("/-- Any affine information carry remains strictly inside", start)
replacement = """theorem gst_shared_information_carry_equation
    (A z T q : Nat) :
    gstAffineMulCarry A (1 + 4*z) (4*T) q + A * gstCarry T q =
      gstAffineMulCarry 4 1 (z + A*T) q +
        4 * gstAffineMulCarry A z T q := by
  simpa [gstAffineMulCarry, gstCarry, gstAffineMulCarryS, gstCarryS] using
    (gst_shared_information_carry_equationS A z T q)

"""
s = s[:start] + replacement + s[end:]

opening = """/-
  Legacy residual overproof.  The final digit theorem does not require a pure
  Navigation witness at every exponent; the two-wave theorem below is strictly
  weaker and sufficient.  This block remains as proof archaeology only.

"""
if opening in s:
    s = s.replace(
        opening,
        "/- Legacy residual proof reactivated for atomic closure. -/\n\n",
        1,
    )

closing = """
-/

-- ============================================================================
-- §PREFIX-ONE SEED-ONE SURGERY (Sol Round 4 — Locked)
"""
if closing in s:
    s = s.replace(
        closing,
        "\n\n-- ============================================================================\n-- §PREFIX-ONE SEED-ONE SURGERY (Sol Round 4 — Locked)\n",
        1,
    )

p.write_text(s, encoding="utf-8")

s2 = p.read_text(encoding="utf-8")
assert "import InformationDescentScratch" in s2
assert "theorem gst_residual_navigation_lift : GSTResidualNavigationLift :=" in s2
assert "gst_shared_information_carry_equationS A z T q" in s2
print("atomic integration patch: OK")
