from pathlib import Path

path = Path("ErdosTernary2.lean")
text = path.read_text(encoding="utf-8")

bad = """/-- The independently kernel-checked w/-
The former terminal closure beginning here was removed from the production
monolith. It depended on the quarantined legacy declaration
`gst_four_power_creation_certificate_inline`, while the attempted replacement module is explicitly
kept outside the production import closure. All preceding kernel-checked
infrastructure remains available for a future proved closure.
-/"""

good = """-- The independently kernel-checked terminal closure beginning here was removed from the production
-- monolith. It depended on the quarantined legacy declaration
-- `gst_four_power_creation_certificate_inline`, while the attempted replacement module is explicitly
-- kept outside the production import closure. All preceding kernel-checked
-- infrastructure remains available for a future proved closure."""

if bad in text:
    path.write_text(text.replace(bad, good, 1), encoding="utf-8")
    print("ERDOS_TERMINAL_COMMENT_PATCHED=1")
elif "/-- The independently kernel-checked w/-" in text:
    raise SystemExit("malformed terminal comment still present but exact block changed")
else:
    print("ERDOS_TERMINAL_COMMENT_ALREADY_CLEAN=1")
