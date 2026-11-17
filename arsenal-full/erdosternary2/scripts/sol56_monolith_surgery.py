from pathlib import Path

path = Path("ErdosTernary2.lean")
text = path.read_text(encoding="utf-8")

import_anchor = "import GSTFinalPurePowerResidueTransplant\n"
new_import = "import GSTGraphV2FourPowerRelocationClosure\n"
if new_import not in text:
    if import_anchor not in text:
        raise SystemExit("SOL56 surgery: import anchor not found")
    text = text.replace(import_anchor, import_anchor + new_import, 1)

old = '''theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  intro K hK5 hK7
  simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using
    (gst_four_power_creation_certificate_inline K hK5 hK7)
'''

new = '''theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact GSTGraphV2FourPowerRelocationClosure.four_power_creation_master
'''

if old in text:
    if text.count(old) != 1:
        raise SystemExit(f"SOL56 surgery: expected one old theorem body, found {text.count(old)}")
    text = text.replace(old, new, 1)
elif new not in text:
    raise SystemExit("SOL56 surgery: neither old nor completed theorem body found")

start = text.find("theorem gst_four_power_creation_master_inline")
end = text.find("theorem gst_prefix_one_navigation_lift", start)
if start < 0 or end < 0:
    raise SystemExit("SOL56 surgery: production theorem window not found")
window = text[start:end]
if "gst_four_power_creation_certificate_inline" in window:
    raise SystemExit("SOL56 surgery: quarantined identifier remains active in master window")
if "gst_oscillation_from_navigation" in window:
    raise SystemExit("SOL56 surgery: historical oscillation route remains active in master window")
if "GSTGraphV2FourPowerRelocationClosure.four_power_creation_master" not in window:
    raise SystemExit("SOL56 surgery: completed standalone master not wired")

path.write_text(text, encoding="utf-8")
print("SOL56 monolith surgery applied and guarded")
