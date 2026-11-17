from pathlib import Path
import hashlib

p = Path("ErdosTernary2.lean")
raw = p.read_bytes()
expected = "98dd8c852bbf0e866342f73a25454c4580a32b89f923a38bee035016eecf3762"
actual = hashlib.sha256(raw).hexdigest()
if actual != expected:
    raise SystemExit(f"source SHA mismatch: {actual}")

s = raw.decode("utf-8")
opening = """/-
  Legacy residual overproof.  The final digit theorem does not require a pure
  Navigation witness at every exponent; the two-wave theorem below is strictly
  weaker and sufficient.  This block remains as proof archaeology only.

/-- First-level residual Ω∞ termination."""
opened = """/-
  Legacy residual overproof.  The final digit theorem does not require a pure
  Navigation witness at every exponent; the two-wave theorem below is strictly
  weaker and sufficient.  This block remains as proof archaeology only.
-/

/-- First-level residual Ω∞ termination."""
if s.count(opening) != 1:
    raise SystemExit(f"legacy opening count = {s.count(opening)}")
s = s.replace(opening, opened, 1)

boundary = "/-- Numerical ceiling used to bound every power-of-four graph witness. -/"
quarantined = "/-\n/-- Numerical ceiling used to bound every power-of-four graph witness. -/"
if s.count(boundary) != 1:
    raise SystemExit(f"numerical-tail boundary count = {s.count(boundary)}")
s = s.replace(boundary, quarantined, 1)

p.write_text(s, encoding="utf-8")
print(hashlib.sha256(p.read_bytes()).hexdigest())
