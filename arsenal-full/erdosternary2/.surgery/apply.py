#!/usr/bin/env python3
"""
Legacy production surgery disabled.

This script used to rewrite ErdosTernary2.lean/lakefile.toml and remove
GSTStep6Close from the Lake root graph. That behavior conflicts with the
certified Step6 close/kernel architecture.

CI must be verification-only. This script intentionally performs no mutation.
"""

print("LEGACY_PRODUCTION_SURGERY_DISABLED=1")
print("No files changed.")
