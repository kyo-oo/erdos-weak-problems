/- ======================================================================
/- CHRONOLOGICAL LABEL — #0002 / 1133
/-    Path         : .devcontainer/setup.sh
/-    Ref          : main
/-    First-commit : 2026-08-14 14:07:02 +0530
/-    Last-commit  : 2026-08-14 14:35:46 +0530
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- ====================================================================== -/

# ======================================================================
# CHRONOLOGICAL LABEL -- #0002 / 1132
#    Path         : .devcontainer/setup.sh
#    Ref          : main
#    First-commit : 2026-08-14 14:07:02 +0530  (85afb9e)
#    Last-commit  : 2026-08-14 14:35:46 +0530  (6591330)
#    Total commits: 2
# ======================================================================
# GIT HISTORY (chronological, oldest first)
# ======================================================================
# [01/2] 2026-08-14 14:07:02 +0530  85afb9e  (ker07-dev)
#        chore: add .devcontainer/setup.sh
# [02/2] 2026-08-14 14:35:46 +0530  6591330  (ker07-dev)
#        fix: Codespace setup delegates to real comparator installer
# ======================================================================

#!/usr/bin/env bash
set -euo pipefail
exec bash scripts/setup-comparator.sh
