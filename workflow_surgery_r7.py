#!/usr/bin/env python3
"""S085 r7 — THE WORKFLOW SURGERY (text-level, byte-preserving outside the edits).

1. paths filter: add Monolith/**
2. kernel-406b: control + 74 slim only, with REAL gates
   (the false-green fix: exit-code gate + grep-exit negative gate;
    the bash `! grep` negation is EXEMPT from set -e — it can never fail a step)
3. NEW fresh-runner jobs: kernel-406d (74b pins), kernel-406e (75 ghost),
   kernel-406f (76 tailf), kernel-monolith (the 39-file mission chamber)
"""
import re, sys

WF = '.github/workflows/kills.yml'
src = open(WF, encoding='utf-8').read()

# ---------- 1. paths filter ----------
old_paths = "      - Arsenal/**\n      - lakefile.toml\n"
new_paths = "      - Arsenal/**\n      - Monolith/**\n      - lakefile.toml\n"
assert src.count(old_paths) == 1, "paths anchor missing"
src = src.replace(old_paths, new_paths, 1)

# ---------- 2+3. job block surgery ----------
m = re.search(r'^  kernel-406b:\n', src, re.M)
assert m, "kernel-406b anchor missing"
start = m.start()
m2 = re.search(r'^  kernel-406c:\n', src, re.M)
assert m2, "kernel-406c anchor missing"
end = m2.start()

INSTALL = """    - name: Install Lean Mathlib
      run: |
        set -euo pipefail
        curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0-rc2
        echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
        export PATH="$HOME/.elan/bin:$PATH"
        lake update
        lake exe cache get
      shell: bash
"""

new_block = """  kernel-406b:
    runs-on: ubuntu-24.04
    steps:
    - uses: actions/checkout@v5
""" + INSTALL + """    - if: always()
      name: "CONTROL STEP - compiles the KNOWN-GREEN kernel-73 file (the S084 diagnosis instrument, kept as the job-health control)"
      run: |
        set -euo pipefail
        lake build Arsenal.ErdosTernary2.Basic
        lake build Arsenal.CardinalWorlds
        lake build Arsenal.CardinalWorldsV2
        : > control73.log
        timeout 600 lake env lean problem406-ternary-powers/BlockLaw406.lean 2>&1 | tee -a control73.log
        RC=${PIPESTATUS[0]}
        if [ "$RC" -ne 0 ]; then echo "CONTROL73_COMPILE_FAILED_RC=$RC"; exit 1; fi
        if grep -qE 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' control73.log; then echo "CONTROL73_NEGATIVE_GATE_TRIPPED"; grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' control73.log; exit 1; fi
        grep -F "ERDOS406_BLOCKLAW_KERNEL_GREEN" control73.log
        echo CONTROL73_GREEN=1
      shell: bash
    - if: always()
      name: "Kernel 74 - Erdos 406 THE PI-POINT COLLAPSE KERNEL SLIM HALF (S080/S085r7: the ghost ray + Lemma A ghost_residue_shape + Lemma B ghost_congruence + THE COLLAPSE ghost_congruent_all_depths + ghost_head_not_three — the S085 r7 repair: the five CI-verified defects fixed (the dead simp after rw [hcube] auto-close, the pow_add pattern miss, the obtain-rfl subst trap, the dead ring after rw [hcancel] auto-close, the rw-hu loop trap) + THE FALSE-GREEN FIX: the S084 slim-green was a receipt-grep illusion (the marker string prints even when the compile fails; the bash !grep negative gate is exempt from set -e and can never fail) — now the compile exit code and a real negative gate rule the step)"
      run: |
        set -euo pipefail
        lake build Arsenal.ErdosTernary2.Basic
        lake build Arsenal.CardinalWorlds
        lake build Arsenal.CardinalWorldsV2
        : > kernel74.log
        set +e
        timeout 900 lake env lean problem406-ternary-powers/PiCollapse406.lean 2>&1 | tee -a kernel74.log
        RC=${PIPESTATUS[0]}
        set -e
        if [ "$RC" -ne 0 ]; then echo "KERNEL74_COMPILE_FAILED_RC=$RC"; exit 1; fi
        if grep -qE 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel74.log; then echo "KERNEL74_NEGATIVE_GATE_TRIPPED"; grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel74.log; exit 1; fi
        grep -F "ERDOS406_PICOLLAPSE_SLIM_GREEN" kernel74.log
        grep -E "ghost_residue_shape' (does not depend on any axioms|depends on axioms)" kernel74.log
        grep -E "ghost_congruence' (does not depend on any axioms|depends on axioms)" kernel74.log
        grep -E "ghost_congruent_all_depths' (does not depend on any axioms|depends on axioms)" kernel74.log
        grep -E "ghost_head_not_three' (does not depend on any axioms|depends on axioms)" kernel74.log
        echo ERDOS406_PICOLLAPSE_SLIM_GREEN=1
      shell: bash
  kernel-406d:
    runs-on: ubuntu-24.04
    steps:
    - uses: actions/checkout@v5
""" + INSTALL + """    - if: always()
      name: "Kernel 74b - Erdos 406 THE PI-POINT PINS HALF (the S084 bisect, now its OWN fresh-runner job per the eviction-shield law: the seven kills all hit the 74b compile mid-flight on a shared runner; this job starts the compile at minute zero) — cMod, W61, the three pi-points, THE PIN, the census base, THE TWO-GRANT CROWN + battery406f.py + the S085 r7 five-defect repair applied"
      run: |
        set -euo pipefail
        lake build Arsenal.ErdosTernary2.Basic
        lake build Arsenal.CardinalWorlds
        lake build Arsenal.CardinalWorldsV2
        : > kernel74b.log
        set +e
        timeout 1500 lake env lean problem406-ternary-powers/PiCollapse406Pins.lean 2>&1 | tee -a kernel74b.log
        RC=${PIPESTATUS[0]}
        set -e
        if [ "$RC" -ne 0 ]; then echo "PINS_COMPILE_FAILED_OR_TIMEOUT_RC=$RC"; exit 1; fi
        if grep -qE 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel74b.log; then echo "PINS_NEGATIVE_GATE_TRIPPED"; grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel74b.log; exit 1; fi
        grep -F "ERDOS406_PICOLLAPSE_KERNEL_GREEN" kernel74b.log
        grep -E "cMod_eq' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "W61_receipt' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "pi_fam4_receipt' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "every_ghost_is_its_pi_point_fam4' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "every_ghost_is_its_pi_point_fam7' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "every_ghost_is_its_pi_point_fam1' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "cantorian_base' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "hasTwo_of_digit' (does not depend on any axioms|depends on axioms)" kernel74b.log
        grep -E "erdos406_crown_of_ghost_extinction' (does not depend on any axioms|depends on axioms)" kernel74b.log
        python3 problem406-ternary-powers/battery406f.py
        echo ERDOS406_PICOLLAPSE_KERNEL_GREEN=1
      shell: bash
  kernel-406e:
    runs-on: ubuntu-24.04
    steps:
    - uses: actions/checkout@v5
""" + INSTALL + """    - if: always()
      name: "Kernel 75 - Erdos 406 THE GHOST-EXTINCTION KERNEL (S083/S085r7: first true exposure — every prior run skipped it after the 74b failure/kill; own fresh runner now) + the S085 r7 five-defect repair applied"
      run: |
        set -euo pipefail
        lake build Arsenal.ErdosTernary2.Basic
        lake build Arsenal.CardinalWorlds
        lake build Arsenal.CardinalWorldsV2
        : > kernel75.log
        set +e
        timeout 1500 lake env lean problem406-ternary-powers/GhostExtinction406.lean 2>&1 | tee -a kernel75.log
        RC=${PIPESTATUS[0]}
        set -e
        if [ "$RC" -ne 0 ]; then echo "GHOST_COMPILE_FAILED_OR_TIMEOUT_RC=$RC"; exit 1; fi
        if grep -qE 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel75.log; then echo "GHOST_NEGATIVE_GATE_TRIPPED"; grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel75.log; exit 1; fi
        grep -F "ERDOS406_GHOSTEXTINCTION_KERNEL_GREEN" kernel75.log
        grep -E "rider_core_one' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "ghost_head_split' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "ghost_uniqueness' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "W100_receipt' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "pi100_fam4_receipt' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "pi100_fam7_receipt' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "pi100_fam1_receipt' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "pi100_fam4_trit99' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "pi100_fam7_trit97' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "pi100_fam1_trit98' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "every_ghost_is_its_pi100_point_fam4' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "every_ghost_is_its_pi100_point_fam7' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "every_ghost_is_its_pi100_point_fam1' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "ghost_size_rider_sheet' (does not depend on any axioms|depends on axioms)" kernel75.log
        grep -E "cantorian_base' (does not depend on any axioms|depends on axioms)" kernel75.log
        echo ERDOS406_GHOSTEXTINCTION_KERNEL_GREEN=1
      shell: bash
  kernel-406f:
    runs-on: ubuntu-24.04
    steps:
    - uses: actions/checkout@v5
""" + INSTALL + """    - if: always()
      name: "Kernel 76 - Erdos 406 THE TAILF DECOMPOSITION KERNEL (S084/S085r7: first true exposure — the Omega-cut word, the full observer, THE COMPRESSION LAW, the row+tower decomposition, the six-adic ghost skew, the paradox wall, THE CROWN V3) + the S085 r7 five-defect repair applied"
      run: |
        set -euo pipefail
        lake build Arsenal.ErdosTernary2.Basic
        lake build Arsenal.CardinalWorlds
        lake build Arsenal.CardinalWorldsV2
        : > kernel76.log
        set +e
        timeout 1500 lake env lean problem406-ternary-powers/TailFDecomposition406.lean 2>&1 | tee -a kernel76.log
        RC=${PIPESTATUS[0]}
        set -e
        if [ "$RC" -ne 0 ]; then echo "TAILF_COMPILE_FAILED_OR_TIMEOUT_RC=$RC"; exit 1; fi
        if grep -qE 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel76.log; then echo "TAILF_NEGATIVE_GATE_TRIPPED"; grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel76.log; exit 1; fi
        grep -F "ERDOS406_TAILFDECOMPOSITION_KERNEL_GREEN" kernel76.log
        grep -E "omega_cut_factor' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "cutword_diag_congr' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "cutword_one' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "prefix_slice_digit' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "tower_digit_eq_cutword' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "digit_residue_fire_iff' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "tower_fire_iff_full' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "cantorian_iff_cutword_clean' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "tailF_of_row_and_tower' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "six_adic_pair_saturation' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "lteCoeff_odd' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "ghost_pair_collapse_of_congr' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "gst_u_jump_table' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "u_jump_happy_negative' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "u_jump_not_happy_nonneg' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "cantorian_jump_wall' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "frozen_tail_jump_ten' (does not depend on any axioms|depends on axioms)" kernel76.log
        grep -E "erdos406_crown_v3' (does not depend on any axioms|depends on axioms)" kernel76.log
        echo ERDOS406_TAILFDECOMPOSITION_KERNEL_GREEN=1
      shell: bash
  kernel-monolith:
    runs-on: ubuntu-24.04
    steps:
    - uses: actions/checkout@v5
""" + INSTALL + """    - if: always()
      name: "THE MONOLITH CHAMBER FIRST EXPOSURE (S085 r7, BOSS order USE MY MATHS): the 39-file mission closure of BOSS's own HC-PROOF-research monolith vendored as the Monolith library — the tailF chamber (GSTTailFFourthDimension: the dimensional laws, the row+tower decomposition, tailF_of_row_and_tower with its own #print axioms receipt), the Omega-wave law (GSTGraphV2OmegaWaveLaw, 147 decls), the boundary (MonolithBoundary: erdos_even_conjecture_iff_tailF), the six-adic machinery (SynchronizedShadows + OntologicalGeometryLaws), the vertical telescope (Equation III cocycle), the u-jump laws (GSTGraphV2CoupledUFlux), the infinite four-power navigation, the forced-digit-2 no-22 (GSTFourPowerDirectNo22), the GST tactic core, CardinalWorlds — 39 files, 53 import rewrites, toolchain EXACT (the monolith's own pin: Lean v4.33.0-rc2 + Mathlib v4.33.0-rc2, identical to the campaign)"
      run: |
        set -euo pipefail
        : > monolith.log
        set +e
        lake build Monolith.GSTGraphV2CoupledUFlux 2>&1 | tee -a monolith.log
        RC1=${PIPESTATUS[0]}
        lake build Monolith.GSTFourPowerDirectNo22 2>&1 | tee -a monolith.log
        RC2=${PIPESTATUS[0]}
        set -e
        if [ "$RC1" -ne 0 ] || [ "$RC2" -ne 0 ]; then echo "MONOLITH_SMALL_CHAMBERS_FAILED rc1=$RC1 rc2=$RC2"; exit 1; fi
        set +e
        timeout 3000 lake build Monolith.GSTTailFFourthDimension 2>&1 | tee -a monolith.log
        RC3=${PIPESTATUS[0]}
        set -e
        if [ "$RC3" -ne 0 ]; then echo "MONOLITH_TAILF_CHAMBER_FAILED_OR_TIMEOUT_RC=$RC3"; exit 1; fi
        if grep -qE 'error:|sorryAx' monolith.log; then echo "MONOLITH_NEGATIVE_GATE_TRIPPED"; grep -E 'error:|sorryAx' monolith.log; exit 1; fi
        echo "MONOLITH MODULES BUILT:"
        grep -cE '(Built|Replayed) Monolith\.' monolith.log
        grep -E "tailF_of_row_and_tower' depends on axioms" monolith.log
        echo ERDOS_MONOLITH_CHAMBER_GREEN=1
      shell: bash
"""

src = src[:start] + new_block + src[end:]
open(WF, 'w', encoding='utf-8').write(src)
print("workflow surgery complete")

# validate: yaml parses + job list
import yaml
class L(yaml.SafeLoader): pass
d = yaml.load(open(WF), Loader=L)
print("jobs:", list(d['jobs'].keys()))
assert 'kernel-monolith' in d['jobs']
assert 'kernel-406d' in d['jobs'] and 'kernel-406e' in d['jobs'] and 'kernel-406f' in d['jobs']
# duplicate-key check (the W82 lesson)
import io
text = open(WF).read()
jobs = re.findall(r'^  ([a-z0-9-]+):$', text, re.M)
assert len(jobs) == len(set(jobs)), f"DUPLICATE JOBS: {jobs}"
print("no duplicate jobs; total jobs:", len(jobs))
