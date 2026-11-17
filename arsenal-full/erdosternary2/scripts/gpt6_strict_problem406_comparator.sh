#!/usr/bin/env bash
# Strict challenge-equivalent Problem 406 comparator.
# Passes ONLY with an unconditional kernel theorem matching the question type.
# The legacy V5 build+grep comparator is NOT this certification.
set -euo pipefail
cd "$(dirname "$0")/.."
source_file="questions/deepmind_problem_406/Challenge.lean"
solution_file="questions/deepmind_problem_406/Solution.lean"
test -f "$source_file"
test -f "$solution_file"

# The standalone challenge and the submitted solution must define the
# benchmark digit predicate byte-identically, not merely share a name.
python3 - <<'PY'
from pathlib import Path
import re
p=re.compile(r'def noTernaryDigitTwo \(n : Nat\) : Bool :=.*?decreasing_by exact Nat.div_lt_self \(by omega\) \(by decide : 1 < 3\)', re.S)
a=Path('questions/deepmind_problem_406/Challenge.lean').read_text()
b=Path('questions/deepmind_problem_406/Solution.lean').read_text()
m=p.search(a); n=p.search(b)
if not m or not n or m.group()!=n.group():
    raise SystemExit('UNCONDITIONAL_COMPARATOR_FAIL: challenge predicate does not match submitted definition')
print('STRICT_PREDICATE_MATCH=1')
PY

export PATH="$HOME/.elan/bin:$PATH"
lake build ErdosTernary2

tmp="$(mktemp --suffix=.lean)"
log="$(mktemp)"
trap 'rm -f "$tmp" "$log"' EXIT
cat "$solution_file" > "$tmp"
cat >> "$tmp" <<'LEAN'

/- STRICT EXTRA TYPE CHECK.
   This WILL FAIL if erdos_ternary_2 has an extra hGate argument.
   A passing lake build or a zero-sorry source scan is not sufficient. -/
example : (∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false) := by
  exact erdos_ternary_2

#print axioms erdos_ternary_2
LEAN
if ! lake env lean "$tmp" 2>&1 | tee "$log"; then
    echo "=== STRICT PROBLEM406 COMPARATOR: FAIL (missing exact unconditional theorem) ==="
    exit 1
fi
python3 - "$log" <<'PY'
from pathlib import Path
import re, sys
s=Path(sys.argv[1]).read_text()
if re.search(r'\bsorryAx\b|\bnative_decide\b|\baxiom\b',s):
    raise SystemExit('STRICT COMPARATOR FAIL: forbidden untrusted proof escape')
m=re.search(r"['\x60]?erdos_ternary_2['\x60]?\s+depends on axioms:\s*\[(.*?)\]",s,re.S)
if not m:
    if 'does not depend on any axioms' in s:
        print('STRICT_AXIOMS_EMPTY=1')
    else:
        raise SystemExit('STRICT COMPARATOR FAIL: axiom audit receipt absent')
else:
    names=[x.strip() for x in m.group(1).split(',') if x.strip()]
    allowed={'propext','Classical.choice','Quot.sound'}
    bad=[n for n in names if n not in allowed]
    if bad: raise SystemExit('STRICT COMPARATOR FAIL: nonstandard axioms '+str(bad))
    print('STRICT_AXIOMS_ALLOWED=',names)
PY
echo "=== STRICT PROBLEM406 UNCONDITIONAL KERNEL: PASS ==="
