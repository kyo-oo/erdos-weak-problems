#!/usr/bin/env python3
# gen_lean_row939.py — W63-B1: generate the Lean snippet for the 10^7 zero-box
# anchor rows (LIST4P7 literal list + memNat + two closed native_decide
# theorems) and splice it into Erdos939R4.lean before `end E939R4`.
import sys, io, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hunt939d as H

L = H.gen4(10 ** 7)
assert len(L) == 234, len(L)
rows = [L[i:i + 10] for i in range(0, len(L), 10)]
body = '\n'.join('  ' + ', '.join(str(v) for v in r) + ',' for r in rows)
# drop the trailing comma of the final row
last = body.rstrip()
assert last.endswith(',')
body = last[:-1]

snippet = '''/-! ## The W63-B1 zero-box anchor rows (10^7, native_decide scale)

`LIST4P7` is the exhaustive 4-powerful list below 10^7 (234 values,
python-certified TWO WAYS in W63-B1: the DFS enumerator `gen4` — which
reproduces the K60 census row at 10^4 exactly — and an INDEPENDENT numpy
rad-sieve computing rad(n) for every n <= 10^7 with the rad^4 | n test; the two
constructions agree element-by-element at 10^7 — validate939_output.txt,
STATUS_W63.md). The two rows below are then CLOSED native_decide goals
(S059 proof-route law): no two COPRIME members of the list sum back into the
list, and no member's successor is a member (the a = 1 lane). Together with
the completeness certificate this is: NO pairwise-coprime triple of
4-powerful numbers a + b = c with c <= 10^7 — the 10^7 anchor of the W63-B1
box frontier (python-certified zero through 10^19; see STATUS_W63.md). -/

/-- Boolean membership in a literal list (structural fold; verbatim pattern
    from Erdos939.lean — this module is standalone by the NO-OOM law). -/
def memNat : Nat → List Nat → Bool
  | _, [] => false
  | n, v :: vs => decide (n = v) || memNat n vs

/-- The exhaustive 4-powerful list below 10^7 (234 values; python dual-method
    certificate: DFS enumerator == independent rad-sieve at 10^7). -/
def LIST4P7 : List Nat :=
[''' + body + ''']

/-- Certified zero-box (r=4, c <= 10^7, pair lane): NO two coprime members of
    the exhaustive 4-powerful list below 10^7 sum to another member. (Every
    pairwise-coprime 4-powerful triple a + b = c with c <= 10^7 would appear
    here — a, b < c <= 10^7 and all three in LIST4P7 by the completeness
    certificate.) -/
theorem box939_r4_1e7_pairs :
    LIST4P7.all (fun a => LIST4P7.all (fun b =>
      !(decide (Nat.gcd a b = 1) && memNat (a + b) LIST4P7))) = true := by
  native_decide

/-- Certified zero-box (r=4, c <= 10^7, successor lane): NO member of the
    exhaustive 4-powerful list below 10^7 has its successor in the list (the
    a = 1 lane: 1 is vacuously 4-powerful per `rpow 4 1 = true`). -/
theorem box939_r4_1e7_succ :
    LIST4P7.all (fun a => !(memNat (a + 1) LIST4P7)) = true := by
  native_decide

'''

LEAN = os.path.join(H.REPO, 'Erdos939R4.lean')
with open(LEAN) as fh:
    src = fh.read()

MARK = 'end E939R4'
assert src.count(MARK) == 1
assert 'LIST4P7' not in src, 'already spliced'
src = src.replace(MARK, snippet + MARK)

# extend the receipts block with the two new rows (before the final #eval)
EV = '#eval "E939R4_CENSUS_GREEN"'
assert src.count(EV) == 1
src = src.replace(EV,
    '#print axioms E939R4.box939_r4_1e7_pairs\n'
    '#print axioms E939R4.box939_r4_1e7_succ\n' + EV)

with open(LEAN, 'w') as fh:
    fh.write(src)
print('spliced LIST4P7 + box939_r4_1e7_pairs/succ into Erdos939R4.lean')
print('list head:', L[:6], '... tail:', L[-3:])
