from lib import v2
W = [0, 4, 5, 7, 10, 11, 13, 15, 17, 19, 20, 21, 23, 24, 26, 28, 29, 31, 34, 35, 36, 37]
s = sum(3**i for i in W)
print('popcount:', len(W), 'max:', max(W))
print('sum =', s)
print('v2 =', v2(s), '-> odd part =', s >> v2(s))
print('excess v2 - max(S) =', v2(s) - max(W))
print('LX check: 2*popcount =', 2*len(W), 'v2 =', v2(s), '-> LX violation' if v2(s) > 2*len(W) else 'ok')
import json
recs = {r['M']: r for r in map(json.loads, open('/home/z/erdos-weak-problems/problem406-ternary-powers/council/S094_doubter/star0.jsonl'))}
print()
print('M=35..40:', [(M, recs[M]['v2star0'], recs[M]['popcount']) for M in range(35, 41)])
w36 = recs[36]['witness']; s36 = sum(3**i for i in w36)
print('witness at 36:', w36)
print('v2(w36-sum) =', v2(s36), 'excess =', v2(s36) - max(w36))
