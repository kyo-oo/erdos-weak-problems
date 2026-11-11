import numpy as np
from fractions import Fraction as F

def count_reps(J, xnum, xden):
    # number of subsets S of {1..J} with v(S) = xnum/xden, via integer subset-sum DP
    tgt = (xnum << J) // xden
    assert (xnum << J) % xden == 0
    cnt = np.zeros(tgt + 1, dtype=np.int64); cnt[0] = 1
    for a in range(1, J + 1):
        w = a << (J - a)
        if w <= tgt:
            cnt[w:] += cnt[:tgt + 1 - w].copy()
    return int(cnt[tgt])

print("c(J) = #{S subset of [1..J] : v(S)=x}  (distinct-piece representations, pieces<=J):")
for (xn, xd, lab) in [(1, 2, "1/2"), (1, 4, "1/4"), (3, 8, "3/8")]:
    row = []
    for J in range(6, 25):
        c = count_reps(J, xn, xd)
        row.append(f"J={J}:{c}")
    print(f"  x={lab}: " + "  ".join(row))

# enumerate the representations of 1/2 with max piece <= 16 (cross-check Kill #5 census)
J = 16
tgt = 1 << (J - 1)
w = {a: a << (J - a) for a in range(1, J + 1)}
reps, rem = [], {a: sum(w[b] for b in range(a, J + 1)) for a in range(1, J + 2)}
def dfs(a, part, cur):
    if part == tgt: reps.append(list(cur)); return
    if a > J or part + rem[a] < tgt or part > tgt: return
    cur.append(a); dfs(a + 1, part + w[a], cur); cur.pop()
    dfs(a + 1, part, cur)
dfs(1, 0, [])
for r in reps: assert sum(F(a, 2 ** a) for a in r) == F(1, 2)
print(f"representations of 1/2 with pieces<=16 ({len(reps)}): {reps}")
