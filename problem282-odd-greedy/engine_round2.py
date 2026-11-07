import sys, time
sys.set_int_max_str_digits(2000000)
from math import gcd
t0=time.time()
def greedy_steps(p, q, fuel=120):
    steps = 0
    while p > 0 and steps <= fuel:
        n = -(-q // p)
        if n % 2 == 0: n += 1
        p = p * n - q
        q = q * n
        steps += 1
        if p == 0: return steps
        g = gcd(p, q)
        if g > 1: p //= g; q //= g
    return None if p > 0 else steps
print("CENSUS q odd <= 301, all 0<p<q, REDUCED each step")
maxsteps = 0; argmax = None; bad = []
top = []
count = 0
for q in range(3, 302, 2):
    for p in range(1, q):
        s = greedy_steps(p, q)
        count += 1
        if s is None: bad.append((p, q))
        else:
            top.append((s, p, q))
            if s > maxsteps: maxsteps = s; argmax = (p, q)
top.sort(reverse=True)
print(f"  pairs: {count}  NON-TERM: {bad if bad else 'NONE'}")
print(f"  max steps: {maxsteps} at {argmax}")
print(f"  top 10: {top[:10]}")
print(f"TOTAL {time.time()-t0:.1f}s")
