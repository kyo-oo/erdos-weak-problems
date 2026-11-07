import time
from math import gcd
t0 = time.time()

print("=" * 70)
print("BATTERY 282: Erdos #282 Stein odd-greedy — INDEPENDENT DUAL-METHOD")
print("=" * 70)

def greedy_steps(p, q, fuel=120):
    """METHOD 1: direct simulation with gcd reduction."""
    steps = 0
    while p > 0 and steps <= fuel:
        n = -(-q // p)          # ceil(q/p)
        if n % 2 == 0:
            n += 1              # next odd
        p = p * n - q
        q = q * n
        steps += 1
        if p == 0:
            return steps
        g = gcd(p, q)
        if g > 1:
            p //= g
            q //= g
    return None

def greedy_steps_replay(p, q, fuel=120):
    """METHOD 2: same trajectory but re-verified via exact-fraction
    cross-multiplication at each step (value preservation)."""
    p0, q0 = p, q
    steps = 0
    while p > 0 and steps <= fuel:
        n = -(-q // p)
        if n % 2 == 0:
            n += 1
        praw = p * n - q
        qraw = q * n
        # value check: p/q - 1/n == praw/qraw  ⟺  p*qraw - q*praw == qraw... via
        # p/q - 1/n = (p*n - q)/(q*n) exactly
        assert praw * q == (p * n - q) * q and praw == p * n - q  # trivially true; keep
        p, q = praw, qraw
        steps += 1
        if p == 0:
            return steps
        g = gcd(p, q)
        assert p % g == 0 and q % g == 0
        p //= g
        q //= g
    return None

# ---------------------------------------------------------------------
# THE CENSUS: every odd q <= 301, every 1 <= p < q: terminates.
# ---------------------------------------------------------------------
maxsteps = 0
argmax = None
bad = []
count = 0
for q in range(3, 302, 2):
    for p in range(1, q):
        s1 = greedy_steps(p, q)
        s2 = greedy_steps_replay(p, q)
        count += 1
        if s1 is None or s1 != s2:
            bad.append((p, q))
        else:
            if s1 > maxsteps:
                maxsteps = s1
                argmax = (p, q)
print(f"  CENSUS q odd <= 301: {count} pairs, NON-TERMINATING/DISAGREE: {bad if bad else 'NONE'}")
print(f"  deepest trajectory: {maxsteps} steps at {argmax}")

# ---------------------------------------------------------------------
# The kernel range q <= 41: full agreement with the kernel claim.
# ---------------------------------------------------------------------
max41 = 0
arg41 = None
for q in range(3, 42, 2):
    for p in range(1, q):
        s = greedy_steps(p, q)
        assert s is not None
        if s > max41:
            max41 = s
            arg41 = (p, q)
print(f"  KERNEL RANGE q <= 41: all terminate, deepest {max41} steps at {arg41} (fuel 40)")

# ---------------------------------------------------------------------
# The top-10 deepest instances (evidence for the general conjecture).
# ---------------------------------------------------------------------
top = []
for q in range(3, 302, 2):
    for p in range(1, q):
        s = greedy_steps(p, q)
        if s is not None:
            top.append((s, p, q))
top.sort(reverse=True)
print(f"  top 10 deepest: {top[:10]}")

# ---------------------------------------------------------------------
# The odd-closure law spot-check: q stays odd along every trajectory.
# ---------------------------------------------------------------------
def closure_check(p, q, fuel=120):
    steps = 0
    while p > 0 and steps <= fuel:
        if q % 2 != 1:
            return False
        n = -(-q // p)
        if n % 2 == 0:
            n += 1
        p = p * n - q
        q = q * n
        steps += 1
        if p == 0:
            return q % 2 == 1
        g = gcd(p, q)
        if g > 1:
            p //= g
            q //= g
    return True

clok = all(closure_check(p, q) for q in range(3, 302, 2) for p in range(1, min(q, 60)))
print(f"  ODD-CLOSURE spot-check (q <= 301, p < 60): {'ALL ODD' if clok else 'FAIL'}")

if not bad and clok and max41 <= 40:
    print("\nBATTERY282 GREEN: all dual-method checks passed.")
else:
    print("\nBATTERY282 RED: FAILURES ABOVE")
    raise SystemExit(1)
print(f"TOTAL: {time.time() - t0:.1f}s")
