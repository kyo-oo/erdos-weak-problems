def d(p, x):
    return (4**x // (3**p)) % 3
def firstp(K):
    for p in range(1, 2*K+3):
        if d(p, K) == 2 and d(p, K+1) == 2:
            return p
    return None

# Test the lift: does gate in 4^(K-1) at p imply gate in 4^K at a RELATED p?
# Specifically: CommonTwo(K-1) at position p --> CommonTwo(K) at position p? p-1? p+1?
lift_same = 0; lift_pm1 = 0; total = 0
for K in range(6, 300):
    if K == 8: continue  # K-1 = 7 exceptional
    p0 = firstp(K-1)
    p1 = firstp(K)
    if p0 is None or p1 is None: continue
    total += 1
    if p1 == p0: lift_same += 1
    if abs(p1 - p0) <= 1: lift_pm1 += 1
print(f"of {total}: same p: {lift_same}, |diff|<=1: {lift_pm1}")

# relationship between firstp(K-1), firstp(K), firstp(K+1) for a range
for K in [10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]:
    print(f"K={K}: firstp(K-1)={firstp(K-1)}, firstp(K)={firstp(K)}")
