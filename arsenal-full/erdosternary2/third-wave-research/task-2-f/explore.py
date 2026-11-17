import sys

def digits3(n):
    ds = []
    while n > 0:
        ds.append(n % 3)
        n //= 3
    return ds  # ds[p] = digit at position p

def digit(n, p):
    return (n // (3**p)) % 3

# 1. Verify CommonTwo for K in 5..3000
fail = []
first_p = {}
for K in range(5, 3000):
    a, b = 4**K, 4**(K+1)
    found = None
    # p can be at most ~1.26*K + 2
    for p in range(1, 2*K + 3):
        if digit(a, p) == 2 and digit(b, p) == 2:
            found = p
            break
    if found is None:
        fail.append(K)
    else:
        first_p[K] = found
print("failures in 5..2999:", fail)
print("sample first-p for K=5..40:", [first_p.get(K) for K in range(5, 41)])
