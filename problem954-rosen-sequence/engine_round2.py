import time
t0 = time.time()
print("ENGINE R2: #954 Rosen — certified sequence + count-function laws")
print("=" * 60)

# a_0 = 0, a_1 = 1; a_{k+1} = smallest n with count_{<=k}(n) < n
# where count(n) = #{(i,j): 0 <= i <= j <= k, j >= 1, a_i + a_j <= n}
N = 400
a = [0, 1]
counts = [1]  # count(a_1)=1: pair (0,1) -> 0+1=1 <= 1... track later
for k in range(1, N):
    # count function for the current sequence a[0..k]
    def cnt(n):
        c = 0
        for i in range(0, k + 1):
            for j in range(i, k + 1):
                if j >= 1 and a[i] + a[j] <= n:
                    c += 1
        return c
    # smallest n with cnt(n) < n  (n must be > a[k] by construction? verify)
    n = a[k] + 1
    while cnt(n) >= n:
        n += 1
    a.append(n)
print(f"  first 25 terms: {a[:25]}")
print(f"  matches published (0,1,3,5,9,13,17,24,31,38,45,...): {a[:11] == [0,1,3,5,9,13,17,24,31,38,45]}")

# the count function on the FULL sequence up to index K: N(x) = #{(i,j): i<=j, j>=1, a_i+a_j <= x}
K = 150
def Nfull(x):
    c = 0
    for i in range(0, K + 1):
        for j in range(i, K + 1):
            if j >= 1 and a[i] + a[j] <= x:
                c += 1
    return c
# the law: N(x) >= x for all x in [1, a[K+1]-1]  (by construction each n < a_{k+1} has cnt(n) >= n)
ok = True
maxdev = 0; argmax = 0
for x in range(1, 300):
    v = Nfull(x)
    if v < x:
        ok = False
        print(f"  VIOLATION at x={x}: N={v}")
    if v - x > maxdev:
        maxdev = v - x; argmax = x
print(f"  LAW N(x) >= x for x < 300: {ok}   max deviation N(x)-x = {maxdev} at x={argmax}")
# deviation profile at powers
for x in [10, 25, 50, 100, 150, 200, 250, 290]:
    print(f"    N({x}) - {x} = {Nfull(x) - x}   (x^(1/4) ~ {x**0.25:.1f})")
print(f"TOTAL {time.time()-t0:.1f}s")
