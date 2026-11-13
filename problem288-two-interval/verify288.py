# Mirror the EXACT Lean defs to be authored in Erdos288.lean:
# wprod a b = product of [a..b] (empty -> 1) via right-recursion
# hnum a b = numerator of sum_{i in [a,b]} 1/i over the product denominator
def wprod(a, b):
    r = 1
    for i in range(a, b + 1):
        r *= i
    return r

def hnum(a, b):
    if b < a: return 0
    h, p = 0, 1
    for i in range(a, b + 1):
        h = h * i + p
        p = p * i
    return h

def equalWindow(a, b, c, d):
    return hnum(a, b) * wprod(c, d) == hnum(c, d) * wprod(a, b)

# 1. ANCHORS (theorem anchor_values):
print("hnum 2 4 =", hnum(2, 4), "wprod 2 4 =", wprod(2, 4))
print("hnum 3 5 =", hnum(3, 5), "wprod 3 5 =", wprod(3, 5))
print("hnum 6 9 =", hnum(6, 9), "wprod 6 9 =", wprod(6, 9))
print("hnum 4 7 =", hnum(4, 7), "wprod 4 7 =", wprod(4, 7))

# 2. Bounded census mirror: e288_no_disjoint_pair_le12
bad = []
for a in range(0, 13):
    for b in range(0, 13):
        for c in range(0, 13):
            for d in range(0, 13):
                if 1 <= a and a <= b and b < c and c <= d and equalWindow(a, b, c, d):
                    bad.append((a, b, c, d))
print("disjoint-equal pairs with endpoints <= 12:", bad)

# 3. Bounded census mirror: e288_single_never_right_le24 (n <= 10, c,d <= 24)
bad2 = []
for n in range(0, 11):
    for c in range(0, 25):
        for d in range(0, 25):
            if 1 <= n and n < c and c <= d and equalWindow(n, n, c, d):
                bad2.append((n, c, d))
print("single-vs-right pairs (n<=10, c,d<=24):", bad2)

# 4. trivial family sanity
print("equalWindow a b a b samples:", [equalWindow(x, y, x, y) for (x, y) in [(2, 4), (3, 5), (1, 1), (6, 9)]])
# 5. bridge arithmetic
print("26 % 3 =", 26 % 3, "; 24^2-1 =", 24**2 - 1, "; (24-1)*(24+1) =", (24-1)*(24+1))
print("(60 % (47*2)) % 47 =", (60 % (47*2)) % 47, "; 60 % 47 =", 60 % 47)
print("empty window: hnum 5 3 =", hnum(5, 3), "wprod 5 3 =", wprod(5, 3))
