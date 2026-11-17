def digit(n, p):
    return (n // (3**p)) % 3

# verify periodicity: digit_p(4^K) depends only on K mod 3^p
ok = True
for p in range(1, 8):
    mod = 3**p
    base = [digit(4**r, p) for r in range(mod)]
    for K in range(mod, mod*3):
        if digit(4**K, p) != base[K % mod]:
            ok = False
            print("periodicity fails", p, K)
print("periodicity holds:", ok)

# f_p(r) for r < 3^p is digit p of 4^r; digit p of 4^K = f_p(K mod 3^p)
# CommonTwo at p for K: f_p(K mod 3^p) = 2 and f_p((K mod 3^p + 1) mod 3^p) = 2
def f(p, r):
    return digit(4**r, p)

def common_two_at(p, r):
    # r in [0, 3^p): does K = r (as exponent) have digit p = 2 in 4^K and 4^(K+1)?
    return f(p, r) == 2 and f(p, (r+1) % 3**p) == 2

# survivor tree
surv = [0]  # level 0: single residue 0 (mod 1)
for p in range(1, 12):
    mod = 3**p
    new = []
    for r in surv:
        for t in range(3):
            cand = r + t * 3**(p-1)
            if not common_two_at(p, cand % mod):
                new.append(cand)
    # also need: covered = in S_q for some q <= p. survivors = not covered at ANY q <= p
    # note: survivors at level p are extensions of survivors at level p-1 NOT newly covered at p
    surv = new
    print(f"level {p}: {len(surv)} survivors mod 3^{p} = {mod}")
    if p <= 6:
        print("   ", sorted(surv))
    else:
        print("   ", sorted(surv)[:20], "...")
