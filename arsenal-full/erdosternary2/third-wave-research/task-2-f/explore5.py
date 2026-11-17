def d(p, x):
    return (4**x // (3**p)) % 3

# S_p = residues x mod 3^p with d(p,x)=2 and d(p,(x+1)%3^p)=2
for p in range(2, 8):
    M = 3**p
    S = [x for x in range(M) if d(p,x)==2 and d(p,(x+1)%M)==2]
    print(f"S_{p} ({len(S)} classes mod {M}): {S}")

# naturals in survivors at high levels
def survives_all_levels_upto(K, P):
    for p in range(1, P+1):
        M = 3**p
        if d(p, K)==2 and d(p,(K+1)%M)==2:
            return False, p
    return True, None

# max first_p for K in 5..2000
mx = 0; arg = 0
for K in range(5, 2000):
    if K == 7: continue
    ok, p = survives_all_levels_upto(K, 2*K+3)
    assert ok == False
    if p > mx: mx, arg = p, K
print("max first_p for K<2000:", mx, "at K =", arg)

# survivors at level p intersect [0,3000)
for p in [8, 10, 12, 14]:
    M = 3**p
    nat_surv = [K for K in range(0, 3000) if survives_all_levels_upto(K, p)[0]]
    print(f"naturals < 3000 surviving through level {p}: {nat_surv}")
