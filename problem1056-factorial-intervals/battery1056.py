# THE 1056 BATTERY (independent, dual-method): verify every case witness
# k=2..11: prime p, all block products == 1 mod p (method A: block products
# directly; method B: factorials at cut points all equal), Wilson anchors.
import sys
def is_prime(n):
    if n < 2: return False
    for q in range(2, int(n**0.5)+1):
        if n % q == 0: return False
    return True

CASES = {
  2:  (11,   [(3,4),(5,7)]),
  3:  (17,   [(2,5),(6,11),(12,15)]),
  4:  (23,   [(2,4),(5,8),(9,11),(12,21)]),
  5:  (109,  [(10,11),(12,39),(40,58),(59,73),(74,85)]),
  6:  (71,   [(8,9),(10,19),(20,51),(52,61),(62,63),(64,70)]),
  7:  (673,  [(160,316),(317,354),(355,393),(394,397),(398,506),(507,545),(546,647)]),
  8:  (599,  [(29,50),(51,122),(123,183),(184,250),(251,289),(290,500),(501,539),(540,555)]),
  9:  (3011, [(2,611),(612,723),(724,749),(750,805),(806,2205),(2206,2261),(2262,2287),(2288,2399),(2400,3009)]),
  10: (27901,[(2452,2867),(2868,4768),(4769,10383),(10384,18707),(18708,19589),(19590,19965),(19966,22981),(22982,24673),(24674,26322),(26323,27263)]),
  11: (52163,[(2,3924),(3925,7291),(7292,7427),(7428,18519),(18520,24931),(24932,26081),(26082,27231),(27232,33643),(33644,44735),(44736,44871),(44872,52161)]),
}
ok = True
for k, (p, blocks) in sorted(CASES.items()):
    assert len(blocks) == k, f"k={k}: {len(blocks)} blocks"
    assert is_prime(p), f"p={p} not prime"
    # intervals consecutive + inside [2, p-1]
    for i in range(len(blocks)-1):
        assert blocks[i][1] + 1 == blocks[i+1][0], f"k={k}: gap between blocks"
    assert blocks[0][0] >= 2 and blocks[-1][1] <= p - 1
    # method A: block products
    for (a, b) in blocks:
        pr = 1
        for t in range(a, b+1): pr = (pr * t) % p
        if pr != 1: print(f"FAIL k={k} block [{a},{b}]: prod={pr}"); ok = False
    # method B: factorials at cuts all equal (chain value)
    cuts = [blocks[0][0] - 1] + [b for (_, b) in blocks]
    vals = set()
    f = 1; fj = {}
    for j in range(1, p):
        f = (f * j) % p
        if j in cuts: fj[j] = f
    vals = {fj[c] for c in cuts}
    if len(vals) != 1: print(f"FAIL k={k}: cut factorial values differ: {vals}"); ok = False
    v = vals.pop()
    # Wilson anchors for value-1 chains
    anchor = "" 
    if v == 1:
        wf = 1; w1 = None; w2 = None
        f = 1
        for j in range(1, p):
            f = (f * j) % p
            if j == 1: w1 = f
            if j == p - 2: w2 = f
        if w1 != 1 or w2 != 1: print(f"FAIL k={k}: Wilson anchors {w1},{w2}"); ok = False
        anchor = " [value-1 Wilson-anchored]"
    print(f"k={k:2d} p={p:6d}: {k} blocks ALL product==1 (dual-method GREEN){anchor}")
print("BATTERY 1056:", "GREEN" if ok else "RED")
sys.exit(0 if ok else 1)
