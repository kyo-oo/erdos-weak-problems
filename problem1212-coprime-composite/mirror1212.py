#!/usr/bin/env python3
"""EXACT python mirror of the Lean E1212 defs (Kernel 65) — certifies every
decide row of Erdos1212.lean BEFORE the CI run (fuel bounds, sweeps,
censuses, walks, directed deaths). Run from anywhere."""

def gcdF(fuel, a, b):
    if fuel == 0:
        return b
    if a == 0:
        return b
    if b == 0:
        return a
    if b < a:
        return gcdF(fuel - 1, b, a)
    if b % a == 0:
        return a
    return gcdF(fuel - 1, b % a, a)

def gcdB(a, b):
    return gcdF(2 * (a + b) + 2, a, b)

def coprimeB(a, b):
    return gcdB(a, b) == 1

def compU(fuel, d, n):
    if fuel == 0:
        return False
    if d * d <= n:
        return (n % d == 0) or compU(fuel - 1, d + 1, n)
    return False

def compB(n):
    return compU(n + 2, 2, n)

def habitatB(v):
    x, y = v
    return (x >= 2) and (y >= 2) and coprimeB(x, y) and (compB(x) or compB(y))

def adjB(v, w):
    x1, y1 = v
    x2, y2 = w
    return (x1 == x2 and (y2 == y1 + 1 or y1 == y2 + 1)) or \
           (y1 == y2 and (x2 == x1 + 1 or x1 == x2 + 1))

def nbrs(v):
    x, y = v
    return [(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)]

def countB(p, l):
    r = 0
    for z in l:
        if p(z):
            r += 1
    return r

def degB(v):
    return countB(habitatB, nbrs(v))

def pairEqB(v, w):
    return v[0] == w[0] and v[1] == w[1]

def memB(v, l):
    for w in l:
        if pairEqB(v, w):
            return True
    return False

def adjToB(v, l):
    for w in l:
        if adjB(v, w):
            return True
    return False

def walkOK(l):
    if not l:
        return True
    if len(l) == 1:
        return habitatB(l[0])
    return habitatB(l[0]) and adjB(l[0], l[1]) and walkOK(l[1:])

def allDistinct(l):
    for i in range(len(l)):
        for j in range(i + 1, len(l)):
            if pairEqB(l[i], l[j]):
                return False
    return True

def liveB(k, x, y):
    if k == 0:
        return habitatB((x, y))
    return habitatB((x, y)) and (liveB(k - 1, x + 1, y) or
                                 liveB(k - 1, x, y + 1))

if __name__ == "__main__":
    ok = True

    def chk(name, got, want):
        global ok
        good = got == want
        ok = ok and good
        print(("PASS" if good else "FAIL"), name, "=", got,
              ("(want %s)" % want) if not good else "")

    # habitat anchor rows (battery §1)
    for v in [(9, 25), (15, 49), (203, 10201), (301, 10205)]:
        chk("habitatB %s" % (v,), habitatB(v), True)
    for n in [9, 25, 203, 301, 10201, 10205]:
        chk("compB %d" % n, compB(n), True)
    chk("coprimeB 9 25", coprimeB(9, 25), True)
    chk("coprimeB 15 49", coprimeB(15, 49), True)
    chk("coprimeB 203 10201", coprimeB(203, 10201), True)
    chk("coprimeB 301 10205", coprimeB(301, 10205), True)

    # degree table (battery §3)
    for v, want in [((9, 25), 2), ((8, 25), 2), ((8, 27), 1), ((15, 49), 1),
                    ((16, 49), 2), ((19, 49), 4), ((203, 10201), 3),
                    ((204, 10201), 2), ((301, 10205), 2)]:
        chk("degB %s" % (v,), degB(v), want)

    # component lists (battery §2 / battery1212b BFS orders)
    c49 = [(4, 9), (5, 9), (5, 9), (5, 8)] if False else [(4, 9), (5, 9), (5, 8)]
    c925 = [(9, 25), (8, 25), (9, 26), (7, 25), (6, 25), (7, 26), (7, 24), (7, 27), (8, 27)]
    c1516 = [(15, 16), (15, 17), (16, 17), (14, 17)]
    c2527 = [(25, 27), (26, 27), (25, 28), (25, 26), (25, 29), (26, 29), (24, 29),
             (27, 29), (28, 29), (27, 28)]
    c15949 = [(15, 49), (16, 49), (17, 49), (18, 49), (17, 50), (17, 48), (19, 49),
              (20, 49), (19, 50), (19, 48), (19, 51), (20, 51), (19, 52)]
    for name, lst in [("c49", c49), ("c925", c925), ("c1516", c1516),
                      ("c2527", c2527), ("c15949", c15949)]:
        chk("%s all habitat" % name, all(habitatB(v) for v in lst), True)
        chk("%s distinct" % name, allDistinct(lst), True)

    # no-exit ring sweep (36 cells around the (9,25) component)
    cells = [(5 + dx, 23 + dy) for dx in range(6) for dy in range(6)]
    noexit = all((not (habitatB(c) and adjToB(c, c925))) or memB(c, c925)
                 for c in cells)
    chk("comp925 no-exit ring (36 cells)", noexit, True)

    # phase rows (battery §4)
    chk("phase15 sweep k<5", all(coprimeB(15 + k, 49) for k in range(5)), True)
    chk("wall 21 49", coprimeB(21, 49), False)
    chk("clean 20 49", coprimeB(20, 49), True)
    chk("wall 301 10206", coprimeB(301, 10206), False)
    chk("clean 301 10207", coprimeB(301, 10207), True)
    chk("phase203 sweep k<99", all(coprimeB(203 + k, 10201) for k in range(99)), True)
    chk("wall 303 10201", coprimeB(303, 10201), False)
    chk("wall 404 10201", coprimeB(404, 10201), False)

    # p103 (the two-phase witness)
    p103 = [(x, 10201) for x in range(203, 302)] + \
           [(301, y) for y in range(10202, 10206)]
    chk("p103 walkOK", walkOK(p103), True)
    chk("p103 distinct", allDistinct(p103), True)
    chk("p103 len", len(p103), 103)

    # small walks
    p7 = [(9, 26), (9, 25, 29)] if False else [(9, 26), (9, 25), (8, 25), (7, 25, 27)] if False else \
         [(9, 26), (9, 25), (8, 25), (7, 25), (7, 26), (7, 27), (8, 27)]
    p8 = [(15, 49), (16, 49), (17, 49), (18, 49), (19, 49), (19, 50), (19, 51), (20, 51)]
    p6 = [(9, 25), (8, 25), (7, 25), (7, 26), (7, 27), (8, 27)]
    for name, lst in [("p7", p7), ("p6", p6)] if False else [("p7", p7), ("p8", p8), ("p6", p6)]:
        chk("%s walkOK" % name, walkOK(lst), True)
        chk("%s distinct" % name, allDistinct(lst), True)

    # directed death rows (battery1212b §2)
    dd = [(2, 9, 25), (2, 25, 9), (3, 15, 16), (6, 25, 27), (8, 9, 49),
          (6, 21, 25), (6, 27, 25), (2, 33, 25), (2, 25, 33), (2, 27, 49),
          (1, 35, 27), (2, 9, 121)]
    for k, x, y in dd:
        chk("liveB %d %d %d" % (k, x, y), liveB(k, x, y), False)

    print()
    print("MIRROR VERDICT:", "ALL GREEN" if ok else "RED — FIX BEFORE CI")
