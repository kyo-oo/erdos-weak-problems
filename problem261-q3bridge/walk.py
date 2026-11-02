#!/usr/bin/env python3
"""#261: (1) walk frontier extension, (2) min-room census, (3) the Q2=>Q3 reduction data.
Walk: v_{N+1} = (2 v_N) mod N ... take iff 2v >= N. Start (n+1, n) for n >= 2, (3,2) for n=1."""
import sys
from collections import defaultdict

def walk_terminates(n, cap_steps=20000):
    if n == 1:
        N, v = 3, 2
    else:
        N, v = n + 1, n
    for _ in range(cap_steps):
        if v == 0:
            return True, N
        if 2 * v >= N:
            v = 2 * v - N
        else:
            v = 2 * v
        N += 1
        if v > (1 << 62):  # runaway guard
            return False, None
    return False, None

def walk_witness(n, cap_steps=20000):
    """return the taken set (pieces) if terminates."""
    if n == 1:
        N, v = 3, 2
    else:
        N, v = n + 1, n
    taken = []
    for _ in range(cap_steps):
        if v == 0:
            return taken
        if 2 * v >= N:
            v = 2 * v - N
            taken.append(N)
        else:
            v = 2 * v
        N += 1
        if v > (1 << 62):
            return None
    return None

def main():
    mode = sys.argv[1]
    if mode == "frontier":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        bad = []
        maxlen = 0; maxn = 0
        for n in range(lo, hi + 1):
            ok, _ = walk_terminates(n)
            if not ok:
                bad.append(n)
        print(f"walk termination {lo}..{hi}: {'ALL TERMINATE' if not bad else 'FAILURES: ' + str(bad[:20])}")
    elif mode == "room":
        # min-room census: for each n, the max piece of the greedy witness (room = maxpiece - n)
        hi = int(sys.argv[2])
        rooms = {}
        worst = []
        for n in range(1, hi + 1):
            w = walk_witness(n)
            if w is None:
                print(f"n={n}: NO WITNESS"); continue
            mx = max(w) if w else n
            room = mx - n
            rooms[n] = (room, len(w), mx)
            worst.append((room, n, len(w), mx))
        worst.sort(reverse=True)
        print("worst rooms (room, n, pieces, maxpiece):", worst[:15])
        rs = [rooms[n][0] for n in rooms]
        import statistics
        print("max room:", max(rs), " mean:", round(statistics.mean(rs),2))
        # distribution
        from collections import Counter
        c = Counter(rs)
        print("room histogram (top):", c.most_common(12))
    elif mode == "q3data":
        # the AP-toggle assembly: for T = 20..64, check every n in [N0, N0+3T] has witness with all pieces <= n+T
        # (the bounded-room hypothesis needed for the Q2=>Q3 theorem)
        T = int(sys.argv[2]); N0 = int(sys.argv[3]); cnt = int(sys.argv[4])
        okall = True
        for n in range(N0, N0 + cnt):
            w = walk_witness(n)
            if w is None or (w and max(w) > n + T):
                okall = False
                print(f"n={n}: room = {max(w)-n if w else None} > T={T}")
        print(f"bounded-room(T={T}) for n in [{N0},{N0+cnt}): {'HOLDS' if okall else 'FAILS'}")

if __name__ == "__main__":
    main()
