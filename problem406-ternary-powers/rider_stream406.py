#!/usr/bin/env python3
"""
KERNEL S095 RECEIPT — THE SIX-RIDER-STREAM X-RAY (two-method, exact big-int)

The S095 kernel (MonolithGate/MahlerRider406.lean) proves:
  * every rider rides from depth zero (the global pin),
  * at most one rider per head; at most six riders in the universe,
  * MahlerSharp <=> no rider at the six heads {1,2,4,5,7,8},
  * the depth ladder: u = a (mod 3), u = 4a (mod 9), u = 11(2a-9) (mod 27),
    32u = 2a-9 (mod 81) at every depth s >= 3.

This receipt computes, TWO INDEPENDENT WAYS, the six residue streams
uhat(a) — the unique residues mod 3^(s+1) pinned by the rider
divisibility 3^(s+1) | 2*u*c_s - (2a-9) — and cross-checks them:

  METHOD A (the ladder): uhat_s = m * (2*c_s)^(-1) mod 3^(s+1), with
    c_s = (4^(3^s) - 1) / 3^(s+1) evaluated by modular exponentiation.

  METHOD B (the diagonal): the frozen diagonal L = lim c_s computed by
    the log series  L = sum_{n>=1} (-1)^(n+1) * 3^(n-1) / n  (exact
    3-adic evaluation mod 3^K), then uhat(m) = m * (2L)^(-1) mod 3^K.

Both methods must agree at every depth for all six heads.  The
identification L = lim c_s is verified at every depth (c_s = L mod
3^(s+1)), and the S092/S094 pinned values of the frozen diagonal
(7 mod 9, 16 mod 27, 16 mod 81, 178 mod 243) are re-derived.

FINITE KILL CERTIFICATE: for each head m, if the pinned depth-D residue
u0 = uhat_D(m) FAILS the depth-(D+1) divisibility, then NO RIDER BELOW
3^(D+1) EXISTS for that head (a rider u < 3^(D+1) is pinned to u0 at
depth D, and must survive depth D+1).
"""

import sys

D = 40  # max depth (streams computed mod 3^(s+1) for s = 0..D)

HEADS = [1, 2, 4, 5, 7, 8]  # the six admissible heads


def v3(n: int) -> int:
    v = 0
    while n % 3 == 0 and n > 0:
        n //= 3
        v += 1
    return v


def c_mod(s: int, M: int) -> int:
    """c_s mod M, for M = 3^k with k <= s+1 (enough precision)."""
    # 4^(3^s) - 1 = 3^(s+1) * c_s  (v3 exactly s+1)
    # Work mod 3^(2s+2): the residue of 4^(3^s)-1 there is
    # 3^(s+1) * (c_s mod 3^(s+1)).
    mod_full = 3 ** (2 * s + 2)
    num = (pow(4, 3 ** s, mod_full) - 1) % mod_full
    return (num // 3 ** (s + 1)) % M


def c_mod_hi(s: int, k: int) -> int:
    """c_s mod 3^k for arbitrary k (needs mod 3^(s+1+k) window)."""
    mod_full = 3 ** (s + 1 + k)
    num = (pow(4, 3 ** s, mod_full) - 1) % mod_full
    return (num // 3 ** (s + 1)) % (3 ** k)


def L_mod(K: int) -> int:
    """The frozen diagonal L = sum (-1)^(n+1) 3^(n-1)/n, mod 3^K."""
    M = 3 ** K
    total = 0
    # terms with v3 = n-1-v3(n) >= K vanish
    for n in range(1, 2 * K + 3):
        v = v3(n)
        e = n - 1 - v
        if e >= K:
            continue
        np_ = n // 3 ** v
        term = (1 if (n + 1) % 2 == 0 else -1) * (3 ** e) * pow(np_, -1, M)
        total += term
    return total % M


def main() -> int:
    ok = True
    print(f"=== KERNEL S095 RECEIPT: the six rider streams, depth {D} ===")
    print(f"heads: {HEADS}   (m = 2a-9 = "
          f"{[2*a-9 for a in HEADS]})")

    # --- sanity: c values and the tower-limit identification ---
    checks = []
    checks.append(("c_0 = 1", c_mod(0, 3) == 1))
    checks.append(("c_1 = 7", c_mod(1, 3 ** 2) == 7))
    checks.append(("c_2 = 9709", c_mod_hi(2, 8) == 9709 % 3 ** 8))
    checks.append(("c_s % 9 = 7 for 1<=s<=D",
                   all(c_mod(s, 9) == 7 for s in range(1, D + 1))))
    checks.append(("c_s % 81 = 16 for 3<=s<=D",
                   all(c_mod(s, 81) == 16 for s in range(3, D + 1))))
    # tower-limit identification: c_s = L mod 3^(s+1)
    ident = all(c_mod(s, 3 ** (s + 1)) == L_mod(s + 1) for s in range(0, D + 1))
    checks.append(("c_s = L mod 3^(s+1) for all s<=D (tower-limit id)", ident))
    # the S092/S094 pinned values of the frozen diagonal
    checks.append(("L = 7 mod 9", L_mod(2) == 7))
    checks.append(("L = 16 mod 27", L_mod(3) == 16))
    checks.append(("L = 16 mod 81", L_mod(4) == 16))
    checks.append(("L = 178 mod 243", L_mod(5) == 178))
    for name, res in checks:
        print(f"  [{'PASS' if res else 'FAIL'}] {name}")
        ok &= res

    # --- the six streams, method A, with nesting verification ---
    print("\n--- METHOD A: the ladder (uhat_s = m*(2c_s)^-1 mod 3^(s+1)) ---")
    streams = {}
    for a in HEADS:
        m = 2 * a - 9
        res = []
        for s in range(0, D + 1):
            M = 3 ** (s + 1)
            cs = c_mod(s, M)
            u = (m % M) * pow((2 * cs) % M, -1, M) % M
            res.append(u)
        streams[a] = res
        # nesting: uhat_{s+1} = uhat_s mod 3^(s+1)
        nesting = all(res[s + 1] % 3 ** (s + 1) == res[s]
                      for s in range(0, D))
        low = [res[0], res[1], res[2], res[3], res[4], res[5]]
        print(f"  head a={a} (m={m:+d}): depth 0..5 residues {low}, "
              f"nesting {'OK' if nesting else 'BROKEN'}, "
              f"uhat_D = {res[D]}")
        ok &= nesting

    # --- cross-check with method B (the diagonal) ---
    print("\n--- METHOD B: the diagonal (uhat = m*(2L)^-1 mod 3^K) ---")
    for a in HEADS:
        m = 2 * a - 9
        agree = True
        for s in range(0, D + 1):
            K = s + 1
            M = 3 ** K
            L = L_mod(K)
            uB = (m % M) * pow((2 * L) % M, -1, M) % M
            if uB != streams[a][s]:
                agree = False
                print(f"  MISMATCH head {a} depth {s}: A={streams[a][s]} B={uB}")
                break
        print(f"  head a={a}: methods A and B agree at every depth 0..{D}"
              f" {'PASS' if agree else 'FAIL'}")
        ok &= agree

    # --- the mod-81 six-residue pin (the kernel's depth-3 uniform law) ---
    print("\n--- the mod-81 six-residue pin (kernel rider_c_mod81_pin) ---")
    expect81 = {1: 58, 2: 53, 4: 43, 5: 38, 7: 28, 8: 23}
    for a in HEADS:
        got = streams[a][3]  # depth 3 -> mod 3^4 = 81
        good = got == expect81[a]
        print(f"  head a={a}: uhat mod 81 = {got} "
              f"(expected {expect81[a]}) {'PASS' if good else 'FAIL'}")
        ok &= good

    # --- the depth-2 six-residue pin (kernel rider_six_family_pin) ---
    print("\n--- the mod-27 six-class pin (kernel rider_six_family_pin) ---")
    expect27 = {1: 4, 2: 26, 4: 16, 5: 11, 7: 1, 8: 23}
    for a in HEADS:
        got = streams[a][2]  # depth 2 -> mod 27
        good = got == expect27[a]
        print(f"  head a={a}: uhat mod 27 = {got} "
              f"(expected {expect27[a]}) {'PASS' if good else 'FAIL'}")
        ok &= good

    # --- FINITE KILL: no rider below 3^(s+1), per head (adaptive depth) ---
    print("\n--- FINITE KILL CERTIFICATE (adaptive depth, base D = %d) ---" % D)
    all_killed = True
    EXT = 10  # adaptive extension budget
    for a in HEADS:
        m = 2 * a - 9
        # extend the stream past D until the kill lands (or budget out)
        res_ext = {s: streams[a][s] for s in range(len(streams[a]))}
        kill = None
        for s in range(D, D + EXT):
            u0 = res_ext[s]
            M1 = 3 ** (s + 2)
            cs1 = c_mod_hi(s + 1, s + 2)
            if (2 * u0 * cs1 - m) % M1 != 0:
                kill = s + 1
                break
            # stream continues: lift to depth s+1
            Mn = 3 ** (s + 2)
            csn = c_mod_hi(s + 1, s + 2)
            res_ext[s + 1] = (m % Mn) * pow((2 * csn) % Mn, -1, Mn) % Mn
        if kill is not None:
            all_killed = all_killed and True
            print(f"  head a={a} (m={m:+d}): pinned u0 = {res_ext[kill - 1]}; "
                  f"depth-{kill} check FAILS for u0 -> "
                  f"NO RIDER BELOW 3^{kill} AT HEAD {a}")
        else:
            all_killed = False
            print(f"  head a={a} (m={m:+d}): stream coherent through depth "
                  f"{D + EXT}; extend further")

    print("\n=== VERDICT ===")
    if ok:
        print("ALL TWO-METHOD CROSS-CHECKS PASS: the six streams are pinned,")
        print("nested, and diagonal-identified; L = lim c_s is re-derived at")
        print("every depth; the S092/S094 pins hold; the kernel's mod-27 and")
        print("mod-81 residue laws are machine-confirmed.  The socket is now")
        print("SIX EXPLICIT 3-ADIC STREAMS; killing each stream's termination")
        print("kills MahlerSharp.")
        if all_killed:
            print(f"FINITE KILL LANDED: no rider u < 3^{D+1} at ANY head.")
        else:
            print("Some heads' depth-(D+1) checks survived: extend D.")
        return 0
    print("RECEIPT FAILURE — a cross-check broke.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
