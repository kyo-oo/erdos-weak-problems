#!/usr/bin/env python3
"""GST V2 handwritten-seed experiment.

No external packages.  This file checks exact finite arithmetic identities only.
It does NOT claim the final prefix-one theorem.
"""

from __future__ import annotations


def A(s: int) -> int:
    return 4 ** (3 ** s)


def c(s: int) -> int:
    return (A(s) - 1) // (3 ** (s + 1))


def z(s: int) -> int:
    cs = c(s)
    assert cs % 3 == 1
    return (cs - 1) // 3


def Q(s: int, b: int) -> int:
    if b == 0:
        return 0
    As = A(s)
    return c(s) * ((As ** b - 1) // (As - 1))


def h(s: int) -> int:
    return (2 ** (3 ** s) + 1) // (3 ** (s + 1))


def x2_mass(R: int, p: int) -> int:
    """m = binary carry + 2*ternary input digit for R -> 2R at row p."""
    d = (R // (3 ** p)) % 3
    if p == 0:
        carry = 0
    else:
        carry = (2 * (R % (3 ** p))) // (3 ** p)
    assert carry in (0, 1)
    return carry + 2 * d


def x2_event(m: int) -> str:
    d = m // 2
    # unique inverse m=a+2d with a in {0,1}
    a = m - 2*d
    # easier brute inverse because integer division above is wrong for odd m>=3
    for aa in (0, 1):
        for dd in (0, 1, 2):
            if aa + 2*dd == m:
                e = m % 3
                if dd == 2 and e == 2:
                    return "SURVIVE"
                if dd != 2 and e == 2:
                    return "CREATE"
                if dd == 2 and e != 2:
                    return "DESTROY"
                return "NEITHER"
    raise AssertionError(m)


def x4_cell(C: int, d: int):
    assert 0 <= C < 4 and 0 <= d < 3
    a, b = divmod(C, 2)
    m1 = a + 2*d
    e = m1 % 3
    ap = m1 // 3
    m2 = b + 2*e
    f = m2 % 3
    bp = m2 // 3
    Cp = 2*ap + bp
    event = (
        "SURVIVE" if d == 2 and f == 2 else
        "CREATE" if d != 2 and f == 2 else
        "DESTROY" if d == 2 and f != 2 else
        "NEITHER"
    )
    return m1, m2, f, Cp, event


def check_x_minus_six_fibre():
    fibre = []
    for C in range(4):
        for d in range(3):
            m1, m2, f, Cp, event = x4_cell(C, d)
            xcoord = m1 + m2
            zor = m2 - m1
            zsym = m1*m2
            if xcoord == 6:
                fibre.append((C,d,m1,m2,zor,zsym,event))
    assert fibre == [
        (0,1,2,4,+2,8,"NEITHER"),
        (0,2,4,2,-2,8,"SURVIVE"),
    ]
    return fibre


def check_half_phase_dual_tower(max_s: int = 6):
    out = []
    for s in range(1, max_s+1):
        hs = h(s)
        cs = c(s)
        assert 2 ** (3 ** s) == -1 + 3 ** (s+1) * hs
        assert cs == 3 ** (s+1) * hs*hs - 2*hs
        assert hs % 9 == 1
        assert cs % 9 == 7
        if s < max_s:
            hnext = h(s+1)
            assert hnext == hs - 3 ** (s+1)*hs*hs + 3 ** (2*s+1)*hs*hs*hs
        out.append((s, hs % 243, cs % 243))
    return out


def check_universal_six_cycle(max_s: int = 6):
    expected_pairs = [
        (0,0),
        (1,3),
        (2,4),
        (5,5),
        (4,2),
        (3,1),
    ]
    rows = []
    for s in range(1, max_s+1):
        N = 3 ** s
        p = s + 1
        M = 3 ** (s+2)
        B = pow(2, N, M)
        assert B == 3 ** (s+1) - 1
        pairs = []
        for j in range(6):
            R = pow(B, j, M)
            m1 = x2_mass(R, p)
            m2 = x2_mass((2*R) % M, p)
            pairs.append((m1,m2))
        assert pairs == expected_pairs
        rows.append((s,p,pairs))
    return rows


def check_Q_modulus(t: int, b: int, m: int):
    assert m > 0
    return Q(t,b) % Q(t,m) == Q(t,b % m)


def check_origin_modulus_samples():
    for t in range(1,4):
        for m in [2,3,6,9,12,36]:
            for b in range(0,40):
                assert check_Q_modulus(t,b,m)
    return True


def origin_transfer(s: int, n: int):
    """Consume only the finite nonzero origin word.

    State X = alpha + beta*Q(ell,n), with parent initial values.
    Returns rows plus final beta exponent E such that beta=4^E.
    """
    ell = s+1
    nn = n
    alpha = z(s)
    beta = A(s)
    beta_exp = 3 ** s
    C = 1
    rows = []
    while nn > 0:
        r = nn % 3
        q = nn // 3
        qr = Q(ell,r)
        d = (alpha + beta*qr) % 3
        e = (4*d + C) % 3
        Cp = (4*d + C) // 3
        alpha_p = (alpha + beta*qr - d) // 3
        multiplier = A(ell) ** r
        beta_p = beta * multiplier
        beta_exp_p = beta_exp + r * (3 ** ell)
        rows.append({
            "ell": ell,
            "n": nn,
            "r": r,
            "C": C,
            "d": d,
            "e": e,
            "Cp": Cp,
            "alpha_mod_27": alpha % 27,
            "beta_exp": beta_exp,
        })
        ell += 1
        nn = q
        alpha = alpha_p
        beta = beta_p
        beta_exp = beta_exp_p
        C = Cp
    assert beta_exp == 3 ** s * (1 + 3*n)
    return rows, beta_exp, alpha, C


def scale_residues(n: int, max_k: int = 6):
    return [n % (6 ** k) for k in range(1,max_k+1)]


def spacetime_origin_grid(n: int, max_t: int = 12, max_k: int = 6):
    """Pure origin coordinate grid behind product_t sum_k 6^k."""
    out = []
    nn = n
    for t in range(max_t):
        out.append((t, nn, scale_residues(nn,max_k)))
        nn //= 3
        if nn == 0:
            out.append((t+1,0,[0]*max_k))
            break
    return out


def main():
    print("x=6 fibre:")
    for row in check_x_minus_six_fibre():
        print(" ",row)

    print("\nHalf-phase h/c checks:")
    for row in check_half_phase_dual_tower():
        print(" ",row)

    print("\nUniversal six-cycle:")
    for s,p,pairs in check_universal_six_cycle():
        print(f"  s={s}, row={p}: {pairs}")

    print("\nQ modulus law samples:", check_origin_modulus_samples())

    print("\nOrigin transfer samples:")
    for n in [1,2,4,5,7,10]:
        rows,bexp,alpha,C = origin_transfer(1,n)
        print(f"  n={n}: trits={[r['r'] for r in rows]}, beta exponent={bexp}, terminal alpha mod27={alpha%27}, C={C}")

    print("\nproduct_t / sum_k coordinate grid example n=100:")
    for row in spacetime_origin_grid(100):
        print(" ",row)


if __name__ == "__main__":
    main()
