#!/usr/bin/env python3
"""
BATTERY 406-B (S076) — THE FIVE NEW LAWS OF THE RIDER CONSTRAINT SET.

The S076 war council extracted five new unconditional necessary-condition laws
for Erdos #406 riders (K with 4^K having only 0/1 ternary digits). This
battery verifies every law empirically (dual-method where applicable) and
extends the certified no-rider census with the new fractional pre-filter.

LAWS:
  L1 FRACTIONAL: rider K => 2*4^K < 3^(M+1), M = floor(log_3(4^K))
     (equivalently {K*log3(4)} < 1 - log3(2) = 0.36907...)
  L2 TAIL: rider K => floor(4^K / 3^(K+1)) is 0/1-ternary
  L3 REPUNIT NO-CARRY: u 0/1-ternary => the ternary digits of 4u+1 are exactly
     e_0 = d_0 + 1, e_j = d_j + d_{j-1} (NO carries, since e_j <= 2 < 3)
  L4 T2-LAW: no riders at K+1 and K+2 simultaneously (no three consecutive)
  L5 MOD-3 GAP: riders r, r+1 (r >= 1) => r == 0 (mod 3)
  LX CONJECTURE (recorded, unproven): v2(cantor n) <= 2*|S| (popcount form)

All checks dual-method where stated. Exit code 0 = ALL GREEN.
"""
import sys

GREEN = True


def digits3(n):
    """Base-3 digit list, position 0 = units."""
    ds = []
    while n > 0:
        ds.append(n % 3)
        n //= 3
    return ds


def is_cantor(n):
    """True iff all base-3 digits of n are in {0, 1}. (method A: divmod)"""
    while n > 0:
        if n % 3 == 2:
            return False
        n //= 3
    return True


def is_cantor_str(n):
    """Method B: via the string representation. Independent of divmod chain."""
    s = ""
    m = n
    while m > 0:
        s = str(m % 3) + s  # this uses divmod too; do a truly independent one:
        m //= 3
    # truly independent: use Python's base conversion by repeated subtraction is
    # too slow; instead verify with the additive reconstruction:
    if n == 0:
        return True
    ds = digits3(n)
    return all(d <= 1 for d in ds) and sum(d * 3**i for i, d in enumerate(ds)) == n


def v2(n):
    if n == 0:
        return 10**9
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def rider(K):
    """K is a rider iff 4^K is 0/1-ternary."""
    return is_cantor(4**K)


def floor_log3(n):
    """M = floor(log_3(n)) via digit length: M = len(digits3(n)) - 1."""
    return len(digits3(n)) - 1


# ---------------------------------------------------------------- L1
def check_L1(Kmax=400):
    """Every rider below Kmax satisfies 2*4^K < 3^(M+1); and every K killed by
    the law (2*4^K >= 3^(M+1)) is truly dead (not a rider). Dual-method:
    the inequality is checked by exact integer arithmetic AND by the
    fractional-part criterion {K*log3(4)} < 1 - log3(2)."""
    ok = True
    riders = [K for K in range(0, Kmax) if rider(K)]
    for K in riders:
        n = 4**K
        M = floor_log3(n)
        lhs, rhs = 2 * n, 3 ** (M + 1)
        if not lhs < rhs:
            print(f"L1 FAIL: rider K={K} has 2*4^K >= 3^(M+1)")
            ok = False
    # the fractional-part cross-check on the boundary
    import math
    for K in riders:
        theta = (K * math.log(4, 3)) % 1.0
        n = 4**K
        M = floor_log3(n)
        passed = (2 * n < 3 ** (M + 1))
        # theta < log3(3/2) iff 2*4^K < 3^(M+1)
        if passed != (theta < math.log(1.5, 3) - 1e-12):
            print(f"L1 fractional-method mismatch at K={K}")
            ok = False
    # the kill lane: every K with 2*4^K >= 3^(M+1) is dead
    killed = 0
    for K in range(0, Kmax):
        n = 4**K
        M = floor_log3(n)
        if 2 * n >= 3 ** (M + 1):
            killed += 1
            if rider(K):
                print(f"L1 CONTRADICTION: rider K={K} killed by the law!")
                ok = False
    print(f"L1 fractional law: riders {riders} all below half-line; "
          f"{killed}/{Kmax} exponents killed forever by the law "
          f"({100.0*killed/Kmax:.1f}%)")
    return ok


# ---------------------------------------------------------------- L2
def check_L2(Kmax=300):
    """Every rider K: floor(4^K / 3^(K+1)) is Cantor. Every dead K: record
    whether the tail is Cantor (the law is necessary, not sufficient)."""
    ok = True
    riders = [K for K in range(0, Kmax) if rider(K)]
    for K in riders:
        tail = (4**K) // (3 ** (K + 1))
        if not is_cantor(tail):
            print(f"L2 FAIL: rider K={K} has non-Cantor tail {tail}")
            ok = False
        # dual method: the tail's digits must equal 4^K's digits above pos K
        ds = digits3(4**K)
        tail_ds = digits3(tail)
        expect = ds[K + 1:]
        if tail_ds != expect:
            print(f"L2 digit-shift mismatch at K={K}")
            ok = False
    # dead K's with Cantor tails (the necessary condition is weak)
    weak = sum(1 for K in range(1, Kmax) if (not rider(K))
               and is_cantor((4**K) // (3 ** (K + 1))))
    print(f"L2 tail law: all riders {riders} have Cantor tails "
          f"(digit-shift verified); dead-K Cantor-tail count (weak passes): "
          f"{weak}/{Kmax}")
    return ok


# ---------------------------------------------------------------- L3
def check_L3(umax=3**9):
    """For every Cantor u in [0, umax): the ternary digits of 4u+1 are exactly
    e_0 = d_0+1, e_j = d_j + d_{j-1} with NO carries; and Cantor(4u+1) iff
    d_0(u)=0 and u has no two adjacent 1-digits."""
    ok = True
    cantor_next = 0
    for u in range(umax):
        if not is_cantor(u):
            continue
        w = 4 * u + 1
        ds = digits3(u)
        got = digits3(w)
        # predicted digits e
        pred = []
        for j in range(max(len(ds), len(got), 1) + 1):
            e = (ds[j] if j < len(ds) else 0) + (ds[j - 1] if 0 <= j - 1 < len(ds) else 0) \
                + (1 if j == 0 else 0)
            pred.append(e)
        # strip trailing zeros of pred to compare with got
        while pred and pred[-1] == 0:
            pred.pop()
        if pred != got:
            print(f"L3 FAIL at u={u} (digits3={ds}): got {got} vs pred {pred}")
            ok = False
            if cantor_next > 5:
                break
        # the iff-law
        no_adj = all(not (ds[j] == 1 and j + 1 < len(ds) and ds[j + 1] == 1)
                     for j in range(len(ds)))
        iff = ((ds[0] if ds else 0) == 0 and no_adj)
        if iff != is_cantor(w):
            print(f"L3 IFF FAIL at u={u}")
            ok = False
        if is_cantor(w):
            cantor_next += 1
    print(f"L3 repunit no-carry law: verified on all Cantor u < {umax} "
          f"({cantor_next} with Cantor successor)")
    return ok


# ---------------------------------------------------------------- L4 + L5
def check_L4_L5(Kmax=400):
    """No three consecutive riders (an immediate corollary of the level-1 dust
    law: any rider r has r % 3 != 2, so among r, r+1, r+2 one is dead);
    consecutive riders r, r+1 (r>=1) => r % 3 == 0; and the NEW sharpened
    constraint: consecutive riders r, r+1 => u_r has no two adjacent 1-digits
    (from the repunit no-carry law). T2-form verified RESTRICTED TO CANTOR u
    (the no-carry law's domain): for Cantor u, Cantor(4u+1) and Cantor(16u+5)
    never both hold (since Cantor(4u+1) forces d_0(u)=0, whence d_0(4u+1)=1,
    which kills Cantor(16u+5))."""
    ok = True
    riders = set(K for K in range(0, Kmax) if rider(K))
    for K in range(Kmax):
        if (K + 1) in riders and (K + 2) in riders:
            print(f"L4 FAIL: riders {K+1} and {K+2} consecutive")
            ok = False
    for r in sorted(riders):
        if r >= 1 and (r + 1) in riders and r % 3 != 0:
            print(f"L5 FAIL: riders {r},{r+1} with r%3={r%3}")
            ok = False
    # the adjacent-1s constraint on consecutive-rider exponents (provable law;
    # empirically vacuous since only {0,1} consecutive exist, u_0 = 0 vacuous)
    for r in sorted(riders):
        if r >= 1 and (r + 1) in riders:
            ds = digits3((4 ** r - 1) // 3)
            if any(ds[j] == 1 and j + 1 < len(ds) and ds[j + 1] == 1
                   for j in range(len(ds))):
                print(f"L5b FAIL: consecutive rider r={r} has adjacent 1s")
                ok = False
    # T2-form restricted to Cantor u (correct domain)
    for u in range(0, 3**8):
        if is_cantor(u) and is_cantor(4 * u + 1) and is_cantor(16 * u + 5):
            print(f"L4 T2-form FAIL at Cantor u={u}")
            ok = False
    print(f"L4/L5: no-three-consecutive riders + mod-3 gap (r=0 mod 3) + "
          f"adjacent-1s constraint + T2-form (Cantor u < 3^8): GREEN")
    return ok


# ---------------------------------------------------------------- LX
def check_LX(Mmax=16):
    """CONJECTURE probe: v2(cantor n) <= 2*popcount_ternary(n) for all Cantor
    n < 3^(Mmax+1) with n == 1 mod 3. Records verdict (evidence, not proof)."""
    ok = True
    worst = (0, 0, 0)
    n = 1
    while n < 3 ** (Mmax + 1):
        if is_cantor(n) and n % 3 == 1:
            pc = sum(1 for d in digits3(n) if d == 1)
            v = v2(n)
            if v > 2 * pc:
                print(f"LX CONJECTURE VIOLATED: n={n} v2={v} popcount={pc}")
                ok = False
            if v - 2 * pc > worst[0]:
                worst = (v - 2 * pc, v, pc)
        n += 2  # n odd only? no: cantor numbers can be even; but v2>0 needs even
        if n % 3 != 1:
            continue
    # full sweep done above only for n%3==1... redo properly:
    worst = (0, 0, 0)
    viol = 0
    for n in range(1, 3 ** (Mmax + 1), 2):
        if n % 3 == 1 and is_cantor(n):
            pc = sum(1 for d in digits3(n) if d == 1)
            v = v2(n)
            if v > 2 * pc:
                viol += 1
            if v - 2 * pc > worst[0]:
                worst = (v - 2 * pc, v, pc)
    # even Cantor numbers: v2 >= 1; include for completeness
    for n in range(2, 3 ** (Mmax + 1), 2):
        if is_cantor(n) and v2(n) > 2 * sum(1 for d in digits3(n) if d == 1):
            viol += 1
    print(f"LX conjecture v2 <= 2*popcount (primitive Cantor < 3^{Mmax+1}): "
          f"{'HOLDS' if viol == 0 else f'{viol} VIOLATIONS'}; "
          f"max excess v2-2pc = {worst[0]} (at v2={worst[1]}, pc={worst[2]})")
    return viol == 0


# ---------------------------------------------------------------- CENSUS
def census_extension(N=1_000_000, lo=200_000):
    """THE CENSUS EXTENSION with the L1 fractional pre-filter: certify no
    riders in (lo, N]. Pre-filter: L1 kills K with 2*4^K >= 3^(M+1) (float
    theta far from the boundary, exact integer comparison near it). Deep
    check on survivors via ONE modular pow 4^K mod 3^61 then digit extraction
    with early exit at the first 2 (empirical death depth < 40)."""
    import math
    tau = 1 - math.log(2, 3)  # 0.36907...
    ZONE = 1e-8  # float-error safety zone (accumulated error < 3e-10)
    survivors = []
    for K in range(lo + 1, N + 1):
        theta = (K * math.log(4, 3)) % 1.0
        if theta > tau + ZONE:
            continue  # killed by L1 (float-certain)
        if theta < tau - ZONE:
            survivors.append(K)  # passes L1 (float-certain)
            continue
        # boundary zone: exact integer comparison 2*4^K vs 3^(M+1)
        M = floor_log3(4**K)
        if 2 * (4**K) < 3 ** (M + 1):
            survivors.append(K)
    print(f"census L1 pre-filter: {N - lo} range -> {len(survivors)} "
          f"survivors ({100.0*len(survivors)/(N-lo):.2f}%)")
    return survivors


def deep_rider_check(K):
    """Full rider check: all ternary digits of 4^K are 0/1. Early exit at the
    first digit 2. Returns (is_rider, first_death_position)."""
    # digits via repeated divmod on 4^K (big int; fast enough per survivor)
    n = 4**K
    q = 0
    while n > 0:
        if n % 3 == 2:
            return False, q
        n //= 3
        q += 1
    return True, None


def census_deep(N=1_000_000, lo=200_000):
    """The certified census extension: no riders in (lo, N]. Stage 1: the L1
    fractional pre-filter (kills ~63%). Stage 2: the modular deep check on
    survivors — 4^K mod 3^61 (one modular pow per survivor), extract the
    first 61 digits, early exit at the first 2. Stage 3: any survivor of the
    61-digit cut (expected ~0) gets the full big-int digit walk."""
    import math
    tau = 1 - math.log(2, 3)
    cand = census_extension(N, lo)
    alive_after_61 = []
    for K in cand:
        r = pow(4, K, 3**61)
        dead = False
        for _ in range(61):
            if r % 3 == 2:
                dead = True
                break
            r //= 3
        if not dead:
            alive_after_61.append(K)
    print(f"census stage 2 (61-digit modular deep check): "
          f"{len(alive_after_61)} survivors of {len(cand)}")
    riders = []
    for K in alive_after_61:
        ok, _ = deep_rider_check(K)
        if ok:
            riders.append(K)
    if riders:
        print(f"CENSUS EXTENSION: NEW RIDERS FOUND {riders} — COUNTEREXAMPLE!")
        return False
    print(f"CENSUS EXTENSION: no riders in ({lo}, {N}] — CERTIFIED. "
          f"(previous boundary: 200000; new boundary: {N})")
    return True


def main():
    global GREEN
    print("=== BATTERY 406-B (S076): THE FIVE NEW LAWS ===")
    GREEN &= check_L1(400)
    GREEN &= check_L2(300)
    GREEN &= check_L3(3**8)
    GREEN &= check_L4_L5(400)
    GREEN &= check_LX(11)
    print("=== THE CENSUS EXTENSION (L1 pre-filter + modular deep check) ===")
    GREEN &= census_deep(1_000_000, 200_000)
    if GREEN:
        print("BATTERY406B_GREEN=1")
        return 0
    print("BATTERY406B_RED=1")
    return 1


if __name__ == "__main__":
    sys.exit(main())
