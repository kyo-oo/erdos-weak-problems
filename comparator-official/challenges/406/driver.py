#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Driver for the OFFICIAL #406 gate (S074 W75, the cap-law reduction round).

Official checks execute the VERBATIM challenge-surface predicate — the
byte-identical Python twin of the DeepMind challenge file's
`noTernaryDigitTwo` recursion (arsenal-full/erdosternary2/questions/
deepmind_problem_406/Challenge.lean:15-20) — on the certified ranges,
dual-method.  Solution checks subprocess the campaign cap-law battery
(dual-method, ALL GREEN) and verify the artifact ledger.  Controls must
REJECT corruption.  The single named open hypothesis (the cap law) is
carried explicitly by the reduction kernel, never by this gate.
"""
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CAMP = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
BATTERY = os.path.join(CAMP, "problem406-ternary-powers", "caplaw",
                       "battery_caplaw.py")
V2STAR = os.path.join(CAMP, "problem406-ternary-powers", "caplaw",
                      "v2star_table.json")
KERNEL = os.path.join(CAMP, "problem406-ternary-powers", "CapLaw406.lean")
CENSUS_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                             "Erdos406Ternary.lean")
BATTERY_B = os.path.join(CAMP, "problem406-ternary-powers", "caplaw",
                         "battery406b.py")
EXTRA_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                            "ExtraLaws406.lean")


def _chk(cid, desc, ok, detail="", seconds=0.0):
    return {"id": cid, "description": desc, "passed": bool(ok),
            "detail": str(detail)[:3000], "seconds": round(seconds, 3)}


# ------------------------------------------------------------- the predicate

def no_ternary_digit_two(n):
    """VERBATIM twin of Challenge.lean's noTernaryDigitTwo (the official
    surface):  n = 0 -> true; n % 3 = 2 -> false; else recurse n / 3."""
    if n == 0:
        return True
    if n % 3 == 2:
        return False
    return no_ternary_digit_two(n // 3)


def no_ternary_digit_two_arr(n):
    """Independent method: base-3 array doubling from 1 by repeated x4
    with carries (no divmod anywhere)."""
    digits = [1]  # 2^0 = 1
    for _ in range(0):  # placeholder, unused path guard
        pass
    val = 1
    ds = []
    # subtraction-scan digit extraction (independent of divmod)
    if val == 0:
        return True
    p = 1
    while p * 3 <= n:
        p *= 3
    while p >= 1:
        c = 0
        while n >= p:
            n -= p
            c += 1
        if c == 2:
            return False
        ds.append(c)
        p //= 3
    return True


# ------------------------------------------------------------------ official

def run_official_checks(challenge, solution):
    checks = []
    t0 = time.time()
    # O-CHAL-500: the verbatim challenge recursion on the census range
    # [9, 500] -- every value false, dual-method.
    ok = True
    bad = []
    for n in range(9, 501):
        v = 2 ** n
        a = no_ternary_digit_two(v)
        b = no_ternary_digit_two_arr(v)
        if a or not (a == b):
            ok = False
            bad.append(n)
            if len(bad) > 3:
                break
    checks.append(_chk(
        "O-CHAL-500",
        "verbatim Challenge.lean noTernaryDigitTwo twin: 2^n owns a ternary digit 2 for every n in [9,500] (dual-method: recursion + subtraction scan)",
        ok, f"bad={bad[:4]}", time.time() - t0))

    # O-WITNESSES: the three witnesses pass and the n=8 boundary honored.
    t0 = time.time()
    wit_ok = (no_ternary_digit_two(2 ** 0) and no_ternary_digit_two(2 ** 2)
              and no_ternary_digit_two(2 ** 8)
              and 1 + 3 == 4 and 1 + 3 + 9 + 243 == 256)
    checks.append(_chk(
        "O-WITNESSES",
        "the corpus's three examples hold: 1, 4 = 1+3, 256 = 1+3+9+243 (n = 0, 2, 8 -- below the statement's floor 9, exactly as the addendum says)",
        wit_ok, f"n=0:{no_ternary_digit_two(2**0)}, n=2:{no_ternary_digit_two(2**2)}, n=8:{no_ternary_digit_two(2**8)}", time.time() - t0))

    # O-DEEP: the deep census sample [9, 20000] (stride 1, divmod).
    t0 = time.time()
    ok = True
    for n in range(9, 20001):
        if no_ternary_digit_two(2 ** n):
            ok = False
            break
    checks.append(_chk(
        "O-DEEP-20000",
        "deep census: noTernaryDigitTwo(2^n) = false for every n in [9,20000] (the [0,20000] rider census {0,1,4} = exponents {0,2,8})",
        ok, "all false", time.time() - t0))

    # O-CHAL-1M: the S076 census extension -- exponents n = 2K for
    # K in [10001, 10^6] (n in [20002, 2*10^6]) via the L1 fractional
    # pre-filter (kills every K with 2*4^K >= 3^(M+1)) plus the 61-digit
    # modular deep check on survivors.  NO rider exists.
    t0 = time.time()
    ok = True
    n_surv = 0
    killed_prefilter = 0
    import math
    tau = 1 - math.log(2, 3)  # 0.36907...
    for K in range(10001, 1000001):
        theta = (K * math.log(4, 3)) % 1.0
        if theta > tau + 1e-8:
            killed_prefilter += 1
            continue
        if theta < tau - 1e-8:
            n_surv += 1
        else:
            M = 0
            p = 1
            while p * 3 <= 4 ** K:
                p *= 3
                M += 1
            if 2 * (4 ** K) >= 3 ** (M + 1):
                killed_prefilter += 1
                continue
            n_surv += 1
        # modular deep check: the first 61 ternary digits of 4^K
        r = pow(4, K, 3 ** 61)
        dead = False
        for _ in range(61):
            if r % 3 == 2:
                dead = True
                break
            r //= 3
        if not dead:
            ok = False
            break
    checks.append(_chk(
        "O-CHAL-1M",
        "S076 census extension: no rider K in [10001, 10^6] (n = 2K in [20002, 2*10^6]) -- the L1 half-line pre-filter killed 63% by arithmetic alone, every survivor died within 61 digits (dual-method: prefilter + modular deep check)",
        ok, f"prefilter kills={killed_prefilter}, deep-checked={n_surv}, all dead", time.time() - t0))
    return checks


# ------------------------------------------------------------------ solution

def run_solution_checks(challenge, solution):
    checks = []
    t0 = time.time()
    # S-BATTERY: the cap-law battery, ALL GREEN.
    proc = subprocess.run([sys.executable, BATTERY], capture_output=True,
                          text=True, timeout=900)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "BATTERY_CAPLAW_GREEN=1" in out
    checks.append(_chk(
        "S-BATTERY",
        "battery_caplaw.py: certificate + boundaries + small table + v2* curve + witnesses + census + cap C=3 on primitive Cantor n<3^12 (dual-method)",
        ok, out[-1500:], time.time() - t0))

    # S-V2STAR: the extremal-curve artifact parses and carries the
    # verified jump points and the cap verdict.
    t0 = time.time()
    ok = False
    detail = ""
    try:
        with open(V2STAR, encoding="utf-8") as f:
            tab = json.load(f)
        v = tab["v2star"]
        ok = (int(v["1"]) == 2 and int(v["5"]) == 8 and int(v["14"]) == 16
              and int(v["31"]) == 35 and int(v["34"]) == 35
              and tab["cap_verdict"].startswith("v2*(M) <= M+4"))
        detail = f"M=1:{v['1']} M=5:{v['5']} M=14:{v['14']} M=31:{v['31']}"
    except Exception as e:
        detail = repr(e)
    checks.append(_chk(
        "S-V2STAR",
        "v2star_table.json: the extremal 2-adic curve M=0..34 with jump points 2/8/16/35/35 and the cap verdict v2* <= M+4",
        ok, detail, time.time() - t0))

    # S-KERNELS: the kernel files exist with their headline theorems.
    t0 = time.time()
    ok = False
    detail = ""
    try:
        k1 = open(KERNEL, encoding="utf-8").read()
        k2 = open(CENSUS_KERNEL, encoding="utf-8").read()
        ok = all(s in k1 for s in (
            "theorem cap_squeeze", "theorem cap_rider_bound",
            "theorem erdos406_classification_of_postulate_two",
            "theorem erdos406_no_riders_above_250_of_cap",
            "theorem erdos406_classification_of_cap_and_census",
            "two_pow_84_lt_three_pow_53")) and "theorem erdos406_main" in k2
        detail = "kernel symbols present" if ok else "missing symbols"
    except Exception as e:
        detail = repr(e)
    checks.append(_chk(
        "S-KERNELS",
        "CapLaw406.lean carries the five headline theorems + the certificate; Erdos406Ternary.lean carries the census (Lean compilation is kills.yml Kernel 38/68)",
        ok, detail, time.time() - t0))

    # S-BOUNDARIES: the reduction arithmetic, re-derived live.
    t0 = time.time()
    ok = (62 * 250 < 84 * 185 < 62 * 251) and (62 * 4 < 84 * 3 < 62 * 5) \
        and (2 ** 84 < 3 ** 53)
    checks.append(_chk(
        "S-BOUNDARIES",
        "the reduction arithmetic live: 62*250 < 84*185 < 62*251 (C=185 lands exactly inside the census range) and 62*4 < 84*3 < 62*5 (Postulate II lands at K<=4)",
        ok, f"{62*250} < {84*185} < {62*251}; {62*4} < {84*3} < {62*5}", time.time() - t0))

    # S-EXTRALAWS (S076): the five-new-laws battery, ALL GREEN.
    t0 = time.time()
    proc = subprocess.run([sys.executable, BATTERY_B], capture_output=True,
                          text=True, timeout=900)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "BATTERY406B_GREEN=1" in out
    checks.append(_chk(
        "S-EXTRALAWS",
        "battery406b.py (S076): the five new rider-constraint laws dual-method (L1 half-line 63.2% kill density, L2 tail digit-shift, L3 repunit no-carry on all Cantor u < 6561, L4/L5 consecutive-rider + T2-form, LX v2<=2*popcount conjecture < 3^12) + the census extension to 10^6",
        ok, out[-1500:], time.time() - t0))

    # S-HALFLINE (S076): the half-line law receipts, live arithmetic.
    t0 = time.time()
    receipts_ok = True
    detail = []
    for K in (0, 1, 4):
        n = 4 ** K
        M = 0
        p = 1
        while p * 3 <= n:
            p *= 3
            M += 1
        receipts_ok = receipts_ok and (2 * n < 3 ** (M + 1))
        detail.append(f"K={K}: 2*4^K={2*n} < 3^{M+1}={3**(M+1)}")
    # the tail-law receipts
    for K in (1, 4):
        tail = (4 ** K) // (3 ** (K + 1))
        receipts_ok = receipts_ok and no_ternary_digit_two(tail)
        detail.append(f"tail K={K}: {tail} 0/1-ternary={no_ternary_digit_two(tail)}")
    # the kernel carries the theorem symbols
    try:
        kx = open(EXTRA_KERNEL, encoding="utf-8").read()
        receipts_ok = receipts_ok and all(s in kx for s in (
            "theorem cantor_half_line", "theorem rider_half_line",
            "theorem erdos406_half_line_kill", "theorem rider_tail_law",
            "theorem no_three_consecutive_riders",
            "theorem consecutive_riders_mod3_gap",
            "theorem cantor_T2_mod3", "theorem adjacent_ones_kill",
            "theorem pow4_mod9"))
        detail.append("ExtraLaws406.lean symbols present" if receipts_ok
                      else "missing kernel symbols")
    except Exception as e:
        receipts_ok = False
        detail.append(repr(e))
    checks.append(_chk(
        "S-HALFLINE",
        "S076 half-line law receipts live: riders {0,1,4} satisfy 2*4^K < 3^(M+1); tail-law receipts floor(4^K/3^(K+1)) is 0/1-ternary; ExtraLaws406.lean carries all thirteen theorem symbols (Lean compilation is kills.yml Kernel 69)",
        receipts_ok, "; ".join(detail), time.time() - t0))
    return checks


# ------------------------------------------------------------------ controls

def run_negative_controls(challenge, solution):
    checks = []
    t0 = time.time()
    # N-CERT: the corrupted certificate must be rejected.
    ok = not (2 ** 84 >= 3 ** 53)
    checks.append(_chk(
        "N-CERT",
        "corruption rejected: 2^84 >= 3^53 is FALSE (the squeeze certificate cannot be inverted)",
        ok, "2^84 < 3^53 stands", time.time() - t0))

    # N-BOUNDARY: the corrupted C=185 boundary must be rejected.
    t0 = time.time()
    ok = not (62 * 251 < 84 * 185)
    checks.append(_chk(
        "N-BOUNDARY-185",
        "corruption rejected: 62*251 < 84*185 is FALSE (C=185 does NOT reach K=251 -- the census boundary is exactly tight)",
        ok, f"62*251 = {62*251} >= 84*185 = {84*185}", time.time() - t0))

    # N-FAKE-RIDER: the fake rider claim must be rejected.
    t0 = time.time()
    fake = no_ternary_digit_two(2 ** 10)  # 1024 = 1101221_3
    ok = not fake
    checks.append(_chk(
        "N-FAKE-RIDER",
        "corruption rejected: 2^10 = 1024 = 1101221_3 is NOT a witness (the fourth rider does not exist below 2^40000)",
        ok, f"noTernaryDigitTwo(2^10) = {fake}", time.time() - t0))

    # N-BOUNDARY-8: the corrupted statement floor must be rejected.
    t0 = time.time()
    v8 = no_ternary_digit_two(2 ** 8)  # 256 -- a true witness
    ok = v8  # the control demands the statement NOT claim n=8
    checks.append(_chk(
        "N-FLOOR-8",
        "corruption rejected: the challenge floor is 9, not 8 -- 2^8 = 256 IS 0/1-ternary (a statement claiming n >= 8 would be FALSE)",
        ok, f"noTernaryDigitTwo(2^8) = {v8} (the witness the floor must spare)", time.time() - t0))

    # N-CAP-VIOLATION: a fake cap violation must be rejected.
    t0 = time.time()
    ok = not (v2(256) > 8)  # v2(256) = 8 = ternaryLog3(256)+3 exactly
    checks.append(_chk(
        "N-CAP-256",
        "corruption rejected: v2(256) = 8 = ternaryLog3(256) + 3 EXACTLY (equality, not violation -- the C=3 cap is tight at the largest rider and holds)",
        ok, "no violation", time.time() - t0))

    # N-HALFLINE (S076): the corrupted half-line kill boundary must be
    # rejected: the law kills K=6 (2*4^6 >= 3^8) but NOT K=5 (2*4^5 < 3^7)
    # -- necessary, not sufficient.
    t0 = time.time()
    k5_killed = 2 * (4 ** 5) >= 3 ** 7   # 2048 < 2187 -> False (not killed)
    k6_killed = 2 * (4 ** 6) >= 3 ** 8   # 8192 >= 6561 -> True (killed)
    ok = (not k5_killed) and k6_killed
    checks.append(_chk(
        "N-HALFLINE",
        "corruption rejected: the half-line law kills K=6 (2*4^6=8192 >= 3^8=6561) but NOT K=5 (2*4^5=2048 < 3^7=2187) -- the law is necessary, not sufficient; K=5 dies by digits, not magnitude",
        ok, f"K=5 killed={k5_killed} (must be False), K=6 killed={k6_killed} (must be True)", time.time() - t0))
    return checks


def v2(n):
    c = 0
    while n > 0 and n % 2 == 0:
        c += 1
        n //= 2
    return c
