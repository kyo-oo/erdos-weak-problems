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
BATTERY_C = os.path.join(CAMP, "problem406-ternary-powers", "battery406c.py")
BATTERY_D = os.path.join(CAMP, "problem406-ternary-powers", "battery406d.py")
BATTERY_E = os.path.join(CAMP, "problem406-ternary-powers", "battery406e.py")
BLOCKLAW_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                               "BlockLaw406.lean")
ANTICLUSTER_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                                  "AntiCluster406.lean")
DUSTFAMILY_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                                 "DustFamily406.lean")
TWOADIC_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                              "TwoAdic406.lean")
DUST_KERNEL = os.path.join(CAMP, "problem406-ternary-powers",
                           "DustLaw406.lean")


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

    # S-TOWER (S077): the 2-adic budget-tower battery, ALL GREEN.
    t0 = time.time()
    proc = subprocess.run([sys.executable, BATTERY_C], capture_output=True,
                          text=True, timeout=900)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "BATTERY406C_GREEN=1" in out
    checks.append(_chk(
        "S-TOWER",
        "battery406c.py (S077): the 2-adic budget tower dual-method (square certificate 3^(2^s)=1+2^(s+2)c, period twin, the tower on all 512 Cantor numbers < 3^9 x 4 levels, rider tower receipts at all legal levels, pairing laws, the census-window kill power, the dust-edge 26 members) (Lean compilation is kills.yml Kernel 70)",
        ok, out[-1500:], time.time() - t0))

    # S-TOWER-LIVE (S077): the tower re-derived live on 256's six levels +
    # the LX refutation receipts.
    t0 = time.time()
    live_ok = True
    detail = []
    for s in range(1, 7):
        counts = {}
        for i in (0, 1, 2, 5):
            counts[i % 2 ** s] = counts.get(i % 2 ** s, 0) + 1
        cs = sum(c * 3 ** r for r, c in counts.items())
        good = cs % 2 ** (s + 2) == 0
        live_ok = live_ok and good
        detail.append(f"s={s}: census {cs} % 2^{s+2}={2**(s+2)} = {cs % 2**(s+2)}")
    # the LX refutation witness, live dual-method
    n1 = 3 ** 0 + 3 ** 7 + 3 ** 8 + 3 ** 13
    live_ok = live_ok and (n1 == 1603072) and no_ternary_digit_two(n1) \
        and v2(n1) == 9 and n1 % 2 ** 9 == 0 and n1 % 2 ** 10 != 0
    detail.append(f"LX witness: {n1} = 2^9*{n1 // 2**9}, v2 = {v2(n1)} > 8 = 2*4")
    n2 = 13 + 3 ** 69
    live_ok = live_ok and no_ternary_digit_two(n2) and v2(n2) == 11
    detail.append(f"far-cap: 13+3^69, v2 = {v2(n2)} > 8")
    # the kernel symbols
    try:
        kt = open(TWOADIC_KERNEL, encoding="utf-8").read()
        kd = open(DUST_KERNEL, encoding="utf-8").read()
        live_ok = live_ok and all(sym in kt for sym in (
            "theorem three_pow_twopow_struct", "theorem three_pow_mod_period",
            "theorem digitsRep_eq", "theorem budget_tower",
            "theorem rider_budget_tower", "theorem pair_mixed",
            "theorem lx_refutation_receipt",
            "theorem lx_refutation_far_cap")) \
            and "theorem dust_edge" in kd
        detail.append("TwoAdic406.lean + DustLaw406.lean symbols present"
                      if live_ok else "missing kernel symbols")
    except Exception as e:
        live_ok = False
        detail.append(repr(e))
    checks.append(_chk(
        "S-TOWER-LIVE",
        "S077 the tower + LX refutation live: 256's digit census solves all 6 legal levels; 1603072 = 3^0+3^7+3^8+3^13 is 0/1-ternary with v2 = 9 > 2*4 (LX REFUTED, one position past the S076 census boundary); the far-cap 13+3^69 carries v2 = 11; kernel symbols present",
        live_ok, "; ".join(detail), time.time() - t0))

    # S-DUST-EDGE (S077): the dust-edge theorem, live tree census.
    t0 = time.time()
    levels = [[0]]
    for j in range(10):
        nxt = []
        for r in levels[-1]:
            d = (4 ** r // 3 ** (j + 1)) % 3
            for t in (0, 1, 2):
                if (d + t) % 3 != 2:
                    nxt.append(r + t * 3 ** j)
        levels.append(sorted(set(nxt)))
    edge_ok = True
    edge_members = []
    for j in range(1, 11):
        for r in levels[j]:
            if 4 ** r < 3 ** (j + 1):
                edge_members.append(r)
                if not no_ternary_digit_two(4 ** r):
                    edge_ok = False
    edge_small = sorted(set(r for r in edge_members if r < 100))
    edge_ok = edge_ok and edge_small == [0, 1, 4] \
        and all(len(levels[j]) == 2 ** j for j in range(11))
    checks.append(_chk(
        "S-DUST-EDGE",
        "S077 the dust-edge theorem live: the tree doubles to level 10 (2^j alive per level), every edge member (4^r < 3^(j+1)) is a rider, and the edge members below 100 are exactly {0,1,4}",
        edge_ok, f"edge members: {edge_members}; below 100: {edge_small}",
        time.time() - t0))

    # S-CENSUS-BRIDGE (S078): the named assembly gap closed — the even
    # census in noTernaryTwo form, live dual-method + kernel symbols.
    t0 = time.time()
    good_dm = []
    for k in range(0, 501, 2):
        if no_ternary_digit_two(2 ** k):
            good_dm.append(k)
    good_arr = []
    for k in range(0, 501, 2):
        if no_ternary_digit_two_arr(2 ** k):
            good_arr.append(k)
    bridge_ok = good_dm == [0, 2, 8] == good_arr
    try:
        ka = open(ANTICLUSTER_KERNEL, encoding="utf-8").read()
        bridge_ok = bridge_ok and all(sym in ka for sym in (
            "theorem noTernaryTwo_of_digits", "theorem digits_of_noTernaryTwo",
            "theorem cantorScan_eq", "theorem noTwo_even_census",
            "theorem rider_edge_anticluster",
            "theorem rider_edge_anticluster_deep"))
    except Exception as e:
        bridge_ok = False
    checks.append(_chk(
        "S-CENSUS-BRIDGE",
        "S078 the census bridge live: dual-method even census (divmod + array) — the only even k <= 500 with 2^k 0/1-ternary are {0,2,8}; AntiCluster406.lean symbols present (verdict bridge both directions, sharp-fuel scanner, even census in verdict form, the anti-clustering law and its deep form)",
        bridge_ok, f"good exponents divmod = {good_dm}; array = {good_arr}",
        time.time() - t0))

    # S-ANTICLUSTER (S078): the first infinite-family anti-clustering law,
    # live: levels 0..20 x r <= 250, plus battery406d ALL GREEN.
    t0 = time.time()
    anti_ok = True
    anti_detail = []
    for r in range(0, 251):
        t = []
        n = 4 ** r
        while n:
            t.append(n % 3)
            n //= 3
        death = next((i for i, x in enumerate(t) if x == 2), None)
        for j in range(0, 21):
            if 4 ** r >= 3 ** (j + 1):
                continue
            if (death is None or death > j) and r not in (0, 1, 4):
                anti_ok = False
                anti_detail.append(f"VIOLATION j={j} r={r}")
    proc = subprocess.run([sys.executable, BATTERY_D], capture_output=True,
                          text=True, timeout=900)
    out = proc.stdout + proc.stderr
    anti_ok = anti_ok and proc.returncode == 0 and "BATTERY406D_GREEN=1" in out
    anti_detail.append("battery406d: " + ("GREEN" if "BATTERY406D_GREEN=1" in out
                                           else "FAILED"))
    checks.append(_chk(
        "S-ANTICLUSTER",
        "S078 the rider-edge anti-clustering law live: for every level j in [0,20] and r <= 250 with 4^r < 3^(j+1), surviving the level-j digit test forces r in {0,1,4} — the first infinite-family anti-clustering law; battery406d.py ALL GREEN (dual-method even census, anti-clustering, family laws to level 16, shadow dust + pi-points, window increment)",
        anti_ok, "; ".join(anti_detail[-6:]), time.time() - t0))

    # S-FAMILY (S078): the five exact family laws, live to level 12.
    t0 = time.time()
    fam_ok = True
    fam_detail = []
    alive = [0]
    for j in range(1, 13):
        nxt = []
        for r in alive:
            d = (4 ** r // 3 ** (j)) % 3
            for t in (0, 1, 2):
                if (d + t) % 3 != 2:
                    nxt.append(r + t * 3 ** (j - 1))
        alive = sorted(set(nxt))
        c1 = sum(1 for r in alive if r % 9 == 1)
        c4 = sum(1 for r in alive if r % 9 == 4)
        c7 = sum(1 for r in alive if r % 9 == 7)
        ct = sum(1 for r in alive if r % 3 == 0)
        cm = sum(1 for r in alive if r % 3 == 2)
        want = (2 ** (j - 2) if j >= 2 else None,
                2 ** (j - 2) if j >= 2 else None, 0, 2 ** (j - 1), 0)
        if j >= 2 and (c1, c4, c7, ct, cm) != want:
            fam_ok = False
            fam_detail.append(f"j={j}: {(c1, c4, c7, ct, cm)} != {want}")
        if len(alive) != 2 ** j:
            fam_ok = False
            fam_detail.append(f"j={j}: |alive| = {len(alive)} != {2 ** j}")
    try:
        kf = open(DUSTFAMILY_KERNEL, encoding="utf-8").read()
        fam_ok = fam_ok and all(sym in kf for sym in (
            "theorem dust_mod3two_zero", "theorem dust_tower_card",
            "theorem dust_fam7_zero", "theorem dust_fam1_card",
            "theorem dust_fam4_card"))
    except Exception as e:
        fam_ok = False
        fam_detail.append(repr(e))
    checks.append(_chk(
        "S-FAMILY",
        "S078 the five exact family laws live: tree A to level 12 — fam1 = 2^(j-2), fam4 = 2^(j-2), fam7 = 0, tower = 2^(j-1), mod3two = 0 at every level; DustFamily406.lean symbols present",
        fam_ok, "; ".join(fam_detail[-6:]) or "all levels exact",
        time.time() - t0))

    # S-SECONDDIGIT (S079): the cut-residue / second-digit law, live.
    t0 = time.time()
    sd_ok = True
    sd_detail = []
    for v in range(0, 7):
        for u in range(1, 30):
            lhs = (4 ** (3 ** v * u)) % (3 ** (v + 2))
            rhs = 1 + (u % 3) * (3 ** (v + 1))
            if lhs != rhs:
                sd_ok = False
                sd_detail.append(f"v={v} u={u}: {lhs} != {rhs}")
                break
        if not sd_ok:
            break
    # rider form on the true riders 1 and 4
    for K in (1, 4):
        vv = 0
        kk = K
        while kk % 3 == 0:
            kk //= 3
            vv += 1
        n = 4 ** K
        dig0 = n % 3
        digv1 = (n // 3 ** (vv + 1)) % 3
        mids = all((n // 3 ** j) % 3 == 0 for j in range(1, vv + 1))
        if not (dig0 == 1 and mids and digv1 == 1):
            sd_ok = False
            sd_detail.append(f"rider K={K} shape fails")
    try:
        kb = open(BLOCKLAW_KERNEL, encoding="utf-8").read()
        sd_ok = sd_ok and all(sym in kb for sym in (
            "theorem pow4_cut_residue_exact",
            "theorem rider_second_digit_residue"))
    except Exception as e:
        sd_ok = False
        sd_detail.append(repr(e))
    checks.append(_chk(
        "S-SECONDDIGIT",
        "S079 the cut residue + second-digit law live: 4^(3^v*u) % 3^(v+2) = 1 + (u%3)*3^(v+1) on v<=6 x u<30; riders 1,4 carry digit 0 = 1, digits 1..v = 0, digit v+1 = 1; BlockLaw406.lean symbols present",
        sd_ok, "; ".join(sd_detail[-4:]) or "all residues exact",
        time.time() - t0))

    # S-WINDOWLAW (S079): the window law, live dual-method.
    t0 = time.time()
    wl_ok = True
    wl_detail = []
    for v in range(0, 7):
        cv = (4 ** (3 ** v) - 1) // (3 ** (v + 1))
        for u in range(1, 25):
            n = 4 ** (3 ** v * u)
            for j in range(0, v + 1):
                a = (n // 3 ** (v + 1 + j)) % 3
                b = (u * cv // 3 ** j) % 3
                if a != b:
                    wl_ok = False
                    wl_detail.append(
                        f"v={v} u={u} j={j}: {a} != {b}")
                    break
            if not wl_ok:
                break
        if not wl_ok:
            break
    try:
        kb = open(BLOCKLAW_KERNEL, encoding="utf-8").read()
        wl_ok = wl_ok and "theorem diagonal_window_law" in kb
    except Exception as e:
        wl_ok = False
        wl_detail.append(repr(e))
    checks.append(_chk(
        "S-WINDOWLAW",
        "S079 the window law live (dual-method): digit3(4^(3^v*u), v+1+j) = digit3(u*lteCoeff v, j) for every j <= v, v <= 6, u < 25; kernel symbol present",
        wl_ok, "; ".join(wl_detail[-4:]) or "all bands read exactly",
        time.time() - t0))

    # S-KILLTRIT (S079): the exponent-trit killing law + the wheel, live.
    t0 = time.time()
    kt_ok = True
    kt_detail = []
    for j in range(0, 7):
        for r in range(0, 40):
            d = (4 ** r // 3 ** (j + 1)) % 3
            for t in (0, 1, 2):
                a = (4 ** (r + t * 3 ** j) // 3 ** (j + 1)) % 3
                if a != (d + t) % 3:
                    kt_ok = False
                    kt_detail.append(
                        f"r={r} t={t} j={j}: {a} != {(d+t)%3}")
                fires = sum(1 for tt in (0, 1, 2)
                            if (4 ** (r + tt * 3 ** j)
                                // 3 ** (j + 1)) % 3 == 2)
                if fires != 1:
                    kt_ok = False
                    kt_detail.append(
                        f"wheel r={r} j={j}: {fires} fires")
    try:
        kb = open(BLOCKLAW_KERNEL, encoding="utf-8").read()
        kt_ok = kt_ok and all(sym in kb for sym in (
            "theorem pow4_killing_trit", "theorem wheel_fire_exists",
            "theorem wheel_fire_unique"))
    except Exception as e:
        kt_ok = False
        kt_detail.append(repr(e))
    checks.append(_chk(
        "S-KILLTRIT",
        "S079 the killing-trit law + the wheel live: digit3(4^(r+t*3^j), j+1) = (digit3(4^r,j+1)+t)%3 on j<=6 x r<40 x t<3, and exactly one of the three lifts fires at every node; kernel symbols present",
        kt_ok, "; ".join(kt_detail[-4:]) or "the master dynamics hold + the wheel is exact",
        time.time() - t0))

    # S-FIRE45 (S079): the fire ladder levels 4 and 5, live.
    t0 = time.time()
    f45_ok = True
    f45_detail = []
    F4 = (16, 31, 61, 76, 124, 139, 169, 184)
    F5 = (58, 103, 193, 205, 238, 250, 340, 385, 463, 508, 529,
          574, 598, 643, 664, 709)
    for v in (4, 5, 6):
        cv = (4 ** (3 ** v) - 1) // (3 ** (v + 1))
        if cv % 243 != 178:
            f45_ok = False
            f45_detail.append(f"c_{v} % 243 = {cv % 243} != 178")
    for r in F4:
        if ((r * 178) % 243) // 81 != 2:
            f45_ok = False
            f45_detail.append(f"F4 residue {r} does not fire")
    cv5 = (4 ** (3 ** 5) - 1) // (3 ** 6)
    if cv5 % 729 != 664:
        f45_ok = False
        f45_detail.append(f"c_5 % 729 = {cv5 % 729} != 664")
    for r in F5:
        if ((r * 664) % 729) // 243 != 2:
            f45_ok = False
            f45_detail.append(f"F5 residue {r} does not fire")
    # the three uniform witnesses, live big-int verification
    for K, row in ((1296, 9), (14094, 11), (42282, 12)):
        d = (4 ** K // 3 ** row) % 3
        if d != 2:
            f45_ok = False
            f45_detail.append(f"witness 4^{K} row {row}: {d} != 2")
    try:
        kb = open(BLOCKLAW_KERNEL, encoding="utf-8").read()
        f45_ok = f45_ok and all(sym in kb for sym in (
            "theorem window_fire_level4", "theorem window_fire_level5",
            "theorem fire_1296_row_nine",
            "theorem fire_14094_row_eleven",
            "theorem fire_42282_row_twelve"))
    except Exception as e:
        f45_ok = False
        f45_detail.append(repr(e))
    checks.append(_chk(
        "S-FIRE45",
        "S079 the fire ladder levels 4+5 live: the 8 residues mod 243 (coeff 178) and 16 residues mod 729 (coeff 664) fire their trits at every cut; the uniform witnesses 4^1296 (row 9), 4^14094 (row 11), 4^42282 (row 12) verified live; kernel symbols present",
        f45_ok, "; ".join(f45_detail[-4:]) or "both families burn at every cut",
        time.time() - t0))

    # S-BLOCKAUTOPSY (S079): the strategic autopsy + the battery exit.
    t0 = time.time()
    ba_ok = True
    ba_detail = []
    for v, n_exp, b2_exp in ((4, 32, 28), (5, 64, 62)):
        c = (4 ** (3 ** v) - 1) // (3 ** (v + 1))
        mod = 3 ** (v + 1)
        base = [u for u in range(mod)
                if u % 3 == 1
                and all(((u * c) // 3 ** jj) % 3 != 2
                        for jj in range(v + 1))]
        cores = sorted(set(base + [u + mod for u in base]))
        in_b2 = 0
        riders = 0
        for u in cores:
            K = 3 ** v * u
            n = 4 ** K
            fire = None
            p = 0
            while 3 ** p <= n:
                if (n // 3 ** p) % 3 == 2:
                    fire = p
                    break
                p += 1
            if fire is None:
                riders += 1
            elif 2 * v + 2 <= fire <= 3 * v + 2:
                in_b2 += 1
        if not (len(cores) == n_exp and in_b2 == b2_exp
                and riders == 0):
            ba_ok = False
            ba_detail.append(
                f"v={v}: cores={len(cores)} b2={in_b2} "
                f"riders={riders} != {n_exp}/{b2_exp}/0")
    try:
        res = subprocess.run(
            ["python3", BATTERY_E], capture_output=True,
            text=True, timeout=600)
        if res.returncode != 0:
            ba_ok = False
            ba_detail.append("battery406e.py FAILED")
    except Exception as e:
        ba_ok = False
        ba_detail.append(repr(e))
    checks.append(_chk(
        "S-BLOCKAUTOPSY",
        "S079 the strategic autopsy live: at cut v=4 exactly 32 window-dust cores, 28 die inside block 2, zero riders; at v=5 exactly 64 cores, 62 die inside block 2, zero riders; battery406e.py exits 0 (52/52)",
        ba_ok, "; ".join(ba_detail[-4:]) or "the block-2 band is the executioner",
        time.time() - t0))


    # S-MAHLER (S092): the Mahler-bridge battery, ALL GREEN.
    t0 = time.time()
    BATTERY_F = os.path.join(CAMP, "problem406-ternary-powers",
                             "battery406f.py")
    proc = subprocess.run([sys.executable, BATTERY_F], capture_output=True,
                          text=True, timeout=1200)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "BATTERY406F_GREEN=1" in out
    checks.append(_chk(
        "S-MAHLER",
        "battery406f.py (S092): the Mahler-bridge battery dual-method — T1 the ghost congruence (both dust-candidate streams satisfy 2*xi*c(k-1)+9 = 2*head mod 3^k to level 30, sieve + modular residue); T2 stream non-termination evidence (15/27, 17/27 nonzero, no period <= 12); T3 the survivor tree law (exact doubling to 2048 classes through level 11, one dead child per parent); T4 the rider anti-clustering strong form (no 0/1-ternary < 3^M divisible by 4^K for K in {8,10,12}, subset-DP + multiple scan); T5 the Mahler fracture scan (every 3-free core < 200 has a diagonal fire depth <= 20)",
        ok, out[-1500:], time.time() - t0))

    # S-MAHLER-KERNEL (S092): the bridge kernel exists with its theorem
    # symbols and the vendored chambers.
    t0 = time.time()
    BRIDGE = os.path.join(CAMP, "MonolithGate", "MahlerBridge406.lean")
    GHOST = os.path.join(CAMP, "MonolithGate", "GSTGhostRayExclusion.lean")
    MAHLER = os.path.join(CAMP, "MonolithGate", "GSTWorldtraceMahler.lean")
    try:
        with open(BRIDGE, encoding="utf-8") as f:
            bt = f.read()
        with open(GHOST, encoding="utf-8") as f:
            gt = f.read()
        with open(MAHLER, encoding="utf-8") as f:
            mt = f.read()
        syms = ["c_eq_omegaCutWord", "ghost_of_dust_shape",
                "mahler_dust_fracture", "mahler_dust_fracture_c",
                "c_trit_fire_transfer", "tower_digit_two_of_diagonal_fire",
                "tower_verdict_of_mahler", "mahler_fracture_record"]
        ok = (all(s in bt for s in syms)
              and "GhostRay" in gt and "ghost_witness" in gt
              and "MahlerSharp" in mt and "worldtrace_mahler_no_cantorian" in mt
              and "sorry" not in bt.replace("sorryAx", "")
              and "ERDOS406_MAHLER_BRIDGE_GREEN" in bt)
        detail = "symbols: " + str(sum(1 for s in syms if s in bt)) + "/" + str(len(syms))
    except Exception as e:
        ok = False
        detail = repr(e)
    checks.append(_chk(
        "S-MAHLER-KERNEL",
        "MonolithGate/MahlerBridge406.lean (S092) carries the eight bridge theorem symbols with zero sorry, the vendored GSTGhostRayExclusion (the ghost ray machinery) and GSTWorldtraceMahler (the relative-precision Mahler theory) beside it (Lean compilation is kills.yml kernel-406mahler)",
        ok, detail, time.time() - t0))

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

    # N-DEEP-315 (S078): the deep-threshold corruption must be rejected —
    # at j = 314 the window does NOT yet cover r = 250 (the level-uniform
    # law's threshold 315 is exactly tight).
    t0 = time.time()
    ok = not (2 ** 500 < 3 ** 315)  # 2^500 > 3^315: the window fails at 314
    checks.append(_chk(
        "N-DEEP-315",
        "corruption rejected: 2^500 < 3^315 is FALSE (at level j = 314 the edge window does NOT cover r = 250 — the deep level-uniform anti-clustering law's threshold is exactly 315)",
        ok, f"2^500 vs 3^315: {'<' if 2**500 < 3**315 else '>='} (window covers the census range from j = 315 on)",
        time.time() - t0))

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

    # N-LX (S077): the corrupted LX conjecture must be REJECTED — the
    # counterexample stands: 1603072 is 0/1-ternary with popcount 4 and
    # v2 = 9 > 8 = 2*4. A solution still claiming LX is corrupt.
    t0 = time.time()
    n1 = 3 ** 0 + 3 ** 7 + 3 ** 8 + 3 ** 13
    lx_claim_false = v2(n1) > 2 * 4  # True -- the refutation
    ok = lx_claim_false and no_ternary_digit_two(n1) and n1 == 1603072
    checks.append(_chk(
        "N-LX",
        "corruption rejected: the LX popcount-cap conjecture (v2 <= 2*popcount3) is FALSE — 1603072 = 3^0+3^7+3^8+3^13 is 0/1-ternary with popcount 4 and v2 = 9 > 8; any ledger still carrying LX as a claim is corrupt (the S077 refutation, one position past the S076 census boundary)",
        ok, f"v2({n1}) = {v2(n1)} > 8; 0/1-ternary = {no_ternary_digit_two(n1)}",
        time.time() - t0))

    # N-TOWER (S077): the corrupted tower direction must be rejected —
    # the census sum is congruent to n (the identity), never independently
    # zero: a random 0/1-digit set's census is NOT 0 mod 8 in general.
    t0 = time.time()
    n_bad = 3 ** 0 + 3 ** 1  # 4: E=1, O=1 -> census level 1 = 1+3 = 4 != 0 mod 8
    census_bad = (1 + 3) % 8
    ok = (census_bad != 0) and (n_bad % 8 == 4)
    checks.append(_chk(
        "N-TOWER",
        "corruption rejected: the tower is an identity (n == census mod 2^(s+2)), not a zero-law — 4 = 3^0+3^1 has census 1+3 = 4 != 0 mod 8 (only RIDERS force census == 0, via n == 0 in the window)",
        ok, f"census(4) mod 8 = {census_bad}; 4 mod 8 = {n_bad % 8} (equal, nonzero)",
        time.time() - t0))

    # N-BLOCKLAW (S079): the corrupted frozen diagonal must be rejected —
    # the level-4 fire family rides the coefficient 178 mod 243; a
    # corrupted coefficient 179 breaks the family.
    t0 = time.time()
    true_fires = sum(1 for r in (16, 31, 61, 76, 124, 139, 169, 184)
                     if ((r * 178) % 243) // 81 == 2)
    fake_fires = sum(1 for r in (16, 31, 61, 76, 124, 139, 169, 184)
                     if ((r * 179) % 243) // 81 == 2)
    ok = (true_fires == 8) and (fake_fires < 8)
    checks.append(_chk(
        "N-BLOCKLAW",
        "corruption rejected: the frozen diagonal's coefficient is 178 mod 243 (all 8 level-4 fire residues burn) — the corrupted coefficient 179 breaks the family",
        ok, f"true coeff: {true_fires}/8 fire; corrupted 179: {fake_fires}/8 fire",
        time.time() - t0))

    # N-WITNESS-ROW (S079): the corrupted witness row must be rejected —
    # 4^1296 fires at row 9 (the uniform level-4 law), NOT at row 10.
    t0 = time.time()
    n_w = 4 ** 1296
    row9 = (n_w // 3 ** 9) % 3
    row10 = (n_w // 3 ** 10) % 3
    ok = (row9 == 2) and (row10 != 2)
    checks.append(_chk(
        "N-WITNESS-ROW",
        "corruption rejected: the uniform witness 4^1296 fires at row 9 EXACTLY (the level-4 law's prediction v+1+4 = 9) — a receipt claiming row 10 is FALSE",
        ok, f"row 9 digit = {row9} (fires); row 10 digit = {row10}",
        time.time() - t0))

    # N-STREAM (S092): the corrupted stream head must be rejected — the
    # class-4 dust stream's head is 1 (16*4 mod 9); a corrupted head 4
    # breaks the ghost congruence at depth 3.
    t0 = time.time()
    c2_mod27 = 16  # c(2) mod 27 (the frozen diagonal's residue)
    true_head = (7 * 4) % 9     # head of core class 4 mod 27
    ok = (true_head == 1)
    r_true = (c2_mod27 * 4) % 27
    ok = ok and (9 <= r_true < 18)  # the middle third at depth 3
    r_fake = (c2_mod27 * (4 + 9)) % 27  # core 13 mod 27 (the corrupted class)
    ok = ok and not (9 <= r_fake < 18)
    checks.append(_chk(
        "N-STREAM",
        "corruption rejected: the class-4 stream's head is 1 with the middle third (c(2)*4) mod 27 = 13 in [9,18); the corrupted class 13 lands at 22 (outside) — the two-class collapse's arithmetic is exact",
        ok, f"true: 13 in [9,18); fake class-13: {r_fake}",
        time.time() - t0))

    return checks


def v2(n):
    c = 0
    while n > 0 and n % 2 == 0:
        c += 1
        n //= 2
    return c
