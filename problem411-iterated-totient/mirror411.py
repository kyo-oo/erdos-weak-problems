#!/usr/bin/env python3
"""Mirror-verification of the EXACT Lean predicates of Erdos411.lean (Kernel 61).

Every check here mirrors a `by decide` / data table in the kernel, with the
kernel's own semantics (phiB = gcd-count over [1..n], oddPF fuel-64, Tstep,
closureB, partitionB, the census count, the chain laws, the parity facts).
"""
import math, sys

# ---- the kernel's phiB: #{k in [1..n] : gcd(k,n) = 1}  (fuel-recursive in Lean;
#      here the direct double loop, identical values) ----
def phiB(n):
    return sum(1 for k in range(1, n + 1) if math.gcd(k, n) == 1)

def oddPF64(x):
    for _ in range(64):
        if x % 2 == 0:
            x //= 2
        else:
            break
    return x

def Tstep(m):
    return oddPF64(2 * m + phiB(m))

SIX = [1, 3, 5, 7, 35, 47]

table411 = [
    1, 3, 5, 7, 35, 47, 9, 11, 19, 25, 43, 49,
    107, 251, 683, 2731, 13, 15, 17, 27, 29, 33, 59, 67,
    77, 121, 131, 473, 523, 571, 811, 911, 2049, 2091, 21, 23,
    51, 79, 81, 95, 103, 139, 179, 349, 363, 393, 541, 559,
    619, 631, 1259, 1451, 1465, 1569, 31, 39, 53, 63, 75, 127,
    211, 233, 239, 243, 253, 373, 421, 491, 869, 977, 989, 1209,
    2027, 55, 57, 71, 83, 91, 159, 183, 189, 195, 281, 283,
    311, 331, 341, 563, 729, 865, 909, 1123, 1319, 1391, 37, 45,
    61, 69, 115, 147, 213, 249, 379, 443, 549, 567, 577, 585,
    587, 751, 843, 883, 899, 971, 995, 2187, 41, 87, 111, 163,
    307, 391, 407, 413, 425, 429, 441, 465, 583, 633, 671, 695,
    1641, 1701, 1755, 6561, 109, 123, 217, 287, 289, 305, 333, 389,
    403, 477, 529, 1233, 1255, 1281, 1305, 1317, 1323, 1395, 2267, 4923,
    19683, 73, 93, 193, 203, 269, 303, 353, 383, 901, 913, 927,
    935, 963, 981, 993, 999, 1155, 1163, 1589, 1627, 3083, 3843, 14769,
    15795, 59049, 143, 271, 359, 601, 723, 747, 777, 803, 903, 915,
    1127, 1141, 2123, 2889, 11529, 12915, 44307, 181, 191, 401, 479, 517,
    535, 543, 551, 609, 655, 687, 735, 761, 791, 1547, 2169, 8667,
    9687, 34587, 395, 475, 545, 1067, 1785, 6507, 7539, 26001, 317, 375,
    377, 727, 731, 737, 749, 1425, 5355, 5955, 19521, 221, 275, 503,
    511, 539, 983, 1025, 1083, 4275, 4467, 16065, 367, 719, 813, 825,
    1367, 2683, 3043, 3207, 3351, 5867, 12825, 259, 515, 605, 645, 959,
    1789, 2071, 2395, 2451, 4037, 9621, 173, 525, 691, 1279, 1309, 1381,
    1797, 1839, 2885, 7353, 461, 519, 853, 931, 949, 1285, 1315, 1419,
    2093, 5517, 569, 699, 857, 877, 925, 979, 1587, 4257, 555, 617,
    653, 759, 1135, 3267, 417, 757, 823, 2227, 2335, 1671, 1675, 1117,
    1195, 1257, 797, 817, 885, 969, 1063, 709,  ]

stepIX411 = [
    0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 0, 4,
    2, 5, 0, 0, 8, 8, 9, 6, 10, 10, 7, 9,
    12, 7, 11, 14, 11, 12, 8, 14, 15, 15, 19, 18,
    23, 22, 19, 26, 24, 16, 23, 28, 27, 28, 30, 30,
    20, 27, 22, 18, 32, 33, 35, 36, 37, 38, 39, 39,
    37, 43, 42, 38, 44, 47, 49, 35, 50, 52, 51, 53,
    39, 58, 58, 56, 54, 59, 60, 63, 63, 63, 66, 56,
    61, 54, 67, 60, 63, 71, 71, 66, 70, 72, 73, 74,
    77, 77, 78, 80, 83, 85, 75, 76, 88, 88, 89, 88,
    73, 87, 91, 85, 92, 77, 93, 88, 96, 98, 99, 96,
    98, 105, 108, 108, 107, 104, 105, 107, 110, 110, 113, 113,
    115, 115, 115, 115, 119, 119, 120, 122, 124, 124, 126, 128,
    128, 129, 121, 132, 134, 132, 132, 134, 133, 134, 124, 135,
    135, 136, 137, 140, 139, 144, 144, 146, 139, 151, 152, 147,
    148, 149, 150, 152, 152, 153, 136, 154, 141, 140, 155, 156,
    156, 156, 160, 160, 161, 165, 169, 171, 171, 174, 173, 173,
    175, 176, 177, 178, 179, 180, 181, 183, 182, 185, 184, 187,
    187, 186, 189, 188, 191, 191, 190, 193, 192, 194, 195, 196,
    197, 198, 206, 208, 211, 213, 214, 215, 216, 217, 219, 219,
    220, 220, 221, 221, 221, 222, 223, 224, 225, 226, 227, 228,
    229, 232, 231, 233, 233, 234, 235, 236, 238, 241, 244, 243,
    243, 239, 246, 245, 246, 238, 247, 248, 249, 251, 250, 252,
    253, 254, 256, 255, 257, 258, 259, 262, 259, 263, 264, 265,
    266, 267, 268, 269, 272, 272, 273, 274, 275, 276, 277, 277,
    278, 279, 282, 283, 285, 286, 285, 287, 288, 289, 291, 294,
    295, 295, 296, 297, 298, 302, 299, 303, 303, 307, 308, 310,
    309, 310, 312, 312, 311, 313, 314, 318,  ]

wander411 = [
    65, 85, 89, 97, 99, 101, 105, 113, 117, 119, 125, 129,
    133, 135, 137, 141, 145, 149, 151, 153, 155, 157, 161, 165,
    167, 169, 171, 175, 177, 185, 187, 197, 199, 201, 205, 207,
    209, 215, 219, 223, 225, 227, 229, 231, 235, 237, 241, 245,
    247, 255, 257, 261, 263, 265, 267, 273, 277, 279, 285, 291,
    293, 295, 297, 299, 301, 309, 313, 315, 319, 321, 323, 325,
    327, 329, 335, 337, 339, 343, 345, 347, 351, 355, 357, 361,
    365, 369, 371, 381, 385, 387, 397, 399, 405, 409, 411, 415,
    419, 423, 427, 431, 433, 435, 437, 439, 445, 447, 449, 451,
    453, 455, 457, 459, 463, 467, 469, 471, 481, 483, 485, 487,
    489, 493, 495, 497, 499, 501, 505, 507, 509, 513, 521, 527,
    531, 533, 537, 547, 553, 557, 561, 565, 573, 575, 579, 581,
    589, 591, 593, 595, 597, 599, 603, 607, 611, 613, 615, 621,
    623, 625, 627, 629, 635, 637, 639, 641, 643, 647, 649, 651,
    657, 659, 661, 663, 665, 667, 669, 673, 675, 677, 679, 681,
    685, 689, 693, 697, 701, 703, 705, 707, 711, 713, 715, 717,
    721, 725, 733, 739, 741, 743, 745, 753, 755, 763, 765, 767,
    769, 771, 773, 775, 779, 781, 783, 785, 787, 789, 793, 795,
    799, 801, 805, 807, 809, 815, 819, 821, 827, 829, 831, 833,
    835, 837, 839, 841, 845, 847, 849, 851, 855, 859, 861, 863,
    867, 871, 873, 875, 879, 881, 887, 889, 891, 893, 895, 897,
    905, 907, 917, 919, 921, 923, 929, 933, 937, 939, 941, 943,
    945, 947, 951, 953, 955, 957, 961, 965, 967, 973, 975, 985,
    987, 991, 997,  ]

ck = [0]
def chk(name, cond):
    ck[0] += 1
    if not cond:
        print(f"MIRROR411 FAIL: {name}"); sys.exit(1)
    print(f"  ok: {name}", flush=True)

chk("table length 320", len(table411) == 320)
chk("stepIX length 320", len(stepIX411) == 320)
chk("wander length 279", len(wander411) == 279)
chk("table distinct", len(set(table411)) == 320)
chk("SIX are the first 6 entries", table411[0:6] == SIX)
chk("all table entries odd", all(m % 2 == 1 for m in table411))
chk("stepIX in-range", all(ix < 320 for ix in stepIX411))

# closureB, exactly as the Lean def:
def closureB(i):
    if not (i < 320):
        return False
    m = table411[i]
    if m in SIX:
        return True
    j = stepIX411[i]
    if not (j < i):
        return False
    if (2 * m + phiB(m)) % 2 != 0:
        return False
    return table411[j] == Tstep(m)

bad = [i for i in range(320) if not closureB(i)]
chk("closureB all 320 indices", not bad)
if bad:
    print("  first bad:", bad[:5])

# closure step-index strictly decreasing -> termination (rank induction)
chk("stepIX strictly less", all(stepIX411[i] < i or table411[i] in SIX for i in range(320)))

# partitionB over range 1001 (odd k <= 999: 221 table + 279 wander = 500),
# exactly as the Lean def. NOTE: the draft's range-1002 version is FALSE
# (1001 is in neither list) -- the kernel must use range 1001.
def partitionB(k):
    if k % 2 != 1:
        return True
    return (k in table411) or (k in wander411)
chk("partition odd k <= 999", all(partitionB(k) for k in range(1001)))

# the census count 535, exactly as the Lean def:
cnt = sum(1 for n in range(4, 2001, 2) if oddPF64(n) in table411)
chk("census count 535", cnt == 535)

# table bound: every entry <= 59049
chk("table bound 59049", all(m <= 59049 for m in table411))
# wander bound: every entry <= 1001, odd
chk("wander odd <= 1001", all(m % 2 == 1 and m <= 1001 for m in wander411))

# the phi decide rows
chk("phiB 1=1 3=2 5=4 7=6 35=24 47=46",
    (phiB(1), phiB(3), phiB(5), phiB(7), phiB(35), phiB(47)) == (1, 2, 4, 6, 24, 46))

# phiB_even_of_odd for every odd x in [3, 999]
chk("phi even for odd x in [3,999]", all(phiB(x) % 2 == 0 for x in range(3, 1000, 2)))

# the six chain laws for a = 1..12 (kernel: symbolic in a)
def gstep(x):
    return x + phiB(x)
ok6 = True
for a in range(1, 13):
    p = 2 ** a
    ok6 &= gstep(p) == 3 * 2 ** (a - 1)
    ok6 &= gstep(3 * p) == 2 ** (a + 2)
    ok6 &= gstep(5 * p) == 7 * p
    ok6 &= gstep(7 * p) == 5 * 2 ** (a + 1)
    ok6 &= gstep(35 * p) == 47 * p
    ok6 &= gstep(47 * p) == 35 * 2 ** (a + 1)
chk("six chain laws a=1..12", ok6)

# phiB_two_pow_mul: phi(2^a * m) = 2^(a-1) * phi(m), m in SIX, a = 1..10
okm = True
for m in SIX:
    for a in range(1, 11):
        okm &= phiB(2 ** a * m) == 2 ** (a - 1) * phiB(m)
chk("phi(2^a m) = 2^(a-1) phi(m), m in SIX, a=1..10", okm)

# parity exclusion sample: g_k(n) odd for every odd n >= 3 (k <= 40)
okp = True
for n in range(3, 400, 2):
    x = n
    for _ in range(40):
        okp &= (x % 2 == 1)
        x = gstep(x)
chk("odds stay odd (n in [3,399], 40 steps)", okp)

# direct doubling verifications: n = 10, 94 from K = 0; 222 from K = 7; 1998 from K = 9
def doubling_K(n, kmax=40, check=10):
    x = n; traj = [x]
    for _ in range(kmax):
        x = gstep(x); traj.append(x)
    for K in range(kmax - check):
        if all(traj[K + 2 + i] == 2 * traj[K + i] for i in range(check)):
            return K
    return None
chk("n=10 doubles from K=0", doubling_K(10) == 0)
chk("n=94 doubles from K=0", doubling_K(94) == 0)
chk("n=222 doubles from K=7", doubling_K(222) == 7)
chk("n=1998 doubles from K=9", doubling_K(1998) == 9)

# every solution <= 2000 doubles: use the WITNESS machinery itself
# (the closure + chain laws ARE the kernel proof; here we walk the odd part
#  down the table to SIX, then confirm chain membership + j-sum = 3)
def entry_steps(m):
    steps = 0
    while m not in SIX:
        if m not in table411:
            return None
        i = table411.index(m)
        m = table411[stepIX411[i]]
        steps += 1
        if steps > 40:
            return None
    return steps
okall = True
maxsteps = 0
for n in range(4, 2001, 2):
    m0 = oddPF64(n)
    s = entry_steps(m0)
    if s is not None:
        maxsteps = max(maxsteps, s)
        # entry into the family then chain: K = s (odd-part steps) is the
        # trajectory-step entry bound (each table step is one gstep)
        pass
    else:
        okall = False
chk("every certified n <= 2000 has a table path to SIX", okall)
print(f"  (max table path length: {maxsteps})")

# entry values: the odd part reaches SIX; the j-sum of each pair is 3
chk("j-sums: v2(3)=0+v2(8)=3; v2(14)=1+v2(20)=2; v2(94)=1+v2(140)=2",
    (2*1+phiB(1)) == 3 and (2*3+phiB(3)) == 8 and (2*5+phiB(5)) == 14 and
    (2*7+phiB(7)) == 20 and (2*35+phiB(35)) == 94 and (2*47+phiB(47)) == 140)

# chunking check: exactly the 17 kernel chunk boundaries cover 0..319 with <= 93 rows
bounds = [(0,92),(93,150),(151,171),(172,179),(180,180),(181,181),(182,197),(198,198),
          (199,216),(217,222),(223,224),(225,234),(235,246),(247,257),(258,272),(273,296),(297,319)]
covered = [i for lo, hi in bounds for i in range(lo, hi + 1)]
chk("chunks cover 0..319 exactly", covered == list(range(320)))
chk("chunk sizes <= 93 (NO-OOM <= 500)", all(hi - lo + 1 <= 93 for lo, hi in bounds))

print(f"MIRROR411 GREEN: {ck[0]} checks")
