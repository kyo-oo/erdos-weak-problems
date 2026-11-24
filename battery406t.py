#!/usr/bin/env python3
# THE SURVIVOR-TREE ENGINE — the terrain analysis for the final assault.
# treeBad K p = (digit3 (4^(K % 3^p)) (p+1) == digit3 (4^((K % 3^p)+1)) (p+1))
#               && (K / 3^p % 3 == 2 - digit3 (4^(K % 3^p)) (p+1))
# digit3 n q = (n / 3^q) % 3 — computed MODULARLY: (4^m mod 3^(q+1)) // 3^q.
import sys
sys.setrecursionlimit(10000)

POW3 = [1]
for _ in range(220):
    POW3.append(POW3[-1]*3)

def digit_of_pow4(m, q):
    # digit3 (4^m) at row q, via modular exponentiation
    M = POW3[q+1]
    return pow(4, m, M) // POW3[q]

def treeBad(K, p):
    P = POW3[p]
    m = K % P
    d1 = digit_of_pow4(m, p+1)
    d2 = digit_of_pow4(m+1, p+1)
    trit = (K // P) % 3
    return (d1 == d2) and (trit == 2 - d1)

def survives_through(K, maxp):
    return all(not treeBad(K, p) for p in range(2, maxp+1))

# ---------- 1. VERIFY THE GREEN BAND TABLES (two-method check) ----------
tailS3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 20, 21, 22, 23, 24, 26]
tailS4 = [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 47, 48, 49, 50, 59, 60, 61, 62, 63, 64, 65, 67, 69, 70, 71, 74, 75, 77, 78, 80]
tailS5 = [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 43, 44, 47, 49, 50, 59, 60, 62, 63, 64, 65, 67, 69, 74, 75, 80, 81, 82, 83, 84, 88, 92, 93, 94, 96, 97, 98, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 118, 119, 120, 121, 125, 128, 129, 130, 131, 140, 141, 142, 143, 144, 148, 150, 151, 152, 155, 156, 158, 159, 161, 165, 166, 167, 168, 169, 171, 172, 173, 177, 178, 183, 184, 186, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 206, 209, 210, 211, 212, 222, 223, 224, 225, 226, 227, 231, 232, 233, 236, 237, 239, 240, 242]
tailS6 = [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 39, 40, 43, 44, 47, 49, 50, 59, 60, 62, 63, 64, 65, 67, 69, 75, 81, 82, 83, 84, 88, 92, 93, 94, 96, 97, 98, 102, 103, 104, 105, 107, 108, 109, 119, 120, 121, 125, 140, 141, 144, 148, 152, 155, 156, 158, 159, 161, 165, 166, 167, 168, 171, 177, 183, 184, 186, 188, 189, 190, 191, 192, 193, 194, 196, 197, 198, 199, 200, 201, 202, 205, 206, 209, 210, 211, 212, 223, 224, 225, 226, 232, 233, 236, 237, 239, 240, 242, 243, 244, 245, 246, 247, 248, 249, 250, 252, 253, 254, 259, 260, 265, 266, 267, 272, 273, 274, 275, 276, 277, 278, 279, 280, 282, 283, 286, 287, 290, 293, 302, 305, 306, 307, 308, 310, 312, 317, 318, 323, 324, 325, 326, 327, 335, 336, 337, 341, 345, 346, 347, 348, 350, 352, 353, 354, 355, 356, 361, 362, 363, 364, 371, 372, 373, 374, 383, 384, 385, 386, 387, 391, 393, 394, 395, 401, 402, 404, 411, 412, 414, 415, 416, 420, 421, 426, 427, 429, 431, 432, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 448, 449, 453, 454, 465, 466, 467, 469, 470, 474, 475, 476, 479, 482, 483, 490, 491, 492, 493, 495, 496, 497, 498, 499, 501, 502, 508, 509, 510, 512, 513, 514, 515, 516, 517, 519, 520, 521, 522, 523, 529, 530, 533, 535, 536, 545, 546, 550, 551, 553, 555, 560, 561, 566, 567, 568, 569, 570, 574, 579, 580, 582, 583, 584, 588, 590, 591, 593, 594, 595, 596, 597, 598, 599, 604, 605, 607, 611, 614, 615, 616, 617, 626, 627, 628, 629, 630, 634, 636, 637, 638, 641, 642, 644, 647, 651, 652, 653, 654, 655, 657, 658, 659, 663, 664, 669, 670, 675, 676, 677, 678, 680, 681, 682, 686, 687, 691, 695, 696, 697, 698, 708, 709, 710, 711, 712, 713, 717, 718, 719, 722, 723, 725, 726, 728]

def survivors_mod(M, maxp):
    # classes c in [0, M) surviving all levels 2..maxp
    return [c for c in range(M) if all(not treeBad(c, p) for p in range(2, maxp+1))]

print("=== 1. BAND TABLE VERIFICATION ===")
myS3 = survivors_mod(27, 2)
myS4 = survivors_mod(81, 3)
myS5 = survivors_mod(243, 4)
myS6 = survivors_mod(729, 5)
print("tailS3 match:", myS3 == tailS3, f"({len(myS3)} classes)")
print("tailS4 match:", myS4 == tailS4, f"({len(myS4)} classes)")
print("tailS5 match:", myS5 == tailS5, f"({len(myS5)} classes)")
print("tailS6 match:", myS6 == tailS6, f"({len(myS6)} classes)")

# ---------- 2. SURVIVOR TREE GROWTH ----------
print("\n=== 2. SURVIVOR TREE GROWTH (children of survivors) ===")
S = myS6  # survivors mod 729 (level 5)
print(f"|S_5| = {len(S)} (mod 729)")
for p in range(6, 15):
    P = POW3[p]
    newS = []
    for c in S:
        # children: c, c+P, c+2P — prefix is c mod P... c < P already? No:
        # survivors mod 3^(p) stored as residues < 3^p. Children mod 3^(p+1).
        for k in range(3):
            child = c + k*P
            if not treeBad(child, p):
                newS.append(child)
    S = sorted(newS)
    print(f"|S_{p}| = {len(S)} (mod 3^{p+1} = {POW3[p+1]}), ratio {len(S)/(len(newS)/3 if False else 1):.0f} children kept of {3*len(tailS6 if p==6 else [])}", end="")
    print(f" | growth vs prev: {len(S)}")

# ---------- 3. FIRE ROWS ABOVE 1500 ----------
print("\n=== 3. FIRE-ROW DISTRIBUTION ABOVE 1500 ===")
import collections
dist = collections.Counter()
maxrow = 0; argmax = 0
nofire = []
for K in range(1501, 30000):
    r = None
    for p in range(2, 120):
        if treeBad(K, p):
            r = p; break
    if r is None:
        nofire.append(K)
    else:
        dist[r] += 1
        if r > maxrow: maxrow = r; argmax = K
print("K in [1501, 30000): no-fire count:", len(nofire), nofire[:10])
print("max fire row:", maxrow, "at K =", argmax)
print("fire row histogram (row: count):")
for r in sorted(dist):
    print(f"  row {r}: {dist[r]}")
