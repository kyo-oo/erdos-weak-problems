/-! # Erdos451_Data — the interval-prime-free sieve oracle (Kill candidate, S033)

Erdős–Graham #451: n_k = smallest n > 2k such that ∏_{1≤i≤k}(n−i) has NO
prime factor in the open interval (k, 2k).

Round-1 reduction (S032): for prime p ∈ (k,2k), p ∣ (n−i) for some 1 ≤ i ≤ k
⟺ n mod p ∈ {1,…,k} (p > k). Hence n_k = least n > 2k with n mod p ∉ {1..k}
for every prime p ∈ (k,2k) — a pure modular sieve.

Definitions: `prodK n k = ∏_{i=1}^{k} (n−i)`; `isP q` = trial-division
primality (Bool, decide).

This module: the 19 witness residues + the 20 completeness chunks + the 19
window enumerations — ALL decide-verified, all under the 501-element NO-OOM
discipline. Battery: 19/19 dual-method GREEN (battery451.py). -/

set_option maxRecDepth 65536

/-- The consecutive product ∏_{i=1}^{k} (n − i). -/
def prodK : Nat → Nat → Nat
  | _, 0 => 1
  | n, k + 1 => (n - (k + 1)) * prodK n k

/-- Trial-division primality (Bool). -/
def isP (q : Nat) : Bool :=
  Nat.ble 2 q && ((List.range (q - 2)).all (fun d => q % (d + 2) != 0))

namespace Erdos451Data

/-! ## §1 The witness residues (n_k mod p ∉ [1,k] for every window prime). -/
theorem w_2  : ([3].all (fun p => !(Nat.ble 1 (6 % p) && Nat.ble (6 % p) 2))) = true := by decide
theorem w_3  : ([5].all (fun p => !(Nat.ble 1 (9 % p) && Nat.ble (9 % p) 3))) = true := by decide
theorem w_4  : ([5, 7].all (fun p => !(Nat.ble 1 (20 % p) && Nat.ble (20 % p) 4))) = true := by decide
theorem w_5  : ([7].all (fun p => !(Nat.ble 1 (13 % p) && Nat.ble (13 % p) 5))) = true := by decide
theorem w_6  : ([7, 11].all (fun p => !(Nat.ble 1 (21 % p) && Nat.ble (21 % p) 6))) = true := by decide
theorem w_7  : ([11, 13].all (fun p => !(Nat.ble 1 (21 % p) && Nat.ble (21 % p) 7))) = true := by decide
theorem w_8  : ([11, 13].all (fun p => !(Nat.ble 1 (22 % p) && Nat.ble (22 % p) 8))) = true := by decide
theorem w_9  : ([11, 13, 17].all (fun p => !(Nat.ble 1 (65 % p) && Nat.ble (65 % p) 9))) = true := by decide
theorem w_10 : ([11, 13, 17, 19].all (fun p => !(Nat.ble 1 (220 % p) && Nat.ble (220 % p) 10))) = true := by decide
theorem w_11 : ([13, 17, 19].all (fun p => !(Nat.ble 1 (51 % p) && Nat.ble (51 % p) 11))) = true := by decide
theorem w_12 : ([13, 17, 19, 23].all (fun p => !(Nat.ble 1 (338 % p) && Nat.ble (338 % p) 12))) = true := by decide
theorem w_13 : ([17, 19, 23].all (fun p => !(Nat.ble 1 (133 % p) && Nat.ble (133 % p) 13))) = true := by decide
theorem w_14 : ([17, 19, 23].all (fun p => !(Nat.ble 1 (321 % p) && Nat.ble (321 % p) 14))) = true := by decide
theorem w_15 : ([17, 19, 23, 29].all (fun p => !(Nat.ble 1 (339 % p) && Nat.ble (339 % p) 15))) = true := by decide
theorem w_16 : ([17, 19, 23, 29, 31].all (fun p => !(Nat.ble 1 (340 % p) && Nat.ble (340 % p) 16))) = true := by decide
theorem w_17 : ([19, 23, 29, 31].all (fun p => !(Nat.ble 1 (113 % p) && Nat.ble (113 % p) 17))) = true := by decide
theorem w_18 : ([19, 23, 29, 31].all (fun p => !(Nat.ble 1 (114 % p) && Nat.ble (114 % p) 18))) = true := by decide
theorem w_19 : ([23, 29, 31, 37].all (fun p => !(Nat.ble 1 (368 % p) && Nat.ble (368 % p) 19))) = true := by decide
theorem w_20 : ([23, 29, 31, 37].all (fun p => !(Nat.ble 1 (550 % p) && Nat.ble (550 % p) 20))) = true := by decide

/-! ## §2 The completeness chunks: every 2k < m < n_k has SOME window prime
p with m % p ∈ [1,k] (so the product HAS a prime factor in (k,2k)). -/
theorem c_2  : ((List.range 1).all (fun off => [3].any (fun p => Nat.ble 1 ((5 + off) % p) && Nat.ble ((5 + off) % p) 2))) = true := by decide
theorem c_3  : ((List.range 2).all (fun off => [5].any (fun p => Nat.ble 1 ((7 + off) % p) && Nat.ble ((7 + off) % p) 3))) = true := by decide
theorem c_4  : ((List.range 11).all (fun off => [5, 7].any (fun p => Nat.ble 1 ((9 + off) % p) && Nat.ble ((9 + off) % p) 4))) = true := by decide
theorem c_5  : ((List.range 2).all (fun off => [7].any (fun p => Nat.ble 1 ((11 + off) % p) && Nat.ble ((11 + off) % p) 5))) = true := by decide
theorem c_6  : ((List.range 8).all (fun off => [7, 11].any (fun p => Nat.ble 1 ((13 + off) % p) && Nat.ble ((13 + off) % p) 6))) = true := by decide
theorem c_7  : ((List.range 6).all (fun off => [11, 13].any (fun p => Nat.ble 1 ((15 + off) % p) && Nat.ble ((15 + off) % p) 7))) = true := by decide
theorem c_8  : ((List.range 5).all (fun off => [11, 13].any (fun p => Nat.ble 1 ((17 + off) % p) && Nat.ble ((17 + off) % p) 8))) = true := by decide
theorem c_9  : ((List.range 46).all (fun off => [11, 13, 17].any (fun p => Nat.ble 1 ((19 + off) % p) && Nat.ble ((19 + off) % p) 9))) = true := by decide
theorem c_10 : ((List.range 199).all (fun off => [11, 13, 17, 19].any (fun p => Nat.ble 1 ((21 + off) % p) && Nat.ble ((21 + off) % p) 10))) = true := by decide
theorem c_11 : ((List.range 28).all (fun off => [13, 17, 19].any (fun p => Nat.ble 1 ((23 + off) % p) && Nat.ble ((23 + off) % p) 11))) = true := by decide
theorem c_12 : ((List.range 313).all (fun off => [13, 17, 19, 23].any (fun p => Nat.ble 1 ((25 + off) % p) && Nat.ble ((25 + off) % p) 12))) = true := by decide
theorem c_13 : ((List.range 106).all (fun off => [17, 19, 23].any (fun p => Nat.ble 1 ((27 + off) % p) && Nat.ble ((27 + off) % p) 13))) = true := by decide
theorem c_14 : ((List.range 292).all (fun off => [17, 19, 23].any (fun p => Nat.ble 1 ((29 + off) % p) && Nat.ble ((29 + off) % p) 14))) = true := by decide
theorem c_15 : ((List.range 308).all (fun off => [17, 19, 23, 29].any (fun p => Nat.ble 1 ((31 + off) % p) && Nat.ble ((31 + off) % p) 15))) = true := by decide
theorem c_16 : ((List.range 307).all (fun off => [17, 19, 23, 29, 31].any (fun p => Nat.ble 1 ((33 + off) % p) && Nat.ble ((33 + off) % p) 16))) = true := by decide
theorem c_17 : ((List.range 78).all (fun off => [19, 23, 29, 31].any (fun p => Nat.ble 1 ((35 + off) % p) && Nat.ble ((35 + off) % p) 17))) = true := by decide
theorem c_18 : ((List.range 77).all (fun off => [19, 23, 29, 31].any (fun p => Nat.ble 1 ((37 + off) % p) && Nat.ble ((37 + off) % p) 18))) = true := by decide
theorem c_19 : ((List.range 329).all (fun off => [23, 29, 31, 37].any (fun p => Nat.ble 1 ((39 + off) % p) && Nat.ble ((39 + off) % p) 19))) = true := by decide
theorem c_20_1 : ((List.range 255).all (fun off => [23, 29, 31, 37].any (fun p => Nat.ble 1 ((41 + off) % p) && Nat.ble ((41 + off) % p) 20))) = true := by decide
theorem c_20_2 : ((List.range 254).all (fun off => [23, 29, 31, 37].any (fun p => Nat.ble 1 ((296 + off) % p) && Nat.ble ((296 + off) % p) 20))) = true := by decide

/-! ## §3 The window enumerations (every prime q ∈ (k, 2k) is in the list). -/
theorem win_2  : ((List.range 4).all (fun q => !(decide (2 < q) && isP q) || decide (q ∈ [3]))) = true := by decide
theorem win_3  : ((List.range 6).all (fun q => !(decide (3 < q) && isP q) || decide (q ∈ [5]))) = true := by decide
theorem win_4  : ((List.range 8).all (fun q => !(decide (4 < q) && isP q) || decide (q ∈ [5, 7]))) = true := by decide
theorem win_5  : ((List.range 10).all (fun q => !(decide (5 < q) && isP q) || decide (q ∈ [7]))) = true := by decide
theorem win_6  : ((List.range 12).all (fun q => !(decide (6 < q) && isP q) || decide (q ∈ [7, 11]))) = true := by decide
theorem win_7  : ((List.range 14).all (fun q => !(decide (7 < q) && isP q) || decide (q ∈ [11, 13]))) = true := by decide
theorem win_8  : ((List.range 16).all (fun q => !(decide (8 < q) && isP q) || decide (q ∈ [11, 13]))) = true := by decide
theorem win_9  : ((List.range 18).all (fun q => !(decide (9 < q) && isP q) || decide (q ∈ [11, 13, 17]))) = true := by decide
theorem win_10 : ((List.range 20).all (fun q => !(decide (10 < q) && isP q) || decide (q ∈ [11, 13, 17, 19]))) = true := by decide
theorem win_11 : ((List.range 22).all (fun q => !(decide (11 < q) && isP q) || decide (q ∈ [13, 17, 19]))) = true := by decide
theorem win_12 : ((List.range 24).all (fun q => !(decide (12 < q) && isP q) || decide (q ∈ [13, 17, 19, 23]))) = true := by decide
theorem win_13 : ((List.range 26).all (fun q => !(decide (13 < q) && isP q) || decide (q ∈ [17, 19, 23]))) = true := by decide
theorem win_14 : ((List.range 28).all (fun q => !(decide (14 < q) && isP q) || decide (q ∈ [17, 19, 23]))) = true := by decide
theorem win_15 : ((List.range 30).all (fun q => !(decide (15 < q) && isP q) || decide (q ∈ [17, 19, 23, 29]))) = true := by decide
theorem win_16 : ((List.range 32).all (fun q => !(decide (16 < q) && isP q) || decide (q ∈ [17, 19, 23, 29, 31]))) = true := by decide
theorem win_17 : ((List.range 34).all (fun q => !(decide (17 < q) && isP q) || decide (q ∈ [19, 23, 29, 31]))) = true := by decide
theorem win_18 : ((List.range 36).all (fun q => !(decide (18 < q) && isP q) || decide (q ∈ [19, 23, 29, 31]))) = true := by decide
theorem win_19 : ((List.range 38).all (fun q => !(decide (19 < q) && isP q) || decide (q ∈ [23, 29, 31, 37]))) = true := by decide
theorem win_20 : ((List.range 40).all (fun q => !(decide (20 < q) && isP q) || decide (q ∈ [23, 29, 31, 37]))) = true := by decide

/-! ## §4 THE W63 EXTENSION ROWS (k = 21..28; S063 W62 certified the
values n_21..n_24 in Python, W63 volley task W63-C3 lands the Lean rows
k = 21..28): the 8 witness residues + the 8 window enumerations + the
198 completeness chunks (all ≤ 500-element, NO-OOM discipline),
generated AND mirror-verified by gen451_lean_w63.py from the triple-route
battery battery451_ext_w63.py (ALL GREEN):
n_21 = 805, n_22 = 2691, n_23 = 1884, n_24 = 2664 (W62),
n_25 = 7653, n_26 = 7654, n_27 = 36887, n_28 = 36888 (W63). -/
theorem w_21 : ([23, 29, 31, 37, 41].all (fun p => !(Nat.ble 1 (805 % p) && Nat.ble (805 % p) 21))) = true := by decide
theorem win_21 : ((List.range 42).all (fun q => !(decide (21 < q) && isP q) || decide (q ∈ [23, 29, 31, 37, 41]))) = true := by decide
theorem c_21_1 : ((List.range 500).all (fun off => [23, 29, 31, 37, 41].any (fun p => Nat.ble 1 ((43 + off) % p) && Nat.ble ((43 + off) % p) 21))) = true := by decide
theorem c_21_2 : ((List.range 262).all (fun off => [23, 29, 31, 37, 41].any (fun p => Nat.ble 1 ((543 + off) % p) && Nat.ble ((543 + off) % p) 21))) = true := by decide
theorem w_22 : ([23, 29, 31, 37, 41, 43].all (fun p => !(Nat.ble 1 (2691 % p) && Nat.ble (2691 % p) 22))) = true := by decide
theorem win_22 : ((List.range 44).all (fun q => !(decide (22 < q) && isP q) || decide (q ∈ [23, 29, 31, 37, 41, 43]))) = true := by decide
theorem c_22_1 : ((List.range 500).all (fun off => [23, 29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((45 + off) % p) && Nat.ble ((45 + off) % p) 22))) = true := by decide
theorem c_22_2 : ((List.range 500).all (fun off => [23, 29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((545 + off) % p) && Nat.ble ((545 + off) % p) 22))) = true := by decide
theorem c_22_3 : ((List.range 500).all (fun off => [23, 29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((1045 + off) % p) && Nat.ble ((1045 + off) % p) 22))) = true := by decide
theorem c_22_4 : ((List.range 500).all (fun off => [23, 29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((1545 + off) % p) && Nat.ble ((1545 + off) % p) 22))) = true := by decide
theorem c_22_5 : ((List.range 500).all (fun off => [23, 29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((2045 + off) % p) && Nat.ble ((2045 + off) % p) 22))) = true := by decide
theorem c_22_6 : ((List.range 146).all (fun off => [23, 29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((2545 + off) % p) && Nat.ble ((2545 + off) % p) 22))) = true := by decide
theorem w_23 : ([29, 31, 37, 41, 43].all (fun p => !(Nat.ble 1 (1884 % p) && Nat.ble (1884 % p) 23))) = true := by decide
theorem win_23 : ((List.range 46).all (fun q => !(decide (23 < q) && isP q) || decide (q ∈ [29, 31, 37, 41, 43]))) = true := by decide
theorem c_23_1 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((47 + off) % p) && Nat.ble ((47 + off) % p) 23))) = true := by decide
theorem c_23_2 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((547 + off) % p) && Nat.ble ((547 + off) % p) 23))) = true := by decide
theorem c_23_3 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((1047 + off) % p) && Nat.ble ((1047 + off) % p) 23))) = true := by decide
theorem c_23_4 : ((List.range 337).all (fun off => [29, 31, 37, 41, 43].any (fun p => Nat.ble 1 ((1547 + off) % p) && Nat.ble ((1547 + off) % p) 23))) = true := by decide
theorem w_24 : ([29, 31, 37, 41, 43, 47].all (fun p => !(Nat.ble 1 (2664 % p) && Nat.ble (2664 % p) 24))) = true := by decide
theorem win_24 : ((List.range 48).all (fun q => !(decide (24 < q) && isP q) || decide (q ∈ [29, 31, 37, 41, 43, 47]))) = true := by decide
theorem c_24_1 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((49 + off) % p) && Nat.ble ((49 + off) % p) 24))) = true := by decide
theorem c_24_2 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((549 + off) % p) && Nat.ble ((549 + off) % p) 24))) = true := by decide
theorem c_24_3 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((1049 + off) % p) && Nat.ble ((1049 + off) % p) 24))) = true := by decide
theorem c_24_4 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((1549 + off) % p) && Nat.ble ((1549 + off) % p) 24))) = true := by decide
theorem c_24_5 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((2049 + off) % p) && Nat.ble ((2049 + off) % p) 24))) = true := by decide
theorem c_24_6 : ((List.range 115).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((2549 + off) % p) && Nat.ble ((2549 + off) % p) 24))) = true := by decide
theorem w_25 : ([29, 31, 37, 41, 43, 47].all (fun p => !(Nat.ble 1 (7653 % p) && Nat.ble (7653 % p) 25))) = true := by decide
theorem win_25 : ((List.range 50).all (fun q => !(decide (25 < q) && isP q) || decide (q ∈ [29, 31, 37, 41, 43, 47]))) = true := by decide
theorem c_25_1 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((51 + off) % p) && Nat.ble ((51 + off) % p) 25))) = true := by decide
theorem c_25_2 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((551 + off) % p) && Nat.ble ((551 + off) % p) 25))) = true := by decide
theorem c_25_3 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((1051 + off) % p) && Nat.ble ((1051 + off) % p) 25))) = true := by decide
theorem c_25_4 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((1551 + off) % p) && Nat.ble ((1551 + off) % p) 25))) = true := by decide
theorem c_25_5 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((2051 + off) % p) && Nat.ble ((2051 + off) % p) 25))) = true := by decide
theorem c_25_6 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((2551 + off) % p) && Nat.ble ((2551 + off) % p) 25))) = true := by decide
theorem c_25_7 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((3051 + off) % p) && Nat.ble ((3051 + off) % p) 25))) = true := by decide
theorem c_25_8 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((3551 + off) % p) && Nat.ble ((3551 + off) % p) 25))) = true := by decide
theorem c_25_9 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((4051 + off) % p) && Nat.ble ((4051 + off) % p) 25))) = true := by decide
theorem c_25_10 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((4551 + off) % p) && Nat.ble ((4551 + off) % p) 25))) = true := by decide
theorem c_25_11 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((5051 + off) % p) && Nat.ble ((5051 + off) % p) 25))) = true := by decide
theorem c_25_12 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((5551 + off) % p) && Nat.ble ((5551 + off) % p) 25))) = true := by decide
theorem c_25_13 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((6051 + off) % p) && Nat.ble ((6051 + off) % p) 25))) = true := by decide
theorem c_25_14 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((6551 + off) % p) && Nat.ble ((6551 + off) % p) 25))) = true := by decide
theorem c_25_15 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((7051 + off) % p) && Nat.ble ((7051 + off) % p) 25))) = true := by decide
theorem c_25_16 : ((List.range 102).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((7551 + off) % p) && Nat.ble ((7551 + off) % p) 25))) = true := by decide
theorem w_26 : ([29, 31, 37, 41, 43, 47].all (fun p => !(Nat.ble 1 (7654 % p) && Nat.ble (7654 % p) 26))) = true := by decide
theorem win_26 : ((List.range 52).all (fun q => !(decide (26 < q) && isP q) || decide (q ∈ [29, 31, 37, 41, 43, 47]))) = true := by decide
theorem c_26_1 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((53 + off) % p) && Nat.ble ((53 + off) % p) 26))) = true := by decide
theorem c_26_2 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((553 + off) % p) && Nat.ble ((553 + off) % p) 26))) = true := by decide
theorem c_26_3 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((1053 + off) % p) && Nat.ble ((1053 + off) % p) 26))) = true := by decide
theorem c_26_4 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((1553 + off) % p) && Nat.ble ((1553 + off) % p) 26))) = true := by decide
theorem c_26_5 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((2053 + off) % p) && Nat.ble ((2053 + off) % p) 26))) = true := by decide
theorem c_26_6 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((2553 + off) % p) && Nat.ble ((2553 + off) % p) 26))) = true := by decide
theorem c_26_7 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((3053 + off) % p) && Nat.ble ((3053 + off) % p) 26))) = true := by decide
theorem c_26_8 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((3553 + off) % p) && Nat.ble ((3553 + off) % p) 26))) = true := by decide
theorem c_26_9 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((4053 + off) % p) && Nat.ble ((4053 + off) % p) 26))) = true := by decide
theorem c_26_10 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((4553 + off) % p) && Nat.ble ((4553 + off) % p) 26))) = true := by decide
theorem c_26_11 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((5053 + off) % p) && Nat.ble ((5053 + off) % p) 26))) = true := by decide
theorem c_26_12 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((5553 + off) % p) && Nat.ble ((5553 + off) % p) 26))) = true := by decide
theorem c_26_13 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((6053 + off) % p) && Nat.ble ((6053 + off) % p) 26))) = true := by decide
theorem c_26_14 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((6553 + off) % p) && Nat.ble ((6553 + off) % p) 26))) = true := by decide
theorem c_26_15 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((7053 + off) % p) && Nat.ble ((7053 + off) % p) 26))) = true := by decide
theorem c_26_16 : ((List.range 101).all (fun off => [29, 31, 37, 41, 43, 47].any (fun p => Nat.ble 1 ((7553 + off) % p) && Nat.ble ((7553 + off) % p) 26))) = true := by decide
theorem w_27 : ([29, 31, 37, 41, 43, 47, 53].all (fun p => !(Nat.ble 1 (36887 % p) && Nat.ble (36887 % p) 27))) = true := by decide
theorem win_27 : ((List.range 54).all (fun q => !(decide (27 < q) && isP q) || decide (q ∈ [29, 31, 37, 41, 43, 47, 53]))) = true := by decide
theorem c_27_1 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((55 + off) % p) && Nat.ble ((55 + off) % p) 27))) = true := by decide
theorem c_27_2 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((555 + off) % p) && Nat.ble ((555 + off) % p) 27))) = true := by decide
theorem c_27_3 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((1055 + off) % p) && Nat.ble ((1055 + off) % p) 27))) = true := by decide
theorem c_27_4 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((1555 + off) % p) && Nat.ble ((1555 + off) % p) 27))) = true := by decide
theorem c_27_5 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((2055 + off) % p) && Nat.ble ((2055 + off) % p) 27))) = true := by decide
theorem c_27_6 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((2555 + off) % p) && Nat.ble ((2555 + off) % p) 27))) = true := by decide
theorem c_27_7 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((3055 + off) % p) && Nat.ble ((3055 + off) % p) 27))) = true := by decide
theorem c_27_8 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((3555 + off) % p) && Nat.ble ((3555 + off) % p) 27))) = true := by decide
theorem c_27_9 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((4055 + off) % p) && Nat.ble ((4055 + off) % p) 27))) = true := by decide
theorem c_27_10 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((4555 + off) % p) && Nat.ble ((4555 + off) % p) 27))) = true := by decide
theorem c_27_11 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((5055 + off) % p) && Nat.ble ((5055 + off) % p) 27))) = true := by decide
theorem c_27_12 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((5555 + off) % p) && Nat.ble ((5555 + off) % p) 27))) = true := by decide
theorem c_27_13 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((6055 + off) % p) && Nat.ble ((6055 + off) % p) 27))) = true := by decide
theorem c_27_14 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((6555 + off) % p) && Nat.ble ((6555 + off) % p) 27))) = true := by decide
theorem c_27_15 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((7055 + off) % p) && Nat.ble ((7055 + off) % p) 27))) = true := by decide
theorem c_27_16 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((7555 + off) % p) && Nat.ble ((7555 + off) % p) 27))) = true := by decide
theorem c_27_17 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((8055 + off) % p) && Nat.ble ((8055 + off) % p) 27))) = true := by decide
theorem c_27_18 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((8555 + off) % p) && Nat.ble ((8555 + off) % p) 27))) = true := by decide
theorem c_27_19 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((9055 + off) % p) && Nat.ble ((9055 + off) % p) 27))) = true := by decide
theorem c_27_20 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((9555 + off) % p) && Nat.ble ((9555 + off) % p) 27))) = true := by decide
theorem c_27_21 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((10055 + off) % p) && Nat.ble ((10055 + off) % p) 27))) = true := by decide
theorem c_27_22 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((10555 + off) % p) && Nat.ble ((10555 + off) % p) 27))) = true := by decide
theorem c_27_23 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((11055 + off) % p) && Nat.ble ((11055 + off) % p) 27))) = true := by decide
theorem c_27_24 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((11555 + off) % p) && Nat.ble ((11555 + off) % p) 27))) = true := by decide
theorem c_27_25 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((12055 + off) % p) && Nat.ble ((12055 + off) % p) 27))) = true := by decide
theorem c_27_26 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((12555 + off) % p) && Nat.ble ((12555 + off) % p) 27))) = true := by decide
theorem c_27_27 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((13055 + off) % p) && Nat.ble ((13055 + off) % p) 27))) = true := by decide
theorem c_27_28 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((13555 + off) % p) && Nat.ble ((13555 + off) % p) 27))) = true := by decide
theorem c_27_29 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((14055 + off) % p) && Nat.ble ((14055 + off) % p) 27))) = true := by decide
theorem c_27_30 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((14555 + off) % p) && Nat.ble ((14555 + off) % p) 27))) = true := by decide
theorem c_27_31 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((15055 + off) % p) && Nat.ble ((15055 + off) % p) 27))) = true := by decide
theorem c_27_32 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((15555 + off) % p) && Nat.ble ((15555 + off) % p) 27))) = true := by decide
theorem c_27_33 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((16055 + off) % p) && Nat.ble ((16055 + off) % p) 27))) = true := by decide
theorem c_27_34 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((16555 + off) % p) && Nat.ble ((16555 + off) % p) 27))) = true := by decide
theorem c_27_35 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((17055 + off) % p) && Nat.ble ((17055 + off) % p) 27))) = true := by decide
theorem c_27_36 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((17555 + off) % p) && Nat.ble ((17555 + off) % p) 27))) = true := by decide
theorem c_27_37 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((18055 + off) % p) && Nat.ble ((18055 + off) % p) 27))) = true := by decide
theorem c_27_38 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((18555 + off) % p) && Nat.ble ((18555 + off) % p) 27))) = true := by decide
theorem c_27_39 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((19055 + off) % p) && Nat.ble ((19055 + off) % p) 27))) = true := by decide
theorem c_27_40 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((19555 + off) % p) && Nat.ble ((19555 + off) % p) 27))) = true := by decide
theorem c_27_41 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((20055 + off) % p) && Nat.ble ((20055 + off) % p) 27))) = true := by decide
theorem c_27_42 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((20555 + off) % p) && Nat.ble ((20555 + off) % p) 27))) = true := by decide
theorem c_27_43 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((21055 + off) % p) && Nat.ble ((21055 + off) % p) 27))) = true := by decide
theorem c_27_44 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((21555 + off) % p) && Nat.ble ((21555 + off) % p) 27))) = true := by decide
theorem c_27_45 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((22055 + off) % p) && Nat.ble ((22055 + off) % p) 27))) = true := by decide
theorem c_27_46 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((22555 + off) % p) && Nat.ble ((22555 + off) % p) 27))) = true := by decide
theorem c_27_47 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((23055 + off) % p) && Nat.ble ((23055 + off) % p) 27))) = true := by decide
theorem c_27_48 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((23555 + off) % p) && Nat.ble ((23555 + off) % p) 27))) = true := by decide
theorem c_27_49 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((24055 + off) % p) && Nat.ble ((24055 + off) % p) 27))) = true := by decide
theorem c_27_50 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((24555 + off) % p) && Nat.ble ((24555 + off) % p) 27))) = true := by decide
theorem c_27_51 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((25055 + off) % p) && Nat.ble ((25055 + off) % p) 27))) = true := by decide
theorem c_27_52 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((25555 + off) % p) && Nat.ble ((25555 + off) % p) 27))) = true := by decide
theorem c_27_53 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((26055 + off) % p) && Nat.ble ((26055 + off) % p) 27))) = true := by decide
theorem c_27_54 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((26555 + off) % p) && Nat.ble ((26555 + off) % p) 27))) = true := by decide
theorem c_27_55 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((27055 + off) % p) && Nat.ble ((27055 + off) % p) 27))) = true := by decide
theorem c_27_56 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((27555 + off) % p) && Nat.ble ((27555 + off) % p) 27))) = true := by decide
theorem c_27_57 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((28055 + off) % p) && Nat.ble ((28055 + off) % p) 27))) = true := by decide
theorem c_27_58 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((28555 + off) % p) && Nat.ble ((28555 + off) % p) 27))) = true := by decide
theorem c_27_59 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((29055 + off) % p) && Nat.ble ((29055 + off) % p) 27))) = true := by decide
theorem c_27_60 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((29555 + off) % p) && Nat.ble ((29555 + off) % p) 27))) = true := by decide
theorem c_27_61 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((30055 + off) % p) && Nat.ble ((30055 + off) % p) 27))) = true := by decide
theorem c_27_62 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((30555 + off) % p) && Nat.ble ((30555 + off) % p) 27))) = true := by decide
theorem c_27_63 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((31055 + off) % p) && Nat.ble ((31055 + off) % p) 27))) = true := by decide
theorem c_27_64 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((31555 + off) % p) && Nat.ble ((31555 + off) % p) 27))) = true := by decide
theorem c_27_65 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((32055 + off) % p) && Nat.ble ((32055 + off) % p) 27))) = true := by decide
theorem c_27_66 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((32555 + off) % p) && Nat.ble ((32555 + off) % p) 27))) = true := by decide
theorem c_27_67 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((33055 + off) % p) && Nat.ble ((33055 + off) % p) 27))) = true := by decide
theorem c_27_68 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((33555 + off) % p) && Nat.ble ((33555 + off) % p) 27))) = true := by decide
theorem c_27_69 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((34055 + off) % p) && Nat.ble ((34055 + off) % p) 27))) = true := by decide
theorem c_27_70 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((34555 + off) % p) && Nat.ble ((34555 + off) % p) 27))) = true := by decide
theorem c_27_71 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((35055 + off) % p) && Nat.ble ((35055 + off) % p) 27))) = true := by decide
theorem c_27_72 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((35555 + off) % p) && Nat.ble ((35555 + off) % p) 27))) = true := by decide
theorem c_27_73 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((36055 + off) % p) && Nat.ble ((36055 + off) % p) 27))) = true := by decide
theorem c_27_74 : ((List.range 332).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((36555 + off) % p) && Nat.ble ((36555 + off) % p) 27))) = true := by decide
theorem w_28 : ([29, 31, 37, 41, 43, 47, 53].all (fun p => !(Nat.ble 1 (36888 % p) && Nat.ble (36888 % p) 28))) = true := by decide
theorem win_28 : ((List.range 56).all (fun q => !(decide (28 < q) && isP q) || decide (q ∈ [29, 31, 37, 41, 43, 47, 53]))) = true := by decide
theorem c_28_1 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((57 + off) % p) && Nat.ble ((57 + off) % p) 28))) = true := by decide
theorem c_28_2 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((557 + off) % p) && Nat.ble ((557 + off) % p) 28))) = true := by decide
theorem c_28_3 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((1057 + off) % p) && Nat.ble ((1057 + off) % p) 28))) = true := by decide
theorem c_28_4 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((1557 + off) % p) && Nat.ble ((1557 + off) % p) 28))) = true := by decide
theorem c_28_5 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((2057 + off) % p) && Nat.ble ((2057 + off) % p) 28))) = true := by decide
theorem c_28_6 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((2557 + off) % p) && Nat.ble ((2557 + off) % p) 28))) = true := by decide
theorem c_28_7 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((3057 + off) % p) && Nat.ble ((3057 + off) % p) 28))) = true := by decide
theorem c_28_8 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((3557 + off) % p) && Nat.ble ((3557 + off) % p) 28))) = true := by decide
theorem c_28_9 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((4057 + off) % p) && Nat.ble ((4057 + off) % p) 28))) = true := by decide
theorem c_28_10 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((4557 + off) % p) && Nat.ble ((4557 + off) % p) 28))) = true := by decide
theorem c_28_11 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((5057 + off) % p) && Nat.ble ((5057 + off) % p) 28))) = true := by decide
theorem c_28_12 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((5557 + off) % p) && Nat.ble ((5557 + off) % p) 28))) = true := by decide
theorem c_28_13 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((6057 + off) % p) && Nat.ble ((6057 + off) % p) 28))) = true := by decide
theorem c_28_14 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((6557 + off) % p) && Nat.ble ((6557 + off) % p) 28))) = true := by decide
theorem c_28_15 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((7057 + off) % p) && Nat.ble ((7057 + off) % p) 28))) = true := by decide
theorem c_28_16 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((7557 + off) % p) && Nat.ble ((7557 + off) % p) 28))) = true := by decide
theorem c_28_17 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((8057 + off) % p) && Nat.ble ((8057 + off) % p) 28))) = true := by decide
theorem c_28_18 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((8557 + off) % p) && Nat.ble ((8557 + off) % p) 28))) = true := by decide
theorem c_28_19 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((9057 + off) % p) && Nat.ble ((9057 + off) % p) 28))) = true := by decide
theorem c_28_20 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((9557 + off) % p) && Nat.ble ((9557 + off) % p) 28))) = true := by decide
theorem c_28_21 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((10057 + off) % p) && Nat.ble ((10057 + off) % p) 28))) = true := by decide
theorem c_28_22 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((10557 + off) % p) && Nat.ble ((10557 + off) % p) 28))) = true := by decide
theorem c_28_23 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((11057 + off) % p) && Nat.ble ((11057 + off) % p) 28))) = true := by decide
theorem c_28_24 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((11557 + off) % p) && Nat.ble ((11557 + off) % p) 28))) = true := by decide
theorem c_28_25 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((12057 + off) % p) && Nat.ble ((12057 + off) % p) 28))) = true := by decide
theorem c_28_26 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((12557 + off) % p) && Nat.ble ((12557 + off) % p) 28))) = true := by decide
theorem c_28_27 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((13057 + off) % p) && Nat.ble ((13057 + off) % p) 28))) = true := by decide
theorem c_28_28 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((13557 + off) % p) && Nat.ble ((13557 + off) % p) 28))) = true := by decide
theorem c_28_29 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((14057 + off) % p) && Nat.ble ((14057 + off) % p) 28))) = true := by decide
theorem c_28_30 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((14557 + off) % p) && Nat.ble ((14557 + off) % p) 28))) = true := by decide
theorem c_28_31 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((15057 + off) % p) && Nat.ble ((15057 + off) % p) 28))) = true := by decide
theorem c_28_32 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((15557 + off) % p) && Nat.ble ((15557 + off) % p) 28))) = true := by decide
theorem c_28_33 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((16057 + off) % p) && Nat.ble ((16057 + off) % p) 28))) = true := by decide
theorem c_28_34 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((16557 + off) % p) && Nat.ble ((16557 + off) % p) 28))) = true := by decide
theorem c_28_35 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((17057 + off) % p) && Nat.ble ((17057 + off) % p) 28))) = true := by decide
theorem c_28_36 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((17557 + off) % p) && Nat.ble ((17557 + off) % p) 28))) = true := by decide
theorem c_28_37 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((18057 + off) % p) && Nat.ble ((18057 + off) % p) 28))) = true := by decide
theorem c_28_38 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((18557 + off) % p) && Nat.ble ((18557 + off) % p) 28))) = true := by decide
theorem c_28_39 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((19057 + off) % p) && Nat.ble ((19057 + off) % p) 28))) = true := by decide
theorem c_28_40 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((19557 + off) % p) && Nat.ble ((19557 + off) % p) 28))) = true := by decide
theorem c_28_41 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((20057 + off) % p) && Nat.ble ((20057 + off) % p) 28))) = true := by decide
theorem c_28_42 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((20557 + off) % p) && Nat.ble ((20557 + off) % p) 28))) = true := by decide
theorem c_28_43 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((21057 + off) % p) && Nat.ble ((21057 + off) % p) 28))) = true := by decide
theorem c_28_44 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((21557 + off) % p) && Nat.ble ((21557 + off) % p) 28))) = true := by decide
theorem c_28_45 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((22057 + off) % p) && Nat.ble ((22057 + off) % p) 28))) = true := by decide
theorem c_28_46 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((22557 + off) % p) && Nat.ble ((22557 + off) % p) 28))) = true := by decide
theorem c_28_47 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((23057 + off) % p) && Nat.ble ((23057 + off) % p) 28))) = true := by decide
theorem c_28_48 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((23557 + off) % p) && Nat.ble ((23557 + off) % p) 28))) = true := by decide
theorem c_28_49 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((24057 + off) % p) && Nat.ble ((24057 + off) % p) 28))) = true := by decide
theorem c_28_50 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((24557 + off) % p) && Nat.ble ((24557 + off) % p) 28))) = true := by decide
theorem c_28_51 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((25057 + off) % p) && Nat.ble ((25057 + off) % p) 28))) = true := by decide
theorem c_28_52 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((25557 + off) % p) && Nat.ble ((25557 + off) % p) 28))) = true := by decide
theorem c_28_53 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((26057 + off) % p) && Nat.ble ((26057 + off) % p) 28))) = true := by decide
theorem c_28_54 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((26557 + off) % p) && Nat.ble ((26557 + off) % p) 28))) = true := by decide
theorem c_28_55 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((27057 + off) % p) && Nat.ble ((27057 + off) % p) 28))) = true := by decide
theorem c_28_56 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((27557 + off) % p) && Nat.ble ((27557 + off) % p) 28))) = true := by decide
theorem c_28_57 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((28057 + off) % p) && Nat.ble ((28057 + off) % p) 28))) = true := by decide
theorem c_28_58 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((28557 + off) % p) && Nat.ble ((28557 + off) % p) 28))) = true := by decide
theorem c_28_59 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((29057 + off) % p) && Nat.ble ((29057 + off) % p) 28))) = true := by decide
theorem c_28_60 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((29557 + off) % p) && Nat.ble ((29557 + off) % p) 28))) = true := by decide
theorem c_28_61 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((30057 + off) % p) && Nat.ble ((30057 + off) % p) 28))) = true := by decide
theorem c_28_62 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((30557 + off) % p) && Nat.ble ((30557 + off) % p) 28))) = true := by decide
theorem c_28_63 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((31057 + off) % p) && Nat.ble ((31057 + off) % p) 28))) = true := by decide
theorem c_28_64 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((31557 + off) % p) && Nat.ble ((31557 + off) % p) 28))) = true := by decide
theorem c_28_65 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((32057 + off) % p) && Nat.ble ((32057 + off) % p) 28))) = true := by decide
theorem c_28_66 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((32557 + off) % p) && Nat.ble ((32557 + off) % p) 28))) = true := by decide
theorem c_28_67 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((33057 + off) % p) && Nat.ble ((33057 + off) % p) 28))) = true := by decide
theorem c_28_68 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((33557 + off) % p) && Nat.ble ((33557 + off) % p) 28))) = true := by decide
theorem c_28_69 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((34057 + off) % p) && Nat.ble ((34057 + off) % p) 28))) = true := by decide
theorem c_28_70 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((34557 + off) % p) && Nat.ble ((34557 + off) % p) 28))) = true := by decide
theorem c_28_71 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((35057 + off) % p) && Nat.ble ((35057 + off) % p) 28))) = true := by decide
theorem c_28_72 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((35557 + off) % p) && Nat.ble ((35557 + off) % p) 28))) = true := by decide
theorem c_28_73 : ((List.range 500).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((36057 + off) % p) && Nat.ble ((36057 + off) % p) 28))) = true := by decide
theorem c_28_74 : ((List.range 331).all (fun off => [29, 31, 37, 41, 43, 47, 53].any (fun p => Nat.ble 1 ((36557 + off) % p) && Nat.ble ((36557 + off) % p) 28))) = true := by decide

#eval "ERDOS451_DATA_GREEN"

end Erdos451Data
