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
theorem win_2  : ((List.range 4).all (fun q => !(Nat.blt 2 q && isP q) || decide (q ∈ [3]))) = true := by decide
theorem win_3  : ((List.range 6).all (fun q => !(Nat.blt 3 q && isP q) || decide (q ∈ [5]))) = true := by decide
theorem win_4  : ((List.range 8).all (fun q => !(Nat.blt 4 q && isP q) || decide (q ∈ [5, 7]))) = true := by decide
theorem win_5  : ((List.range 10).all (fun q => !(Nat.blt 5 q && isP q) || decide (q ∈ [7]))) = true := by decide
theorem win_6  : ((List.range 12).all (fun q => !(Nat.blt 6 q && isP q) || decide (q ∈ [7, 11]))) = true := by decide
theorem win_7  : ((List.range 14).all (fun q => !(Nat.blt 7 q && isP q) || decide (q ∈ [11, 13]))) = true := by decide
theorem win_8  : ((List.range 16).all (fun q => !(Nat.blt 8 q && isP q) || decide (q ∈ [11, 13]))) = true := by decide
theorem win_9  : ((List.range 18).all (fun q => !(Nat.blt 9 q && isP q) || decide (q ∈ [11, 13, 17]))) = true := by decide
theorem win_10 : ((List.range 20).all (fun q => !(Nat.blt 10 q && isP q) || decide (q ∈ [11, 13, 17, 19]))) = true := by decide
theorem win_11 : ((List.range 22).all (fun q => !(Nat.blt 11 q && isP q) || decide (q ∈ [13, 17, 19]))) = true := by decide
theorem win_12 : ((List.range 24).all (fun q => !(Nat.blt 12 q && isP q) || decide (q ∈ [13, 17, 19, 23]))) = true := by decide
theorem win_13 : ((List.range 26).all (fun q => !(Nat.blt 13 q && isP q) || decide (q ∈ [17, 19, 23]))) = true := by decide
theorem win_14 : ((List.range 28).all (fun q => !(Nat.blt 14 q && isP q) || decide (q ∈ [17, 19, 23]))) = true := by decide
theorem win_15 : ((List.range 30).all (fun q => !(Nat.blt 15 q && isP q) || decide (q ∈ [17, 19, 23, 29]))) = true := by decide
theorem win_16 : ((List.range 32).all (fun q => !(Nat.blt 16 q && isP q) || decide (q ∈ [17, 19, 23, 29, 31]))) = true := by decide
theorem win_17 : ((List.range 34).all (fun q => !(Nat.blt 17 q && isP q) || decide (q ∈ [19, 23, 29, 31]))) = true := by decide
theorem win_18 : ((List.range 36).all (fun q => !(Nat.blt 18 q && isP q) || decide (q ∈ [19, 23, 29, 31]))) = true := by decide
theorem win_19 : ((List.range 38).all (fun q => !(Nat.blt 19 q && isP q) || decide (q ∈ [23, 29, 31, 37]))) = true := by decide
theorem win_20 : ((List.range 40).all (fun q => !(Nat.blt 20 q && isP q) || decide (q ∈ [23, 29, 31, 37]))) = true := by decide

#eval "ERDOS451_DATA_GREEN"

end Erdos451Data
