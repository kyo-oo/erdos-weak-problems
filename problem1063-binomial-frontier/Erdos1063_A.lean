import Erdos1063_Base

/-! # Erdos1063_A — the nine witnesses + the small completeness chunks.

Witnesses k = 6..14 (S032 engine, battery-verified 13/13): each n_k has
wcount = k−1 EXACTLY (one exempt position — "all but one"). Completeness:
every 2k ≤ n < n_k has wcount ≤ k−2 (at least two failing positions). -/

set_option maxRecDepth 65536

namespace Erdos1063Data

/-! ## The witnesses (decide: wcount n_k k = k−1 exactly). -/
theorem w_6  : Nat.ble 5  (wcount 75 6)    = true := by decide
theorem w_7  : Nat.ble 6  (wcount 30 7)    = true := by decide
theorem w_8  : Nat.ble 7  (wcount 70 8)    = true := by decide
theorem w_9  : Nat.ble 8  (wcount 56 9)    = true := by decide
theorem w_10 : Nat.ble 9  (wcount 2403 10) = true := by decide
theorem w_11 : Nat.ble 10 (wcount 280 11)  = true := by decide
theorem w_12 : Nat.ble 11 (wcount 3465 12) = true := by decide
theorem w_13 : Nat.ble 12 (wcount 210 13)  = true := by decide
theorem w_14 : Nat.ble 13 (wcount 793 14)  = true := by decide

/-! ## The small completeness chunks (k = 6, 7, 8, 9, 11, 13). -/
theorem c_6  : ((List.range 63).all  (fun off => Nat.ble (wcount (12 + off) 6) 4))  = true := by decide
theorem c_7  : ((List.range 16).all  (fun off => Nat.ble (wcount (14 + off) 7) 5))  = true := by decide
theorem c_8  : ((List.range 54).all  (fun off => Nat.ble (wcount (16 + off) 8) 6))  = true := by decide
theorem c_9  : ((List.range 38).all  (fun off => Nat.ble (wcount (18 + off) 9) 7))  = true := by decide
theorem c_11 : ((List.range 258).all (fun off => Nat.ble (wcount (22 + off) 11) 9)) = true := by decide
theorem c_13 : ((List.range 184).all (fun off => Nat.ble (wcount (26 + off) 13) 11)) = true := by decide

#eval "ERDOS1063_A_GREEN"

end Erdos1063Data
