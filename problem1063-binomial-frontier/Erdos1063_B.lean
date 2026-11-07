import Erdos1063_Base

/-! # Erdos1063_B — the k = 10 completeness chunks (n_10 = 2403).
[20, 2403) = 2383 values, five term-budgeted chunks. -/

set_option maxRecDepth 65536

namespace Erdos1063Data

theorem c_10_1 : ((List.range 476).all (fun off => Nat.ble (wcount (20 + off) 10) 8)) = true := by decide
theorem c_10_2 : ((List.range 476).all (fun off => Nat.ble (wcount (496 + off) 10) 8)) = true := by decide
theorem c_10_3 : ((List.range 476).all (fun off => Nat.ble (wcount (972 + off) 10) 8)) = true := by decide
theorem c_10_4 : ((List.range 476).all (fun off => Nat.ble (wcount (1448 + off) 10) 8)) = true := by decide
theorem c_10_5 : ((List.range 479).all (fun off => Nat.ble (wcount (1924 + off) 10) 8)) = true := by decide

#eval "ERDOS1063_B_GREEN"

end Erdos1063Data
