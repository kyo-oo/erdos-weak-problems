import Erdos1063_Base

/-! # Erdos1063_C — the k = 12 completeness chunks (n_12 = 3465).
[24, 3465) = 3441 values, eight term-budgeted chunks. -/

set_option maxRecDepth 65536

namespace Erdos1063Data

theorem c_12_1 : ((List.range 430).all (fun off => Nat.ble (wcount (24 + off) 12) 10)) = true := by decide
theorem c_12_2 : ((List.range 430).all (fun off => Nat.ble (wcount (454 + off) 12) 10)) = true := by decide
theorem c_12_3 : ((List.range 430).all (fun off => Nat.ble (wcount (884 + off) 12) 10)) = true := by decide
theorem c_12_4 : ((List.range 430).all (fun off => Nat.ble (wcount (1314 + off) 12) 10)) = true := by decide
theorem c_12_5 : ((List.range 430).all (fun off => Nat.ble (wcount (1744 + off) 12) 10)) = true := by decide
theorem c_12_6 : ((List.range 430).all (fun off => Nat.ble (wcount (2174 + off) 12) 10)) = true := by decide
theorem c_12_7 : ((List.range 430).all (fun off => Nat.ble (wcount (2604 + off) 12) 10)) = true := by decide
theorem c_12_8 : ((List.range 431).all (fun off => Nat.ble (wcount (3034 + off) 12) 10)) = true := by decide

#eval "ERDOS1063_C_GREEN"

end Erdos1063Data
