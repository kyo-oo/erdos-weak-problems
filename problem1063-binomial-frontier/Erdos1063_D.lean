import Erdos1063_Base

/-! # Erdos1063_D — the k = 14 completeness chunks (n_14 = 793).
[28, 793) = 765 values, two term-budgeted chunks. -/

set_option maxRecDepth 65536

namespace Erdos1063Data

theorem c_14_1 : ((List.range 480).all (fun off => Nat.ble (wcount (28 + off) 14) 12)) = true := by decide
theorem c_14_2 : ((List.range 285).all (fun off => Nat.ble (wcount (508 + off) 14) 12)) = true := by decide

#eval "ERDOS1063_D_GREEN"

end Erdos1063Data
