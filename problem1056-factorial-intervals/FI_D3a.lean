import FI_Base
/-! k=10 data A (p=27901): blocks 1–3, [2452,10383] — 7932 terms. -/
theorem fi_k10_b1 : prodmod 27901 2452 2867 = 1 := by decide
theorem fi_k10_b2 : prodmod 27901 2868 4768 = 1 := by decide
theorem fi_k10_b3 : prodmod 27901 4769 10383 = 1 := by decide
#eval "FI_D3a_GREEN"
