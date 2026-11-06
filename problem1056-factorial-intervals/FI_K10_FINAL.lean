import Arsenal.CardinalWorlds
import FI_Base
import FI_D3a
import FI_D3b
import FI_D3c

set_option maxRecDepth 65536

/-! ## The case k = 10 — NEW (p = 27901). The FINAL ASSEMBLY: zero kernel
work — the block products were decided in the data modules; this module
composes them and decides the primality. -/
theorem erdos1056_k10 : Nat.Prime 27901 ∧
    prodmod 27901 2452 2867 = 1 ∧ prodmod 27901 2868 4768 = 1 ∧
    prodmod 27901 4769 10383 = 1 ∧ prodmod 27901 10384 18707 = 1 ∧
    prodmod 27901 18708 19589 = 1 ∧ prodmod 27901 19590 19965 = 1 ∧
    prodmod 27901 19966 22981 = 1 ∧ prodmod 27901 22982 24673 = 1 ∧
    prodmod 27901 24674 26322 = 1 ∧ prodmod 27901 26323 27263 = 1 :=
  ⟨by decide, fi_k10_b1, fi_k10_b2, fi_k10_b3, fi_k10_b4, fi_k10_b5,
    fi_k10_b6, fi_k10_b7, fi_k10_b8, fi_k10_b9, fi_k10_b10⟩

#eval "FI_K10_GREEN"
#print axioms erdos1056_k10
