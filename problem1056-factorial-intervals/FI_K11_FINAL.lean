import Arsenal.CardinalWorlds
import FI_Base
import FI_D4a
import FI_D4b
import FI_D4c
import FI_D4d
import FI_D4e

/-! ## The case k = 11 — THE FRONTIER (p = 52163): eleven consecutive
intervals covering [2, 52161], every block product ≡ 1 (mod 52163) —
the value-1 chain cut at 1, 3924, 7291, 7427, 18519, 24931, 26081,
27231, 33643, 44735, 44871, 52161. The FINAL ASSEMBLY: zero kernel work. -/
theorem erdos1056_k11 : Nat.Prime 52163 ∧
    prodmod 52163 2 3924 = 1 ∧ prodmod 52163 3925 7291 = 1 ∧
    prodmod 52163 7292 7427 = 1 ∧ prodmod 52163 7428 18519 = 1 ∧
    prodmod 52163 18520 24931 = 1 ∧ prodmod 52163 24932 26081 = 1 ∧
    prodmod 52163 26082 27231 = 1 ∧ prodmod 52163 27232 33643 = 1 ∧
    prodmod 52163 33644 44735 = 1 ∧ prodmod 52163 44736 44871 = 1 ∧
    prodmod 52163 44872 52161 = 1 :=
  ⟨by decide, fi_k11_b1, fi_k11_b2, fi_k11_b3, fi_k11_b4, fi_k11_b5,
    fi_k11_b6, fi_k11_b7, fi_k11_b8, fi_k11_b9, fi_k11_b10, fi_k11_b11⟩

#eval "FI_K11_GREEN"
#print axioms erdos1056_k11
