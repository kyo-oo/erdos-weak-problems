import GSTGraphV2SixAdicOntologicalGeometryLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2SixAdicUnitIsometry

open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicOntologicalGeometryLaws

/-- Translation is a genuine six-adic isometry: it both preserves and reflects
    every resolution class. -/
theorem six_iso_translate_iff (k : Nat) (a x y : Int) :
    SixAdicIsoAt k (a + x) (a + y) ↔ SixAdicIsoAt k x y := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      x - y = (a + x) - (a + y) := by ring
      _ = (6 : Int) ^ k * q := hq
  · exact six_iso_translate k a x y

/-- Reflection law for multiplication by any chart multiplier carrying an
    explicit inverse certificate modulo `6^k`.

    The certificate `b*a = 1 + 6^k*c` is exactly the finite-resolution notion
    that `a` is a unit in the six-adic quotient at level `k`. -/
theorem six_iso_mul_reflect_of_mod_inverse
    {k : Nat} {a b c x y : Int}
    (hinv : b * a = 1 + (6 : Int)^k * c)
    (h : SixAdicIsoAt k (a*x) (a*y)) :
    SixAdicIsoAt k x y := by
  rcases h with ⟨q, hq⟩
  refine ⟨b*q - c*(x-y), ?_⟩
  calc
    x - y = (b*a) * (x-y) - ((6 : Int)^k * c) * (x-y) := by
      rw [hinv]
      ring
    _ = b * (a*x - a*y) - ((6 : Int)^k * c) * (x-y) := by ring
    _ = b * ((6 : Int)^k * q) - ((6 : Int)^k * c) * (x-y) := by rw [hq]
    _ = (6 : Int)^k * (b*q - c*(x-y)) := by ring

/-- A multiplier possessing a modular inverse certificate is therefore a true
    six-adic isometry at resolution `k`, not merely a non-expansive map. -/
theorem six_iso_mul_iff_of_mod_inverse
    {k : Nat} {a b c x y : Int}
    (hinv : b * a = 1 + (6 : Int)^k * c) :
    SixAdicIsoAt k (a*x) (a*y) ↔ SixAdicIsoAt k x y := by
  constructor
  · exact six_iso_mul_reflect_of_mod_inverse hinv
  · intro h
    exact six_iso_mul k a x y h

/-- Multiplication by six is an exact similarity of the resolution tree:
    shifting both energies by one base-six factor raises the resolution by
    exactly one level, in both directions. -/
theorem six_scale_exact_iff {k : Nat} {x y : Int} :
    SixAdicIsoAt (k+1) (6*x) (6*y) ↔ SixAdicIsoAt k x y := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hcancel : 6 * (x-y) = 6 * ((6 : Int)^k * q) := by
      calc
        6 * (x-y) = 6*x - 6*y := by ring
        _ = (6 : Int)^(k+1) * q := hq
        _ = 6 * ((6 : Int)^k * q) := by rw [pow_succ]; ring
    nlinarith
  · exact six_iso_scale_six

#check six_iso_translate_iff
#check six_iso_mul_reflect_of_mod_inverse
#check six_iso_mul_iff_of_mod_inverse
#check six_scale_exact_iff
#print axioms six_iso_translate_iff
#print axioms six_iso_mul_reflect_of_mod_inverse
#print axioms six_iso_mul_iff_of_mod_inverse
#print axioms six_scale_exact_iff

end GSTGraphV2SixAdicUnitIsometry
