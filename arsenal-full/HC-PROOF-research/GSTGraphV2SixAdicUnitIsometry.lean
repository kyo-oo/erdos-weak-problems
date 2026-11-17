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

/-- A finite-resolution six-adic unit certificate for a chart
multiplier.  It records an explicit inverse and the exact multiple of 6^k by
which inverse multiplication differs from one. -/
structure SixAdicUnitCertificate (k : Nat) (a : Int) where
  inverse : Int
  correction : Int
  inverse_exact :
    inverse * a = 1 + (6 : Int)^k * correction

/-- Every unit certificate induces an exact multiplicative isometry. -/
theorem SixAdicUnitCertificate.mul_isometry_iff
    {k : Nat} {a : Int}
    (U : SixAdicUnitCertificate k a)
    (x y : Int) :
    SixAdicIsoAt k (a*x) (a*y) ↔ SixAdicIsoAt k x y :=
  six_iso_mul_iff_of_mod_inverse U.inverse_exact

/-- Identity is a certified unit at every resolution. -/
def SixAdicUnitCertificate.one (k : Nat) :
    SixAdicUnitCertificate k 1 where
  inverse := 1
  correction := 0
  inverse_exact := by ring

/-- **UNIT-CERTIFICATE COMPOSITION.**
Certified chart multipliers are closed under multiplication, with an explicit
composed inverse and correction term. -/
def SixAdicUnitCertificate.mul
    {k : Nat} {a d : Int}
    (A : SixAdicUnitCertificate k a)
    (D : SixAdicUnitCertificate k d) :
    SixAdicUnitCertificate k (a*d) where
  inverse := D.inverse * A.inverse
  correction :=
    D.correction + D.inverse * A.correction * d
  inverse_exact := by
    calc
      (D.inverse * A.inverse) * (a*d) =
          D.inverse * (A.inverse*a) * d := by ring
      _ = D.inverse * (1 + (6 : Int)^k * A.correction) * d := by
          rw [A.inverse_exact]
      _ = (D.inverse*d) +
          (6 : Int)^k * (D.inverse * A.correction * d) := by ring
      _ = (1 + (6 : Int)^k * D.correction) +
          (6 : Int)^k * (D.inverse * A.correction * d) := by
          rw [D.inverse_exact]
      _ = 1 + (6 : Int)^k *
          (D.correction + D.inverse * A.correction * d) := by ring

/-- A certified multiplier remains an exact six-adic isometry after an
arbitrary affine translation. -/
theorem SixAdicUnitCertificate.affine_isometry_iff
    {k : Nat} {a : Int}
    (U : SixAdicUnitCertificate k a)
    (shift x y : Int) :
    SixAdicIsoAt k (shift + a*x) (shift + a*y) ↔
      SixAdicIsoAt k x y := by
  rw [six_iso_translate_iff]
  exact U.mul_isometry_iff x y

/-- Any finite product of two certified chart transformations preserves and
reflects the exact same six-adic resolution relation. -/
theorem composed_unit_isometry_iff
    {k : Nat} {a d : Int}
    (A : SixAdicUnitCertificate k a)
    (D : SixAdicUnitCertificate k d)
    (x y : Int) :
    SixAdicIsoAt k ((a*d)*x) ((a*d)*y) ↔
      SixAdicIsoAt k x y :=
  (A.mul D).mul_isometry_iff x y

/-- **ITERATED UNIT ACTION.**  Every natural power of one certified
six-adic unit remains an exact isometry at the same resolution.  Thus one
certificate generates an infinite discrete isometry action. -/
theorem SixAdicUnitCertificate.pow_isometry_iff
    {k : Nat} {a : Int}
    (U : SixAdicUnitCertificate k a) :
    ∀ n : Nat, ∀ x y : Int,
      SixAdicIsoAt k ((a^n)*x) ((a^n)*y)
        ↔ SixAdicIsoAt k x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp
  | succ n ih =>
      intro x y
      have hstep :=
        U.mul_isometry_iff ((a^n)*x) ((a^n)*y)
      have hstep' :
          SixAdicIsoAt k ((a^(n+1))*x) ((a^(n+1))*y)
            ↔ SixAdicIsoAt k ((a^n)*x) ((a^n)*y) := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hstep
      exact hstep'.trans (ih x y)

/-- The iterated unit action remains exact after any common affine shift. -/
theorem SixAdicUnitCertificate.pow_affine_isometry_iff
    {k : Nat} {a : Int}
    (U : SixAdicUnitCertificate k a)
    (n : Nat) (shift x y : Int) :
    SixAdicIsoAt k
        (shift + (a^n)*x) (shift + (a^n)*y)
      ↔ SixAdicIsoAt k x y := by
  rw [six_iso_translate_iff]
  exact U.pow_isometry_iff n x y

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
#check SixAdicUnitCertificate
#check SixAdicUnitCertificate.mul_isometry_iff
#check SixAdicUnitCertificate.one
#check SixAdicUnitCertificate.mul
#check SixAdicUnitCertificate.affine_isometry_iff
#check composed_unit_isometry_iff
#check SixAdicUnitCertificate.pow_isometry_iff
#check SixAdicUnitCertificate.pow_affine_isometry_iff
#check six_scale_exact_iff
#print axioms six_iso_translate_iff
#print axioms six_iso_mul_reflect_of_mod_inverse
#print axioms six_iso_mul_iff_of_mod_inverse
#print axioms SixAdicUnitCertificate.mul_isometry_iff
#print axioms SixAdicUnitCertificate.affine_isometry_iff
#print axioms composed_unit_isometry_iff
#print axioms SixAdicUnitCertificate.pow_isometry_iff
#print axioms SixAdicUnitCertificate.pow_affine_isometry_iff
#print axioms six_scale_exact_iff

end GSTGraphV2SixAdicUnitIsometry
