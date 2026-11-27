import Mathlib

/-!
# GST N-HOMOLOGY SURGERY: integer geometric replacement on P1 x P1

Original all-X target is an integral homology-preserving replacement of
arbitrary primitive Hodge currents by Kähler calibrated ones.

The previous GST N-cohomology is a rational coordinate module and lacks
a geometric boundary operator. This module adds an integer boundary move
in the actual P1 x P1 geometric test, with:
  A = antiholomorphic antipodal graph, class B-A, area 2, period 0;
  Y = holomorphic diagonal,          class A+B, area 2, period 2;
  F = holomorphic ruling fiber,      class B,   area 1, period 1.
The genuine projective homology relation is [A]+[Y]=2[F].
Its boundary is an integer three-current in P1 x P1, by the
integral cycle homology relation; NO explicit 3-current is
built in Lean here.

Replacing A+Y by 2F preserves integral homology and lowers the
ABSOLUTE calibration defect from 2 to 0. The same arithmetic
works for ANY nonnegative integer combination in which enough
diagonal sheets are present to replace all negative-angle sheets.

This is a concrete geometry-specific GST N-channel boundary surgery,
not a universal all-X Hodge solver. Its verification makes the real
global remaining obligation clear: manufacture geometrically certified
homology relations allowing this surgery for arbitrary primitive
Hodge carriers on arbitrary X.
-/

set_option maxHeartbeats 2000000

namespace GSTNPrimitiveGeometricSurgery

/-- Integer coefficients of three ACTUAL geometric current types. -/
structure GeometricCycle where
  anti : ℤ
  diagonal : ℤ
  ruling : ℤ

/-- Integral H_2(X,Z) coordinate in the first ruling/hyperplane basis. -/
def homology (T : GeometricCycle) : ℤ × ℤ :=
  (-T.anti + T.diagonal, T.anti + T.diagonal + T.ruling)

/-- The closed Kähler form period of this signed geometric current. -/
def period (T : GeometricCycle) : ℤ :=
  2 * T.diagonal + T.ruling

/-- Geometric current mass when the distinct sheets do not overlap in area. -/
def currentMass (T : GeometricCycle) : ℤ :=
  2 * |T.anti| + 2 * |T.diagonal| + |T.ruling|

def calibrationDefect (T : GeometricCycle) : ℤ :=
  currentMass T - period T

/-- Integral homology surgery, realized by a multiple of the homology
relation [anti-graph]+[diagonal]=2[ruling]. -/
def surgery (T : GeometricCycle) (k : ℤ) : GeometricCycle :=
  ⟨T.anti - k, T.diagonal - k, T.ruling + 2*k⟩

theorem surgery_preserves_integral_homology
    (T : GeometricCycle) (k : ℤ) :
    homology (surgery T k) = homology T := by
  simp only [homology, surgery]
  congr 1 <;> ring

theorem surgery_preserves_calibration_period
    (T : GeometricCycle) (k : ℤ) :
    period (surgery T k) = period T := by
  simp [period, surgery]
  ring

/-- Positive initial coefficients and valid replacement amount:
T is sum of actual positive oriented geometric sheets. -/
def SurgeryAdmissible (T : GeometricCycle) (k : ℤ) : Prop :=
  0 ≤ k ∧ k ≤ T.anti ∧ k ≤ T.diagonal ∧ 0 ≤ T.ruling

theorem surgery_mass_exact_drop
    (T : GeometricCycle) (k : ℤ)
    (h : SurgeryAdmissible T k) :
    currentMass (surgery T k) = currentMass T - 2*k := by
  rcases h with ⟨hk, ha, hb, hc⟩
  have haa : 0 ≤ T.anti := le_trans hk ha
  have hbb : 0 ≤ T.diagonal := le_trans hk hb
  have hd1 : 0 ≤ T.anti - k := sub_nonneg.mpr ha
  have hd2 : 0 ≤ T.diagonal - k := sub_nonneg.mpr hb
  have hd3 : 0 ≤ T.ruling + 2*k := by omega
  simp only [currentMass, surgery]
  rw [abs_of_nonneg hd1, abs_of_nonneg hd2, abs_of_nonneg hd3,
      abs_of_nonneg haa, abs_of_nonneg hbb, abs_of_nonneg hc]
  ring

theorem surgery_defect_exact_drop
    (T : GeometricCycle) (k : ℤ)
    (h : SurgeryAdmissible T k) :
    calibrationDefect (surgery T k) =
      calibrationDefect T - 2*k := by
  unfold calibrationDefect
  rw [surgery_mass_exact_drop T k h,
      surgery_preserves_calibration_period]
  ring

/-- Exact geometric starting current: antiholomorphic antipodal graph
PLUS the holomorphic diagonal. -/
def badPrimitiveAmple : GeometricCycle := ⟨1,1,0⟩

/-- An actual homologous positive holomorphic cycle: two ruling fibers. -/
def calibratedReplacement : GeometricCycle := ⟨0,0,2⟩

theorem explicit_geometric_surgery :
    surgery badPrimitiveAmple 1 = calibratedReplacement := by
  rfl

theorem explicit_surgery_preserves_homology :
    homology calibratedReplacement = homology badPrimitiveAmple := by
  rw [← explicit_geometric_surgery]
  exact surgery_preserves_integral_homology badPrimitiveAmple 1

theorem explicit_surgery_reaches_zero_absolute_defect :
    calibrationDefect badPrimitiveAmple = 2 ∧
    calibrationDefect calibratedReplacement = 0 ∧
    homology calibratedReplacement = homology badPrimitiveAmple := by
  constructor
  · norm_num [calibrationDefect, currentMass, period, badPrimitiveAmple]
  constructor
  · norm_num [calibrationDefect, currentMass, period, calibratedReplacement]
  · exact explicit_surgery_preserves_homology

/-- More than one example: ANY positive integer packet with enough
diagonal mass for the anti-graph component undergoes exact
integer homology-preserving replacement with defect zero. -/
theorem eliminate_all_anti_graphs
    (T : GeometricCycle)
    (hA : 0 ≤ T.anti)
    (hB : T.anti ≤ T.diagonal)
    (hC : 0 ≤ T.ruling) :
    calibrationDefect (surgery T T.anti) = 0 ∧
    homology (surgery T T.anti) = homology T := by
  have h : SurgeryAdmissible T T.anti := ⟨hA, le_refl _, hB, hC⟩
  constructor
  · have hd := surgery_defect_exact_drop T T.anti h
    rw [hd]
    simp only [calibrationDefect, currentMass, period]
    rw [abs_of_nonneg hA,
        abs_of_nonneg (le_trans hA hB),
        abs_of_nonneg hC]
    ring
  · exact surgery_preserves_integral_homology T T.anti

#check explicit_surgery_reaches_zero_absolute_defect
#check eliminate_all_anti_graphs
#print axioms explicit_surgery_reaches_zero_absolute_defect
#print axioms eliminate_all_anti_graphs


/-! ## Exact classification of the integer geometric surgery orbit

The original result constructed one good surgery.  The upgraded law is
COMPLETE in this genuine P¹×P¹ three-carrier model: two integer geometric
packets have equal full integral homology if and only if their difference
is an integer multiple of the graph+diagonal-to-rulings boundary relation.

For positive packets, the EXISTENCE of any positive calibrated packet in
a given exact homology class is equivalent to the sharp inequality
anti <= diagonal.  This is an actual integer-effective cone criterion
for this geometric configuration, with no rational saturation shortcut.
-/

/-- The generator (-1,-1,2) of the integer boundary lattice spans
the ENTIRE kernel of the full H₂ homology signature, not just
the previously constructed one-parameter examples. -/
theorem surgery_orbit_complete
    (T U : GeometricCycle) :
    homology T = homology U ↔ ∃ k : ℤ, surgery T k = U := by
  constructor
  · intro h
    have h₁ :
        -T.anti + T.diagonal = -U.anti + U.diagonal :=
      congrArg Prod.fst h
    have h₂ :
        T.anti + T.diagonal + T.ruling =
          U.anti + U.diagonal + U.ruling :=
      congrArg Prod.snd h
    refine ⟨T.anti - U.anti, ?_⟩
    cases T with
    | mk a d r =>
      cases U with
      | mk a' d' r' =>
        change
          (⟨a - (a-a'), d - (a-a'), r + 2*(a-a')⟩ : GeometricCycle) =
            ⟨a',d',r'⟩
        have ha : a - (a-a') = a' := by omega
        have hd : d - (a-a') = d' := by
          have hh : -a+d=-a'+d' := h₁
          omega
        have hr : r + 2*(a-a') = r' := by
          have hh₁ : -a+d=-a'+d' := h₁
          have hh₂ : a+d+r=a'+d'+r' := h₂
          omega
        rw [ha, hd, hr]
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact (surgery_preserves_integral_homology T k).symm

/-- Positive integral packets have defect *exactly* twice their
antiholomorphic-graph multiplicity.  There are no other
hidden positive defects in this packet model. -/
theorem positive_packet_defect_formula
    (T : GeometricCycle)
    (ha : 0 ≤ T.anti)
    (hd : 0 ≤ T.diagonal)
    (hr : 0 ≤ T.ruling) :
    calibrationDefect T = 2 * T.anti := by
  unfold calibrationDefect currentMass period
  rw [abs_of_nonneg ha, abs_of_nonneg hd, abs_of_nonneg hr]
  ring

/-- SHARP integer effective-cone criterion. Every positive integer
packet in the same *full* homology class is accounted for by
surgery_orbit_complete. Thus a calibrated positive representative
exists if and ONLY IF the diagonal multiplicity is at least the
antigraph multiplicity in the initial positive packet. -/
theorem effective_calibrated_replacement_iff
    (T : GeometricCycle)
    (ha : 0 ≤ T.anti)
    (hd : 0 ≤ T.diagonal)
    (hr : 0 ≤ T.ruling) :
    (∃ U : GeometricCycle,
       0 ≤ U.anti ∧ 0 ≤ U.diagonal ∧ 0 ≤ U.ruling ∧
       homology U = homology T ∧ calibrationDefect U = 0) ↔
      T.anti ≤ T.diagonal := by
  constructor
  · rintro ⟨U, hUanti, hUdiag, hUruling, hclass, hcal⟩
    have hformula :=
      positive_packet_defect_formula U hUanti hUdiag hUruling
    rw [hformula] at hcal
    have hfirst :
        -U.anti + U.diagonal = -T.anti + T.diagonal :=
      congrArg Prod.fst hclass
    omega
  · intro hle
    let U := surgery T T.anti
    refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [U, surgery]; omega
    · dsimp [U, surgery]; omega
    · dsimp [U, surgery]; omega
    · change homology (surgery T T.anti) = homology T
      exact surgery_preserves_integral_homology T T.anti
    · exact (eliminate_all_anti_graphs T ha hle hr).1

#check surgery_orbit_complete
#check effective_calibrated_replacement_iff
#print axioms surgery_orbit_complete
#print axioms effective_calibrated_replacement_iff



/-! ## A global geometric mass certificate, across the WHOLE integer orbit

The earlier effective-cone theorem characterized when a positive
calibrated packet exists. Now the calibrated replacement is proved to
be a GLOBAL MASS MINIMIZER against EVERY signed integer packet in
the same full H₂ class, not just those accessible by a chosen
monotone surgery or with nonnegative coordinates.
-/

/-- Every integral P¹×P¹ geometric packet has mass at least the
ℓ¹ norm of its full two-coordinate integral homology signature.
This is a genuine integer linear dual certificate. -/
theorem currentMass_ge_homology_l1 (T : GeometricCycle) :
    |(homology T).1| + |(homology T).2| ≤ currentMass T := by
  change abs (-T.anti + T.diagonal) +
      abs (T.anti + T.diagonal + T.ruling) ≤
        2 * abs T.anti + 2 * abs T.diagonal + abs T.ruling
  have triangle (x y : ℤ) : abs (x + y) ≤ abs x + abs y := by
    apply abs_le.mpr
    constructor
    · have hx := neg_abs_le x
      have hy := neg_abs_le y
      omega
    · have hx := le_abs_self x
      have hy := le_abs_self y
      omega
  have h1 := triangle (-T.anti) T.diagonal
  have h2 := triangle (T.anti + T.diagonal) T.ruling
  have h3 := triangle T.anti T.diagonal
  rw [abs_neg] at h1
  omega

/-- Exact mass of the holomorphic replacement: it saturates the
integer-homology ℓ¹ lower bound with equality. -/
theorem effective_replacement_mass_eq_homology_l1
    (T : GeometricCycle)
    (ha : 0 ≤ T.anti)
    (hd : T.anti ≤ T.diagonal)
    (hr : 0 ≤ T.ruling) :
    currentMass (surgery T T.anti) =
      |(homology T).1| + |(homology T).2| := by
  have hdef := (eliminate_all_anti_graphs T ha hd hr).1
  have hperiod := surgery_preserves_calibration_period T T.anti
  have hx : 0 ≤ (homology T).1 := by
    change 0 ≤ -T.anti + T.diagonal
    omega
  have hy : 0 ≤ (homology T).2 := by
    change 0 ≤ T.anti + T.diagonal + T.ruling
    omega
  rw [abs_of_nonneg hx, abs_of_nonneg hy]
  unfold calibrationDefect at hdef
  unfold period at hperiod
  change currentMass (surgery T T.anti) -
      (2 * (surgery T T.anti).diagonal +
          (surgery T T.anti).ruling) = 0 at hdef
  change 2 * (surgery T T.anti).diagonal +
      (surgery T T.anti).ruling =
        2 * T.diagonal + T.ruling at hperiod
  change currentMass (surgery T T.anti) =
      (-T.anti + T.diagonal) +
        (T.anti + T.diagonal + T.ruling)
  omega

/-- GLOBAL optimality: no SIGNED integer packet in the SAME actual
two-dimensional integral homology class can lower the calibrated
replacement's mass even further. -/
theorem effective_replacement_globally_mass_minimal
    (T U : GeometricCycle)
    (ha : 0 ≤ T.anti)
    (hd : T.anti ≤ T.diagonal)
    (hr : 0 ≤ T.ruling)
    (hclass : homology U = homology T) :
    currentMass (surgery T T.anti) ≤ currentMass U := by
  rw [effective_replacement_mass_eq_homology_l1 T ha hd hr]
  have hb := currentMass_ge_homology_l1 U
  rw [hclass] at hb
  exact hb

#check effective_replacement_globally_mass_minimal
#print axioms effective_replacement_globally_mass_minimal

end GSTNPrimitiveGeometricSurgery
