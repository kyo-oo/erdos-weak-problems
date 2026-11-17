import GSTGraphV2NonEuclidean

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2NonEuclideanLaws

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2NonEuclidean

/-- x' is exactly the next forward non-dimensional coordinate. -/
theorem xPrime_exact (R N p : Nat) :
    (axes R N p).xPrime = (axes R N (p+1)).x := by
  rfl

/-- Every canonical pair of consecutive vertices is a true forward edge. -/
theorem forward_edge_exact (R N p : Nat) :
    ForwardEdge (axes R N p) (axes R N (p+1)) := by
  rfl

/-- The z' boundary coordinate strictly decreases on every live forward edge. -/
theorem boundary_strict
    (R N p : Nat) (hp : p < N) :
    (axes R N (p+1)).zPrime < (axes R N p).zPrime := by
  simp [axes]
  omega

/-- The seventh non-dimensional axis is the exact finite natural descent
`n -> n/3`. -/
theorem nAxis_forward_exact (R N p : Nat) :
    (axes R N p).nAxis.2 = (axes R N p).nAxis.1 / 3 := by
  simp only [axes]
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- The n' component of one vertex is literally the n component of the next. -/
theorem nAxis_glues_exact (R N p : Nat) :
    (axes R N p).nAxis.2 = (axes R N (p+1)).nAxis.1 := by
  rfl

/-- NULL is a genuine space, not an absorbing terminal: a BIG2 vertex in NULL
regenerates to carry two, hence ALT-, on the next forward edge. -/
theorem null_big2_regenerates_alt
    (R N p : Nat)
    (hnull : (axes R N p).yPrime = .null)
    (hbig2 : (axes R N p).z = 2) :
    (axes R N (p+1)).y = 2 ∧
      (axes R N (p+1)).yPrime = .altMinus := by
  have hC0 : carry4 R p = 0 := by
    by_contra h0
    by_cases h3 : carry4 R p = 3
    · simp [axes, GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3] at hnull
    · simp [axes, GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3] at hnull
  have hd2 : digit3 R p = 2 := by
    simpa [axes] using hbig2
  have hnext : carry4 R (p+1) = 2 := by
    rw [carry4_forward_exact R p, hC0, hd2]
    norm_num [GST2DMixedEmergence.nextCarry]
  constructor
  · simpa [axes] using hnext
  · simp [axes, GSTGraphV2NonEuclidean.spaceOfCarry, hnext]

/-- GST+ BIG2 stays GST+ on the next forward edge. -/
theorem gstPlus_big2_propagates
    (R N p : Nat)
    (hplus : (axes R N p).yPrime = .gstPlus)
    (hbig2 : (axes R N p).z = 2) :
    (axes R N (p+1)).y = 3 ∧
      (axes R N (p+1)).yPrime = .gstPlus := by
  have hC3 : carry4 R p = 3 := by
    by_contra h3
    by_cases h0 : carry4 R p = 0
    · simp [axes, GSTGraphV2NonEuclidean.spaceOfCarry, h0] at hplus
    · simp [axes, GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3] at hplus
  have hd2 : digit3 R p = 2 := by
    simpa [axes] using hbig2
  have hnext : carry4 R (p+1) = 3 := by
    rw [carry4_forward_exact R p, hC3, hd2]
    norm_num [GST2DMixedEmergence.nextCarry]
  constructor
  · simpa [axes] using hnext
  · simp [axes, GSTGraphV2NonEuclidean.spaceOfCarry, hnext]

/-- The old arithmetic sheet's carry is exactly the y coordinate of its
ambient GST projection. -/
theorem physical_projection_y_exact (E N t p : Nat) :
    (physicalProjection E N t p).y =
      (GSTGraphV2InfiniteControl.graph E t p).seven.carry := by
  rfl

/-- The old arithmetic sheet's ternary information is exactly the z coordinate
of its ambient GST projection. -/
theorem physical_projection_z_exact (E N t p : Nat) :
    (physicalProjection E N t p).z =
      (GSTGraphV2InfiniteControl.graph E t p).seven.digit := by
  rfl

/-- The arithmetic sheet's space classifier embeds faithfully into y'. -/
theorem physical_projection_space_exact (E N t p : Nat) :
    (physicalProjection E N t p).yPrime =
      match (GSTGraphV2InfiniteControl.graph E t p).seven.space with
      | GSTCanonicalSevenAxisBridge.Space.null => .null
      | GSTCanonicalSevenAxisBridge.Space.altMinus => .altMinus
      | GSTCanonicalSevenAxisBridge.Space.gstPlus => .gstPlus := by
  change GSTGraphV2NonEuclidean.spaceOfCarry (carry4 (4^t * E) p) =
    match GSTCanonicalSevenAxisBridge.spaceOfCarry (carry4 (4^t * E) p) with
    | GSTCanonicalSevenAxisBridge.Space.null => GSTGraphV2NonEuclidean.Space.null
    | GSTCanonicalSevenAxisBridge.Space.altMinus => GSTGraphV2NonEuclidean.Space.altMinus
    | GSTCanonicalSevenAxisBridge.Space.gstPlus => GSTGraphV2NonEuclidean.Space.gstPlus
  by_cases h0 : carry4 (4^t * E) p = 0
  · simp [GSTGraphV2NonEuclidean.spaceOfCarry,
      GSTCanonicalSevenAxisBridge.spaceOfCarry, h0]
  · by_cases h3 : carry4 (4^t * E) p = 3
    · simp [GSTGraphV2NonEuclidean.spaceOfCarry,
        GSTCanonicalSevenAxisBridge.spaceOfCarry, h0, h3]
    · simp [GSTGraphV2NonEuclidean.spaceOfCarry,
        GSTCanonicalSevenAxisBridge.spaceOfCarry, h0, h3]

/-- A physical-sheet Happy cell is exactly an ambient GST witness realization
at the same arithmetic energy and ternary position. -/
theorem physical_happy_iff_ambient_witness
    (E N t p : Nat) :
    GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E t p).seven.carry
        (GSTGraphV2InfiniteControl.graph E t p).seven.digit ↔
      WitnessAt (physicalProjection E N t p) := by
  change GSTU2DEventTransport.HappyCell
      (carry4 (4^t * E) p) (digit3 (4^t * E) p) ↔
    (digit3 (4^t * E) p = 2 ∧
      (GSTGraphV2NonEuclidean.spaceOfCarry (carry4 (4^t * E) p) = .null ∨
       GSTGraphV2NonEuclidean.spaceOfCarry (carry4 (4^t * E) p) = .gstPlus))
  unfold GSTU2DEventTransport.HappyCell
  by_cases h0 : carry4 (4^t * E) p = 0
  · simp [GSTGraphV2NonEuclidean.spaceOfCarry, h0]
  · by_cases h3 : carry4 (4^t * E) p = 3
    · simp [GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3]
    · simp [GSTGraphV2NonEuclidean.spaceOfCarry, h0, h3]

#check xPrime_exact
#check forward_edge_exact
#check boundary_strict
#check nAxis_forward_exact
#check nAxis_glues_exact
#check null_big2_regenerates_alt
#check gstPlus_big2_propagates
#check physical_projection_y_exact
#check physical_projection_z_exact
#check physical_projection_space_exact
#check physical_happy_iff_ambient_witness

#print axioms boundary_strict
#print axioms nAxis_forward_exact
#print axioms null_big2_regenerates_alt
#print axioms physical_happy_iff_ambient_witness

end GSTGraphV2NonEuclideanLaws
