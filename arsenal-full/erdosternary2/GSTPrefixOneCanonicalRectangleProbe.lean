import GSTPrefixOneSpacetimeIncidenceControl
import GSTCanonicalBoundaryRigidity
import GSTCanonicalEnergyControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTSpacetimeV2

namespace GSTPrefixOneCanonicalRectangleProbe

/-- Shifted form of the exact signed x2/base3 spacetime divergence.  This is
identical to the origin-based rectangle law, but observes the physical rows
`b, ..., b + K - 1`.  No terminal-state or support hypothesis is introduced. -/
theorem physical_signed_rectangle_incidence_shifted_exact
    (R L b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      Finset.sum (Finset.range L) (fun r =>
        GSTPhysicalKernel.signedKernelTwice
          (GSTPhysicalKernel.binaryColumnCarry R (b+j) r)
          (GSTPhysicalKernel.binaryColumnDigit R (b+j) r))) =
      14 *
        (Finset.sum (Finset.range K) (fun j =>
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) L)) -
          Finset.sum (Finset.range K) (fun j =>
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) 0))) +
      7 * Finset.sum (Finset.range K) (fun j =>
        Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) r) *
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) (r+1)))) := by
  calc
    Finset.sum (Finset.range K) (fun j =>
        Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.signedKernelTwice
            (GSTPhysicalKernel.binaryColumnCarry R (b+j) r)
            (GSTPhysicalKernel.binaryColumnDigit R (b+j) r))) =
      Finset.sum (Finset.range K) (fun j =>
        14 *
          (GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) L) -
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) 0)) +
        7 * Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) r) *
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R (b+j) (r+1)))) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact GSTPhysicalKernel.signedKernelTwice_physical_telescope
          R (b+j) L
    _ = 14 *
          (Finset.sum (Finset.range K) (fun j =>
              GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R (b+j) L)) -
            Finset.sum (Finset.range K) (fun j =>
              GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R (b+j) 0))) +
        7 * Finset.sum (Finset.range K) (fun j =>
          Finset.sum (Finset.range L) (fun r =>
            GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R (b+j) r) *
              GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R (b+j) (r+1)))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_sub_distrib]

/-- Exact canonical specialization through the earliest child gate.  It keeps
all boundary and interior incidence terms visible so the next proof step is an
arithmetic/geometry statement rather than another semantic transport lemma. -/
theorem canonical_prefix_one_shifted_signed_rectangle
    (s n q : Nat) (hs : 1 ≤ s) :
    let E := GSTSpacetimeV2.canonicalFullEnergy s n
    let L := GSTSpacetimeV2.canonicalBinaryWidth s
    let b := s + 2
    Finset.sum (Finset.range (q+1)) (fun j =>
      Finset.sum (Finset.range L) (fun r =>
        GSTPhysicalKernel.signedKernelTwice
          (GSTPhysicalKernel.binaryColumnCarry E (b+j) r)
          (GSTPhysicalKernel.binaryColumnDigit E (b+j) r))) =
      14 *
        (Finset.sum (Finset.range (q+1)) (fun j =>
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit E (b+j) L)) -
          Finset.sum (Finset.range (q+1)) (fun j =>
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit E (b+j) 0))) +
      7 * Finset.sum (Finset.range (q+1)) (fun j =>
        Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit E (b+j) r) *
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit E (b+j) (r+1)))) := by
  dsimp only
  exact physical_signed_rectangle_incidence_shifted_exact
    (GSTSpacetimeV2.canonicalFullEnergy s n)
    (GSTSpacetimeV2.canonicalBinaryWidth s) (s+2) (q+1)

#check physical_signed_rectangle_incidence_shifted_exact
#check canonical_prefix_one_shifted_signed_rectangle
#print axioms physical_signed_rectangle_incidence_shifted_exact
#print axioms canonical_prefix_one_shifted_signed_rectangle

end GSTPrefixOneCanonicalRectangleProbe
