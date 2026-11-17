import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2PerfectPowerAncestry

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTU2DEventTransport

/-- A graph whose base energy is `4^K` is the absolute perfect-power sheet
started from energy `1`, shifted horizontally by `K`, at every arithmetic
observable.  The bookkeeping `horizontal` field is intentionally excluded:
only the physical cell coordinates are identified. -/
theorem power_origin_observables_exact
    (K t p : Nat) :
    (graph (4^K) t p).seven.carry = (graph 1 (K+t) p).seven.carry ∧
    (graph (4^K) t p).seven.digit = (graph 1 (K+t) p).seven.digit ∧
    (graph (4^K) t p).eventCode = (graph 1 (K+t) p).eventCode ∧
    (graph (4^K) t p).uCharge = (graph 1 (K+t) p).uCharge ∧
    (graph (4^K) t p).mixedCharge = (graph 1 (K+t) p).mixedCharge ∧
    (graph (4^K) t p).crossingCharge = (graph 1 (K+t) p).crossingCharge ∧
    (graph (4^K) t p).survive = (graph 1 (K+t) p).survive := by
  have hpow : 4^t * 4^K = 4^(K+t) * 1 := by
    rw [Nat.mul_one]
    calc
      4^t * 4^K = 4^(t+K) := (Nat.pow_add 4 t K).symm
      _ = 4^(K+t) := by rw [Nat.add_comm]
  simp only [graph, cell, GSTCanonicalSevenAxisBridge.vertex]
  rw [hpow]
  simp

/-- Happy/event-eight is invariant under the same exact perfect-power
horizontal reindexing. -/
theorem power_origin_happy_iff
    (K t p : Nat) :
    HappyCell
        (graph (4^K) t p).seven.carry
        (graph (4^K) t p).seven.digit ↔
      HappyCell
        (graph 1 (K+t) p).seven.carry
        (graph 1 (K+t) p).seven.digit := by
  rw [(power_origin_observables_exact K t p).1,
      (power_origin_observables_exact K t p).2.1]

/-- Event-eight itself is invariant under the absolute power-origin shift. -/
theorem power_origin_event_eight_iff
    (K t p : Nat) :
    (graph (4^K) t p).eventCode = 8 ↔
      (graph 1 (K+t) p).eventCode = 8 := by
  rw [(power_origin_observables_exact K t p).2.2.1]


/-! ## Perfect-power horizontal action -/

/-- Re-basing a perfect-power world after `L` horizontal waves is exactly
the same physical world as increasing its perfect-power origin from `K` to
`K+L`.  All enriched observables agree. -/
theorem power_origin_rebase_observables_exact
    (K L t p : Nat) :
    (graph (4^K) (L+t) p).seven.carry =
        (graph (4^(K+L)) t p).seven.carry ∧
    (graph (4^K) (L+t) p).seven.digit =
        (graph (4^(K+L)) t p).seven.digit ∧
    (graph (4^K) (L+t) p).eventCode =
        (graph (4^(K+L)) t p).eventCode ∧
    (graph (4^K) (L+t) p).uCharge =
        (graph (4^(K+L)) t p).uCharge ∧
    (graph (4^K) (L+t) p).mixedCharge =
        (graph (4^(K+L)) t p).mixedCharge ∧
    (graph (4^K) (L+t) p).crossingCharge =
        (graph (4^(K+L)) t p).crossingCharge ∧
    (graph (4^K) (L+t) p).survive =
        (graph (4^(K+L)) t p).survive := by
  have h1 := power_origin_observables_exact K (L+t) p
  have h2 := power_origin_observables_exact (K+L) t p
  rw [Nat.add_assoc] at h2
  exact
    ⟨h1.1.trans h2.1.symm,
      h1.2.1.trans h2.2.1.symm,
      h1.2.2.1.trans h2.2.2.1.symm,
      h1.2.2.2.1.trans h2.2.2.2.1.symm,
      h1.2.2.2.2.1.trans h2.2.2.2.2.1.symm,
      h1.2.2.2.2.2.1.trans h2.2.2.2.2.2.1.symm,
      h1.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.symm⟩

/-- Happy transport is invariant under the same perfect-power re-basing. -/
theorem power_origin_rebase_happy_iff
    (K L t p : Nat) :
    HappyCell
        (graph (4^K) (L+t) p).seven.carry
        (graph (4^K) (L+t) p).seven.digit
      ↔
    HappyCell
        (graph (4^(K+L)) t p).seven.carry
        (graph (4^(K+L)) t p).seven.digit := by
  rw [(power_origin_rebase_observables_exact K L t p).1,
      (power_origin_rebase_observables_exact K L t p).2.1]


#check power_origin_observables_exact
#check power_origin_happy_iff
#check power_origin_event_eight_iff
#check power_origin_rebase_observables_exact
#check power_origin_rebase_happy_iff
#print axioms power_origin_observables_exact
#print axioms power_origin_happy_iff
#print axioms power_origin_event_eight_iff
#print axioms power_origin_rebase_observables_exact

end GSTGraphV2PerfectPowerAncestry
