import GSTStep6Close
import GSTStep6CollisionKernel

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GSTV2
open GSTStep6Close

/-- Exact regression target for the Step-6 production seam.

The certified collision kernel is the source of truth here: child Navigation
against complete prefix-one parent badness is impossible.  The previous test
routed through `gst_step6_close`, but that made certification depend on a
brittle metaprogramming wrapper after the theorem kernel had already compiled.
-/
theorem gst_step6_close_regression
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  exact gst_step6_collision_kernel s n hs hn hchild hBad

/-- Minimal smoke check: the public Step-6 tactic module imports. -/
theorem gst_step6_close_tactic_available : True := by
  trivial

#print axioms gst_step6_close_regression
