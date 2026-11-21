import GSTWorldCosmology
import Mathlib

/-!
# GST original limitless cosmos: finite native observations are always exact

This is a directly source-grounded topological piece of the author's
NEW all-cardinal/cosmology proof program, not a replacement P1 test.

Original GSTWorldCosmology:
  CompletedCosmos = (Nat times Nat) -> Int
  CompactCosmos = (Nat times Nat) ->_0 Int
The statements below build a GENUINE finite-support GST state matching
ANY prescribed completed GST universe on ANY finite set of information
cells. Hence CompactCosmos is dense in CompletedCosmos under the
coordinatewise product-of-discrete-integers topology.

This theorem is internal signal topology, not an algebraic original-X
Chow cycle-class realization. The latter must be constructed separately
before inferring rational Hodge algebraicity from this density.
-/

set_option maxHeartbeats 1000000
noncomputable section

namespace GSTCardinalTopologicalFiniteWindowLanding

open GSTWorldCosmology

/-- The exact old finite-window observation has a genuinely compact
native GST realization, for ANY original completed signal. -/
theorem completed_has_compact_matching_window
    (f : CompletedCosmos) (A B : ℕ) :
    ∃ g : CompactCosmos,
      observe A B (fun c => g c) = observe A B f := by
  refine ⟨compactWindow (observe A B f), ?_⟩
  funext c
  have h := compactWindow_apply (observe A B f)
    (c.1.val, c.2.val)
  change (compactWindow (observe A B f)) (c.1.val,c.2.val) =
    f (c.1.val,c.2.val)
  rw [h]
  simp [extendWindow, observe, c.1.isLt, c.2.isLt]

/-- The stronger topology-facing statement: ANY finite set of
observed GST signal cells can be matched exactly by one compact source,
regardless of the size of the limitless ambient coordinate family. -/
theorem completed_has_compact_matching_finite_cells
    (f : CompletedCosmos) (S : Finset CosmicCell) :
    ∃ g : CompactCosmos, ∀ c ∈ S, g c = f c := by
  let A : ℕ := S.sup Prod.fst + 1
  let B : ℕ := S.sup Prod.snd + 1
  refine ⟨compactWindow (observe A B f), ?_⟩
  intro c hc
  have hA : c.1 < A := by
    dsimp [A]
    exact Nat.lt_succ_of_le (Finset.le_sup hc)
  have hB : c.2 < B := by
    dsimp [B]
    exact Nat.lt_succ_of_le (Finset.le_sup hc)
  rw [compactWindow_apply]
  simp [extendWindow, observe, hA, hB]

#check completed_has_compact_matching_window
#check completed_has_compact_matching_finite_cells
#print axioms completed_has_compact_matching_window
#print axioms completed_has_compact_matching_finite_cells

end GSTCardinalTopologicalFiniteWindowLanding
