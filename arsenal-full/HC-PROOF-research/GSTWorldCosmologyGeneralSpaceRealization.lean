import GSTGeneralSpaceCohomology
import GSTWorldCosmology

namespace GSTWorldCosmologyGeneralSpaceRealization

open GSTGeneralSpace
open GSTWorldCosmology

/-- The old `Nat × Nat` limitless carrier is now one ordered chart-sector of
General Space rather than the ontology of General Space itself. -/
def worldGeneralSpace : GeneralSpace where
  Point := CosmicCell
  Path c d := c.1 ≤ d.1 ∧ c.2 ≤ d.2
  idPath := fun c => ⟨le_rfl, le_rfl⟩
  compPath := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  comp_id_left := by intros; apply Subsingleton.elim
  comp_id_right := by intros; apply Subsingleton.elim
  comp_assoc := by intros; apply Subsingleton.elim

/-- The historical rectangular coordinate carrier is an exact chart. -/
def cosmicCellChart : GeneralSpace.Chart worldGeneralSpace where
  Coord := CosmicCell
  observe := id

@[simp] theorem cosmicCellChart_exact (c : CosmicCell) :
    cosmicCellChart.observe c = c := rfl

/-- Forward movement by `(carry,digit)` is a genuine General Space path. -/
def shiftPath (c : CosmicCell) (carry digit : Nat) :
    worldGeneralSpace.Path c (c.1 + carry, c.2 + digit) := by
  exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Pure carry movement is a General Space path. -/
def carryPath (c : CosmicCell) (n : Nat) :
    worldGeneralSpace.Path c (c.1 + n, c.2) := by
  exact ⟨Nat.le_add_right _ _, le_rfl⟩

/-- Pure digit movement is a General Space path. -/
def digitPath (c : CosmicCell) (n : Nat) :
    worldGeneralSpace.Path c (c.1, c.2 + n) := by
  exact ⟨le_rfl, Nat.le_add_right _ _⟩

/-- Completed GST fields become one realization carried by the General Space
sector.  Evaluation at a cosmic point is the realization map. -/
def completedFieldRealization (f : CompletedCosmos) :
    Realization worldGeneralSpace where
  State := Int
  realize := f

/-- Compact GST fields give the corresponding algebraic realization. -/
def compactFieldRealization (f : CompactCosmos) :
    Realization worldGeneralSpace where
  State := Int
  realize := fun c => f c

/-- Existing finite observations remain exact observations of the same
completed realization. -/
theorem finite_observation_is_chart_restriction
    (A B : Nat) (f : CompletedCosmos) :
    observe A B f = fun c =>
      (completedFieldRealization f).realize (c.1.val, c.2.val) := rfl

#check worldGeneralSpace
#check cosmicCellChart
#check shiftPath
#check carryPath
#check digitPath
#check completedFieldRealization
#check compactFieldRealization
#check finite_observation_is_chart_restriction

end GSTWorldCosmologyGeneralSpaceRealization
