import GSTGeneralSpaceCohomology
import GSTGraphV2NonEuclidean
import GSTCausalFoldDefect

namespace GSTGraphV2GeneralSpaceRealization

open GSTGeneralSpace
open GSTGraphV2NonEuclidean

/-- Graph-V2's seven-axis states form a General Space whose paths are finite
reflexive/transitive chains of genuine Graph-V2 forward edges. -/
def graphV2GeneralSpace : GeneralSpace where
  Point := SevenAxes
  Path := Relation.ReflTransGen ForwardEdge
  idPath := fun x => Relation.ReflTransGen.refl
  compPath := fun α β => α.trans β
  comp_id_left := by intros; apply Subsingleton.elim
  comp_id_right := by intros; apply Subsingleton.elim
  comp_assoc := by intros; apply Subsingleton.elim

/-- The seven-axis packet itself is a chart of the General Space sector. -/
def sevenAxesChart : GeneralSpace.Chart graphV2GeneralSpace where
  Coord := SevenAxes
  observe := id

@[simp] theorem sevenAxesChart_exact (a : SevenAxes) :
    sevenAxesChart.observe a = a := rfl

/-- The historical forward edge embeds as a one-step General Space path. -/
def forwardEdgePath {u v : SevenAxes} (h : ForwardEdge u v) :
    graphV2GeneralSpace.Path u v :=
  Relation.ReflTransGen.single h

/-- Every canonical Graph-V2 forward-path step is a General Space path. -/
def canonicalStepPath (R N start L i : Nat) :
    graphV2GeneralSpace.Path
      ((forwardPath R N start L).node i)
      ((forwardPath R N start L).node (i+1)) :=
  forwardEdgePath (forwardPath_edge_exact R N start L i)

/-- The old three-space label becomes an observable of the General Space
sector, not a restriction on the ontology. -/
def spaceObservable : GeneralSpace.Observable graphV2GeneralSpace Space :=
  fun a => a.yPrime

/-- Digit content is another chart observable. -/
def digitObservable : GeneralSpace.Observable graphV2GeneralSpace Nat :=
  fun a => a.z

/-- Carry content is another chart observable. -/
def carryObservable : GeneralSpace.Observable graphV2GeneralSpace Nat :=
  fun a => a.y

/-- Witnesshood is now an intrinsic predicate on this Graph-V2 realization. -/
def witnessPredicate : GeneralSpace.Predicate graphV2GeneralSpace := WitnessAt

/-- The historical arithmetic projection is explicitly a realization into the
General Space sector. -/
def physicalPointRealization (E N t p : Nat) : graphV2GeneralSpace.Point :=
  physicalProjection E N t p

#check graphV2GeneralSpace
#check sevenAxesChart
#check forwardEdgePath
#check canonicalStepPath
#check spaceObservable
#check digitObservable
#check carryObservable
#check witnessPredicate
#check physicalPointRealization

/-! Realized causal fold defects. Forward reachability by itself does not
assert Hodge preservation; the operator square must actually commute. -/
section OperatorDefect
open GSTCausalFoldDefect
variable {R : Type*} [Ring R]

theorem forward_pair_defect
    (P : OperatorRealization graphV2GeneralSpace R)
    {u v w : SevenAxes} (huv : ForwardEdge u v) (hvw : ForwardEdge v w)
    (J K L : R) :
    defect J L (P.operator (graphV2GeneralSpace.compPath
      (forwardEdgePath huv) (forwardEdgePath hvw))) =
      defect K L (P.operator (forwardEdgePath hvw)) *
        P.operator (forwardEdgePath huv) +
      P.operator (forwardEdgePath hvw) *
        defect J K (P.operator (forwardEdgePath huv)) := by
  exact causal_path_defect P (forwardEdgePath huv) (forwardEdgePath hvw) J K L

theorem safe_forward_pair
    (P : OperatorRealization graphV2GeneralSpace R)
    {u v w : SevenAxes} (huv : ForwardEdge u v) (hvw : ForwardEdge v w)
    (J K L : R)
    (hFirst : defect J K (P.operator (forwardEdgePath huv)) = 0)
    (hSecond : defect K L (P.operator (forwardEdgePath hvw)) = 0) :
    defect J L (P.operator (graphV2GeneralSpace.compPath
      (forwardEdgePath huv) (forwardEdgePath hvw))) = 0 := by
  rw [forward_pair_defect P huv hvw J K L, hFirst, hSecond]
  simp

#print axioms forward_pair_defect
#print axioms safe_forward_pair
end OperatorDefect

/-! The spatial experiment needs its own actual General Space sector.
The arithmetic SevenAxes ForwardEdge above is not relabeled as a geometric
curvature edge. Points here retain the full chronological word.
-/
def causalWordSpace (A : Type*) : GeneralSpace where
  Point := List A
  Path xs ys := ∃ suffix, ys=xs++suffix
  idPath := fun xs => ⟨[],by simp⟩
  compPath := by
    intro xs ys zs hxy hyz
    rcases hxy with ⟨a,rfl⟩
    rcases hyz with ⟨b,rfl⟩
    exact ⟨a++b,by simp [List.append_assoc]⟩
  comp_id_left := by intros; apply Subsingleton.elim
  comp_id_right := by intros; apply Subsingleton.elim
  comp_assoc := by intros; apply Subsingleton.elim

def appendCausalFold {A : Type*} (xs : List A) (a : A) :
    (causalWordSpace A).Path xs (xs++[a]) := ⟨[a],rfl⟩

def wordCurvature {V : Type*} [AddCommGroup V] :
    GeneralSpace.Observable (causalWordSpace V) V := List.sum

theorem wordCurvature_composition {V : Type*} [AddCommGroup V] (xs ys : List V) :
    wordCurvature (xs++ys)=wordCurvature xs+wordCurvature ys := by
  simp [wordCurvature,List.sum_append]

theorem inverse_fold_restores_endpoint {V : Type*} [AddCommGroup V] (K : V) :
    wordCurvature [K,-K]=0 := by simp [wordCurvature]

theorem restored_endpoint_can_have_broken_prefix {V : Type*} [AddCommGroup V]
    (K : V) (hK : K ≠ 0) :
    wordCurvature [K] ≠ 0 ∧ wordCurvature [K,-K]=0 := by
  simpa [wordCurvature] using (And.intro hK (add_neg_cancel K))

#print axioms wordCurvature_composition
#print axioms restored_endpoint_can_have_broken_prefix
end GSTGraphV2GeneralSpaceRealization
