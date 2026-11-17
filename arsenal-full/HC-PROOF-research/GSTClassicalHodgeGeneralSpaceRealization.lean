import GSTGeneralSpacePartialRealization
import GSTClassicalHodgeGradedGeometricProgramOrbit
import GSTClassicalHodgeExactClayStatement

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceRealization

open GSTGeneralSpace
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- All even rational Betti states, retaining their codimension/weight label. -/
abbrev EvenBettiPoint
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :=
  Σ p : Nat, RationalSingularCohomology H.analytification (2 * p)

/-- Genuine geometric-program reachability between two even Betti states. -/
def GeometricReachability
    (G : GeometricCycleClassSpine V H)
    (x y : EvenBettiPoint V H) : Prop :=
  ∃ P : GradedGeometricProgram V x.1 y.1,
    P.cohomologyEval G x.2 = y.2

/-- The even Betti universe equipped with genuine mixed projective/cut paths. -/
def hodgeGeneralSpace
    (G : GeometricCycleClassSpine V H) : GeneralSpace where
  Point := EvenBettiPoint V H
  Path := GeometricReachability G
  idPath := by
    intro x
    refine ⟨GradedGeometricProgram.id x.1, ?_⟩
    rfl
  compPath := by
    intro x y z hxy hyz
    rcases hxy with ⟨P, hP⟩
    rcases hyz with ⟨Q, hQ⟩
    refine ⟨GradedGeometricProgram.comp P Q, ?_⟩
    change Q.cohomologyEval G (P.cohomologyEval G x.2) = z.2
    rw [hP, hQ]
  comp_id_left := by intros; apply Subsingleton.elim
  comp_id_right := by intros; apply Subsingleton.elim
  comp_assoc := by intros; apply Subsingleton.elim

/-- The total Betti face is literally the point carrier of the Hodge General
Space. -/
def bettiRealization
    (G : GeometricCycleClassSpine V H) :
    Realization (hodgeGeneralSpace G) where
  State := EvenBettiPoint V H
  realize := id

/-- The rational `(p,p)` Hodge locus inside the total Betti General Space. -/
def HodgeLocus
    (G : GeometricCycleClassSpine V H)
    (x : (hodgeGeneralSpace G).Point) : Prop :=
  x.2 ∈ rationalHodgeSubspace (H.hodgeBigrading x.1)

/-- The genuine algebraic-cycle locus inside the total Betti General Space. -/
def NativeLocus
    (G : GeometricCycleClassSpine V H)
    (x : (hodgeGeneralSpace G).Point) : Prop :=
  x.2 ∈ LinearMap.range (H.cycleClass x.1)

/-- Algebraic cycles form a partial realization of the full Betti universe.
No algebraicity of arbitrary Hodge states is assumed. -/
def nativePartialRealization
    (G : GeometricCycleClassSpine V H) :
    PartialRealization (hodgeGeneralSpace G) where
  Domain := NativeLocus G
  State := Σ p : Nat, codimensionCycles V.X p
  realize := by
    intro x hx
    exact ⟨x.1, Classical.choose hx⟩

/-- A native-domain witness really maps back to the represented Betti state. -/
theorem nativePartialRealization_spec
    (G : GeometricCycleClassSpine V H)
    (x : (hodgeGeneralSpace G).Point)
    (hx : NativeLocus G x) :
    H.cycleClass x.1
        ((nativePartialRealization G).realize x hx).2 = x.2 := by
  exact Classical.choose_spec hx

/-- **GENERAL-SPACE NATIVE SYNCHRONIZATION.**
The algebraic partial realization is closed under every genuine graded
geometric path.  This is a direct consequence of the existing master
cycle-class naturality law, not a Hodge-surjectivity assumption. -/
theorem nativeLocus_pathClosed
    (G : GeometricCycleClassSpine V H) :
    (nativePartialRealization G).PathClosed := by
  intro x y hxy hx
  rcases hxy with ⟨P, hP⟩
  rcases hx with ⟨Z, hZ⟩
  refine ⟨P.cycleEval G Z, ?_⟩
  rw [P.cycleClass_cycleEval G Z]
  rw [hZ]
  exact hP

/-- Every genuine General Space path starting at an algebraic Betti state
lands at another algebraic Betti state. -/
theorem nativeLocus_of_reachable
    (G : GeometricCycleClassSpine V H)
    {x y : (hodgeGeneralSpace G).Point}
    (hxy : (hodgeGeneralSpace G).Path x y)
    (hx : NativeLocus G x) :
    NativeLocus G y :=
  nativeLocus_pathClosed G hxy hx

/-- The exact rational Hodge conjecture is precisely inclusion of the Hodge
locus into the native partial-realization domain. -/
theorem exactHodge_iff_hodgeLocus_le_nativeLocus
    (G : GeometricCycleClassSpine V H) :
    EveryHodgeClassIsRationalAlgebraic H ↔
      ∀ x : (hodgeGeneralSpace G).Point,
        HodgeLocus G x → NativeLocus G x := by
  constructor
  · intro h x hx
    exact h x.1 x.2 hx
  · intro h p alpha halpha
    exact h ⟨p, alpha⟩ halpha

#check EvenBettiPoint
#check GeometricReachability
#check hodgeGeneralSpace
#check HodgeLocus
#check NativeLocus
#check nativePartialRealization
#check nativeLocus_pathClosed
#check nativeLocus_of_reachable
#check exactHodge_iff_hodgeLocus_le_nativeLocus

#print axioms nativeLocus_pathClosed
#print axioms exactHodge_iff_hodgeLocus_le_nativeLocus

end GSTClassicalHodgeGeneralSpaceRealization
