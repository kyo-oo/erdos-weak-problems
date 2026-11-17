import GSTClassicalHodgeCompactPresentationRoundtrip
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeLiveApexSpineFanFinale

/-!
# GST CLASSICAL HODGE — EXACT VERTICAL CUT RAYS

The apex/spine/fan normal form isolates one remaining vertical liveness question:
when a Hodge sheet is live, why is the canonical projective cut tower nonzero?

The geometry of the principal-cut operator makes a stronger local reduction
possible.  At presentation level every exact successor contributes a unit atom
and every non-exact candidate contributes zero.  Therefore all transition
coefficients are nonnegative.

Start at any component-generic point occurring with coefficient one in the
canonical codimension-zero fundamental presentation.  If one relative
codimension-one successor survives the exact ambient stratum at every chosen
step, then the endpoint of that single vertical ray has strictly positive
coefficient in the full canonical cut presentation.  Other branches can merge
into it, but cannot cancel it because every transition coefficient is
nonnegative.

Projective degree is strictly positive on every codimension point.  Hence the
full canonical cut presentation has strictly positive Betti trace, so its
actual cycle class is nonzero.

Thus the vertical part of GST Graph V2 does NOT require all possible branches
to survive.  One exact root-to-weight ray suffices to certify the live node.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeExactVerticalCutRay

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeLiveApexSpineFanFinale
open GSTClassicalHodgeCanonicalCutProgramSpine
open GSTClassicalHodgeRootedStrictRelationFan
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Pointwise nonnegativity of a finite native codimension presentation. -/
def PresentationNonnegative
    {p : Nat} (φ : FiniteCodimensionPresentation V.X p) : Prop :=
  ∀ x, 0 ≤ φ x

/-- Every exact-stratum successor atom has coefficient zero or one, hence is
pointwise nonnegative. -/
theorem successorAtomPresentation_nonnegative
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    PresentationNonnegative (V := V) (successorAtomPresentation V p x y) := by
  intro z
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    by_cases hz : z = (⟨ambientSuccessorPoint V x.1 y, hy⟩ :
        CodimensionPoint V.X (p + 1))
    · subst z
      simp
    · simp [hz]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp

/-- The complete successor presentation of one source point is nonnegative. -/
theorem successorPresentation_nonnegative
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    PresentationNonnegative (V := V) (successorPresentation V p x) := by
  intro z
  classical
  unfold successorPresentation
  rw [Finset.sum_apply]
  exact Finset.sum_nonneg fun y hy =>
    successorAtomPresentation_nonnegative (V := V) p x y z

/-- A selected exact successor occurs with strictly positive coefficient in the
full successor presentation of its source atom. -/
theorem successorPresentation_exact_target_pos
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y0 : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy0Mem : y0 ∈ relativeCodimensionOneFinset V x.1)
    (hy0Exact : Order.coheight (ambientSuccessorPoint V x.1 y0) = p + 1) :
    0 < successorPresentation V p x
      (⟨ambientSuccessorPoint V x.1 y0, hy0Exact⟩ :
        CodimensionPoint V.X (p + 1)) := by
  classical
  unfold successorPresentation
  rw [Finset.sum_apply]
  apply Finset.sum_pos'
  · intro y hy
    exact successorAtomPresentation_nonnegative (V := V) p x y _
  · refine ⟨y0, hy0Mem, ?_⟩
    rw [successorAtomPresentation_eq_single V p x y0 hy0Exact]
    simp

/-- The free successor operator preserves pointwise nonnegativity. -/
theorem successorPresentationOperator_nonnegative
    (p : Nat)
    (φ : FiniteCodimensionPresentation V.X p)
    (hφ : PresentationNonnegative (V := V) φ) :
    PresentationNonnegative (V := V) (successorPresentationOperator V p φ) := by
  intro z
  classical
  change 0 ≤ φ.sum (fun x q => q • successorPresentation V p x) z
  rw [Finsupp.sum_apply]
  apply Finset.sum_nonneg
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (hφ x) (successorPresentation_nonnegative (V := V) p x z)

/-- If a source coefficient is positive and one exact successor is selected,
the target coefficient after the full free transition is positive.  All other
source/branch contributions are nonnegative and therefore cannot cancel it. -/
theorem successorPresentationOperator_exact_target_pos
    (p : Nat)
    (φ : FiniteCodimensionPresentation V.X p)
    (hφ : PresentationNonnegative (V := V) φ)
    (x : CodimensionPoint V.X p)
    (hx : 0 < φ x)
    (y0 : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy0Mem : y0 ∈ relativeCodimensionOneFinset V x.1)
    (hy0Exact : Order.coheight (ambientSuccessorPoint V x.1 y0) = p + 1) :
    0 < successorPresentationOperator V p φ
      (⟨ambientSuccessorPoint V x.1 y0, hy0Exact⟩ :
        CodimensionPoint V.X (p + 1)) := by
  classical
  let z : CodimensionPoint V.X (p + 1) :=
    ⟨ambientSuccessorPoint V x.1 y0, hy0Exact⟩
  change 0 < φ.sum (fun a q => q • successorPresentation V p a) z
  rw [Finsupp.sum_apply]
  apply Finset.sum_pos'
  · intro a ha
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (hφ a) (successorPresentation_nonnegative (V := V) p a z)
  · have hxmem : x ∈ φ.support := Finsupp.mem_support_iff.mpr (ne_of_gt hx)
    refine ⟨x, hxmem, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos hx
      (successorPresentation_exact_target_pos (V := V) p x y0 hy0Mem hy0Exact)

/-- Finite-presentation version of the canonical projective cut tower. -/
noncomputable def canonicalCutPresentation
    (V : SmoothProjectiveComplexScheme) :
    (p : Nat) → FiniteCodimensionPresentation V.X p
  | 0 => codimensionZeroPresentation V
  | p + 1 => successorPresentationOperator V p (canonicalCutPresentation V p)

@[simp]
theorem canonicalCutPresentation_zero
    (V : SmoothProjectiveComplexScheme) :
    canonicalCutPresentation V 0 = codimensionZeroPresentation V := rfl

@[simp]
theorem canonicalCutPresentation_succ
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    canonicalCutPresentation V (p + 1) =
      successorPresentationOperator V p (canonicalCutPresentation V p) := rfl

/-- The finite presentation tower is exactly the already-existing native
`projectiveCutTower`; no new geometric tower is introduced. -/
theorem realize_canonicalCutPresentation
    (V : SmoothProjectiveComplexScheme) :
    ∀ p : Nat,
      realizeFiniteCodimensionPresentation V.X p
        (canonicalCutPresentation V p) = projectiveCutTower V p := by
  intro p
  induction p with
  | zero =>
      rfl
  | succ p ih =>
      rw [canonicalCutPresentation_succ, projectiveCutTower_succ]
      rw [← ih]
      letI : CompactSpace V.X := smoothProjectiveCompactSpace V
      simp [successorNativeOperator, successorFiniteNativeOperator,
        presentationOfNativeCycleLinear_apply,
        presentation_realizeFiniteCodimensionPresentation]

/-- The base presentation is pointwise nonnegative. -/
theorem codimensionZeroPresentation_nonnegative
    (V : SmoothProjectiveComplexScheme) :
    PresentationNonnegative (V := V) (codimensionZeroPresentation V) := by
  intro x
  classical
  unfold codimensionZeroPresentation
  rw [Finset.sum_apply]
  apply Finset.sum_nonneg
  intro y hy
  by_cases hxy : x = y
  · subst y
    simp
  · simp [hxy]

/-- Every selected component-generic apex occurs in the base presentation with
strictly positive coefficient (indeed coefficient one). -/
theorem codimensionZeroPresentation_pos_of_mem
    (V : SmoothProjectiveComplexScheme)
    (x : CodimensionPoint V.X 0)
    (hx : x ∈ codimensionZeroPointFinset V) :
    0 < codimensionZeroPresentation V x := by
  classical
  unfold codimensionZeroPresentation
  rw [Finset.sum_apply]
  apply Finset.sum_pos'
  · intro y hy
    by_cases hxy : x = y
    · subst y
      simp
    · simp [hxy]
  · refine ⟨x, hx, ?_⟩
    simp

/-- Every level of the finite canonical cut presentation is pointwise
nonnegative. -/
theorem canonicalCutPresentation_nonnegative
    (V : SmoothProjectiveComplexScheme) :
    ∀ p : Nat, PresentationNonnegative (V := V) (canonicalCutPresentation V p) := by
  intro p
  induction p with
  | zero => exact codimensionZeroPresentation_nonnegative V
  | succ p ih =>
      exact successorPresentationOperator_nonnegative (V := V) p
        (canonicalCutPresentation V p) ih

/-- A single exact vertical GST ray.  The base vertex is one actual component
generic point occurring in the canonical codimension-zero presentation.  Each
step chooses one relative coheight-one successor which survives the exact
ambient `p+1` grading filter. -/
inductive ExactVerticalCutRay
    (V : SmoothProjectiveComplexScheme) :
    (p : Nat) → CodimensionPoint V.X p → Type
  | base
      (x : CodimensionPoint V.X 0)
      (hx : x ∈ codimensionZeroPointFinset V) :
      ExactVerticalCutRay V 0 x
  | step
      {p : Nat}
      {x : CodimensionPoint V.X p}
      (ray : ExactVerticalCutRay V p x)
      (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
      (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
      (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
      ExactVerticalCutRay V (p + 1)
        (⟨ambientSuccessorPoint V x.1 y, hyExact⟩ :
          CodimensionPoint V.X (p + 1))

/-- The endpoint of one exact vertical ray has strictly positive coefficient
in the FULL canonical cut presentation at that weight. -/
theorem ExactVerticalCutRay.endpoint_coefficient_pos
    {p : Nat}
    {x : CodimensionPoint V.X p}
    (ray : ExactVerticalCutRay V p x) :
    0 < canonicalCutPresentation V p x := by
  induction ray with
  | base x hx =>
      exact codimensionZeroPresentation_pos_of_mem V x hx
  | @step p x ray y hyMem hyExact ih =>
      exact successorPresentationOperator_exact_target_pos
        (V := V) p (canonicalCutPresentation V p)
        (canonicalCutPresentation_nonnegative V p) x ih y hyMem hyExact

/-- Bundle existence of a surviving root-to-weight vertical ray without
choosing a globally distinguished endpoint. -/
structure ExactVerticalCutRayCertificate
    (V : SmoothProjectiveComplexScheme) (p : Nat) where
  endpoint : CodimensionPoint V.X p
  ray : ExactVerticalCutRay V p endpoint

/-- A nonnegative finite presentation with one positive coefficient has
strictly positive weighted degree whenever every point weight is positive. -/
theorem weighted_sum_pos_of_nonnegative_of_one_pos
    {p : Nat}
    (φ : FiniteCodimensionPresentation V.X p)
    (hφ : PresentationNonnegative (V := V) φ)
    (x0 : CodimensionPoint V.X p)
    (hx0 : 0 < φ x0)
    (degree : CodimensionPoint V.X p → ℚ)
    (hdegree : ∀ x, 0 < degree x) :
    0 < φ.sum (fun x a => a * degree x) := by
  classical
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (hφ x) (le_of_lt (hdegree x))
  · have hxmem : x0 ∈ φ.support := Finsupp.mem_support_iff.mpr (ne_of_gt hx0)
    exact ⟨x0, hxmem, mul_pos hx0 (hdegree x0)⟩

/-- **ONE VERTICAL RAY ⇒ POSITIVE PROJECTIVE TRACE.** -/
theorem trace_projectiveCutTower_pos_of_exactVerticalRay
    (D : ProjectiveDegreeTraceSemantics V H)
    {p : Nat}
    {x : CodimensionPoint V.X p}
    (ray : ExactVerticalCutRay V p x) :
    0 < D.trace p (H.cycleClass p (projectiveCutTower V p)) := by
  rw [← realize_canonicalCutPresentation V p]
  rw [D.trace_realize_presentation]
  exact weighted_sum_pos_of_nonnegative_of_one_pos
    (V := V)
    (canonicalCutPresentation V p)
    (canonicalCutPresentation_nonnegative V p)
    x ray.endpoint_coefficient_pos
    (D.pointDegree p)
    (D.pointDegree_pos p)

/-- **ONE VERTICAL RAY ⇒ LIVE CANONICAL CUT NODE.**
This is the key graph-theoretic liveness theorem: a single exact surviving
root-to-weight path rules out vanishing of the whole canonical tower class. -/
theorem cycleClass_projectiveCutTower_ne_zero_of_exactVerticalRay
    (D : ProjectiveDegreeTraceSemantics V H)
    {p : Nat}
    {x : CodimensionPoint V.X p}
    (ray : ExactVerticalCutRay V p x) :
    H.cycleClass p (projectiveCutTower V p) ≠ 0 := by
  intro hzero
  have hpos := trace_projectiveCutTower_pos_of_exactVerticalRay D ray
  rw [hzero, LinearMap.map_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Certificate form used by the live apex/spine/fan finale. -/
theorem cycleClass_projectiveCutTower_ne_zero_of_certificate
    (D : ProjectiveDegreeTraceSemantics V H)
    {p : Nat}
    (C : ExactVerticalCutRayCertificate V p) :
    H.cycleClass p (projectiveCutTower V p) ≠ 0 :=
  cycleClass_projectiveCutTower_ne_zero_of_exactVerticalRay D C.ray

/-- **VERTICAL-RAY + HORIZONTAL-FAN EXACT HODGE FINALE.**
For every live Hodge sheet, one exact vertical cut ray certifies the canonical
spine node.  One rooted strict-relation fan from that node then compiles every
basis direction and hence every Hodge class into one graded correspondence
program from the geometric origin. -/
theorem exactHodge_of_verticalRays_and_rootedFans
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p)
    (fan : ∀ p : Nat, ∀ hlive : HodgeWeightLive H p,
      RootedStrictRelationFan
        (canonicalCutOrbitSeed G p
          (cycleClass_projectiveCutTower_ne_zero_of_certificate
            D (vertical p hlive)))) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply exactHodge_of_live_apexSpineFans G
    (fun p hlive =>
      cycleClass_projectiveCutTower_ne_zero_of_certificate
        D (vertical p hlive))
  exact fan

#check PresentationNonnegative
#check canonicalCutPresentation
#check realize_canonicalCutPresentation
#check ExactVerticalCutRay
#check ExactVerticalCutRay.endpoint_coefficient_pos
#check ExactVerticalCutRayCertificate
#check trace_projectiveCutTower_pos_of_exactVerticalRay
#check cycleClass_projectiveCutTower_ne_zero_of_exactVerticalRay
#check exactHodge_of_verticalRays_and_rootedFans

#print axioms realize_canonicalCutPresentation
#print axioms ExactVerticalCutRay.endpoint_coefficient_pos
#print axioms trace_projectiveCutTower_pos_of_exactVerticalRay
#print axioms cycleClass_projectiveCutTower_ne_zero_of_exactVerticalRay
#print axioms exactHodge_of_verticalRays_and_rootedFans

end GSTClassicalHodgeExactVerticalCutRay
