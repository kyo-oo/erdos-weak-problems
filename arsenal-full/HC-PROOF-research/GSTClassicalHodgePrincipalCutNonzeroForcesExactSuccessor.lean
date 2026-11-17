import GSTClassicalHodgeProjectiveDegreeTrace

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT NONVANISHING FORCES AN EXACT SUCCESSOR

The geometry-built principal-cut operator is defined by filtering the finite
relative codimension-one locus through the exact ambient codimension `p+1`
stratum.  Previously the seed route supplied one ambient-exact successor as an
external geometric input.

This file reverses that dependency.

If the genuine principal-cut cohomology action on one actual point-cycle class
is nonzero, then cycle-class naturality forces the corresponding native
principal-cut cycle to be nonzero.  But that native cycle is a finite sum of
only exact-stratum atoms with coefficient `+1`; therefore at least one actual
relative successor must lie in ambient codimension `p+1`.

Once projective degree/Betti trace semantics are available, the same exact
survivor gives positive Betti trace.  Hence the principal-cut image itself is a
nonzero algebraic Hodge class and supplies the synchronized native Hodge seed.

No catenary/height-additivity hypothesis, Hodge-basis representative, matrix
unit naturality, or Hodge-surjectivity premise occurs here.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **NATIVE NONVANISHING RECOVERS THE EXACT AMBIENT STRATUM.**

The principal-cut point image can only be nonzero if at least one relative
codimension-one successor survives the operator's exact ambient codimension
filter. -/
theorem exists_exact_relative_successor_of_native_point_nonzero
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hNative :
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0) :
    ∃ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
      y ∈ relativeCodimensionOneFinset V x.1 ∧
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  by_contra hEx
  have hbad :
      ∀ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
        y ∈ relativeCodimensionOneFinset V x.1 →
        Order.coheight (ambientSuccessorPoint V x.1 y) ≠ p + 1 := by
    intro y hy hExact
    apply hEx
    exact ⟨y, hy, hExact⟩
  apply hNative
  rw [successorNativeOperator_point]
  have hpres : successorPresentation V p x = 0 := by
    classical
    unfold successorPresentation
    apply Finset.sum_eq_zero
    intro y hy
    exact successorAtomPresentation_eq_zero V p x y (hbad y hy)
  rw [hpres]
  simp

/-- **NATIVE NONVANISHING PRODUCES AN ACTUAL NEXT-CODIMENSION POINT.**

The exact successor extracted above already carries precisely the equality
needed to inhabit `CodimensionPoint V.X (p+1)`.  Export that geometry directly
instead of forcing downstream files to unpack the relative-cut witness again. -/
theorem exists_codimensionPoint_succ_of_native_point_nonzero
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hNative :
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0) :
    Nonempty (CodimensionPoint V.X (p + 1)) := by
  obtain ⟨y, _hyMem, hyExact⟩ :=
    exists_exact_relative_successor_of_native_point_nonzero
      (V := V) p x hNative
  exact ⟨⟨ambientSuccessorPoint V x.1 y, hyExact⟩⟩

/-- **COHOMOLOGICAL NONVANISHING RECOVERS AN EXACT GEOMETRIC SUCCESSOR.**

Because the geometric cycle-class spine gives an exact commuting square for
the actual principal-cut operator, a nonzero cohomological point image forces
its native point image to be nonzero.  The preceding theorem then extracts an
actual ambient codimension-`p+1` successor. -/
theorem exists_exact_relative_successor_of_principalCut_point_nonzero
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    ∃ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
      y ∈ relativeCodimensionOneFinset V x.1 ∧
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  apply exists_exact_relative_successor_of_native_point_nonzero
    (V := V) p x
  intro hNative
  have hnat :=
    (G.principalCutPair p).cycleClass_natural
      (codimensionPointCycle V.X p x)
  rw [G.principalCutPair_native p, hNative, LinearMap.map_zero] at hnat
  exact hCoh hnat.symm

/-- **COHOMOLOGICAL NONVANISHING PRODUCES AN ACTUAL NEXT-CODIMENSION POINT.**

This is the Hodge-spine-facing form of the strengthened successor theorem. -/
theorem exists_codimensionPoint_succ_of_principalCut_point_nonzero
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    Nonempty (CodimensionPoint V.X (p + 1)) := by
  obtain ⟨y, _hyMem, hyExact⟩ :=
    exists_exact_relative_successor_of_principalCut_point_nonzero
      (V := V) (H := H) G p x hCoh
  exact ⟨⟨ambientSuccessorPoint V x.1 y, hyExact⟩⟩

/-- **NONZERO PRINCIPAL-CUT ACTION PRODUCES A GENUINE ALGEBRAIC HODGE SEED.**

The spine's commuting square directly identifies the class of the actual
native cut with the nonzero cohomological image.  Its Hodge type follows from
the spine.  Projective degree, positive trace and an extracted successor are
unnecessary for this implication and are removed from its premises. -/
noncomputable def nativeHodgeSeed_of_principalCut_point_nonzero
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) := by
  let Z : codimensionCycles V.X (p + 1) :=
    successorNativeOperator V p (codimensionPointCycle V.X p x)
  have hclass : H.cycleClass (p + 1) Z ≠ 0 := by
    intro hzero
    have hnat := (G.principalCutPair p).cycleClass_natural
      (codimensionPointCycle V.X p x)
    rw [G.principalCutPair_native p] at hnat
    apply hCoh
    exact hnat.symm.trans hzero
  let alpha : ClassicalHodgeFiber V H (p + 1) :=
    ⟨H.cycleClass (p + 1) Z, G.algebraic_is_hodge (p + 1) Z⟩
  refine {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  apply hclass
  exact congrArg Subtype.val hz

/-- Existential form consumed by orbit/closure arguments. -/
theorem principalCut_point_nonzero_gives_nativeHodgeSeed
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1)) :=
  ⟨nativeHodgeSeed_of_principalCut_point_nonzero G p x hCoh⟩

/-! ## Exact survival classification

These are equivalences for the actual cut, not a new survival postulate.
The reverse implications use the positive native atom count already proved
in `SingleExactSuccessorSurvival`.  In particular native nonvanishing alone
now certifies Betti nonvanishing when degree semantics are available.
-/

/-- Native point survival is exactly nonemptiness of the exact cut locus. -/
theorem native_point_nonzero_iff_exact_successor_nonempty
    (p : Nat) (x : CodimensionPoint V.X p) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 ↔
      (exactRelativeSuccessorFinset V p x).Nonempty := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ :=
      exists_exact_relative_successor_of_native_point_nonzero p x h
    exact ⟨y, (mem_exactRelativeSuccessorFinset V p x y).2 ⟨hy, he⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨hm, he⟩ := (mem_exactRelativeSuccessorFinset V p x y).1 hy
    exact successorNativeOperator_point_ne_zero_of_one_exact V p x y hm he

/-- The cut is zero precisely when its exact successor locus is empty. -/
theorem native_point_eq_zero_iff_exact_successor_empty
    (p : Nat) (x : CodimensionPoint V.X p) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) = 0 ↔
      exactRelativeSuccessorFinset V p x = ∅ := by
  classical
  simpa only [not_not, Finset.not_nonempty_iff_eq_empty] using
    not_congr (native_point_nonzero_iff_exact_successor_nonempty
      (V := V) p x)

/-- Positive degree rules out homological cancellation for this entire native
cut.  No cohomological nonvanishing premise is needed. -/
theorem successor_cycleClass_nonzero_iff_native_nonzero
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) (x : CodimensionPoint V.X p) :
    H.cycleClass (p + 1)
        (successorNativeOperator V p (codimensionPointCycle V.X p x)) ≠ 0 ↔
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  constructor
  · intro h hz
    exact h (by rw [hz, map_zero])
  · intro h hz
    obtain ⟨y, hy, he⟩ :=
      exists_exact_relative_successor_of_native_point_nonzero p x h
    have hp := D.trace_successor_positive_of_one_exact p x y hy he
    rw [hz, map_zero] at hp
    exact (lt_irrefl 0) hp

/-- The positive trace is an exact detector of native cut survival. -/
theorem successor_trace_positive_iff_native_nonzero
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) (x : CodimensionPoint V.X p) :
    0 < D.trace (p + 1)
      (H.cycleClass (p + 1)
        (successorNativeOperator V p (codimensionPointCycle V.X p x))) ↔
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  constructor
  · intro hp hz
    rw [hz, map_zero, map_zero] at hp
    exact (lt_irrefl 0) hp
  · intro h
    obtain ⟨y, hy, he⟩ :=
      exists_exact_relative_successor_of_native_point_nonzero p x h
    exact D.trace_successor_positive_of_one_exact p x y hy he

/-- Degree semantics makes the spine's cohomological cut nonzero exactly when
its geometry-built native cut is nonzero. -/
theorem principalCut_point_nonzero_iff_native_nonzero
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) (x : CodimensionPoint V.X p) :
    (G.principalCutPair p).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0 ↔
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  have hnat := (G.principalCutPair p).cycleClass_natural
    (codimensionPointCycle V.X p x)
  rw [G.principalCutPair_native p] at hnat
  rw [← hnat]
  exact successor_cycleClass_nonzero_iff_native_nonzero D p x

/-- A synchronized seed from a native survival proof, with its Hodge and
cohomological nonzero fields derived from the spine and positive degree. -/
noncomputable def nativeHodgeSeed_of_native_point_nonzero
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) (x : CodimensionPoint V.X p)
    (h : successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) :=
  nativeHodgeSeed_of_principalCut_point_nonzero G p x
    ((principalCut_point_nonzero_iff_native_nonzero G D p x).2 h)

#print axioms native_point_nonzero_iff_exact_successor_nonempty
#print axioms native_point_eq_zero_iff_exact_successor_empty
#print axioms successor_cycleClass_nonzero_iff_native_nonzero
#print axioms successor_trace_positive_iff_native_nonzero
#print axioms principalCut_point_nonzero_iff_native_nonzero
#print axioms nativeHodgeSeed_of_native_point_nonzero

#check exists_exact_relative_successor_of_native_point_nonzero
#check exists_codimensionPoint_succ_of_native_point_nonzero
#check exists_exact_relative_successor_of_principalCut_point_nonzero
#check exists_codimensionPoint_succ_of_principalCut_point_nonzero
#check nativeHodgeSeed_of_principalCut_point_nonzero
#check principalCut_point_nonzero_gives_nativeHodgeSeed

#print axioms exists_exact_relative_successor_of_native_point_nonzero
#print axioms exists_codimensionPoint_succ_of_native_point_nonzero
#print axioms exists_exact_relative_successor_of_principalCut_point_nonzero
#print axioms exists_codimensionPoint_succ_of_principalCut_point_nonzero
#print axioms principalCut_point_nonzero_gives_nativeHodgeSeed

end GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
