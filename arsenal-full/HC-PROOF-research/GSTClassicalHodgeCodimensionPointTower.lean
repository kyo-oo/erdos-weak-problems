import GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
import GSTClassicalHodgeCodimensionZeroDegreeApex
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — CODIMENSION POINT TOWER

This module removes the ghost-indexed codimension-point existence burden from
GST Plane Completeness.

The preceding principal-cut theorem already proves that nonvanishing of the
native principal-cut image of an actual codimension-p point manufactures an
actual ambient codimension-(p+1) point.  The projective carrier already has a
canonical codimension-zero apex.  Therefore one uniform LOCAL law saying that
the native principal cut of every tower point survives recursively generates
actual codimension points at every finite weight.

The uniform survival law remains a hypothesis; induction does not prove it.
The unconditional construction below instead follows actual exact cuts to a
requested finite weight and returns either a reached point or a certified
stopped cut.  Its horizon is arbitrary: it imposes no fixed bound on the GST
universe and makes no unjustified claim that every individual carrier survives
at all weights.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCodimensionPointTower

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
open GSTClassicalHodgeCodimensionZeroDegreeApex
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSingleExactSuccessorSurvival

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **UNIFORM LOCAL PRINCIPAL-CUT SURVIVAL LAW.**

Every actual codimension-p point has a nonzero geometry-built principal-cut
successor.  This law is purely native and contains no Hodge target or ghost
index. -/
def NativePointSuccessorNonvanishing
    (V : SmoothProjectiveComplexScheme) : Prop :=
  ∀ (p : Nat) (x : CodimensionPoint V.X p),
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0

/-- **CONDITIONAL ACTUAL CODIMENSION-POINT TOWER.**

Starting from the canonical codimension-zero generic apex, repeatedly extract
the actual exact ambient successor forced by native principal-cut
nonvanishing. -/
noncomputable def codimensionPointTower
    (V : SmoothProjectiveComplexScheme)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V) :
    (p : Nat) → CodimensionPoint V.X p
  | 0 => apexCodimensionZeroPoint V
  | p + 1 =>
      Classical.choice
        (exists_codimensionPoint_succ_of_native_point_nonzero
          (V := V) p (codimensionPointTower V hstep p)
          (hstep p (codimensionPointTower V hstep p)))

/-- Every finite codimension therefore has an actual point under the single
uniform local survival law. -/
theorem codimensionPoint_exists_of_nativePointSuccessorNonvanishing
    (V : SmoothProjectiveComplexScheme)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V)
    (p : Nat) :
    Nonempty (CodimensionPoint V.X p) :=
  ⟨codimensionPointTower V hstep p⟩

/-- In particular every weight selected by a hypothetical omniversal separator
ghost has an actual codimension point.  The ghost contributes only its natural
number weight; no ghost-specific geometric existence axiom remains. -/
theorem ghostCodimensionPoints_of_nativePointSuccessorNonvanishing
    (G : GeometricCycleClassSpine V H)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V) :
    ∀ E : OmniversalSeparatorGhost G,
      Nonempty (CodimensionPoint V.X E.weight) := by
  intro E
  exact codimensionPoint_exists_of_nativePointSuccessorNonvanishing
    V hstep E.weight

/-! ## Unconditional finite cut search with a stop certificate

The search chooses an actual member of the exact successor finset at each
successful step.  A stopped result certifies this selected path, not the
nonexistence of points or of other successful paths on the carrier.
-/

/-- A proof-relevant history of genuine exact principal-cut steps. -/
inductive NativeCutPath (V : SmoothProjectiveComplexScheme) :
    (p : Nat) → CodimensionPoint V.X p → Type
  | root (x : CodimensionPoint V.X 0) : NativeCutPath V 0 x
  | step {p : Nat} {x : CodimensionPoint V.X p}
      (history : NativeCutPath V p x)
      (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
      (hy : y ∈ relativeCodimensionOneFinset V x.1)
      (he : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
      NativeCutPath V (p + 1) ⟨ambientSuccessorPoint V x.1 y, he⟩

/-- A reached weight contains its actual point and complete native cut path. -/
structure NativeCutReached (V : SmoothProjectiveComplexScheme) (p : Nat) where
  point : CodimensionPoint V.X p
  history : NativeCutPath V p point

/-- The selected native path stopped strictly before the requested weight. -/
structure NativeCutStop (V : SmoothProjectiveComplexScheme) (target : Nat) where
  level : Nat
  before_target : level < target
  reached : NativeCutReached V level
  exact_locus_empty : exactRelativeSuccessorFinset V level reached.point = ∅

/-- A stop certificate proves the actual native cut is zero. -/
theorem NativeCutStop.native_cut_eq_zero
    {target : Nat} (S : NativeCutStop V target) :
    successorNativeOperator V S.level
      (codimensionPointCycle V.X S.level S.reached.point) = 0 :=
  (native_point_eq_zero_iff_exact_successor_empty S.level S.reached.point).2
    S.exact_locus_empty

/-- Naturality transports a native stop to a zero cohomological cut, without
any projective degree or nonvanishing assumption. -/
theorem NativeCutStop.cohomological_cut_eq_zero
    {target : Nat} (S : NativeCutStop V target)
    (G : GeometricCycleClassSpine V H) :
    (G.principalCutPair S.level).cohomologyOperator
      (H.cycleClass S.level
        (codimensionPointCycle V.X S.level S.reached.point)) = 0 := by
  have h := (G.principalCutPair S.level).cycleClass_natural
    (codimensionPointCycle V.X S.level S.reached.point)
  rw [G.principalCutPair_native S.level, S.native_cut_eq_zero, map_zero] at h
  exact h.symm

/-- **UNCONDITIONAL CUT SEARCH.** No survival axiom occurs in this definition.
The construction is classical/noncomputable, as is the existing geometric cut
finset; it is not a claim of a numerical algorithm for scheme points. -/
noncomputable def nativeCutSearch
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] :
    (target : Nat) → Sum (NativeCutReached V target) (NativeCutStop V target)
  | 0 => .inl ⟨apexCodimensionZeroPoint V,
      NativeCutPath.root (apexCodimensionZeroPoint V)⟩
  | p + 1 =>
    match nativeCutSearch V p with
    | .inr S => .inr {
        level := S.level
        before_target := Nat.lt_trans S.before_target (Nat.lt_succ_self p)
        reached := S.reached
        exact_locus_empty := S.exact_locus_empty
      }
    | .inl R => by
        classical
        by_cases hs : (exactRelativeSuccessorFinset V p R.point).Nonempty
        · let y := Classical.choose hs
          have hy := Classical.choose_spec hs
          have hm := (mem_exactRelativeSuccessorFinset V p R.point y).1 hy
          exact .inl ⟨⟨ambientSuccessorPoint V R.point.1 y, hm.2⟩,
            NativeCutPath.step R.history y hm.1 hm.2⟩
        · exact .inr {
            level := p
            before_target := Nat.lt_succ_self p
            reached := R
            exact_locus_empty := Finset.not_nonempty_iff_eq_empty.mp hs
          }

/-- Every requested weight is either reached or has a concrete stopped cut
on the selected finite native path. -/
theorem native_cut_reached_or_stopped
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] (target : Nat) :
    Nonempty (NativeCutReached V target) ∨ Nonempty (NativeCutStop V target) := by
  cases nativeCutSearch V target with
  | inl R => exact Or.inl ⟨R⟩
  | inr S => exact Or.inr ⟨S⟩

/-- Uniform survival excludes every stop certificate.  The converse direction
is not claimed: exclusion on one selected path need not imply all-point survival. -/
theorem no_nativeCutStop_of_uniform_survival
    (hstep : NativePointSuccessorNonvanishing V) (target : Nat) :
    IsEmpty (NativeCutStop V target) := by
  refine ⟨?_⟩
  intro S
  exact hstep S.level S.reached.point S.native_cut_eq_zero

/-- Native cuts into an empty codimension stratum vanish.  Therefore the
uniform survival premise cannot be inferred merely from the existence of an
unbounded cosmic address space. -/
theorem native_cut_eq_zero_of_next_stratum_empty
    (p : Nat) (x : CodimensionPoint V.X p)
    [IsEmpty (CodimensionPoint V.X (p + 1))] :
    successorNativeOperator V p (codimensionPointCycle V.X p x) = 0 := by
  by_contra h
  obtain ⟨y⟩ := exists_codimensionPoint_succ_of_native_point_nonzero p x h
  exact isEmptyElim y

/-- A populated stratum followed by an empty one refutes uniform cut survival. -/
theorem not_uniform_survival_of_next_stratum_empty
    (p : Nat) (x : CodimensionPoint V.X p)
    [IsEmpty (CodimensionPoint V.X (p + 1))] :
    ¬ NativePointSuccessorNonvanishing V := by
  intro hstep
  exact hstep p x (native_cut_eq_zero_of_next_stratum_empty p x)

#print axioms nativeCutSearch
#print axioms NativeCutStop.native_cut_eq_zero
#print axioms NativeCutStop.cohomological_cut_eq_zero
#print axioms native_cut_reached_or_stopped
#print axioms not_uniform_survival_of_next_stratum_empty

#check NativePointSuccessorNonvanishing
#check codimensionPointTower
#check codimensionPoint_exists_of_nativePointSuccessorNonvanishing
#check ghostCodimensionPoints_of_nativePointSuccessorNonvanishing

#print axioms codimensionPointTower
#print axioms codimensionPoint_exists_of_nativePointSuccessorNonvanishing
#print axioms ghostCodimensionPoints_of_nativePointSuccessorNonvanishing

end GSTClassicalHodgeCodimensionPointTower
