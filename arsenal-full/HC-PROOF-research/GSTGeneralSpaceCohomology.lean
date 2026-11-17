import GSTGeneralSpaceDuality

universe u v w

namespace GSTGeneralSpace

/-- Cohomological structure is an optional realization capability, not part of
General Space ontology.  It is deliberately grading-generic. -/
structure CohomologyGeometry (G : GeneralSpace) (R : Type w)
    [CommSemiring R] where
  Grade : Type w
  Coh : Grade → Type w
  addCommMonoid : ∀ q, AddCommMonoid (Coh q)
  module : ∀ q, Module R (Coh q)
  gradeMul : Grade → Grade → Grade
  cup : ∀ {p q}, Coh p → Coh q → Coh (gradeMul p q)
  cup_zero_left : ∀ {p q} (b : Coh q), cup (0 : Coh p) b = 0
  cup_zero_right : ∀ {p q} (a : Coh p), cup a (0 : Coh q) = 0

namespace CohomologyGeometry

variable {G : GeneralSpace} {R : Type w} [CommSemiring R]

/-- A cohomological observable attached to a General Space point. -/
structure ClassField (C : CohomologyGeometry G R) where
  grade : C.Grade
  classAt : G.Point → C.Coh grade

/-- A graded transport operation, stated independently of coordinates. -/
structure Transport (C : CohomologyGeometry G R) where
  map : ∀ {q : C.Grade} {x y : G.Point}, G.Path x y → C.Coh q → C.Coh q
  map_id : ∀ {q} (x : G.Point) (a : C.Coh q), map (G.idPath x) a = a
  map_comp : ∀ {q} {x y z : G.Point}
      (α : G.Path x y) (β : G.Path y z) (a : C.Coh q),
    map (G.compPath α β) a = map β (map α a)
  map_cup : ∀ {p q} {x y : G.Point} (γ : G.Path x y)
      (a : C.Coh p) (b : C.Coh q),
    map γ (C.cup a b) = C.cup (map γ a) (map γ b)

end CohomologyGeometry

#check CohomologyGeometry
#check CohomologyGeometry.ClassField
#check CohomologyGeometry.Transport


/-! ## GST native cycle geometry versus reversible General Space paths

All GST cohomology, cosmology, CM/NM, and world-transport laws must
respect the REAL native cycle-class map. This new compatibility
theorem proves a sharp algebraicity invariant of reversible GST
recoordination: no series of reversible path operations can turn
an unrepresented cohomology class into an algebraic cycle.

It does not rule out genuinely new sources: an irreversible native
world birth, exceptional Gysin class, or extra geometric cycle can
change the native image. It also does not disprove the Hodge conjecture:
the argument is about the precise power of one kind of GST operator.
-/

namespace NativeCycleRecoordination

variable {G : GeneralSpace}
variable {N H : Type*}
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup H] [Module ℚ H]

/-- A native algebraic cycle class map intertwined with ACTUAL GST
General Space paths, both at the native-cycle and rational Hodge
cohomology levels. No reverse cohomology-to-Chow selector is given. -/
structure CyclePathRealization
    (G : GeneralSpace)
    (N H : Type*)
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup H] [Module ℚ H] where
  cycleClass : N →ₗ[ℚ] H
  nativeTransport :
    ∀ {x y : G.Point}, G.Path x y → N →ₗ[ℚ] N
  hodgeTransport :
    ∀ {x y : G.Point}, G.Path x y → H →ₗ[ℚ] H
  naturality : ∀ {x y : G.Point} (γ : G.Path x y) (Z : N),
    cycleClass (nativeTransport γ Z) =
      hodgeTransport γ (cycleClass Z)
  hodge_id : ∀ (x : G.Point) (alpha : H),
    hodgeTransport (G.idPath x) alpha = alpha
  hodge_comp : ∀ {x y z : G.Point}
    (γ : G.Path x y) (δ : G.Path y z) (alpha : H),
    hodgeTransport (G.compPath γ δ) alpha =
      hodgeTransport δ (hodgeTransport γ alpha)

/-- FORWARD: every actual native Chow representative survives any
general-space geometric path compatible with the cycle-class map. -/
theorem transported_native_cycle_stays_algebraic
    (P : CyclePathRealization G N H)
    {x y : G.Point} (γ : G.Path x y)
    (alpha : H)
    (h : alpha ∈ LinearMap.range P.cycleClass) :
    P.hodgeTransport γ alpha ∈ LinearMap.range P.cycleClass := by
  obtain ⟨Z, hZ⟩ := h
  refine ⟨P.nativeTransport γ Z, ?_⟩
  calc
    P.cycleClass (P.nativeTransport γ Z) =
      P.hodgeTransport γ (P.cycleClass Z) := P.naturality γ Z
    _ = P.hodgeTransport γ alpha := by rw [hZ]

/-- REVERSE: a reversible GST recoordination cannot hide a
nonalgebraic Hodge direction. If the transported class has an
actual rational Chow representative, its backward native transport
constructs a representative of the original class. -/
theorem algebraicity_iff_reversible_general_space_transport
    (P : CyclePathRealization G N H)
    {x y : G.Point}
    (ρ : Recoordination G x y)
    (alpha : H) :
    alpha ∈ LinearMap.range P.cycleClass ↔
      P.hodgeTransport ρ.forward alpha ∈
        LinearMap.range P.cycleClass := by
  constructor
  · exact transported_native_cycle_stays_algebraic P ρ.forward alpha
  · intro h
    obtain ⟨Z, hZ⟩ := h
    refine ⟨P.nativeTransport ρ.backward Z, ?_⟩
    calc
      P.cycleClass (P.nativeTransport ρ.backward Z) =
        P.hodgeTransport ρ.backward (P.cycleClass Z) :=
          P.naturality ρ.backward Z
      _ = P.hodgeTransport ρ.backward
            (P.hodgeTransport ρ.forward alpha) := by rw [hZ]
      _ = P.hodgeTransport
            (G.compPath ρ.forward ρ.backward) alpha := by
              rw [P.hodge_comp]
      _ = P.hodgeTransport (G.idPath x) alpha := by
              rw [ρ.forward_backward]
      _ = alpha := P.hodge_id x alpha

/-- Exact CONTRAPOSITIVE GST obstruction. No generalized world
recoordination, including composition of arbitrarily many
reversible presentations, can magically eliminate a missing
primitive rational Hodge direction from the native image. -/
theorem missing_native_direction_persists_recoordination
    (P : CyclePathRealization G N H)
    {x y : G.Point} (ρ : Recoordination G x y)
    (alpha : H)
    (hMissing : alpha ∉ LinearMap.range P.cycleClass) :
    P.hodgeTransport ρ.forward alpha ∉
      LinearMap.range P.cycleClass := by
  intro h
  exact hMissing
    ((algebraicity_iff_reversible_general_space_transport
      P ρ alpha).mpr h)


/-! ## WHOLE REALIZATION: IRREVERSIBLE BUT SPLIT CAUSAL FOLDS

A dimension/topology birth need NOT be a reversible General Space
recoordination. The geometric projective folds have genuine Hodge
and algebraic-cycle RETURNS (e.g. a distinguished section).
The next law works for an arbitrary forward causal path, rather than
assuming a reverse causal path exists. Its native-cycle commutative
square is indispensable: Hodge-charge preservation alone cannot
produce a canonical Chow representative.

This is the exact dimension-free algebraicity-defect transport
under compatible causal folding. It can be instantiated at every
emergent geometric dimension without identifying causal cell index
with the scheme's Krull dimension.
-/

/-- A genuinely possibly irreversible GST causal fold reflects
algebraicity of EVERY rational Hodge-fiber class once there is a
canonical native-cycle return compatible with a Hodge left inverse.
No Chow source for the input class is assumed. -/
theorem algebraicity_iff_split_causal_fold
    (P : CyclePathRealization G N H)
    {x y : G.Point} (γ : G.Path x y)
    (nativeReturn : N →ₗ[ℚ] N)
    (hodgeReturn : H →ₗ[ℚ] H)
    (hReturnCompatible : ∀ Z : N,
      P.cycleClass (nativeReturn Z) =
        hodgeReturn (P.cycleClass Z))
    (hHodgeRetract : ∀ alpha : H,
      hodgeReturn (P.hodgeTransport γ alpha) = alpha)
    (alpha : H) :
    alpha ∈ LinearMap.range P.cycleClass ↔
      P.hodgeTransport γ alpha ∈ LinearMap.range P.cycleClass := by
  constructor
  · exact transported_native_cycle_stays_algebraic P γ alpha
  · intro h
    obtain ⟨Z, hZ⟩ := h
    refine ⟨nativeReturn Z, ?_⟩
    calc
      P.cycleClass (nativeReturn Z) =
          hodgeReturn (P.cycleClass Z) :=
            hReturnCompatible Z
      _ = hodgeReturn (P.hodgeTransport γ alpha) := by rw [hZ]
      _ = alpha := hHodgeRetract alpha

/-- Every actual rational Hodge direction missing from the original
canonical algebraic image survives an irreversible dimensional fold
having a genuine Chow-compatible left return. In particular, shape
purity of the new world does not erase the missing original source. -/
theorem missing_native_direction_persists_split_causal_fold
    (P : CyclePathRealization G N H)
    {x y : G.Point} (γ : G.Path x y)
    (nativeReturn : N →ₗ[ℚ] N)
    (hodgeReturn : H →ₗ[ℚ] H)
    (hReturnCompatible : ∀ Z : N,
      P.cycleClass (nativeReturn Z) =
        hodgeReturn (P.cycleClass Z))
    (hHodgeRetract : ∀ alpha : H,
      hodgeReturn (P.hodgeTransport γ alpha) = alpha)
    (alpha : H)
    (hMissing : alpha ∉ LinearMap.range P.cycleClass) :
    P.hodgeTransport γ alpha ∉ LinearMap.range P.cycleClass := by
  intro hFolded
  exact hMissing ((algebraicity_iff_split_causal_fold
    P γ nativeReturn hodgeReturn hReturnCompatible hHodgeRetract alpha).mpr
      hFolded)

/-- Compatibility of this genuinely one-sided fold law with two
consecutive causal births. The complex dimension of the intermediate
world is not an input; its actual native/Hodge retractions are. -/
theorem algebraicity_iff_two_split_causal_folds
    (P : CyclePathRealization G N H)
    {x y z : G.Point}
    (γ : G.Path x y) (δ : G.Path y z)
    (nativeReturn₁ nativeReturn₂ : N →ₗ[ℚ] N)
    (hodgeReturn₁ hodgeReturn₂ : H →ₗ[ℚ] H)
    (hCompat₁ : ∀ Z : N,
      P.cycleClass (nativeReturn₁ Z) =
        hodgeReturn₁ (P.cycleClass Z))
    (hCompat₂ : ∀ Z : N,
      P.cycleClass (nativeReturn₂ Z) =
        hodgeReturn₂ (P.cycleClass Z))
    (hRetract₁ : ∀ alpha : H,
      hodgeReturn₁ (P.hodgeTransport γ alpha) = alpha)
    (hRetract₂ : ∀ beta : H,
      hodgeReturn₂ (P.hodgeTransport δ beta) = beta)
    (alpha : H) :
    alpha ∈ LinearMap.range P.cycleClass ↔
      P.hodgeTransport (G.compPath γ δ) alpha ∈
        LinearMap.range P.cycleClass := by
  calc
    alpha ∈ LinearMap.range P.cycleClass ↔
        P.hodgeTransport γ alpha ∈ LinearMap.range P.cycleClass :=
          algebraicity_iff_split_causal_fold
            P γ nativeReturn₁ hodgeReturn₁ hCompat₁ hRetract₁ alpha
    _ ↔ P.hodgeTransport δ (P.hodgeTransport γ alpha) ∈
          LinearMap.range P.cycleClass :=
          algebraicity_iff_split_causal_fold
            P δ nativeReturn₂ hodgeReturn₂ hCompat₂ hRetract₂
              (P.hodgeTransport γ alpha)
    _ ↔ P.hodgeTransport (G.compPath γ δ) alpha ∈
          LinearMap.range P.cycleClass := by
            rw [P.hodge_comp]


/-! ## DIMENSIONLESS GST: ARBITRARY FINITE-DEPTH CAUSAL FOLD TOWER

These laws use each actual GeneralSpace path, not a sequence of chosen
coordinate dimensions.  The source and target of each path are typed
by a world trajectory.  Native and Hodge returns must be compatible
with the same underlying cycle class map; the theorem neither assigns
a complex dimension to a causal cell nor manufactures an algebraic
representative from pure Hodge charge.
-/

/-- Entire Hodge state after n consecutive (possibly irreversible)
dimensionless GST causal paths. It has no intrinsic dimension bound. -/
def causalTowerHodgeState
    (P : CyclePathRealization G N H)
    (world : ℕ → G.Point)
    (step : ∀ n : ℕ, G.Path (world n) (world (n + 1))) :
    ℕ → H → H
  | 0, alpha => alpha
  | n + 1, alpha =>
      P.hodgeTransport (step n) (causalTowerHodgeState P world step n alpha)

/-- At every finite emergent causal depth, native algebraicity is
reflected EXACTLY if each geometrically certified causal step has
a genuine native/Betti left return. The source class is never chosen
from an assumed Hodge-to-Chow inverse. -/
theorem algebraicity_iff_any_finite_causal_tower
    (P : CyclePathRealization G N H)
    (world : ℕ → G.Point)
    (step : ∀ n : ℕ, G.Path (world n) (world (n + 1)))
    (nativeReturn : ∀ n : ℕ, N →ₗ[ℚ] N)
    (hodgeReturn : ∀ n : ℕ, H →ₗ[ℚ] H)
    (hReturnCompatible : ∀ (n : ℕ) (Z : N),
      P.cycleClass (nativeReturn n Z) =
        hodgeReturn n (P.cycleClass Z))
    (hHodgeRetract : ∀ (n : ℕ) (alpha : H),
      hodgeReturn n (P.hodgeTransport (step n) alpha) = alpha)
    (alpha : H) (n : ℕ) :
    alpha ∈ LinearMap.range P.cycleClass ↔
      causalTowerHodgeState P world step n alpha ∈
        LinearMap.range P.cycleClass := by
  induction n with
  | zero =>
      simp only [causalTowerHodgeState]
  | succ n ih =>
      change alpha ∈ LinearMap.range P.cycleClass ↔
        P.hodgeTransport (step n)
          (causalTowerHodgeState P world step n alpha) ∈
            LinearMap.range P.cycleClass
      exact ih.trans
        (algebraicity_iff_split_causal_fold P (step n)
          (nativeReturn n) (hodgeReturn n)
          (hReturnCompatible n) (hHodgeRetract n)
          (causalTowerHodgeState P world step n alpha))

/-- A rational Hodge direction missing from the native image
cannot disappear at ANY FINITE causal depth, without imposing
a geometric dimension cap or asserting that each arbitrary
GST higher cell is itself a smooth projective variety. -/
theorem missing_native_direction_persists_any_finite_causal_tower
    (P : CyclePathRealization G N H)
    (world : ℕ → G.Point)
    (step : ∀ n : ℕ, G.Path (world n) (world (n + 1)))
    (nativeReturn : ∀ n : ℕ, N →ₗ[ℚ] N)
    (hodgeReturn : ∀ n : ℕ, H →ₗ[ℚ] H)
    (hReturnCompatible : ∀ (n : ℕ) (Z : N),
      P.cycleClass (nativeReturn n Z) =
        hodgeReturn n (P.cycleClass Z))
    (hHodgeRetract : ∀ (n : ℕ) (alpha : H),
      hodgeReturn n (P.hodgeTransport (step n) alpha) = alpha)
    (alpha : H)
    (hMissing : alpha ∉ LinearMap.range P.cycleClass) :
    ∀ n : ℕ,
      causalTowerHodgeState P world step n alpha ∉
        LinearMap.range P.cycleClass := by
  intro n hFold
  exact hMissing
    ((algebraicity_iff_any_finite_causal_tower P world step
        nativeReturn hodgeReturn hReturnCompatible hHodgeRetract
        alpha n).mpr hFold)

#check causalTowerHodgeState
#check algebraicity_iff_any_finite_causal_tower
#check missing_native_direction_persists_any_finite_causal_tower
#print axioms algebraicity_iff_any_finite_causal_tower
#print axioms missing_native_direction_persists_any_finite_causal_tower

#check algebraicity_iff_split_causal_fold
#check missing_native_direction_persists_split_causal_fold
#check algebraicity_iff_two_split_causal_folds
#print axioms algebraicity_iff_split_causal_fold
#print axioms algebraicity_iff_two_split_causal_folds

#check CyclePathRealization
#check algebraicity_iff_reversible_general_space_transport
#check missing_native_direction_persists_recoordination
#print axioms algebraicity_iff_reversible_general_space_transport
#print axioms missing_native_direction_persists_recoordination

end NativeCycleRecoordination

end GSTGeneralSpace
