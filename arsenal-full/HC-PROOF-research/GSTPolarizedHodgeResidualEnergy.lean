import GSTUniversalHodgeResidualProjection
import GSTGraphV2SelfExpandingCosmology

/-!
# GST polarized primitive Hodge residual — exact Pythagorean identity

The Hodge–Riemann bilinear relations supply a rational polarization Q
with positive-definite signed primitive (p,p) intersection pairing
on an arbitrary smooth projective complex variety X.

For a finite genuine native algebraic primitive basis z_i with
a rational Gram-dual detector ell_i(x)=Q(x,cl(z_i)),
our universal native projection Z_alpha gives exact orthogonality:
  Q(r_alpha, cl(Z_alpha)) = 0.

Consequently:
  Q(alpha,alpha)=Q(cl(Z_alpha),cl(Z_alpha))+Q(r_alpha,r_alpha).

In the TRUE positive-definite primitive Hodge fiber, a hypothetical
missing Hodge class has strictly POSITIVE residual square, whereas
algebraic targets have zero residual once the full algebraic primitive
subspace has been used as source basis.

This is a sharp numerical invariant for the ORIGINAL GST
omniversal ghost question. It does not independently prove that
the residual vanishes, and does not smuggle in such a premise.
-/

set_option maxHeartbeats 3500000
noncomputable section

open GSTUniversalHodgeResidualProjection

namespace GSTPolarizedHodgeResidualEnergy

variable {ι N V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup V] [Module ℚ V]

/-- The class of the native projection is orthogonal to the true
Hodge residual, provided the probes are actual polarization
intersection readouts. This identity has NO target-preimage premise. -/
theorem residual_orthogonal_to_algebraic_projection
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (alpha : V) :
    (Q (residualClass P alpha))
      (P.cycleClass (projectedNativeCycle P alpha)) = 0 := by
  classical
  have hzero (i : ι) :
      (Q (residualClass P alpha))
        (P.cycleClass (P.cycles i)) = 0 := by
    rw [← hGeometricPairing i (residualClass P alpha)]
    exact residual_orthogonal_to_all_geometric_cycles P alpha i
  calc
    (Q (residualClass P alpha))
        (P.cycleClass (projectedNativeCycle P alpha)) =
      ∑ i, (P.detectors i alpha) *
          ((Q (residualClass P alpha))
            (P.cycleClass (P.cycles i))) := by
          simp [projectedNativeCycle, map_sum, map_smul]
    _ = 0 := by simp [hzero]

/-- Polarized primitive Hodge-PYTHAGORAS with a genuine native
algebraic projection on the ORIGINAL target carrier. -/
theorem primitive_polarization_pythagoras
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (alpha : V) :
    (Q alpha) alpha =
      (Q (P.cycleClass (projectedNativeCycle P alpha)))
        (P.cycleClass (projectedNativeCycle P alpha)) +
      (Q (residualClass P alpha)) (residualClass P alpha) := by
  let a := P.cycleClass (projectedNativeCycle P alpha)
  let r := residualClass P alpha
  have hsum : a + r = alpha :=
    actual_cycle_plus_residual_equals_target P alpha
  have hcross : (Q r) a = 0 :=
    residual_orthogonal_to_algebraic_projection
      P Q hGeometricPairing alpha
  have hcross' : (Q a) r = 0 := by
    rw [hSym a r]
    exact hcross
  change (Q alpha) alpha = (Q a) a + (Q r) r
  calc
    (Q alpha) alpha = (Q (a+r)) (a+r) := by rw [hsum]
    _ = (Q a) a + (Q a) r + (Q r) a + (Q r) r := by
      simp only [map_add, LinearMap.add_apply]
      ring
    _ = (Q a) a + (Q r) r := by rw [hcross, hcross']; ring

/-- If alpha is NOT algebraically representable, its canonical
residual has strictly POSITIVE polarization energy whenever
Q is genuinely positive definite on the primitive Hodge fiber.
This is a real obstruction certificate, not a universal
vanishing theorem. -/
theorem nonalgebraic_primitive_forces_positive_residual_energy
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V)
    (hmissing : alpha ∉ LinearMap.range P.cycleClass) :
    0 < (Q (residualClass P alpha)) (residualClass P alpha) := by
  exact hPositive _ (any_unrepresented_target_has_nonzero_residual
    P alpha hmissing)


/-! ## GST automatic independent geometric readout from POLARIZED residual energy

The old arbitrary-rank native coordinate theorem required an externally chosen
linear readout vanishing on all old classes and nonzero on a born class.
Here we construct that readout **from the actual polarized Hodge pairing**
and the canonical finite native residual.

For an independently constructed native fresh cycle, the residual r of its
real cycle class v after subtracting the known geometric dual basis defines
a native, canonically computed readout Q(r, -). Geometric polarization forces
this readout to vanish on all old cycle classes; a nonzero (positive) residual
energy Q(r,r) forces it to detect the fresh cycle class. Thus the GST birth
increases actual algebraic Hodge rank, with no free readout-choice premise.

The input fresh remains an ACTUAL native cycle, and the geometric pairing and
positivity must be independently verified on the original X. This theorem
does not manufacture an arbitrary requested primitive Chow representative.
-/

/-- GST builds the independent coordinate readout DIRECTLY from its
polarized residual. For every old genuine native generator, it is zero. -/
theorem native_residual_builds_geometric_readout
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N) (i : ι) :
    (Q (residualClass P (P.cycleClass fresh)))
      (P.cycleClass (P.cycles i)) = 0 := by
  rw [← hPair i (residualClass P (P.cycleClass fresh))]
  exact residual_orthogonal_to_all_geometric_cycles P
    (P.cycleClass fresh) i

/-- The same CANONICAL residual readout evaluates on the fresh native
cycle to exactly its polarized energy, no arbitrary readout parameter. -/
theorem native_residual_readout_fresh_eq_energy
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N) :
    (Q (residualClass P (P.cycleClass fresh)))
      (P.cycleClass fresh) =
    (Q (residualClass P (P.cycleClass fresh)))
      (residualClass P (P.cycleClass fresh)) := by
  let v := P.cycleClass fresh
  have hsum := actual_cycle_plus_residual_equals_target P v
  have hcross := residual_orthogonal_to_algebraic_projection P Q hPair v
  calc
    (Q (residualClass P v)) v =
        (Q (residualClass P v))
          (P.cycleClass (projectedNativeCycle P v) +
            residualClass P v) := by rw [hsum]
    _ = (Q (residualClass P v))
          (P.cycleClass (projectedNativeCycle P v)) +
        (Q (residualClass P v)) (residualClass P v) := by
          rw [map_add]
    _ = (Q (residualClass P v)) (residualClass P v) := by
      rw [hcross]
      ring

/-- A new GST geometric cycle with strictly positive measured residual
energy **automatically increases the ACTUAL native algebraic Hodge span**.
The complete readout is Q(r,-), constructed from old native cycles
and their canonical Hodge intersection values. No hFresh readout premise. -/
theorem positive_residual_energy_forces_strict_native_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N)
    (hEnergy :
      0 < (Q (residualClass P (P.cycleClass fresh)))
        (residualClass P (P.cycleClass fresh))) :
    Submodule.span ℚ (Set.range (fun i : ι => P.cycleClass (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert (P.cycleClass fresh)
          (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) := by
  let readout : V →ₗ[ℚ] ℚ :=
    Q (residualClass P (P.cycleClass fresh))
  have hOld : ∀ i : ι, readout (P.cycleClass (P.cycles i)) = 0 :=
    native_residual_builds_geometric_readout P Q hPair fresh
  have hFresh : readout (P.cycleClass fresh) ≠ 0 := by
    rw [native_residual_readout_fresh_eq_energy P Q hPair fresh]
    exact ne_of_gt hEnergy
  have hnot :
      P.cycleClass fresh ∉
        Submodule.span ℚ (Set.range (fun i : ι => P.cycleClass (P.cycles i))) := by
    intro hspan
    have hker :
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) ≤
        LinearMap.ker readout := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (hOld i)
    exact hFresh (LinearMap.mem_ker.mp (hker hspan))
  apply lt_of_le_of_ne
  · exact Submodule.span_mono (Set.subset_insert _ _)
  · intro heq
    have hnew :
      P.cycleClass fresh ∈
        Submodule.span ℚ
          (Set.insert (P.cycleClass fresh)
            (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    rw [← heq] at hnew
    exact hnot hnew


/-- **GST geometric Gram-surplus rank birth.** The independent source
coordinate is certified directly by comparing only two genuine
intersection measurements: the fresh cycle's self-intersection and
the self-intersection of its exact already-algebraic projection.
No externally supplied `thirdRead` or `hFresh` hypothesis occurs;
the strict surplus is a geometric quantity measurable on the original
projective variety from actual algebraic source cycles. -/
theorem native_geometric_gram_surplus_forces_strict_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N)
    (hGram :
      (Q (P.cycleClass fresh)) (P.cycleClass fresh) >
      (Q (P.cycleClass (projectedNativeCycle P (P.cycleClass fresh))))
        (P.cycleClass (projectedNativeCycle P (P.cycleClass fresh)))) :
    Submodule.span ℚ
        (Set.range (fun i : ι => P.cycleClass (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert (P.cycleClass fresh)
          (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) := by
  have hPythagoras :=
    primitive_polarization_pythagoras P Q hSym hPair
      (P.cycleClass fresh)
  have hEnergy :
      0 < (Q (residualClass P (P.cycleClass fresh)))
        (residualClass P (P.cycleClass fresh)) := by
    linarith
  exact positive_residual_energy_forces_strict_native_rank_birth
    P Q hPair fresh hEnergy

#check native_geometric_gram_surplus_forces_strict_rank_birth
#print axioms native_geometric_gram_surplus_forces_strict_rank_birth


/-! ## GST geometric world birth + native residual energy: INTEGRATED upgrade

Combine the user's ORIGINAL arbitrary-source self-expanding geometric birth,
the old independently constructed native cycles, and the polarized Hodge
intersection coordinate. The proof constructs the born native cycle using the
actual world birth, not a function from arbitrary Hodge classes to cycles;
then measures strict algebraic-rank growth by the COMPLETELY COMPUTED
two-term intersection Gram surplus, with no externally chosen third readout.

This is an effective bridge BETWEEN GST ontological birth and GST
polarized energy, over arbitrary original target-world cycle carrier.
The remaining geometric input is an independently constructed
birth on that world whose real Gram surplus is positive.
-/

universe uWorld uState uLaw uSort

/-- A genuine dependent GST geometric world-birth supplies a new
native geometric coordinate as soon as its intersection Gram
surplus is verified positive. The output class is the CANONICAL
cycle class of the BORN native object, not a free Hodge inverse. -/
theorem gst_world_birth_gram_surplus_constructs_fresh_native_class
    (C : GSTGraphV2SelfExpandingCosmology.SelfExpandingCosmos.{uWorld,uState,uLaw,uSort})
    (R : GSTGraphV2SelfExpandingCosmology.NativeGeometryBirth.GeometricCycleBirthRealization C)
    {I : Type uWorld} {src : I → C.World} {target : C.World}
    (e : C.Birth src target)
    [AddCommGroup (C.State target)] [Module ℚ (C.State target)]
    [AddCommGroup (C.Law target)] [Module ℚ (C.Law target)]
    (P : GeometricDualCyclePacket ι (C.State target) (C.Law target))
    (hCanonical :
      ∀ Z : C.State target,
        P.cycleClass Z = R.cycleClass target Z)
    (Q : C.Law target →ₗ[ℚ] C.Law target →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : C.Law target, (Q x) y = (Q y) x)
    (hPair : ∀ (i : ι) (x : C.Law target),
      P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (sources : (i : I) → C.State (src i))
    (hGram :
      (Q (P.cycleClass (R.assembleNative e sources)))
        (P.cycleClass (R.assembleNative e sources)) >
      (Q (P.cycleClass (projectedNativeCycle P
        (P.cycleClass (R.assembleNative e sources)))))
        (P.cycleClass (projectedNativeCycle P
          (P.cycleClass (R.assembleNative e sources))))) :
    Submodule.span ℚ (Set.range
        (fun i : ι => R.cycleClass target (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert
          (R.cycleClass target (R.assembleNative e sources))
          (Set.range (fun i : ι =>
            R.cycleClass target (P.cycles i)))) := by
  have hBorn :
      P.cycleClass (R.assembleNative e sources) =
        R.assembleHodge e (fun i => R.cycleClass (src i) (sources i)) :=
    (hCanonical _).trans (R.compatible e sources)
  have hRank :=
    native_geometric_gram_surplus_forces_strict_rank_birth
      P Q hSym hPair (R.assembleNative e sources) hGram
  simpa only [hCanonical] using hRank

#check gst_world_birth_gram_surplus_constructs_fresh_native_class
#print axioms gst_world_birth_gram_surplus_constructs_fresh_native_class


/-! ## GST FULL GRAM-DUAL POLARIZED BIRTH — no orthonormality shortcut

The old hPair hypothesis assumed that the normalized independent
native cycles were orthonormal for Q. On a cubic fourfold, the ACTUAL
hyperplane-square native class has intersection self-pairing THREE,
so that restriction would falsely reject honest native geometry.

A correct rational native detector is a GRAM-DUAL coordinate.
If old_i denote actual independent native cycle classes, the
only required Gram law is:
  Q(x,old_j) = Σ_i detector_i(x) Q(old_i,old_j).
It is derived, for a nondegenerate rational intersection Gram,
by multiplying the geometric intersection row by its inverse.
No square-root rational orthonormalization is required.

The following GST theorem constructs the missing-coordinate detector
Q(r,-) from that law and proves strict native rank gain using only
a POSITIVE geometric intersection Gram surplus. This handles
arbitrary positive rational Gram forms on original X.
-/

/-- GST rational Gram-dual geometry makes its TRUE native Hodge
residual orthogonal to EVERY old native cycle without requiring
that the native cycle intersection Gram is the identity matrix. -/
theorem gram_dual_residual_orthogonal_to_old_native
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGramDual : ∀ (j : ι) (x : V),
      (Q x) (P.cycleClass (P.cycles j)) =
        ∑ i, (P.detectors i x) *
          (Q (P.cycleClass (P.cycles i)))
            (P.cycleClass (P.cycles j)))
    (alpha : V) (j : ι) :
    (Q (residualClass P alpha))
      (P.cycleClass (P.cycles j)) = 0 := by
  rw [hGramDual j (residualClass P alpha)]
  simp [residual_orthogonal_to_all_geometric_cycles P alpha]

/-- UNRESTRICTED RATIONAL GRAM GST NATIVE BIRTH.
The geometric Gram surplus is the primitive residual energy
and it is STRICTLY POSITIVE exactly when the new native direction
has positive residual energy. This suffices to construct the
actual native Hodge rank extension without any selected readout,
orthonormal basis, abstract Hodge inverse, or target preimage. -/
theorem arbitrary_rational_gram_surplus_constructs_native_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (hGramDual : ∀ (j : ι) (x : V),
      (Q x) (P.cycleClass (P.cycles j)) =
        ∑ i, (P.detectors i x) *
          (Q (P.cycleClass (P.cycles i)))
            (P.cycleClass (P.cycles j)))
    (fresh : N)
    (hGram :
      (Q (P.cycleClass fresh)) (P.cycleClass fresh) >
      (Q (P.cycleClass (projectedNativeCycle P (P.cycleClass fresh))))
        (P.cycleClass (projectedNativeCycle P (P.cycleClass fresh)))) :
    Submodule.span ℚ
        (Set.range (fun i : ι => P.cycleClass (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert (P.cycleClass fresh)
          (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) := by
  let v : V := P.cycleClass fresh
  let a : V := P.cycleClass (projectedNativeCycle P v)
  let r : V := residualClass P v
  have hOld (i : ι) : (Q r) (P.cycleClass (P.cycles i)) = 0 :=
    gram_dual_residual_orthogonal_to_old_native P Q hGramDual v i
  have hcross : (Q r) a = 0 := by
    calc
      (Q r) a = ∑ i, (P.detectors i v) *
          ((Q r) (P.cycleClass (P.cycles i))) := by
            simp [a, projectedNativeCycle, map_sum, map_smul]
      _ = 0 := by simp [hOld]
  have hcross' : (Q a) r = 0 := by
    rw [hSym a r]
    exact hcross
  have hsum : a + r = v :=
    actual_cycle_plus_residual_equals_target P v
  have hpyth :
      (Q v) v = (Q a) a + (Q r) r := by
    calc
      (Q v) v = (Q (a+r)) (a+r) := by rw [hsum]
      _ = (Q a) a + (Q a) r + (Q r) a + (Q r) r := by
        simp only [map_add, LinearMap.add_apply]
        ring
      _ = (Q a) a + (Q r) r := by rw [hcross,hcross']; ring
  have hEnergy : 0 < (Q r) r := by
    have hge : (Q v) v > (Q a) a := hGram
    linarith
  have hRead : (Q r) v = (Q r) r := by
    calc
      (Q r) v = (Q r) (a+r) := by rw [hsum]
      _ = (Q r) a + (Q r) r := by rw [map_add]
      _ = (Q r) r := by rw [hcross]; ring
  have hFresh : (Q r) (P.cycleClass fresh) ≠ 0 := by
    change (Q r) v ≠ 0
    rw [hRead]
    exact ne_of_gt hEnergy
  have hnot :
      P.cycleClass fresh ∉
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) := by
    intro hspan
    have hker :
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) ≤
        LinearMap.ker (Q r) := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (hOld i)
    exact hFresh (LinearMap.mem_ker.mp (hker hspan))
  apply lt_of_le_of_ne
  · exact Submodule.span_mono (Set.subset_insert _ _)
  · intro heq
    have hnew :
      P.cycleClass fresh ∈
        Submodule.span ℚ
          (Set.insert (P.cycleClass fresh)
            (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    rw [← heq] at hnew
    exact hnot hnew


/-! ## GST TARGET-DRIVEN NATIVE BIRTH: residual coupling and energy descent

A serious change from a "fresh class measured after birth" criterion:
use the SPECIFIC unresolved target alpha to choose the next native birth.
The canonical rational Hodge residual r_alpha and true intersection
polarization Q construct a readout Q(r_alpha,-) vanishing on ALL old
native cycles under the full rational Gram-dual law.

Therefore ANY independently constructed native geometric cycle Z
with Q(r_alpha,cl(Z)) ≠ 0 *necessarily* adds a new algebraic Hodge
direction. No basis sheet, coordinate choice, or target preimage
appears among the new inputs. This is a GST target-directed BIRTH
criterion, rather than a generic independent rank certificate.

The optimal rational coefficient t=Q(r,z)/Q(z,z) removes EXACTLY
Q(r,z)^2 / Q(z,z) units of polarized residual energy when Q(z,z)>0.
In the true primitive Hodge fiber, Hodge-Riemann gives such positivity.
These are exact laws; existence of a coupled new native Z for every
remaining target is still the unproved universal geometric step.
-/

/-- Every target-residual intersection coupling with a genuine new
native cycle certifies strict algebraic source birth; the detector
is CONSTRUCTED from the input target and old native Gram matrix. -/
theorem target_residual_coupling_constructs_native_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGramDual : ∀ (j : ι) (x : V),
      (Q x) (P.cycleClass (P.cycles j)) =
        ∑ i, (P.detectors i x) *
          (Q (P.cycleClass (P.cycles i)))
            (P.cycleClass (P.cycles j)))
    (alpha : V) (fresh : N)
    (hCouple :
      (Q (residualClass P alpha)) (P.cycleClass fresh) ≠ 0) :
    Submodule.span ℚ
        (Set.range (fun i : ι => P.cycleClass (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert (P.cycleClass fresh)
          (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) := by
  let r := residualClass P alpha
  let ell : V →ₗ[ℚ] ℚ := Q r
  have hOld (i : ι) : ell (P.cycleClass (P.cycles i)) = 0 :=
    gram_dual_residual_orthogonal_to_old_native P Q hGramDual alpha i
  have hnot :
      P.cycleClass fresh ∉
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) := by
    intro hspan
    have hker :
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) ≤
        LinearMap.ker ell := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (hOld i)
    exact hCouple (LinearMap.mem_ker.mp (hker hspan))
  apply lt_of_le_of_ne
  · exact Submodule.span_mono (Set.subset_insert _ _)
  · intro heq
    have hnew :
        P.cycleClass fresh ∈
          Submodule.span ℚ
            (Set.insert (P.cycleClass fresh)
              (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    rw [← heq] at hnew
    exact hnot hnew

/-- The EXACT rational energy improvement from applying a native
geometric direction with its optimal polarized intersection coefficient.
It uses the genuine bilinear polarized geometry, NOT a freely assigned
"mass gradient" or a presumed algebraic target witness. -/
theorem optimal_target_residual_step_energy_identity
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (r z : V)
    (hz : (Q z) z ≠ 0) :
    (Q (r - (((Q r) z / (Q z) z) • z)))
        (r - (((Q r) z / (Q z) z) • z)) =
      (Q r) r - ((Q r) z)^2 / (Q z) z := by
  have hzr : (Q z) r = (Q r) z := hSym z r
  simp only [map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
  change (Q r) r -
      ((Q r) z / (Q z) z) * ((Q z) r) -
      ((Q r) z / (Q z) z) *
        ((Q r) z - ((Q r) z / (Q z) z) * ((Q z) z)) =
    (Q r) r - ((Q r) z)^2 / (Q z) z
  rw [hzr]
  field_simp [hz]
  ring

/-- Nonzero native target coupling yields a STRICT reduction in
polarized residual energy. Its coefficient is a rational number
computed from the true intersection matrix. -/
theorem optimal_target_residual_step_energy_strict
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (r z : V)
    (hz : 0 < (Q z) z)
    (hc : (Q r) z ≠ 0) :
    (Q (r - (((Q r) z / (Q z) z) • z)))
        (r - (((Q r) z / (Q z) z) • z)) <
      (Q r) r := by
  rw [optimal_target_residual_step_energy_identity Q hSym r z (ne_of_gt hz)]
  have hnum : 0 < ((Q r) z)^2 := sq_pos_of_ne_zero hc
  have hdiv : 0 < ((Q r) z)^2 / (Q z) z := div_pos hnum hz
  linarith



/-! ## GST TRUE ORTHOGONAL NATIVE BIRTH: preserve the old native source

The previous energy step subtracted a rational multiple of the whole fresh
Hodge class z from the target residual r. This generally reintroduces
components along the old native span, violating the defining orthogonality
of r and wasting energy. Its formula was algebraically correct but NOT
the optimal source-extension projection.

The GST upgrade corrects this at the NATIVE CHOW level: first remove
the old projected native component from the independent fresh cycle.
The resulting genuine rational algebraic cycle z_perp has class equal
to the old Gram-orthogonal RESIDUAL of z. Use z_perp, not z, to correct
the prescribed target residual. This preserves ALL old detectors and
has optimal polarized energy for the expanded native source.

The effective formula outputs an actual native cycle and does not
assume target alpha is algebraic. If residual(alpha) is in the
one-dimensional rational span of residual(z), the output represents
alpha EXACTLY in one step. Producing the fresh Z for each target is
still the universal geometric birth problem.
-/

/-- Actual native cycle carrying the newly born primitive Hodge
direction, corrected by SUBTRACTING the old algebraic projection. -/
def orthogonalizedNativeBirth
    (P : GeometricDualCyclePacket ι N V) (fresh : N) : N :=
  fresh - projectedNativeCycle P (P.cycleClass fresh)

/-- The new native class is EXACTLY the old GST Hodge residual
of the independently constructed fresh native cycle. -/
theorem orthogonalizedNativeBirth_class
    (P : GeometricDualCyclePacket ι N V) (fresh : N) :
    P.cycleClass (orthogonalizedNativeBirth P fresh) =
      residualClass P (P.cycleClass fresh) := by
  simp [orthogonalizedNativeBirth, residualClass]

/-- A specific target-born rational NATIVE cycle that uses the old
native projection and one genuinely new orthogonalized source. -/
def correctedTargetNativeBirth
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V) (fresh : N) (t : ℚ) : N :=
  projectedNativeCycle P alpha + t • orthogonalizedNativeBirth P fresh

/-- The complete unrepresented target is reduced by the exact native
newcomer residual, with NO reintroduced old native Hodge components. -/
theorem correctedTargetNativeBirth_residual
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V) (fresh : N) (t : ℚ) :
    alpha - P.cycleClass (correctedTargetNativeBirth P alpha fresh t) =
      residualClass P alpha -
        t • residualClass P (P.cycleClass fresh) := by
  simp only [correctedTargetNativeBirth, map_add, map_smul,
    orthogonalizedNativeBirth_class, residualClass]
  abel

/-- A genuinely new native source on the original X whose projected
primitive direction spans the requested target residual constructs an
EXACT native cycle in one step. Unlike the prior scalar-only step,
the correction is applied to an actual algebraic source whose old
native component has been subtracted explicitly. -/
theorem correctedTargetNativeBirth_exact_of_residual_parallel
    (P : GeometricDualCyclePacket ι N V)
    (alpha : V) (fresh : N) (t : ℚ)
    (hParallel :
      residualClass P alpha =
        t • residualClass P (P.cycleClass fresh)) :
    P.cycleClass (correctedTargetNativeBirth P alpha fresh t) = alpha := by
  have h :=
    correctedTargetNativeBirth_residual P alpha fresh t
  rw [hParallel, sub_self] at h
  exact sub_eq_zero.mp h |>.symm

/-- A POSITIVE true primitive intersection form and nonzero coupling
give strict energy reduction for the ACTUAL corrected native source.
This is the optimal orthogonal residual, not the earlier correction
against an unprojected cycle. -/
theorem correctedTargetNativeBirth_strict_energy_descent
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (alpha : V) (fresh : N)
    (hs :
      0 < (Q (residualClass P (P.cycleClass fresh)))
        (residualClass P (P.cycleClass fresh)))
    (hc :
      (Q (residualClass P alpha))
        (residualClass P (P.cycleClass fresh)) ≠ 0) :
    let t :=
      (Q (residualClass P alpha))
        (residualClass P (P.cycleClass fresh)) /
      (Q (residualClass P (P.cycleClass fresh)))
        (residualClass P (P.cycleClass fresh))
    (Q (alpha - P.cycleClass
      (correctedTargetNativeBirth P alpha fresh t)))
      (alpha - P.cycleClass
        (correctedTargetNativeBirth P alpha fresh t)) <
      (Q (residualClass P alpha)) (residualClass P alpha) := by
  dsimp
  rw [correctedTargetNativeBirth_residual]
  exact optimal_target_residual_step_energy_strict Q hSym
    (residualClass P alpha)
    (residualClass P (P.cycleClass fresh)) hs hc


/-- GST SINGLE-BIRTH UNIVERSALITY IN A ONE-DIRECTION RESIDUAL SECTOR.
One independently constructed native algebraic source saturates EVERY
rational Hodge target whenever the common geometric-detector kernel
is the Q-line generated by the new source's primitive residual.

The line-span test concerns the actual rational Hodge SPACE and
can be checked by its dimension and intersection matrix. It does
NOT supply individual Hodge class cycle witnesses. Unlike a
target-by-target choice, one geometrically constructed native source
is reused for ALL targets in this sector. -/
theorem one_native_birth_saturates_rank_one_residual_sector
    (P : GeometricDualCyclePacket ι N V)
    (fresh : N)
    (hResidualLine : ∀ v : V,
      (∀ i : ι, P.detectors i v = 0) →
        ∃ t : ℚ, v =
          t • residualClass P (P.cycleClass fresh)) :
    ∀ alpha : V, ∃ Z : N, P.cycleClass Z = alpha := by
  intro alpha
  obtain ⟨t, ht⟩ := hResidualLine (residualClass P alpha)
    (fun i => residual_orthogonal_to_all_geometric_cycles P alpha i)
  exact ⟨correctedTargetNativeBirth P alpha fresh t,
    correctedTargetNativeBirth_exact_of_residual_parallel
      P alpha fresh t ht⟩

#check one_native_birth_saturates_rank_one_residual_sector
#print axioms one_native_birth_saturates_rank_one_residual_sector

#check orthogonalizedNativeBirth_class
#check correctedTargetNativeBirth_residual
#check correctedTargetNativeBirth_exact_of_residual_parallel
#check correctedTargetNativeBirth_strict_energy_descent
#print axioms correctedTargetNativeBirth_exact_of_residual_parallel

/-! ## GST rational integral polarization QUANTUM-GAP exactness law

A signed integral primitive Hodge intersection has positive INTEGER
value when nonzero. For rational primitives, a fixed integer D clears
the cohomological denominator: D² Q(r,r) lies in ℤ. Thus positive
residual energy cannot vary continuously through zero while D stays
fixed. Any constructed native cycle with D² Q(r,r)<1 must be EXACT.

This law is stronger than infinite energy descent: ONE sufficiently
accurate geometric native construction proves exact representability.
Geometric authentication of its rational lattice bound hIntegral and
its small-energy bound hSmall remains an independent source task.
Do NOT promote those two inputs into unexplained universal axioms.
-/

/-- Exact GST arithmetic polarization gap: a nonnegative rational
energy whose fixed-denominator normalization is an INTEGER is either
zero or has normalized energy at least one. -/
theorem integer_polarization_gap_vanishes_below_one
    (energy : ℚ) (D : ℕ) (hD : 0 < D) (m : ℤ)
    (hIntegral : (D : ℚ)^2 * energy = (m : ℚ))
    (hNonneg : 0 ≤ energy)
    (hSmall : (D : ℚ)^2 * energy < 1) :
    energy = 0 := by
  have hpositive : 0 < (D : ℚ)^2 := by
    have hDn : (0 : ℚ) < D := by exact_mod_cast hD
    positivity
  have hm_nonneg : (0 : ℚ) ≤ (m : ℚ) := by
    rw [← hIntegral]
    positivity
  have hm_lt : (m : ℚ) < 1 := by
    simpa only [hIntegral] using hSmall
  have hm_nonneg_int : 0 ≤ m := by exact_mod_cast hm_nonneg
  have hm_lt_int : m < 1 := by exact_mod_cast hm_lt
  have hmzero : m = 0 := by omega
  have hscaled : (D : ℚ)^2 * energy = 0 := by
    simpa [hmzero] using hIntegral
  exact (mul_eq_zero.mp hscaled).resolve_left (ne_of_gt hpositive)

/-- If the actually constructed rational native projection has
polarized residual energy below its independently verified fixed
integral-lattice gap, the projection is an EXACT Hodge representative.
No limits, closure arguments, target Chow witness, or infinite
continuation are assumed: one finite arithmetic gap check suffices. -/
theorem quantized_energy_certificate_constructs_exact_native_cycle
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V) (D : ℕ) (hD : 0 < D) (m : ℤ)
    (hIntegral :
      (D : ℚ)^2 * (Q (residualClass P alpha))
        (residualClass P alpha) = (m : ℚ))
    (hSmall :
      (D : ℚ)^2 * (Q (residualClass P alpha))
        (residualClass P alpha) < 1) :
    P.cycleClass (projectedNativeCycle P alpha) = alpha := by
  let r := residualClass P alpha
  have hNonneg : 0 ≤ (Q r) r := by
    by_cases hr : r = 0
    · simp [hr]
    · exact le_of_lt (hPositive r hr)
  have hEnergyZero : (Q r) r = 0 :=
    integer_polarization_gap_vanishes_below_one
      ((Q r) r) D hD m hIntegral hNonneg hSmall
  have hR : r = 0 := by
    by_contra hr
    exact (ne_of_gt (hPositive r hr)) hEnergyZero
  have hh := actual_cycle_plus_residual_equals_target P alpha
  change P.cycleClass (projectedNativeCycle P alpha) + r = alpha at hh
  rw [hR, add_zero] at hh
  exact hh


/-! ## GST exact SCHUR-COMPLEMENT GRAM DETERMINANT GAP

This is the sharpened, GEOMETRY-DERIVED normalization. For integral
old primitive native cycles z_i, let G=(Q(z_i,z_j)) be their full
integral nondegenerate Gram matrix, with determinant g>0. For an
integral primitive Hodge target alpha, let the augmented matrix be
  [ G   b ]
  [ b'  c ],
where b_i=Q(alpha,z_i) and c=Q(alpha,alpha).
The exact Schur identity from block triangular elimination gives
 det(G_aug)=det(G)*(c-b' G^{-1} b)
           =det(G)*Q(residual, residual).
Both determinants are INTEGERS and g>0. Hence any nonzero residual
has energy >=1/g. No free denominator D is needed: geometry gives it.

The Lean theorem below kernel-checks the exact lattice step once
these determinant values are computed from the actual Gram geometry.
The general block-determinant identity itself is proved in the
mathematical route record and has NOT been installed as a new axiom.
Its carrier-specific native Betti/cup naturality remains required.
-/

/-- Exact integer Gram-determinant quantum law:
for positive integral old Gram determinant g and nonnegative
integer augmented determinant m, a residual with
g*energy=m and energy<1/g is necessarily EXACTLY zero. -/
theorem gram_determinant_gap_exactness
    (energy : ℚ) (g : ℕ) (hg : 0 < g) (m : ℕ)
    (hSchur : (g : ℚ) * energy = (m : ℚ))
    (hSmall : energy < 1 / (g : ℚ)) :
    energy = 0 := by
  have hgQ : (0 : ℚ) < g := by exact_mod_cast hg
  have hprod : (g : ℚ) * energy < 1 := by
    have hh := mul_lt_mul_of_pos_left hSmall hgQ
    have hdiv : (g : ℚ) * (1 / (g : ℚ)) = 1 := by
      field_simp
    simpa only [hdiv] using hh
  have hm_ltQ : (m : ℚ) < 1 := by
    rw [hSchur] at hprod
    exact hprod
  have hm_lt : m < 1 := by exact_mod_cast hm_ltQ
  have hmzero : m = 0 := by omega
  have hscale : (g : ℚ) * energy = 0 := by
    simpa [hmzero] using hSchur
  exact (mul_eq_zero.mp hscale).resolve_left (ne_of_gt hgQ)

/-- An integer-valued actual Gram determinant produces an EXACT native
cycle on the original Hodge carrier as soon as one finite geometry
construction gives energy below the CANONICAL determinant gap. -/
theorem geometric_gram_determinant_gap_constructs_exact_native
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V) (g : ℕ) (hg : 0 < g) (m : ℕ)
    (hSchur :
      (g : ℚ) * (Q (residualClass P alpha))
        (residualClass P alpha) = (m : ℚ))
    (hSmall :
      (Q (residualClass P alpha))
        (residualClass P alpha) < 1 / (g : ℚ)) :
    P.cycleClass (projectedNativeCycle P alpha) = alpha := by
  let r := residualClass P alpha
  have hz : (Q r) r = 0 :=
    gram_determinant_gap_exactness ((Q r) r) g hg m hSchur hSmall
  have hr : r = 0 := by
    by_contra h
    exact (ne_of_gt (hPositive r h)) hz
  have h := actual_cycle_plus_residual_equals_target P alpha
  change P.cycleClass (projectedNativeCycle P alpha) + r = alpha at h
  rw [hr, add_zero] at h
  exact h


/-! ## GST NONLINEAR ANTI-DECK SOURCE: EXACT OPTIMAL SIGN PERIODS

The accompanying genuine scheme-level LaTeX construction
(GST_nonlinear_antideck_chow_source_birth_2026-10-22.tex) constructs
signed anticharacter-pair pushforwards from actual branched double
covers of an arbitrary original X.  Here we kernel-check its exact
finite rational sign/amplification law INSIDE the existing polarized
GST module.  The geometric realization of each component source and
the genuine canonical Betti comparison remain mathematical inputs;
this theorem does not fabricate algebraic sources for a target.
-/

/-- Every finite rational component period can be oriented with a
genuine deck-sign coefficient so that its contribution is positive.
The factor two is the ACTUAL degree-two signed-cover return. -/
private theorem signed_antideck_atom (a : ℚ) :
    (if 0 ≤ a then (2 : ℚ) else -2) * a = 2 * |a| := by
  by_cases h : 0 ≤ a
  · simp [h, abs_of_nonneg h] <;> ring
  · have hn : a < 0 := lt_of_not_ge h
    simp [h, abs_of_neg hn] <;> ring

/-- A target-sensitive finite signed source combination; the
geometric branch theorem realizes precisely these signed degree-two coefficients
when the indices enumerate components of a reduced 2-divisor
intersection and the sign-compatible cover has been constructed. -/
noncomputable def signedAntideckPeriodSource
    (z : ι → V) (period : ι → ℚ) : V :=
  ∑ i : ι, (if 0 ≤ period i then (2 : ℚ) else -2) • z i

/-- The signed double-world source couples with the true measured
residual by the EXACT rational absolute-period sum, not an assumed
Gram determinant, invented nonzero detector or Hodge-to-Chow map. -/
theorem signedAntideckPeriodSource_pairing
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (r : V) (z : ι → V) (period : ι → ℚ)
    (hperiod : ∀ i, period i = (Q r) (z i)) :
    (Q r) (signedAntideckPeriodSource z period) =
      2 * ∑ i : ι, |period i| := by
  classical
  calc
    (Q r) (signedAntideckPeriodSource z period) =
        ∑ i : ι, (if 0 ≤ period i then (2 : ℚ) else -2) *
          (Q r) (z i) := by
            simp only [signedAntideckPeriodSource, map_sum, map_smul, smul_eq_mul]
    _ = ∑ i : ι, (if 0 ≤ period i then (2 : ℚ) else -2) *
          period i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hperiod i]
    _ = ∑ i : ι, 2 * |period i| := by
            apply Finset.sum_congr rfl
            intro i hi
            exact signed_antideck_atom (period i)
    _ = 2 * ∑ i : ι, |period i| := by
            rw [Finset.mul_sum]

#check signedAntideckPeriodSource
#check signedAntideckPeriodSource_pairing
#print axioms signedAntideckPeriodSource_pairing

#check gram_determinant_gap_exactness
#check geometric_gram_determinant_gap_constructs_exact_native
#print axioms geometric_gram_determinant_gap_constructs_exact_native

#check integer_polarization_gap_vanishes_below_one
#check quantized_energy_certificate_constructs_exact_native_cycle
#print axioms quantized_energy_certificate_constructs_exact_native_cycle

#check target_residual_coupling_constructs_native_rank_birth
#check optimal_target_residual_step_energy_identity
#check optimal_target_residual_step_energy_strict
#print axioms target_residual_coupling_constructs_native_rank_birth
#print axioms optimal_target_residual_step_energy_identity

#check gram_dual_residual_orthogonal_to_old_native
#check arbitrary_rational_gram_surplus_constructs_native_rank_birth
#print axioms arbitrary_rational_gram_surplus_constructs_native_rank_birth

#check native_residual_builds_geometric_readout
#check native_residual_readout_fresh_eq_energy
#check positive_residual_energy_forces_strict_native_rank_birth
#print axioms positive_residual_energy_forces_strict_native_rank_birth

#check residual_orthogonal_to_algebraic_projection
#check primitive_polarization_pythagoras
#check nonalgebraic_primitive_forces_positive_residual_energy
#print axioms primitive_polarization_pythagoras
#print axioms nonalgebraic_primitive_forces_positive_residual_energy

end GSTPolarizedHodgeResidualEnergy
