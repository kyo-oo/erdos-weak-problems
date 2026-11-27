import HCUniverse2.GSTImageThreeCurvatureResonance
import HCUniverse2.waves.GSTNCohomologyV3
import Mathlib

/-!
# GST Image-3 original N-cohomology holewise curvature transport

Preserve the OWNER'S EXISTING independent N-cohomology shape
`GSTNCohomology.NShape` and ALL its actual `Fin s.holes` hole indices.
At every independently indexed original hole, retain the ORIGINAL
twelve-cell U/J/M/[J,M] CM source, with freely varying rational
direct strength a_i and curvature strength b_i.

This file proves exact full hole-index naturality of the two-cell
CM recurrence and constructive simultaneous source-coordinate
coverage away from the half-curvature resonance.

The individual reconstruction coefficients MAY VARY with the hole.
This is NOT falsely called a single shared Krylov orbit or a
canonical Chow/Hodge realization. A single common full 12h orbit
needs the separately proved/admitted spectral CRT step.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeIndependentNCohoSource

open GSTImageThreeCurvatureResonance
open GSTGraphV2CMWaveFusion

/-- One original twelve-cell source for EACH actual NShape hole. -/
abbrev OriginalWaveHoles (s : GSTNCohomology.NShape) :=
  Fin s.holes → WaveSignal

/-- The owner's genuine source operation, pointwise on all actual
independent N-cohomology holes. No index is collapsed. -/
def holewiseCurvatureFold
    (s : GSTNCohomology.NShape)
    (a b : Fin s.holes → ℚ)
    (u : OriginalWaveHoles s) : OriginalWaveHoles s :=
  fun i => curvatureFold (a i) (b i) (u i)

/-- The ORIGINAL mixed Wave-I seed in every NShape source channel. -/
def uniformOriginalSeed
    (s : GSTNCohomology.NShape) : OriginalWaveHoles s :=
  fun _ => seed

/-- Preserve the exact original null/max physical readouts for ALL holes. -/
def holewiseFixedPair
    (s : GSTNCohomology.NShape)
    (u : OriginalWaveHoles s) : Fin s.holes → ℚ × ℚ :=
  fun i => fixedPair (u i)

/-- The full N-hole family obeys the ORIGINAL CM two-cell evolution,
with no finite bound on the number of holes. -/
theorem holewiseFixedPair_curvatureFold
    (s : GSTNCohomology.NShape)
    (a b : Fin s.holes → ℚ)
    (u : OriginalWaveHoles s) :
    holewiseFixedPair s (holewiseCurvatureFold s a b u) =
      fun i =>
        (u i nullCell + (1+2*b i)*u i maximumCell,
         (1+2*a i)*u i maximumCell+(2*b i-1)*u i nullCell) := by
  funext i
  exact fixedPair_curvatureFold (a i) (b i) (u i)

/-- Every real original N-hole channel inherits the SAME universal
second-order null-cell recurrence, with its own actual strengths. -/
theorem holewise_second_order_null
    (s : GSTNCohomology.NShape)
    (a b : Fin s.holes → ℚ)
    (u : OriginalWaveHoles s) (i : Fin s.holes) :
    (holewiseCurvatureFold s a b
      (holewiseCurvatureFold s a b u)) i nullCell =
      (2+2*a i) * (holewiseCurvatureFold s a b u) i nullCell -
        (2+2*a i-4*b i*b i)*u i nullCell := by
  exact fixedPair_second_order_null (a i) (b i) (u i)

/-- The maximum-cell CM recurrence is equally valid holewise, at
any original finite N-cohomology shape. -/
theorem holewise_second_order_maximum
    (s : GSTNCohomology.NShape)
    (a b : Fin s.holes → ℚ)
    (u : OriginalWaveHoles s) (i : Fin s.holes) :
    (holewiseCurvatureFold s a b
      (holewiseCurvatureFold s a b u)) i maximumCell =
      (2+2*a i) * (holewiseCurvatureFold s a b u) i maximumCell -
        (2+2*a i-4*b i*b i)*u i maximumCell := by
  exact fixedPair_second_order_maximum (a i) (b i) (u i)

/-- An arbitrary prescribed pair of original null/max values
in EVERY finite N-cohomology hole is reconstructed from the
actual original mixed seed and FIRST original CM fold, whenever
each real curvature channel is away from resonance. Holewise
coefficients are preserved independently; NO Hodge target basis
or artificial all-X cycle-class inverse is postulated. -/
theorem holewise_two_step_reconstruct
    (s : GSTNCohomology.NShape)
    (a b : Fin s.holes → ℚ)
    (hgood : ∀ i : Fin s.holes, b i ≠ (1/2 : ℚ))
    (x y : Fin s.holes → ℚ) :
    ∃ left right : Fin s.holes → ℚ,
      (∀ i,
        left i * seed nullCell +
          right i * curvatureFold (a i) (b i) seed nullCell = x i) ∧
      (∀ i,
        left i * seed maximumCell +
          right i * curvatureFold (a i) (b i) seed maximumCell = y i) := by
  classical
  have hlocal : ∀ i : Fin s.holes, ∃ l r : ℚ,
      l * seed nullCell +
        r * curvatureFold (a i) (b i) seed nullCell = x i ∧
      l * seed maximumCell +
        r * curvatureFold (a i) (b i) seed maximumCell = y i := by
    intro i
    exact fixedPair_two_step_reconstruct
      (a i) (b i) (x i) (y i) (hgood i)
  choose l r hlr using hlocal
  exact ⟨l, r, fun i => (hlr i).1, fun i => (hlr i).2⟩

#check OriginalWaveHoles
#check holewiseCurvatureFold
#check holewiseFixedPair_curvatureFold
#check holewise_second_order_null
#check holewise_second_order_maximum
#check holewise_two_step_reconstruct
#print axioms holewise_two_step_reconstruct

end GSTImageThreeIndependentNCohoSource
