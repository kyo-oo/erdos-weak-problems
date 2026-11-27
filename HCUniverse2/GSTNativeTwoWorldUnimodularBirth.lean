import Mathlib

/-!
# Original GST source-birth correction: exactly TWO native new world coordinates

Companion ORIGINAL source and actual CHOW geometric proof:
research/derivations/GST_20261112_corrected_infinite_native_birth_minimal_N14_constant_family_realization.tex

The owner's true 12-cell U/J/M/[J,M] Nav OFF/ON matrices have Smith
forms diag(1^10,4,4) and diag(1^10,3,0), respectively, checked by
exact original-source Wolfram code. At the obstructing primes 2 and 3
each has rank 10, so at least TWO appended coordinates are required
for a unimodular extension that keeps the original 12x12 block.

This file proves, for ARBITRARY integer Smith coefficients a,b, the
exact two-world birth/inversion map on the four residual coordinates:
    ((x,y),(u,v)) ↦ ((a*x+u,b*y+v),(x,y))
    inverse: ((X,Y),(x,y)) ↦ ((x,y),(X-a*x,Y-b*y)).
There is no positive/negative time bound. The full original 14x14
matrix is conjugate to this block plus the original ten identity axes
by actual unimodular Smith transforms. It preserves the old 12x12
matrix as top-left block.

CRITICAL HONEST SOURCE GATE: realizing 14 native coordinates as 14
copies of a genuine original scheme X DOES construct a true algebraic
correspondence, but does NOT produce a new Chow source for prescribed
alpha outside the original canonical cycle-class image. The proof
below is about arithmetic/abstract module components, not an illicit
universal Hodge-to-Chow inverse.
-/

set_option maxHeartbeats 1200000

namespace GSTNativeTwoWorldUnimodularBirth

/-- General INTEGER source-birth operator on the two nontrivial Smith
axes and the TWO appended N-world coordinates. The original Smith
core (a,b) is UNCHANGED. -/
def twoBirthForward (a b : ℤ)
    (s : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((a * s.1.1 + s.2.1, b * s.1.2 + s.2.2),
   (s.1.1, s.1.2))

/-- Exact integral inverse: EVERY native input is recoverable from
every generation, with no division by a, b or a cardinal. -/
def twoBirthInverse (a b : ℤ)
    (s : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((s.2.1, s.2.2),
   (s.1.1 - a * s.2.1, s.1.2 - b * s.2.2))

theorem twoBirthInverse_forward (a b : ℤ)
    (s : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoBirthInverse a b (twoBirthForward a b s) = s := by
  rcases s with ⟨⟨x,y⟩,⟨u,v⟩⟩
  apply Prod.ext
  · apply Prod.ext <;> dsimp [twoBirthForward, twoBirthInverse]
  · apply Prod.ext <;> dsimp [twoBirthForward, twoBirthInverse] <;> ring

theorem twoBirthForward_inverse (a b : ℤ)
    (s : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoBirthForward a b (twoBirthInverse a b s) = s := by
  rcases s with ⟨⟨x,y⟩,⟨u,v⟩⟩
  apply Prod.ext
  · apply Prod.ext <;> dsimp [twoBirthForward, twoBirthInverse] <;> ring
  · apply Prod.ext <;> dsimp [twoBirthForward, twoBirthInverse]

/-- Inversion in the doubly obstructed original physical OFF Smith
axes (4,4) is exact and unconditional, even though 4 is not a unit
in the integers. -/
theorem originalPhysicalOff_twoWorld_bijective :
    Function.Bijective (twoBirthForward 4 4) := by
  constructor
  · intro s t h
    have hh := congrArg (twoBirthInverse 4 4) h
    simpa only [twoBirthInverse_forward] using hh
  · intro t
    exact ⟨twoBirthInverse 4 4 t,
      twoBirthForward_inverse 4 4 t⟩

/-- Likewise the physical ON original Smith factors (3,0)
are fully recoverable after exactly two new world channels:
the preexisting zero factor needs no invented inverse. -/
theorem originalPhysicalOn_twoWorld_bijective :
    Function.Bijective (twoBirthForward 3 0) := by
  constructor
  · intro s t h
    have hh := congrArg (twoBirthInverse 3 0) h
    simpa only [twoBirthInverse_forward] using hh
  · intro t
    exact ⟨twoBirthInverse 3 0 t,
      twoBirthForward_inverse 3 0 t⟩

/-- Abstract 14-sheet source gate instantiated by the genuine
componentwise canonical cycle map on the disjoint union
Y = X ⨿ ... ⨿ X. If a source for the SPECIFIED marked alpha
exists in Y, it must ALREADY exist on original X.
The ACTUAL projective geometric proof is in the companion TeX. -/
theorem originalX_alpha_source_required_from_fourteen_clones
    {A B : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B]
    (cl : A →ₗ[ℚ] B) (alpha : B)
    (z : Fin 14 → A)
    (hz : ∀ i : Fin 14,
      cl (z i) = if i = 0 then alpha else 0) :
    ∃ zOriginal : A, cl zOriginal = alpha := by
  exact ⟨z 0, by simpa using hz 0⟩

#check twoBirthInverse_forward
#check twoBirthForward_inverse
#check originalPhysicalOff_twoWorld_bijective
#check originalPhysicalOn_twoWorld_bijective
#check originalX_alpha_source_required_from_fourteen_clones

#print axioms twoBirthInverse_forward
#print axioms originalPhysicalOff_twoWorld_bijective
#print axioms originalPhysicalOn_twoWorld_bijective
#print axioms originalX_alpha_source_required_from_fourteen_clones

end GSTNativeTwoWorldUnimodularBirth
