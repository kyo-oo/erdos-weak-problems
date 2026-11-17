import Mathlib
import GSTGradedWorldAlgebra

/-!
# GST DIMENSION-FREE POINCARE DUALITY

The original Lefschetz crown proves one anti-diagonal perfect pairing on the
fixed 4 x 3 chart.

Every positive rectangular A x B GST world has a canonical complementary
cell involution

  (C,d) |-> (A-1-C, B-1-d).

It reverses total degree around top degree A+B-2, gives an equivalence
between every degree-k sector and its complementary degree, and induces an
integrally perfect anti-diagonal pairing on the full coefficient lattice.

Thus the old 1,2,3,3,2,1 palindromic profile and twelve-cell Poincare
pairing are finite shadows of one dimension-free duality law.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldPoincareDuality

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open scoped BigOperators

/-- Complement one finite coordinate inside its ambient interval. -/
def complementFin {n : Nat} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.1, by omega⟩

@[simp]
theorem complementFin_involutive
    {n : Nat} (i : Fin n) :
    complementFin (complementFin i) = i := by
  apply Fin.ext
  unfold complementFin
  simp only
  omega

/-- Complementary cell in an arbitrary rectangular world. -/
def worldDual {A B : Nat} (c : WorldCell A B) : WorldCell A B :=
  (complementFin c.1, complementFin c.2)

@[simp]
theorem worldDual_involutive
    {A B : Nat} (c : WorldCell A B) :
    worldDual (worldDual c) = c := by
  rcases c with ⟨C,d⟩
  simp [worldDual]

theorem worldDual_injective
    {A B : Nat} :
    Function.Injective (@worldDual A B) := by
  intro x y h
  have h' := congrArg worldDual h
  simpa using h'

/-- Complementation reverses degree exactly around the top degree. -/
theorem worldDegree_dual_sum
    {A B : Nat} (c : WorldCell A B) :
    worldDegree (worldDual c) + worldDegree c = A+B-2 := by
  rcases c with ⟨⟨C,hC⟩,⟨d,hd⟩⟩
  unfold worldDegree worldDual complementFin
  simp only
  omega

theorem worldDegree_le_top
    {A B : Nat} (c : WorldCell A B) :
    worldDegree c ≤ A+B-2 := by
  have h := worldDegree_dual_sum c
  omega

/-- Exact complementary-degree formula. -/
theorem worldDegree_dual
    {A B : Nat} (c : WorldCell A B) :
    worldDegree (worldDual c) = A+B-2 - worldDegree c := by
  have h := worldDegree_dual_sum c
  omega

/-- Cells of one exact total degree. -/
abbrev DegreeCell (A B k : Nat) : Type :=
  { c : WorldCell A B // worldDegree c = k }

/-- Poincare complement is an equivalence between degree k and
degree top-k. -/
def degreeDualEquiv
    {A B : Nat} (k : Nat) (hk : k ≤ A+B-2) :
    DegreeCell A B k ≃ DegreeCell A B (A+B-2-k) where
  toFun c :=
    ⟨worldDual c.1, by
      rw [worldDegree_dual, c.2]⟩
  invFun c :=
    ⟨worldDual c.1, by
      rw [worldDegree_dual, c.2]
      omega⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- **PALINDROMIC HILBERT LAW.**
Complementary degree sectors have exactly the same number of cells in every
rectangular world. -/
theorem degreeCell_card_symmetry
    {A B : Nat} (k : Nat) (hk : k ≤ A+B-2) :
    Fintype.card (DegreeCell A B k) =
      Fintype.card (DegreeCell A B (A+B-2-k)) := by
  exact Fintype.card_congr (degreeDualEquiv k hk)

/-- Delta basis vector at one world cell. -/
def worldBasis
    {A B : Nat} (c : WorldCell A B) : WorldCoef A B :=
  fun x => if x = c then 1 else 0

/-- Dimension-free top intersection pairing. -/
def worldTopPairing
    {A B : Nat} (f g : WorldCoef A B) : ℤ :=
  ∑ c : WorldCell A B, f c * g (worldDual c)

/-- Pairing against the complementary basis vector extracts one coordinate. -/
theorem worldTopPairing_pick_left
    {A B : Nat} (f : WorldCoef A B) (c : WorldCell A B) :
    worldTopPairing f (worldBasis (worldDual c)) = f c := by
  classical
  unfold worldTopPairing
  rw [Finset.sum_eq_single c]
  · simp [worldBasis]
  · intro b hb hbc
    have hne : worldDual b ≠ worldDual c := by
      intro h
      exact hbc (worldDual_injective h)
    simp [worldBasis, hne]
  · simp

/-- Mirrored coordinate extraction. -/
theorem worldTopPairing_pick_right
    {A B : Nat} (g : WorldCoef A B) (c : WorldCell A B) :
    worldTopPairing (worldBasis (worldDual c)) g = g c := by
  classical
  unfold worldTopPairing
  rw [Finset.sum_eq_single (worldDual c)]
  · simp [worldBasis]
  · intro b hb hbc
    simp [worldBasis, hbc]
  · simp

/-- **INTEGRAL LEFT NONDEGENERACY IN EVERY DIMENSION.** -/
theorem worldTopPairing_nondegenerate_left
    {A B : Nat} (f : WorldCoef A B)
    (h : ∀ g : WorldCoef A B, worldTopPairing f g = 0) :
    f = fun _ => 0 := by
  funext c
  have hc := h (worldBasis (worldDual c))
  rw [worldTopPairing_pick_left] at hc
  exact hc

/-- **INTEGRAL RIGHT NONDEGENERACY IN EVERY DIMENSION.** -/
theorem worldTopPairing_nondegenerate_right
    {A B : Nat} (g : WorldCoef A B)
    (h : ∀ f : WorldCoef A B, worldTopPairing f g = 0) :
    g = fun _ => 0 := by
  funext c
  have hc := h (worldBasis (worldDual c))
  rw [worldTopPairing_pick_right] at hc
  exact hc

/-- Pairing of two exact sectors is zero unless their degrees add to top. -/
theorem worldTopPairing_sectors_zero
    {A B : Nat} (k j : Nat)
    (hkj : k+j ≠ A+B-2)
    (f g : WorldCoef A B) :
    worldTopPairing
        (worldSectorProj k f)
        (worldSectorProj j g) = 0 := by
  classical
  unfold worldTopPairing
  apply Finset.sum_eq_zero
  intro c hc
  unfold worldSectorProj
  by_cases hk : worldDegree c = k
  · by_cases hj : worldDegree (worldDual c) = j
    · exfalso
      apply hkj
      have hdual := worldDegree_dual_sum c
      omega
    · simp [hk, hj]
  · simp [hk]

/-- The dual of a degree-k basis cell lies in the complementary sector. -/
theorem worldBasis_dual_degree
    {A B : Nat} (k : Nat) (hk : k ≤ A+B-2)
    (c : DegreeCell A B k) :
    worldSectorProj (A+B-2-k)
        (worldBasis (worldDual c.1)) =
      worldBasis (worldDual c.1) := by
  funext x
  unfold worldSectorProj worldBasis
  by_cases hx : x = worldDual c.1
  · subst x
    have hdeg :
        worldDegree (worldDual c.1) = A+B-2-k := by
      rw [worldDegree_dual, c.2]
    simp [hdeg]
  · simp [hx]

/-- **PERFECT COMPLEMENTARY-SECTOR PAIRING.**
A degree-k class pairing to zero against every complementary degree class
is itself zero. -/
theorem complementary_sector_nondegenerate_left
    {A B : Nat} (k : Nat) (hk : k ≤ A+B-2)
    (f : WorldCoef A B)
    (hf : worldSectorProj k f = f)
    (horth :
      ∀ g : WorldCoef A B,
        worldTopPairing f
          (worldSectorProj (A+B-2-k) g) = 0) :
    f = fun _ => 0 := by
  funext c
  by_cases hcdeg : worldDegree c = k
  · let ck : DegreeCell A B k := ⟨c,hcdeg⟩
    have hzero :=
      horth (worldBasis (worldDual c))
    have hproj :
        worldSectorProj (A+B-2-k)
          (worldBasis (worldDual c)) =
        worldBasis (worldDual c) := by
      simpa [ck] using worldBasis_dual_degree k hk ck
    rw [hproj, worldTopPairing_pick_left] at hzero
    exact hzero
  · have hpoint := congrFun hf c
    unfold worldSectorProj at hpoint
    simp [hcdeg] at hpoint
    exact hpoint.symm

/-- Capstone: involutive duality, palindromic sectors, global perfect pairing,
and complementary-sector orthogonality all hold in arbitrary world shape. -/
theorem world_poincare_duality_crown :
    (∀ A B (c : WorldCell A B),
      worldDual (worldDual c) = c)
    ∧ (∀ A B (c : WorldCell A B),
      worldDegree (worldDual c) + worldDegree c = A+B-2)
    ∧ (∀ A B k, k ≤ A+B-2 →
      Fintype.card (DegreeCell A B k) =
        Fintype.card (DegreeCell A B (A+B-2-k)))
    ∧ (∀ A B (f : WorldCoef A B),
      (∀ g : WorldCoef A B, worldTopPairing f g = 0) →
        f = fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B c
    exact worldDual_involutive c
  · intro A B c
    exact worldDegree_dual_sum c
  · intro A B k hk
    exact degreeCell_card_symmetry k hk
  · intro A B f h
    exact worldTopPairing_nondegenerate_left f h

#check complementFin
#check worldDual
#check worldDegree_dual_sum
#check degreeDualEquiv
#check degreeCell_card_symmetry
#check worldTopPairing
#check worldTopPairing_pick_left
#check worldTopPairing_nondegenerate_left
#check worldTopPairing_sectors_zero
#check complementary_sector_nondegenerate_left
#check world_poincare_duality_crown

#print axioms worldDegree_dual_sum
#print axioms degreeCell_card_symmetry
#print axioms worldTopPairing_nondegenerate_left
#print axioms worldTopPairing_sectors_zero
#print axioms complementary_sector_nondegenerate_left
#print axioms world_poincare_duality_crown


/-! ## Compact-support/ordinary pairing without a global top cell -/
def cosmicPairing (f : CompactCosmos) (g : CompletedCosmos) : ℤ :=
  f.sum (fun c z => z*g c)

@[simp] theorem cosmicPairing_single (c : CosmicCell) (z : ℤ) (g : CompletedCosmos) :
    cosmicPairing (Finsupp.single c z) g = z*g c := by
  simp [cosmicPairing]

def cosmicProbe (c : CosmicCell) : CompletedCosmos := fun d => if d=c then 1 else 0

@[simp] theorem cosmicPairing_probe (f : CompactCosmos) (c : CosmicCell) :
    cosmicPairing f (cosmicProbe c) = f c := by
  classical
  by_cases hc : f c=0
  · simp [cosmicPairing, Finsupp.sum, cosmicProbe, hc]
  · simp [cosmicPairing, Finsupp.sum, cosmicProbe, Finsupp.mem_support_iff, hc]

theorem cosmicPairing_nondegenerate_left (f : CompactCosmos)
    (h : ∀ g : CompletedCosmos, cosmicPairing f g=0) : f=0 := by
  apply Finsupp.ext
  intro c
  simpa using h (cosmicProbe c)

theorem cosmicPairing_nondegenerate_right (g : CompletedCosmos)
    (h : ∀ f : CompactCosmos, cosmicPairing f g=0) : g=0 := by
  funext c
  simpa using h (Finsupp.single c 1)

/-- Observational equality on a support envelope suffices for every compact
pairing; there is no appeal to a fictional last cell at infinity. -/
theorem cosmicPairing_local (f : CompactCosmos) (g h : CompletedCosmos)
    (heq : ∀ c ∈ f.support, g c=h c) : cosmicPairing f g=cosmicPairing f h := by
  unfold cosmicPairing Finsupp.sum
  apply Finset.sum_congr rfl
  intro c hc
  exact congrArg (fun z : ℤ => f c * z) (heq c hc)

#print axioms cosmicPairing_nondegenerate_left
#print axioms cosmicPairing_nondegenerate_right

end GSTWorldPoincareDuality
