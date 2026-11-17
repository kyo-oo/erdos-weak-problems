import Mathlib
import GSTUniversalAddressBridge

/-!
# GST DIMENSION-FREE HODGE DIAGONAL

The historical HC Hodge layer is tied to the 4 x 3 chart:
the live weights are p < 3 and the diagonal address is 4*p.

Both facts are shadows of one rectangular theorem.

In an A x B output world:
* a weight-p diagonal cell exists exactly when p < A and p < B;
* its row-major address is p + B*p = (B+1)*p;
* a Hodge class supported on that one diagonal cell is exactly one integer
  multiple of the diagonal basis class;
* if p is outside either world depth, the Hodge sector is zero.

Thus the old p < 3 / address 4p mechanism is replaced by a
dimension-free Hodge diagonal law.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTDimensionFreeHodgeDiagonal

open GSTWorldRecoordinationGroupoid
open GSTUniversalAddressBridge

/-- Diagonal cell of weight p in an A x B output chart. -/
def diagonalState
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    ShapeState (outputShape A B) :=
  (⟨p, hpA⟩, ⟨p, hpB⟩)

/-- Canonical invariant address of the diagonal cell. -/
def diagonalAddress
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    Fin (A*B) :=
  shapeCodeEquiv (outputShape A B) (diagonalState hpA hpB)

/-- **GENERAL DIAGONAL CODE LAW.**
The old 4p address is the B=3 specialization of (B+1)p. -/
theorem diagonalAddress_val
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    (diagonalAddress hpA hpB).1 = (B+1)*p := by
  unfold diagonalAddress diagonalState
  change p + B*p = (B+1)*p
  ring

/-- Diagonal Kronecker class in an arbitrary rectangular world. -/
def worldDiagonalClass
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    ShapeCoef (outputShape A B) :=
  worldBasis (outputShape A B) (diagonalState hpA hpB)

/-- Weight-p Hodge support means all amplitudes vanish off the p,p cell. -/
def isWorldHodgeClass
    {A B : Nat} (p : Nat)
    (f : ShapeCoef (outputShape A B)) : Prop :=
  ∀ x : ShapeState (outputShape A B),
    x.1.1 ≠ p ∨ x.2.1 ≠ p -> f x = 0

/-- The diagonal class has value one at its own diagonal cell. -/
@[simp]
theorem worldDiagonalClass_at_diagonal
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    worldDiagonalClass hpA hpB (diagonalState hpA hpB) = 1 := by
  simp [worldDiagonalClass, worldBasis]

/-- The diagonal class vanishes at every other state. -/
theorem worldDiagonalClass_off_diagonal
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (x : ShapeState (outputShape A B))
    (hx : x.1.1 ≠ p ∨ x.2.1 ≠ p) :
    worldDiagonalClass hpA hpB x = 0 := by
  unfold worldDiagonalClass worldBasis
  have hne : x ≠ diagonalState hpA hpB := by
    intro h
    apply hx.elim
    · intro hC
      apply hC
      simpa [diagonalState] using congrArg (fun y => y.1.1) h
    · intro hd
      apply hd
      simpa [diagonalState] using congrArg (fun y => y.2.1) h
  simp [hne]

/-- **DIMENSION-FREE RANK-ONE HODGE CLASSIFICATION.**
Every live weight-p Hodge sector is exactly Z on its diagonal generator,
with a unique coefficient read directly at the diagonal cell. -/
theorem world_hodge_rank_one
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (f : ShapeCoef (outputShape A B)) :
    isWorldHodgeClass p f ↔
      ∃! z : ℤ,
        f = fun x => z * worldDiagonalClass hpA hpB x := by
  constructor
  · intro hf
    let d := diagonalState hpA hpB
    refine ⟨f d, ?_, ?_⟩
    · funext x
      by_cases hC : x.1.1 = p
      · by_cases hd : x.2.1 = p
        · have hx : x = d := by
            apply Prod.ext
            · apply Fin.ext
              simpa [d, diagonalState] using hC
            · apply Fin.ext
              simpa [d, diagonalState] using hd
          subst x
          simp [d]
        · have hzero := hf x (Or.inr hd)
          rw [hzero]
          simp [worldDiagonalClass_off_diagonal hpA hpB x (Or.inr hd)]
      · have hzero := hf x (Or.inl hC)
        rw [hzero]
        simp [worldDiagonalClass_off_diagonal hpA hpB x (Or.inl hC)]
    · intro z hz
      have hdiag := congrFun hz d
      have hclass :
          worldDiagonalClass hpA hpB d = 1 := by
        simp [d]
      rw [hclass, mul_one] at hdiag
      exact hdiag.symm
  · rintro ⟨z, hz, huniq⟩
    intro x hx
    rw [hz]
    change z * worldDiagonalClass hpA hpB x = 0
    rw [worldDiagonalClass_off_diagonal hpA hpB x hx]
    ring

/-- The unique coefficient is exactly the diagonal evaluation. -/
theorem world_hodge_coefficient_exact
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (f : ShapeCoef (outputShape A B))
    (hf : isWorldHodgeClass p f) :
    ∀ x : ShapeState (outputShape A B),
      f x =
        f (diagonalState hpA hpB) *
          worldDiagonalClass hpA hpB x := by
  obtain ⟨z, hz, huniq⟩ :=
    (world_hodge_rank_one hpA hpB f).mp hf
  intro x
  rw [hz]
  simp

/-- If the weight lies outside either rectangle depth, every weight-p Hodge
class is forced to be zero. -/
theorem world_hodge_zero_outside
    {A B p : Nat}
    (hout : A ≤ p ∨ B ≤ p)
    (f : ShapeCoef (outputShape A B))
    (hf : isWorldHodgeClass p f) :
    f = fun _ => 0 := by
  funext x
  apply hf x
  rcases hout with hA | hB
  · left
    have hxA : x.1.1 < A := by
      simpa [outputShape] using x.1.2
    omega
  · right
    have hxB : x.2.1 < B := by
      simpa [outputShape] using x.2.2
    omega

/-!
## Direct rational classification in every rectangular GST world

The original law above classifies integer wave amplitudes.  The rational
Clay theorem must not infer rational algebraicity solely by rationalizing
integer-valued cochains: genuinely rational amplitudes are independent inputs.

Here the original arbitrary-depth rectangular geometry is promoted directly
from ℤ-valued to ℚ-valued amplitudes.  No integrality, finite twelve-cell
constraint, or external geometric realization premise is required.
-/

/-- Rational amplitudes on any rectangular GST observation geometry. -/
abbrev RationalWorldCoef (A B : Nat) : Type :=
  ShapeState (outputShape A B) → ℚ

/-- The original integral diagonal cycle, now evaluated with rational
coefficients.  It exists at every weight visible in both axes. -/
def rationalWorldDiagonalClass
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    RationalWorldCoef A B :=
  fun x => (worldDiagonalClass hpA hpB x : ℚ)

/-- Direct rational Hodge support, not an integer cochain in disguise. -/
def isRationalWorldHodgeClass
    {A B : Nat} (p : Nat) (f : RationalWorldCoef A B) : Prop :=
  ∀ x : ShapeState (outputShape A B),
    x.1.1 ≠ p ∨ x.2.1 ≠ p → f x = 0

@[simp]
theorem rationalWorldDiagonalClass_at_diagonal
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    rationalWorldDiagonalClass hpA hpB (diagonalState hpA hpB) = 1 := by
  simp [rationalWorldDiagonalClass]

theorem rationalWorldDiagonalClass_off_diagonal
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (x : ShapeState (outputShape A B))
    (hx : x.1.1 ≠ p ∨ x.2.1 ≠ p) :
    rationalWorldDiagonalClass hpA hpB x = 0 := by
  simp [rationalWorldDiagonalClass,
    worldDiagonalClass_off_diagonal hpA hpB x hx]

/-- **DIRECT RATIONAL DIMENSION-FREE CLAY LAW.**
At every pair of finite world depths and every live weight, a rational
Hodge cochain has one and only one rational cycle coefficient.  The
coefficient is its own diagonal evaluation; no integral lift is used. -/
theorem rational_world_hodge_rank_one
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (f : RationalWorldCoef A B) :
    isRationalWorldHodgeClass p f ↔
      ∃! q : ℚ, f = fun x => q * rationalWorldDiagonalClass hpA hpB x := by
  constructor
  · intro hf
    let d := diagonalState hpA hpB
    refine ⟨f d, ?_, ?_⟩
    · funext x
      by_cases hC : x.1.1 = p
      · by_cases hd : x.2.1 = p
        · have hx : x = d := by
            apply Prod.ext
            · apply Fin.ext
              simpa [d, diagonalState] using hC
            · apply Fin.ext
              simpa [d, diagonalState] using hd
          subst x
          simp [d]
        · have hzero := hf x (Or.inr hd)
          rw [hzero]
          simp [rationalWorldDiagonalClass_off_diagonal hpA hpB x (Or.inr hd)]
      · have hzero := hf x (Or.inl hC)
        rw [hzero]
        simp [rationalWorldDiagonalClass_off_diagonal hpA hpB x (Or.inl hC)]
    · intro q hq
      have hdiag := congrFun hq d
      have hclass : rationalWorldDiagonalClass hpA hpB d = 1 := by
        simp [d]
      rw [hclass, mul_one] at hdiag
      exact hdiag.symm
  · rintro ⟨q, hq, _⟩ x hx
    rw [hq]
    change q * rationalWorldDiagonalClass hpA hpB x = 0
    rw [rationalWorldDiagonalClass_off_diagonal hpA hpB x hx]
    ring

/-- **EXACT EXTRACTOR**, rational and at arbitrary dimension. -/
theorem rational_world_hodge_coefficient_exact
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (f : RationalWorldCoef A B)
    (hf : isRationalWorldHodgeClass p f) :
    ∀ x : ShapeState (outputShape A B),
      f x = f (diagonalState hpA hpB) *
        rationalWorldDiagonalClass hpA hpB x := by
  obtain ⟨q, hq, _⟩ := (rational_world_hodge_rank_one hpA hpB f).mp hf
  intro x
  rw [hq]
  simp

/-- **SHARP DEAD-WEIGHT LAW.**  At an arbitrary out-of-depth weight every
direct rational GST Hodge cochain vanishes; there is no rational-lift loophole. -/
theorem rational_world_hodge_zero_outside
    {A B p : Nat} (hout : A ≤ p ∨ B ≤ p)
    (f : RationalWorldCoef A B)
    (hf : isRationalWorldHodgeClass p f) :
    f = fun _ => 0 := by
  funext x
  apply hf x
  rcases hout with hA | hB
  · left
    have hxA : x.1.1 < A := by
      simpa [outputShape] using x.1.2
    omega
  · right
    have hxB : x.2.1 < B := by
      simpa [outputShape] using x.2.2
    omega

/-- Full direct rational classification: exact unique generators on every
live weight, plus exact vanishing outside the observation depths. -/
theorem rational_dimension_free_hodge_crown :
    (∀ A B p (hpA : p < A) (hpB : p < B)
        (f : RationalWorldCoef A B),
      isRationalWorldHodgeClass p f ↔
        ∃! q : ℚ, f = fun x => q * rationalWorldDiagonalClass hpA hpB x)
    ∧ (∀ A B p (f : RationalWorldCoef A B),
      (A ≤ p ∨ B ≤ p) →
        isRationalWorldHodgeClass p f → f = fun _ => 0) := by
  constructor
  · intro A B p hpA hpB f
    exact rational_world_hodge_rank_one hpA hpB f
  · intro A B p f hout hf
    exact rational_world_hodge_zero_outside hout f hf

#check rational_world_hodge_rank_one
#check rational_world_hodge_coefficient_exact
#check rational_world_hodge_zero_outside
#print axioms rational_world_hodge_rank_one
#print axioms rational_dimension_free_hodge_crown

/-- Every weight is either live on both axes or lies outside at least one
axis.  Combined with world_hodge_rank_one and world_hodge_zero_outside,
this is the exact all-weight dichotomy. -/
theorem world_weight_live_or_outside
    (A B p : Nat) :
    (p < A ∧ p < B) ∨ (A ≤ p ∨ B ≤ p) := by
  omega

/-- Under the universal address dictionary, the diagonal class becomes the
single universal basis vector at address (B+1)p. -/
theorem worldAddress_diagonalClass
    {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    worldAddress (outputShape A B)
        (worldDiagonalClass hpA hpB)
      =
    addressBasis (diagonalAddress hpA hpB) := by
  exact worldAddress_worldBasis
    (outputShape A B) (diagonalState hpA hpB)

/-- Exact numeric version of the address theorem. -/
theorem worldAddress_diagonal_support_code
    {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (i : Fin (A*B))
    (hi : i.1 ≠ (B+1)*p) :
    worldAddress (outputShape A B)
      (worldDiagonalClass hpA hpB) i = 0 := by
  rw [worldAddress_diagonalClass]
  unfold addressBasis
  have hne : i ≠ diagonalAddress hpA hpB := by
    intro h
    apply hi
    rw [h, diagonalAddress_val hpA hpB]
  simp [hne]

/-- The historical diagonal index 4p is exactly the 4 x 3 specialization. -/
theorem hc_diagonal_address
    {p : Nat} (hp : p < 3) :
    (diagonalAddress (A:=4) (B:=3) (p:=p) (by omega) hp).1 = 4*p := by
  simpa using
    (diagonalAddress_val
      (A:=4) (B:=3) (p:=p) (by omega) hp)

/-- One crown collecting the dimension-free Hodge diagonal upgrade. -/
theorem dimension_free_hodge_crown :
    (∀ A B p (hpA : p < A) (hpB : p < B)
        (f : ShapeCoef (outputShape A B)),
      isWorldHodgeClass p f ↔
        ∃! z : ℤ,
          f = fun x => z * worldDiagonalClass hpA hpB x)
    ∧ (∀ A B p (f : ShapeCoef (outputShape A B)),
      (A ≤ p ∨ B ≤ p) ->
        isWorldHodgeClass p f -> f = fun _ => 0)
    ∧ (∀ A B p (hpA : p < A) (hpB : p < B),
      (diagonalAddress hpA hpB).1 = (B+1)*p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B p hpA hpB f
    exact world_hodge_rank_one hpA hpB f
  · intro A B p f hout hf
    exact world_hodge_zero_outside hout f hf
  · intro A B p hpA hpB
    exact diagonalAddress_val hpA hpB

#check diagonalAddress_val
#check worldDiagonalClass
#check isWorldHodgeClass
#check world_hodge_rank_one
#check world_hodge_coefficient_exact
#check world_hodge_zero_outside
#check world_weight_live_or_outside
#check worldAddress_diagonalClass
#check hc_diagonal_address
#check dimension_free_hodge_crown

#print axioms world_hodge_rank_one
#print axioms world_hodge_coefficient_exact
#print axioms world_hodge_zero_outside
#print axioms worldAddress_diagonalClass
#print axioms dimension_free_hodge_crown


/-! ## The Hodge generator at every natural weight -/
open GSTWorldCosmology

noncomputable def cosmicDiagonalClass (p : ℕ) : CompactCosmos := Finsupp.single (p,p) 1

def isCosmicHodgeClass (p : ℕ) (f : CompletedCosmos) : Prop :=
  ∀ c, c ≠ (p,p) → f c = 0

/-- There is no global upper weight. -/
@[simp] theorem cosmicDiagonalClass_self (p : ℕ) : cosmicDiagonalClass p (p,p) = 1 := by
  simp [cosmicDiagonalClass]

theorem cosmic_hodge_rank_one (p : ℕ) (f : CompletedCosmos) :
    isCosmicHodgeClass p f ↔
      ∃! z : ℤ, f = fun c => z * cosmicDiagonalClass p c := by
  constructor
  · intro hf
    refine ⟨f (p,p), ?_, ?_⟩
    · funext c
      by_cases hc : c=(p,p)
      · subst c; simp
      · simp [hf c hc, cosmicDiagonalClass, hc, Ne.symm hc]
    · intro z hz
      have h := congrFun hz (p,p)
      simpa using h.symm
  · rintro ⟨z, rfl, _⟩ c hc
    simp [cosmicDiagonalClass, hc, Ne.symm hc]

theorem observe_cosmicDiagonalClass {A B p : ℕ} (hA : p < A) (hB : p < B) :
    observe A B (cosmicDiagonalClass p) = worldDiagonalClass hA hB := by
  funext c
  change Finsupp.single (p,p) (1 : ℤ) (c.1.val,c.2.val) =
    if c = (⟨p,hA⟩,⟨p,hB⟩) then 1 else 0
  have he : (p,p) = (c.1.val,c.2.val) ↔ c = (⟨p,hA⟩,⟨p,hB⟩) := by
    simp only [Prod.mk.injEq, Prod.ext_iff, Fin.ext_iff, eq_comm]
  simp only [Finsupp.single_apply, he]

theorem cosmic_weight_invisible {A B p : ℕ} (h : A ≤ p ∨ B ≤ p) :
    observe A B (cosmicDiagonalClass p) = 0 := by
  funext c
  have hn : (c.1.val,c.2.val) ≠ (p,p) := by
    intro he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    rcases h with h | h <;> omega
  change cosmicDiagonalClass p (c.1.val,c.2.val) = (0 : ℤ)
  simp [cosmicDiagonalClass, hn, Ne.symm hn]

#print axioms cosmic_hodge_rank_one

end GSTDimensionFreeHodgeDiagonal
