/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0265 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/InformationRegenerationScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-15 15:19:07 +0530  (5c58cbd)
/-    Last-commit  : 2026-08-15 15:32:21 +0530  (2d9d22d)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-15 15:19:07 +0530  5c58cbd  (ker07-dev)
/-        Formalize canonical information regeneration step
/- [02/2] 2026-08-15 15:32:21 +0530  2d9d22d  (ker07-dev)
/-        Make canonical regeneration decomposition explicit
/- ====================================================================== -/

import InformationStateScratch
import InformationBadTraceScratch
import OriginTransducerScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Seed-retaining complete bad language for the scratch information state. -/
def GSTSeededBadTraceS (seed R : Nat) : Prop :=
  ∀ j, GSTBadPairS (gstAffineMulCarryS 4 seed R j) (gstDigitS R j)

/-- Dividing a relative affine realization by one ternary position preserves
    the same relative multiplier.  Only the finite offset is regenerated. -/
theorem gst_relative_affine_tail_divS
    (A Z Y : Nat) :
    (Z + A*Y) / 3 =
      (Z + A*(Y%3)) / 3 + A*(Y/3) := by
  have h := gst_affine_tail_div_decompositionS Z A Y 1
  simpa [gstAffineMulCarryS] using h

/-- The emitted digit of a relative affine realization depends only on the
    current child digit and the finite information offset. -/
theorem gst_relative_affine_emitted_digitS
    (A Z Y : Nat) :
    (Z + A*Y) % 3 = (Z + A*(Y%3)) % 3 := by
  simp [Nat.add_mod, Nat.mul_mod]

/-- Exact simultaneous regeneration step.  One natural-origin trit is consumed
    in the child affine state, while the parent remains the same relative
    A-affine realization of the regenerated child.  No information is erased. -/
theorem gst_canonical_information_regeneratesS
    (Q : Nat → Nat → Nat)
    (t n childOffset childMul originA A Z : Nat)
    (hrec : Q t (3*(n/3) + n%3) =
      Q t (n%3) + 3 * originA^(n%3) * Q (t+1) (n/3)) :
    let E := childOffset + childMul * Q t (n%3)
    let r := E % 3
    let childOffset' := E / 3
    let childMul' := childMul * originA^(n%3)
    let Y' := childOffset' + childMul' * Q (t+1) (n/3)
    let e := (Z + A*r) % 3
    let Z' := (Z + A*r) / 3
    childOffset + childMul * Q t n = r + 3*Y' ∧
      Z + A*(childOffset + childMul * Q t n) =
        e + 3*(Z' + A*Y') := by
  dsimp only
  have hchild :=
    affine_natural_origin_stepS Q t n childOffset childMul originA hrec
  dsimp only at hchild
  constructor
  · exact hchild
  · let r := (childOffset + childMul * Q t (n % 3)) % 3
    let Y' := (childOffset + childMul * Q t (n % 3)) / 3 +
      childMul * originA ^ (n % 3) * Q (t + 1) (n / 3)
    have hchild' : childOffset + childMul * Q t n = r + 3*Y' := by
      simpa [r, Y'] using hchild
    have hsplit : Z + A*r = (Z + A*r) % 3 + 3*((Z + A*r)/3) := by
      have h := Nat.mod_add_div (Z + A*r) 3
      omega
    calc
      Z + A*(childOffset + childMul * Q t n) =
          Z + A*(r + 3*Y') := by rw [hchild']
      _ = (Z + A*r) + 3*(A*Y') := by ring
      _ = ((Z + A*r) % 3 + 3*((Z + A*r)/3)) + 3*(A*Y') := by rw [← hsplit]
      _ = (Z + A*r) % 3 + 3*((Z + A*r)/3 + A*Y') := by ring
      _ = (Z + A * ((childOffset + childMul * Q t (n % 3)) % 3)) % 3 +
          3 * ((Z + A * ((childOffset + childMul * Q t (n % 3)) % 3)) / 3 +
            A * ((childOffset + childMul * Q t (n % 3)) / 3 +
              childMul * originA ^ (n % 3) * Q (t + 1) (n / 3))) := by
        rfl

/-- A complete seed-retaining parent bad trace remains bad after consuming its
    first ternary row.  The new seed is exactly the regenerated carry. -/
theorem gst_seeded_bad_trace_regenerates_tailS
    (D X : Nat) (hbad : GSTSeededBadTraceS D X) :
    GSTSeededBadTraceS
      (gstAffineMulCarryS 4 D X 1) (X/3) := by
  intro j
  have h := hbad (1+j)
  rw [gst_seeded_affine_carry_semigroupS D X 1 j,
      gst_seeded_affine_digit_shiftS X 1 j] at h
  simpa using h

/-- The child seed regenerates by the same local GST equation when the first
    emitted child digit is consumed. -/
theorem gst_child_seed_after_regenerationS
    (C Y : Nat) :
    gstAffineMulCarryS 4 C Y 1 =
      gstStepCarryS C (Y%3) := by
  simp [gstAffineMulCarryS, gstStepCarryS]

/-- Likewise for the parent seed. -/
theorem gst_parent_seed_after_regenerationS
    (D X : Nat) :
    gstAffineMulCarryS 4 D X 1 =
      gstStepCarryS D (X%3) := by
  simp [gstAffineMulCarryS, gstStepCarryS]

/-- NULL is therefore a regenerative carrier state, not an absorbing endpoint:
    a child digit two at carry zero moves to carry two in the regenerated tail. -/
theorem gst_null_gate_regenerates_seedS
    (Y : Nat) (hd : Y % 3 = 2) :
    gstAffineMulCarryS 4 0 Y 1 = 2 := by
  rw [gst_child_seed_after_regenerationS, hd]
  decide

/-- A GST+ child digit two similarly regenerates with carry three. -/
theorem gst_plus_gate_regenerates_seedS
    (Y : Nat) (hd : Y % 3 = 2) :
    gstAffineMulCarryS 4 3 Y 1 = 3 := by
  rw [gst_child_seed_after_regenerationS, hd]
  decide
