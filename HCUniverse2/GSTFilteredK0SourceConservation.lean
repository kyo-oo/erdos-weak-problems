import Mathlib

/-!
# Arbitrary-depth extension conservation and finite-trace source obstruction

Uncompiled proof draft. For actual algebraic bundles, short exact sequences
give the displayed K0 equations. The readout is a positive Chern-character
piece, whose value on the trivial line is zero. Naturality and degree trace
must be instantiated with the actual canonical maps, not chosen to force a
conclusion. This no-go applies to the stated finite-cover filtered constructor.
-/

open scoped BigOperators
namespace GSTFilteredK0SourceConservation

theorem filtration_total {K : Type*} [AddCommGroup K]
    (tower graded : ℕ → K) (hzero : tower 0=0)
    (hstep : ∀ j,tower (j+1)=tower j+graded j) (n : ℕ) :
    tower n=∑ j ∈ Finset.range n,graded j := by
  induction n with
  | zero => simpa using hzero
  | succ n ih => rw [hstep,ih,Finset.sum_range_succ]

/-- No number or ordering of extensions changes an additive characteristic. -/
theorem filtration_character {K W : Type*} [AddCommGroup K] [AddCommGroup W]
    (ch : K →+ W) (tower graded : ℕ → K) (hzero : tower 0=0)
    (hstep : ∀ j,tower (j+1)=tower j+graded j) (n : ℕ) :
    ch (tower n)=∑ j ∈ Finset.range n,ch (graded j) := by
  rw [filtration_total tower graded hzero hstep,map_sum]

theorem trivial_graded_character_zero {K W : Type*}
    [AddCommGroup K] [AddCommGroup W]
    (ch : K →+ W) (unitClass : K) (hunit : ch unitClass=0)
    (tower graded : ℕ → K) (rank : ℕ → ℤ) (hzero : tower 0=0)
    (hstep : ∀ j,tower (j+1)=tower j+graded j)
    (hgraded : ∀ j,graded j=rank j • unitClass) (n : ℕ) : ch (tower n)=0 := by
  rw [filtration_character ch tower graded hzero hstep]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hgraded,map_zsmul,hunit,smul_zero]

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

theorem finite_trace_reflects_zero (pull : V →ₗ[ℚ] W) (push : W →ₗ[ℚ] V)
    (degree : ℚ) (hd : degree≠0) (trace : ∀ x,push (pull x)=degree • x)
    (x : V) (hx : pull x=0) : x=0 := by
  have h := trace x
  rw [hx,map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hd

/-- The actual original-X readout vanishes if its finite pullback has a
trivial-graded filtration. The filtration length is unrestricted. -/
theorem finite_filtered_source_character_zero {K : Type*} [AddCommGroup K]
    (pull : V →ₗ[ℚ] W) (push : W →ₗ[ℚ] V)
    (degree : ℚ) (hd : degree≠0) (trace : ∀ x,push (pull x)=degree • x)
    (ch : K →+ W) (unitClass : K) (hunit : ch unitClass=0)
    (tower graded : ℕ → K) (rank : ℕ → ℤ) (hzero : tower 0=0)
    (hstep : ∀ j,tower (j+1)=tower j+graded j)
    (hgraded : ∀ j,graded j=rank j • unitClass) (n : ℕ)
    (originalCharacter : V) (naturality : pull originalCharacter=ch (tower n)) :
    originalCharacter=0 := by
  apply finite_trace_reflects_zero pull push degree hd trace
  rw [naturality]
  exact trivial_graded_character_zero ch unitClass hunit tower graded rank
    hzero hstep hgraded n

/-- A prescribed nonzero target cannot be born from such a carrier at any
nonzero rational scale. This is an obstruction to that constructor, not HC. -/
theorem scaled_target_zero_of_character_zero (alpha originalCharacter : V)
    (mu : ℚ) (hmu : mu≠0) (hcharacter : originalCharacter=0)
    (hpure : originalCharacter=mu • alpha) : alpha=0 := by
  have h : mu • alpha=0 := hpure.symm.trans hcharacter
  exact (smul_eq_zero.mp h).resolve_left hmu

#print axioms filtration_character
#print axioms finite_filtered_source_character_zero
#print axioms scaled_target_zero_of_character_zero

/-! ## Localization after the sharper smooth-branch computation

These are exactness consequences only. The geometric dimension argument
identifying a zero support group is supplied in the hand derivation.
-/

theorem localized_source_has_support {A B D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (support : A →+ B) (restrict : B →+ D)
    (hexact : ∀ b,restrict b=0 ↔ ∃ a,support a=b)
    (b : B) (hb : restrict b=0) : ∃ a,support a=b :=
  (hexact b).mp hb

theorem localized_source_zero_if_support_zero {A B D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (support : A →+ B) (restrict : B →+ D)
    (hexact : ∀ b,restrict b=0 ↔ ∃ a,support a=b)
    (hzero : ∀ a,support a=0) (b : B) (hb : restrict b=0) : b=0 := by
  obtain ⟨a,ha⟩ := localized_source_has_support support restrict hexact b hb
  exact ha.symm.trans (hzero a)

theorem original_return_zero_of_localized_source {B D : Type*}
    [AddCommGroup B] [AddCommGroup D]
    (restrict : B →+ D) (hinj : Function.Injective restrict)
    (returnToOriginal : B →+ V) (b : B) (hb : restrict b=0) :
    returnToOriginal b=0 := by
  have hz : b=0 := hinj (hb.trans (map_zero restrict).symm)
  rw [hz,map_zero]

#print axioms localized_source_zero_if_support_zero
end GSTFilteredK0SourceConservation
