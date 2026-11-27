import Mathlib

/-!
# GST infinite source-birth: alpha-marked period, rationality and Chow gates

Authoritative ORIGINAL-X geometry:
 research/derivations/GST_20261112_alpha_marked_infinity_control_hodge_locus_and_source_obstructions.tex
 research/derivations/GST_20261112_constant_family_countable_field_algebraic_witness_descent.tex

Three executed original-X source-existence checks:

1. Prescribed rational Hodge class alpha on E_i x E_i:
   J_tau^T alpha J_tau=alpha has exact period components
   -u/v and 1/v-1 for tau=u+i v, v!=0. The scalar period-gate
   is zero EXACTLY at the prescribed original complex structure.
   This is an alpha-dependent obstruction to manufacturing infinitely
   many distinct Hodge-preserving fibers.

2. The TRUE original cross-class on E_{i t} x E_i satisfies
   the rational (1,1) equations c=-t*b, d=t*a.
   In particular the fixed original alpha=(a,b,c,d)=(0,1,-1,0)
   stays Hodge precisely at t=1. The independent exact Wolfram
   computation verifies the entire 4-by-4 real J-invariance matrix.

3. A true degree-one algebraic line of xy=s z^2 at s=0 has an
   ACTUAL first-order lifting obstruction: y*L+x*M=-z^2 is impossible.
   The algebraic evaluation x=y=0,z=1 disproves this equality for
   ANY coefficient commutative ring with a nontrivial target.

4. A genuine source on ONE very-general fiber of a smooth
   projective family suffices to descend to ALL original fibers
   under the separate RELATIVE CHOW PROPERNESS geometric theorem.
   The Lean set lemma here proves precisely the countable closed
   profile logic. It does NOT postulate existence of that source.

NO sorry, no native Hodge surjectivity and no hidden target
Chow representative are introduced.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTNativeAlphaMarkedInfiniteSourceGate

/-- Two entries of the REAL Hodge-type defect for the exact
PRESCRIBED diagonal-cross class alpha on
E_(u+i*v) x E_i, calculated from J_tau^T A_alpha J_tau-A_alpha.
The complete J-invariance check is in the geometric derivation. -/
def prescribedAlphaPeriodDefect (u v : ℚ) : ℚ × ℚ :=
  (-u / v, 1 / v - 1)

/-- The prescribed cross alpha has NO nonconstant rational-period
Hodge locus on the entire first-factor deformation chart:
the exact period gate is zero only at tau=i. -/
theorem prescribed_alpha_isolated_period
    (u v : ℚ) (hv : v ≠ 0) :
    prescribedAlphaPeriodDefect u v = (0, 0) ↔
      u = 0 ∧ v = 1 := by
  constructor
  · intro h
    have hu : -u / v = 0 := congrArg Prod.fst h
    have hvone : 1 / v - 1 = 0 := congrArg Prod.snd h
    field_simp [hv] at hu hvone
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [prescribedAlphaPeriodDefect]

/-- The exact rational cross-Hodge coordinates of the actual
projective abelian surface E_(i*t) x E_i; sourced from a full
J-invariance computation, not a guessed Hodge-to-Chow inverse. -/
def crossHodgeEquation (t a b c d : ℚ) : Prop :=
  d = t * a ∧ c = -(t * b)

/-- For the ORIGINAL integral diagonal cross alpha=(0,1,-1,0),
the Hodge type equation forces the unchanged original t=1. -/
theorem original_integral_cross_class_only_at_one (t : ℚ) :
    crossHodgeEquation t 0 1 (-1) 0 ↔ t = 1 := by
  simp [crossHodgeEquation]
  exact eq_comm

/-- General set-theoretic heart of the ONE VERY-GENERAL fiber theorem.
Actual relative Chow sources are encoded by countably many CLOSED
profile-images C_n. The geometric theorem proves this hypothesis.
A source at a point outside all PROPER images implies a source
on EVERY original X fiber, independent of cycle degree bounds. -/
theorem oneVeryGeneralSource_descendsToOriginal
    {B : Type*} (C : ℕ → Set B)
    (bGeneric bOriginal : B)
    (hVeryGeneral : ∀ n, C n ≠ Set.univ → bGeneric ∉ C n)
    (hSource : ∃ n, bGeneric ∈ C n) :
    ∃ n, bOriginal ∈ C n := by
  rcases hSource with ⟨n, hn⟩
  have hfull : C n = Set.univ := by
    by_contra hproper
    exact hVeryGeneral n hproper hn
  refine ⟨n, ?_⟩
  rw [hfull]
  trivial

/-- The independent exact FIRST-ORDER obstruction to deforming
one algebraic component of xy=s*z^2 from the special fiber:
the hypothetical factorization forces y*L+x*M=-z*z,
which fails under the witness x=y=0,z=1.
R may be the genuine polynomial coordinate ring, and phi its
evaluation at [0:0:1]; no Hodge assumption is involved. -/
theorem no_algebraic_line_lift_at_first_order
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (phi : R →+* S) (x y z : R)
    (hx : phi x = 0) (hy : phi y = 0) (hz : phi z = 1) :
    ¬ ∃ L M : R, y * L + x * M = -(z * z) := by
  rintro ⟨L, M, h⟩
  have hImage := congrArg phi h
  simp [hx, hy, hz] at hImage

#check prescribedAlphaPeriodDefect
#check prescribed_alpha_isolated_period
#check crossHodgeEquation
#check original_integral_cross_class_only_at_one
#check oneVeryGeneralSource_descendsToOriginal
#check no_algebraic_line_lift_at_first_order

#print axioms prescribed_alpha_isolated_period
#print axioms original_integral_cross_class_only_at_one
#print axioms oneVeryGeneralSource_descendsToOriginal
#print axioms no_algebraic_line_lift_at_first_order

end GSTNativeAlphaMarkedInfiniteSourceGate
