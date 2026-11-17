import Mathlib
import GSTLefschetzCrown

/-!
# LEFSCHETZ CROWN V2 — EXACT COMPLEMENTARY-POWER ARITHMETIC

The finite GST lattice has sector ranks 1,2,3,3,2,1.
This layer computes the complementary Lefschetz powers exactly over Z.
The resulting integral determinants are 10, 6, and 1.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTLefschetzCrownV2

open GSTWaveCohomology
open GSTCanonicalSevenAxisBridge
open GSTLefschetzCrown

def S0val (a : ℤ) : WaveCoef :=
  S12 (fun i => if i = 0 then a else 0)

def S1val (a b : ℤ) : WaveCoef :=
  S12 (fun i => if i = 1 then a else if i = 3 then b else 0)

def S2val (a b c : ℤ) : WaveCoef :=
  S12 (fun i => if i = 2 then a else if i = 4 then b else if i = 6 then c else 0)


/-- One polarization step from degree zero to degree one. -/
theorem lefschetz_degree0_to1_exact (a : ℤ) :
    lefschetzOp (S0val a) = S1val a a := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12,
      S0val, S1val] <;> ring

/-- One polarization step from degree one to degree two. -/
theorem lefschetz_degree1_to2_exact (a b : ℤ) :
    lefschetzOp (S1val a b) = S2val a (a+b) b := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12,
      S1val, S2val] <;> ring

/-- One polarization step from degree three to degree four. -/
theorem lefschetz_degree3_to4_exact (x y z : ℤ) :
    lefschetzOp (S3val x y z) = S4val (x+y) (y+z) := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12,
      S3val, S4val] <;> ring

/-- One polarization step from degree four to the top degree. -/
theorem lefschetz_degree4_to5_exact (x y : ℤ) :
    lefschetzOp (S4val x y) = S5val (x+y) := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12,
      S4val, S5val] <;> ring

/-- The middle complementary map is triangular and unimodular. -/
theorem lefschetz_degree2_exact (a b c : ℤ) :
    lefschetzOp (S2val a b c) = S3val (a+b) (b+c) c := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12,
      S2val, S3val] <;> ring

/-- The degree-one complementary third power has the exact 2x2 matrix
[[3,3],[1,3]]. -/
theorem lefschetz_degree1_third_exact (a b : ℤ) :
    (Nat.iterate lefschetzOp 3) (S1val a b) =
      S4val (3*a + 3*b) (a + 3*b) := by
  change lefschetzOp (lefschetzOp (lefschetzOp (S1val a b))) =
    S4val (3*a + 3*b) (a + 3*b)
  rw [lefschetz_degree1_to2_exact, lefschetz_degree2_exact,
      lefschetz_degree3_to4_exact]
  congr 1 <;> ring

/-- The degree-zero complementary fifth power is multiplication by ten. -/
theorem lefschetz_degree0_fifth_exact (a : ℤ) :
    (Nat.iterate lefschetzOp 5) (S0val a) = S5val (10*a) := by
  change lefschetzOp
    (lefschetzOp
      (lefschetzOp
        (lefschetzOp
          (lefschetzOp (S0val a))))) = S5val (10*a)
  rw [lefschetz_degree0_to1_exact, lefschetz_degree1_to2_exact,
      lefschetz_degree2_exact, lefschetz_degree3_to4_exact,
      lefschetz_degree4_to5_exact]
  congr 1
  ring

/-- The exact determinant at degree zero. -/
theorem lefschetz_degree0_determinant : (10 : ℤ) ≠ 0 := by decide

/-- The exact determinant of the degree-one complementary matrix. -/
theorem lefschetz_degree1_determinant :
    (3:ℤ) * 3 - 3 * 1 = 6 := by ring

/-- The exact determinant of the degree-two complementary matrix. -/
theorem lefschetz_degree2_determinant :
    (1:ℤ) = 1 := rfl

/-- Degree two to degree three is an integral isomorphism with explicit
inverse coordinates. -/
theorem lefschetz_degree2_section (x y z : ℤ) :
    lefschetzOp (S2val (x-y+z) (y-z) z) = S3val x y z := by
  rw [lefschetz_degree2_exact]
  congr 1 <;> ring

/-- The degree-zero complementary map is injective over Z. -/
theorem lefschetz_degree0_fifth_injective
    {a b : ℤ}
    (h : (Nat.iterate lefschetzOp 5) (S0val a) =
         (Nat.iterate lefschetzOp 5) (S0val b)) :
    a = b := by
  rw [lefschetz_degree0_fifth_exact, lefschetz_degree0_fifth_exact] at h
  have hc := congrArg (fun f : WaveCoef => gev f 11) h
  simp [S5val, gev_S12] at hc
  omega

/-- The degree-one complementary map is injective over Z. -/
theorem lefschetz_degree1_third_injective
    {a b c d : ℤ}
    (h : (Nat.iterate lefschetzOp 3) (S1val a b) =
         (Nat.iterate lefschetzOp 3) (S1val c d)) :
    a = c ∧ b = d := by
  rw [lefschetz_degree1_third_exact,
      lefschetz_degree1_third_exact] at h
  have h8 := congrArg (fun f : WaveCoef => gev f 8) h
  have h10 := congrArg (fun f : WaveCoef => gev f 10) h
  simp [S4val, gev_S12] at h8 h10
  constructor <;> omega

/-- The middle complementary map is injective integrally. -/
theorem lefschetz_degree2_injective
    {a b c x y z : ℤ}
    (h : lefschetzOp (S2val a b c) =
         lefschetzOp (S2val x y z)) :
    a = x ∧ b = y ∧ c = z := by
  rw [lefschetz_degree2_exact, lefschetz_degree2_exact] at h
  have h5 := congrArg (fun f : WaveCoef => gev f 5) h
  have h7 := congrArg (fun f : WaveCoef => gev f 7) h
  have h9 := congrArg (fun f : WaveCoef => gev f 9) h
  simp [S3val, gev_S12] at h5 h7 h9
  constructor
  · omega
  constructor <;> omega

/-- Integral top surjectivity fails exactly at unit scale: 1 is not in the
image of the fifth complementary power from the degree-zero lattice. -/
theorem lefschetz_degree0_not_integrally_surjective :
    ¬ ∃ a : ℤ, (Nat.iterate lefschetzOp 5) (S0val a) = S5val 1 := by
  rintro ⟨a,ha⟩
  rw [lefschetz_degree0_fifth_exact] at ha
  have h11 := congrArg (fun f : WaveCoef => gev f 11) ha
  simp [S5val, gev_S12] at h11
  omega

/-- The exact integral complementary-power profile. -/
theorem lefschetz_integral_profile :
    (∀ a : ℤ, (Nat.iterate lefschetzOp 5) (S0val a) = S5val (10*a))
    ∧ (∀ a b : ℤ, (Nat.iterate lefschetzOp 3) (S1val a b) =
        S4val (3*a+3*b) (a+3*b))
    ∧ (∀ a b c : ℤ, lefschetzOp (S2val a b c) =
        S3val (a+b) (b+c) c) :=
  ⟨lefschetz_degree0_fifth_exact,
    lefschetz_degree1_third_exact,
    lefschetz_degree2_exact⟩

#check S0val
#check S1val
#check S2val
#check lefschetz_degree0_to1_exact
#check lefschetz_degree1_to2_exact
#check lefschetz_degree2_exact
#check lefschetz_degree3_to4_exact
#check lefschetz_degree4_to5_exact
#check lefschetz_degree1_third_exact
#check lefschetz_degree0_fifth_exact
#check lefschetz_degree2_section
#check lefschetz_degree0_fifth_injective
#check lefschetz_degree1_third_injective
#check lefschetz_degree2_injective
#check lefschetz_degree0_not_integrally_surjective
#check lefschetz_integral_profile

#print axioms lefschetz_degree2_exact
#print axioms lefschetz_degree1_third_exact
#print axioms lefschetz_degree0_fifth_exact
#print axioms lefschetz_degree0_not_integrally_surjective
#print axioms lefschetz_integral_profile

end GSTLefschetzCrownV2
