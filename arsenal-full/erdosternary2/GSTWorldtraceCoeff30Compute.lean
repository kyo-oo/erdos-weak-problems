import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact kernel-verifiable GST coefficient c_29 modulo 3^30
Never expand the huge number 4^(3^29). Instead propagate a tiny modular
coefficient by the exact GST cubic recursion and a polynomial congruence law.
-/
namespace GSTWorldtraceCoeff30Compute

open GSTCanonicalTailLTE

def modulus : Nat := 3^30

def residueCoeff : Nat → Nat
 | 0 => 1
 | n+1 =>
   let x := residueCoeff n
   (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus

private theorem polynomial_mod (n x y : Nat)
    (h : x%modulus=y%modulus) :
    (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus =
    (y+3^(n+1)*y^2+3^(2*n+1)*y^3)%modulus := by
  have hp2 : (x^2)%modulus=(y^2)%modulus := by
    calc
      (x^2)%modulus = ((x%modulus)^2)%modulus := Nat.pow_mod x 2 modulus
      _ = ((y%modulus)^2)%modulus := by rw [h]
      _ = (y^2)%modulus := (Nat.pow_mod y 2 modulus).symm
  have hp3 : (x^3)%modulus=(y^3)%modulus := by
    calc
      (x^3)%modulus = ((x%modulus)^3)%modulus := Nat.pow_mod x 3 modulus
      _ = ((y%modulus)^3)%modulus := by rw [h]
      _ = (y^3)%modulus := (Nat.pow_mod y 3 modulus).symm
  have hm2 : (3^(n+1)*x^2)%modulus =
      (3^(n+1)*y^2)%modulus := by
    calc
      (3^(n+1)*x^2)%modulus =
          ((3^(n+1)%modulus)*(x^2%modulus))%modulus :=
        Nat.mul_mod _ _ _
      _ = ((3^(n+1)%modulus)*(y^2%modulus))%modulus := by rw [hp2]
      _ = (3^(n+1)*y^2)%modulus := (Nat.mul_mod _ _ _).symm
  have hm3 : (3^(2*n+1)*x^3)%modulus =
      (3^(2*n+1)*y^3)%modulus := by
    calc
      (3^(2*n+1)*x^3)%modulus =
          ((3^(2*n+1)%modulus)*(x^3%modulus))%modulus :=
        Nat.mul_mod _ _ _
      _ = ((3^(2*n+1)%modulus)*(y^3%modulus))%modulus := by rw [hp3]
      _ = (3^(2*n+1)*y^3)%modulus := (Nat.mul_mod _ _ _).symm
  have hsum2 :
      (x+3^(n+1)*x^2)%modulus =
      (y+3^(n+1)*y^2)%modulus := by
    calc
      (x+3^(n+1)*x^2)%modulus =
        ((x%modulus)+(3^(n+1)*x^2)%modulus)%modulus :=
          Nat.add_mod _ _ _
      _ = ((y%modulus)+(3^(n+1)*y^2)%modulus)%modulus := by
        rw [h, hm2]
      _ = (y+3^(n+1)*y^2)%modulus := (Nat.add_mod _ _ _).symm
  calc
    (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus =
      (((x+3^(n+1)*x^2)%modulus)+
       (3^(2*n+1)*x^3)%modulus)%modulus := Nat.add_mod _ _ _
    _ = (((y+3^(n+1)*y^2)%modulus)+
       (3^(2*n+1)*y^3)%modulus)%modulus := by rw [hsum2, hm3]
    _ = (y+3^(n+1)*y^2+3^(2*n+1)*y^3)%modulus :=
       (Nat.add_mod _ _ _).symm

theorem residue_coeff_correct (n : Nat) :
    residueCoeff n = lteCoeff n%modulus := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have h : residueCoeff n%modulus=lteCoeff n%modulus := by
        rw [ih]
        simp only [Nat.mod_mod]
      have hp := polynomial_mod n (residueCoeff n) (lteCoeff n) h
      change
        (residueCoeff n +3^(n+1)*(residueCoeff n)^2+
          3^(2*n+1)*(residueCoeff n)^3)%modulus =
        (lteCoeff n +3^(n+1)*(lteCoeff n)^2+
          3^(2*n+1)*(lteCoeff n)^3)%modulus
      exact hp

/-- A finite 30-step modular-recurrence computation, not huge raw powers. -/
theorem residue_coeff29 :
    residueCoeff 29 = 28881270545965 := by
  have h0 : residueCoeff 0 = 1 := by decide
  have h1 : residueCoeff 1 = 7 := by
    change (residueCoeff 0 + 3^1*(residueCoeff 0)^2 + 3^(2*0+1)*(residueCoeff 0)^3) % modulus = 7
    rw [h0]
    decide
  have h2 : residueCoeff 2 = 9709 := by
    change (residueCoeff 1 + 3^2*(residueCoeff 1)^2 + 3^(2*1+1)*(residueCoeff 1)^3) % modulus = 9709
    rw [h1]
    decide
  have h3 : residueCoeff 3 = 16508849503894 := by
    change (residueCoeff 2 + 3^3*(residueCoeff 2)^2 + 3^(2*2+1)*(residueCoeff 2)^3) % modulus = 16508849503894
    rw [h2]
    decide
  have h4 : residueCoeff 4 = 739617338671 := by
    change (residueCoeff 3 + 3^4*(residueCoeff 3)^2 + 3^(2*3+1)*(residueCoeff 3)^3) % modulus = 739617338671
    rw [h3]
    decide
  have h5 : residueCoeff 5 = 71067161322664 := by
    change (residueCoeff 4 + 3^5*(residueCoeff 4)^2 + 3^(2*4+1)*(residueCoeff 4)^3) % modulus = 71067161322664
    rw [h4]
    decide
  have h6 : residueCoeff 6 = 54811230443908 := by
    change (residueCoeff 5 + 3^6*(residueCoeff 5)^2 + 3^(2*5+1)*(residueCoeff 5)^3) % modulus = 54811230443908
    rw [h5]
    decide
  have h7 : residueCoeff 7 = 4017725547505 := by
    change (residueCoeff 6 + 3^7*(residueCoeff 6)^2 + 3^(2*6+1)*(residueCoeff 6)^3) % modulus = 4017725547505
    rw [h6]
    decide
  have h8 : residueCoeff 8 = 53557880811820 := by
    change (residueCoeff 7 + 3^8*(residueCoeff 7)^2 + 3^(2*7+1)*(residueCoeff 7)^3) % modulus = 53557880811820
    rw [h7]
    decide
  have h9 : residueCoeff 9 = 2446769818006 := by
    change (residueCoeff 8 + 3^9*(residueCoeff 8)^2 + 3^(2*8+1)*(residueCoeff 8)^3) % modulus = 2446769818006
    rw [h8]
    decide
  have h10 : residueCoeff 10 = 6224067740734 := by
    change (residueCoeff 9 + 3^10*(residueCoeff 9)^2 + 3^(2*9+1)*(residueCoeff 9)^3) % modulus = 6224067740734
    rw [h9]
    decide
  have h11 : residueCoeff 11 = 58944092348788 := by
    change (residueCoeff 10 + 3^11*(residueCoeff 10)^2 + 3^(2*10+1)*(residueCoeff 10)^3) % modulus = 58944092348788
    rw [h10]
    decide
  have h12 : residueCoeff 12 = 177815079542482 := by
    change (residueCoeff 11 + 3^12*(residueCoeff 11)^2 + 3^(2*11+1)*(residueCoeff 11)^3) % modulus = 177815079542482
    rw [h11]
    decide
  have h13 : residueCoeff 13 = 180826261449352 := by
    change (residueCoeff 12 + 3^13*(residueCoeff 12)^2 + 3^(2*12+1)*(residueCoeff 12)^3) % modulus = 180826261449352
    rw [h12]
    decide
  have h14 : residueCoeff 14 = 95810771521789 := by
    change (residueCoeff 13 + 3^14*(residueCoeff 13)^2 + 3^(2*13+1)*(residueCoeff 13)^3) % modulus = 95810771521789
    rw [h13]
    decide
  have h15 : residueCoeff 15 = 23778641378788 := by
    change (residueCoeff 14 + 3^15*(residueCoeff 14)^2 + 3^(2*14+1)*(residueCoeff 14)^3) % modulus = 23778641378788
    rw [h14]
    decide
  have h16 : residueCoeff 16 = 13573383044434 := by
    change (residueCoeff 15 + 3^16*(residueCoeff 15)^2 + 3^(2*15+1)*(residueCoeff 15)^3) % modulus = 13573383044434
    rw [h15]
    decide
  have h17 : residueCoeff 17 = 188848740136021 := by
    change (residueCoeff 16 + 3^17*(residueCoeff 16)^2 + 3^(2*16+1)*(residueCoeff 16)^3) % modulus = 188848740136021
    rw [h16]
    decide
  have h18 : residueCoeff 18 = 97001415126835 := by
    change (residueCoeff 17 + 3^18*(residueCoeff 17)^2 + 3^(2*17+1)*(residueCoeff 17)^3) % modulus = 97001415126835
    rw [h17]
    decide
  have h19 : residueCoeff 19 = 27350572193926 := by
    change (residueCoeff 18 + 3^19*(residueCoeff 18)^2 + 3^(2*18+1)*(residueCoeff 18)^3) % modulus = 27350572193926
    rw [h18]
    decide
  have h20 : residueCoeff 20 = 24289175489848 := by
    change (residueCoeff 19 + 3^20*(residueCoeff 19)^2 + 3^(2*19+1)*(residueCoeff 19)^3) % modulus = 24289175489848
    rw [h19]
    decide
  have h21 : residueCoeff 21 = 15104985377614 := by
    change (residueCoeff 20 + 3^21*(residueCoeff 20)^2 + 3^(2*20+1)*(residueCoeff 20)^3) % modulus = 15104985377614
    rw [h20]
    decide
  have h22 : residueCoeff 22 = 193443547135561 := by
    change (residueCoeff 21 + 3^22*(residueCoeff 21)^2 + 3^(2*21+1)*(residueCoeff 21)^3) % modulus = 193443547135561
    rw [h21]
    decide
  have h23 : residueCoeff 23 = 110785836125455 := by
    change (residueCoeff 22 + 3^23*(residueCoeff 22)^2 + 3^(2*22+1)*(residueCoeff 22)^3) % modulus = 110785836125455
    rw [h22]
    decide
  have h24 : residueCoeff 24 = 68703835189786 := by
    change (residueCoeff 23 + 3^24*(residueCoeff 23)^2 + 3^(2*23+1)*(residueCoeff 23)^3) % modulus = 68703835189786
    rw [h23]
    decide
  have h25 : residueCoeff 25 = 148348964477428 := by
    change (residueCoeff 24 + 3^25*(residueCoeff 24)^2 + 3^(2*24+1)*(residueCoeff 24)^3) % modulus = 148348964477428
    rw [h24]
    decide
  have h26 : residueCoeff 26 = 181393220245705 := by
    change (residueCoeff 25 + 3^26*(residueCoeff 25)^2 + 3^(2*25+1)*(residueCoeff 25)^3) % modulus = 181393220245705
    rw [h25]
    decide
  have h27 : residueCoeff 27 = 74634855455887 := by
    change (residueCoeff 26 + 3^27*(residueCoeff 26)^2 + 3^(2*26+1)*(residueCoeff 26)^3) % modulus = 74634855455887
    rw [h26]
    decide
  have h28 : residueCoeff 28 = 166142025275731 := by
    change (residueCoeff 27 + 3^28*(residueCoeff 27)^2 + 3^(2*27+1)*(residueCoeff 27)^3) % modulus = 166142025275731
    rw [h27]
    decide
  have h29 : residueCoeff 29 = 28881270545965 := by
    change (residueCoeff 28 + 3^29*(residueCoeff 28)^2 + 3^(2*28+1)*(residueCoeff 28)^3) % modulus = 28881270545965
    rw [h28]
    decide
  exact h29

/-- Fully kernel-certified GST stable-coefficient value c_29 modulo 3^30. -/
theorem coeff29_exact_mod30 :
    lteCoeff 29 % 3^30 = 28881270545965 := by
  calc
    lteCoeff 29 % 3^30 = residueCoeff 29 :=
      (residue_coeff_correct 29).symm
    _ = 28881270545965 := residue_coeff29

#print axioms residue_coeff_correct
#print axioms residue_coeff29
#print axioms coeff29_exact_mod30

end GSTWorldtraceCoeff30Compute
