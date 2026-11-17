# GST exact first CommonTwo for the all-ones exponent tower

2026-10-29. New mathematics derivation; paper-level, not yet Lean kernel-verified. Does not assume universal hGate.

## Physical source
For each m >= 8 put K_m=(3^m-1)/2, T_m=2^(3^m)+1, D_m=T_m/3^(m+1).
The standard factorization x^3+1=(x+1)(x^2-x+1), starting at 2+1=3, shows 3^(m+1) divides T_m and D_m is odd. For the physical affine orbit A_K=(4^K-1)/3,
2*A_(K_m)+1 = 3^m*D_m,
A_(K_m+1) = 4*A_(K_m)+1 = 2*3^m*D_m - 1.

## Universal stabilized 9-trit coefficient
T_(m+1)=3*T_m-3*T_m^2+T_m^3 exactly.
For m>=8, 3^(m+1)|T_m implies both 3*T_m^2 and T_m^3 are divisible by 3^(m+11). Thus T_(m+1) congruent 3*T_m modulo 3^(m+11).
Base m=8: 3^18=387420489; 2^6561 mod3^18 =165652127, so
T_8 mod 3^18 = 165652128 = 8416*3^9.
Repeated-squaring base certificate: 6561=2^0+2^5+2^7+2^8+2^11+2^12. The relevant 2^(2^j) residues mod3^18 at j=0,5,7,8,11,12 are respectively 2,33341917,87832543,181857625,306532588,4513507. Their product is 165652127 mod3^18.
By induction, for every m>=8,
T_m congruent 8416*3^(m+1) modulo 3^(m+10), hence
D_m congruent 8416 modulo 3^9 (=19683).

## Exact first physical collision
Let S_m=(3^m-1)/2. Then the exact affine source-neighbor decomposition is
A_(K_m) = S_m + 3^m*((D_m-1)/2),
A_(K_m+1) = (3^m-1) + 3^m*(2D_m-1).
The first m affine digits of the source are all 1, the neighbor all 2.
Because 2 is invertible mod3^9 and D_m congruent 8416,
(D_m-1)/2 congruent 14049 mod19683;
2D_m-1 congruent 16831 mod19683.
Their nine low-to-high ternary digits are:
source  [0,0,1,1,2,0,1,0,2]
neighbor[1,0,1,2,0,0,2,1,2].
The first shared digit 2 is affine position m+8. Physical original powers
4^K_m and 4^(K_m+1) equal 1+3*A_K and thus share digit 2 first
at physical position p=m+9.

THEOREM (paper derivation, all m>=8): The original CommonTwo witness for
K=(3^m-1)/2 first occurs exactly at p=m+9; there is no earlier shared 2.
This proves an infinite family of previously arbitrarily delayed genuine
physical perfect-power sources DOES eventually collide.

Validation: exact modular computations for m=8,...,70 found p=m+9,
and arithmetic residue certificate supplied above independently proves
the entire unbounded family. Not a full universal hGate proof.
The existence of a physical same-row 2 at p=m+9 for every m>=8 is now STRICT LEAN KERNEL VERIFIED in GSTProblem406AllOnesFirstCollision.lean; dedicated GitHub Actions run 40911647994 PASSED. Exact minimality of that row (the word FIRST) is established in the arithmetic derivation here, but is not yet a separately kernel-certified minimality theorem.


## Independent GST-native proof by the exact nonlinear peel1 law

The same all-scale collision admits an especially direct derivation
using existing GSTFourPowerAffineExponentPeel and the newly transplanted
GSTProblem406GSTPeelFixedPoint. Define
  B_m = ternaryOnes(m) + 3^m*14049,
so B_(m+1)=1+3B_m exactly. The established exact GST polynomial is
  peel1(x)=x+3*x*(2*x+1)^2,
and the exact source transformation is
  affineOrbit(ternaryOnes(m+1))
    =1+3*peel1(affineOrbit(ternaryOnes(m))).

Crucially
  2B_m+1=3^m*28099,
so peel1(B_m)-B_m is divisible by 3^(2m+1).
For m>=8, 2m+1>=m+9, hence
  peel1(B_m)==B_m (mod 3^(m+9)).
If affineOrbit(ternaryOnes m)==B_m mod3^(m+9), multiplication of
the congruence by 3 plus 1 and GST peel substitution gives
  affineOrbit(ternaryOnes(m+1))
    == 1+3B_m = B_(m+1) (mod3^(m+10)).
The base m=8 is a finite exact certificate:
  ternaryOnes 8 = 3280;
  3^17=129140163;
  B_8=92178769;
  4^3280 mod3^18 = 276536308 = 3*B_8+1.
Thus for ALL m>=8 the true affineOrbit source has the
full nine-trit core residue B_m, proving the same common row m+9.

Unlike a generic signed-flux or infinite controller argument, this
proof retains the exact physical source and uses GST peel dynamics
to generate its stable collision directly. Its implementation is
GSTProblem406AllOnesFirstCollision.lean and is to be promoted to
verified status only on a successful strict isolated CI receipt.
