# GST/Worldtrace normalized-core rigidity: 2026-10-29

**Base:** e22be08ef95b4d180fab105c198a4e00b8ccacc2. **Status:** new all-scale finite-core theorem, not a proof of the full Erdős conjecture.

## Exact new statement

For every u,s in N with 1 <= u <= 1,171,317, u%3 != 0,
and K=u*3^s not in {1,4}, there is a ternary position p
with 1 <= p <= s+42 and digit_3(4^K,p)=2.
When s>=29, a stronger bound p<=s+30 holds.

The finite portion is exhaustively *computer-verified*, not yet a
22-million-case kernel proof. The unbounded s-reduction uses formal
GST coefficient-stabilization and tower-window lemmas.

## Mathematical derivation

Define c_s=(4^(3^s)-1)/3^(s+1). Its exact GST cubic recursion is
  c_(s+1)=c_s+3^(s+1)*c_s^2+3^(2s+1)*c_s^3.
It follows by induction that, for every width w>=1 and s>=w-1,
  c_s = c_(w-1) (mod 3^w).

The exact exponent tower factorization
  4^(u*3^s)=(1+3^(s+1)*c_s)^u
and binomial expansion imply
  floor(4^(u*3^s)/3^(s+1)) = u*c_s (mod 3^(s+1)).
Therefore, for k<=s,
  digit_3(4^(u*3^s), s+1+k)=digit_3(u*c_s,k).

At width 30, c_29 mod 3^30 = 28881270545965.
Every normalized u in 1..1171317 has a digit 2 in the lowest
30 trits of u*c_29, so all s>=29 have a digit at row <=s+30.

For s=0..28, exact modular arithmetic at modulus 3^(s+85)
finds p<=s+42 in every three-free core except original exponents
1 and 4. The complete coverage is
  780878 three-free cores x 29 scales - 2 = 22645460 cases.
The largest relative position p-s-1 is 41.

**Computational reproduction:** scripts/gpt6_threefree_1171317_certificate.py.
GitHub workflow: .github/workflows/gpt6_threefree_1171317_certificate.yml.
Disjoint scale intervals: [0,7), [7,14), [14,21), [21,29);
a fifth job independently verifies the 30-trit coefficient and core scan.
No randomized sample or floating-point arithmetic is used.

## Why normalization strengthens the original cutoff

The earlier unrestricted 30-trit coefficient survivor 140805 has
  140805 = 3^3 * 5215.
It is not a three-free core and its all-scale family is already
covered by the prior <=140804 theorem applied to 5215.
The true first three-free 30-trit survivor is 1171318.
The exact identity
  4^((u*3^v)*3^s)=4^(u*3^(s+v))
absorbs arbitrary factors of three into the scale.
GSTNormalizedCoreRigidity.lean formalizes this identity and the
uniform transport of a coefficient digit; its verification status
must be checked independently from the finite script.

## New rigorous obstruction to fixed-window closure

For each L>=1, c_(L-1) == 1 (mod 3), so it has a unique inverse
r_L modulo 3^L. This inverse satisfies r_L==1 (mod 3) and
  r_L*c_(L-1) == 1 (mod 3^L).
Thus for EVERY fixed finite L a three-free natural multiplier
has a clean L-trit coefficient window. No universal proof can
follow solely by imposing one fixed coefficient-window depth.

Moreover, multiplication by c_(L-1) permutes all residues modulo
3^L. The clean three-free residues are exactly those with first
ternary digit 1 and each remaining digit 0 or 1. Hence there are
exactly 2^(L-1) clean three-free residues.

Independent Wolfram exact checks:
  L=18: c=235352482, inverse=44359807;
  L=30: c=28881270545965, inverse=109262695190521;
  L=40: c=7397285475167095237, inverse=713933817667338604.
In every case the product is 1 modulo 3^L.

This obstruction is to a finite-window proof METHOD, not to the
Erdős conjecture. A clean coefficient window does not establish
a completely digit-two-free power.

## True terminal target and strict comparator

The missing theorem is still:
  for every K>=5, exists p>=1 such that digit_3(4^K,p)=2.
The remaining step must force an eventual digit-two collision
along every *eventually-zero ternary exponent* path. The
binary 3-adic survivor tree and density estimates alone are
insufficient to exclude the finite natural paths.

The legacy V5 comparator only builds and scans for sorry.
It may print PASS for a theorem with an hGate hypothesis.
The separate scripts/gpt6_strict_problem406_comparator.sh
checks the exact unconditional challenge theorem type through Lean,
and checks trusted kernel axiom dependencies. It is a strict LOCAL
test, not an external official grading-service claim.

No unconditional proof of Erdős is asserted in this checkpoint.


## Exact all-exponent GST dust-tree and global density-zero theorem

Let D_L be the set of exponents r modulo 3^L for which 4^r has
no digit two in positions 1,...,L. The GST exponent-trit lift is

  digit_3(4^(r+a*3^L),L+1) =
    (digit_3(4^r,L+1)+a) mod 3,    0<=a<3.

The three children of each r cover the three possible new digits exactly
once. The previously fixed rows 1..L are invariant under addition of
a*3^L. Thus each surviving node has exactly two surviving children,
starting with the one empty node D_0={0}. Inductively,

  |D_L|=2^L for every L>=0.

Wolfram exact modular arithmetic independently checked L=1..8 with counts
2,4,8,16,32,64,128,256. The local one-dead-child law is formalized in
GSTWorldtraceFiniteDust.lean (verify its dedicated kernel CI before
promoting that file to kernel-checked).

For any finite N, at most 2^L*(floor((N-1)/3^L)+1) exponents 0<=K<N
can have no digit two anywhere in 4^K. Dividing by N and letting N grow
shows upper density at most (2/3)^L for each L. Taking L to infinity,
the set of complete digit-two-free four-power exponents has NATURAL
DENSITY ZERO.

This is a global unconditional consequence for unrestricted exponents K.
Density zero does not imply emptiness and is not a replacement for the
terminal natural-path exclusion.
