# GST nonlinear polynomial component birth equals spectral eigenbundle CHOW, with all-X signed return

- **Date:** 2026-10-24 IST
- **Kind:** Direct Mathbox positive construction, algebraic geometry and computation self-audit
- **Base checkpoint:** `7642af890e4fb3b1abd4bcce3ea483aa614e7e0c`, branch `research/gpt6-native-point-primitive-span-20261017`
- **Target:** original X, codimension p, prescribed rational (p,p) alpha, actual original CH^p(X)_Q and canonical Betti equality
- **Math source:** [October 23 simultaneous Deligne–Gersten and spectral fold derivation, expanded with new non-split component theorem](../derivations/GST_alpha_deligne_integral_fold_kgersten_source_birth_2026_10_23.tex), source commit `104190f7905915a62f0cf3bf5fba5c6810e57f68`
- **Route distinction:** Instead of another smooth polynomial idempotent deformation (shown K0-rigid in the immediately preceding attempt), construct the INDIVIDUAL components of a reducible principal polynomial divisor on the SAME real Jouanolou fold and compute each actual CHOW class. A reducible total divisor can be Chow zero while its signed components are nonzero, mirroring October 22 nonlinear anti-deck source creation.

## 1. Genuine fold source construction

On the actual smooth affine algebraic quadric Q={xy+z^2=1} with true involution A={{z,x},{y,-z}}, P=(I+A)/2, q:Q->P1 taking the +1 eigenline, the global principal divisor of regular x is
    div_Q(x)=L_+ + L_-,  L_+=V(x,z-1), L_-=V(x,z+1).
The two lines are actual distinct reduced irreducible algebraic Cartier divisors of Q, EACH isomorphic to A1. Their sum is principal, hence zero in actual CH1(Q).

The scheme-theoretic +eigenline fiber q^-1([e2]) is EXACTLY L_-: solving P e2=e2 imposes x=0,z=-1. Hence [L_-]=q*c1(O_P1(1)) in CH^1(Q). The + eigenbundle im P=q*O_P1(-1), and therefore
    [L_+]=-[L_-]=c1^CH(im P)
in TRUE INTEGRAL CH^1(Q)=Z, not merely a numerical/Betti identity. The nonzero normalized Chern period from Oct 23 spectral curvature equals its canonical rational Betti class. The single SAME polynomial xy+z²=1 generates both the eigenbundle algebra and the nonzero signed geometric component.

## 2. Actual original-X source returned from arbitrary algebraic line bundle

For ANY original smooth projective X of dimension d>=1 and any sufficiently very ample L, choose a general pencil of sections; if d>=2 blow up its smooth codimension-two base locus b:Y->X, yielding the algebraic pencil morphism f:Y->P1 with f*O(1)=b*L-E; d=1 needs no blowup. Pull back the SAME Q-fold as W=Y×_P1 Q with affine-line bundle q_f:W->Y. The actual pulled-back born component L_{+,f} yields
    -b_*(q_f*)^-1 [L_{+,f}] = c1^CH(L) in CH^1(X).
Proof: original Q identity, Chow homotopy invariance of q_f, then b_*b* c1(L)=c1(L) and b_*E=0 for centre codim 2. No codimension-one Chow representative of a prescribed Hodge input is supplied.

For prescribed beta rational Hodge (1,1), choose M via Lefschetz (1,1) after clearing m. Take L_+=M⊗H^k, L_-=H^k, k large; the signed difference of these two actual returned component cycles divided by m gives a rational divisor Z_beta on original X with canonical Betti beta. Products of p such born signed divisor cycles give a genuine original-X CH^p representative for EVERY prescribed alpha in the divisor-generated rational Hodge subalgebra. This is an ACTUAL all-X original-geometry fold source constructor in that quantified sector, not a claim higher primitive Hodge classes are divisor products.

## 3. Executed exact source check

The independent stateless Wolfram algebra check returned
    {A²=I:True, P²=P:True, P.e2 at x=0,z=-1:{0,1}, P.e2 at x=0,z=+1:{0,0}, Groebner ideal on x=0:{z²-1,x}, two eigenline tests:True,True}.
One first symbolic call had a Wolfram ReplaceAll parentheses error and produced warnings; the second call explicitly fixed evaluation order and returned the exact clean output above. The scheme/Chow identities are mathematical proofs in the cited derivation, not numerical extrapolations.

## 4. Evidence and continuation contract

- **Proved in the exact stated scope**, subject to standard exact algebraic geometry inputs (Jouanolou affine bundles, Bertini/pencil resolution, blowup Chow pushforward, Lefschetz (1,1), canonical Betti naturality).
- **Original-X universal dimension:** Yes for every smooth projective X and rational divisor-generated target alpha, not an assumed higher codimension Chow preimage.
- **New positive GST law:** principal polynomial TOTAL divisor can have Chow-zero class while its nonlinear individual folded components have NONZERO genuine Chow classes; these agree EXACTLY with a spectral eigenbundle Chern source in the same fold.
- **Full arbitrary higher primitive alpha:** Not settled. Algebraic forms and even nonlinear component splitting are constructive source operations, but no universal theorem yet forces an alpha-selected codimension-p independent component with prescribed canonical period. This result is not relabeled the full Hodge conjecture.
- **Lean CI:** No Lean files changed this round; no new kernel run claimed. LaTeX source verified structurally after write.
- **Review:** Mathbox author self-audit with exact independent algebra checks; no external referee.
