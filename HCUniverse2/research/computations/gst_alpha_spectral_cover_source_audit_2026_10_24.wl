(* Exact Wolfram tests for GST alpha-selected polynomial spectral cover,
   source-neutral eigenmodule, two-sheet anti-deck and quadratic Chow leading term.
   Date: 2026-10-24. These tests are finite symbolic checks, not a
   Lean proof of the Hodge conjecture. *)
ClearAll[a, b, c, d, x, y, z, e, t, lam, s];
mat = {{a,b},{c,d}};
detIdentity = FullSimplify[mat.mat-(a+d)mat+(a d-b c)IdentityMatrix[2] ==
    ConstantArray[0,{2,2}]];
qe = {{1,e x},{e y,0}};
bb = 2 qe-IdentityMatrix[2];
disc=1+4e^2 x y;
defectIdentity = FullSimplify[qe.qe-qe == e^2 x y IdentityMatrix[2]];
spectralIdentity = FullSimplify[bb.bb == disc IdentityMatrix[2]];
charPoly = Factor[Det[lam IdentityMatrix[2]-qe]];
overQuadric = Factor[(disc/.y->(1-z^2)/x)/.e->1/10];
eplus = (IdentityMatrix[2]+bb/t)/2;
eminus=(IdentityMatrix[2]-bb/t)/2;
deckSwap=FullSimplify[(eplus/.t->-t)==eminus];
formalChi2 = Coefficient[Normal[Series[(Exp[s a]-Exp[s b])^2,{s,0,4}]],s,2];
chow2Identity = FullSimplify[formalChi2==(a-b)^2];
tests = <|
  "GenericCayleyHamilton"->detIdentity,
  "PolynomialIdempotentDefect"->defectIdentity,
  "SpectralDoubleWorldInvolution"->spectralIdentity,
  "DeckExchange"->deckSwap,
  "VirtualAntiEigenlineSquareCh2"->chow2Identity
|>;
Print["ASSERTIONS=",tests];
Print["ALL_TRUE=",And@@Values[tests]];
Print["CHAR_POLYNOMIAL=",charPoly];
Print["QUADRIC_DISCRIMINANT_EPS_1_OVER_10=",overQuadric];
Print["CH2_SQUARE_COEFFICIENT=",formalChi2];
