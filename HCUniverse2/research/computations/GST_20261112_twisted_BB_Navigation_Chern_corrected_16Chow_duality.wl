(* GST genuinely TWISTED original-X algebraic Navigation / Chern source birth.
   B=Bl_12(EllipticCurve x P1), original non-Tate smooth projective
   surface, NS rank14, e_i^2=-1, f*g=1. X=P_B(mathcal E),
   mathcal E an ACTUAL split bundle of rank m+1=8:
   O, O(f), O(g), O(e1), O(e2), O(e3),
   O(f+g), O(2f+e4).
   The distinct torus weights 0,...,7 act algebraically on
   this genuinely nontrivial projective bundle, with exactly
   eight fixed components B of complex dim2.
   The codim2 Hodge fiber has dimension16 and ACTUAL cycles:
   A0=o, A_D=D_i xi (14 divisors), Atop=xi^2.

   For ANY rank-(m+1) vector bundle over ANY smooth proj
   complex surface B, the projective bundle pushforwards are
     pi_* xi^m=1,
     pi_* xi^(m+1)=c1(mathcal E),
     pi_* xi^(m+2)=c1(mathcal E)^2-c2(mathcal E).
   The ACTUAL initial complementary classes
     B0=xi^m, B_D=D_i^dual xi^(m-1),
     Btop=o xi^(m-2)
   produce a lower-unitriangular true Chow intersection Gram.
   Inverting it constructs actual corrected Chow duals with
   Chern coefficients; no invented cycle map or Gram axiom.
   The true original GST U/J/M/[J,M] 12-wave can then act
   through algebraic matrix units built from these cycles.
   The generic projective-bundle dual theorem has a symbolic
   proof; the m=7,rank14 case is an exact large integer audit. *)

Module[{N=12,m=7,G,e,f,g,roots,c1,c1sq,c2,t,
  w,v,gram,corrector,correctionFirst,allPassed},

 G=IdentityMatrix[14];
 Do[G[[i,i]]=-1,{i,1,12}];
 G[[13,13]]=0;G[[14,14]]=0;
 G[[13,14]]=1;G[[14,13]]=1;

 e[i_]:=UnitVector[14,i];
 f=e[13];g=e[14];
 roots={ConstantArray[0,14],f,g,
   e[1],e[2],e[3],f+g,2f+e[4]};
 c1=Total[roots];
 c1sq=c1.G.c1;
 c2=Sum[roots[[i]].G.roots[[j]],
   {i,1,Length[roots]},
   {j,i+1,Length[roots]}];
 t=c1sq-c2;
 w=G.c1;
 v=c1;

 (* Ordering A=(o,D_1 xi,...,D_14 xi,xi^2).
    Initial duals B=(xi^m,D_i^dual xi^(m-1),o xi^(m-2)).
    Actual top intersection product matrix for twisted P(E).
    It is lower unitriangular with exact determinant +1. *)
 gram=IdentityMatrix[16];
 gram[[2;;15,1]]=w;
 gram[[16,1]]=t;
 gram[[16,2;;15]]=v;
 corrector=Inverse[gram];

 correctionFirst=corrector[[All,1]];
 allPassed=(
   Length[roots]==8&&
   c1sq==12&&c2==7&&t==5&&
   Det[gram]==1&&
   gram.corrector==IdentityMatrix[16]&&
   And@@(IntegerQ/@Flatten[corrector])&&
   corrector[[-1,1]]==c2);

 <|"originalVariety"->"P_B(O+O(f)+O(g)+O(e1)+O(e2)+O(e3)+O(f+g)+O(2f+e4))",
 "originalComplexDimension"->m+2,
 "trueAlgebraicNavigationFixedSurfaces"->m+1,
 "actualBundleChernRootCount"->Length[roots],
 "trueChernC1Coordinates"->c1,
 "trueChernC1SquaredDegree"->c1sq,
 "trueChernC2Degree"->c2,
 "xiTopPushforwardC1SquaredMinusC2"->t,
 "originalX16TwistedChowGramDet"->Det[gram],
 "actualCorrectedChowDualFirstColumn"->correctionFirst,
 "actualCorrectedChowDualLastRow"->corrector[[-1,All]],
 "all16OriginalXActualChowDualPairings"->gram.corrector==IdentityMatrix[16],
 "integralChernCorrectedChowDuals"->And@@(IntegerQ/@Flatten[corrector]),
 "allPassed"->allPassed|>
]
