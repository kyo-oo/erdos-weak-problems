(* OWNER'S THREE CARDINAL-WORLD IMAGES + HYPOTHESIS PROOF PART 1
   Exact discriminating computation on the specified original X=P1 x P1:
    - Rational Chow ring Q[H1,H2]/(H1^2,H2^2)
    - Original actual wave U fixed pair, CM J, SURVIVE M, commutator [J,M]
    - True equal-area real harmonic Hodge Star on H^2
    - Physical Navigation b=0 or b=1, exact original-X Chow matrix fold
    - Owner's Z=Z0+N(Z0), class of N(Z) as (T+T^2)class(Z0)
    - The cardinal-indexed world classes ell_n=n H1+(n^2+1) H2,
      whose image has rank 2 despite unbounded index sets.
   Finite rank tests do NOT establish uncountable coverage; the
   independent mathematical proof uses dim_Q H^2(P1xP1)=2.
*)

Module[{h1,h2,red,gram,star,U,J,M,C,F,seed,folds,starMetricR,
   world,symbolicWorldIdentity,worldRanks,pdfFold,alphaSymbolic,
   verifyNPlusN2,hankel},
red[z_]:=PolynomialRemainder[PolynomialRemainder[Expand[z],h1^2,h1],h2^2,h2];
gram={{0,1},{1,0}};
star={{0,1},{1,0}};
U=IdentityMatrix[2];
J={{0,1},{-1,0}};
M={{0,0},{0,2}};
C=J.M-M.J;
F[b_]:=U+J+M+b*C;
seed={1,0};
world[n_]:={n,n^2+1};
symbolicWorldIdentity=FullSimplify[world[n]==n*world[1]+(n-1)^2*world[0],Element[n,Integers]];
worldRanks=Table[<|"throughN"->m,"sourceRank"->MatrixRank[Table[world[n],{n,0,m}]]|>,{m,{0,1,2,3,10,30}}];
hankel[t_]:=Module[{k,orbit,ell,h},
 k=Transpose[{seed,t.seed}];ell=Last[Inverse[k]];orbit=NestList[t.#&,seed,2];
 h=Table[ell.orbit[[i+j+1]],{i,0,1},{j,0,1}];
 <|"matrix"->h,"det"->Det[h]|>];
folds=Table[Module[{t=F[b],k,coeff},
 k=Transpose[{seed,t.seed}];
 coeff=Simplify[Inverse[k].{a,q}];
 <|"navigationCharge"->b,"actualFold"->t,"krylovDet"->Det[k],
 "ownerTwoBirth"->seed+t.seed,
 "ownerNPlusN2Native"->t.(seed+t.seed),
 "ownerNPlusN2Operator"->(t+MatrixPower[t,2]).seed,
 "pdfIdentityVerified"->(t.(seed+t.seed)==(t+MatrixPower[t,2]).seed),
 "targetReturnCoefficients"->coeff,
 "targetReturned"->FullSimplify[k.coeff=={a,q}],
 "hankel"->hankel[t]|>],{b,{0,1}}];
starMetricR={{0,1/r},{r,0}};
<|"surface"->"P1 times P1",
  "ChowSquareRelations"->{red[h1^2],red[h2^2],red[h1*h2]},
  "ChowIntersectionGram"->gram,"ChowGramDet"->Det[gram],
  "equalAreaHodgeStar"->star,"starSquared"->star.star,
  "originalFixedPairJ"->J,"J2"->J.J,
  "originalFixedPairSurviveM"->M,
  "exactOriginalCMCurvature"->C,
  "exactCurvatureEquals2HodgeStar"->(C==2star),
  "unequalMetricStarMatchesOnlyAtEqualAreas"->Solve[Thread[Flatten[C]==Flatten[2starMetricR]],r],
  "originalPhysicalNavigationFolds"->folds,
  "cardinalStageWorldIdentityForAllIntegers"->symbolicWorldIdentity,
  "finiteRankDiscriminator"->worldRanks,
  "allPassed"->(
    Det[gram]==-1 && red[h1^2]==0 && red[h2^2]==0 &&
    star.star==IdentityMatrix[2] && J.J==-IdentityMatrix[2] &&
    C==2star && symbolicWorldIdentity &&
    And@@Lookup[folds,"pdfIdentityVerified"] &&
    And@@Lookup[folds,"targetReturned"] &&
    Lookup[folds,"krylovDet"]=={-1,1} &&
    And@@(Lookup[Lookup[folds,"hankel"],"det"]=={-1,-1}))|>
]
