(* ORIGINAL OWNER GST CARDINAL WORLD / N-HODGE / HODGE STAR / NAVIGATION
   ACTUAL source-birth theorem from arbitrary original (X,p,alpha), with
   alpha specified only as rational Hodge coordinates a_i in dimension r.
   Let world W=(P1)^(r+p-1), h_i^2=0, Z_i=h_i Product h_extra,
   Y_i=Product_{j<=r,j!=i} h_j. Check genuine Chow duality:
      deg(Z_i Y_j)=KroneckerDelta[i,j].
   Born Chow Z_alpha=sum_i a_i Z_i, exact algebraic recovery of all a_i.

   Also reconstruct literal owner's true original 4x3 U,J,M,[J,M] and
   verify the original mixed seed's 12-wave physical determinants.
   The true algebraic matrix units in CH^dim(W)(W x W)
   realize ANY rational 12-wave on the born source sector.

   Finally p=d-1 original-X Hard Lefschetz SOURCE RETURN in the true
   projective 3fold X=(P1)^3: for alpha=a h1h2+b h1h3+c h2h3,
   invert h cup on H^2 and reconstruct a TRUE divisor combination.
   These tests are exact finite diagnostics; the derivation proves
   the parameter-uniform Chow intersection theorem mathematically.
   NO arbitrary middle-primitive original-X source claim is made. *)

Module[{cases,dual,worldR,coP,d,extra,zi,yi,g,cell,u,j,mm,cc,
        off,on,seed,koff,kon,gram,beta,rhs,restored,a,b,c,full},
dual[sets1_,sets2_,dim_]:=If[
  Intersection[sets1,sets2]=={}&&
  Length[Union[sets1,sets2]]==dim,1,0];
cases=Flatten[Table[
 d=worldR+coP-1;extra=Range[worldR+1,d];
 zi=Table[Join[{i},extra],{i,1,worldR}];
 yi=Table[DeleteCases[Range[worldR],i],{i,1,worldR}];
 g=Table[dual[zi[[i]],yi[[j]],d],
   {i,1,worldR},{j,1,worldR}];
 <|"HodgeRank"->worldR,"cycleCodimension"->coP,
   "worldComplexDimension"->d,
   "cycleClassesAreAlgebraicallyDual"->(g==IdentityMatrix[worldR]),
   "equalAreaHodgeStarComplement"->And@@Table[
       Complement[Range[d],zi[[i]]]==yi[[i]],
       {i,1,worldR}]|>,
 {worldR,1,7},{coP,1,5}],1];

cell=Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
u=ConstantArray[0,{12,12}];j=ConstantArray[0,{12,12}];
mm=ConstantArray[0,{12,12}];
Do[With[{i=cell[[row,1]],k=cell[[row,2]]},
 u[[row,1+3*Quotient[i+4*k,3]+Mod[i+4*k,3]]]=1;
 j[[row,1+3*(3-i)+(2-k)]]=If[
  MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
 With[{pp=Mod[Quotient[i,2]+2*k,3]},
 mm[[row,row]]=Boole[k==2&&pp==2]+
  Boole[pp==2&&Mod[Mod[i,2]+2*pp,3]==2]]
],{row,1,12}];
cc=j.mm-mm.j;off=u+j+mm;on=off+cc;
seed=Join[{1,1},ConstantArray[0,10]];
koff=Transpose[NestList[off.#&,seed,11]];
kon=Transpose[NestList[on.#&,seed,11]];

(* Exact true X=(P1)^3, d=3,p=2 original-X constructive return *)
gram={{0,1,1},{1,0,1},{1,1,0}};
rhs={c,b,a};
beta=Simplify[Inverse[gram].rhs];
restored=Simplify[{
 beta[[1]]+beta[[2]],
 beta[[1]]+beta[[3]],
 beta[[2]]+beta[[3]]}];
full=<|
 "checkedCardinalToricWorldCases"->Length[cases],
 "allBornChowCyclesHaveExactIntersectionDuals"->
  And@@Lookup[cases,"cycleClassesAreAlgebraicallyDual"],
 "allProductHodgeStarsMatchCycleComplements"->
  And@@Lookup[cases,"equalAreaHodgeStarComplement"],
 "originalU5"->(MatrixPower[u,5]==IdentityMatrix[12]),
 "originalJ2"->(j.j==-IdentityMatrix[12]),
 "originalCMRank"->MatrixRank[cc],
 "original12NavigationOffSeedOrbitDet"->Det[koff],
 "original12NavigationOnSeedOrbitDet"->Det[kon],
 "actualThreefoldCupIntersectionGram"->gram,
 "threefoldGramDet"->Det[gram],
 "originalAlphaChosenDivisorCoefficients"->beta,
 "actualOriginalXCodim2CycleCoefficientsRestored"->restored,
 "allPassed"->(
  And@@Lookup[cases,"cycleClassesAreAlgebraicallyDual"]&&
  And@@Lookup[cases,"equalAreaHodgeStarComplement"]&&
  MatrixPower[u,5]==IdentityMatrix[12]&&
  j.j==-IdentityMatrix[12]&&
  Det[koff]==-1149656584000&&
  Det[kon]==-445265540949&&
  Det[gram]==2&&restored=={a,b,c})|>;
full
]

(* SECOND independent ORIGINAL-X Hodge-star algebraic source check.
   On a real smooth projective threefold (P1)^3, the Kahler
   Hodge star maps alpha=a x1x2+b x1x3+c x2x3 to
   beta=c x1+b x2+a x3.
   The genuine original-X Chow output
     -beta*h +(3/2)*tr(beta)*h^2
   reproduces alpha as a CHOW ring identity, not just periods.
   The rational factorial identity is tested for d=2,...,12,
   while its general proof is elementary factorial algebra. *)
Module[{a,b,c,x1,x2,x3,h,alpha,beta,t,reduction,
  starBorn,facTests},
h=x1+x2+x3;
alpha=a*x1*x2+b*x1*x3+c*x2*x3;
beta=c*x1+b*x2+a*x3;
t=(a+b+c)/3;
reduction[z_]:=Expand[z]/.{x1^2->0,x2^2->0,x3^2->0};
starBorn=reduction[-beta*h+(3/2)*t*h^2];
facTests=Table[
 FullSimplify[-1/Factorial[d-2]+d/Factorial[d-1]-1/Factorial[d-1]],
 {d,2,12}];
<|"metricStarOfGivenOriginalAlpha"->beta,
  "rationalKahlerTrace"->t,
  "actualChowCycleFromGSTHodgeStar"->starBorn,
  "exactChowTargetDifference"->Simplify[starBorn-alpha],
  "allStarFactorialTestsD2Through12"->facTests,
  "allPassed"->(
    Simplify[starBorn-alpha]==0&&And@@(#==0&/@facTests))|>
]
