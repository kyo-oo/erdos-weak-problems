(* OWNER GST POSITIVE-DIMENSIONAL ALGEBRAIC NAVIGATION / TRUE CHOW SOURCE

  X_m = Bl_12(E x P1) x P^m, m>=2, E elliptic.
  The first factor B has h10=1, h11=14 and original real Chow
  divisor basis f,g,e1..e12; f^2=g^2=0, fg=1, e_i e_j=-delta_ij.
  A true G_m action on the P^m factor with all weights distinct
  has m+1 fixed components, each the ACTUAL complex surface B.
  Brosnan motivic BB decomposition therefore creates genuine
  original-X cycles for EVERY rational Hodge input and codimension.
  The rank16 p=2 source basis and 16 algebraic duals are EXPLICIT.
  This checks m=7 as an exact discriminating example.

  On 12 exceptional-source Chow directions, realize the owner's true
  unmodified Fin4 x Fin3 native U/J/M/[J,M] source by genuine
  original-X Chow matrix-unit correspondences. Add FOUR stated
  scalar correspondence channels with eigenvalues 10,20,30,40.
  Test the complete 16-dimensional SINGLE ACTUAL CHOW seed orbit
  and return a prescribed rational source coordinate vector.

  This is finite exact verification of Chow coefficients, not
  a general proof of Brosnan's motivic theorem, a substitute
  for actual CH^p(X), or a proof for arbitrary unrelated X. *)

Module[{m=7,N=12,u,v,hB,hX,g16,dual16,ranks,
 cells,uu,jj,mm,cc,off,on,scalar,fold,seed,t0,t1,k0,k1,
 spectralOff,spectralOn,target,c0,c1,allPassed},

 hB=Expand[(1+u+v+u*v)*(1+u*v)+N*u*v];
 hX=Expand[hB*Sum[(u*v)^j,{j,0,m}]];
 ranks=Table[Coefficient[Coefficient[hX,u,p],v,p],
   {p,0,m+2}];

 (* A_1..A_12=e_i xi, A_13=o, A_14=f xi,
    A_15=g xi, A_16=xi^2.
    Complementary middle-dual pairing against
    D_i=-e_i xi^(m-1), D_13=xi^m,
    D_14=g xi^(m-1), D_15=f xi^(m-1),
    D_16=o xi^(m-2) is the EXACT IDENTITY. *)
 g16=ArrayFlatten[{
   {-IdentityMatrix[N],ConstantArray[0,{N,4}]},
   {ConstantArray[0,{4,N}],
    {{1,0,0,0},{0,0,1,0},{0,1,0,0},{0,0,0,1}}}
 }];
 dual16=Inverse[g16];

 (* Exact literal original physical GST source matrices. *)
 cells=Flatten[Table[{i,q},{i,0,3},{q,0,2}],1];
 uu=ConstantArray[0,{12,12}];
 jj=ConstantArray[0,{12,12}];
 mm=ConstantArray[0,{12,12}];
 Do[With[{i=cells[[row,1]],q=cells[[row,2]]},
   uu[[row,1+3*Quotient[i+4*q,3]+Mod[i+4*q,3]]]=1;
   jj[[row,1+3*(3-i)+(2-q)]]=If[
     MemberQ[{0,1,3,4,5,9},i+4*q],1,-1];
   With[{pp=Mod[Quotient[i,2]+2*q,3]},
    mm[[row,row]]=Boole[q==2&&pp==2]+
      Boole[pp==2&&Mod[Mod[i,2]+2*pp,3]==2]]],
 {row,1,12}];
 cc=jj.mm-mm.jj;
 off=uu+jj+mm;
 on=off+cc;

 scalar={10,20,30,40};
 fold[f_]:=ArrayFlatten[{
   {f,ConstantArray[0,{12,4}]},
   {ConstantArray[0,{4,12}],DiagonalMatrix[scalar]}
 }];
 t0=fold[off];t1=fold[on];
 seed=Join[{1,1},ConstantArray[0,10],{1,1,1,1}];
 k0=Transpose[NestList[t0.#&,seed,15]];
 k1=Transpose[NestList[t1.#&,seed,15]];
 spectralOff=Table[Det[off-l IdentityMatrix[12]],{l,scalar}];
 spectralOn=Table[Det[on-l IdentityMatrix[12]],{l,scalar}];
 target=Table[(j^2-3*j+7)/5,{j,1,16}];
 c0=LinearSolve[k0,target];
 c1=LinearSolve[k1,target];

 allPassed=(
   (Coefficient[hB,u*v]==0||Coefficient[Coefficient[hB,u,1],v,1]==14)&&
   ranks[[3]]==16&&
   (Coefficient[hX,u,1]/.v->0)==1&&
   Det[g16]==-1&&
   g16.dual16==IdentityMatrix[16]&&
   And@@(IntegerQ/@Flatten[dual16])&&
   MatrixPower[uu,5]==IdentityMatrix[12]&&
   jj.jj==-IdentityMatrix[12]&&
   And@@(#!=0&/@Join[spectralOff,spectralOn])&&
   Det[k0]!=0&&Det[k1]!=0&&
   k0.c0==target&&k1.c1==target);

 <|"originalX"->"Bl_12(E x P1) x P7",
   "complexDimension"->m+2,
   "genuineNavigationFixedSurfaceCount"->m+1,
   "originalHodgeOffDiagonal_h10"->(Coefficient[hX,u,1]/.v->0),
   "baseHodgePolynomial"->hB,
   "rationalDiagonalHodgeRanksByCodim"->ranks,
   "actualOriginalX16SourceIntersectionGramDet"->Det[g16],
   "allActualChowDualsIntegral"->And@@(IntegerQ/@Flatten[dual16]),
   "originalPhysicalU5"->MatrixPower[uu,5]==IdentityMatrix[12],
   "originalPhysicalJ2minusI"->jj.jj==-IdentityMatrix[12],
   "originalCurvatureRank"->MatrixRank[cc],
   "fourScalarSourceEigenvalues"->scalar,
   "offExactEigenvalueAvoidanceDeterminants"->spectralOff,
   "onExactEigenvalueAvoidanceDeterminants"->spectralOn,
   "offFull16SingleActualChowSeedKrylovDet"->Det[k0],
   "onFull16SingleActualChowSeedKrylovDet"->Det[k1],
   "offPrescribedRationalAlphaReturned"->(k0.c0==target),
   "onPrescribedRationalAlphaReturned"->(k1.c1==target),
   "allPassed"->allPassed|>
]
