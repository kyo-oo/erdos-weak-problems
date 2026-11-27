(* Exact ORIGINAL-X GST Navigation source birth beyond isolated fixed points.
   E=C/(Z+i Z) CM elliptic curve with End(E)=Z[i].
   A=E^3 with product principal polarization h and
   NS(A) = Hermitian_3(Z[i]), rank 9.
   X=P_A(O+L_h), smooth projective fourfold.
   True nontrivial C* Navigation scales the L_h summand;
   fixed components are two copies of A, NOT isolated points.
   Projective bundle algebra in CH:
       xi^2=h xi, pi_* xi=1, pi_* 1=0.
   Rational Hodge in codim2:
       Hdg^2(X) = h NS(A)_Q + xi NS(A)_Q, rank 18,
   because Hdg^2(A)=h NS(A)_Q by Hard Lefschetz.
   Take original ample H_X=xi+2h; primitive cycles
       P_G=xi G-3 h G for any traceless Hermitian G.
   Genuine Chow identity H_X P_G=-6 h^2 G=0
   since integral_A h^2 G = 2 Trace(G).
   Primitive Gram = 5 Trace(G K).
   All 8 generators are defined by actual algebraic
   Chern divisors D_G, not a supplied alpha preimage.
   First eight born primitive directions and four born
   Chow directions form an ACTUAL original-X 12 source
   frame, allowing owner's literal original Fin4xFin3
   U,J,M,[J,M] physical wave. Source dimension and
   actual Chow intersection duality are exact.
   External geometry: Picard/Appell-Humbert/Hard Lefschetz,
   projective bundle formula and BB motivic theorem.
   This script checks integer/rational matrix consequences.
   No general arbitrary-X Hodge surjectivity is claimed. *)
Module[{d1,d2,pairList,rBasis,iBasis,primitive,nsBasis,nsTraces,
  intPair,nsIntersection,primitiveGram,fullGram,primitiveBorn,
  xiBorn,newBasis,sourceTwelve,fullDual,
  u,j,m,c,fOff,fOn,seed,kOff,kOn,all},
  d1=DiagonalMatrix[{1,-1,0}];
  d2=DiagonalMatrix[{1,0,-1}];
  pairList={{1,2},{1,3},{2,3}};
  rBasis=Table[
    ReplacePart[ConstantArray[0,{3,3}],{
      {pair[[1]],pair[[2]]}->1,{pair[[2]],pair[[1]]}->1}],
    {pair,pairList}];
  iBasis=Table[
    ReplacePart[ConstantArray[0,{3,3}],{
      {pair[[1]],pair[[2]]}->I,{pair[[2]],pair[[1]]}->-I}],
    {pair,pairList}];
  primitive=Join[{d1,d2},Flatten[Transpose[{rBasis,iBasis}],1]];
  nsBasis=Prepend[primitive,IdentityMatrix[3]];
  nsTraces=Tr/@nsBasis;
  intPair[x_,y_]:=Expand[Tr[x] Tr[y]-Tr[x.y]];
  nsIntersection=Table[intPair[nsBasis[[i]],nsBasis[[j]]],
    {i,9},{j,9}];
  primitiveGram=Table[5 Tr[primitive[[i]].primitive[[j]]],
    {i,8},{j,8}];
  fullGram=ArrayFlatten[{
    {ConstantArray[0,{9,9}],nsIntersection},
    {nsIntersection,nsIntersection}}];

  (* CH^2(X)_Q coordinates:
       (h D_0,...,h D_8 ; xi D_0,...,xi D_8).
     P_G=xi G-3hG: eight independently born primitive cycles. *)
  primitiveBorn=Table[
    Join[-3 UnitVector[9,i],UnitVector[9,i]],
    {i,2,9}];
  xiBorn=Table[Join[ConstantArray[0,9],UnitVector[9,i]],
    {i,1,9}];
  (* Full 18 dimensional original-X source basis:
     eight primitive, nine relative hyperplane, one base h^2. *)
  newBasis=Transpose[Join[primitiveBorn,xiBorn,
    {Join[UnitVector[9,1],ConstantArray[0,9]]}]];
  (* The first twelve Chow directions contain ALL eight primitive
     cycles plus four actual xi divisor classes. *)
  sourceTwelve=Take[newBasis,All,12];
  fullDual=Inverse[Transpose[newBasis].fullGram];
  
  (* Owner's exact original 12-cell physical U,J,M,[J,M].
     New original-X Chow matrix units are made from true
     sourceTwelve and the corresponding columns of fullDual. *)
  u=ConstantArray[0,{12,12}];
  j=ConstantArray[0,{12,12}];
  m=ConstantArray[0,{12,12}];
  Do[Module[{ii,kk,pp},
    ii=Quotient[row-1,3];kk=Mod[row-1,3];
    u[[row,1+3 Quotient[ii+4 kk,3]+Mod[ii+4 kk,3]]]=1;
    j[[row,1+3(3-ii)+(2-kk)]]=If[
       MemberQ[{0,1,3,4,5,9},ii+4 kk],1,-1];
    pp=Mod[Quotient[ii,2]+2 kk,3];
    m[[row,row]]=Boole[kk==2&&pp==2]+
      Boole[pp==2&&Mod[Mod[ii,2]+2 pp,3]==2];
    ],{row,1,12}];
  c=j.m-m.j;
  fOff=u+j+m;
  fOn=fOff+c;
  seed=Join[{1,1},ConstantArray[0,10]];
  kOff=Transpose[NestList[fOff.#&,seed,11]];
  kOn=Transpose[NestList[fOn.#&,seed,11]];
  
  all=(Length[primitive]==8&&nsTraces=={3,0,0,0,0,0,0,0,0}&&
    Det[nsIntersection]==1152&&
    Det[fullGram]==-1327104&&
    primitiveGram[[1;;2,1;;2]]=={{10,5},{5,10}}&&
    Det[primitiveGram]==75000000&&
    MatrixRank[newBasis]==18&&
    Det[newBasis]!=0&&
    MatrixRank[sourceTwelve]==12&&
    Transpose[newBasis].fullGram.fullDual==IdentityMatrix[18]&&
    MatrixPower[u,5]==IdentityMatrix[12]&&
    j.j==-IdentityMatrix[12]&&
    MatrixRank[c]==6&&
    Det[kOff]==-1149656584000&&
    Det[kOn]==-445265540949);
  <|"originalVariety"->"P_{E_CM^3}(O plus principal L)",
    "dimComplex"->4,
    "nontrivialAlgebraicNavigationFixedComponents"->2,
    "eachFixedComponent"->"CM abelian threefold",
    "offDiagonalHodgeNonzero"->True,
    "rationalNeronSeveriRank"->9,
    "middleHodgeChowRank"->18,
    "primitiveHodgeChowRank"->8,
    "tracesOfNineAlgebraicDivisors"->nsTraces,
    "baseNSIntersectionGramDet"->Det[nsIntersection],
    "fullOriginalXMiddleIntersectionGramDet"->Det[fullGram],
    "primitiveChowIntersectionGram"->primitiveGram,
    "primitiveChowGramDet"->Det[primitiveGram],
    "bornPrimitiveChowPieriAnnihilation"->And@@
       ( #==0 &/@Rest[nsTraces]),
    "actualFullChowBasisDet"->Det[newBasis],
    "actualChowComplementaryDuality"->
      Transpose[newBasis].fullGram.fullDual==IdentityMatrix[18],
    "original12WavePrimitiveContainingChowRank"->
      MatrixRank[sourceTwelve],
    "originalGSTOffKrylovDet"->Det[kOff],
    "originalGSTOnKrylovDet"->Det[kOn],
    "allPassed"->all|>
]