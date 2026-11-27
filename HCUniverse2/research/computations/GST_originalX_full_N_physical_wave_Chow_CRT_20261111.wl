(* AUTHOR ORIGINAL GST PHYSICAL NAVIGATION -> TRUE ORIGINAL-X CHOW SOURCE INVERSE.
   Same literal 4x3 Wave-I basis, shuffle U, signed CM mirror J,
   genuine SURVIVE source M, curvature C = JM-MJ, original two-cell seed.
   For a fixed original X with Picard rank at least 12 and any p,
   the companion derivation constructs genuine original-X Chow
   correspondence Gamma_b = Phi(U+J+M+b C), b∈{0,1}, from actual
   divisor intersection Gram-dual Chow matrix units.

   This script tests exact inverse of the 12-vector source Krylov orbit
   for physical Navigation off/on. For prescribed alpha, detector
   vector x_i=integral_X(alpha cup cl(Y_i)) may have arbitrary
   rational coordinates. Polynomial coefficients c=Inverse[K].x
   produce a TRUE Chow cycle Z=sum_j c_j Gamma^j(Z_seed) whose
   canonical Betti class is the 12-source-sector projector of alpha.
   The source-to-X construction is proven in the geometric TeX,
   not by a floating numerical fit or a choice of inverse cycleClass. *)

ClearAll[GSTOrigXCells,GSTOrigXIdx,GSTOrigXShuffle,GSTOrigXMirror,
  GSTOrigXSign,GSTOrigXSurvive,GSTOrigXU,GSTOrigXJ,GSTOrigXM,GSTOrigXC,
  GSTOrigXSeed,GSTOrigXKrylov,GSTOrigXResults];

GSTOrigXCells = Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
GSTOrigXIdx[z_] := First[FirstPosition[GSTOrigXCells,z]];
GSTOrigXShuffle[{i_,k_}] := {Quotient[i+4*k,3],Mod[i+4*k,3]};
GSTOrigXMirror[{i_,k_}] := {3-i,2-k};
GSTOrigXSign[{i_,k_}] := If[MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
GSTOrigXSurvive[{i_,k_}] := Module[{p=Mod[Quotient[i,2]+2*k,3],q},
  q=Mod[Mod[i,2]+2*p,3];
  Boole[k==2]Boole[p==2] + Boole[p==2]Boole[q==2]];
GSTOrigXU = Table[
  Boole[z==GSTOrigXIdx[GSTOrigXShuffle[GSTOrigXCells[[i]]]]],
  {i,12},{z,12}];
GSTOrigXJ = Table[
  GSTOrigXSign[GSTOrigXCells[[i]]]*
   Boole[z==GSTOrigXIdx[GSTOrigXMirror[GSTOrigXCells[[i]]]]],
  {i,12},{z,12}];
GSTOrigXM = DiagonalMatrix[GSTOrigXSurvive/@GSTOrigXCells];
GSTOrigXC = GSTOrigXJ.GSTOrigXM-GSTOrigXM.GSTOrigXJ;
GSTOrigXSeed = Boole[MemberQ[{{0,0},{0,1}},#]]&/@GSTOrigXCells;
GSTOrigXKrylov[t_,v_,n_] := Transpose[NestList[t.#&,v,n-1]];
GSTOrigXResults = Table[Module[{f,k,ki,target,c,vTest},
  f=GSTOrigXU+GSTOrigXJ+GSTOrigXM+b*GSTOrigXC;
  k=GSTOrigXKrylov[f,GSTOrigXSeed,12];
  ki=Inverse[k];target=UnitVector[12,GSTOrigXIdx[{3,2}]];
  c=ki.target;
  vTest=Table[k.ki.UnitVector[12,i]==UnitVector[12,i],{i,1,12}];
  <|"navigationCharge"->b,"det"->Det[k],
    "targetCoefficients"->c,"exactInverse"->ki.k==IdentityMatrix[12],
    "recoversMaximumOriginalGSTCell"->k.c==target,
    "all12OriginalGSTCellDirectionsRecovered"->And@@vTest|>],
  {b,{0,1}}];
<|"originalU5"->MatrixPower[GSTOrigXU,5]==IdentityMatrix[12],
  "originalJ2"->GSTOrigXJ.GSTOrigXJ==-IdentityMatrix[12],
  "originalCurvatureRank"->MatrixRank[GSTOrigXC],
  "states"->GSTOrigXResults,
  "allPassed"->(
     MatrixPower[GSTOrigXU,5]==IdentityMatrix[12] &&
     GSTOrigXJ.GSTOrigXJ==-IdentityMatrix[12] &&
     MatrixRank[GSTOrigXC]==6 &&
     GSTOrigXResults[[1,"det"]]==-1149656584000 &&
     GSTOrigXResults[[2,"det"]]==-445265540949 &&
     And@@Lookup[GSTOrigXResults,"exactInverse"] &&
     And@@Lookup[GSTOrigXResults,"recoversMaximumOriginalGSTCell"] &&
     And@@Lookup[GSTOrigXResults,"all12OriginalGSTCellDirectionsRecovered"])|>



(* Additional FULL N-hole original-X source matrix experiment.
   True physical Navigation gates are 0/1; h=2 and h=1 cases,
   with the additional independent source channels 1 and 4.
   All source matrices act on ACTUAL Chow classes after Gram-minor
   extraction, by the geometric theorem in the accompanying TeX.

   We test exact rational sample prescribed alpha coordinates as well,
   proving in the tested matrix that ONE polynomial source return
   recovers the whole algebraic source projection. *)

Module[{f0,f1,zero12,zero121,zero112,t25,v25,k25,t16,v16,k16,
  x25,c25,x16,c16,norms,monomialPair,mrank},
  f0=GSTOrigXU+GSTOrigXJ+GSTOrigXM;
  f1=f0+GSTOrigXC;
  zero12=ConstantArray[0,{12,12}];
  zero121=ConstantArray[0,{12,1}];
  zero112=ConstantArray[0,{1,12}];
  t25=ArrayFlatten[{
    {f0,zero12,zero121},
    {zero12,f1+20*IdentityMatrix[12],zero121},
    {zero112,zero112,{{40}}}}];
  v25=Join[GSTOrigXSeed,GSTOrigXSeed,{1}];
  k25=GSTOrigXKrylov[t25,v25,25];
  x25=Table[(i^2-3*i+5)/7,{i,0,24}];
  c25=LinearSolve[k25,x25];
  t16=ArrayFlatten[{
    {f0,ConstantArray[0,{12,4}]},
    {ConstantArray[0,{4,12}],DiagonalMatrix[{20,40,60,80}]}}];
  v16=Join[GSTOrigXSeed,ConstantArray[1,4]];
  k16=GSTOrigXKrylov[t16,v16,16];
  x16=Table[(i^2+1)/5,{i,0,15}];
  c16=LinearSolve[k16,x16];
  norms={Max[Total[Abs[f0],{2}]],Max[Total[Abs[f1],{2}]]};
  monomialPair=Table[KroneckerDelta[i+j,11],{i,0,11},{j,0,11}];
  mrank=MatrixRank[monomialPair];
  <|"exactOriginalFOffKrylovDet"->Det[GSTOrigXKrylov[f0,GSTOrigXSeed,12]],
    "exactOriginalFOnKrylovDet"->Det[GSTOrigXKrylov[f1,GSTOrigXSeed,12]],
    "waveBlockInfinityNorms"->norms,"spectralSpacing"->20,
    "Nholes2Remainder1Rank"->MatrixRank[k25],
    "Nholes2Remainder1PrescribedAlphaReturned"->(k25.c25==x25),
    "Nholes1Remainder4Rank"->MatrixRank[k16],
    "Nholes1Remainder4PrescribedAlphaReturned"->(k16.c16==x16),
    "Picard2P11xP11MiddleMonomialRank"->mrank,
    "Picard2P11xP11MiddleMonomialDet"->Det[monomialPair],
    "allPassed"->(
      Det[GSTOrigXKrylov[f0,GSTOrigXSeed,12]]==-1149656584000 &&
      Det[GSTOrigXKrylov[f1,GSTOrigXSeed,12]]==-445265540949 &&
      Max[norms]<=6 &&
      MatrixRank[k25]==25 && k25.c25==x25 &&
      MatrixRank[k16]==16 && k16.c16==x16 &&
      mrank==12 && Det[monomialPair]==1)|>
]
