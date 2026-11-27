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


(* Exact full-original TWELVE cell Physical Navigation polynomial spectral
   projectors: NO guessed operator, data inherited from source code above.
   The legitimate geometric meaning is a rational polynomial in an ACTUAL
   original-X rational Chow correspondence, when an independently
   constructed twelve-dimensional Chow source frame exists. *)
Module[{z,f0,f1,q0,q1,eg,pol0,pol1,p0,p1,id,offComp,onComp},
f0=GSTOrigXU+GSTOrigXJ+GSTOrigXM;
f1=f0+GSTOrigXC;
id=IdentityMatrix[12];
q0=Cancel[CharacteristicPolynomial[f0,z]/(z-2)^2];
q1=Cancel[CharacteristicPolynomial[f1,z]/(z*(z-4))];
eg=PolynomialExtendedGCD[q0,(z-2)^2,z];
pol0=PolynomialRemainder[Expand[eg[[2,1]]*q0],
 (z-2)^2*q0,z];
pol1=Expand[z*q1/(4*(q1/.z->4))];
p0=Sum[Coefficient[pol0,z,k] MatrixPower[f0,k],
  {k,0,Exponent[pol0,z]}];
p1=Sum[Coefficient[pol1,z,k] MatrixPower[f1,k],
  {k,0,Exponent[pol1,z]}];
offComp=id-p0;onComp=id-p1;
<|"offCharPoly"->Factor[CharacteristicPolynomial[f0,z]],
 "onCharPoly"->Factor[CharacteristicPolynomial[f1,z]],
 "offQat2"->(q0/.z->2),"onQat4"->(q1/.z->4),
 "offProjectorPolynomial"->pol0,
 "onProjectorPolynomial"->pol1,
 "offProjectorRank"->MatrixRank[p0],
 "onProjectorRank"->MatrixRank[p1],
 "offComplementRank"->MatrixRank[offComp],
 "onComplementRank"->MatrixRank[onComp],
 "offIdempotent"->p0.p0==p0,
 "onIdempotent"->p1.p1==p1,
 "offOrthogonalAlgebraicSplit"->p0.offComp==ConstantArray[0,{12,12}],
 "onOrthogonalAlgebraicSplit"->p1.onComp==ConstantArray[0,{12,12}],
 "offFourierNativeRelation"->MatrixPower[f0-2id,2].p0==ConstantArray[0,{12,12}],
 "onFourierNativeRelation"->(f1-4id).p1==ConstantArray[0,{12,12}],
 "allPassed"->(
  (q0/.z->2)==1192&&(q1/.z->4)==707131&&
  MatrixRank[p0]==2&&MatrixRank[p1]==1&&
  MatrixRank[offComp]==10&&MatrixRank[onComp]==11&&
  p0.p0==p0&&p1.p1==p1&&
  p0.offComp==ConstantArray[0,{12,12}]&&
  p1.onComp==ConstantArray[0,{12,12}]&&
  MatrixPower[f0-2id,2].p0==ConstantArray[0,{12,12}]&&
  (f1-4id).p1==ConstantArray[0,{12,12}])|>
]
