Module[{g,s,pm,stable,reach,step,reflected,cases=0,failures={},firstFailure,
 density,physical,physicalChecks,q,u,b,proj,k,v,w,r,coef,extract,cmat,lt,tt,typedChecks,oneSidedMap,rhs,aug},
 step[mask_] := Fold[BitOr,mask,Flatten[Table[
   If[BitAnd[mask,2^i]!=0 && BitAnd[g,2^(3i+j)]!=0,2^j,0],
   {i,0,2},{j,0,2}]]];
 Do[
  stable=Select[Range[0,7],Function[pm,
    And@@Flatten[Table[
      !(BitAnd[pm,2^i]!=0 && BitAnd[g,2^(3i+j)]!=0) ||
         BitAnd[pm,2^j]!=0,{i,0,2},{j,0,2}]]]];
  Do[
   reach=FixedPoint[step,s];
   reflected=Fold[BitAnd,7,Select[stable,BitAnd[#,s]==s&]];
   cases++;
   If[reach!=reflected,AppendTo[failures,{g,s,reach,reflected}]],
   {s,0,7}],
  {g,0,511}];
 density[cc_,dd_]:={9,-35,-91}[[Mod[4dd+cc,3]+1]]-
  7{9,-35,-91}[[dd+1]]+{0,77,154,252}[[cc+1]]-
  3{0,77,154,252}[[Quotient[4dd+cc,3]+1]];
 physical=Table[density[cc,dd],{cc,0,3},{dd,0,2}];
 physicalChecks=And@@Flatten[Table[
   (density[cc,dd]>0)==(dd==2 && (cc==0 || cc==3)),
   {cc,0,3},{dd,0,2}]];
 q=DiagonalMatrix[{3,5,7}];u={{1,0},{1,1},{0,1}};
 b=Transpose[u].q.u;
 proj=u.Inverse[b].Transpose[u].q;k=IdentityMatrix[3]-proj;
 v={a,beta,c};w={d,e,f};r=k.v;coef=-Inverse[q];
 extract=Simplify[-coef.q.w];
 cmat={{1,0},{0,1},{0,0}};
 lt={{t11,t12},{t21,t22}};
 tt={{t11,t12,t13},{t21,t22,t23},{0,0,t33}};
 typedChecks={
  Simplify[cmat.lt==tt.cmat],
  Simplify[Transpose[r].q.u=={0,0}],
  Simplify[r.q.u.{{aa,bb},{cc,dd}}.Transpose[u].q.r==0],
  Simplify[(IdentityMatrix[3]-DiagonalMatrix[{1,1,0}]).
    DiagonalMatrix[{0,0,1}].DiagonalMatrix[{1,1,0}]==ConstantArray[0,{3,3}]],
  Simplify[DiagonalMatrix[{0,0,1}].DiagonalMatrix[{0,0,1}].
    DiagonalMatrix[{0,0,1}]==DiagonalMatrix[{0,0,1}]]
 };
 oneSidedMap=KroneckerProduct[IdentityMatrix[3],q.u];
 rhs=Flatten[Transpose[-q]];
 aug=Join[oneSidedMap,Transpose[{rhs}],2];
 <|"Version"->$Version,
 "SemanticReflectionGraphs"->512,"SeedSetsPerGraph"->8,
 "GraphSeedCases"->cases,"ReflectionFailures"->failures,
 "OntologicalPhysicalTable"->physical,
 "All12PositiveSectorChecks"->physicalChecks,
 "NativeLiftAndDefectChecks"->typedChecks,
 "FullFactorizationBilinearIdentity"->Simplify[v.q.coef.q.w==-v.q.w],
 "ExtractedNativeCoordinates"->extract,
 "FactorExtractionRecoversTarget"->Simplify[extract==w],
 "ProperFrameResidualEnergy"->Factor[r.q.r],
 "OneSidedCoefficientSystemRanks"->{MatrixRank[oneSidedMap],MatrixRank[aug]},
 "NoOneSidedFactorizationThroughProperFrame"->(MatrixRank[aug]>MatrixRank[oneSidedMap]),
 "K3DiagonalFactorCoefficient"->-1/21,
 "K3ExtractedNativeCoefficient"->Simplify[-(-1/21)*(21 a)],
 "K3ExtractedPositivePeriod"->Simplify[(21 a)*(-(-1/21)*(21 a))]
 |>
]
