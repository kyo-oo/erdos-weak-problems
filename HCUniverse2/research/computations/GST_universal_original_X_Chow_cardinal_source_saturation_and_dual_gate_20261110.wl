(* GST universal Chow source saturation / independent-dual necessity.
   Mathematical geometry:
   For ANY original smooth connected projective d-fold X, ample h,
   q=degree h^d, every actual Z in CH^p(X)_Q has actual correspondence
   Gamma_Z=pr1^*h^(d-p) . pr2^*Z / q.
   It acts as Gamma_Z(A)=ell_h(A) Z and Gamma_Z(h^p)=Z.
   Thus all such Gamma_Z form a cardinal-indexed orbit reaching every
   ALREADY ALGEBRAIC class. This does NOT establish the Hodge conjecture.
   All Gamma_Z share one readout ell_h, so any single finite linear
   combination of them + identity is I+w ell_h and its seed orbit
   has dimension <=2: a dual GST Hodge-star source is indispensable
   to compile a higher-rank ONE-fold orbit.

   The below exact matrices are test representations of these abstract
   identities. They are not newly computed canonical geometry on X.
*)
ClearAll[test,runs,ans];
test[r_Integer?Positive]:=Module[
 {seed=UnitVector[r,1], read=UnitVector[r,1],
  vectors,sourceOps,orbitFamily,oneFold,oldKry,duals,
  newFold,newKry,readLast,hank},
 vectors=IdentityMatrix[r];
 sourceOps=Table[Outer[Times,vectors[[i]],read],{i,1,r}];
 orbitFamily=Transpose[Table[sourceOps[[i]].seed,{i,1,r}]];
 oneFold=IdentityMatrix[r]+Total[If[r==1,sourceOps,Rest[sourceOps]]];
 oldKry=Transpose[NestList[oneFold.#&,seed,r-1]];
 duals=IdentityMatrix[r];
 newFold=Table[Boole[j==Mod[i,r]+1],{j,1,r},{i,1,r}];
 newKry=Transpose[NestList[newFold.#&,seed,r-1]];
 readLast=UnitVector[r,r];
 hank=Table[readLast.MatrixPower[newFold,i+j].seed,
   {i,0,r-1},{j,0,r-1}];
 <|"r"->r,
  "allCorrespondencesRecoverSource"->And@@Table[
    sourceOps[[i]].seed==vectors[[i]],{i,1,r}],
  "allActualSourcesSpanAlgebraicModel"->MatrixRank[orbitFamily],
  "oneCommonReadoutFoldOrbitRank"->MatrixRank[oldKry],
  "rankBoundTwo"->(MatrixRank[oldKry]<=2),
  "multiReadoutCyclicRank"->MatrixRank[newKry],
  "multiReadoutHankelDet"->Det[hank],
  "expectedHankelDet"->(-1)^(r(r-1)/2),
  "pass"->(MatrixRank[orbitFamily]==r &&
     MatrixRank[oldKry]<=2 && MatrixRank[newKry]==r &&
     Det[hank]==(-1)^(r(r-1)/2))|>
];
runs=Table[test[r],{r,1,8}];
ans=<|"ranksTested"->Length[runs],
 "cases"->(KeyTake[# ,{"r","allActualSourcesSpanAlgebraicModel","oneCommonReadoutFoldOrbitRank","multiReadoutCyclicRank","multiReadoutHankelDet","pass"}]&/@runs),
 "rankFourSingleFoldCannotBeFull"->(runs[[4]]["oneCommonReadoutFoldOrbitRank"]==2),
 "rankFourWithIndependentDuals"->(runs[[4]]["multiReadoutCyclicRank"]==4),
 "allPassed"->And@@(Lookup[#,"pass"]&/@runs)|>;
Print[ans];ans