(* GST cardinal-topology Hodge approximation + polarized residual-energy test.
   Mathematical theorem (proved separately for ANY finite rational Hodge
   fiber W with a rational positive-definite Hodge-Riemann pairing Q):
   Let A=im(cycleClass_X) rational subspace. Then
      closure_W_R(A_Q)=A_Q tensor_Q R,
      closure_W_R(A_Q) intersect W_Q=A_Q.
   Therefore ANY cohomologically convergent cardinal-indexed finite
   partial-sum net of ACTUAL algebraic cycle classes with a rational
   Hodge target has a FINITE algebraic representative. This supplies
   a valid alternative proof target but does NOT prove such approximating
   sources exist for arbitrary target alpha.

   The minimum rational residual energy equals the squared Q-norm
   of the Q-orthogonal complement of A. Exact finite experiment below
   tests Gram/Schur and energy descent as ACTUAL algebraic source
   directions are added, not a proof of universal source birth.
*)
ClearAll[Qmat,alpha,sourceMatrix,proj,energy,case,checks,gram,b,schur,ginv,runs,res];
Qmat={{3,1,0,0},{1,4,1,0},{0,1,5,1},{0,0,1,6}};
alpha={1,1,2,1};
sourceMatrix[k_Integer?Positive]:=Transpose[Table[UnitVector[4,i],{i,1,k}]];
proj[v_,bmat_] := Module[{g=Transpose[bmat].Qmat.bmat},
 bmat.Inverse[g].Transpose[bmat].Qmat.v];
energy[v_] := v.Qmat.v;
case[k_Integer?Positive] := Module[{bb=sourceMatrix[k],pp,rr},
 pp=proj[alpha,bb];rr=alpha-pp;
 <|"numberOfNativeSources"->k,
   "spanRank"->MatrixRank[bb],
   "rationalBestProjection"->pp,
   "rationalResidual"->rr,
   "minimumResidualEnergy"->energy[rr],
   "projectionOrthogonal"->(Transpose[bb].Qmat.rr==ConstantArray[0,k]),
   "rationalProjection"->And@@(MatchQ[#, _Integer | _Rational] & /@ pp)|>];
runs=Table[case[k],{k,1,4}];
b=sourceMatrix[2];
gram=Transpose[b].Qmat.b;
ginv=Inverse[gram];
schur=Qmat[[3,3]]-
 (Transpose[b].Qmat.UnitVector[4,3]).ginv.
 (Transpose[b].Qmat.UnitVector[4,3]);
res=<|
 "GramLeadingMinors"->Table[Det[Qmat[[1;;j,1;;j]]],{j,1,4}],
 "positiveRationalForm"->And@@Table[
     Det[Qmat[[1;;j,1;;j]]]>0,{j,1,4}],
 "rankGrowthSchurComplement"->schur,
 "rankGrowthIdentity"->(
   Det[Transpose[sourceMatrix[3]].Qmat.sourceMatrix[3]]==
     Det[gram]*schur),
 "sourceBirthSequence"->(KeyTake[# ,{
 "numberOfNativeSources","spanRank","minimumResidualEnergy",
 "projectionOrthogonal","rationalProjection"}]&/@runs),
 "strictEnergyDrop"->And@@Table[
   runs[[i]]["minimumResidualEnergy"] >
      runs[[i+1]]["minimumResidualEnergy"],{i,1,3}],
 "lastResidualZero"->(runs[[4]]["minimumResidualEnergy"]==0),
 "allPassed"->(And@@Table[Det[Qmat[[1;;j,1;;j]]]>0,{j,1,4}] &&
   Det[Transpose[sourceMatrix[3]].Qmat.sourceMatrix[3]]==Det[gram]*schur &&
   runs[[4]]["minimumResidualEnergy"]==0 &&
   And@@(Lookup[#,"projectionOrthogonal"]&/@runs) &&
   And@@(Lookup[#,"rationalProjection"]&/@runs) &&
   And@@Table[runs[[i]]["minimumResidualEnergy"] >
     runs[[i+1]]["minimumResidualEnergy"],{i,1,3}])
|>;
Print[res];res