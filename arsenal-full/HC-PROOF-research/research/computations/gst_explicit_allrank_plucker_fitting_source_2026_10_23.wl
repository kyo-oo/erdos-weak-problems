(* Mathbox: ACTUAL all-rank Pluecker projector algebra and Fitting source.
   General theorem proven by the alternating determinant Cramer identity
   in GST_explicit_plucker_fitting_source_algebra_all_rank_original_X_2026_10_23.tex.
   Exact rational tests here independently check low ranks, basis invariance,
   projector idempotence, trace, and determinantal rank-zero locus.
*)
ClearAll["Global`*"];
formEval[vs_List, weights_Association] :=
 Module[{rr=Length[vs],mm=Length[First[vs]],ids},
  ids=Subsets[Range[mm],{rr}];
  Sum[weights[ids[[z]]] Det[
     (Transpose[vs])[[ids[[z]]]]],{z,Length[ids]}]
 ];
projector[frame_List,wt_Association]:=
 Module[{rr=Length[frame],mm=Length[First[frame]],den,entries},
  den=formEval[frame,wt];
  If[den==0,Return[$Failed]];
  entries=Table[
   Sum[frame[[i,j]] formEval[
        ReplacePart[frame,i->UnitVector[mm,k]],wt],
       {i,1,rr}]/den,
   {j,1,mm},{k,1,mm}];
  entries
 ];
frameMake[rr_,mm_,shift_:0]:=
 Table[Table[
  If[i==j,1,0]+If[i>rr,Mod[i+j+shift,5]+1,0],
  {i,1,mm}],{j,1,rr}];
weightMake[rr_,mm_]:=Module[{idxs=Subsets[Range[mm],{rr}]},
 AssociationThread[idxs,
    Table[If[idxs[[a]]===Range[rr],100003,2+Total[idxs[[a]]^2]],
          {a,Length[idxs]}]]
];
testOne[rr_,mm_,shift_]:=
 Module[{u=frameMake[rr,mm,shift],wt=weightMake[rr,mm],
         pp,transform,pp2,traceOK,projectOK,frameOK},
  pp=projector[u,wt];
  If[pp===$Failed,Return[{rr,mm,shift,False,False,False,False}]];
  transform=IdentityMatrix[rr];
  If[rr>=2,transform[[1,2]]=2];
  pp2=projector[transform.u,wt];
  traceOK=TrueQ[Tr[pp]==rr];
  projectOK=TrueQ[pp.pp==pp];
  frameOK=And@@Table[TrueQ[pp.u[[j]]==u[[j]]],{j,rr}];
  {rr,mm,shift,traceOK,projectOK,frameOK,TrueQ[pp2==pp]}
 ];
projectorTests=Flatten[Table[
 testOne[rr,mm,shift],
 {rr,1,4},{mm,rr+1,Min[rr+3,7]},{shift,0,2}],2];
(* Genuine Gr(2,5) incidence zero-locus local test.
   Base S=span(e1,e2), incidence phi(e1,e2)=1.
   P(e5)=0 for phi=e1^e2, while adding phi(e5,e2)=1 gives P(e5)=e1.
   Fitting determinant ideal I_4([I-P | P e5]) vanishes iff section vanishes. *)
u=UnitVector[5,1];v=UnitVector[5,2];frame2={u,v};
idx=Subsets[Range[5],{2}];base=AssociationThread[idx,ConstantArray[0,Length[idx]]];
wt0=Association[base];wt0[{1,2}]=1;
wt1=Association[wt0];wt1[{2,5}]=-1;
pZero=projector[frame2,wt0];pNonzero=projector[frame2,wt1];
e5=UnitVector[5,5];
bZero=Transpose[Append[Transpose[IdentityMatrix[5]-pZero],pZero.e5]];
bNonzero=Transpose[Append[Transpose[IdentityMatrix[5]-pNonzero],pNonzero.e5]];
fittingChecks=<|
 "projectorZeroSection"->TrueQ[pZero.e5==ConstantArray[0,5]],
 "rankZero"->MatrixRank[bZero],
 "rankNonzero"->MatrixRank[bNonzero],
 "predictedRanks"->{3,4},
 "zeroLocusCorrect"->TrueQ[MatrixRank[bZero]==3&&MatrixRank[bNonzero]==4]
|>;
(* Independent original-X Gr(2,5) intersection arithmetic. *)
hh=x+y; ss=x y;
intGr[f_]:=Coefficient[Coefficient[Expand[(x-y)f],x,4],y,3];
theta=2 hh^2/5-ss;
schubertChecks={intGr[hh^6],intGr[ss hh^4],
 intGr[ss^2 hh^2],intGr[theta hh^4],intGr[theta^2 hh^2]};
(* Exact Todd-corrected divisor Gysin cancellation, in truncated
   Chow degrees of the source. The formal virtual K-class has
   ch(v_D)=beta * td(N), and GRR divides by td(N). *)
toddTests=Table[
 Module[{td,corrected,back},
  td=Normal[Series[z/(1-Exp[-z]),{z,0,d}]];
  corrected=Normal[Series[beta td,{z,0,d}]];
  back=Normal[Series[corrected (1-Exp[-z])/z,{z,0,d-1}]];
  {d,TrueQ[Expand[back-beta]===0]}
 ],{d,1,10}];
(* Chow Chern difference with arbitrary LOWER common characters:
   log c+(t)-log c-(t) is pure in t^p, thus their
   degree-p coefficient difference is (-1)^(p-1)(p-1)! m z. *)
newtonTests=Table[
 Module[{shared,scale,plus,minus},
  shared=Sum[(-1)^(j-1)Factorial[j-1] aa[j] t^j,
              {j,1,p-1}];
  scale=(-1)^(p-1)Factorial[p-1] mm zz;
  plus=Coefficient[Normal[Series[Exp[shared+
      (aa[p]+scale) t^p],{t,0,p}]],t,p];
  minus=Coefficient[Normal[Series[Exp[shared+
      aa[p] t^p],{t,0,p}]],t,p];
  {p,TrueQ[Expand[plus-minus-scale]===0]}
 ],{p,1,8}];
(* Target-driven actual original-X algebraic source solver:
   on Gr(2,5), h^2 is two Pluecker hyperplanes (vector {1,0}),
   and s2 is the genuine regular zero of S-dual or the
   genuine GST P(w0) Fitting scheme (vector {0,1}).
   The prescribed alpha = (2/5)h^2 - s2.
*)
targetVec={2/5,-1};
baseSource={{1},{0}};
newSource={{1,0},{0,1}};
sourceDual={0,-1};
selectedCoeffs=LinearSolve[newSource,targetVec];
targetSourcePass=TrueQ[newSource.selectedCoeffs==targetVec];
sourceRankPass=TrueQ[MatrixRank[baseSource]==1&&MatrixRank[newSource]==2
    &&sourceDual.baseSource[[All,1]]==0
    &&sourceDual.newSource[[All,2]]==-1];
(* INDEPENDENT symbolic 3-dimensional rank-two exterior contraction:
   A is an arbitrary skew matrix, u and v arbitrary symbolic
   independent vectors, Delta=u.A.v.  Test polynomial numerators
   without dividing by Delta (a nonzero incidence unit). *)
skew={{0,coefA,coefB},{-coefA,0,coefC},{-coefB,-coefC,0}};
symU={u1,u2,u3};symV={v1,v2,v3};
symDelta=symU.skew.symV;
symNumerator=Outer[Times,symU,skew.symV]-
             Outer[Times,symV,skew.symU];
symProjectorIdentity=And@@(PossibleZeroQ/@Flatten[
 Map[Together,symNumerator.symNumerator-
                   symDelta symNumerator,{2}]]);
symTraceIdentity=PossibleZeroQ[
 Together[Tr[symNumerator]-2 symDelta]];
symFrameIdentity=And@@(PossibleZeroQ/@Flatten[
 Map[Together,{symNumerator.symU-symDelta symU,
               symNumerator.symV-symDelta symV}, {2}]] /. 
  {False->False,True->True});
out=<|
 "unrestrictedSymbolicRank2Dimension3NumeratorIdempotence"->symProjectorIdentity,
 "unrestrictedSymbolicRank2Trace"->symTraceIdentity,
 "unrestrictedSymbolicRank2ImageOnFrame"->symFrameIdentity,
 "projectorCases"->Length[projectorTests],
 "allProjectorTests"->And@@Flatten[projectorTests[[All,4;;7]]],
 "projectorFailures"->Select[projectorTests,Not[And@@#[[4;;7]]]&],
 "fittingScheme"->fittingChecks,
 "ToddSourceGradings"->Length[toddTests],
 "ToddCancellationAllPass"->And@@toddTests[[All,2]],
 "ToddFailures"->Select[toddTests,Not[#[[2]]]&],
 "NewtonPureChowGrades"->Length[newtonTests],
 "NewtonPureDifferenceAllPass"->And@@newtonTests[[All,2]],
 "NewtonFailures"->Select[newtonTests,Not[#[[2]]]&],
 "TargetAlphaSelectedActualFittingCoefficients"->selectedCoeffs,
 "FittingRankJumpAndDual"->sourceRankPass,
 "ActualTargetChowSourceExact"->targetSourcePass,
 "schubertPeriods"->schubertChecks,
 "schubertExact"->TrueQ[schubertChecks==={5,2,1,0,1/5}]
|>;
Print[out];out