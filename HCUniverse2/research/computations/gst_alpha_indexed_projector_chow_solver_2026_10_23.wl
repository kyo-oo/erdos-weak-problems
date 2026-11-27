(* Exact GST source algebra: finite-idempotent polynomial identities,
   prescribed-alpha rational Chow source solver, and dual missing-
   geometry witness. These inputs are rational canonical Betti
   vectors of genuine Chow sources, not hypothetical classes.
   Mathematical theorem in GST_alpha_indexed_finite_pole_projector_source_algebra_2026_10_23.tex.
*)
ClearAll["Global`*"];
rationalSourceSolve[cols_List,target_List]:=Module[
 {mat,aug,rank,witness,solution,ns},
 mat=Transpose[cols];
 aug=Transpose[Append[cols,target]];
 rank=MatrixRank[mat];
 If[MatrixRank[aug]==rank,
   solution=LinearSolve[mat,target];
   <|"status"->"EXACT_CHOW",
     "coefficients"->solution,
     "verified"->TrueQ[mat.solution==target],
     "rank"->rank|>,
   ns=NullSpace[Transpose[mat]];
   witness=SelectFirst[ns,Not[PossibleZeroQ[#.target]]&];
   witness=witness/(witness.target);
   <|"status"->"MISSING_SOURCE",
     "dualWitness"->witness,
     "annihilatesExistingSources"->And@@(PossibleZeroQ /@ (Transpose[mat].witness)),
     "pairsWithTarget"->witness.target,
     "rank"->rank|>
 ]
];
(* Genuine algebraic source 1: Pluecker square on Gr(2,5).
   Its rational Betti coordinates in (h^2,s2) are (1,0). *)
h2={1,0};
(* Target prescribed before constructing the next source. *)
alpha={2/5,-1};
firstStage=rationalSourceSolve[{h2},alpha];
(* Genuine algebraic source 2: intrinsic tangent projective
   characteristic class pch2 = -(7/12)h^2 - s2.
   Its existing geometric source is independently established
   in GST_intrinsic_projective_curvature_tracezero_source_2026-10-23.tex. *)
pgl={-7/12,-1};
secondStage=rationalSourceSolve[{h2,pgl},alpha];
dual=firstStage["dualWitness"];
dualPgl=dual.pgl;
(* Polynomial matrix-scheme kernel: A_ij=x_i ell_j,
   incidence section s=sum_j ell_j x_j. In every n,
   A^2=s A and tr(A)=s. Seven exact independent checks. *)
polyChecks=Table[
 Module[{xv=Array[x,n],hv=Array[ell,n],numerator,s,z},
   numerator=Outer[Times,xv,hv];s=hv.xv;
   z=Map[Together,numerator.numerator-s numerator,{2}];
   {n,And@@(PossibleZeroQ/@Flatten[z]),
        PossibleZeroQ[Together[Tr[numerator]-s]]}],
 {n,2,8}];
(* An original curve X=P1:
   A/s defines algebraic q*O(-1) with ch1=-h.
   Solve arbitrary alpha=(3/2)h as (-3/2)[O(-1)]_ch1. *)
curveStage=rationalSourceSolve[{{-1}},{3/2}];
(* Native rank-one projective algebraic curvature:
   local image generator (1,u), dual normal (1,v),
   Grassmann connection omega=(v/(1+u v)) du.
   Curvature coefficient in du^dv orientation is
   -D[v/(1+u v),v] = -1/(1+u v)^2. *)
grassmannOmegaCoefficient=v/(1+u v);
grassmannCurvatureCoefficient=-D[grassmannOmegaCoefficient,v];
grassmannCurvatureCheck=TrueQ[
 FullSimplify[grassmannCurvatureCoefficient+
                             1/(1+u v)^2]==0];
(* The rational coordinate dual is an ACTUAL Hodge-type period:
   on Gr(2,5), psi = 5 theta h^2 is of bidegree (4,4).
   Schubert integration [xx^4 yy^3](xx-yy)F checks all pairings. *)
hGrass=xx+yy; sGrass=xx yy; thetaGrass=2 hGrass^2/5-sGrass;
pglGrass=-7 hGrass^2/12-sGrass;
psiGrass=5 thetaGrass hGrass^2;
schubertInt[f_]:=Coefficient[Coefficient[
  Expand[(xx-yy) f],xx,4],yy,3];
hodgeDualPairings={
 schubertInt[hGrass^2 psiGrass],
 schubertInt[thetaGrass psiGrass],
 schubertInt[pglGrass psiGrass]};
output=<|
 "firstStage"->firstStage,
 "dualWitnessPairsWithNewPGL"->dualPgl,
 "secondStage"->secondStage,
 "firstStageRankOne"->TrueQ[firstStage["rank"]==1],
 "PGLRankJump"->TrueQ[secondStage["rank"]==2],
 "exactSolution"->TrueQ[secondStage["coefficients"]=={59/60,1}],
 "actualCurveSolution"->curveStage,
 "actualRationalHodgeDualPairings"->hodgeDualPairings,
 "HodgeDualAllPass"->TrueQ[hodgeDualPairings==={0,1,1}],
 "algebraicGrassmannCurvatureCoefficient"->grassmannCurvatureCoefficient,
 "algebraicGrassmannCurvatureExact"->grassmannCurvatureCheck,
 "incidencePolynomialCases"->Length[polyChecks],
 "allIncidenceSchemesPass"->And@@Flatten[polyChecks[[All,2;;3]]],
 "incidenceFailures"->Select[polyChecks,Not[And@@#[[2;;3]]]&]
|>;
Print[output];output