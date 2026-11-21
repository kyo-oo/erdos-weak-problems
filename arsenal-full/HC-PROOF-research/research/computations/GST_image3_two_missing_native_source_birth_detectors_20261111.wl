(* ORIGINAL GST Image-3 source birth: two exact missing-cycle detectors.
   The entire calculation uses the original 4 carry x 3 trit U/J/M
   and the original mixed seed. It identifies two rational row functionals
   annihilating the ENTIRE source-free U+J Krylov space, and shows that
   SURVIVE native wave birth releases BOTH within depths n=2,3.

   Exact tested:
   - source-free K0 has rank 10, with 2-dimensional left annihilator;
   - detectors are explicitly specified in physical cell coordinates;
   - each annihilates ALL 12 source-free orbit columns;
   - original source-on fold T1 reaches the two complementary modes at
     n=2,3 with detector minor det=-4;
   - original J/M curvature seed has detector (2,0).
   This is an information-cohomology result, not an original-X Chow lift.
*)
ClearAll[cells,ix,sh,mir,sgn,src,u,j,m,seed,t0,t1,
 k0,k1,dA,dB,dMat,probe,curv,sub,tests];
cells=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
ix[a_]:=First[FirstPosition[cells,a]];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mir[{c_,d_}]:={3-c,2-d};
sgn[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
src[{c_,d_}]:=Module[{mid=Mod[Quotient[c,2]+2d,3],fin},
 fin=Mod[Mod[c,2]+2mid,3];
 Boole[d==2]Boole[mid==2]+Boole[mid==2]Boole[fin==2]];
u=Table[Boole[k==ix[sh[cells[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cells[[i]]]*Boole[k==ix[mir[cells[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cells];
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
t0=u+j;t1=u+j+m;
k0=Transpose[NestList[t0.#&,seed,11]];
k1=Transpose[NestList[t1.#&,seed,11]];
dA={0,0,-1,0,0,0,-1,-1,-1,0,-1,1};
dB={-1,1,0,1,1,1,0,0,0,1,0,0};
dMat={dA,dB};
probe=Table[dMat.MatrixPower[t1,n].seed,{n,0,11}];
curv=j.m-m.j;
sub=Transpose[probe[[{3,4}]]];
tests=<|
 "sourceFreeRank"->MatrixRank[k0],
 "sourceOnRank"->MatrixRank[k1],
 "sourceFreeAnnulatorsIndependent"->(MatrixRank[dMat]==2),
 "bothDetectorsAnnihilateAllOffOrbit"->(dMat.k0==ConstantArray[0,{2,12}]),
 "firstFourOnOrbitProbes"->Take[probe,4],
 "probeAtDepth2and3"->sub,
 "detOfNewSourceBirth2x2"->Det[sub],
 "allMissingModesBornByDepth3"->(Det[sub]!=0),
 "curvatureSeedProbes"->dMat.curv.seed,
 "exactRankGrowth"->(MatrixRank[k0]==10&&MatrixRank[k1]==12),
 "allPassed"->(MatrixRank[k0]==10&&MatrixRank[k1]==12&&
   MatrixRank[dMat]==2&&dMat.k0==ConstantArray[0,{2,12}]&&
   Take[probe,4]=={{0,0},{0,0},{-2,0},{-8,2}}&&
   Det[sub]==-4&&dMat.curv.seed=={2,0})|>;
Print[tests];tests