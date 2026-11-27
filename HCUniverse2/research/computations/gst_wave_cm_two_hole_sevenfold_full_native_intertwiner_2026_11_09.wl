(* GST Wave I+II+CM two-channel FULL geometric fold on CM elliptic sevenfold.
   Exact arithmetic. All source cycles are explicit divisor products D_I in
   CH^2(X)_Q, X=E1×...×E7 (pairwise nonisogenous CM elliptic curves).
   Matrix coefficients induce genuine CH^7(X×X)_Q correspondences via
   Gamma_{JI}=pr1^*(D_{I^c}) * pr2^*(D_J).
   Unlike the old sixfold projection, this quotient commutes with the
   ENTIRE original 24-dimensional wave fold (not merely nine prefix states).
   The rank-14 result only concerns the algebraic divisor-product primitive
   sector, not the full primitive Hodge fiber on arbitrary X. *)
Module[{states, fold, mirror, sign, mass, U, J, M, T, seed, Q2,
  piv2, Sel2, R2, B2, T24, Q14, B14, source24, K14, m=7,
  singles, pairs, sixes, L, A, B, P, pivCols, pivRows, Sel, D,
  Phi, G, geoSeed, geoKry, selRows, ell, h14, genChar, x},
 states=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
 fold[{c_,d_}]:={Quotient[c+4*d,3],Mod[c+4*d,3]};
 mirror[{c_,d_}]:={3-c,2-d};
 sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4*d],1,-1];
 mass[{c_,d_}]:=If[{c,d}=={1,1}||{c,d}=={2,2},1,
                         If[{c,d}=={3,2},2,0]];
 U=Table[Boole[states[[j]]==fold[states[[i]]]],
          {i,12},{j,12}];
 J=Table[sign[states[[i]]]*Boole[states[[j]]==mirror[states[[i]]]],
          {i,12},{j,12}];
 M=DiagonalMatrix[mass/@states]; T=U+J+M;
 seed=Boole[#=={0,0}||#=={0,1}]&/@states;

 (* 2-dimensional generalized eigenspace quotient from second wave channel.
    Q2 (T+10 I)=B2 Q2 on ALL 12 signals. *)
 Q2=NullSpace[Transpose[MatrixPower[T-2*IdentityMatrix[12],2]]];
 piv2={};
 Do[If[MatrixRank[Q2[[All,Append[piv2,i]]]]>Length[piv2],
       AppendTo[piv2,i]],{i,1,12}];
 Sel2=Transpose[UnitVector[12,#]&/@piv2];
 R2=Sel2.Inverse[Q2[[All,piv2]]];
 B2=Q2.(T+10*IdentityMatrix[12]).R2;
 T24=ArrayFlatten[{{T,ConstantArray[0,{12,12}]},
                    {ConstantArray[0,{12,12}],T+10*IdentityMatrix[12]}}];
 Q14=ArrayFlatten[{{IdentityMatrix[12],ConstantArray[0,{12,12}]},
                    {ConstantArray[0,{2,12}],Q2}}];
 B14=ArrayFlatten[{{T,ConstantArray[0,{12,2}]},
                    {ConstantArray[0,{2,12}],B2}}];
 source24=Join[seed,seed];
 K14=Transpose[NestList[B14.#&,Q14.source24,13]];

 (* Geometrically true hard-Lefschetz correction at codim2 on E^7:
    P_prim=I - L(L^5)^{-1}L^4.
    Each d_i^2=0, ∫X d1...d7=1. *)
 singles=Subsets[Range[m],{1}];
 pairs=Subsets[Range[m],{2}];
 sixes=Subsets[Range[m],{m-1}];
 L=Table[If[SubsetQ[pairs[[i]],singles[[j]]],1,0],
         {i,Length[pairs]},{j,Length[singles]}];
 A=Table[If[SubsetQ[sixes[[i]],pairs[[j]]],24,0],
         {i,Length[sixes]},{j,Length[pairs]}];
 B=Table[If[SubsetQ[sixes[[i]],singles[[j]]],120,0],
         {i,Length[sixes]},{j,Length[singles]}];
 P=IdentityMatrix[Length[pairs]]-L.Inverse[B].A;
 pivCols={};
 Do[If[MatrixRank[P[[All,Append[pivCols,i]]]]>Length[pivCols],
       AppendTo[pivCols,i]],{i,1,Length[pairs]}];
 K=P[[All,pivCols]];
 pivRows={};
 Do[If[MatrixRank[K[[Append[pivRows,i],All]]]>Length[pivRows],
       AppendTo[pivRows,i]],{i,1,Length[pairs]}];
 Sel=UnitVector[21,#]&/@pivRows;
 D=Inverse[K[[pivRows,All]]].Sel;

 (* ALL-WAVE exact Chow and whole Betti operator commuting square. *)
 Phi=K.Q14;
 G=K.B14.D;
 geoSeed=Phi.source24;
 geoKry=Transpose[NestList[G.#&,geoSeed,13]];
 selRows={};
 Do[If[MatrixRank[geoKry[[Append[selRows,i],All]]]>Length[selRows],
       AppendTo[selRows,i]],{i,1,21}];
 ell=Inverse[geoKry[[selRows,All]]][[14]].(UnitVector[21,#]&/@selRows);
 h14=Table[ell.Nest[G.#&,geoSeed,i+j],{i,0,13},{j,0,13}];

 <|
   "waveAll24Dimensions"->Dimensions[T24],
   "waveQuotientRank"->MatrixRank[Q14],
   "waveAll24Intertwine"->(Q14.T24==B14.Q14),
   "waveQuotientKrylovRank"->MatrixRank[K14],
   "waveKrylov14Determinant"->Det[K14],
   "complexDimension"->m,
   "codimTwoDivisorCycleCount"->Length[pairs],
   "primitiveRank"->MatrixRank[P],
   "primitiveIdempotent"->(P.P==P),
   "primitiveTestZero"->(A.P==ConstantArray[0,{7,21}]),
   "nativeChowDualIdentity"->(D.K==IdentityMatrix[14]),
   "full24WaveToChowIntertwine"->(G.Phi==Phi.T24),
   "nativeFoldPrimitive"->(A.G==ConstantArray[0,{7,21}]),
   "geometricWaveOrbitRank"->MatrixRank[geoKry],
   "rationalChowOperator"->AllTrue[Flatten[G],Element[#,Rationals]&],
   "hankelAntiTriangular"->And@@Flatten[
     Table[If[i+j<13,h14[[i+1,j+1]]==0,
       If[i+j==13,h14[[i+1,j+1]]==1,True]],
       {i,0,13},{j,0,13}]],
   "geometricMomentDeterminant"->Det[h14]
 |>
]
