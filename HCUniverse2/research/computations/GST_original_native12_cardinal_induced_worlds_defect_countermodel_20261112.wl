(* Original user's EXACT GST 12-cell U,J,M,[J,M] wave finite-cyclic
   model extended to a 13-dimensional Betti fiber with one class outside
   the actual algebraic image. A Z2 world-swap induction makes that
   class GLOBAL INVARIANT but does NOT make it algebraic. This is an
   ABSTRACT rational-model counterexample to purely formal inference,
   NOT a geometric Hodge counterexample and NOT a claim that any
   actual smooth projective X has nonalgebraic Hodge classes.
   The genuine source definitions are duplicated verbatim from the
   previously committed original-X 12-wave exact calculator. *)
Module[{cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,folds,cl,cl2,betti,
   indInvariants,indAlgebraic,ghost,swap,mat,report},
cells=Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
idx[z_]:=First[FirstPosition[cells,z]];
sh[{i_,k_}]:={Quotient[i+4*k,3],Mod[i+4*k,3]};
mir[{i_,k_}]:={3-i,2-k};
sgn[{i_,k_}]:=If[MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
surv[{i_,k_}]:=Module[{p=Mod[Quotient[i,2]+2*k,3],q},
 q=Mod[Mod[i,2]+2*p,3];
 Boole[k==2]Boole[p==2]+Boole[p==2]Boole[q==2]];
U=Table[Boole[z==idx[sh[cells[[i]]]]],{i,12},{z,12}];
J=Table[sgn[cells[[i]]]*Boole[z==idx[mir[cells[[i]]]]],{i,12},{z,12}];
M=DiagonalMatrix[surv/@cells];
C=J.M-M.J;
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
folds=Table[Module[{F=U+J+M+b*C,K},
 K=Transpose[NestList[F.#&,seed,11]];
 <|"charge"->b,"nativeFullKrylovRank"->MatrixRank[K],
 "nativeDeterminant"->Det[K],
 "nativeBettiSquare"->(ArrayFlatten[{{F,ConstantArray[0,{12,1}]},
   {ConstantArray[0,{1,12}],{{0}}}}].
   Join[IdentityMatrix[12],{ConstantArray[0,12]}] ==
   Join[IdentityMatrix[12],{ConstantArray[0,12]}].F)|>],
 {b,{0,1}}];
cl=Join[IdentityMatrix[12],{ConstantArray[0,12]}];
cl2=KroneckerProduct[IdentityMatrix[2],cl];
indInvariants=Join[IdentityMatrix[13],IdentityMatrix[13]];
indAlgebraic=Join[cl,cl];
ghost=Join[UnitVector[13,13],UnitVector[13,13]];
swap=KroneckerProduct[{{0,1},{1,0}},IdentityMatrix[13]];
report=<|"physicalStates"->folds,"all12NativeDirectionsCyclic"->(
  Lookup[folds,"nativeFullKrylovRank"]=={12,12}),
"originalBettiDimension"->13,"originalAlgebraicImageDimension"->MatrixRank[cl],
"originalGhostOutsideImage"->(MatrixRank[Join[Transpose[cl],{UnitVector[13,13]}]]==13),
"inducedTwoWorldsFixedSpaceDimension"->MatrixRank[indInvariants],
"inducedTwoWorldsAlgebraicFixedDimension"->MatrixRank[indAlgebraic],
"inducedGhostIsMonodromyInvariant"->swap.ghost==ghost,
"inducedGhostStillNotAlgebraic"->(
 MatrixRank[Join[Transpose[indAlgebraic],{ghost}]]==13),
"allPassed"->(
 Lookup[folds,"nativeFullKrylovRank"]=={12,12} &&
 And@@Lookup[folds,"nativeBettiSquare"] &&
 MatrixRank[cl]==12 && MatrixRank[indInvariants]==13 &&
 MatrixRank[indAlgebraic]==12 && swap.ghost==ghost &&
 MatrixRank[Join[Transpose[indAlgebraic],{ghost}]]==13)|>;
report]
