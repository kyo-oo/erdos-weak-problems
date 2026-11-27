(* ORIGINAL-X, PRESCRIBED ALPHA, INFINITE GST WORLDS -- exact Hodge rationality gate.
   Original complex torus X_i=E_i x E_i, real T4 with coordinates
   x1,y1,x2,y2. Prescribed integral diagonal-cross algebraic
   2-class alpha= dx1 ^ dy2 + dx2 ^ dy1.
   Change first factor to E_tau, tau=u+i v (v>0), fixed E_i.
   Every X_tau is an ACTUAL smooth projective abelian surface.
   Analytic topology/diffeomorphism keeps alpha rational and flat.
   Hodge type (1,1) iff J_tau^T A J_tau=A.
   Original GST source U,J,M,[J,M] does not alter this Hodge gate.

   Independently test the 1-parameter positive-imaginary t slice,
   every rational cross-(1,1) class, and the native attempt of using
   Hodge projection P_t=(Id+pullback_J_t)/2.
   EXACT rational-symbolic arithmetic, no floating point.
   This is a counterexample to AUTOMATIC infinite Hodge-preserving
   deformations, NOT a Hodge conjecture counterexample; original
   alpha is algebraic at t=1.
*)

Module[{u,v,t,Juv,J1,Jfull,alpha,defect,sol,deriv,vec,
  Jt,Jtfull,allCross,rationalDefect,relations,hodgeProjected,
  sampleT,ratQ,samples,checks},
 Juv={{-u/v,-(u^2+v^2)/v},{1/v,u/v}};
 J1={{0,-1},{1,0}};
 Jfull=ArrayFlatten[{{Juv,ConstantArray[0,{2,2}]},
                      {ConstantArray[0,{2,2}],J1}}];
 alpha={{0,0,0,1},{0,0,-1,0},{0,1,0,0},{-1,0,0,0}};
 defect=FullSimplify[Transpose[Jfull].alpha.Jfull-alpha,
                     Assumptions->v>0];
 sol=Reduce[v>0 && And@@Thread[Flatten[defect]==0],
            {u,v},Reals];
 deriv=Simplify[{D[defect,u],D[defect,v]}/.{u->0,v->1}];
 
 Jt={{0,-t},{1/t,0}};
 Jtfull=ArrayFlatten[{{Jt,ConstantArray[0,{2,2}]},
                       {ConstantArray[0,{2,2}],J1}}];
 allCross=ConstantArray[0,{4,4}];
 allCross[[1,3]]=a;allCross[[3,1]]=-a;
 allCross[[1,4]]=b;allCross[[4,1]]=-b;
 allCross[[2,3]]=c;allCross[[3,2]]=-c;
 allCross[[2,4]]=d;allCross[[4,2]]=-d;
 rationalDefect=FullSimplify[Transpose[Jtfull].allCross.Jtfull-allCross];
 relations=Solve[And@@Thread[Flatten[rationalDefect]==0],{c,d}];
 hodgeProjected=FullSimplify[
   (alpha+Transpose[Jtfull].alpha.Jtfull)/2];
 ratQ[x_]:= IntegerQ[x] || Head[x]===Rational;
 sampleT={1,2,3/2,Sqrt[2],GoldenRatio};
 samples=Table[
   <|"t"->s,
     "projected12"->Simplify[hodgeProjected[[1,4]]/.t->s],
     "projected23"->Simplify[hodgeProjected[[2,3]]/.t->s],
     "exactRationalCoefficients"->(ratQ[Simplify[hodgeProjected[[1,4]]/.t->s]] &&
                                   ratQ[Simplify[hodgeProjected[[2,3]]/.t->s]])|>,
   {s,sampleT}];
 checks={
   FullSimplify[Jfull.Jfull,Assumptions->v>0]==-IdentityMatrix[4],
   sol===(u==0&&v==1),
   MatrixRank[Transpose[Flatten /@ deriv]]==2,
   FullSimplify[Transpose[Jtfull].hodgeProjected.Jtfull-hodgeProjected]
     ==ConstantArray[0,{4,4}],
   FullSimplify[hodgeProjected[[1,4]]-(1+1/t)/2]===0,
   FullSimplify[hodgeProjected[[3,2]]-(1+t)/2]===0,
   (c/.First[relations])===-b*t && (d/.First[relations])===a*t,
   Lookup[samples,"exactRationalCoefficients"]==={True,True,True,False,False}
 };
 <|"originalX"->"E_i x E_i",
   "allFibersSmoothProjective"->True,
   "givenIntegralPrescribedCrossClass"->alpha,
   "generalTauHodgeDefect"->defect,
   "prescribedAlphaHodgeLocus"->sol,
   "infinitesimalHodgeObstructionRank"->MatrixRank[Transpose[Flatten /@ deriv]],
   "allCrossHodgeClassConditions"->relations,
   "projectedHodgeClassAlwaysType11"->checks[[4]],
   "attemptedNativeHodgeProjection"->hodgeProjected,
   "sampleRationality"->samples,
   "allPassed"->And@@checks|>
]