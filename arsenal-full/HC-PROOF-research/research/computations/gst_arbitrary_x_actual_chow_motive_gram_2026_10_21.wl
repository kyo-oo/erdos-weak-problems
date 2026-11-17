(* EXACT FINITE COEFFICIENT AUDIT for the arbitrary-X rational Chow correspondence theorem.
   Source: GST_arbitrary_X_bounded_Chow_specialization_source_birth_2026-10-21.tex.
   This verifies rational Gram and projector arithmetic, NOT scheme-level
   Chow push-pull and NOT the universal rational Hodge conjecture. *)
ClearAll[g,c,v,old,w,sigma,q,full,schur];
g={{4,2,1},{2,6,3},{1,3,5}};
c={{1,0},{0,1},{0,0}};
old=FullSimplify[c.Inverse[Transpose[c].g.c].Transpose[c].g];
v={0,0,1};
w=FullSimplify[(IdentityMatrix[3]-old).v];
sigma=FullSimplify[w.g.w];
q=FullSimplify[Outer[Times,w,w.g]/sigma];
full=FullSimplify[old+q];
schur=FullSimplify[g[[3,3]]-
   g[[3,1;;2]].Inverse[g[[1;;2,1;;2]]].g[[1;;2,3]]];
assertion=And[
  sigma==7/2, schur==sigma,
  Det[g]==70, Det[g[[1;;2,1;;2]]]==20,
  q.q==q, old.old==old,
  old.q==ConstantArray[0,{3,3}],
  q.old==ConstantArray[0,{3,3}],
  full==IdentityMatrix[3]
];
If[!TrueQ[assertion],Print["FAIL"];Abort[]];
Print[<|"status"->"PASS","sourceGram"->g,"oldProjector"->old,
 "newPrimitiveSourceW"->w,"SchurNorm"->sigma,
 "newProjector"->q,"newDet"->Det[g],
 "orthogonalChowCompositionCoefficientsVerified"->True|>];