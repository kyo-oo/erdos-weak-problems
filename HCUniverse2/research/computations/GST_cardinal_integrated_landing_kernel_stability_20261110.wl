(* GST cardinal-connected fold DESCENT gate: exact rational test.
   Input is a global GST signal V=Q^3 and a prescribed landing
   q:V->W=Q^2. The exact theorem is:
   a T:W->W satisfying q F = T q exists iff F(ker q) subset ker q,
   provided q is surjective.
   This gate is necessary but NOT sufficient for a genuine Chow
   correspondence on arbitrary original X.
   A surjective landing with an already given native Chow lift
   would be circular as a proof of the rational Hodge conjecture.
*)
ClearAll[q,ker,fg,fb,t,seed,kry,ell,hank,passed,result];
q={{1,0,0},{0,1,0}};
ker={0,0,1};
fg={{0,1,0},{1,0,0},{1,1,2}};
fb={{0,1,1},{1,0,0},{0,0,2}};
t={{0,1},{1,0}};
seed={1,0,0};ell={1,0};
kry=Transpose[{q.seed,q.fg.seed}];
hank=Table[ell.q.MatrixPower[fg,i+j].seed,
 {i,0,1},{j,0,1}];
passed=(q.fg==t.q)&&(Det[hank]==1)&&(q.fb.ker=={1,0});
result=<|"globalSourceDimension"->3,
 "hodgeTargetDimension"->2,
 "landingSurjective"->(MatrixRank[q]==2),
 "goodKernelPreserved"->(q.fg.ker=={0,0}),
 "goodHodgeFoldDescends"->(q.fg==t.q),
 "goodLandedOrbitRank"->MatrixRank[kry],
 "goodLandedHankelDet"->Det[hank],
 "badKernelLeakage"->q.fb.ker,
 "badFoldFailsToDescend"->(q.fb.ker!={0,0}),
 "badGlobalFoldFullRank"->(MatrixRank[fb]==3),
 "allPassed"->passed|>;
Print[result];result