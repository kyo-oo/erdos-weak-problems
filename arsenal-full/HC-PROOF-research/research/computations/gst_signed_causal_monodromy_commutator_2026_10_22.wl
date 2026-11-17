(* Symbolic exact signature-composition audit, GST 22 Oct 2026.
   Verifies graded commutator and signed purity, not geometric monodromy. *)
ClearAll[kk,pp,qq,aa,bb,rr,foldop,nilop,puregap,charge,comm];
foldop[x_,a_,b_]:={x[[1]]+a+b,x[[2]]+a,x[[3]]+a};
nilop[x_,r_]:={x[[1]],x[[2]]-r,x[[3]]-r};
puregap[x_]:=x[[2]]+x[[3]]-x[[1]];
charge[x_]:=x[[2]]-x[[3]];
comm=FullSimplify[nilop[foldop[{kk,pp,qq},aa,bb],rr]-
                  foldop[nilop[{kk,pp,qq},rr],aa,bb]];
{"commutator",comm,
 "purityDifference",FullSimplify[
    puregap[nilop[foldop[{kk,pp,qq},aa,bb],rr]]-
    puregap[{kk,pp,qq}]],
 "chargeDifference",FullSimplify[
    charge[nilop[foldop[{kk,pp,qq},aa,bb],rr]]-
    charge[{kk,pp,qq}]],
 "commutesExactly",comm=={0,0,0}}
