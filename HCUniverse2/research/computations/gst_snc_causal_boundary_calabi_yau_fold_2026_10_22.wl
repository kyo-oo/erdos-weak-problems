(* GST all-dimensional higher-causal SNC -> smooth Calabi-Yau fold.
   Purely exact rational/integer checks; base date 2026-10-22.
   For n>=2, Y_n={Product x_i=0} in P^n; dual complex is
   the boundary of the n-simplex. The smooth general fibre is a
   degree n+1 hypersurface. The geometric Hodge and smoothing theorems
   are mathematical arguments, not claims derived from finite tests. *)

Clear[faces,bd,nn,kk,jj,ii,rr,cc,fullRanks,dimVec,
  homologyTable,chiSmooth,chiCentral,chiTable,q,deligneCentral,
  deligneIntersection,deligneChecks];

faces[n_,k_]:=Subsets[Range[n+1],{k+1}];
bd[n_,k_]:=Module[{r=faces[n,k-1],c=faces[n,k]},
 Table[Sum[If[Delete[c[[col]],{pos}]==r[[row]],
                 (-1)^(pos-1),0],{pos,1,k+1}],
   {row,1,Length[r]},{col,1,Length[c]}]];

homologyTable=Table[
 Module[{ranks=Table[MatrixRank[bd[n,k]],{k,1,n-1}],
   expected=Table[Binomial[n,k],{k,1,n-1}],
   dims=Table[Binomial[n+1,k+1],{k,0,n-1}],
   dd=Table[bd[n,k],{k,1,n-1}]},
  {n,ranks,expected,ranks===expected,
    And@@Table[
      dd[[k]].dd[[k+1]]==ConstantArray[0,
        {Length[faces[n,k-1]],Length[faces[n,k+1]]}],
      {k,1,n-2}],
    dims[[-1]]-ranks[[-1]],
    And@@Table[dims[[k+1]]-ranks[[k]]-ranks[[k+1]]==0,
      {k,1,n-2}]}
 ],{n,2,7}];

chiSmooth[n_]:=With[{d=n+1},
  d Sum[Binomial[n+1,k](-d)^(n-1-k),{k,0,n-1}]];
chiCentral[n_]:=n+1;
chiTable=Table[{n,chiSmooth[n],chiCentral[n],
  chiSmooth[n]-chiCentral[n]},{n,2,9}];

deligneCentral[n_]:=Expand[Sum[q^k,{k,0,n}]-(q-1)^n];
deligneIntersection[n_]:=Expand[
 Sum[(-1)^(k+1) Binomial[n+1,k] Sum[q^j,{j,0,n-k}],
  {k,1,n}]];
deligneChecks=Table[
 {n,TrueQ[deligneCentral[n]===deligneIntersection[n]],
  TrueQ[(deligneCentral[n]/.q->1)==chiCentral[n]]},
 {n,2,10}];

{"HomologyBoundaryRanksAndSquaredZero"->homologyTable,
 "ChainTestsPassed"->And@@Flatten[homologyTable[[All,{4,5,7}]]],
 "AllTopH1"->AllTrue[homologyTable[[All,6]],(#===1)&],
 "EulerSmoothCentralJump"->chiTable,
 "DeligneChecks"->deligneChecks,
 "DeligneChecksPassed"->And@@Flatten[deligneChecks[[All,{2,3}]]]}
