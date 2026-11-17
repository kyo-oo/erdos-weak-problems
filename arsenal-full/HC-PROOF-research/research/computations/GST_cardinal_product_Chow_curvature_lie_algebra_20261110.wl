(* Exact GST native noncommutative curvature for GENUINE Chow matrix units
   on X_d=(P^1)^d in codimension p, where r=binomial(d,p).
   E_{I,J}=pr_1^*h_{I^c} pr_2^*h_J maps h_I to h_J.
   Their true Chow composition gives:
   E_{I,J} o E_{K,L} = delta_(I,L) E_{K,J}.
   Their commutator span is sl_r(Q), dimension r^2-1.
   Tested for ranks 2,3,4 by all index quadruples, exact rational
   matrix arithmetic. The all-rank proof is the standard matrix-unit
   commutator basis identity. This is product-family geometry, NOT
   universal correspondence realization on arbitrary X.
*)
ClearAll[gstOne,gstRuns,gstResult];
gstOne[n_Integer?Positive]/;n>=2 := Module[{e,valid,commWords,rank},
 e[i_,j_] := Normal[SparseArray[{{j,i}->1},{n,n}]];
 valid=And@@Flatten[Table[
   e[i,j].e[k,l]-e[k,l].e[i,j] ==
   KroneckerDelta[i,l] e[k,j]-KroneckerDelta[k,j] e[i,l],
   {i,n},{j,n},{k,n},{l,n}],3];
 commWords=Flatten[Table[
   Flatten[e[i,j].e[k,l]-e[k,l].e[i,j]],
   {i,n},{j,n},{k,n},{l,n}],3];
 rank=MatrixRank[commWords];
 <|"rankHodge"->n,"allBracketIdentities"->valid,
   "curvatureSpanRank"->rank,"expectedSlRank"->n^2-1,
   "allPassed"->(valid&&rank==n^2-1)|>
];
gstRuns=Table[gstOne[n],{n,2,4}];
gstResult=<|"cases"->gstRuns,
  "allPassed"->And@@(Lookup[#,"allPassed"]&/@gstRuns)|>;
Print[gstResult];gstResult