(* Exact GST higher-causal monodromy operator commutant experiment.
   Claim tested: one rational fixed-vector direction, n independent
   commuting endomorphisms for a single Jordan block of length n.
   Field: Q; n=2..8. No sampling/tolerances/seeds.
   Actual Chow algebraicity is NOT an assertion of these computations. *)

Clear[shift,centRank,n,mat,vars,eq,cm,tab,s,k,pows,flat,
 ellipticHodge,allPass,hd];
shift[n_Integer?Positive]:=Table[KroneckerDelta[j,i+1],{i,1,n},{j,1,n}];
centRank[n_Integer?Positive]:=Module[{s=shift[n],x,v,c},
  x=Array[xx,{n,n}];v=Flatten[x];
  c=Normal[CoefficientArrays[Flatten[x.s-s.x],v][[2]]];
  n^2-MatrixRank[c]
];
tab=Table[Module[{s=shift[n],powers,flat},
  powers=Table[If[k==0,IdentityMatrix[n],MatrixPower[s,k]],{k,0,n-1}];
  flat=Flatten/@powers;
  {n,n-MatrixRank[s],centRank[n],MatrixRank[flat],
   And@@(TrueQ[#.s==s.#]&/@powers),
   TrueQ[MatrixPower[s,n]==ConstantArray[0,{n,n}]]}
 ],{n,2,8}];
ellipticHodge={{0,-1},{1,0}};
hd=shift[2].ellipticHodge-ellipticHodge.shift[2];
allPass=And@@(Function[row,
  row[[2]]==1 && row[[3]]==row[[1]] &&
  row[[4]]==row[[1]] && TrueQ[row[[5]]] && TrueQ[row[[6]]]
 ]/@tab);

(* Full rank-m original-X rational cohomology factor tensored with
   the rank-n causal Picard-Fuchs monodromy Jordan subsystem.
   The monodromy operator on the tensor is I_m x J_n.
   Invariant vectors have rank m; invariant endomorphisms have rank m^2 n. *)
Clear[kronNil,commutantDimension,allXTensors];
kronNil[m_Integer?Positive,n_Integer?Positive]:=
  KroneckerProduct[IdentityMatrix[m],shift[n]];
commutantDimension[m_Integer?Positive,n_Integer?Positive]:=
 Module[{q,N=kronNil[m,n],v,C,d=m*n},
  q=Array[qv,{d,d}];v=Flatten[q];
  C=Normal[CoefficientArrays[Flatten[q.N-N.q],v][[2]]];
  d^2-MatrixRank[C]];
allXTensors=Flatten[Table[With[{op=kronNil[m,n]},
 {m,n,m*n,m*n-MatrixRank[op],commutantDimension[m,n],m^2*n}
 ],{m,1,3},{n,2,4}],1];
allXPass=And@@(
  (#[[4]]==#[[1]]&&#[[5]]==#[[6]])&/@allXTensors
);

{"JordanData(n,FixedDim,CentralizerDim,PowersRank,Commute,Nilpotent)"->tab,
 "AllPass"->allPass,
 "AllXTensorTests(m,n,totalDim,fixedDim,operatorDim,expected)"->allXTensors,
 "AllXPass"->allXPass,
 "EllipticJCommutatorWithComplexStructure"->hd,
 "EllipticJIsNotPureHodgeMorph"->TrueQ[hd!=ConstantArray[0,{2,2}]]}
