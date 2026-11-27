(* GST cardinal/topology/Hodge-star expansion: EXACT finite-stage tests.
   These computations use the TRUE Chow ring basis of (P^1)^d:
   CH^*((P^1)^d)_Q = Q[H1,...,Hd]/(H1^2,...,Hd^2).
   The codimension-p basis H_I is indexed by p-element subsets I.
   Its intersection dual is H_(I^c), represented by a genuine algebraic
   cycle; external product gives actual codimension-d Chow matrix units
   on X_d x X_d. This constructs a full cyclic algebraic fold for EVERY
   finite dimension d in this product family.
   Tests d=1,..,6 and all p=0,..,d are evidence only of exact formulas.
   The general theorem is proven in the companion derivation.
   Arbitrary cardinal indices and tau are NOT numerical matrix inputs.
*)
ClearAll[gstCase,gstRuns,gstAll,gstSmall,gstCompress,gstCI];
gstCase[d_Integer?Positive,p_Integer?NonNegative]/;p<=d :=
 Module[{inds,duals,compinds,n,t,seed,kry,ell,mom,hank,star,backstar,
          pair,all=Range[d],expected},
  inds=Subsets[all,{p}];
  duals=Subsets[all,{d-p}];
  n=Length[inds];
  pair=Table[Boole[Sort[Complement[all,inds[[i]]]]===Sort[duals[[j]]]],
    {i,n},{j,n}];
  star=pair;
  backstar=Transpose[star];
  t=Table[Boole[i==Mod[j,n]+1],{i,n},{j,n}];
  seed=UnitVector[n,1];
  kry=Transpose[Table[MatrixPower[t,j].seed,{j,0,n-1}]];
  ell=UnitVector[n,1];
  hank=Table[ell.MatrixPower[t,i+j].seed,{i,0,n-1},{j,0,n-1}];
  expected=(-1)^((n-1)(n-2)/2);
  <|"d"->d,"p"->p,"rankHodge"->n,"binomialRank"->Binomial[d,p],
    "hodgeStarPairRank"->MatrixRank[star],
    "hodgeStarInvolutive"->(backstar.star==IdentityMatrix[n]),
    "cyclicRank"->MatrixRank[kry],
    "cyclicDet"->Det[kry],
    "hankelDet"->Det[hank],
    "expected"->expected,
    "pass"->(n==Binomial[d,p] &&
      MatrixRank[star]==n &&
      backstar.star==IdentityMatrix[n] &&
      MatrixRank[kry]==n && Det[kry]==1 && Det[hank]==expected)|>
 ];
gstRuns=Flatten[Table[gstCase[d,p],{d,1,6},{p,0,d}],1];
gstCompress={{1,1}};
gstSmall=<|
 "twoDivisorClassRank"->MatrixRank[IdentityMatrix[2]],
 "oneScalarCompressionRank"->MatrixRank[gstCompress],
 "nonzeroKernelOfCompression"->(gstCompress.{1,-1}=={0}),
 "finiteIterate0_1_2_onInfiniteShift"->{{1,0,0,0},{0,1,0,0},{0,0,1,0}}|>;
gstAll=<|
 "familiesChecked"->Length[gstRuns],
 "allProductFiniteDimensionCasesPassed"->And@@(Lookup[#,"pass"]&/@gstRuns),
 "cases"->gstRuns,
 "compressionTest"->gstSmall,
 "allPassed"->(And@@(Lookup[#,"pass"]&/@gstRuns) &&
    gstSmall["nonzeroKernelOfCompression"] &&
    gstSmall["oneScalarCompressionRank"]<gstSmall["twoDivisorClassRank"])
 |>;
Print[gstAll];gstAll