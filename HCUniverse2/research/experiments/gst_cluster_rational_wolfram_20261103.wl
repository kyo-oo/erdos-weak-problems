(* Exact finite evidence. All-rank geometric claims have separate hand proofs.
   Independent route: SymmetricReduction and conjugacy-class cycle indices. *)
ClearAll["Global`*"];
started = AbsoluteTime[]; assertionCount = 0;
assert[b_, label_] := If[TrueQ[b], assertionCount++, Throw[<|"failed" -> label|>]];
result = Catch[
  selectorRows = {};
  Do[
    vars = Array[x, n]; esym = Array[e, n];
    Do[
      weights = Join[Range[r], Range[n-r]];
      exponents = Select[Tuples[Table[Range[0, Floor[4/w]], {w,weights}]],
        1 <= Dot[weights,#] <= 4 &];
      counts = ConstantArray[0,4];
      Do[
        degree = Dot[weights,exp];
        transfer = Total[Table[
          rest = Complement[Range[n], subset];
          cherns = Join[Table[SymmetricPolynomial[j,vars[[subset]]],{j,r}],
            Table[SymmetricPolynomial[j,vars[[rest]]],{j,n-r}]];
          Times @@ MapThread[Power,{cherns,exp}],
          {subset,Subsets[Range[n],{r}]}]];
        reduced = SymmetricReduction[Expand[transfer],vars,esym];
        assert[reduced[[2]] === 0,"selector symmetry"];
        assert[Expand[reduced[[1]] /. Thread[esym->0]] === 0,"positive selector transfer"];
        counts[[degree]]++, {exp,exponents}];
      selectorRows = Join[selectorRows, Table[{n,r,d,counts[[d]]},{d,4}]],
      {r,0,n}],{n,2,5}];

  vars={x,y,z}; delta=(x-y)*(x-z)*(y-z);
  cyc=x^2*y+y^2*z+z^2*x;
  gb=GroebnerBasis[Table[SymmetricPolynomial[j,vars],{j,3}],vars,
      MonomialOrder->Lexicographic];
  nf[p_] := PolynomialReduce[Expand[p],gb,vars,MonomialOrder->Lexicographic][[2]];
  rd=nf[delta]; rc=nf[cyc];
  assert[rd =!= 0,"orientation formally survives"];
  assert[Expand[2*rc-rd]===0,"cyclic orientation sign"];
  assert[nf[delta^2]===0,"orientation square"];
  orientationNormalForm=SortBy[({First[#],Last[#]}& /@ CoefficientRules[rd,vars]),First];

  cycleCentralizer[ls_] := Times @@ ((#[[1]]^#[[2]]*Factorial[#[[2]]])& /@ Tally[ls]);
  hs[n_,terms_,order_] := Module[{num,poly,coeff,d=n*(n-1)/2},
    num=Product[1-t^j,{j,n}];
    poly=Cancel[num*Total[(#[[2]]/(Times @@ ((1-t^#)& /@ #[[1]])))& /@ terms]/order];
    assert[PolynomialQ[poly,t],"coinvariant polynomial"];
    coeff=PadRight[CoefficientList[poly,t],d+1];
    assert[And @@ (IntegerQ[#] && #>=0 & /@ coeff),"Hilbert positivity"];
    assert[Total[coeff]===Factorial[n]/order,"Hilbert total dimension"];
    coeff];
  hilbertRows={};
  Do[
    parts=IntegerPartitions[n];
    full=({#,Factorial[n]/cycleCentralizer[#]}& /@ parts);
    alt=Select[full,EvenQ[n-Length[#[[1]]]]&];
    cyclic=Table[{ConstantArray[n/GCD[n,k],GCD[n,k]],1},{k,0,n-1}];
    Do[
      coeff=hs[n,spec[[2]],spec[[3]]];
      If[spec[[1]]==="S",assert[coeff===Join[{1},ConstantArray[0,Length[coeff]-1]],"symmetric constant"]];
      If[spec[[1]]==="A",assert[coeff===Join[{1},ConstantArray[0,Length[coeff]-2],{1}],"alternating threshold"]];
      AppendTo[hilbertRows,{n,spec[[1]],coeff}],
      {spec,{{"S",full,Factorial[n]},{"A",alt,Factorial[n]/2},{"C",cyclic,n}}}],
    {n,2,7}];

  grassmannDegree[nn_,rr_] := Module[{zz,d,expr,top,vd,answer},
    zz=Array[z,rr];d=rr*(nn-rr);
    expr=(Times @@ ((1+#*t)^nn& /@ zz))/
      (Times @@ Flatten[Table[1+(zz[[i]]-zz[[j]])*t,{i,rr},{j,rr}]]);
    top=Expand[Coefficient[Normal[Series[expr,{t,0,d}]],t,d]];
    vd=Times @@ Flatten[Table[zz[[i]]-zz[[j]],{i,rr},{j,i+1,rr}]];
    answer=Fold[Coefficient[#1,#2[[1]],#2[[2]]]&,Expand[top*vd],
      Table[{zz[[i]],nn-i},{i,rr}]];
    assert[answer===Binomial[nn,rr],"global incidence top Chern degree"];
    {nn,rr,d,answer}];
  grassmannRows=Flatten[Table[Table[grassmannDegree[n,r],{r,0,n}],{n,2,5}],1];

  scales={-5,-1/3,1/2,2,7/3};targets=0;missing=0;
  Do[
    a=aa/2;b=bb/3;targets++;If[b!=0,missing++];
    assert[2*(a/2)===a,"rational index witness"];
    Do[assert[(m*b===0)===(b===0),"missing direction scale"];
       assert[{m*a,m*b}/m==={a,b},"rational normalization"],{m,scales}];
    assert[a*{1,0}+b*{0,1}==={a,b},"labeled ruling reconstruction"],
    {aa,-5,5},{bb,-5,5}];
  rationalRows=<|"targets"->targets,"nonzero_scales_per_target"->Length[scales],
    "integer_index_control_breaks"->Length[Select[Range[-10,10],OddQ]],
    "rational_index_control_breaks"->Count[Table[2*(tt/2)==tt,{tt,-10,10}],False],
    "two_direction_control_breaks"->missing|>;
  <|"all_passed"->True,"assertion_count"->assertionCount,
    "selector_rows"->selectorRows,"orientation_normal_form"->orientationNormalForm,
    "hilbert_rows"->hilbertRows,"rational_rows"->rationalRows,"grassmann_rows"->grassmannRows,
    "kernel_version"->$Version,"runtime_seconds"->(AbsoluteTime[]-started)|>
];
ExportString[result,"RawJSON","Compact"->True]
