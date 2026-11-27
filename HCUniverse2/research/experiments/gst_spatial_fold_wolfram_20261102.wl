(* Exact audit. Bitmask exterior algebra differs from Python's tuple basis.
   No finite run is a proof of the arbitrary-X Hodge conjecture. *)
ClearAll["Global`*"];
assertions = 0;
check[h_, tag_] := If[TrueQ[h], assertions++, Throw[<|"Failure" -> tag|>]];
timing = AbsoluteTiming[result = Catch[Module[
  {rotationRows = {}, exteriorRows = {}, causalRows = {}, variableRows = {},
   n, jj, uu, ui, ss, si, kk, gg, ee, minors, ds, basis, ambient, balanced,
   chargeRank, r, expected, js, ts, pp, lhs, rhs, before, after, edge,
   x, y, f, df, mat, coords, fields, nij, poly, test, z, a, j, p},
  Do[
    n = 2*s;
    jj = KroneckerProduct[IdentityMatrix[s], {{0,-1},{1,0}}];
    Do[
      uu = IdentityMatrix[n]; ui = IdentityMatrix[n];
      Do[
        ss = IdentityMatrix[n]; si = IdentityMatrix[n];
        ss[[Mod[k,n]+1,Mod[k+1,n]+1]] = k+1;
        si[[Mod[k,n]+1,Mod[k+1,n]+1]] = -k-1;
        uu = ss.uu; ui = ui.si,
        {k,0,variant}];
      kk = uu.jj.ui; gg = IdentityMatrix[n]+Transpose[kk].kk;
      ee = Transpose[kk].gg;
      check[kk.kk == -IdentityMatrix[n], "rotation square"];
      check[Transpose[ee] == -ee, "alternating"];
      check[Transpose[kk].ee.kk == ee && ee.kk == gg, "invariance and sign"];
      minors = Table[Det[gg[[1;;k,1;;k]]], {k,1,n}];
      check[And @@ Thread[minors > 0], "positive exact principal minors"];
      check[Abs[Det[kk-IdentityMatrix[n]]] == 2^s, "door determinant"];
      AppendTo[rotationRows, {s,variant,Det[gg],minors}],
      {variant,0,2}],
    {s,1,5}];
  Do[
    check[{{-1,-1},{1,-1}}.{y-x,-x-y} == 2*{x,y}, "doubled witness"];
    check[{{-1,-1},{1,-1}}.{(y-x)/2,-(x+y)/2} == {x,y}, "rational inverse"];
    check[And @@ (IntegerQ /@ {(y-x)/2,-(x+y)/2}) == EvenQ[x+y], "parity door"],
    {x,-4,4},{y,-4,4}];

  (* An association stores mask -> exact coefficient. *)
  clean[q_] := Select[q, # != 0 &];
  plus[qs___] := clean[Merge[{qs},Total]];
  scale[c_,q_] := clean[Map[c*# &,q]];
  one[j_] := <|2^j -> 1|>;
  bits[m_] := Select[Range[0,7], BitGet[m,#] == 1 &];
  wedge[q_,r_] := Module[{out=<||>,mask,sgn},
    KeyValueMap[Function[{u,c},KeyValueMap[Function[{v,d},
      If[BitAnd[u,v] == 0,
        mask=BitOr[u,v];
        sgn=(-1)^Total[Flatten[Outer[Boole[#1>#2] &,bits[u],bits[v]]]];
        AssociateTo[out,mask -> (Lookup[out,mask,0]+sgn*c*d)]]],r]],q];
    clean[out]];
  extProduct[qs_] := Fold[wedge,<|0 -> 1|>,qs];
  vectorRank[qs_] := Module[{masks=Union @@ (Keys /@ qs)},
    If[qs == {} || masks == {},0,MatrixRank[Table[Lookup[q,m,0],{q,qs},{m,masks}]]]];
  Do[
    ds=Table[wedge[one[2*j],one[2*j+1]],{j,0,s-1}];
    Do[
      AppendTo[ds,plus[wedge[plus[one[2*j],scale[-1,one[2*k]]],
          plus[one[2*j+1],scale[-1,one[2*k+1]]]],scale[-1,ds[[j+1]]],scale[-1,ds[[k+1]]]]];
      AppendTo[ds,plus[wedge[plus[one[2*j],one[2*k+1]],
          plus[one[2*j+1],scale[-1,one[2*k]]]],scale[-1,ds[[j+1]]],scale[-1,ds[[k+1]]]]],
      {j,0,s-1},{k,j+1,s-1}];
    basis={<|0 -> 1|>};
    Do[
      If[p>0,
        poly=Flatten[Table[wedge[q,t],{q,basis},{t,ds}],1];
        (* Keep a basis by independent MatrixRank increments. *)
        basis={};r=0;
        Do[If[vectorRank[Append[basis,q]]>r,AppendTo[basis,q];r++],{q,poly}]];
      balanced=Flatten[Table[extProduct[Join[
        (plus[one[2*#],scale[I,one[2*#+1]]] & /@ ii),
        (plus[one[2*#],scale[-I,one[2*#+1]]] & /@ jj2)]],
        {ii,Subsets[Range[0,s-1],{p}]},{jj2,Subsets[Range[0,s-1],{p}]}],1];
      expected=If[p<=s,Binomial[s,p]^2,0];
      check[vectorRank[balanced] == expected, "complex balanced basis"];
      check[Length[basis] == expected, "actual divisor products"];
      check[vectorRank[Join[basis,balanced]] == expected, "same complex subspace"];
      ambient=If[2*p<=2*s,Binomial[2*s,2*p],0];
      chargeRank=ambient-expected;
      AppendTo[exteriorRows,{s,p,ambient,chargeRank,Length[basis]}],
      {p,0,s+1}],
    {s,0,4}];

  m[n_,t_] := Table[Mod[(i+2)*(j+1)+t*(i-j+1),7]-3,{i,0,n-1},{j,0,n-1}];
  Do[
    js=Table[m[n,10+j],{j,0,len}];ts=Table[m[n,1+j],{j,0,len-1}];
    pp=Fold[#2.#1 &,IdentityMatrix[n],ts];
    lhs=Last[js].pp-pp.First[js];rhs=ConstantArray[0,{n,n}];
    Do[
      before=Fold[#2.#1 &,IdentityMatrix[n],Take[ts,j-1]];
      after=Fold[#2.#1 &,IdentityMatrix[n],Drop[ts,j]];
      edge=js[[j+1]].ts[[j]]-ts[[j]].js[[j]];
      rhs+=after.edge.before,{j,1,len}];
    check[lhs == rhs,"heterogeneous telescoping"];
    AppendTo[causalRows,{n,len,Total[Flatten[lhs]^2]}],
    {n,1,4},{len,0,6}];
  check[{{0,-1},{1,0}}.DiagonalMatrix[{1,-1}] !=
        DiagonalMatrix[{1,-1}].{{0,-1},{1,0}},"unsafe reflection"];
  check[MatrixPower[DiagonalMatrix[{1,-1}],2] == IdentityMatrix[2],"endpoint cancellation"];

  coords={x1,x2,x3,x4};
  mat={{0,-1,0,0},{1,0,0,0},{0,0,0,-1/f[x1]},{0,0,f[x1],0}};
  bracket[u_,v_] := Table[Sum[u[[k]]*D[v[[j]],coords[[k]]]-v[[k]]*D[u[[j]],coords[[k]]],
    {k,1,4}],{j,1,4}];
  nij[i_,j_] := Together[bracket[mat[[All,i]],mat[[All,j]]] -
    mat.bracket[mat[[All,i]],UnitVector[4,j]] -
    mat.bracket[UnitVector[4,i],mat[[All,j]]]];
  check[nij[1,3] == {0,0,f'[x1]/f[x1],0},"symbolic vector-field Nijenhuis"];
  check[Simplify[(f'[x1]/f[x1]) /. f -> Function[t,2+Sin[2*Pi*t]] /. x1 -> 0] == Pi,
    "actual compact torus nonintegrability"];
  Do[
    test=Table[nij[i,j] /. {f[x1]->a,f'[x1]->d},{i,1,4},{j,1,4}];
    check[Flatten[test] == ConstantArray[0,64] || d!=0,"zero derivative suffices"];
    check[test[[1,3]] == {0,0,d/a,0},"bracket parameter table"];
    AppendTo[variableRows,ToString[#,InputForm] & /@ {a,d,d/a}],
    {a,{1/2,1,2,3}},{d,{-2,0,1,5}}];
  <|"all_passed"->True,"assertion_count"->assertions,"kernel_version"->$Version,
    "rotation_rows"->rotationRows,"exterior_rows"->exteriorRows,
    "causal_rows"->causalRows,"variable_rows"->variableRows|>
]]];
If[AssociationQ[result],AssociateTo[result,"runtime_seconds"->First[timing]]];
ExportString[result,"RawJSON","Compact"->True]
