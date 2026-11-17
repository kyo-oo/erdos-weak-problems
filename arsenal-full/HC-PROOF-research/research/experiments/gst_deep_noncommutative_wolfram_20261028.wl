(* Exact experiment contract.
   Base 417b4aa5a50280b655c31bd066f588e0c6330365.
   Universal polynomial identities are tested symbolically on the stated
   generic matrix models. Finite-group averaging is tested on EVERY basis
   vector of the rational 2-cocycle kernel for the listed finite actions.
   No random sampling, machine reals, geometric coverage or novelty claim.
   Execute the complete file with the Wolfram Language evaluator plugin.
*)
ClearAll["Global`*"];
Catch[
  results = {};
  assert[label_, condition_] := If[TrueQ[condition],
    AppendTo[results, label], Throw[<|"Failed" -> label|>, "audit"]];
  zeroQ[mat_] := AllTrue[Flatten[mat], TrueQ[Expand[#] === 0] &];
  elapsed = First[AbsoluteTiming[
    amat = {{0,0,0},{0,0,-1},{0,1,0}};
    bmat = {{0,0,1},{0,0,0},{-1,0,0}};
    cmat = {{0,-1,0},{1,0,0},{0,0,0}};
    mats = {amat,bmat,cmat};
    assert["all weighted frames singular", Expand[Det[x amat+y bmat+z cmat]] === 0];
    assert["quadratic word recovery", Total[Map[#.# &,mats]] === -2 IdentityMatrix[3]];
    assert["integer fourth-order word recovery",
      Total[Map[Function[p,Dot[mats[[p[[1]]]],mats[[p[[1]]]],
        mats[[p[[2]]]],mats[[p[[2]]]]]],Subsets[Range[3],{2}]]] === IdentityMatrix[3]];
    assert["operators really do not commute", amat.bmat =!= bmat.amat];

    tri[n_, tag_] := UpperTriangularize[
      Array[Symbol[tag<>ToString[#1]<>ToString[#2]] &, {n,n}], 1];
    star[u_,v_] := u+v+u.v;
    (* Explicit multiplication fixes the 0th power to the identity, including
       singular symbolic matrices; no matrix inverse/eigensystem is used. *)
    productPower[u_,k_] := Nest[u.# &,IdentityMatrix[Length[u]],k];
    invpoly[u_,n_] := Total[Table[productPower[-u,k],{k,0,n-1}]];
    ax=tri[4,"ax"]; bx=tri[4,"bx"]; cx=tri[4,"cx"];
    assert["ordered star associativity", zeroQ[star[star[ax,bx],cx]-star[ax,star[bx,cx]]]];
    assert["depth-four inverse on the left", zeroQ[(IdentityMatrix[4]+ax).invpoly[ax,4]-IdentityMatrix[4]]];
    assert["depth-four inverse on the right", zeroQ[invpoly[ax,4].(IdentityMatrix[4]+ax)-IdentityMatrix[4]]];
    assert["exact ordered gauge defect", zeroQ[
      (IdentityMatrix[4]+ax).(IdentityMatrix[4]+bx).invpoly[cx,4]-IdentityMatrix[4]
        -(star[ax,bx]-cx).invpoly[cx,4]]];
    assert["generic depth-four model is not cubic", !zeroQ[MatrixPower[ax,3]]];
    assert["generic depth-four model is noncommuting", !zeroQ[ax.bx-bx.ax]];

    ff={{0,1,0,0},{0,0,0,0},{0,0,2,0},{0,0,0,3}};
    ee=MatrixPower[ff,2].(19 IdentityMatrix[4]-5 ff)/36;
    ll=MatrixPower[ff,2].(65 IdentityMatrix[4]-19 ff)/216;
    assert["Fitting spectral projector", ee === DiagonalMatrix[{0,0,1,1}]];
    assert["Fitting inverse relation", ff.ll === ee && ll.ff === ee];
    assert["projector is idempotent", ee.ee === ee];
    assert["nilpotent image can be missed", ff.{0,1,0,0} === {1,0,0,0} &&
      ee.{1,0,0,0} === {0,0,0,0}];
    assert["generalized fixed mode exists", ff.{0,1,0,0} =!= {0,0,0,0} &&
      MatrixPower[ff,2].{0,1,0,0} === {0,0,0,0}];
    jj3={{0,1,0},{0,0,1},{0,0,0}};
    assert["generalized nonfixed mode already in source image",
      jj3.{0,0,1} === {0,1,0} && jj3.{0,1,0} === {1,0,0} &&
      jj3.jj3.{0,1,0} === {0,0,0}];

    auditAction[reps_, table_, label_] := Module[
      {n,dim,vars,flat,cv,eqs,mat,basis,checked,arr,avg,reconstructed},
      n=Length[reps]; dim=Length[First[reps]];
      vars=Array[zz,{n,n,dim}]; flat=Flatten[vars];
      cv[g_,h_] := vars[[g+1,h+1]];
      eqs=Flatten[Table[
        reps[[g+1]].cv[h,k]-cv[table[[g+1,h+1]],k]+cv[g,table[[h+1,k+1]]]-cv[g,h],
        {g,0,n-1},{h,0,n-1},{k,0,n-1}]];
      mat=Table[Coefficient[eqs[[row]],flat[[col]]],{row,Length[eqs]},{col,Length[flat]}];
      basis=NullSpace[mat];
      assert[label<>" representation law",And@@Flatten[Table[
        reps[[g+1]].reps[[h+1]] === reps[[table[[g+1,h+1]]+1]],
        {g,0,n-1},{h,0,n-1}]]];
      assert[label<>" group table associative",And@@Flatten[Table[
        table[[table[[g+1,h+1]]+1,k+1]] === table[[g+1,table[[h+1,k+1]]+1]],
        {g,0,n-1},{h,0,n-1},{k,0,n-1}]]];
      checked=And@@Table[
        arr=ArrayReshape[vec,{n,n,dim}];
        avg=Table[Total[arr[[g+1]]]/n,{g,0,n-1}];
        reconstructed=Table[avg[[g+1]]+reps[[g+1]].avg[[h+1]]-
          avg[[table[[g+1,h+1]]+1]],{g,0,n-1},{h,0,n-1}];
        reconstructed === arr,{vec,basis}];
      assert[label<>" complete cocycle basis",checked];
      <|"Action"->label,"GroupOrder"->n,"CoefficientRank"->dim,
        "CochainDimension"->Length[flat],"CocycleDimension"->Length[basis],
        "ConstraintRank"->MatrixRank[mat],"EveryCocycleBasisVectorReconstructed"->checked|>
    ];
    auditCyclic[n_, rmat_, label_] := auditAction[
      Table[productPower[rmat,g],{g,0,n-1}],
      Table[Mod[g+h,n],{g,0,n-1},{h,0,n-1}],label];
    perms=Permutations[Range[3]];
    s3reps=Map[IdentityMatrix[3][[#]] &,perms];
    s3table=Table[First[FirstPosition[s3reps,s3reps[[g]].s3reps[[h]]]]-1,{g,6},{h,6}];
    assert["S3 genuinely noncommutative",s3reps[[2]].s3reps[[3]] =!= s3reps[[3]].s3reps[[2]]];
    rows=Join[Table[auditCyclic[n,{{1}},"trivial C"<>ToString[n]],{n,1,6}],
      {auditCyclic[2,{{-1}},"sign C2"],auditCyclic[2,{{0,1},{1,0}},"swap C2"],
       auditCyclic[3,{{0,-1},{1,-1}},"rotation C3"],
       auditCyclic[4,{{0,-1},{1,0}},"rotation C4"],
       auditCyclic[6,{{0,-1},{1,1}},"rotation C6"],
       auditAction[ConstantArray[{{1}},6],s3table,"trivial S3"],
       auditAction[s3reps,s3table,"permutation S3"]}];
  ]];
  <|"AllPassed"->True,"KernelVersion"->$Version,"RuntimeSeconds"->elapsed,
    "AssertionCount"->Length[results],"Assertions"->results,
    "FiniteActionRows"->rows,"NumericApproximationUsed"->False|>,
  "audit"
]
