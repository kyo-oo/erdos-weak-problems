(* Exact contract: all 2x2 matrices and all idempotent pairs over the six
   listed prime-power rings. Nilpotence bound 2e for Mat_2(Z/p^e).
   Independent implementation: gst_projection_branch_checks.py.
   Universal geometric statements are supplied by hand proofs, not this run. *)
ClearAll["Global`*"];
Catch[
  passed={}; assert[s_,q_] := If[TrueQ[q],AppendTo[passed,s],Throw[<|"Failed"->s|>,"audit"]];
  elapsed=First[AbsoluteTiming[
    ii=IdentityMatrix[2]; zz=ConstantArray[0,{2,2}];
    mm[a_,b_,m_] := Mod[a.b,m];
    ee[a_,m_] := Mod[a.a-a,m];
    nn[a_,m_] := Mod[a-(2 a-ii).ee[a,m],m];
    br[p_,q_,m_] := Mod[q.p+(ii-q).(ii-p),m];
    ni[a_,m_,bound_] := Module[{r=ii,found=0},Do[r=mm[r,a,m];If[r===zz,found=j;Break[]],{j,bound}];found];
    rows=Table[Module[{m=spec[[1]],p=spec[[2]],ex=spec[[3]],mats,idems,eligible=0,hist=<||>,
                     okDef=True,okComp=True,okBound=True,okCorr=True,okInt=True,okProd=True,
                     okInv=True,okConj=True,nearpairs=0,e,n,r,k,u,v,d,c,ds,ss,term,inverse},
      mats=Map[Partition[#,2]&,Tuples[Range[0,m-1],4]];
      idems=Select[mats,ee[#,m]===zz&];
      Do[e=ee[a,m];n=ni[e,m,2 ex];
        okDef=okDef && ee[nn[a,m],m]===Mod[e.e.(4 e-3 ii),m];
        okComp=okComp && nn[Mod[ii-a,m],m]===Mod[ii-nn[a,m],m];
        okBound=okBound && ((n>0)===(Mod[e.e,p]===zz));
        If[n>0,eligible++;AssociateTo[hist,n->(Lookup[hist,n,0]+1)];
          k=0;While[2^k<n,k++];r=Nest[nn[#,m]&,a,k];okCorr=okCorr && ee[r,m]===zz],{a,mats}];
      Do[u=br[a,b,m];v=br[b,a,m];d=Mod[b-a,m];c=Mod[ii-d.d,m];
        okInt=okInt && mm[u,a,m]===mm[b,u,m];
        okProd=okProd && mm[u,v,m]===c && mm[v,u,m]===c;
        n=ni[d,m,2 ex];If[n>0,nearpairs++;ss=zz;term=ii;ds=mm[d,d,m];
          Do[ss=Mod[ss+term,m];term=mm[term,ds,m],{n}];inverse=mm[v,ss,m];
          okInv=okInv && mm[u,inverse,m]===ii && mm[inverse,u,m]===ii;
          okConj=okConj && mm[mm[u,a,m],inverse,m]===b],{a,idems},{b,idems}];
      assert["mod "<>ToString[m]<>" defect",okDef];
      assert["mod "<>ToString[m]<>" complement",okComp];
      assert["mod "<>ToString[m]<>" nilpotence bound",okBound];
      assert["mod "<>ToString[m]<>" every eligible correction",okCorr];
      assert["mod "<>ToString[m]<>" all intertwining",okInt];
      assert["mod "<>ToString[m]<>" all bridge products",okProd];
      assert["mod "<>ToString[m]<>" every bridge inverse",okInv];
      assert["mod "<>ToString[m]<>" every conjugacy",okConj];
      <|"Modulus"->m,"MatrixCount"->Length[mats],"EligibleMatrices"->eligible,
        "DefectNilpotenceHistogram"->KeySort[hist],"IdempotentCount"->Length[idems],
        "IdempotentPairCount"->Length[idems]^2,"NilpotentDifferencePairCount"->nearpairs|>
    ],{spec,{{2,2,1},{3,3,1},{4,2,2},{5,5,1},{8,2,3},{9,3,2}}}];
    a={{0,a12,a13,a14},{0,1,a23,a24},{0,0,0,a34},{0,0,0,1}};
    identity=IdentityMatrix[4];
    correction[x_] := Expand[x-(2 x-identity).(x.x-x)];
    q=correction[correction[a]];
    zeroQ[x_] := And@@Map[TrueQ[Expand[#]===0]&,Flatten[x]];
    assert["symbolic noncommuting four-dimensional exactification",zeroQ[q.q-q]];
    assert["symbolic initial defect has fourth power zero",zeroQ[Nest[(a.a-a).#&,identity,4]]];
    assert["generic correction is nonconstant",!zeroQ[q-DiagonalMatrix[{0,1,0,1}]]];
    assert["universal boundary-defect polynomial",Expand[(x-y)^2-(2-x-y)^2+4(2-x-y)-4(1-x*y)]===0];
    dof={{1,1},{t,-t}}; left={{1,0},{-t,1}};right={{1,-1},{0,1}};
    assert["ramification cokernel normal form",zeroQ[left.dof.right-DiagonalMatrix[{1,-2t}]]];
    assert["ramification determinant simple",Expand[Det[dof]+2t]===0];
    assert["quadratic companion",zeroQ[{{0,1},{t^2,0}}.{{0,1},{t^2,0}}-t^2 ii]];
    assert["three-twist extraction",Expand[(alphaSym+2divSym)^2+(alphaSym-2divSym)^2-
      2alphaSym^2-8divSym^2]===0];
    pair[i_,j_] := If[i==j,-2,If[Abs[i-j]==1,1,0]];
    assert["every reflected A1 through A12 pair",And@@Flatten[Table[
      With[{j=n+1-i},pair[i,i]+pair[j,j]-pair[i,j]-pair[j,i]===
        If[i==j,0,If[Abs[i-j]==1,-6,-4]]],{n,1,12},{i,1,n}]]];
    assert["exact exceptional extraction scales",1/(8*(-6))===-1/48 && 1/(8*(-4))===-1/32];
    coneBasis=GroebnerBasis[{2x,z,y},{x,y,z}];
    assert["reduced cone singular ideal",And@@Table[
      PolynomialReduce[v,coneBasis,{x,y,z}][[2]]===0,{v,{x,y,z}}]];
    assert["integral two-primary hostile control",And@@Table[
      Mod[(-1)^2,2^s]===1 && Mod[(-2)^s,2^s]===0 && Mod[-1,2^s]=!=1,{s,2,8}]];
    assert["split-cover isotropic nonzero control",
      With[{v={1,0,-1,0},h={1,1,1,1},j={{0,1,0,0},{1,0,0,0},{0,0,0,1},{0,0,1,0}}},
       v.j.v===0 && v.j.h===0 && v=!={0,0,0,0}]];
  ]];
  <|"AllPassed"->True,"KernelVersion"->$Version,"RuntimeSeconds"->elapsed,
    "AssertionCount"->Length[passed],"Assertions"->passed,"FiniteRows"->rows,
    "NumericApproximationUsed"->False|>,"audit"]
