(* Exact rational verification of the original-X alpha-selected Yoneda
   matrix-unit algebra in abstract rational Hodge coordinates.
   This tests algebraic identities, not geometric Ext identification or Chow. *)
ClearAll[CheckYonedaUnits, CMCheck, n];
CheckYonedaUnits[n_Integer]:=Module[{qm,sm,gram,dual,op,zz,ok,traces,sumdiag},
 qm=DiagonalMatrix[Range[2,n+1]];
 sm=Table[If[i==j,1,If[i<j,1/(i+j),0]],{i,1,n},{j,1,n}];
 gram=Transpose[sm].qm.sm;
 dual=sm.Inverse[gram];
 op=Table[Outer[Times,sm[[All,i]],(Transpose[dual].qm)[[j,All]]],{i,1,n},{j,1,n}];
 zz=ConstantArray[0,{n,n}];
 ok=And@@Flatten[Table[op[[i,j]].op[[k,l]]===If[j==k,op[[i,l]],zz],{i,1,n},{j,1,n},{k,1,n},{l,1,n}]];
 traces=And@@Flatten[Table[Tr[op[[i,j]]]===KroneckerDelta[i,j],{i,1,n},{j,1,n}]];
 sumdiag=Total[Table[op[[i,i]],{i,1,n}]]===IdentityMatrix[n];
 <|"dimension"->n,"pairingDet"->Det[gram],
   "allProducts"->ok,"allTraces"->traces,"reconstructIdentity"->sumdiag|>
];
CMCheck=Module[{J,M},
 J={{0,-1},{1,0}};M={{1,0},{0,0}};
 <|"JsquareMinusIdentity"->(J.J===-IdentityMatrix[2]),
 "Mprojection"->(M.M===M),
 "nonzeroCMcommutator"->(J.M-M.J==={{0,1},{1,0}})|>];
result=Table[CheckYonedaUnits[n],{n,1,5}];
allPassed=And@@Flatten[Join[Flatten[Values[KeyTake[#,{"allProducts","allTraces","reconstructIdentity"}]]&/@result],
 Values[CMCheck]]];
Print[<|"allPassed"->allPassed,"matrixUnitTests"->Sum[n^4,{n,1,5}],
"dimensions"->result,"CM"->CMCheck|>];
If[!TrueQ[allPassed],Abort[]];
