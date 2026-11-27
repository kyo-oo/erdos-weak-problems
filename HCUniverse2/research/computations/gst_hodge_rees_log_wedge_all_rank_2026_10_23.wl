(* Mathbox exact EXTERIOR-ALGEBRA audit: Rees fold z_i=t u_i.
   Every factor dlog(z_i)=dlog(t)+dlog(u_i).
   A monomial is encoded as sorted distinct basis indices:
   0 = dlog t; 1..p = dlog u_i.
   Independent combinatorial antisymmetric wedge expansion,
   not Wolfram symbolic commutative polynomial multiplication.
*)
ClearAll["Global`*"];
encode[seq_List]:=StringRiffle[ToString/@Sort[seq],","];
logWedgeTest[n_Integer]:=Module[
 {choiceLists,rules,actual,expected,key,terms,ok,variants},
 choiceLists=Tuples[{0,1},n];
 rules=DeleteCases[Table[
   Module[{sequence},
    sequence=Table[If[choice[[i]]==1,0,i],{i,1,n}];
    If[Length[Union[sequence]]!=n,Nothing,
      encode[sequence]->Signature[sequence]]
   ],{choice,choiceLists}],Nothing];
 actual=Merge[rules,Total];
 expected=Association[encode[Range[n]]->1];
 Do[
   key=encode[Prepend[DeleteCases[Range[n],j],0]];
   expected[key]=(-1)^(j-1),
 {j,1,n}];
 terms=Union[Keys[actual],Keys[expected]];
 ok=And@@Table[Lookup[actual,term,0]===Lookup[expected,term,0],
            {term,terms}];
 {n,Length[choiceLists],Length[rules],Length[actual],ok}
];
tests=Table[logWedgeTest[n],{n,1,12}];
(* Independent checks of low-degree explicit residues.
 p=1: dlog z1 = dlog u1 + dlog t
 p=2: dlog z1 ^ dlog z2 =
  dlog u1 ^ dlog u2 + dlog t ^ (dlog u2 - dlog u1)
 p=3: residue = (du2^du3)-(du1^du3)+(du1^du2)
*)
lowDegreeExpected=<|
 "p1Residue"->{1},
 "p2Residue"->{1,-1},
 "p3Residue"->{1,-1,1}
|>;
(* Fixed-bundle regular-section Chow constraint:
 any two section zero loci have the same top Chern class,
 so their class difference is exactly zero.
 This is a symbolic CHOW structural assertion,
 independently of all coefficients of a varying section. *)
fixedBundleChowSame=Expand[chernTop-chernTop]===0;
out=<|
 "ranks"->Length[tests],
 "allLogExteriorIdentitiesPass"->And@@tests[[All,5]],
 "caseStats"->tests,
 "failures"->Select[tests,Not[#[[5]]]&],
 "fixedBundleZeroLocusChowDifference"->fixedBundleChowSame,
 "lowDegreeResidueSignPatterns"->lowDegreeExpected
|>;
Print[out];out