(* Exact ALL-RATIONAL original GST CM curvature strength certificate.
   The full symbolic determinant factorization comes from the original
   source-matrix construction in
   GST_image3_curvature_only_source_and_resonance_20261111.wl:
     det Krylov(U+J+b [J,M])=b^4 (2 b-1) P10(b) P16(b).

   P10, P16 have integer coefficients and leading coefficients 36900
   and 331776 respectively, both nonzero modulo 7. Exhaust ALL seven
   residues in F_7, not samples. Neither has any residue root.
   Rational-root theorem => no rational root of P10 or P16.

   Hence the only rational b whose original twelve-state Krylov
   determinant vanishes are b=0 and b=1/2.

   The theorem is ORIGINAL GST NATIVE-information cyclicity, NOT
   arbitrary-X Hodge algebraicity.
*)
ClearAll[p10,p16,r10,r16,l10,l16,checks];
p10[x_]:=411701-2185728*x^2+293888*x^3+3073344*x^4-
 960384*x^5-1658656*x^6+835776*x^7+244932*x^8-
 222264*x^9+36900*x^10;
p16[x_]:=255140-1606056*x^2+3096493*x^4-2099096*x^6+
 1818992*x^8-3016960*x^10+2444032*x^12-
 1234944*x^14+331776*x^16;
r10=Table[Mod[p10[k],7],{k,0,6}];
r16=Table[Mod[p16[k],7],{k,0,6}];
l10=Mod[36900,7];l16=Mod[331776,7];
checks=<|"completePrimeField"->Range[0,6],
 "P10Mod7AllResidues"->r10,
 "P16Mod7AllResidues"->r16,
 "LeadingCoefficientsMod7"->{l10,l16},
 "P10NoRootsInF7"->FreeQ[r10,0],
 "P16NoRootsInF7"->FreeQ[r16,0],
 "LeadingCoefficientsInvertible"->(l10!=0&&l16!=0),
 "P10StrengthOne"->p10[1],
 "P16StrengthOne"->p16[1],
 "CurvatureStrengthOneFullDet"->p10[1]p16[1]|>;
checks=Append[checks,"allPassed"->(
 FreeQ[r10,0]&&FreeQ[r16,0]&&l10!=0&&l16!=0&&
 p10[1]p16[1]==1386205893)];
Print[checks];checks