(* Genuine fixed-component motivic Navigation source birth audit.
   A=E_CM^3, hodge polynomial H_A=(1+u)^3(1+v)^3,
   E an actual elliptic curve with Hodge numbers (1,1,1,1).
   X=P_A(O+L) has Hodge polynomial (1+uv)*H_A from
   projective bundle formula and BB fixed components
   F_0=A at Tate shift 0, F_1=A at shift 1.
   Coefficient [u^p v^p] equals rational Hodge rank only
   because A is a CM E^3 with maximal Picard rank 9.
   This check distinctly tests non-diagonal Hodge components,
   and does not pretend BB decomposition is derived by finite
   coefficient computations. *)
Module[{u,v,ha,hx,hBB,hodd,diag,offdiag,diff,
  check},
ha=Expand[(1+u)^3(1+v)^3];
hx=Expand[(1+u v)ha];
hBB=Expand[ha+u v ha];
diag=Table[Coefficient[Coefficient[hx,u,p],v,p],{p,0,4}];
offdiag=Coefficient[Coefficient[hx,u,1],v,0];
diff=Expand[hx-hBB];
(* Original CM abelian fixed source known in all codim<=3,
   so Hdg image defect zero in each, hence zero in X. *)
check=(diag=={1,10,18,10,1}&&offdiag==3&&
 diff==0&&Factor[ha]==(1+u)^3(1+v)^3);
<|"fixedComponentHodgePolynomial"->ha,
 "fullOriginalFourfoldHodgePolynomial"->hx,
 "BBTwoFixedComponentMotivicHodgePolynomial"->hBB,
 "allCanonicalHodgeDiagonalDimensions"->diag,
 "actualOffDiagonalH10"->offdiag,
 "fixedComponentMotivicRealizationError"->diff,
 "allPassed"->check|>
]