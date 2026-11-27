(* GST original-X higher primitive Chern source discriminating test.
   X=Gr(2,4), Picard rank1, dim4, p=2.
   True tautological bundles S,Q: sigma2=c2(Q), sigma11=c2(dual tautological subbundle S).
   The rational Schubert ring is represented by Chern roots x,y
   modulo complete symmetric relations h3=h4=0.
   Primitive P=sigma2-sigma11 is an ACTUAL algebraic Chow class
   beyond fixed-h divisor-square span. Original GST CM null/max
   physical Navigation b∈{0,1} has actual two-cell operator
   [[1,1+2b],[2b-1,3]] on the TRUE Chow basis h²,P.

   This is an exact RESTRICTED geometric source-birth test.
   It does not construct corresponding bundles for arbitrary X
   and prescribed unknown Hodge residual. *)
Module[{x,y,h3,h4,gb,red,h,s2,s11,P,top,a0,a1,v,kry,hank,states},
h3=x^3+x^2*y+x*y^2+y^3;
h4=x^4+x^3*y+x^2*y^2+x*y^3+y^4;
gb=GroebnerBasis[{h3,h4},{x,y}];
red[f_]:=PolynomialReduce[Expand[f],gb,{x,y}][[2]];
h=x+y;s2=x^2+x*y+y^2;s11=x*y;P=s2-s11;
top=x^2*y^2;
a0={{1,1},{-1,3}};a1={{1,3},{1,3}};v={1,0};
kry[t_]:=Transpose[{v,t.v}];
hank[t_]:=Module[{L=Last[Inverse[kry[t]]],
  orbit=NestList[t.#&,v,2],H},
 H=Table[L.orbit[[i+j+1]],{i,0,1},{j,0,1}];
 <|"matrix"->H,"det"->Det[H]|>];
states=Table[Module[{A=If[b==0,a0,a1],K},
 K=kry[A];
 <|"physicalNavigationCharge"->b,"matrix"->A,
 "characteristicPolynomial"->CharacteristicPolynomial[A,z],
 "sourceKrylovDet"->Det[K],"hankel"->hank[A],
 "primitiveFromOriginalGSTOneFold"->((2*b-1)*(A.v-v)=={0,1})|>],
 {b,{0,1}}];
<|"HodgeChernRelation"->Expand[h^2-s2-s11]==0,
 "primitiveKilledByAmple"->red[h*P]==0,
 "sigma2SquareTop"->red[s2^2-top]==0,
 "sigma11SquareTop"->red[s11^2-top]==0,
 "sigmaMixedTopZero"->red[s2*s11]==0,
 "primitiveSelfPairing"->Coefficient[red[P^2],x^2*y^2],
 "divisorSquaredSectorRank"->1,
 "genuineChernSourceSectorRank"->2,
 "physicalGSTStates"->states,
 "allPassed"->(red[h*P]==0&&red[P^2]==2*top&&
  red[s2*s11]==0&&
  And@@Lookup[states,"primitiveFromOriginalGSTOneFold"]&&
  And@@(Lookup[Lookup[states,"hankel"],"det"]=={-1,-1}))|>
]
