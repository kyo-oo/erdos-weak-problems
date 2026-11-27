(* Owner's image 3 all-degree GST N-cohomology/Hodge-Star/CM construction.
 The genuine Hodge Star on an original complex d-fold maps degree 2p
 to complementary degree 2(d-p), so use P_p direct-sum P_(d-p).
 After identification of the two rational Hodge fibers by a rational
 polarized Hodge-Star isomorphism D, original J, M and curvature become
 J={{0,1},{-1,0}}, M=diag(0,2), S=swap, [J,M]=2S.
 On r-dimensional rational Hodge fibers, the full operation is
 KroneckerProduct[ F_b, IdentityMatrix[r] ].
 The script tests bounded ranks; the universal conclusion follows
 algebraically from the proven quadratic matrix identity, not the sweep.
 No algebraic correspondence implementing D on arbitrary original X is
 assumed or claimed here. *)

Module[{star,J,M,C,b,F,zero2,states,rows},
star={{0,1},{1,0}};
J={{0,1},{-1,0}};
M={{0,0},{0,2}};
C=J.M-M.J;
F={{1,1+2*b},{2*b-1,3}};
zero2=ConstantArray[0,{2,2}];
states=Table[
 Module[{t=F/.b->q,poly},
  poly=t.t-4*t+4*(1-q^2)*IdentityMatrix[2];
  <|"physicalCharge"->q,
    "characteristicPolynomial"->CharacteristicPolynomial[t,z],
    "exactQuadraticZero"->(poly==zero2)|>],
 {q,{0,1}}];
rows=Flatten[Table[
 Module[{t=KroneckerProduct[F/.b->q,IdentityMatrix[m]],v,k},
 v=Table[j^2+3*j+1,{j,1,2*m}];
 k=Transpose[NestList[t.#&,v,2*m-1]];
 <|"physicalCharge"->q,"pairedHodgeDim"->2*m,
   "oneSeedKrylovRank"->MatrixRank[k]|>],
 {m,{1,2,3,4,6,10}},{q,{0,1}}]];
<|"originalJ2"->J.J,
  "curvatureIsTwiceStar"->(C==2*star),
  "starSquare"->star.star,
  "generalPhysicalQuadraticZero"->(
    FullSimplify[F.F-4*F+4*(1-b^2)*IdentityMatrix[2]]==zero2),
  "physicalStates"->states,
  "finiteRankWitnesses"->rows,
  "maxObservedOneSeedRank"->Max[Lookup[rows,"oneSeedKrylovRank"]],
  "allPassed"->And[
    J.J==-IdentityMatrix[2],
    C==2*star,
    star.star==IdentityMatrix[2],
    FullSimplify[F.F-4*F+4*(1-b^2)*IdentityMatrix[2]]==zero2,
    And@@Lookup[states,"exactQuadraticZero"],
    And@@((#<=2)& /@ Lookup[rows,"oneSeedKrylovRank"])]|>
]
