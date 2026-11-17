(* GST arbitrary-X relative-Chow route: exact finite arithmetic discriminator.
   This verifies the alternating form of the *actual elliptic family*
   X_t = E_i x E_(i+t), and a rational rank-plateau model.
   It does NOT verify the general relative Chow properness theorem or
   the rational Hodge conjecture. Stateless Wolfram Language script. *)
ClearAll[t, ell, hol1, hol2, wedgeCoeff, stageMatrices, stageRanks,
         qGram, src, target, proj, remainder, energy];
ell = SparseArray[{{1,4}->1,{4,1}->-1,{3,2}->-1,{2,3}->1},{4,4}];
hol1={1,0,I,0};hol2={0,1,0,I+t};
wedgeCoeff=Expand[
 Sum[ell[[i,j]]*(hol1[[k]] hol2[[l]]-hol1[[l]] hol2[[k]])*
     Signature[{i,j,k,l}],{i,1,4},{j,1,4},{k,1,4},{l,1,4}]/4];
stageMatrices={{{1,0,0}},{{1,0,0},{2,0,0}},
                  {{1,0,0},{2,0,0},{0,1,0}}};
stageRanks=MatrixRank/@stageMatrices;
qGram=DiagonalMatrix[{2,3,5}];
src={{1,1},{0,1},{0,0}};target={3,4,2};
proj=src.Inverse[Transpose[src].qGram.src].Transpose[src].qGram;
remainder=(IdentityMatrix[3]-proj).target;
energy=Simplify[remainder.qGram.remainder];
result=<|"EllipticHodgeTypeObstructionCoefficient"->wedgeCoeff,
          "HodgeAtCenter"->(wedgeCoeff/.t->0),
          "ExactOnlyAtCenter"->(wedgeCoeff==t),
          "RankPlateauAndGrowth"->stageRanks,
          "Residual"->remainder,
          "NativeResidualEnergy"->energy|>;
If[!TrueQ[wedgeCoeff==t] || stageRanks=!={1,1,2} ||
      remainder=!={0,0,2} || energy=!=20,
      Print["FAIL"];Abort[]];
Print[result]; Print["PASS: exact finite algebra only"];