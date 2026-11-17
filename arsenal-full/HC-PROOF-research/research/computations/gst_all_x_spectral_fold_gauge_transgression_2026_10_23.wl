(* Exact algebraic-versus-holomorphic projector source test on the same
   Jouanolou GST Q = {x y + z^2 = 1}. Reproduce with the Wolfram Language
   evaluator; no random input or numerical tolerances. *)

ClearAll[x, z, y, p, gauge, pp, c2coef];
y = (1-z^2)/x;
p = {{(1+z)/2, x/2}, {y/2, (1-z)/2}};
gauge = {{1, 0}, {Exp[z], 1}};
pp = FullSimplify[gauge.p.Inverse[gauge]];

c2coef[t_] := FullSimplify[
 Tr[t.(D[t,x].D[t,z]-D[t,z].D[t,x])],
 Assumptions -> x != 0
];

checks = <|
  "algebraicIdempotent" -> FullSimplify[p.p == p, Assumptions -> x != 0],
  "holomorphicIdempotent" -> FullSimplify[pp.pp == pp, Assumptions -> x != 0],
  "involutionAlgebraic" -> FullSimplify[(2 p-IdentityMatrix[2]).(2 p-IdentityMatrix[2]) == IdentityMatrix[2], Assumptions -> x != 0],
  "involutionHolomorphic" -> FullSimplify[(2 pp-IdentityMatrix[2]).(2 pp-IdentityMatrix[2]) == IdentityMatrix[2], Assumptions -> x != 0],
  "regularCurvature_dx_dz" -> (c2coef[p] === -1/(2 x)),
  "holomorphicCurvature_dx_dz" -> FullSimplify[c2coef[pp] == -1/(2 x)+Exp[z]/2, Assumptions -> x != 0],
  "literalExactTransgression" -> FullSimplify[c2coef[pp]-c2coef[p] == D[x Exp[z]/2,x], Assumptions -> x != 0],
  "restrictedNonpolynomialEntry" -> FullSimplify[(pp[[2,1]] /. x->1) == (1-z^2)/2+z Exp[z]-Exp[2 z]/2]
|>;
{checks, And@@Values[checks], c2coef[p], c2coef[pp], c2coef[pp]-c2coef[p]}
