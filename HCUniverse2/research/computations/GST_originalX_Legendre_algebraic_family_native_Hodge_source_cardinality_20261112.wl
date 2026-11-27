(* Genuine ALGEBRAIC smooth-projective base family:
  E_lambda: y^2=x(x-1)(x-lambda), lambda in A1 minus {0,1}.
  Original E_{-1} has j invariant 1728; isomorphic to E_i.
  For X_lambda=E_lambda x E_{-1}, the original actual
  diagonal-cross divisor class is rational Hodge at lambda=-1.
  Its local flat transport can be Hodge at another fiber only
  when there exists a nonzero rational Hodge cross correspondence,
  hence E_lambda is ISOGENOUS to E_{-1}.
  The isogeny partners of a fixed elliptic curve have
  only countably many isomorphism classes (finite subgroups
  of a fixed elliptic curve form a countable set).
  The algebraic j(lambda) function has finite fibers,
  so only countably many distinct lambda can be isogenous
  to E_{-1}. This rules out a freely manufactured
  uncountable source-bearing family for THIS alpha,
  even though the original alpha is already algebraic.

  Wolfram verifies the exact algebraic j map, nonconstancy,
  original CM point and its actual finite isomorphism orbit.
  Countability of the isogeny orbit is proved separately
  from finite subgroups, NOT inferred from finite samples.
*)
Module[{z,j,roots,der,pFactor,checks},
 j=256*(1-z+z^2)^3/(z^2*(1-z)^2);
 roots=DeleteDuplicates[z/.Solve[j==1728,z,Complexes]];
 der=Factor[D[j,z]];
 pFactor=Factor[Together[j-1728]];
 checks={
  Simplify[j/.z->-1]==1728,
  Sort[roots]==Sort[{-1,1/2,2}],
  der=!=0,
  Exponent[Numerator[Together[j]],z]==6,
  pFactor===64*(z-2)^2*(z+1)^2*(2*z-1)^2/((z-1)^2*z^2)
 };
 <|"family"->"Legendre elliptic curves over lambda!=0,1",
   "original"->"lambda=-1 with E_{-1} isomorphic to E_i",
   "jInvariant"->j,
   "originalJ"->Simplify[j/.z->-1],
   "sameIsomorphismClassDistinctLambda"->roots,
   "jMinus1728Exact"->pFactor,
   "isogenySourceLocusCardinality"->"countable from countably many finite subgroups",
   "allPassed"->And@@checks|>
]