(* Exact finite-difference identity behind divisor algebra sourced
   by all finite Noether-normalization fold maps X -> P^d.
   Mathematical theorem in GST_optimal_rank_universal_stein_fold_trace_residual_2026-10-23.tex:
   sum_(S subset [p]) (-1)^(p-|S|)(A+eps sum_(i in S) lambda_i)^p
    = p! eps^p product_i lambda_i.
   Tests are identity checks; the unrestricted theorem follows
   by inclusion-exclusion in the Chow ring. *)
ClearAll[aa,ee,xx];
tests=Table[Module[{xs=Array[xx,p],s},
 s=Sum[(-1)^(p-Length[z]) (aa+ee Total[xs[[z]]])^p,
    {z,Subsets[Range[p]]}];
 TrueQ[Expand[s-Factorial[p] ee^p Times@@xs]===0]
],{p,1,6}];
out=<|"codimensions"->Range[6],
 "allExactFiniteFoldPolarizationsPass"->And@@tests,
 "perCodimension"->tests|>;
Print[out];out