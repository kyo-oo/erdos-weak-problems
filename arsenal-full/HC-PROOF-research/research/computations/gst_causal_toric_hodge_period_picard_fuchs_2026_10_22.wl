(* Exact all-dimensional GST causal toric-boundary to pure-Hodge period.
   Dwork family x_0 ... x_n + t Sum_i x_i^(n+1) = 0 in P^n.
   Constant term:
      Phi_n(z) = Sum_{k>=0} a(n,k) z^k,
      a(n,k)=((n+1)k)!/(k!)^(n+1), z=(-t)^(n+1).
   Picard-Fuchs operator:
      theta^n - (n+1)z Product_{r=1}^n ((n+1)theta+r).
   All calculations are exact; finite checks do not prove period identification.
*)

Clear[a,n,k,r,z,theta,recurrence,coefficients,operatorCheck];
a[n_,k_]:=Factorial[(n+1)k]/Factorial[k]^(n+1);
recurrence=Flatten[Table[
 TrueQ[
  k^n a[n,k] == (n+1) Product[(n+1)(k-1)+r,
     {r,1,n}] a[n,k-1]],
 {n,2,8},{k,1,12}]];
coefficients=Table[{n,Table[a[n,k],{k,0,4}]},{n,2,5}];

(* Independently evaluate the coefficient of z^k in the formal PF
   equation, including the k=0 initial boundary. *)
operatorCheck=Flatten[Table[
 TrueQ[
  If[k==0,0,k^n a[n,k]] -
    If[k==0,0,(n+1) Product[(n+1)(k-1)+r,
      {r,1,n}] a[n,k-1]] == 0],
 {n,2,8},{k,0,12}]];

{"FactorialRecurrenceCount"->Length[recurrence],
 "FactorialRecurrenceAllTrue"->And@@recurrence,
 "PicardFuchsCoefficientCount"->Length[operatorCheck],
 "PicardFuchsCoefficientsAllTrue"->And@@operatorCheck,
 "FirstFivePeriodCoefficients"->coefficients}
