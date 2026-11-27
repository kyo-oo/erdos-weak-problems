(* Exact all-p positive/negative binomial world arithmetic.
 Scope: algebraic equalities of Chern classes and positive hyperplane moments,
 not an algebraic-Chow source or a current-rectifiability computation. *)
ClearAll[ww,posMoment,negMoment,posMult,negMult,polyClass,posWorld,negWorld,survive,pp,kk,cc,hh,mm,rr,report];
ww[pp_Integer,kk_Integer]:=(-1)^(kk-1) Binomial[pp+1,kk];
posMoment[pp_Integer]:=Sum[If[OddQ[kk],Binomial[pp+1,kk] kk^pp,0],{kk,1,pp+1}];
negMoment[pp_Integer]:=Sum[If[EvenQ[kk],Binomial[pp+1,kk] kk^pp,0],{kk,1,pp+1}];
posMult[pp_Integer]:=Sum[If[OddQ[kk],Binomial[pp+1,kk],0],{kk,1,pp+1}];
negMult[pp_Integer]:=Sum[If[EvenQ[kk],Binomial[pp+1,kk],0],{kk,1,pp+1}];
polyClass[pp_Integer,rk_,kk_Integer,m_]:=Binomial[rk,pp](kk m)^pp hh^pp+cc;
posWorld[pp_Integer,rk_,m_]:=Expand[Sum[If[OddQ[kk],Binomial[pp+1,kk]*polyClass[pp,rk,kk,m],0],{kk,1,pp+1}]];
negWorld[pp_Integer,rk_,m_]:=Expand[Sum[If[EvenQ[kk],Binomial[pp+1,kk]*polyClass[pp,rk,kk,m],0],{kk,1,pp+1}]];
survive[pp_Integer,rk_,m_]:=Expand[posWorld[pp,rk,m]-negWorld[pp,rk,m]];
report=Table[<|"p"->pp,"P_sourceMultiplicity"->posMult[pp],
"N_sourceMultiplicity"->negMult[pp],"P_hyperplaneMoment"->posMoment[pp],
"N_hyperplaneMoment"->negMoment[pp],
"balance"->TrueQ[posMoment[pp]==negMoment[pp]],
"sourceMultiplicity"->TrueQ[posMult[pp]==2^pp && negMult[pp]==2^pp-1],
"exactCohomology"->TrueQ[survive[pp,rr,mm]==cc]|>,{pp,1,12}];
allPassed=And@@Flatten[Table[Values[KeyTake[report[[pp]],{"balance","sourceMultiplicity","exactCohomology"}]],{pp,1,12}]];
Print[<|"allPassed"->allPassed,"cases"->12,
"volumeMoments_p1_to_p8"->Table[posMoment[pp],{pp,1,8}],
"codimTwoPlus"->posWorld[2,rr,mm],
"codimTwoMinus"->negWorld[2,rr,mm],
"codimTwoSurvival"->survive[2,rr,mm]|>];
If[!TrueQ[allPassed],Abort[]];
