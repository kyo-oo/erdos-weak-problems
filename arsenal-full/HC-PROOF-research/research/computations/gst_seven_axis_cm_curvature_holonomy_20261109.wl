(* GST seven-axis information + CM ordered curvature + native source
   Exact Wolfram Language reproducibility packet, 2026-11-09.
   Computes only rational/integer finite assertions; no floating tolerance.
   The 6-dimensional middle-Hodge sector is the geometric divisor-product
   matrix-unit action established in the repository's 2026-11-08 derivation.
*)
Module[{f, inv, states, j, k, p, orbit, delta, comm, ordered,
        coeff2, eps=1/10, edgeDet, radix, tests,
        gamma11, gamma21, seed, fourfoldCycle},
  f[{c_,d_}] := {Quotient[c+4*d,3], Mod[c+4*d,3]};
  inv[{cp_,dp_}] := {Mod[dp+3*cp,4], Quotient[dp+3*cp,4]};
  states = Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];

  j = {{0,-1},{1,0}};
  k = {{1,0},{0,-1}};
  p[{c_,d_}] := c*j + d*k;
  orbit = NestList[f,{0,1},5];
  delta = Table[p[orbit[[i+1]]]-p[orbit[[i]]],{i,1,5}];
  comm = j.k-k.j;
  ordered = Fold[Dot,IdentityMatrix[2],
                 Table[IdentityMatrix[2]+eps*delta[[i]],{i,1,5}]];
  coeff2 = Sum[delta[[i]].delta[[q]],{i,1,4},{q,i+1,5}];
  edgeDet = Table[Det[IdentityMatrix[2]+eps*delta[[i]]],{i,1,5}];

  radix[m_,n_,z_] := Quotient[z,n]+m*Mod[z,n];
  tests = Flatten[Table[
    And[
      AllTrue[Range[0,m*n-1],
              Mod[radix[m,n,#]-m*#,m*n-1]==0&],
      Sort[radix[m,n,#]&/@Range[0,m*n-1]]
        === Range[0,m*n-1]],
    {m,2,7},{n,2,7}]];

  gamma11 = SparseArray[{{1,1}->1},{6,6}];
  gamma21 = SparseArray[{{2,1}->1},{6,6}];
  seed = UnitVector[6,1];
  fourfoldCycle = (Normal[gamma11.gamma21-gamma21.gamma11]).seed;

  <|
    "inverse12"->AllTrue[states,inv[f[#]]==#&],
    "period5_12"->AllTrue[states,Nest[f,#,5]==#&],
    "radix36"->And@@tests,
    "cycle"->orbit,
    "cmOddNonzero"->(comm!={{0,0},{0,0}}),
    "additiveZero"->(Total[delta]===ConstantArray[0,{2,2}]),
    "quadraticOrderedCoefficient"->coeff2,
    "quadraticOrderedNonzero"->(coeff2!=ConstantArray[0,{2,2}]),
    "edgeDeterminants"->edgeDet,
    "orderedHolonomy"->ordered,
    "orderedDeterminant"->Det[ordered],
    "fourfoldCodimTwoCurvatureCycle"->fourfoldCycle,
    "fourfoldRankGain"->(MatrixRank[Transpose[{seed,fourfoldCycle}]]==2)
  |>
]
