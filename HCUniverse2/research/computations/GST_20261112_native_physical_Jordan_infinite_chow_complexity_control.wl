(* OWNER original GST 4x3 U/J/M/CM null/maximum factor, exact physical
   Navigation b=0/1, direct SURVIVE strength 1.
   Check the exact ALL-n identities by symbolic nilpotent/idempotent
   algebra, and independently by exact powers n=1..24.
   Scope: rational native source only; degrees/denominators of actual
   original-X algebraic cycles are different, scheme-theoretic quantities.
   Geometric bounded-complexity theorem in companion TeX
   uses real projective relative Chow parameter spaces. *)
Module[{f0,f1,identity2,nzero,pone,seed,n,powerOff,powerOn,
    checksOff,checksOn,offSeed,onSeed,out},
  f0={{1,1},{-1,3}};f1={{1,3},{1,3}};
  identity2=IdentityMatrix[2];
  nzero=f0-2 identity2;
  pone=f1/4;
  seed={1,0};
  powerOff[k_]:=2^k (identity2+k nzero/2);
  powerOn[k_]:=4^k pone;
  checksOff=Table[MatrixPower[f0,k]==powerOff[k],{k,1,24}];
  checksOn=Table[MatrixPower[f1,k]==powerOn[k],{k,1,24}];
  offSeed=Table[MatrixPower[f0,k].seed,{k,1,8}];
  onSeed=Table[MatrixPower[f1,k].seed,{k,1,8}];
  out=<|"originalPhysicalOff"->f0,
    "originalPhysicalOn"->f1,
    "offNilpotent"->nzero,
    "offNilpotentSquared"->nzero.nzero,
    "onNormalizedIdempotent"->pone,
    "onIdempotentSquared"->pone.pone,
    "onNormalizedRank"->MatrixRank[pone],
    "offCharacteristicPolynomial"->CharacteristicPolynomial[f0,x],
    "onCharacteristicPolynomial"->CharacteristicPolynomial[f1,x],
    "offPowersVerifiedN1to24"->And@@checksOff,
    "onPowersVerifiedN1to24"->And@@checksOn,
    "offOriginalSeedFirst8"->offSeed,
    "onOriginalSeedFirst8"->onSeed,
    "allPassed"->(
      nzero.nzero==ConstantArray[0,{2,2}] &&
      pone.pone==pone && MatrixRank[pone]==1 &&
      And@@checksOff && And@@checksOn)|>;
  out
]