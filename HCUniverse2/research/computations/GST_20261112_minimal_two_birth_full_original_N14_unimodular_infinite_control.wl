(* OWNER GST FULL NATIVE 12-CELL UNCONDITIONAL TWO-WORLD BIRTH:
   This is a MATHEMATICALLY NEW integral native extension of the actual
   U,J,M,[J,M] source, not a proof of canonical Chow algebraicity.
   Definitions copied literally from established original source.
   No input cycle on other fibers, no conditional Chow theorem.
   Smith: physical off {1^10,4,4}; on {1^10,3,0}.
   At primes 2 and 3 respectively the 12-core mod-p ranks are 10.
   Hence any integral unimodular EXTENSION fixing the original core
   must adjoin >= TWO auxiliary source directions.
   Explicit E injection to the last two Smith coordinates constructs
   a 14 x 14 unimodular integer block extension without editing any of
   the original 12 x 12 coefficients.
   The original mixed seed extended by ZERO in both new channels
   is full-rank Krylov cyclic in both physical Navigation states.
   Thus any finite positive or negative iterate is an integer lattice
   automorphism, with exact determinant 1. This does not give algebraic
   cycles on an arbitrary original smooth projective X: that requires
   an independent geometric realization map not assumed here.
*)

GSTOrigXCells = Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
GSTOrigXIdx[z_] := First[FirstPosition[GSTOrigXCells,z]];
GSTOrigXShuffle[{i_,k_}] := {Quotient[i+4*k,3],Mod[i+4*k,3]};
GSTOrigXMirror[{i_,k_}] := {3-i,2-k};
GSTOrigXSign[{i_,k_}] := If[MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
GSTOrigXSurvive[{i_,k_}] := Module[{p=Mod[Quotient[i,2]+2*k,3],q},
  q=Mod[Mod[i,2]+2*p,3];
  Boole[k==2]Boole[p==2] + Boole[p==2]Boole[q==2]];
GSTOrigXU = Table[
  Boole[z==GSTOrigXIdx[GSTOrigXShuffle[GSTOrigXCells[[i]]]]],
  {i,12},{z,12}];
GSTOrigXJ = Table[
  GSTOrigXSign[GSTOrigXCells[[i]]]*
   Boole[z==GSTOrigXIdx[GSTOrigXMirror[GSTOrigXCells[[i]]]]],
  {i,12},{z,12}];
GSTOrigXM = DiagonalMatrix[GSTOrigXSurvive/@GSTOrigXCells];
GSTOrigXC = GSTOrigXJ.GSTOrigXM-GSTOrigXM.GSTOrigXJ;
GSTOrigXSeed = Boole[MemberQ[{{0,0},{0,1}},#]]&/@GSTOrigXCells;
GSTOrigXKrylov[t_,v_,n_] := Transpose[NestList[t.#&,v,n-1]];

Module[{seed,all},
seed=Join[GSTOrigXSeed,{0,0}];
all=Table[Module[{F,smith,left,D,right,E,B,C,G,krylov,prime,red},
 F=GSTOrigXU+GSTOrigXJ+GSTOrigXM+charge GSTOrigXC;
 smith=SmithDecomposition[F];
 {left,D,right}=smith;
 E=Join[ConstantArray[0,{10,2}],IdentityMatrix[2]];
 B=Inverse[left].E;
 C=Transpose[E].Inverse[right];
 G=ArrayFlatten[{{F,B},{C,ConstantArray[0,{2,2}]}}];
 prime=If[charge==0,2,3];
 red=RowReduce[Mod[F,prime],Modulus->prime];
 krylov=GSTOrigXKrylov[G,seed,14];
 <|"physicalCharge"->charge,
   "originalCoreDet"->Det[F],
   "originalSmithInvariants"->Diagonal[D],
   "rankModuloObstructingPrime"->Length[Select[red,#!=ConstantArray[0,12]&]],
   "obstructingPrime"->prime,
   "minimalNewWorldCount"->2,
   "smithFactorizationExact"->(left.F.right==D),
   "nativeExtensionSize"->Dimensions[G],
   "unmodifiedOriginalGSTCore"->G[[1;;12,1;;12]]==F,
   "newChannels"->2,
   "newNativeOperatorIntegral"->And@@(IntegerQ/@Flatten[G]),
   "newNativeInverseIntegral"->And@@(IntegerQ/@Flatten[Inverse[G]]),
   "newNativeDet"->Det[G],
   "originalSeedZeroExtraKrylovDet"->Det[krylov],
   "originalSeedIsFull14Cyclic"->Det[krylov]!=0,
   "allFiniteInversePowersCheck"->And@@Table[
    MatrixPower[G,t].MatrixPower[G,-t]==IdentityMatrix[14],
    {t,0,6}]|>],{charge,{0,1}}];
<|"originalU5"->MatrixPower[GSTOrigXU,5]==IdentityMatrix[12],
"originalJ2"->GSTOrigXJ.GSTOrigXJ==-IdentityMatrix[12],
"physicalStates"->all,
"allPassed"->(
 And@@Lookup[all,"smithFactorizationExact"] &&
 And@@Lookup[all,"unmodifiedOriginalGSTCore"] &&
 And@@Lookup[all,"newNativeOperatorIntegral"] &&
 And@@Lookup[all,"newNativeInverseIntegral"] &&
 And@@Lookup[all,"originalSeedIsFull14Cyclic"] &&
 And@@Lookup[all,"allFiniteInversePowersCheck"] &&
 Lookup[all,"newNativeDet"]=={1,1} &&
 Lookup[all,"rankModuloObstructingPrime"]=={10,10} &&
 Lookup[all,"originalSeedZeroExtraKrylovDet"]==
 {-823658646480,14979092529})|>
]
