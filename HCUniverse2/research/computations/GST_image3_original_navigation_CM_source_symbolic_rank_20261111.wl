(* ORIGINAL OWNER GST — symbolic navigation/source-strength theorem.
   Exact full 12-state U (x4/base3 shuffle), J (CM signed mirror),
   M (true Wave-I SURVIVE multiplicity), original mixed seed.
   No replacement physical operator and no arbitrary Hodge cycles.
   Mathematica exact polynomial arithmetic only.
   
   Mathematical theorem obtained:
     det Krylov(U+J+lambda M) = -4 lambda^2 (1+lambda)
                                   P8(lambda) P9(lambda).
   P8 has NO root mod 3 with leading coefficient 256 coprime to 3.
   P9 has NO root mod 13 with leading coefficient 640 coprime to 13.
   Rational Root Theorem => P8, P9 have NO rational root.
   Hence all rational lambda other than 0,-1 give cyclic rank 12.

   The code asserts the complete symbolic identity and modular
   certificates, not just tests at finitely many rational lambda.
*)
ClearAll[cc,idx,shuffle,mirror,sign,sourceMultiplicity,uu,jj,mm,
  sourceSeed,fold,fullKrylov,rawDet,expected,p8,p9,cert8,cert9,
  rankCases,result];
cc=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
idx[a_]:=First[FirstPosition[cc,a]];
shuffle[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mirror[{c_,d_}]:={3-c,2-d};
sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
sourceMultiplicity[{c_,d_}]:=Module[{mid=Mod[Quotient[c,2]+2d,3],fin},
 fin=Mod[Mod[c,2]+2mid,3];
 Boole[d==2]Boole[mid==2]+Boole[mid==2]Boole[fin==2]];
uu=Table[Boole[k==idx[shuffle[cc[[i]]]]],{i,12},{k,12}];
jj=Table[sign[cc[[i]]]*Boole[k==idx[mirror[cc[[i]]]]],{i,12},{k,12}];
mm=DiagonalMatrix[sourceMultiplicity/@cc];
sourceSeed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cc;
fold[z_]:=uu+jj+z mm;
fullKrylov[z_]:=Transpose[NestList[fold[z].#&,sourceSeed,11]];
p8[z_]:=411701+899200 z-342272 z^2-123812 z^3-
 14492 z^4-25296 z^5+4672 z^6-832 z^7+256 z^8;
p9[z_]:=12176+45312 z+72685 z^2+59539 z^3+
 15088 z^4-15320 z^5-13120 z^6-1376 z^7+1984 z^8+640 z^9;
rawDet=Det[fullKrylov[z]];
expected=-4 z^2(1+z)p8[z]p9[z];
cert8=Table[Mod[p8[k],3],{k,0,2}];
cert9=Table[Mod[p9[k],13],{k,0,12}];
rankCases=Table[<|"strength"->k,"rank"->MatrixRank[fullKrylov[k]],
 "det"->Det[fullKrylov[k]]|>,{k,{0,-1,1,2,1/2,-2}}];
result=<|"originalU5"->(MatrixPower[uu,5]==IdentityMatrix[12]),
 "originalJ2"->(jj.jj==-IdentityMatrix[12]),
 "originalUJcommute"->(uu.jj==jj.uu),
 "trueWaveSurviveSource"->(mm!=ConstantArray[0,{12,12}]),
 "symbolicDeterminantIdentity"->(Expand[rawDet-expected]===0),
 "polynomialDegree"->Exponent[rawDet,z],
 "factorP8"->p8[z],"factorP9"->p9[z],
 "P8LeadingCoefficient"->Coefficient[p8[z],z,8],
 "P9LeadingCoefficient"->Coefficient[p9[z],z,9],
 "P8Mod3Residues"->cert8,"P9Mod13Residues"->cert9,
 "P8NoRationalRootViaPrime3"->(
  Mod[Coefficient[p8[z],z,8],3]!=0 && FreeQ[cert8,0]),
 "P9NoRationalRootViaPrime13"->(
  Mod[Coefficient[p9[z],z,9],13]!=0 && FreeQ[cert9,0]),
 "navigationOffKrylovRank"->MatrixRank[fullKrylov[0]],
 "navigationOnKrylovRank"->MatrixRank[fullKrylov[1]],
 "navigationOnDet"->Det[fullKrylov[1]],
 "curvatureRank"->MatrixRank[jj.mm-mm.jj],
 "fixedSeedCurvatureValue"->((jj.mm-mm.jj).sourceSeed)[[idx[{3,2}]]],
 "rationalStrengthSpotChecks"->rankCases
|>;
result=Append[result,"allPassed"->(
 result["originalU5"]&&result["originalJ2"]&&result["originalUJcommute"]&&
 result["symbolicDeterminantIdentity"]&&
 result["P8NoRationalRootViaPrime3"]&&
 result["P9NoRationalRootViaPrime13"]&&
 result["navigationOffKrylovRank"]==10 &&
 result["navigationOnKrylovRank"]==12 &&
 result["navigationOnDet"]==-1149656584000 &&
 result["curvatureRank"]==6&&result["fixedSeedCurvatureValue"]==2)];
Print[result];result