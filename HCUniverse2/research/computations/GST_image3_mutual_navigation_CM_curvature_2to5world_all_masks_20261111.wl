(* GST ORIGINAL-WAVE MUTUAL SOURCE NAVIGATION — exact deterministic certificate.
   User's OWN operators: U^5=I physical carry/trit shuffle,
   J^2=-I signed CM mirror, M original SURVIVE, original seed,
   Wave-II N-hole addressing 10 (i-1). No invented Hodge cycles.

   New bidirectional neighbor source transport:
     F_ij = delta_ij (U+J+k_i M+10(i-1) I)
            + delta_(|i-j|,1) M.
   k_i is the ORIGINAL physical Navigation gate {0,1}.
   For ALL binary masks h=2,3,4,5, the exact 12h Krylov
   determinant is nonzero mod 1009 or mod 1013. This
   rigorously certifies rank 12h over Q IN THESE FINITE CASES.
   This does not prove arbitrary h or original-X Chow realization.

   Audit: "off" all masks h=2 against U,J,I and source M,
   plus two original annihilator detectors and their transverse
   2x2 minor under M and CM curvature [J,M].
*)
ClearAll[cells,idx,sh,mirror,sgn,src,UU,JJ,MM,seed,id,z,
  physicalFold,kr,cert,mm,checks,records,baseK,read,
  born,curv,noGo,ablation,summary];

cells=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
idx[a_]:=First[FirstPosition[cells,a]];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mirror[{c_,d_}]:={3-c,2-d};
sgn[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
src[{c_,d_}]:=Module[{a=Mod[Quotient[c,2]+2d,3],b},
 b=Mod[Mod[c,2]+2a,3];
 Boole[d==2]Boole[a==2]+Boole[a==2]Boole[b==2]];
UU=Table[Boole[k==idx[sh[cells[[i]]]]],{i,12},{k,12}];
JJ=Table[sgn[cells[[i]]]*Boole[k==idx[mirror[cells[[i]]]]],{i,12},{k,12}];
MM=DiagonalMatrix[src/@cells];
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
id=IdentityMatrix[12];z=ConstantArray[0,{12,12}];

physicalFold[mask_List,offDiag_]:=Module[{h=Length[mask]},
 ArrayFlatten[Table[
   If[i==k,UU+JJ+mask[[i]]MM+10(i-1)id,
     If[Abs[i-k]==1,offDiag,z]],
     {i,h},{k,h}]]];
kr[fold_,vec_,prime_Integer]:=
  Transpose[NestList[Mod[fold.#,prime]&,vec,Length[vec]-1]];
cert[mask_List]:=Module[{T,v,K,a,b},
 T=physicalFold[mask,MM];
 v=Flatten[ConstantArray[seed,Length[mask]]];
 K=kr[T,v,1009];a=Det[K,Modulus->1009];
 b=If[a==0,Det[kr[T,v,1013],Modulus->1013],Missing["not needed"]];
 <|"mask"->mask,"h"->Length[mask],"detMod1009"->a,
 "detMod1013IfNeeded"->b,"certified"->(a!=0 || b=!=0)|>];
records=Flatten[Table[cert/@Tuples[{0,1},h],{h,2,5}],1];

baseK=Transpose[NestList[(UU+JJ).#&,seed,11]];
read={{0,0,-1,0,0,0,-1,-1,-1,0,-1,1},
 {-1,1,0,1,1,1,0,0,0,1,0,0}};
curv=JJ.MM-MM.JJ;
noGo=<|"oldRank"->MatrixRank[baseK],
 "dualKillOld"->(read.baseK==ConstantArray[0,{2,12}]),
 "UStable"->(read.UU.baseK==ConstantArray[0,{2,12}]),
 "JStable"->(read.JJ.baseK==ConstantArray[0,{2,12}]),
 "MTransverseMinor"->Det[(read.MM.baseK)[[All,{2,5}]]],
 "CMCurvatureTransverseMinor"->Det[(read.curv.baseK)[[All,{1,2}]]]|>;
ablation=Map[Function[pair,
 Module[{name=pair[[1]],op=pair[[2]],T,v},
  T=physicalFold[{0,0},op];v=Join[seed,seed];
  <|"cross"->name,"rankMod1009"->
    MatrixRank[kr[T,v,1009],Modulus->1009]|>]],
 {{"none",z},{"I",id},{"U",UU},{"J",JJ},
 {"U+J",UU+JJ},{"M",MM},{"CM",curv}}];

summary=<|"countMasks"->Length[records],
 "certifiedAll"->And@@(Lookup[records,"certified"]),
 "exceptionalMod1009Cases"->Select[records,#detMod1009==0&],
 "caseCountByH"->Table[{h,Count[records,r_/;r["h"]==h]},{h,2,5}],
 "nativeNoGoAndCurvatureWitnesses"->noGo,
 "twoWorldAllOffAblation"->ablation,
 "allPassed"->(And@@(Lookup[records,"certified"]) &&
   noGo["oldRank"]==10&&noGo["dualKillOld"]&&
   noGo["UStable"]&&noGo["JStable"]&&
   noGo["MTransverseMinor"]==-2&&
   noGo["CMCurvatureTransverseMinor"]==4)|>;
Print[summary];summary
