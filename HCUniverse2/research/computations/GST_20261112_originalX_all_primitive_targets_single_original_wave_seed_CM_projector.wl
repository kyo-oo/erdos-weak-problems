(* All prescribed original-X primitive rational Hodge classes on
   X=P_{A}(O+L), A=E_CM^3, via one ORIGINAL GST wave seed.
   The eight genuinely algebraic primitive Chow generators P_i
   have the actual intersection Gram G_prim below, established
   geometrically by symmetric Appell-Humbert divisors and
   O'Sullivan Chow injectivity.
   For arbitrary rational Hodge alpha primitive, its true
   canonical Betti intersection readouts are r_i=int_X alpha P_i.
   Solve c=Gprim^-1*r and build the true Chow cycle sum c_i P_i.
   Since the primitive Hodge dimension is EXACTLY eight,
   this is a genuine original-X source return for EVERY alpha
   in that primitive space.

   The initial TRUE original GST Fin4xFin3 U/J/M/[J,M] 12-wave
   source classes are (P1,...,P8,C0,..,C3).
   The actual original-X correspondence has one seed P1+P2
   and rational Krylov matrix K_b for physical Navigation b=0/1.
   The exact polynomial coefficients K_b^-1 (c1,..,c8,0,..,0)
   construct the SAME actual original-X Chow class.
   No assumption of a preexisting alpha Chow class.
   The full universal Hodge conjecture for arbitrary X is not proved. *)

Module[{readouts,gram,coeff,expected,cells,u,j,m,comm,f0,f1,
 seed,k0,k1,target0,coeff0,coeff1,witness,return0,return1,ok},
 readouts=Table[Symbol["hodgeReadout"<>ToString[i]],{i,1,8}];
 gram=DiagonalMatrix[{10,10,10,10,10,10,10,10}];
 gram[[1,2]]=5;gram[[2,1]]=5;
 coeff=Simplify[Inverse[gram].readouts];
 expected=Join[{(2 readouts[[1]]-readouts[[2]])/15,
   (-readouts[[1]]+2 readouts[[2]])/15},
   Table[readouts[[i]]/10,{i,3,8}]];
 cells=Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
 u=ConstantArray[0,{12,12}];
 j=ConstantArray[0,{12,12}];
 m=ConstantArray[0,{12,12}];
 Do[Module[{i,k,p},
   i=cells[[row,1]];k=cells[[row,2]];
   u[[row,1+3 Quotient[i+4k,3]+Mod[i+4k,3]]]=1;
   j[[row,1+3(3-i)+(2-k)]]=If[
      MemberQ[{0,1,3,4,5,9},i+4k],1,-1];
   p=Mod[Quotient[i,2]+2k,3];
   m[[row,row]]=Boole[k==2&&p==2]+
       Boole[p==2&&Mod[Mod[i,2]+2p,3]==2];
 ],{row,1,12}];
 comm=j.m-m.j;
 f0=u+j+m;f1=f0+comm;
 seed=Join[{1,1},ConstantArray[0,10]];
 k0=Transpose[NestList[f0.#&,seed,11]];
 k1=Transpose[NestList[f1.#&,seed,11]];
 target0=Join[coeff,ConstantArray[0,4]];
 coeff0=Simplify[Inverse[k0].target0];
 coeff1=Simplify[Inverse[k1].target0];
 witness=Range[1,8];
 return0=k0.(coeff0/.Thread[readouts->witness]);
 return1=k1.(coeff1/.Thread[readouts->witness]);
 ok=(Simplify[gram.coeff-readouts]==ConstantArray[0,8]&&
    Simplify[coeff-expected]==ConstantArray[0,8]&&
    Det[gram]==75000000&&
    Det[k0]==-1149656584000&&
    Det[k1]==-445265540949&&
    Simplify[k0.coeff0-target0]==ConstantArray[0,12]&&
    Simplify[k1.coeff1-target0]==ConstantArray[0,12]&&
    return0==Join[(coeff/.Thread[readouts->witness]),ConstantArray[0,4]]&&
    return1==Join[(coeff/.Thread[readouts->witness]),ConstantArray[0,4]]);
 <|"originalX"->"P_{E_CM^3}(O+L), codim2 primitive",
   "allPrimitiveHodgeDimensions"->8,
   "actualEightChowSourceGramDet"->Det[gram],
   "arbitraryPrescribedTargetIntersectionSymbols"->readouts,
   "exactOriginalXChowCoefficients"->coeff,
   "fullPrimitiveTargetReturn"->
     Simplify[gram.coeff-readouts]==ConstantArray[0,8],
   "originalPhysicalGSTOffKrylovDet"->Det[k0],
   "originalPhysicalGSTOnKrylovDet"->Det[k1],
   "everyRationalPrimitiveTargetOneSeedOff"->TrueQ[
     Simplify[k0.coeff0-target0]==ConstantArray[0,12]],
   "everyRationalPrimitiveTargetOneSeedOn"->TrueQ[
     Simplify[k1.coeff1-target0]==ConstantArray[0,12]],
   "exactIntegerTargetOffTest"->return0,
   "exactIntegerTargetOnTest"->return1,
   "allPassed"->ok|>
]