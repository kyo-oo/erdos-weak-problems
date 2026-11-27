(* Exact finite tests for the theorem on connected GST (Z/2)^(p-1)
   free multiverse quotient and the deck-neutral mixed spectral source.
   Date 2026-10-24. A finite-rank character check; general proof is
   in GST_nonlinear_antideck_chow_source_birth_2026-10-22.tex. *)
ClearAll[p, group, chars, products, vals, tests, ix];
tests=Table[
 Module[{group,character,neutral,nontrivial,free,transfer,expected},
  group=Tuples[{0,1},p-1];
  character=Function[{g,i},
     If[i<p,(-1)^g[[i]],(-1)^Total[g]]];
  neutral=And@@Table[
     Product[character[g,i],{i,1,p}]==1,
     {g,group}];
  nontrivial=And@@Table[
     Sort[DeleteDuplicates[Table[character[g,i],{g,group}]]]=={-1,1},
     {i,1,p}];
  free=And@@Table[
     (Total[g]==0)||(Count[Table[character[g,i],{i,1,p}],-1]>=1),
     {g,group}];
  transfer=(-2)^p Total[Table[Product[character[g,i],{i,1,p}],{g,group}]];
  expected=(-1)^p 2^(2p-1);
  <|"p"->p,"order"->Length[group],
    "characterNeutral"->neutral,
    "allDegreeTwoCharactersNontrivial"->nontrivial,
    "freeActionTest"->free,
    "cohomologyTransferCorrect"->(transfer==expected),
    "actualCoefficient"->transfer|>],
 {p,2,9}];
Print["CHARACTER_TESTS=",tests];
Print["ALL_TRUE=",And@@Flatten[
 Table[{tests[[ix,"characterNeutral"]],
   tests[[ix,"allDegreeTwoCharactersNontrivial"]],
   tests[[ix,"freeActionTest"]],
   tests[[ix,"cohomologyTransferCorrect"]]},
   {ix,Length[tests]}]]];
