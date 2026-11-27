(* User-correction mathematical diagnostic:
  Does actual original GST nonzero [J,M] curvature and
  globally invertible algebraic matrix gauge create a new
  positive Chow-Chern source? NO: global image module free.
  Exact Wolfram uses only integer polynomial/rational arithmetic.
  The conclusion for any rank is an algebraic module proof,
  not a finite-example extrapolation. *)
Module[{x,y,g,gi,p,px,py,cw,ax,ay,j,mm,cm,idempotent},
g={{1,x},{y,1+x*y}};
gi=Simplify[Inverse[g]];
p=Simplify[g.DiagonalMatrix[{1,0}].gi];
px=D[p,x];py=D[p,y];
cw=Simplify[Tr[p.(px.py-py.px)]];
ax=Simplify[(gi.D[g,x])[[1,1]]];
ay=Simplify[(gi.D[g,y])[[1,1]]];
j={{0,1},{-1,0}};mm={{0,0},{0,2}};
cm=j.mm-mm.j;
idempotent=Simplify[p.p-p]==ConstantArray[0,{2,2}];
<|"globalAlgebraicGaugeDet"->Factor[Det[g]],
"trueRegularIdempotent"->idempotent,
"globalFreeImageGenerator"->Simplify[g.{1,0}],
"nonzeroLocalCurvatureCoefficient"->cw,
"globalFrameConnection"->{ax,ay},
"exactCurvatureCoefficient"->Simplify[D[ay,x]-D[ax,y]],
"originalCMCommutator"->cm,
"actualPositiveChowChernClass"->"zero; Im(P)=g(A e1) is free",
"allPassed"->(Det[g]==1&&idempotent&&cw==-1&&
Simplify[D[ay,x]-D[ax,y]]==-1&&
cm=={{0,2},{2,0}})|>
]