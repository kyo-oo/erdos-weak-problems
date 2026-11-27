Module[{q,u,g,h,k,v,r,energy,checks,scaled,signchecks,sigma,sg,period,bi,idx,e},
q=DiagonalMatrix[{3,5,7}];
u={{1,0},{1,1},{0,1}};
g=Transpose[u].q.u;
h=Simplify[u.Inverse[g].Transpose[u].q];
k=IdentityMatrix[3]-h;
v={a,b,c};
r=Simplify[k.v];
energy=Factor[r.q.r];
checks={
 Simplify[h.h==h],
 Simplify[k.k==k],
 Simplify[h.k==ConstantArray[0,{3,3}]],
 Simplify[k.u==ConstantArray[0,{3,2}]],
 Simplify[Transpose[u].q.r=={0,0}],
 Simplify[energy==105 (a-b+c)^2/71],
 Simplify[Inverse[g].g.Inverse[g]==Inverse[g]],
 Simplify[(Transpose[v].q.h.v)==(Transpose[u].q.v).Inverse[g].(Transpose[u].q.v)]
};
scaled={
 Simplify[(e q).h==e q.h],
 Simplify[u.Inverse[e g].Transpose[u].(e q)==h,Assumptions->e>0],
 Simplify[r.(e q).r==e energy,Assumptions->e>0]
};
signchecks=Flatten[Table[
 sigma=(-1)^(m+p+1);
 sg=sigma q;
 period=Transpose[u].sg.v;
 bi=(-1)^p period;
 idx=Expand[(-1)^m (v.sg.((-1)^p v)-bi.Inverse[sigma g].period)];
 Simplify[-idx==energy],
 {p,1,6},{m,2p+1,2p+3}
]];
<|"Version"->$Version,"Field"->"Q(a,b,c,e), e>0 only for degree interpretation",
"FrameGram"->g,"FrameDeterminant"->Det[g],
"Projection"->h,"ResidualProjection"->k,
"ResidualEnergy"->energy,
"ProjectorAndSchurChecks"->checks,
"AlterationChecks"->scaled,
"ParityCasesTested"->Length[signchecks],"AllParityChecks"->And@@signchecks,
"OutsideFrameResidualEnergy"->(energy/.{a->1,b->0,c->0}),
"K3M5P2DiagonalIndex"->((-1)^5*21),
"FullFrameResidualEnergy"->Simplify[(v-IdentityMatrix[3].v).q.(v-IdentityMatrix[3].v)],
"NativePartialTraceResidualPeriod"->Simplify[r.q.k.{x,y,z}==r.q.{x,y,z}],
"PartialTracePreservesInvisibleInput"->Simplify[r.q.k.u.{x,y}==0],
"ResidualNormPositiveExample"->(energy/.{a->1,b->0,c->0})>0|>
]
