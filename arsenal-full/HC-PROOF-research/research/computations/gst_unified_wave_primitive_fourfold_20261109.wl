(* Exact GST unified Wave I/II + CM + primitive (P^1)^4 computation.
   All integers/rationals, no floating tolerance.
   The geometric test is an explicit projective fourfold whose
   primitive (2,2) classes are algebraic; this is an adapter test,
   not a claim that every fourfold has the same Hodge structure. *)
Module[{states,shuffle,mirror,sign,mid,final,survive,u,j,source,t,seed,
        krylov,choose2,choose3,lefs,poincare,primitive,gram,dual,
        wave0,wave1,rebuild,det12},
  states=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
  shuffle[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
  mirror[{c_,d_}]:={3-c,2-d};
  sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
  mid[c_,d_]:=Mod[Quotient[c,2]+2d,3];
  final[c_,d_]:=Mod[Mod[c,2]+2mid[c,d],3];
  survive[{c_,d_}]:=Boole[d==2&&mid[c,d]==2]+
                    Boole[mid[c,d]==2&&final[c,d]==2];
  u=Table[Boole[states[[q]]==shuffle[states[[r]]]],
    {r,12},{q,12}];
  j=Table[sign[states[[r]]]*
           Boole[states[[q]]==mirror[states[[r]]]],
    {r,12},{q,12}];
  source=DiagonalMatrix[survive/@states];
  t=u+j+source;
  seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@states;
  krylov=Transpose[Table[MatrixPower[t,k].seed,{k,0,11}]];
  det12=Det[krylov];

  (* X=(P^1)^4, d_i=hyperplane class of the i-th factor;
     d_i^2=0.  The basis of CH^2 is all 2-element index subsets. *)
  choose2=Subsets[Range[4],{2}];
  choose3=Subsets[Range[4],{3}];
  lefs=Table[Boole[SubsetQ[J,I]],{J,choose3},{I,choose2}];
  poincare=Table[Boole[Intersection[I,J]=={}],
    {I,choose2},{J,choose2}];
  primitive=NullSpace[lefs];
  gram=primitive.poincare.Transpose[primitive];
  dual=Inverse[gram].primitive.poincare;

  (* GST NShape with two holes at channels 0 and 1:
     eigenvalues 2 and 12, orbit vectors (1,1), (2,12). *)
  wave0=primitive[[1]]+primitive[[2]];
  wave1=2primitive[[1]]+12primitive[[2]];
  rebuild=Expand[({(12a-2b)/10,(b-a)/10}).{wave0,wave1}];

  <|
    "original_wave_12x12_Krylov_rank"->MatrixRank[krylov],
    "original_wave_12x12_Krylov_determinant"->det12,
    "CM_complex_structure_exact"->(j.j==-IdentityMatrix[12]),
    "wave_source_CM_curvature_nonzero"->(j.source!=source.j),
    "original_wave_source_readout_left_eigen"->With[
      {ell=UnitVector[12,1]-UnitVector[12,12]},ell.t==2ell],
    "primitive_codim2_basis_labels"->choose2,
    "L_to_H6_matrix"->lefs,
    "primitive_rank"->Length[primitive],
    "primitive_cycle_basis"->primitive,
    "primitive_cycles_killed_by_L"->(
      lefs.Transpose[primitive]==ConstantArray[0,{4,2}]),
    "intersection_gram"->gram,
    "intersection_gram_determinant"->Det[gram],
    "geometric_dual_on_frame"->dual.Transpose[primitive],
    "two_hole_wave_vandermonde_determinant"->Det[{{1,1},{2,12}}],
    "wave_zero_native_cycle"->wave0,
    "wave_one_native_cycle"->wave1,
    "wave_reconstructed_primitive_cycle"->rebuild,
    "wave_reconstruction_verified"->TrueQ[
      FullSimplify[rebuild==a primitive[[1]]+b primitive[[2]]]]
  |>
]
