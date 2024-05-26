BeginPackage["Q3`"]

{ WickState };

{ WickExpectation };

{ WickLogarithmicNegativity, WickTimeReversalMoment };

Begin["`Private`"]


(**** <WickState> ****)

WickState::usage = "WickState[spec, <|c1->n1, c2->n2, \[Ellipsis], cm->nm|>] represents a many-body state of a system of m fermionic modes c1, c2, \[Ellipsis], cm that initially occupy the modes with occupation number n1, n2, \[Ellipsis], nm.\nFor details of spec, see the Help documentation."

WickState /:
MakeBoxes[vec:WickState[spec:PatternSequence[PatternSequence[_?MatrixQ, {__?AnyFermionQ}]..., _?MatrixQ],aa_Association], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ {"Bare modes: ", Keys @ aa},
      BoxForm`SummaryItem @ {"Occupation: ", Values @ aa},
      BoxForm`SummaryItem @ {"Stages: ", (Length[{spec}]+1)/2}
    },
    { BoxForm`SummaryItem @ { "Transformations: ",
        Map[MatrixForm[#[[;;UpTo[4], ;;UpTo[4]]]]&, {spec}[[1;; ;;2]]] }
    },
    fmt, "Interpretable" -> Automatic ]

WickState /:
MakeBoxes[vec:WickState[spec:PatternSequence[PatternSequence[{_?MatrixQ, _?MatrixQ}, {__?AnyFermionQ}]..., {_?MatrixQ, _?MatrixQ}],aa_Association], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ {"Bare modes: ", Keys @ aa},
      BoxForm`SummaryItem @ {"Occupation: ", Values @ aa},
      BoxForm`SummaryItem @ {"Stages: ", (Length[{spec}]+1)/2}
    },
    { BoxForm`SummaryItem @ { "Transformations: ",
        Map[MatrixForm[#[[;;UpTo[4], ;;UpTo[4]]]]&, {spec}[[1;; ;;2]], {2}] }
    },
    fmt, "Interpretable" -> Automatic ]

WickState[any__, Ket[a_Association]] := WickState[any, a]

WickState[pre___, op_Multiply, post___] := WickState[pre, List @@ op, post]

(**** </WickState> ****)


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[expr, spec] calculates the expectation value of a polynomial of fermion creation and annihilation operators with respect to WickState[spec] efficiently based on the Wick theorem.\nFor details of spec, see WickState."

WickExpectation[c_, any__, Ket[a_Association]] := WickExpectation[c, any, a]

WickExpectation[_?AnyFermionQ, any__, _Association] = 0


(* linearity *)

WickExpectation[z_?CommutativeQ, any__, _Association] = z

WickExpectation[z_?CommutativeQ op_, any__, vec_] :=
  z * WickExpectation[op, any, vec]

WickExpectation[expr_Plus, any__, vec_] := 
  WickExpectation[#, any, vec]& /@ expr


WickExpectation[
  spec:PatternSequence[HoldPattern @ Multiply[__?AnyFermionQ], {_?MatrixQ, _?MatrixQ}].., 
  vv_Association
] :=
  theWickNambu[{spec} /. Multiply -> List, vv]

WickExpectation[spec:PatternSequence[{__?AnyFermionQ}, {_?MatrixQ, _?MatrixQ}].., vv_Association] :=
  theWickNambu[{spec}, vv]


WickExpectation[spec:PatternSequence[HoldPattern @ Multiply[__?AnyFermionQ], _?MatrixQ].., vv_Association] :=
  theWickFermi[{spec} /. Multiply -> List, vv]

WickExpectation[spec:PatternSequence[{__?AnyFermionQ}, _?MatrixQ].., vv_Association] :=
  theWickFermi[{spec}, vv]

(**** </WickExpectation> ****)


(**** <theWickNambu> ****)

theWickNambu::usage = "WickNambu[...] ... "

theWickNambu[ss:{PatternSequence[{__?AnyFermionQ}, {_?MatrixQ, _?MatrixQ}]..}, vv_Association] :=
  Module[
    { rr = Thread[Keys[vv] -> Range[Length @ vv]],
      id = One[Length @ vv],
      zr = Zero[Length @ vv, Length @ vv],
      bb, cc, ff, nn, mm },
    mm = FoldList[theNambuDot, {id, zr}, Reverse @ ss[[2;; ;;2]]];
    (* {level, species, sheer/dagger} *)
    cc = Append[ss[[1;; ;;2]], Dagger @ Keys[theKetTrim @ vv]];
    dd = Dagger @ Reverse @ Map[Reverse, Rest @ cc];
    cc = Catenate @ Reverse @ MapIndexed[theFermionCode, Reverse @ cc];
    dd = Catenate @ MapIndexed[theFermionCode, dd];
    ff = Join[dd, cc] /. rr;
    nn = Length[ff];
    ff = Table[
      {i, j} -> theNambuM[mm][ff[[i]], ff[[j]]],
      {i, nn},
      {j, i+1, nn}
    ];
    Pfaffian @ SymmetrizedArray[Flatten[ff, 1], {nn, nn}, Antisymmetric[{1, 2}]]
  ]


theNambuDot::usage = "theNambuDot[{u1,v1}, {u2,v2}] ..."

theNambuDot[{u1_, v1_}, {u2_, v2_}] :=
  {u1.u2 + Conjugate[v1].v2, v1.u2 + Conjugate[u1].v2}


theNambuM::usage = "theNambuM[mm][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input form: {level, species, sheer/dagger} *)
(* mm:{{_?MatrixQ, _?MatrixQ}..} *)

theNambuM[mm_][{i_, a_, 0}, {j_, b_, 0}] := Dot[mm[[i, 1]], Topple @ mm[[j, 2]]][[a, b]]

theNambuM[mm_][{i_, a_, 0}, {j_, b_, 1}] := Dot[mm[[i, 1]], Topple @ mm[[j, 1]]][[a, b]]

theNambuM[mm_][{i_, a_, 1}, {j_, b_, 0}] := Dot[mm[[i, 2]], Topple @ mm[[j, 2]]][[a, b]]

theNambuM[mm_][{i_, a_, 1}, {j_, b_, 1}] := Dot[mm[[i, 2]], Topple @ mm[[j, 1]]][[a, b]]

(**** </theWickNambu> ****)


(**** <theWickFermi> ****)

theWickFermi::usage = "WickFermi[...] ... "

theWickFermi[ss:{PatternSequence[{__?AnyFermionQ}, _?MatrixQ]..}, vv_Association] :=
  Module[
    { rr = Thread[Keys[vv] -> Range[Length @ vv]],
      id = One[Length @ vv],
      bb, cc, ff, nn, mm },
    mm = FoldList[Dot, id, Reverse @ ss[[2;; ;;2]]];
    (* {level, species, sheer/dagger} *)
    cc = Append[ss[[1;; ;;2]], Dagger @ Keys[theKetTrim @ vv]];
    dd = Dagger @ Reverse @ Map[Reverse, Rest @ cc];
    cc = Catenate @ Reverse @ MapIndexed[theFermionCode, Reverse @ cc];
    dd = Catenate @ MapIndexed[theFermionCode, dd];
    ff = Join[dd, cc] /. rr;
    nn = Length[ff];
    ff = Table[
      {i, j} -> theFermiM[mm][ff[[i]], ff[[j]]],
      {i, nn},
      {j, i+1, nn}
    ];
    Pfaffian @ SymmetrizedArray[Flatten[ff, 1], {nn, nn}, Antisymmetric[{1, 2}]]
  ]


theFermionCode::usage = "theFermionCode[...] ..."

theFermionCode[cc:{__?AnyFermionQ}, {k_Integer}] :=
  theFermionCode[#, k]& /@ cc

theFermionCode[c_?FermionQ, k_Integer] := {k, c, 0}

theFermionCode[HoldPattern @ Dagger[c_?FermionQ], k_Integer] := {k, c, 1}


theFermiM::usage = "theFermiM[mat][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input: {level, species, sheer/dagger} *)
theFermiM[mm_][{_, _, 1}, {_, _, _}] = 0

theFermiM[mm_][{_, _, 0}, {_, _, 0}] = 0

theFermiM[mm:{__?MatrixQ}][{i_, a_, 0}, {j_, b_, 1}] := Dot[mm[[i]], Topple @ mm[[j]]][[a, b]]

(**** </theWickFermi> ****)


(**** <WickLogarithmicNegtivity> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[{grn,anm}, {k1,k2,\[Ellipsis]}] returns the fermionic negativity over modes k1, k2, \[Ellipsis] of the fermionic Gaussian states characterized by the Green's function grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickLogarithmicNegativity[grn, {k1,k2,\[Ellipsis]}] is equivalent to WickLogarithmicNegativity[{grn,0}, {k1,k2,\[Ellipsis]}]."

WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}] :=
  WickTimeReversalMoment[1/2, grn, kk]

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := 
  WickTimeReversalMoment[1/2, {grn, anm}, kk]

(**** </WickLogarithmicNegtivity> ****)


(**** <WickTimeReversalMoment> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {grn,anm}, {k1,k2,\[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the Green's funciton grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn,0}, {k1,k2,\[Ellipsis]}]."

WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}] :=
  WickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk]

WickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { dd = Length[grn],
    gg, zr, id, xx, zz, uu, ww, pf, dgn, off
  },
  zr = Zero[dd, dd];
  id = One[dd];
  xx = CircleTimes[ThePauli[1], id];
  zz = CircleTimes[ThePauli[3], id];
  
   (* \Gamma *)
   gg = ArrayFlatten @ {
    {id - grn, anm},
    {Topple @ anm, Transpose[grn] - id}
  };
  pf = Power[Pfaffian[Inverse[gg.xx]], 2];

  (* \Omega of the density operator \rho *)
  ww = Inverse[gg] - zz;

  uu = SparseArray[
    Flatten @ {
      Thread[Transpose@{kk, dd + kk} ->  I],
      Thread[Transpose@{dd + kk, kk} -> -I],
      Thread[Transpose@{kk, kk} -> 0],
      Thread[Transpose@{dd + kk, dd + kk} -> 0],
      {i_, i_} -> 1,
      {_, _} -> 0
    },
    {2*dd, 2*dd}
  ];
  (* \Omega of partial TR *)
  ww = Topple[uu] . ww . uu;

  dgn = CirclePlus[ww[[;;dd, ;;dd]], ww[[dd+1;;, dd+1;;]]];
  off = ArrayFlatten @ {
    {zr, ww[[;;dd, dd+1;;]]},
    {ww[[dd+1;;, ;;dd]], zr}
  };
  pf = Pfaffian[(off - zz).xx] / pf;

  (* effective \Omega of \Xi *)
  ww = off + dgn . Inverse[zz - off] . dgn;
  pf = pf * Pfaffian[xx.(ww + zz)];

  (* effective \Gamma *)
  gg = Inverse[ww + zz];
  (* effective Green's function Gij *)
  gg = CircleTimes[ThePauli[10], id] - gg;

  (* Recall the particle-hole symmetry. *)
  gg = Take[Eigenvalues @ gg, dd];
  Total[Log[2, Power[gg, alpha] + Power[1-gg, alpha]]] + Log[2, Power[pf, alpha]]
]

(**** </WickTimeReversalMoment> ****)


End[]

EndPackage[]
