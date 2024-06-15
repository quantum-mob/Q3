BeginPackage["Q3`"]

{ WickLogarithmicNegativity, WickTimeReversalMoment };

{ WickState, WickOperate,
  WickExpectation, WickGreensFunction };


Begin["`Private`"]

(**** <WickLogarithmicNegtivity> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[{grn,anm}, {k1,k2,\[Ellipsis]}] returns the fermionic negativity over modes k1, k2, \[Ellipsis] of the fermionic Gaussian states characterized by the Green's function grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickLogarithmicNegativity[grn, {k1,k2,\[Ellipsis]}] is equivalent to WickLogarithmicNegativity[{grn,0}, {k1,k2,\[Ellipsis]}]."

WickLogarithmicNegativity[kk:{__Integer}][any_] :=
  WickLogarithmicNegativity[any, kk]

WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}] :=
  WickTimeReversalMoment[1/2, grn, kk]

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := 
  WickTimeReversalMoment[1/2, {grn, anm}, kk]

(**** </WickLogarithmicNegtivity> ****)


(**** <WickTimeReversalMoment> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {grn,anm}, {k1,k2,\[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the Green's funciton grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn,0}, {k1,k2,\[Ellipsis]}]."

WickTimeReversalMoment::sing = "Matrix `` is singular; PseudoInverse is used instead of Inverse."


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
  ww = If[ ZeroQ[Det @ gg],
    Inverse[gg] - zz,
    PseudoInverse[gg] - zz
  ];

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


(**** <transformsObject> ****)

transformsObject /:
MakeBoxes[transformsObject[trs:{{_?MatrixQ, _?MatrixQ}..}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    "transformsObject", trs, None,
    { BoxForm`SummaryItem @ { "Number of Transformations: ", Length @ trs },
      BoxForm`SummaryItem @ { "Dimensions of each: ", Dimensions @ trs[[1, 1]] }
    },
    { BoxForm`SummaryItem @ { "Transformations: ", Map[MatrixObject, trs, {2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]

(**** </transformsObject> ****)


(**** <WickState> ****)

WickState::usage = "WickState[enc, trs, mat, {c1, c2, \[Ellipsis], cm}] represents a many-body state of m fermionic modes c1, c2, \[Ellipsis], cm in a structed data form."

WickState::trs = "Inconsistent transformations ``; each transformation must be specified either {mat, mat} or mat form."

WickState /:
MakeBoxes[vec:WickState[pp:{___?FermionQ}, mm:{{_?MatrixQ, _?MatrixQ}...}, ff_?MatrixQ, cc:{__?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", cc },
      BoxForm`SummaryItem @ { "Initial occupation: ", vec["Initial occupation"] }
    },
    { BoxForm`SummaryItem @ { "Encoded modes: ", pp },
      BoxForm`SummaryItem @ { "Transformations: ", transformsObject @ mm },
      BoxForm`SummaryItem @ { "Wick matrix: ", ff }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickState[pp_, mm_, ff_, cc_]["Encoded modes"] = pp

WickState[pp_, mm_, ff_, cc_]["Bare modes"] = cc

WickState[pp_, mm_, ff_, cc_]["Transformations"] = mm

WickState[pp_, mm_, ff_, cc_]["Wick matrix"] = ff

WickState[pp_, mm_, ff_, cc_]["Stages"] := Length[mm]

WickState[pp_, mm_, ff_, cc_]["Initial occupation"] :=
  ReplacePart[Table[0, Length @ cc], Thread[Cases[pp, _[1, k_, 1] -> k] -> 1]]


WickState[any___, Ket[a_Association]] := WickState[any, a]

WickState[pre___, op_Multiply, post___] := WickState[pre, List @@ op, post]


WickState[spec:({__?AnyFermionQ} | {_?MatrixQ, _?MatrixQ} | _?MatrixQ)..., aa_Association] :=
  Module[
    { cc = Keys[aa],
      enc, trs, mat },
    {enc, trs, mat} = getWickMatrix[cc][spec, Dagger @ Keys @ theKetTrim @ aa];
    WickState[enc, trs, mat, cc]
  ]

WickState[aa_Association] :=
  WickState[{}, {theNambuOne @ Length @ Keys @ aa}, {{}}, Keys @ aa] /; 
  Total[Values @ aa] == 0

WickState /:
Norm[ws_WickState] := Sqrt[Pfaffian[ws @ "Wick matrix"]]

(**** </WickState> ****)


(**** <WickOperate> ****)

WickOperate::usage = "WickOperate[{c1,c2,...,ck}, ws] returns the output state in the form of WickState upon applying c1**c2**...**ck on WickState ws.\nWickOperate[{u, v}, ws] returns the output state when applying the unitary operator specified by matrices {u, v}."

WickOperate[any_][ws_WickState] := WickOperate[any, ws]

WickOperate[msr_Measurement, ws_WickState] := msr[ws]

WickOperate[op:{__?AnyFermionQ}, WickState[{}, uu_, {{}}, cc:{__?FermionQ}]] :=
  Module[
    {enc, trs, mat},
    {enc, trs, mat} = getWickMatrix[cc][op, First @ uu];
    WickState[enc, trs, mat, cc]
  ]

WickOperate[op:{__?AnyFermionQ}, ws_WickState] :=
  Module[
    {enc, trs, mat},
    {enc, trs, mat} = getWickMatrix[cc][op, First @ uu];
    Echo["Here"];
    WickState[enc, trs, mat, cc]
  ]

WickOperate[trs:{_?MatrixQ, _?MatrixQ}, ws_WickState] :=
  Module[
    { pp = ws["Encoded modes"],
      uu = ws["Transformations"],
      vv },
    vv = theNambuDot[trs, Last @ uu];
    If[ Length[uu] > Max[First /@ pp],
      uu[[-1]] = vv,
      AppendTo[uu, vv]
    ];
    ReplacePart[ws, 2 -> uu]
  ]

(**** </WickOperate> ****)


(**** <Measurement> ****)

Measurement[c_?FermionQ][ws_WickState] := Module[
  { tt = ws["Stages"],
    cc = ws["Bare modes"],
    pp = ws["Encoded modes"],
    mm = ws["Transformations"],
    ff = ws["Wick matrix"],
    gg, dd, nn },

  nn = Length[pp] / 2;
  dd = theWickCode[cc][{c, Dagger @ c}, {tt}]; (* op := c ** Dagger[c] *)

  (* For the expectation value of c ** Dagger[c] *)
  {pp, mm, gg} = jamWickMatrix[dd, pp, mm, ff, nn];

  (* Simulate the measurement process. *)
  (* NOTE: WickState is unnormalized. *)
  If[ RandomReal[] < Chop[Pfaffian @ gg / Pfaffian @ ff],
    $MeasurementOut[c] = 0,
    $MeasurementOut[c] = 1;
    dd = Reverse @ dd;
    pp = ArrayPermute[pp, nn+1 <-> nn+2];
    gg = ArrayPermute[gg, nn+1 <-> nn+2];
    gg += SymmetrizedArray[{{nn+1, nn+2}->1}, Dimensions @ gg, Antisymmetric[{1,2}]]
  ];
  
  (* Construct the post-measurment state. *)
  {pp, mm, gg} = jamWickMatrix[dd, pp, mm, gg, nn];
  WickState[pp, mm, gg, cc]
]

(**** </Measurement> ****)


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[ws] represents an expectation value with respect to the Wick state ws.\nWickState[ws][{c1, c2, \[Ellipsis], cn}] returns the expectation value of c1 ** c2 ** \[Ellipsis] ** cn.\nWickState[ws][expr] returns the expectation value of a polynomial expr of fermion creation and annihilation operators.\nWickExpecation[spec] automatically converts spec to WickState; see WickState for details of spec."

WickExpectation[c_, any__, Ket[a_Association]] := WickExpectation[c, any, a]

WickExpectation[_?AnyFermionQ, any__, _Association] = 0


(* linearity *)

WickExpectation[spec___, Ket[a_Association]] :=
  WickExpectation[WickState[spec, a]]

WickExpectation[spec___, a_Association] :=
  WickExpectation[WickState[spec, a]]


WickExpectation[ws_WickState][z_?CommutativeQ] := z

WickExpectation[ws_WickState][z_?CommutativeQ op_] :=
  z * WickExpectation[ws][op]

WickExpectation[ws_WickState][expr_Plus] := 
  WickExpectation[ws] /@ expr


WickExpectation[ws_WickState][HoldPattern @ Multiply[ops__?AnyFermionQ]] :=
  WickExpectation[ws][{ops}]

WickExpectation[ws_WickState][ops:{__?AnyFermionQ}] := Module[
  { tt = ws["Stages"],
    cc = ws["Bare modes"],
    dd, pp, uv, mm, gg },
  dd = theWickCode[cc][ops, {tt}];
  {pp, uv, mm} = List @@ Most[ws];
  gg = Last @ jamWickMatrix[dd, pp, uv, mm, Length[pp]/2];
  Pfaffian[gg] / Pfaffian[mm]
]

(**** </WickExpectation> ****)


(**** <WickGreensFunction> ****)

WickGreensFunction::usage = "WickGreensFunction[ws] returns the pair {G, F} of normal Green's function G and anomalous Green's function F with respect to the Wick state ws."

WickGreensFunction[ws_WickState] := Module[
  { tt = ws["Stages"],
    cc = ws["Bare modes"],
    dd, pp, uv, mm, ff, gg, L, n, i, j },
  {pp, uv, mm} = List @@ Most[ws];

  n = Length[cc];
  L = Length[pp] / 2;

  (* Green's function *)
  gg = Flatten @ Table[
    dd = theWickCode[cc][{cc[[i]], Dagger @ cc[[j]]}, {tt}];
    {i, j} -> Pfaffian @ Last @ jamWickMatrix[dd, pp, uv, mm, L],
    {i, 1, n},
    {j, i, n}
  ];
  gg = SymmetrizedArray[gg, {n, n}, Hermitian @ {1, 2}];

  (* anomalous Green's function *)
  ff = Flatten @ Table[
    dd = theWickCode[cc][{cc[[i]], cc[[j]]}, {tt}];
    {i, j} -> Pfaffian @ Last @ jamWickMatrix[dd, pp, uv, mm, L],
    {i, 1, n},
    {j, i+1, n}
  ];
  ff = SymmetrizedArray[ff, {n, n}, Antisymmetric @ {1, 2}];

  Normal @ {gg, ff} / Pfaffian[mm]
]

(**** </WickGreensFunction> ****)


(**** <WickLogarithmicNegtivity> ****)

WickLogarithmicNegativity[dd:{__?FermionQ}][ws_WickState] :=
  WickLogarithmicNegativity[ws, dd]

WickLogarithmicNegativity[ws_WickState, dd:{__?FermionQ}] := Module[
  { gg = WickGreensFunction[ws],
    cc = Last[ws],
    kk },
  kk = dd /. Thread[cc -> Range[Length @ cc]];
  WickTimeReversalMoment[1/2, gg, kk]
]

(**** </WickLogarithmicNegtivity> ****)


(**** <getWickMatrix> ****)

getWickMatrix::usage = "getWickMatrix[{c1,c2,...}][spec] parse spec and create the Wick matrix."

getWickMatrix[cc_][pre___, aa:{_?MatrixQ, _?MatrixQ}, bb:{_?MatrixQ, v_?MatrixQ}.., Shortest[post___]] :=
  getWickMatrix[cc][pre, theNambuDot[aa, bb], post]

getWickMatrix[cc_][pre___, aa_?MatrixQ, bb__?MatrixQ, Shortest[post___]] :=
  getWickMatrix[cc][pre, Dot[aa, bb], post]

getWickMatrix[cc_][pre___, aa_?MatrixQ, post___] :=
  getWickMatrix[cc][pre, toNambuForm @ aa, post]

(* OUTPUT: {enc, trs, mat}
  enc: the list of encoded modes
  trs: the transformations of the encoded modes
  mat: the Wick matrix
  *)
getWickMatrix[cc:{__?FermionQ}][spec:({___?AnyFermionQ} | {_?MatrixQ, _?MatrixQ})...] :=
  Module[
    { trs = Cases[{spec}, {_?MatrixQ, _?MatrixQ}, {1}],
      enc = Flatten /@ SequenceSplit[{spec, {}}, {{_?MatrixQ, _?MatrixQ}}],
      mat, n, i, j },
    n = Length[cc];

    (* transformations *)
    If[ Length[Last @ enc] == 0,
      enc = Most[enc];
      trs = FoldList[theNambuDot[#2, #1]&, Reverse @ trs],
      trs = FoldList[theNambuDot[#2, #1]&, theNambuOne @ n, Reverse @ trs]
    ];

    (* encoded fermion modes *)
    enc = Flatten @ Reverse @ MapIndexed[theWickCode[cc], Reverse @ enc];
    enc = Join[dagWickCode @ enc, enc];

    n = Length[enc];
    mat = Flatten @ Table[
      {i, j} -> theWickContract[trs][enc[[i]], enc[[j]]],
      {i, n},
      {j, i+1, n}
    ];
    mat = SymmetrizedArray[mat, {n, n}, Antisymmetric[{1, 2}]];
    {enc, trs, mat}
  ]

(**** </getWickMatrix> ****)


(**** <jamWickMatrix> ****)

jamWickMatrix::usage = "jamWickMatrix[dd, pp, mm, mat, n] cleaves the Wick matrix mat at row and column n and add additional blocks with rows and columns corresponding to the new fermion modes dd."

(* INPUT
  dd : the list of new fermion modes to wedge into the Wick matrix mat.
  pp : the list of encoded fermion modes labeling the rows and columns of the Wick matrix mat
  mm : the list of transformations of fermion modes
  mat: the Wick matrix to updated
  n  : the row and column where the new modes to be wedged.
*)
(* NOTE: Both dd and pp are given in the form of encoded modes. *)
jamWickMatrix[ dd:{__?FermionQ}, (* encoded modes *)
  pp:{__?FermionQ}, mm:{{_?MatrixQ, _?MatrixQ}...},
  ff_SymmetrizedArray, n_Integer] := Module[
  { m = Length[dd],
    p1, p2, rr, ss, i, j },

  {p1, p2} = TakeDrop[pp, n];

  (* crack open the matrix. *)
  rr = Most[SymmetrizedArrayRules @ ff] /. {
      {i_, j_} /; i > n && j > n -> {i + m, j + m},
      {i_, j_} /; i > n -> {i + m, j},
      {i_, j_} /; j > n -> {i, j + m}
  };

  (* wedge additional blocks into the crack. *)
  ss = Flatten @ Table[
    {i, j+n} -> theWickContract[mm][p1[[i]], dd[[j]]],
    {i, n},
    {j, m}
  ];
  rr = Join[rr, ss];
  ss = Flatten @ Table[
    {i+n, j+n} -> theWickContract[mm][dd[[i]], dd[[j]]],
    {i, m},
    {j, i+1, m}
  ];
  rr = Join[rr, ss];
  ss = Flatten @ Table[
    {i+n, j+n+m} -> theWickContract[mm][dd[[i]], p2[[j]]],
    {i, m},
    {j, Length[pp] - n}
  ];
  rr = Join[rr, ss];

  (* Reconstruct the Wick matrix. *)
  { Join[p1, dd, p2], 
    mm,
    SymmetrizedArray[rr, Dimensions[ff] + {m, m}, Antisymmetric[{1, 2}]]
  }
]

(**** </jamWickMatrix> ****)


(**** <theWickContract> ****)

theWickContract::usage = "theWickContract[mm][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input: {level, species, sheer/dagger} *)
(* mm:{{_?MatrixQ, _?MatrixQ}..} *)
(* Convention: barc_i --> barU_{ij}barc_j with barU := {{U, V}, Conjugate @ {V, U}} *)

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 0], f_[j_, b_, 0]] :=
  Chop @ Dot[mm[[i, 1, a]], mm[[j, 2, b]]]

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 0], f_[j_, b_, 1]] :=
  Chop @ Dot[mm[[i, 1, a]], Conjugate @ mm[[j, 1, b]]]

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 1], f_[j_, b_, 0]] :=
  Chop @ Dot[Conjugate @ mm[[i, 2, a]], mm[[j, 2, b]]]

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 1], f_[j_, b_, 1]] :=
  Chop @ Dot[Conjugate @ mm[[i, 2, a]], Conjugate @ mm[[j, 1, b]]]

(**** </theWickContract> ****)


(**** <theWickCode> ****)

theWickCode::usage = "theWickCode[rules][{c1, c2, ...}, {time}] converts each fermion operator c[k] to {time, k, 0} and Dagger[c[k]] to {time, k, 1}.\nIntended to be used with MapIndexed."

(* output: {time, species, sheer/dagger} *)

theWickCode[rr_, t_Integer][c_?FermionQ] :=
  Head[c][t, ReplaceAll[c, rr], 0]

theWickCode[rr_, t_Integer][HoldPattern @ Dagger[c_?FermionQ]] :=
  Head[c][t, ReplaceAll[c, rr], 1]


theWickCode[ff:{___?FermionQ}] := 
 theWickCode[Thread[ff -> Range[Length @ ff]]]

theWickCode[rr_][cc:{___?AnyFermionQ}, {t_Integer}] :=
  Map[theWickCode[rr, t], cc]


dagWickCode::usage = "dagWickCode[...] ..."

dagWickCode[ff:{f_[_, _, _]...}] := Reverse @ Map[dagWickCode, ff]

dagWickCode[f_[t_, k_, d_]] := f[t, k, Mod[d+1, 2]]

(**** </theWickCode> ****)


(**** <theNambuDot> ****)

theNambuDot::usage = "theNambuDot[{u1,v1}, {u2,v2}] ..."

SetAttributes[theNambuDot, Flat]

theNambuDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

theNambuDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barc_i --> barU_{ij}barc_j with barU := {{U, V}, Conjugate @ {V, U}} *)


theNambuOne::usage = "theNambuOne[n] returns the pair {One[n], Zero[n,n]}."

theNambuOne[n_Integer] := {One @ n, Zero @ {n, n}}


toNambuForm::usage = "toNambuForm[mat] ..."

toNambuForm[m_?MatrixQ] := {m, Zero @ Dimensions @ m}

(**** </theNambuDot> ****)

End[]

EndPackage[]
