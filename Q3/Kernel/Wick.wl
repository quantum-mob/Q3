BeginPackage["Q3`"]

{ WickLogarithmicNegativity, WickTimeReversalMoment };

{ WickState, WickHistory, WickOperate, WickUnitary,
  WickExpectation, WickGreensFunction };

{ WickRandomCircuit };

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
  pf = Check[Inverse[gg.xx], PseudoInverse[gg.xx]];
  pf = Power[Pfaffian[pf], 2];

  (* \Omega of the density operator \rho *)
  ww = Check[Inverse[gg] - zz, PseudoInverse[gg] - zz];

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
  ww = Check[Inverse[zz - off], PseudoInverse[zz - off]];
  ww = off + dgn . ww . dgn;
  pf = pf * Pfaffian[xx.(ww + zz)];

  (* effective \Gamma *)
  (* gg = Inverse[ww + zz]; *)
  gg = Check[Inverse[ww + zz], PseudoInverse[ww + zz]];
  (* effective Green's function Gij *)
  gg = CircleTimes[ThePauli[10], id] - gg;

  (* Recall the particle-hole symmetry. *)
  gg = Take[Eigenvalues @ gg, dd];
  Total[Log[2, Power[gg, alpha] + Power[1-gg, alpha]]] + Log[2, Power[pf, alpha]]
]

(**** </WickTimeReversalMoment> ****)


(**** <NambuTransforms> ****)

NambuTransforms /:
MakeBoxes[NambuTransforms[trs:{{_?MatrixQ, _?MatrixQ}..}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    "NambuTransforms", trs, None,
    { BoxForm`SummaryItem @ { "Number of Transformations: ", Length @ trs },
      BoxForm`SummaryItem @ { "Dimensions of each: ", Dimensions @ trs[[1, 1]] }
    },
    { BoxForm`SummaryItem @ { "Transformations: ", Map[MatrixObject, trs, {2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]

(**** </NambuTransforms> ****)


(**** <WickState> ****)

WickState::usage = "WickState[enc, trs, mat, {c1, c2, \[Ellipsis], cm}] represents a many-body state of m fermionic modes c1, c2, \[Ellipsis], cm in a structed data form."

WickState::trs = "Inconsistent transformations ``; each transformation must be specified either {mat, mat} or mat form."

WickState::frm = "No fermion modes in ``."

WickState /:
MakeBoxes[vec:WickState[pp:{___?FermionQ}, mm:{{_?MatrixQ, _?MatrixQ}...}, ff_?MatrixQ, cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", cc },
      BoxForm`SummaryItem @ { "Initial occupation: ", vec["Initial occupation"] }
    },
    { BoxForm`SummaryItem @ { "Encoded modes: ", pp },
      BoxForm`SummaryItem @ { "Transformations: ", NambuTransforms @ mm },
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


WickState[spec___, aa_Association] := (
  Message[WickState::frm, aa];
  WickState[{}, {{{{0}}, {{0}}}}, {{}}, {}] 
) /; Fermions[aa] == {}


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


(**** <WickHistory> ****)

WickHistory::usage = "WickHistory[ws, t] returns the past Wick state at stage t of the current Wick state ws.\nWickHistory[ws] returns all past states of the current Wick state ws."

WickHistory[ws_WickState] := Block[
  { t },
  Table[WickHistory[ws, t], {t, ws["Stages"]}]
]

WickHistory[ws_WickState, t_Integer] := Module[
  { dd, uu, mm, cc, rr, ss },
  {dd, uu, mm, cc} = List @@ ws;
  dd = Select[dd, First[#] <= t &];
  mm = cutWickMatrix[mm, Length[dd]/2];
  WickState[dd, Take[uu, UpTo[t]], mm, cc]
]

(**** </WickHistory> ****)


(**** <WickOperate> ****)

WickOperate::usage = "WickOperate[{c1,c2,...,ck}, ws] returns the output state in the form of WickState upon applying c1**c2**...**ck on WickState ws.\nWickOperate[{u, v}, ws] returns the output state when applying the unitary operator specified by matrices {u, v}."

Format[WickOperate[trs:{_?MatrixQ, _?MatrixQ}]] :=
  WickOperate[NambuTransforms @ trs]


WickOperate[any_][ws_WickState] := WickOperate[any, ws]


WickOperate[msr_Measurement, ws_WickState] := msr[ws]

WickOperate[trs_WickUnitary, ws_WickState] := trs[ws]

WickOperate[trs:{_?MatrixQ, _?MatrixQ}, ws_WickState] :=
  WickUnitary[trs][ws]


(* For the vacuum state *)
WickOperate[op:{__?AnyFermionQ}, WickState[{}, {uv_}, {{}}, cc:{__?FermionQ}]] :=
  Module[
    {enc, trs, mat},
    {enc, trs, mat} = getWickMatrix[cc][op, uv];
    WickState[enc, trs, mat, cc]
  ]

WickOperate[op:{__?AnyFermionQ}, ws_WickState] :=
  Module[
    { enc, trs, mat, dd },
    {enc, trs, mat} = List @@ Most[ws];
    dd = Join[Dagger @ Reverse @ op, op];
    dd = theWickCode[Last @ ws][dd, {Length @ trs}];
    {enc, trs, mat} = jamWickMatrix[dd, enc, trs, mat, Length[enc]/2];
    WickState[enc, trs, mat, Last @ ws]
  ]

(**** </WickOperate> ****)


(**** </WickUnitary> ****)

WickUnitary::usage = "WickUnitary[{u, v}] represents the unitary matrix ArrayFlatten[{{u, v}, Conjugate @ {v, u}}] in the Nambu space."

WickUnitary /:
MakeBoxes[op:WickUnitary[trs:{_?MatrixQ, _?MatrixQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Type: ", "Nambu" },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ trs }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[MatrixObject, trs] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]


WickUnitary[trs:{_?MatrixQ, _?MatrixQ}][ws_WickState] :=
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

(**** </WickUnitary> ****)


(**** <Measurement> ****)

Measurement[c_?FermionQ][ws_WickState] := Module[
  { tt = ws["Stages"],
    cc = ws["Bare modes"],
    aa = ws["Encoded modes"],
    uu = ws["Transformations"],
    mm = ws["Wick matrix"],
    bb, vv, nn,
    op, kk },
  kk = Length[aa] / 2;
  op = theWickCode[cc][{c, Dagger @ c}, {tt}]; (* op := c ** Dagger[c] *)

  (* For the expectation value of c ** Dagger[c] *)
  {bb, vv, nn} = jamWickMatrix[op, aa, uu, mm, kk];

  (* Simulate the measurement process. *)
  (* NOTE: WickState is unnormalized. *)
  If[ RandomReal[] < Chop[Pfaffian @ nn / Pfaffian @ mm],
    $MeasurementOut[c] = 0,
    $MeasurementOut[c] = 1;
    op = Reverse @ op;  (* op := Dagger[c] ** c *)
    {bb, vv, nn} = jamWickMatrix[op, aa, uu, mm, kk]
  ];

  (* PrintTemporary["Measurement outcome on mode ", c, ": ", $MeasurementOut[c]]; *)
  
  (* Construct the post-measurment state. *)
  {bb, vv, nn} = jamWickMatrix[op, bb, vv, nn, kk];
  WickState[bb, vv, nn, cc]
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
    aa, bb, pp, uv, mm, ff, gg, L, n, i, j },
  {pp, uv, mm} = List @@ Most[ws];

  n = Length[cc];
  L = Length[pp] / 2;

  (* encoded modes *)
  aa = theWickCode[cc][cc, {tt}];
  bb = dagWickCode /@ aa;

  (* Green's function *)
  gg = Flatten @ Table[
    {i, j} -> Pfaffian @ Last @ jamWickMatrix[{aa[[i]], bb[[j]]}, pp, uv, mm, L],
    {i, 1, n},
    {j, i, n}
  ];
  gg = SymmetrizedArray[gg, {n, n}, Hermitian @ {1, 2}];

  (* anomalous Green's function *)
  ff = Flatten @ Table[
    {i, j} -> Pfaffian @ Last @ jamWickMatrix[{aa[[i]], aa[[j]]}, pp, uv, mm, L],
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
  pp:{__?FermionQ}, uv:{{_?MatrixQ, _?MatrixQ}...}, mm_SymmetrizedArray,
  n_Integer] := Module[
  { m = Length[dd],
    p1, p2, rr, ss, i, j },

  {p1, p2} = TakeDrop[pp, n];

  (* crack open the matrix. *)
  rr = Most[SymmetrizedArrayRules @ mm] /. {
    {i_, j_} /; i > n && j > n -> {i + m, j + m},
    {i_, j_} /; i > n -> {i + m, j},
    {i_, j_} /; j > n -> {i, j + m}
  };

  (* wedge additional blocks into the crack. *)
  ss = Flatten @ Table[
    {i, j+n} -> theWickContract[uv][p1[[i]], dd[[j]]],
    {i, n},
    {j, m}
  ];
  rr = Join[rr, ss];
  ss = Flatten @ Table[
    {i+n, j+n} -> theWickContract[uv][dd[[i]], dd[[j]]],
    {i, m},
    {j, i+1, m}
  ];
  rr = Join[rr, ss];
  ss = Flatten @ Table[
    {i+n, j+n+m} -> theWickContract[uv][dd[[i]], p2[[j]]],
    {i, m},
    {j, Length[pp] - n}
  ];
  rr = Join[rr, ss];

  (* Reconstruct the Wick matrix. *)
  { Join[p1, dd, p2], 
    uv,
    SymmetrizedArray[rr, Dimensions[mm] + {m, m}, Antisymmetric[{1, 2}]]
  }
]

(**** </jamWickMatrix> ****)


(**** <cutWickMatrix> ****)

cutWickMatrix::usage = "cutWickMatrix[mat,k] takes the first and last k rows and columns of matrix mat."

cutWickMatrix[mat_SymmetrizedArray, k_Integer] := Module[
  { n = First[Dimensions@mat],
    rr },
  rr = Most@SymmetrizedArrayRules[mat];
  rr = Join[
    Normal @ KeySelect[rr, First[#] <= k && Last[#] <= k &],
    Normal @ KeySelect[rr, First[#] <= k && Last[#] > n-k &],
    Normal @ KeySelect[rr, First[#] > n-k && Last[#] > n-k &]
  ];
  rr = KeyReplace[ rr,
    { {i_, j_} /; i > n-k && j > n-k -> {i - n + 2*k, j - n + 2*k},
      {i_, j_} /; j > n-k -> {i, j - n + 2*k} }
  ];
  SymmetrizedArray[rr, {2 k, 2 k}, Antisymmetric@{1, 2}]
]

(**** </cutWickMatrix> ****)


(**** <theWickContract> ****)

theWickContract::usage = "theWickContract[mm][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input: {level, species, sheer/dagger} *)
(* mm:{{_?MatrixQ, _?MatrixQ}..} *)
(* Convention: barc_i --> barU_{ij}barc_j with barU := {{U, V}, Conjugate @ {V, U}} *)

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 0], f_[j_, b_, 0]] :=
  Dot[mm[[i, 1, a]], mm[[j, 2, b]]]

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 0], f_[j_, b_, 1]] :=
  Dot[mm[[i, 1, a]], Conjugate @ mm[[j, 1, b]]]

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 1], f_[j_, b_, 0]] :=
  Dot[Conjugate @ mm[[i, 2, a]], mm[[j, 2, b]]]

theWickContract[mm:{{_?MatrixQ, _?MatrixQ}..}][f_[i_, a_, 1], f_[j_, b_, 1]] :=
  Dot[Conjugate @ mm[[i, 2, a]], Conjugate @ mm[[j, 1, b]]]

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


(**** <WickRandomCircuit> ****)

WickRandomCircuit::usage = "WickRandomCircuit[{c1, c2, \[Ellipsis]}, wu, p, t] simulates a random quantum circuit of depth t, where layers of Wick unitary wu alternate with layers of measurements on fermion modes selected randomly from {c1, c2, \[Ellipsis]} with probability p."

Options[WickRandomCircuit] = {
  "Samples" -> 50,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "WRC"
}

WickRandomCircuit[cc_, uv:{_?MatrixQ, _?MatrixQ}, rest___] :=
  WickRandomCircuit[cc, WickUnitary @ uv, rest]

WickRandomCircuit[
  cc:{__?FermionQ},
  wu:WickUnitary[{_?MatrixQ, _?MatrixQ}], 
  p_?NumericQ, t_Integer, OptionsPattern[]] :=
Module[
  { k = 0,
    progress = 0,
    in, qc, data, n },
  PrintTemporary @ ProgressIndicator @ Dynamic[progress];

  (* initial state with half-filling *)
  n = Length[cc];
  in = PadRight[Riffle[Table[1, Floor[n/2]], Table[0, Floor[n/2]]], n];
  in = wu[WickState @ Ket[cc -> in]];

  (* quantum circuit with randomly selected measurements *)

  n = OptionValue["Samples"];
  data = Table[
    progress = ++k / n;
    qc = Riffle[Measurement /@ RandomPick[cc, p, t], wu];
    Fold[Construct[#2, #1]&, in, qc],
    n
  ];

  If[Not @ OptionValue["SaveData"], Return @ data];

  PrintTemporary["Saving the data (", ByteCount[data], " bytes) ..."]; 
  PrintTemporary["It may take some time."];
    
  file = OptionValue["Filename"];
  If[ file === Automatic,
    file = FileNameJoin @ {
      Directory[],
      ToString[Unique @ OptionValue @ "Prefix"]
    };
    file = StringJoin[file, ".mx"]
  ];

  If[OptionValue["Overwrite"] && FileExistsQ[file], DeleteFile @ file];

  Export[file, Association @ {"Times" -> tt, "Data" -> data}]
]

(**** </WickRandomCircuit> ****)


End[]

EndPackage[]
