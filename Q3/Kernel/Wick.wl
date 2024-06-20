BeginPackage["Q3`"]

{ WickLogarithmicNegativity, WickTimeReversalMoment };

{ WickState, WickHistory, WickOperator, WickUnitary,
  WickExpectation, WickGreensFunction };

{ WickCircuit, WickRandomCircuit };

{ WickEntanglementEntropy };
{ QuantumLog }; (* mainly in vonNeumann.wl *)

Begin["`Private`"]

(**** <WickTimeReversalMoment> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {grn,anm}, {k1,k2,\[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the Green's funciton grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn,0}, {k1,k2,\[Ellipsis]}]."

WickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[WickTimeReversalMoment] = { "Epsilon" -> 1.25*^-5 } (* 1.0*^-8 is also a reasonable choice *)


WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  WickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk, opts]

WickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, OptionsPattern[]] := Module[
  { dd = Length[grn],
    gg, oo, id, xx, zz, uu, ww, pf, dgn, off
  },
  oo = Zero[dd, dd];
  id = One[dd];
  xx = CircleTimes[ThePauli[1], id];
  zz = CircleTimes[ThePauli[3], id];

  (* \Gamma *)
  gg = id - grn;
  Check[
    Inverse @ gg,
    Message[WickTimeReversalMoment::sing];
    gg = tameMatrix[gg, OptionValue["Epsilon"]]
  ];
  gg = ArrayFlatten @ {
    {gg, anm},
    {Topple @ anm, -Transpose[gg]}
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
    {oo, ww[[;;dd, dd+1;;]]},
    {ww[[dd+1;;, ;;dd]], oo}
  };
  pf = Check[
    Pfaffian[(off - zz).xx] / pf, 
    Message[WickTimeReversalMoment::infy];
    PseudoDivide[Pfaffian[(off - zz).xx], pf],
    Power::infy
  ];

  (* effective \Omega of \Xi *)
  ww = Inverse[zz - off];
  ww = off + dgn . ww . dgn;
  pf = pf * Pfaffian[xx.(ww + zz)];

  (* effective \Gamma *)
  gg = Inverse[ww + zz];
  (* effective Green's function Gij *)
  gg = CircleTimes[ThePauli[10], id] - gg;

  (* Recall the particle-hole symmetry. *)
  gg = Take[Eigenvalues @ gg, dd];
  Total[Log[2, Power[gg, alpha] + Power[1-gg, alpha]]] + Log[2, Power[pf, alpha]]
]


(* NOtE: mat is supposed to be Hermitian. *)
tameMatrix[mat_?MatrixQ, eps_] := Module[
  {val, vec},
  {val, vec} = Eigensystem[mat];
  val = val /. {x_?(ZeroQ[#, eps] &) :> x + 1.25*eps};
  Transpose[vec] . DiagonalMatrix[val] . Conjugate[vec]
]

(**** </WickTimeReversalMoment> ****)


(**** <WickLogarithmicNegtivity> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[{grn,anm}, {k1,k2,\[Ellipsis]}] returns the fermionic negativity over modes k1, k2, \[Ellipsis] of the fermionic Gaussian states characterized by the Green's function grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickLogarithmicNegativity[grn, {k1,k2,\[Ellipsis]}] is equivalent to WickLogarithmicNegativity[{grn,0}, {k1,k2,\[Ellipsis]}]."

Options[WickLogarithmicNegativity] = Options[WickTimeReversalMoment]


WickLogarithmicNegativity[kk:{__Integer}][any_] :=
  WickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, grn, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(**** </WickLogarithmicNegtivity> ****)


(**** <NambuMatrices> ****)

NambuMatrices /:
MakeBoxes[NambuMatrices[trs:{{_?MatrixQ, _?MatrixQ}..}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    "NambuMatrices", trs, None,
    { BoxForm`SummaryItem @ { "Number of Transformations: ", Length @ trs },
      BoxForm`SummaryItem @ { "Dimensions of each: ", Dimensions @ trs[[1, 1]] }
    },
    { BoxForm`SummaryItem @ { "Transformations: ", Map[MatrixObject, trs, {2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]

(**** </NambuMatrices> ****)


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
      BoxForm`SummaryItem @ { "Transformations: ", NambuMatrices @ mm },
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
    {enc, trs, mat} = wmBuild[cc][spec, Dagger @ Keys @ theKetTrim @ aa];
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
  mm = wmTake[mm, Length[dd]/2];
  WickState[dd, Take[uu, UpTo[t]], mm, cc]
]


WickHistory[{wc_WickCircuit, ws_WickState}] := Module[
  { cc, id, new, n },
  cc = Cases[First @ ws, c_[1, k_, 1] -> c[1, k, _], 1];
  id = WickUnitary @ theNambuOne[Length @ Last @ ws];
  new = FoldList[wcEvent, {cc, {id}}, First @ wc];
  wsClone[ws] /@ new
]


wsClone[ws_WickState][{enc_, trs_}] := Module[
  { dd, mm, n },
  dd = Cases[First @ ws, Alternatives @@ enc];
  n = Length[dd] / 2;
  mm = wmTake[ws[[3]], n];
  WickState[dd, trs /. {WickUnitary -> Identity}, mm, Last @ ws]
]


wcEvent[{enc_, trs_}, wu_WickUnitary] := Module[
  { t = Max[First /@ enc],
    new },
  new = theNambuDot[wu, Last @ trs];
  new = If[ t < Length[trs],
    Append[Most @ trs, new],
    Append[trs, new]
  ];
  {enc, new}
]

wcEvent[{enc_, trs_}, Measurement[cc_]] := Module[
  { t = Length[trs],
    new },
  new = Prepend[#, t]& /@ Through[cc[_]];
  new = Join[new, enc];
  {new, trs}
]

(**** </WickHistory> ****)


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


(**** <WickOperator> ****)

WickOperator::usage = "WickOperator[{c1,c2,...,ck}] represents an operator equivalent to c1**c2**...**ck, but is to be applied to a Wick state. on WickState ws.\nWickOperator[Measurement[c]] or WickOperator[Measurement[{c1, c2, \[Ellipsis]}]] is equivalent to Measurement[\[Ellipsis]].\nWickOperator[{u, v}] is equivalent to WickUnitary[{u, v}]."

WickOperator[msr_Measurement] = msr

WickOperator[trs_WickUnitary] = trs

WickOperator[trs:{_?MatrixQ, _?MatrixQ}] :=
  WickUnitary[trs]


(* For the vacuum state *)
WickOperator[op:{__?AnyFermionQ}][WickState[{}, {uv_}, {{}}, cc:{__?FermionQ}]] :=
  Module[
    {enc, trs, mat},
    {enc, trs, mat} = wmBuild[cc][op, uv];
    WickState[enc, trs, mat, cc]
  ]

WickOperator[{}][ws_WickState] = ws

WickOperator[op:{__?AnyFermionQ}][ws_WickState] :=
  Module[
    { enc, trs, mat, dd },
    {enc, trs, mat} = List @@ Most[ws];
    dd = Join[Dagger @ Reverse @ op, op];
    dd = theWickCode[Last @ ws][dd, {Length @ trs}];
    {enc, trs, mat} = wmWedge[dd, enc, trs, mat, Length[enc]/2];
    WickState[enc, trs, mat, Last @ ws]
  ]

(**** </WickOperator> ****)


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
  {bb, vv, nn} = wmWedge[op, aa, uu, mm, kk];

  (* Simulate the measurement process. *)
  (* NOTE: WickState is unnormalized. *)
  If[ RandomReal[] < Chop[Pfaffian @ nn / Pfaffian @ mm],
    $MeasurementOut[c] = 0,
    $MeasurementOut[c] = 1;
    op = Reverse @ op;  (* op := Dagger[c] ** c *)
    {bb, vv, nn} = wmWedge[op, aa, uu, mm, kk]
  ];

  (* PrintTemporary["Measurement outcome on mode ", c, ": ", $MeasurementOut[c]]; *)
  
  (* Construct the post-measurment state. *)
  {bb, vv, nn} = wmWedge[op, bb, vv, nn, kk];
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
    cc, dd, pp, uv, mm, gg },
  {pp, uv, mm, cc} = List @@ ws;
  dd = theWickCode[cc][ops, {tt}];
  gg = Last @ wmWedge[dd, pp, uv, mm, Length[pp]/2];
  Pfaffian[gg] / Pfaffian[mm]
]

(**** </WickExpectation> ****)


(**** <WickGreensFunction> ****)

WickGreensFunction::usage = "WickGreensFunction[ws] returns the pair {G, F} of normal Green's function G and anomalous Green's function F with respect to the Wick state ws.\nWickGreensFunction[ws, {d1, d2, \[Ellipsis]}] calculates the Green's functionns over the modes {d1, d2, \[Ellipsis]} out of all fermion modes in ws."

WickGreensFunction[ws_WickState] :=
  WickGreensFunction[ws, Last @ ws]

WickGreensFunction[ws_WickState, dd:{___?FermionQ}] := Module[
  { tt = ws["Stages"],
    aa, bb, pp, uv, mm, ff, gg, L, n, i, j },
  {pp, uv, mm, cc} = List @@ ws;

  n = Length[dd];
  L = Length[pp] / 2;

  (* encoded modes *)
  aa = theWickCode[cc][dd, {tt}];
  bb = dagWickCode /@ aa; (* NOT dagWickCode[aa] *)

  (* Green's function *)
  gg = Table[
    {i, i} -> Re @ Pfaffian @ Last @ wmWedge[{aa[[i]], bb[[i]]}, pp, uv, mm, L],
    {i, 1, n}
  ]; (* supposed to be real *)
  gg = Join[ gg,
    Flatten @ Table[
      {i, j} -> Pfaffian @ Last @ wmWedge[{aa[[i]], bb[[j]]}, pp, uv, mm, L],
      {i, 1, n},
      {j, i+1, n}
    ]
  ];
  gg = SymmetrizedArray[gg, {n, n}, Hermitian @ {1, 2}];

  (* anomalous Green's function *)
  ff = Flatten @ Table[
    {i, j} -> Pfaffian @ Last @ wmWedge[{aa[[i]], aa[[j]]}, pp, uv, mm, L],
    {i, 1, n},
    {j, i+1, n}
  ];
  ff = SymmetrizedArray[ff, {n, n}, Antisymmetric @ {1, 2}];

  {gg, ff} / Re[Pfaffian @ mm] (* This Pfaffian is supposed to be real. *)
]

(**** </WickGreensFunction> ****)


(**** <WickLogarithmicNegtivity> ****)

WickLogarithmicNegativity[dd:{__?FermionQ}][ws_WickState] :=
  WickLogarithmicNegativity[ws, dd]

WickLogarithmicNegativity[ws_WickState, dd:{__?FermionQ}, opts:OptionsPattern[]] := Module[
  { gg = WickGreensFunction[ws],
    cc = Last[ws],
    kk },
  kk = dd /. Thread[cc -> Range[Length @ cc]];
  WickTimeReversalMoment[1/2, gg, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]
]

(**** </WickLogarithmicNegtivity> ****)


(**** <EntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

WickEntanglementEntropy::usage = "WickEntanglementEntropy[ws, {d1, d2, \[Ellipsis]}] returns the entanglement entropy in the Wick state ws between the subsystem {d1, d2, \[Ellipsis]} \[Subset] {c1, c2, \[Ellipsis], cn} and the rest.\nWickEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] calculates the entanglement entropy from the normal (grn) and anomalous (anm) Green's functions. The index set {k1, k2, \[Ellipsis]} specifies the subsystem."

WickEntanglementEntropy[ws_WickState, dd:{__?FermionQ}] := Module[
  { gg = WickGreensFunction[ws, dd],
    id, ff },
  gg = theNambuGreen[gg];
  id = One[Dimensions @ gg];
  (QuantumLog[gg] + QuantumLog[id - gg]) / 2
]

WickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]],
    id },
  gg = theNambuGreen[{gg, ff}];
  (* gg = SymmetrizedArray[gg, Dimensions @ gg, Hermitian @ {1,2}]; *)
  id = One[Dimensions @ gg];
  (QuantumLog[gg] + QuantumLog[id - gg]) / 2
]
(* NOTE: It seems that Part does not support properly SymmetrizedArray, hence Normal is required in the above. *)

(**** </EntanglementEntropy> ****)


(**** <wmBuild> ****)

wmBuild::usage = "wmBuild[{c1,c2,...}][spec] parse spec and create the Wick matrix."

wmBuild[cc_][pre___, aa:{_?MatrixQ, _?MatrixQ}, bb:{_?MatrixQ, v_?MatrixQ}.., Shortest[post___]] :=
  wmBuild[cc][pre, theNambuDot[aa, bb], post]

wmBuild[cc_][pre___, aa_?MatrixQ, bb__?MatrixQ, Shortest[post___]] :=
  wmBuild[cc][pre, Dot[aa, bb], post]

wmBuild[cc_][pre___, aa_?MatrixQ, post___] :=
  wmBuild[cc][pre, toNambuForm @ aa, post]

(* OUTPUT: {enc, trs, mat}
  enc: the list of encoded modes
  trs: the transformations of the encoded modes
  mat: the Wick matrix
  *)
wmBuild[cc:{__?FermionQ}][spec:({___?AnyFermionQ} | {_?MatrixQ, _?MatrixQ})...] :=
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

(**** </wmBuild> ****)


(**** <wmWedge> ****)

wmWedge::usage = "wmWedge[dd, pp, mm, mat, n] cleaves the Wick matrix mat at row and column n and wedge into there additional blocks with rows and columns corresponding to the new fermion modes dd."

(* INPUT
  dd : the list of new fermion modes to wedge into the Wick matrix mat.
  pp : the list of encoded fermion modes labeling the rows and columns of the Wick matrix mat
  mm : the list of transformations of fermion modes
  mat: the Wick matrix to updated
  n  : the row and column where the new modes to be wedged.
*)
(* NOTE: Both dd and pp are given in the form of encoded modes. *)
wmWedge[ dd:{__?FermionQ}, (* encoded modes *)
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

(**** </wmWedge> ****)


(**** <wmTake> ****)

wmTake::usage = "wmTake[mat,k] takes the first and last k rows and columns of Wick matrix mat."

wmTake[mat_SymmetrizedArray, k_Integer] := Module[
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

(**** </wmTake> ****)


(**** <theWickContract> ****)

theWickContract::usage = "theWickContract[mm][a, b] calcualtes the Wick contraction between two dressed modes a and b."

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

theWickCode::usage = "theWickCode[rules][{c[k1], c[k2], ...}, {time}] converts each fermion operator c[k] to c[time, k, 0] and Dagger[c[k]] to c[time, k, 1].\nIntended to be used with MapIndexed."

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

theNambuDot[a_WickUnitary, b_WickUnitary] :=
  WickUnitary @ theNambuDot[First @ a, First @ b]

(**** </theNambuDot> ****)


theNambuOne::usage = "theNambuOne[n] returns the pair {One[n], Zero[n,n]}."

theNambuOne[n_Integer] := {One @ n, Zero @ {n, n}}


toNambuForm::usage = "toNambuForm[mat] ..."

toNambuForm[m_?MatrixQ] := {m, Zero @ Dimensions @ m}


theNambuGreen::usage = "theNambuGreen[{g, f}] ..."

theNambuGreen[{g_?MatrixQ, f_?MatrixQ}] := ArrayFlatten @ {
  {g, f},
  {Topple[f], One[Dimensions @ g] - Transpose[g]}
}


(**** <WickRandomCircuit> ****)

WickRandomCircuit::usage = "WickRandomCircuit[{c1, c2, \[Ellipsis]}, wu, p, t] simulates a random quantum circuit of depth t, where layers of Wick unitary wu alternate with layers of measurements on fermion modes selected randomly from {c1, c2, \[Ellipsis]} with probability p."

WickRandomCircuit::data = "Unknown data form ``."

Options[WickRandomCircuit] = {
  "InitialOccupation" -> Automatic,
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Data" -> "States",
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
    program, data,
    in, qc, n, m },
  PrintTemporary @ ProgressIndicator @ Dynamic[progress];

  (* initial state *)
  n = Length[cc];
  in = OptionValue["InitialOccupation"];
  If[ in === Automatic,
    in = PadRight[{1, 0}, n, {1, 0}] (* half-filling *)
  ];
  in = WickState @ Ket[cc -> PadRight[in, n, in]];

  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  program := {
    WickCircuit[qc, cc],
      Table[
      progress = ++k / (n*m);
      Fold[Construct[#2, #1]&, in, qc],
      m 
    ]
  };
  Switch[ OptionValue["Data"],
    "States",
    Null,
    "Correlations",
    program := Table[
      progress = ++k / (n*m);
      FoldPairList[{WickGreensFunction[#1], Construct[#2, #1]}&, in, qc],
      m
    ],
    _, Message[WickRandomCircuit::data, OptionValue["Data"]]
  ];
  data = Table[
    (* quantum circuit with randomly selected measurements *)
    qc = Riffle[ Table[wu, t], Measurement /@ RandomPick[cc, p, t] ];
    program,
    n
  ];
  Switch[ OptionValue["Data"],
    "Correlations", data = Flatten[data, 1]
  ];

  (* save data *)
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


(**** <WickCircuit> ****)

WickCircuit::usage = "WickCircuit[{g1, g2, \[Ellipsis]}, {c1, c2, \[Ellipsis]}] represents a Wick random circuit with gates g1, g2, \[Ellipsis] on fermion modes c1, c2, \[Ellipsis]."

WickCircuit /:
MakeBoxes[wc:WickCircuit[gg:{(_Measurement | _WickUnitary)..}, cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", cc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", gg[[;;UpTo[5]]] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(**** </WickCircuit> ****)


End[]

EndPackage[]
