BeginPackage["Q3`"]

{ WickLogarithmicNegativity, WickTimeReversalMoment };
{ WickEntanglementEntropy, WickMutualInformation };
{ QuantumLog }; (* mainly in vonNeumann.wl *)

{ WickState, WickHistory, WickOperator, WickUnitary };
{ WickExpectation, WickGreensFunction };

{ WickCircuit, WickRandomCircuit };

{ NambuMatrix, NambuOne, NambuZero,
  NambuRandomMatrix };

Begin["`Private`"]

(**** <NambuMatrix> ****)

NambuMatrix::usage = "NambuMatrix[{a, b}, type] represents a 2n\[Times]2n matrix of type in the Nambu space, the n\[Times]n upper-left and upper-right blocks of which are given by a and b, respectively.\nNambuMatrix[mat] returns the pair {a, b}, where a and b are the n\[Times]n upper-left and upper-right blocks, respectively, of 2n\[Times]2n matrix mat.\nNambuMatrix[mat, type] returns NambuMatrix[{a, b}, type], where a and b are as above.\nNambuMatrix[{mat, 0}] returns the pair {mat, Zero @ Dimenions @ mat}.\nNambuMatrix[{mat, 0}, type] is equivalent to NambuMatrix[NambuMatrix[{mat, 0}], type]."

NambuMatrix::odd = "Matrix `` has odd dimenions."

NambuMatrix /:
MakeBoxes[op:NambuMatrix[trs:{_?MatrixQ, _?MatrixQ}, type_], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NambuMatrix, op, None,
    { BoxForm`SummaryItem @ { "Type: ", type },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ trs }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[MatrixObject, trs] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]


NambuMatrix[mat_?SquareMatrixQ] := Module[
  { n = (Length[mat] + 1) / 2 },
  Message[NambuMatrix::odd, mat];
  { mat[[ ;;n, ;;n]], Zero[n] }
] /; OddQ[Length @ mat]

NambuMatrix[mat_?SquareMatrixQ] := With[
  { n = Length[mat] / 2 },
  { mat[[ ;;n, ;;n]], mat[[ ;;n, n+1;; ]] }
]

NambuMatrix[mat_?SquareMatrixQ, type_] :=
  NambuMatrix[NambuMatrix[mat], type]


NambuMatrix[{mat_?SquareMatrixQ, 0}] :=
  {mat, Zero @ Dimensions @ mat}

NambuMatrix[{mat_?SquareMatrixQ, 0}, type_] :=
  NambuMatrix[{mat, Zero @ Dimensions @ mat}, type]


NambuMatrix /:
MatrixForm @ NambuMatrix[mm:{_, _}, _] := Map[MatrixForm, mm]

NambuMatrix /:
Part[NambuMatrix[{a_?MatrixQ, b_?MatrixQ}, type_], spec__] :=
  NambuMatrix[{Part[a, spec], Part[b, spec]}, type]


NambuMatrix /:
Normal @ NambuMatrix[{u_, v_}, "Unitary"] :=
  ArrayFlatten @ {
    {u, v},
    Conjugate @ {v, u}
  }

NambuMatrix /:
Normal @ NambuMatrix[{ham_, del_}, "Hermitian"] :=
  ArrayFlatten @ {
    {ham, del},
    {Topple[del], -Transpose[ham]}
  }

NambuMatrix /:
Normal @ NambuMatrix[{g_, f_}, "Green's"] :=
  ArrayFlatten @ {
    {g, f},
    {Topple[f], One[Dimensions @ g] - Transpose[g]}
  }


NambuMatrix /:
Topple[NambuMatrix[mm:{_?MatrixQ, _?MatrixQ}, "Unitary"]] :=
  NambuMatrix[theNambuTopple @ mm, "Unitary"]

NambuMatrix /:
Topple[NambuMatrix[{ham_?MatrixQ, del_?MatrixQ}, "Hermitian"]] :=
  NambuMatrix[{Topple @ ham, del}, "Hermitian"]

NambuMatrix /:
Topple[NambuMatrix[{g_?MatrixQ, f_?MatrixQ}, "Green's"]] :=
  NambuMatrix[{Topple @ g, f}, "Green's"]


NambuMatrix /:
  Plus[NambuMatrix[a_, type_], NambuMatrix[b_, type_]] :=
    NambuMatrix[a + b, type]

NambuMatrix /:
  Times[z_, NambuMatrix[mm_, type_]] :=
    NambuMatrix[z * mm, type]

NambuMatrix /:
Dot[NambuMatrix[a_, type_], NambuMatrix[b_, type_]] :=
  NambuMatrix[theNambuDot[a, b], type]


NambuOne::usage = "NambuOne[n] returns the pair {One[n], Zero[{n, n}]}, which represents the identity matrix in the Nambu space."

NambuOne[n_Integer] := {One @ n, Zero @ {n, n}}

NambuOne[n_Integer, type_] := NambuMatrix[NambuOne @ n, type]


NambuZero::usage = "NambuZero[n] returns the pair {Zero[{n, n}], Zero[{n, n}]}, which represents the zero matrix in the Nambu space."

NambuZero[n_Integer] := {Zero @ {n, n}, Zero @ {n, n}}

NambuZero[n_Integer, type_] := NambuMatrix[NambuZero @ n, type]

(**** </NambuMatrix> ****)


(**** <theNambuDot> ****)

theNambuDot::usage = "theNambuDot[{u1,v1}, {u2,v2}] ..."

SetAttributes[theNambuDot, Flat]

theNambuDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

theNambuDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barU := {{U, V}, Conjugate @ {V, U}} *)

(**** </theNambuDot> ****)


(**** <theNambuTopple> ****)

theNambuTopple::usage = "theNambuTopple[{u, v}] ..."

theNambuTopple[{u_?MatrixQ, v_?MatrixQ}] := {Topple @ u, Transpose @ v}
(* NOTE: This works only for UNITARY matrices of the form {{u, v}, {Conjugate[v], Conjugate[u]}}in the Nambu space. *)

(**** </theNambuTopple> ****)


(**** <NambuRandomMatrix> ****)

NambuRandomMatrix::usage = "NambuRandomMatrix[n, type] returns a randomly generated matrix of type in the Nambu space with the n\[Times]n upper-left and upper-right blocks."

NambuRandomMatrix[n_Integer, "Hermitian"] :=
  NambuMatrix[
    { RandomHermitian[n],
      Symmetrize[RandomMatrix[n], Antisymmetric @ {1, 2}] },
    "Hermitian"
  ]

NambuRandomMatrix[n_Integer, "Unitary"] := With[
  { barH = NambuRandomMatrix[n, "Hermitian"] },
  NambuMatrix[MatrixExp[I * Normal[barH]], "Unitary"]
]

(**** </NambuRandomMatrix> ****)


(**** <WickTimeReversalMoment> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)

WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."

WickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[WickTimeReversalMoment] = { "Epsilon" -> 1.25*^-5 } (* 1.0*^-8 is also a reasonable choice *)


WickTimeReversalMoment[alpha_, NambuMatrix[{g_?MatrixQ, f_?MatrixQ}, "Green's"], rest__] := 
  WickTimeReversalMoment[alpha, {g, f}, rest]

WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  WickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk, opts]

WickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, OptionsPattern[]] := Module[
  { dd = Length[grn],
    gg, oo, id, xx, zz, uu, ww, pf, dgn, off
  },
  oo = Zero[{dd, dd}];
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
  (* NOTE: When there is a fermion mode that is unoccuppied with certainty, the coherent-state representation becomes unusual, and one needs to handle such cases separately. While this is possible, Q3 offers a ditry trick. *)
  gg = Normal @ NambuMatrix[{gg, -anm}, "Hermitian"];
  
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

tameMatrix::usage = "tameMatrix[mat, eps] tames a singular matrix mat with a small positive eps, and returns the resulting non-singular matrix."

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
  WickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[WickLogarithmicNegativity, "Epsilon"]]

WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, grn, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[NambuMatrix[{g_?MatrixQ, f_?MatrixQ}, "Green's"], rest__] :=
  WickLogarithmicNegativity[{g, f}, rest]


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


(**** <BogoliubovTransforms> ****)

BogoliubovTransforms /:
MakeBoxes[BogoliubovTransforms[trs:{{_?MatrixQ, _?MatrixQ}..}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    "BogoliubovTransforms", trs, None,
    { BoxForm`SummaryItem @ { "Transforms: ", Length @ trs },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ trs[[1, 1]] }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[MatrixObject, trs, {2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]

(**** </BogoliubovTransforms> ****)


AddElaborationPatterns[_WickState, _WickUnitary, _WickOperator];


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
      BoxForm`SummaryItem @ { "Transformations: ", BogoliubovTransforms @ mm },
      BoxForm`SummaryItem @ { "Wick matrix: ", MatrixObject @ ff }
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
  WickState[{}, {NambuOne @ Length @ Keys @ aa}, {{}}, Keys @ aa] /; 
  Total[Values @ aa] == 0


WickState /:
Norm[ws_WickState] := Power[Det[ws @ "Wick matrix"], 1/4]
(* NOTE: The pfaffian of this Wick matrix must be positive. *)


WickState /:
Matrix[ws_WickState, rest___] := ws * Matrix[Ket[], rest]

WickState /:
Matrix[ws:WickState[enc_List, trs:{{_?MatrixQ, _?MatrixQ}..}, mat_?MatrixQ, cc:{__?FermionQ}]] := Matrix[ws, cc]

WickState /:
Matrix[ws:WickState[enc_List, trs:{{_?MatrixQ, _?MatrixQ}..}, mat_?MatrixQ, cc:{__?FermionQ}], ss:{__?SpeciesQ}] :=
  Module[
    { ff = Drop[enc, Length[enc]/2],
      uu = Successive[theNambuDot[#2, theNambuTopple[#1]]&, trs] },
    ff = WickOperator /@ theWickDecode[cc] @ GroupBy[ff, First];
    uu = WickUnitary[#, cc]& /@ uu;
    SparseArray @ Fold[
      Dot[Matrix[#2, ss], #1]&,
      Matrix[Ket[cc], ss],
      Riffle[Reverse @ Values @ ff, uu]
    ]
  ]

WickState /:
Expand[ws:WickState[enc_List, trs:{{_?MatrixQ, _?MatrixQ}..}, mat_?MatrixQ, cc:{__?FermionQ}]] :=
  State[Matrix[ws, cc], cc]

WickState /:
Elaborate[ws:WickState[enc_List, trs:{{_?MatrixQ, _?MatrixQ}..}, mat_?MatrixQ, cc:{__?FermionQ}]] :=
  ExpressionFor[Matrix[ws, cc], cc]

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
  id = WickUnitary[1, Last @ ws];
  new = FoldList[wcEvent, {cc, {id}}, First @ wc];
  wsClone[ws] /@ new
]


wsClone::usage = "wsClone[ws][{enc, trs}] returns a clone of Wick state ws by selecting encoded modes and blocks of the Wick matrix that are consistent with enc and replacing BdG transforms with trs."

wsClone[ws_WickState][{enc_, trs_}] := Module[
  { dd, mm, wu, n },
  dd = Cases[First @ ws, Alternatives @@ enc];
  n = Length[dd] / 2;
  mm = wmTake[ws[[3]], n];
  WickState[dd, trs /. {wu_WickUnitary :> First[wu]}, mm, Last @ ws]
]


wcEvent::usage = "wcEvent[{enc, trs}, gate] updates {enc, trs} according to the new gate."

wcEvent[{enc_, trs_}, wu_WickUnitary] := Module[
  { t = Max[First /@ enc],
    new },
  new = Dot[wu, Last @ trs];
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


(**** <WickUnitary> ****)

WickUnitary::usage = "WickUnitary[{u, v}] represents the unitary matrix ArrayFlatten[{{u, v}, Conjugate @ {v, u}}] in the Nambu space."

WickUnitary /:
MakeBoxes[op:WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, ___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", "Unspecified" },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ trs }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[MatrixObject, trs] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]

WickUnitary /:
MakeBoxes[op:WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, cc:{___?FermionQ}, ___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ trs }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[MatrixObject, trs] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]


WickUnitary[0, cc:{___?FermionQ}, rest___] := (* zero in the Nambu space *)
  WickUnitary[NambuZero[Length @ cc], cc, rest]

WickUnitary[1, cc:{___?FermionQ}, rest___] := (* identity in the Nambu space *)
  WickUnitary[NambuOne[Length @ cc], cc, rest]


WickUnitary[NambuMatrix[{u_?MatrixQ, v_?MatrixQ}, "Unitary"], rest___] :=
  WickUnitary[{u, v}, rest]

WickUnitary[mat_?SquareMatrixQ, rest___] :=
  WickUnitary[NambuMatrix @ mat, rest]
  (* NOTE: Matrix mat is assumed to be unitary and have the block structure of a Bogoliubov-de Gennes transform. *)


WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, ___][fs_Ket] :=
  WickUnitary[trs][WickState @ fs]

WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, ___][ws_WickState] :=
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


WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___][fs_Ket] :=
  WickUnitary[trs] @ WickState @ KetRegulate[fs, cc]

WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___][ws_WickState] :=
  WickUnitary[trs][ws] /; cc == Last[ws]


WickUnitary /:
Times[z_, WickUnitary[uv_, rest___]] := WickUnitary[z * uv, rest]

WickUnitary /:
Plus[WickUnitary[a_, cc_, opts___?OptionQ], WickUnitary[b_, cc_, more___?OptionQ]] :=
  WickUnitary[a + b, cc, Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Plus[WickUnitary[a_, opts___?OptionQ], WickUnitary[b_, more___?OptionQ]] :=
  WickUnitary[a + b, Sequence @@ Flatten @ {opts, more}]


WickUnitary /:
Dot[WickUnitary[a_, cc_, opts___?OptionQ], WickUnitary[b_, cc_, more___?OptionQ]] :=
  WickUnitary[theNambuDot[a, b], cc, Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Dot[WickUnitary[a_, opts___?OptionQ], WickUnitary[b_, more___?OptionQ]] :=
  WickUnitary[theNambuDot[a, b], Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Topple[WickUnitary[mm:{_?MatrixQ, _?MatrixQ}, rest___]] :=
  WickUnitary[theNambuTopple @ mm, rest]


WickUnitary /:
Elaborate[wu:WickUnitary[{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___]] :=
  ExpressionFor[Matrix @ wu, cc]

WickUnitary /: (* fallback *)
Elaborate[wu_WickUnitary] = wu


WickUnitary /: (* fallback *)
Matrix[wu_WickUnitary, rest___] := wu * Matrix[1, rest]

WickUnitary /:
Matrix[wu:WickUnitary[{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___]] :=
  Matrix[wu, cc]

WickUnitary /:
Matrix[WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___], ss:{__?SpeciesQ}] := Module[
  { ff = Select[ss, FermionQ],
    rr = Select[ss, Not @* FermionQ],
    mm, n },
  n = Length[ff];
  
  (* Jordan-Wigner transformation *)
  mm = Table[PadRight[Table[3, k-1], n], {k, n}] + 4 * One[n];
  mm = ThePauli /@ mm;
  
  ff = Thread[ff -> mm];
  rr = Thread[rr -> Map[One, Dimension @ rr]];
  
  (* Convert the Nambu spinor to a list of matrices *)
  mm = Values @ KeyTake[Join[ff, rr], cc];
  mm = Join[mm, Topple /@ mm];

  MatrixExp @ TensorContract[
    Transpose[Topple /@ mm, {3, 1, 2}] . MatrixLog[Normal @ NambuMatrix[trs, "Unitary"]] . mm / 2,
    {{2, 3}}
  ]
]


WickUnitary /:
Normal @ WickUnitary[uv:{_?MatrixQ, _?MatrixQ}, ___] :=
  Normal @ NambuMatrix[uv, "Unitary"]

WickUnitary /:
MatrixForm @ WickUnitary[uv:{_?MatrixQ, _?MatrixQ}, ___] :=
  Map[MatrixForm, uv]

WickUnitary /: 
NonCommutativeQ[_WickUnitary] = True

WickUnitary /:
MultiplyKind[_WickUnitary] = Fermion

WickUnitary /:
Multiply[pre___, wu_WickUnitary, ws_WickState] := Multiply[pre, wu @ ws]

WickUnitary /:
Multiply[pre___, wu_WickUnitary, fs_Ket] := Multiply[pre, wu @ fs]


WickUnitary /:
ParseGate[WickUnitary[trs_, ff:{___?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[ff, more, opts, "Label" -> "U"]

(**** </WickUnitary> ****)


(**** <WickOperator> ****)

WickOperator::usage = "WickOperator[{c1,c2,...,ck}] represents an operator equivalent to c1**c2**...**ck, but is to be applied to a Wick state. on WickState ws.\nWickOperator[Measurement[c]] or WickOperator[Measurement[{c1, c2, \[Ellipsis]}]] is equivalent to Measurement[\[Ellipsis]].\nWickOperator[{u, v}] is equivalent to WickUnitary[{u, v}]."

WickOperator[msr_Measurement] = msr

WickOperator[trs_WickUnitary] = trs

WickOperator[trs:{_?MatrixQ, _?MatrixQ}] :=
  WickUnitary[trs]


WickOperator[op:{___?AnyFermionQ}][fs_Ket] :=
  WickOperator[op][WickState @ fs]

WickOperator[{}][ws_WickState] = ws


(* For the vacuum state *)
WickOperator[op:{__?AnyFermionQ}, ___][WickState[{}, {uv_}, {{}}, cc:{__?FermionQ}]] :=
  Module[
    {enc, trs, mat},
    {enc, trs, mat} = wmBuild[cc][op, uv];
    WickState[enc, trs, mat, cc]
  ]

WickOperator[op:{__?AnyFermionQ}, ___][ws_WickState] :=
  Module[
    { enc, trs, mat, dd },
    {enc, trs, mat} = List @@ Most[ws];
    dd = Join[Dagger @ Reverse @ op, op];
    dd = theWickCode[Last @ ws][dd, {Length @ trs}];
    {enc, trs, mat} = wmWedge[dd, enc, trs, mat, Length[enc]/2];
    WickState[enc, trs, mat, Last @ ws]
  ]


WickOperator /: 
NonCommutativeQ[_WickOperator] = True

WickOperator /:
MultiplyKind[_WickOperator] = Fermion

WickOperator /:
Multiply[pre___, opr_WickOperator, ws_WickState] := Multiply[pre, opr[ws]]

WickOperator /:
Multiply[pre___, opr_WickOperator, fs_Ket] := Multiply[pre, opr[WickState @ fs]]


WickOperator /:
Matrix[WickOperator[cc:{__?AnyFermionQ}, ___], rest___] :=
  Dot @@ Matrix[cc, rest]

WickOperator /: (* fallback *)
Matrix[op_WickOperator, rest___] := op * Matrix[1, rest]

WickOperator /:
Elaborate[op:WickOperator[{__?AnyFermionQ}, ___]] :=
  ExpressionFor[Matrix[op], Fermions @ op]

WickOperator /: (* fallback *)
Elaborate[op_WickOperator] = op 


WickOperator /:
ParseGate[WickOperator[op:{___?AnyFermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[Fermions @ op, more, opts]

(**** </WickOperator> ****)


(**** <Measurement> ****)

theMeasurement[fs_Ket, c_?FermionQ] := theMeasurement[WickState @ fs, c]

theMeasurement[ws_WickState, c_?FermionQ] := Module[
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
  (* NOTE: Both nn and mm have a positive Pfaffian. *)
  (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases. *)
  If[ RandomReal[] < Quiet[Chop[Sqrt[Det @ nn / Det @ mm]], Det::luc],
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


Measurement /:
Multiply[msr:Measurement[_?FermionQ|{__?FermionQ}], ws_WickState] := msr[ws]

Measurement /:
Multiply[msr:Measurement[_?FermionQ|{__?FermionQ}], fs_Ket] := msr[WickState @ fs]

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

WickExpectation[ws_WickState][WickOperator[ops:{__?AnyFermionQ}, ___]] :=
  WickExpectation[ws][ops]

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

WickGreensFunction::usage = "WickGreensFunction[ws] returns the pair {G, F} of normal Green's function G and anomalous Green's function F with respect to Wick state ws.\nWickGreensFunction[ws, {d1, d2, \[Ellipsis]}] calculates the Green's functionns over given fermion modes {d1, d2, \[Ellipsis]} out of all fermion modes in ws."

WickGreensFunction[ws_WickState] :=
  WickGreensFunction[ws, Last @ ws]

WickGreensFunction[ws_WickState, dd:{___?FermionQ}] := Module[
  { tt = ws["Stages"],
    aa, bb, pp, uv, mm, ff, gg, i, j, k, n },
  {pp, uv, mm, cc} = List @@ ws;

  n = Length[dd];
  k = Length[pp] / 2;

  (* encoded modes *)
  aa = theWickCode[cc][dd, {tt}];
  bb = dagWickCode /@ aa; (* NOT dagWickCode[aa] *)

  (* normal Green's function *)
  gg = Zero[{n, n}];
  Table[
    gg[[i, i]] = Re @ Sqrt @ Quiet[Det @ Last @ wmWedge[{aa[[i]], bb[[i]]}, pp, uv, mm, k], Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases. *)
    {i, 1, n}
  ];
  Table[
    gg[[i, j]] = Pfaffian @ Last @ wmWedge[{aa[[i]], bb[[j]]}, pp, uv, mm, k];
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];

  (* anomalous Green's function *)
  ff = Zero[{n, n}];
  Table[
    ff[[i, j]] =  Pfaffian @ Last @ wmWedge[{aa[[i]], aa[[j]]}, pp, uv, mm, k];
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];

  NambuMatrix[{gg, ff} / Re[Sqrt @ Det @ mm], "Green's"]
  (* NOTE: The Pfaffian of mm is supposed to be real positive. *)
]

(**** </WickGreensFunction> ****)


(**** <WickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

WickEntanglementEntropy::usage = "WickEntanglementEntropy[ws, {d1, d2, \[Ellipsis]}] returns the entanglement entropy in the Wick state ws between the subsystem {d1, d2, \[Ellipsis]} \[Subset] {c1, c2, \[Ellipsis], cn} and the rest of the total system {c1,c2,\[Ellipsis],cn} of fermion modes.\nWickEntanglementEntropy[{gg, ff}, {k1, k2, \[Ellipsis]}] or WickEntanglementEntropy[NambuMatrix[{gg, ff}, \"Green's\"], {k1, k2, \[Ellipsis]}] calculates the entanglement entropy from the matrices gg and ff of normal and anomalous Green's functions, respectively. The index list {k1, k2, \[Ellipsis]} specifies the subsystem {ck1,ck2,\[Ellipsis]}\[Subset]{c1,c2,\[Ellipsis],cn}."

WickEntanglementEntropy[dd:{__?FermionQ}][ws_WickState] :=
  WickEntanglementEntropy[ws, dd]

WickEntanglementEntropy[ws_WickState, dd:{__?FermionQ}] :=
  WickEntanglementEntropy[WickGreensFunction[ws, dd], Range[Length @ dd]]


WickEntanglementEntropy[kk:{__Integer}][spec_] :=
  WickEntanglementEntropy[spec, kk]

WickEntanglementEntropy[grn:NambuMatrix[{_?MatrixQ, _?MatrixQ}, "Green's"], kk:{__Integer}] :=
  theWickEntropy[Normal @ grn[[kk, kk]]]

WickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  theWickEntropy @ Normal @ NambuMatrix[{gg, ff}, "Green's"]
]

WickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  WickEntanglementEntropy[NambuMatrix @ {grn, 0}, kk]


theWickEntropy::usage = "theWickEntropy[grn] returns the entropy of the fermionic Gaussian state characterized by the matrix grn of Green's function."

theWickEntropy[grn_?MatrixQ] :=
  ( QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn] ) / 2

(**** </WickEntanglementEntropy> ****)


(**** <WickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

WickMutualInformation::usage = "WickMutualInformation[ws, {d1, d2, \[Ellipsis]}] returns the mutual information in Wick state ws between the subsystem {d1, d2, \[Ellipsis]} \[Subset] {c1, c2, \[Ellipsis], cn} and the rest of the total system {c1,c2,\[Ellipsis],cn} of fermion modes.\nWickMutualInformation[{gg, ff}, {k1, k2, \[Ellipsis]}] or WickMutualInformation[NambuMatrix[{gg, ff}, \"Green's\"] {k1, k2, \[Ellipsis]}] calculates the mutual information from the matrices gg and ff of normal and anomalous Green's functions, respectively. The index list {k1, k2, \[Ellipsis]} specifies the subsystem {ck1,ck2,\[Ellipsis]}\[Subset]{c1,c2,\[Ellipsis],cn}."

WickMutualInformation[dd:{__?FermionQ}][ws_WickState] :=
  WickMutualInformation[ws, dd]

WickMutualInformation[ws_WickState, dd:{__?FermionQ}] := 
  WickMutualInformation[
    WickGreensFunction[ws], 
    Lookup[First /@ PositionIndex[Last @ ws], dd]
  ]


WickMutualInformation[kk:{__Integer}][spec_] :=
  WickMutualInformation[spec, kk]

WickMutualInformation[grn:NambuMatrix[{_?MatrixQ, _?MatrixQ}, "Green's"], kk_] := With[
  { ll = Supplement[Range @ Length @ First @ First @ grn, kk] },
  theWickEntropy[Normal @ grn[[kk, kk]]] + theWickEntropy[Normal @ grn[[ll, ll]]] - theWickEntropy[Normal @ grn]
]

WickMutualInformation[mm:{_?MatrixQ, _?MatrixQ}, kk:{__Integer}] :=
  WickMutualInformation[NambuMatrix[mm, "Green's"], kk]

WickMutualInformation[grn_?MatrixQ, kk:{__Integer}] :=
  WickMutualInformation[NambuMatrix[{grn, 0}, "Green's"], kk]

(**** </WickMutualInformation> ****)


(**** <wmBuild> ****)

wmBuild::usage = "wmBuild[{c1,c2,...}][spec] parse spec and create the Wick matrix."

wmBuild[cc_][pre___, aa:{_?MatrixQ, _?MatrixQ}, bb:{_?MatrixQ, v_?MatrixQ}.., Shortest[post___]] :=
  wmBuild[cc][pre, theNambuDot[aa, bb], post]

wmBuild[cc_][pre___, aa_?MatrixQ, bb__?MatrixQ, Shortest[post___]] :=
  wmBuild[cc][pre, Dot[aa, bb], post]

wmBuild[cc_][pre___, aa_?MatrixQ, post___] :=
  wmBuild[cc][pre, {aa, Zero @ Dimensions @ aa}, post]

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
      trs = FoldList[theNambuDot[#2, #1]&, NambuOne @ n, Reverse @ trs]
    ];

    (* encoded fermion modes *)
    enc = Flatten @ Reverse @ MapIndexed[theWickCode[cc], Reverse @ enc];
    enc = Join[dagWickCode @ enc, enc];

    n = Length[enc];
    mat = Zero[{n, n}];
    Table[
      mat[[i, j]] = theWickContract[trs][enc[[i]], enc[[j]]];
      mat[[j, i]] = -mat[[i, j]],
      {i, n},
      {j, i+1, n}
    ];
    (* mat = SymmetrizedArray[mat, {n, n}, Antisymmetric[{1, 2}]]; *)
    (* NOTE: Too dense and pointless for most purposes. *)
    {enc, trs, Normal @ mat}
  ]

(**** </wmBuild> ****)


(**** <wmWedge> ****)

wmWedge::usage = "wmWedge[dd, pp, mm, mat, k] cleaves the Wick matrix mat at row and column k and wedge into there additional blocks with rows and columns corresponding to the new fermion modes dd."

(* INPUT
  dd : the list of new fermion modes to wedge into the Wick matrix mat.
  pp : the list of encoded fermion modes labeling the rows and columns of the Wick matrix mat
  mm : the list of transformations of fermion modes
  mat: the Wick matrix to updated
  n  : the row and column where the new modes to be wedged.
*)

(* NOTE: Both dd and pp are given in the form of encoded modes. *)
wmWedge[ dd:{__?FermionQ}, (* encoded modes *)
  pp:{__?FermionQ}, uv:{{_?MatrixQ, _?MatrixQ}...}, mat_?MatrixQ,
  k_Integer] := Module[
  { new = mat,
    p1, p2, rr, ss, i, j, n },
  n = Length[dd];
  {p1, p2} = TakeDrop[pp, k];

  (* Crack open the matrix. *)
  new = Zero[Dimensions[mat] + n];
  new[[ ;;k, ;;k]] = mat[[ ;;k, ;;k]];
  new[[ ;;k, n+k+1;; ]] = mat[[ ;;k, k+1;; ]];
  new[[n+k+1;; , ;;k]] = mat[[k+1;; , ;;k]];
  new[[n+k+1;; , n+k+1;; ]] = mat[[k+1;; , k+1;; ]];

  (* wedge additional blocks into the crack. *)
  Table[
    new[[i, j+k]] = theWickContract[uv][p1[[i]], dd[[j]]];
    new[[j+k, i]] = -new[[i, j+k]],
    {i, k},
    {j, n}
  ];
  Table[
    new[[i+k, j+k]] = theWickContract[uv][dd[[i]], dd[[j]]];
    new[[j+k, i+k]] = -new[[i+k, j+k]],
    {i, n},
    {j, i+1, n}
  ];
  Table[
    new[[i+k, j+k+n]] = theWickContract[uv][dd[[i]], p2[[j]]];
    new[[j+k+n, i+k]] = -new[[i+k, j+k+n]],
    {i, n},
    {j, Length[pp] - k}
  ];

  (* Reconstruct the Wick matrix. *)
  { Join[p1, dd, p2], uv, Normal @ new }
]

(**** </wmWedge> ****)


(**** <wmTake> ****)

wmTake::usage = "wmTake[mat,k] takes the first and last k rows and columns of Wick matrix mat."

wmTake[mat_?MatrixQ, k_Integer] := Module[
  { rr },
  rr = List /@ Range[1+k, Length[mat]-k];
  Delete[Transpose @ Delete[Transpose @ mat, rr], rr]
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


theWickDecode::usage = "theWickDecode[cc][c[t_, k_, type_]] returns cc[[k]] if type is 0 and Dagger[cc[[kk]]] if type is 1."

theWickDecode[cc:{__?FermionQ}][ff:(_List|_Association)] := Map[theWickDecode[cc], ff]

theWickDecode[cc:{__?FermionQ}][_[t_, k_, 0]] := cc[[k]]

theWickDecode[cc:{__?FermionQ}][_[t_, k_, 1]] := Dagger[ cc[[k]] ]

(**** </theWickCode> ****)


(**** <WickRandomCircuit> ****)

WickRandomCircuit::usage = "WickRandomCircuit[{c1, c2, \[Ellipsis]}, wu, p, t] simulates a random quantum circuit of depth t, where layers of Wick unitary wu alternate with layers of measurements on fermion modes selected randomly from {c1, c2, \[Ellipsis]} with probability p."

WickRandomCircuit::data = "Unknown data form ``."

Options[WickRandomCircuit] = {
  "InitialOccupation" -> Automatic,
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Output" -> "States",
  "Prefix" -> "WRC"
}

WickRandomCircuit[cc_, trs:{_?MatrixQ, _?MatrixQ}, rest___] :=
  WickRandomCircuit[cc, WickUnitary[trs, cc], rest]

WickRandomCircuit[cc_, NambuMatrix[trs:{_?MatrixQ, _?MatrixQ}, "Unitary"], rest___] :=
  WickRandomCircuit[cc, WickUnitary[trs, cc], rest]

WickRandomCircuit[cc_, WickUnitary[trs:{_?MatrixQ, _?MatrixQ}, opts___?OptionQ], rest___] :=
  WickRandomCircuit[cc, WickUnitary[trs, cc, opts], rest]

WickRandomCircuit[
  cc:{__?FermionQ},
  wu:WickUnitary[{_?MatrixQ, _?MatrixQ}, {__?FermionQ}, ___],
  p_?NumericQ, t_Integer, OptionsPattern[]] :=
Module[
  { k = 0,
    progress = 0,
    program, data,
    in, qc, qc2, n, m },
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
  Switch[ OptionValue["Output"],
    "States",
    Null,
    "Correlations",
    program := Table[
      progress = ++k / (n*m);
      FoldPairList[{WickGreensFunction[#1], Construct[#2, #1]}&, in, Append[qc, WickUnitary[1, cc]]],
      m
    ],
    _, Message[WickRandomCircuit::data, OptionValue["Output"]]
  ];
  data = Table[
    (* quantum circuit with randomly selected measurements *)
    qc = Riffle[ Table[wu, t], Measurement /@ RandomPick[cc, p, t] ];
    program,
    n
  ];
  Switch[ OptionValue["Output"],
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

  Export[file, data]
]

(**** </WickRandomCircuit> ****)


(**** <WickCircuit> ****)

WickCircuit::usage = "WickCircuit[{g1, g2, \[Ellipsis]}, {c1, c2, \[Ellipsis]}] represents a quantum circuit consisting of Wick gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes c1, c2, \[Ellipsis]."

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

WickCircuit /:
  Graphics[wc_WickCircuit, opts___?OptionQ] :=
  Graphics[QuantumCircuit @@ First[wc], opts]

WickCircuit /:
  Show[wc_WickCircuit, opts___?OptionQ] :=
  Graphics[QuantumCircuit @@ First[wc], opts]

(**** </WickCircuit> ****)


End[]

EndPackage[]
