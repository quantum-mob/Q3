BeginPackage["Q3`"]

{ BdGState, BdGUnitary, BdGOperator, BdGOperatorFrom };

{ RandomBdGState };


Begin["`Private`"]

AddElaborationPatterns[_BdGState, _BdGOperator, _BdGUnitary];


(**** <BdGState> ****)

BdGState::usage = "BdGState[uv, trs, {c1, c2, \[Ellipsis]}] represents a many-fermion quantum state for fermion modes {c1, c2, \[Ellipsis]} that has undergone the overall Bogoliubov-de Gennes type evolution specified by reduced Nambu matrix uv and quantum decoherence process (including measurements) specified by matrix trs."

BdGState::bad = "Unsupported form of Wick state ``."

BdGState /:
MakeBoxes[ws:BdGState[uv:{_?MatrixQ, _?MatrixQ}, ops:(_?MatrixQ|{}), cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BdGState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", cc },
      BoxForm`SummaryItem @ { "Operators: ",  Length @ ops}
    },
    { BoxForm`SummaryItem @ { "Overall unitary: ", ArrayShort /@ uv },
      BoxForm`SummaryItem @ { "Operator transforms: ",
        If[ops == {}, {}, ArrayShort /@ First @ PartitionInto[ops, {1, 2}]] }    
    },
    fmt,
    "Interpretable" -> Automatic
  ]

BdGState[cc:{__?FermionQ}] :=
  BdGState[NambuOne[Length @ cc], {}, cc]

BdGState[ops_?MatrixQ, cc:{__?FermionQ}] :=
  BdGState[NambuOne[Length @ cc], ops, cc]

BdGState[Ket[aa_Association]] := Module[
  { cc = Select[Keys @ aa, FermionQ],
    dd = Select[Keys @ theKetTrim @ aa, FermionQ] },
  BdGState[
    NambuOne[Length @ cc],
    First @ BdGOperatorFrom[Dagger @ dd, cc],
    cc
  ]
]

BdGState[ops:{__Dagger?AnyFermionQ}, cc:{__?FermionQ}] :=
  BdGState @ Ket[cc -> 0, Peel[ops] -> 1]


BdGState /:
NormSquare[BdGState[_, {}, cc:{___?FermionQ}]] = 1

BdGState /:
NormSquare[BdGState[_, ops_?MatrixQ, cc:{__?FermionQ}]] := 
  Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[theConjugateReverse @ ops, ops], Det::luc]

BdGState /:
Norm[ws:BdGState[_, _?MatrixQ, {__?FermionQ}]] := Sqrt[NormSquare @ ws]


BdGState /:
Normalize[ws:BdGState[_, {}, {__?FermionQ}]] = ws

BdGState /:
Normalize[ws:BdGState[uv_?NambuMatrixQ, ops_?MatrixQ, cc:{___?FermionQ}]] := Module[
  { new },
  new = ops * Power[Norm @ ws, -1/Length[ops]];
  BdGState[uv, new, cc]
]


BdGState /:
Expand[ws:BdGState[_?NambuMatrixQ, _?MatrixQ, cc:{___?FermionQ}]] :=
  State[Matrix[ws, cc], cc]


BdGState /:
Elaborate[ws:BdGState[_?NambuMatrixQ, _?MatrixQ, cc:{__?FermionQ}]] :=
  ExpressionFor[Matrix[ws, cc], cc]

BdGState /:
Elaborate[ws_BdGState] = ws (* fallback *)


BdGState /:
Matrix[ws:BdGState[_, _, cc:{__?FermionQ}]] := Matrix[ws, cc]

BdGState /:
Matrix[ws:BdGState[uv_?NambuMatrixQ, trs_?MatrixQ, cc:{__?FermionQ}], ss:{__?SpeciesQ}] :=
  Module[
    { ops = WickElements[trs, cc],
      vec },
    vec = SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ops, ss]
    ];
    Matrix[BdGUnitary[uv, cc], ss] . vec
  ]

BdGState /: (* fallback *)
Matrix[ws_BdGState, rest___] := (
  Message[BdGState::bad, ws];
  Matrix[Ket[], rest]
)


BdGState /:
NonCommutativeQ[_BdGState] = True

BdGState /:
MultiplyKind[_BdGState] = Fermion

(**** </BdGState> ****)


(**** <BdGUnitary> ****)

BdGUnitary::usage = "BdGUnitary[{a, b}, {c1, c2, \[Ellipsis]}] represents a unitary operator on fermion modes {c1, c2, \[Ellipsis], cn} in the Nambu space that is characterized by the n\[Times]n upper-left and upper-right blocks a and b, respectively."

BdGUnitary::odd = "Matrix `` has odd dimenions."

BdGUnitary /:
MakeBoxes[op:BdGUnitary[uv_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    BdGUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ uv }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, uv] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[uv]

BdGUnitary[0, cc:{___?FermionQ}, rest___] := (* zero in the Nambu space *)
  BdGUnitary[NambuZero[Length @ cc], cc, rest]

BdGUnitary[1, cc:{___?FermionQ}, rest___] := (* identity in the Nambu space *)
  BdGUnitary[NambuOne[Length @ cc], cc, rest]


BdGUnitary[mat_?SquareMatrixQ, rest___] :=
  BdGUnitary[NambuMatrix @ mat, rest]

BdGUnitary[{mat_?SquareMatrixQ, 0}, rest___] :=
  BdGUnitary[NambuMatrix[{mat, 0}], rest]

BdGUnitary[NambuMatrix[uv_?NambuMatrixQ, "Unitary"], rest___] :=
  BdGUnitary[uv, rest]


BdGUnitary /:
MatrixForm @ BdGUnitary[mm_?NambuMatrixQ, rest___] := Map[MatrixForm, mm]

BdGUnitary /:
ArrayShort @ BdGUnitary[mm_?NambuMatrixQ, rest___] := Map[ArrayShort, mm]

BdGUnitary /:
Part[BdGUnitary[{a_?MatrixQ, b_?MatrixQ}, rest___], spec__] :=
  BdGUnitary[{Part[a, spec], Part[b, spec]}, rest]


BdGUnitary /:
Normal @ BdGUnitary[{u_?MatrixQ, v_?MatrixQ}, ___] :=
  ArrayFlatten @ {
    {u, v},
    Conjugate @ {v, u}
  }


BdGUnitary /:
Dagger[BdGUnitary[mm_?NambuMatrixQ, rest___]] :=
  BdGUnitary[theNambuTopple @ mm, rest]


BdGUnitary /:
Plus[BdGUnitary[a_, cc_, any___], BdGUnitary[b_, cc_, other___]] :=
  BdGUnitary[a + b, cc, any, other]

BdGUnitary /:
Times[z_, BdGUnitary[mm_, rest___]] :=
  BdGUnitary[z * mm, rest]

BdGUnitary /:
Dot[BdGUnitary[a_, cc_, any___], BdGUnitary[b_, cc_, other___]] :=
  BdGUnitary[theNambuDot[a, b], any, other]


BdGUnitary /:
Matrix[BdGUnitary[trs_?NambuMatrixQ, cc:{__?FermionQ}, ___], ss:{__?SpeciesQ}] := Module[
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
    Transpose[Topple /@ mm, {3, 1, 2}] . MatrixLog[Normal @ BdGUnitary @ trs] . mm / 2,
    {{2, 3}}
  ]
]


BdGUnitary /:
ParseGate[BdGUnitary[uv_?NambuMatrixQ, cc:{___?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[cc, more, opts, "Label" -> "U"]


BdGUnitary /:
NonCommutativeQ[_BdGUnitary] = True

BdGUnitary /:
MultiplyKind[_BdGUnitary] = Fermion

BdGUnitary /:
Multiply[pre___, opr_BdGUnitary, ws_BdGState] := Multiply[pre, opr[ws]]

BdGUnitary /:
Multiply[pre___, opr_BdGUnitary, fs_Ket] := Multiply[pre, opr[BdGState @ fs]]

BdGUnitary[new_?NambuMatrixQ, cc_, ___][BdGState[uv_, trs_, cc_]] :=
  BdGState[theNambuDot[new, uv], trs, cc]

(**** </BdGUnitary> ****)


(**** <BdGOperator> ****)

BdGOperator::usage = "BdGOperator[m, {c1,c2,\[Ellipsis]}] represents a sequence of quantum operations that are described linear combinations in the creation and annihilation operators of the fermion modes {Subscript[c, 1],Subscript[c, 2],\[Ellipsis]} with coefficients given by the elements of matrix m."

BdGOperator /:
MakeBoxes[BdGOperator[ops_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest}, 
    m, n },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  {m, n} = Dimensions[ops];
  BoxForm`ArrangeSummaryBox[
    BdGOperator, mat, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Transforms: ", ArrayShort /@ First @ PartitionInto[ops, {1, 2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

BdGOperator[msr_Measurement] = msr

BdGOperator[trs_BdGUnitary] = trs

(* canonicalization *)
BdGOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  BdGOperatorFrom[ops, cc, rest]


BdGOperator[{}, ___][any_] = any

BdGOperator[spec__][fs_Ket] := BdGOperator[spec][BdGState @ fs]

BdGOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___][BdGState[uv_, mm_, cc_]] :=
  BdGState[uv, Join[trs . Normal[NambuMatrix[uv, "Unitary"]], mm], cc]


BdGOperator /: 
NonCommutativeQ[_BdGOperator] = True

BdGOperator /:
MultiplyKind[_BdGOperator] = Fermion

BdGOperator /:
Multiply[pre___, opr_BdGOperator, ws_BdGState] := Multiply[pre, opr[ws]]

BdGOperator /:
Multiply[pre___, opr_BdGOperator, fs_Ket] := Multiply[pre, opr[BdGState @ fs]]


BdGOperator /:
Matrix[BdGOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___], rest___] :=
  Dot @@ Matrix[WickElements[trs, cc], rest]

BdGOperator /: (* fallback *)
Matrix[op_BdGOperator, rest___] := op * Matrix[1, rest]


BdGOperator /:
Elaborate[BdGOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___]] :=
  Apply[Multiply, WickElements[trs, cc]]

BdGOperator /: (* fallback *)
Elaborate[op_BdGOperator] = op 


BdGOperator /:
VacuumExpectation @ BdGOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___] :=
  Pfaffian @ WickMatrix[trs]


BdGOperator /:
ParseGate[BdGOperator[trs_, cc:{__?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[cc, more, opts]

(**** </BdGOperator> ****)


(**** <BdGOperatorFrom> ****)

(* NOTE: In principle, BdGOperatorFrom may be integrated into BdGOperator, but separating this feature keeps better the performance of BdGOperator. *)

BdGOperatorFrom::usage = "BdGOperatorFrom[expr, {c1,c2,\[Ellipsis]}] constructs BdGOperator from expr, which is supposed to be a linear combination or a list of linear combinations in the creation and annihilation operators of fermion modes {c1, c2, \[Ellipsis]}."

BdGOperatorFrom::nlin = WickOperatorFrom::nlin

BdGOperatorFrom[expr_, cc:{__?FermionQ}, rest___] :=
  BdGOperator[theBdGOperator[expr, cc], cc, rest] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[BdGOperatorFrom::nlin, expr, cc];
    False
  ]


theBdGOperator[expr_List, cc:{__?FermionQ}] :=
  Map[Coefficient[#, Join[cc, Dagger @ cc]] &, expr]

theBdGOperator[expr_, cc:{__?FermionQ}] :=
  { Coefficient[expr, Join[cc, Dagger @ cc]] }


(**** </BdGOperatorFrom> ****)


(**** <Measurement> ****)

Measurement /:
Multiply[pre___, msr:Measurement[_?FermionQ|{__?FermionQ}], ws_BdGState] :=
  Multiply[pre, msr[ws]]

theMeasurement[ws:BdGState[uv_, trs_, cc_], c_?FermionQ] := Module[
  { msr, dgr, mat, prb },
  msr = First @ BdGOperator[{c, Dagger @ c}, cc];
  msr = msr . Normal[BdGUnitary @ uv];

  dgr = theConjugateReverse[trs];

  mat = WickMatrix @ Join[dgr, msr, trs];
  prb = Re @ Sqrt @ Quiet[Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= NormSquare[ws];
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[c] = 0;
    BdGOperator[{c, Dagger @ c}, cc][ws],
    $MeasurementOut[c] = 1;
    BdGOperator[{Dagger @ c, c}, cc][ws]
  ]
]

(**** </Measurement> ****)


WickExpectation[ws_BdGState][HoldPattern @ Multiply[ops__?AnyFermionQ]] :=
  WickExpectation[ws] @ BdGOperatorFrom[{ops}, Last @ ws]

WickExpectation[ws:BdGState[uu_, bb_, cc_]][BdGOperator[ops_?MatrixQ, ___]] := Module[
  { aa = theConjugateReverse[bb],
    mat },
  mat = WickMatrix @ Join[aa, ops, bb];
  Pfaffian[mat] / NormSquare[ws]
]


WickEntanglementEntropy[ws_BdGState, dd:{__?FermionQ}] :=
  WickEntanglementEntropy[WickGreensFunction[ws, dd], Range[Length @ dd]]

WickLogarithmicNegativity[ws_BdGState, dd:{__?FermionQ}, opts:OptionsPattern[]] := Module[
  { gg = WickGreensFunction[ws],
    cc = Last[ws],
    kk },
  kk = dd /. Thread[cc -> Range[Length @ cc]];
  WickTimeReversalMoment[1/2, gg, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]
]


(**** <WickGreensFunction> ****)

WickGreensFunction[ws_BdGState] :=
  WickGreensFunction[ws, Last @ ws]

WickGreensFunction[BdGState[uv_, qq_, cc_], dd:{___?FermionQ}] := Module[
  { uu = Normal @ NambuMatrix[uv, "Unitary"],
    pp = theConjugateReverse[qq],
    aa, bb, ff, gg, kk, n },
  kk = First /@ PositionIndex @ Join[cc, Dagger @ cc];
  aa = uu[[ Lookup[kk, dd] ]];
  bb = uu[[ Lookup[kk, Dagger @ dd] ]];

  n = Length[dd];
  gg = Normal @ Zero[{n, n}];
  Table[
    gg[[i, i]] = Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[pp, {aa[[i]], bb[[i]]}, qq], Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, n}
  ];
  Table[
    gg[[i, j]] = Pfaffian @ WickMatrix @ Join[pp, {aa[[i]], bb[[j]]}, qq];
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];

  ff = Normal @ Zero[{n, n}];
  Table[
    ff[[i, j]] = Pfaffian @ WickMatrix @ Join[pp, {aa[[i]], aa[[j]]}, qq];
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];
  NambuMatrix[{gg, ff}, "Green's"]
  (* NOTE: The input BdGState is assumed normalized. *)
]

(**** </WickGreensFunction> ****)


RandomBdGState::usage = "RandomBdGState[k, {c1, c2, \[Ellipsis]}] randomly generates a depth-k BdG state with half filling on fermion modes {c1, c2, \[Ellipsis]}."

RandomBdGState[k_Integer?Positive, cc:{__?FermionQ}] := Module[
  { mm, in },
  mm = Table[RandomVector[2 Length @ cc], k];
  in = BdGState[Dagger @ cc[[;; ;;2]], cc];
  BdGOperator[mm, cc][in]
]

End[]

EndPackage[]
