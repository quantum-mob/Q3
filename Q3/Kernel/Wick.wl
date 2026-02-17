(* ::Package:: *)

(* Classical simulation of fermionic Gaussian processes without pairing potential *)
(* See Appendix B in Feng & Chen (2024). *)
(* See also Cano, Tilloy and De Luca (2019). *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ WickState, RandomWickState };
{ WickFidelity };

{ WickUnitary, RandomWickUnitary,
  WickHermitian, RandomWickHermitian,
  WickNonunitary, RandomWickNonunitary,
  WickJump, RandomWickJump,
  WickMeasurement, RandomWickMeasurement };

{ WickOdds, WickDamping };

{ WickGreen, RandomWickGreen, 
  WickPureQ, WickDensityMatrix,
  WickOccupation };

(* supporting utilities *)
{ WickFlop, RandomWickFlop };

{ WickCircuit, RandomWickCircuit, RandomWickCircuitSimulate };

{ WickScramblingCircuit, WickScramblingSimulate };

{ WickLindbladSolve,
  WickSteadyState };
{ WickSimulate, $WickMinorSteps };
{ WickMonitor };

{ WickLogarithmicNegativity };
{ WickEntropy, WickEntanglementEntropy, WickMutualInformation };

(* VonNeumann.wl *)
{ QuantumLog };


Begin["`Private`"] (* Fermionic quantum computation *)

(**** <WickState> ****)
WickState::usage = "WickState[mat] represents a fermionic Gaussian pure state without pairing correlation, which consists of occupied dressed fermion modes di that are related to the bare modes di = Sum[mat[i,j] c[j], {j, 1, n}]."

WickState /:
MakeBoxes[ws:WickState[{type:(0|Null), n_Integer},  ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { If[type === Null, "Null state", "Vacuum state"] }
    },
    {},
    fmt,
    "Interpretable" -> Automatic
  ]

WickState /:
MakeBoxes[ws:WickState[trs_?MatrixQ,  ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ws },
      BoxForm`SummaryItem @ { "Particles: ", Length @ trs }
    },
    { BoxForm`SummaryItem @ { "Transformation: ",ArrayShort @ trs }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* canonicalization *)
WickState[trs_?MatrixQ, rest___] :=
  WickState[SparseArray @ trs, rest] /; 
  Head[trs] =!= SparseArray

(* initialization by occupation numbers *)
WickState[vv_, n_Integer, rest___?OptionQ] := Module[
  { ww = PadRight[Normal @ vv, n, vv],
    kk },
  kk = Flatten @ Position[ww, 1];
  WickState[One[n][[kk]], rest]
] /; VectorQ[vv, BinaryQ]


WickState /:
Normalize[ws:WickState[{0|1, _Integer}, ___]] = ws

WickState /:
Normalize[WickState[trs_?MatrixQ, rest___]] := Module[
  {qq, rr},
  {qq, rr} = QRDecomposition[ConjugateTranspose @ trs];
  WickState[qq, rest]
]


WickState /:
Elaborate[ws_WickState] := ExpressionFor[Matrix @ ws]

WickState /:
ExpressionFor[ws_WickState, ss:{___?SpeciesQ}] := 
  ExpressionFor[Matrix @ ws, Select[ss, FermionQ]]


WickState /:
Matrix[ws:WickState[_?MatrixQ, ___], ss:{___?SpeciesQ}] :=
  MatrixEmbed[Matrix @ ws, Select[ss, FermionQ], ss]

WickState /: (* null state *)
Matrix[WickState[{Null, n_Integer}, ___]] := Zero @ Power[2, n]

WickState /: (* vacuum state *)
Matrix[WickState[{0, n_Integer}, ___]] := PadRight[{1}, Power[2, n]]

WickState /:
Matrix[WickState[trs_?MatrixQ, ___]] := Module[
  { n = Last[Dimensions @ trs],
    mm, vv },
  mm = JordanWignerTransform[n]; (* fermion annihilators *)
  vv = ConjugateTranspose[Apply[Dot, trs.mm]] . PadRight[{1}, Power[2, n]];
  CanonicalizeVector[vv]
]
(**** </WickState> ****)


RandomWickState::usage = "RandomWickState[{n, 0}] randomly generates a Gaussian pure state of n fermion modes."

RandomWickState[n_Integer, opts___?OptionQ] := 
  RandomWickState[{RandomInteger @ {0, n}, n}, opts]

RandomWickState[{0, n_Integer}, opts___?OptionQ] :=
  WickState[{0, n}, opts] (* the vacuum state *)

RandomWickState[{m_Integer, n_Integer}, opts___?OptionQ] := Module[
  { uu, kk },
  kk = RandomSample[Range @ n, m];
  uu = RandomUnitary[n];
  WickState[uu[[kk]], opts]
]


(**** <globalGateQ> ****)
globalGateQ::usage = "globalGateQ[op] returns True if the gate op acts on the whole system; and False otherwise."

globalGateQ[op:_Symbol[__]] := Or[Length[op] == 1, OptionQ @ op[[2]]]

globalGateQ[_] = False
(**** </globalGateQ> ****)


(**** <WickUnitary> ****)
WickUnitary::usage = "WickUnitary[u] represents the Gaussian unitary gate corresponding to the canonical transformation of the fermion modes characterized by the unitary matrix u."

WickUnitary /:
MakeBoxes[op:WickUnitary[uu_?MatrixQ, ___], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op },
      BoxForm`SummaryItem @ If[
        globalGateQ[op],
        { "Dimensions: ", Dimensions @ uu },
        { "Acting on: ", op[[2]] }
      ]
    },
    { BoxForm`SummaryItem @ { "Transformation: ", ArrayShort @ uu }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* conversion *)
WickUnitary[ham_WickHermitian, dt_?NumericQ, opts___?OptionQ] :=
  WickUnitary[MatrixExp[-I*dt*First[ham]], opts]

WickUnitary /:
Normal[WickUnitary[mm_?MatrixQ, ___], rest___] := Normal[mm, rest]

WickUnitary /:
MatrixForm[WickUnitary[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickUnitary /:
ArrayShort[WickUnitary[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

WickUnitary /:
Dagger @ WickUnitary[mat_?MatrixQ, kk:Repeated[{___Integer}, {0, 1}], opts___?OptionQ] := 
  WickUnitary[
    ConjugateTranspose @ mat, kk,
    ReplaceRulesBy[{opts}, "Label" -> auxSuperDagger]
  ]

WickUnitary /:
Dot[
  WickUnitary[a_?MatrixQ, any___], 
  WickUnitary[b_?MatrixQ, other___]
] :=
  WickUnitary[Dot[a, b], any, other]


WickUnitary /:
ExpressionFor[op:WickUnitary[_?MatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

WickUnitary /: (* fallback *)
ExpressionFor[op_WickUnitary, ___] = op


WickUnitary /:
Matrix[op:WickUnitary[_?MatrixQ, kk:{__Integer}, ___], n_Integer] := 
  MatrixEmbed[Matrix @ op, kk, n]

WickUnitary /:
Matrix[op:WickUnitary[mat_?MatrixQ, ___]] := Module[
  { hh = MatrixLog[mat],
    mm, n },
  n = If[ globalGateQ[op],
    Last[Dimensions @ mat], 
    Length @ op[[2]]
  ];
  mm = JordanWignerTransform[n];
  mm = TensorContract[
    Transpose[ConjugateTranspose /@ mm, {3, 1, 2}] . hh . mm,
    {{2, 3}}
  ];
  MatrixExp[mm]
]

WickUnitary /:
Matrix[op:WickUnitary[_?MatrixQ, kk:{__Integer}, ___?OptionQ], ss:{__?SpeciesQ}] := Module[
  { cc = Select[ss, FermionQ] },
  MatrixEmbed[Matrix[op, Length @ cc], cc, ss]
]

WickUnitary /:
Matrix[op:WickUnitary[_?MatrixQ, ___?OptionQ], ss:{__?SpeciesQ}] := 
  MatrixEmbed[Matrix @ op, Select[ss, FermionQ], ss]

WickUnitary /: (* fallback *)
Matrix[op_WickUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]

(* acting on Wick state *)
WickUnitary[uu_?MatrixQ, ___?OptionQ][WickState[mm_?MatrixQ, rest___]] :=
  WickState[mm . ConjugateTranspose[uu], rest]

(* acting on Wick state *)
WickUnitary[uu_?MatrixQ, kk:{__Integer}, ___?OptionQ][WickState[mm_?MatrixQ, rest___]] :=
  Module[
    { new = mm },
    new[[All, kk]] = new[[All, kk]] . ConjugateTranspose[uu];
    WickState[new, rest]
  ]


WickUnitary[uu_?MatrixQ, opts___?OptionQ][c_?FermionQ] :=
  WickUnitary[uu, c @ Range @ Length @ uu, opts]

WickUnitary[uu_?MatrixQ, kk:{__Integer}, opts___?OptionQ][c_?FermionQ] :=
  WickUnitary[uu, c @ kk, opts]

WickUnitary /:
ParseGate[WickUnitary[u_, cc:{__?FermionQ}, rest___]] :=
  Gate[cc, rest]
(**** </WickUnitary> ****)


RandomWickUnitary[n_Integer, rest___] :=
  WickUnitary[RandomUnitary @ n, rest]

RandomWickUnitary[kk:{__Integer}, rest___] :=
  WickUnitary[RandomUnitary @ Length @ kk, kk, rest]

(**** <WickHermitian> ****)
WickHermitian::usage = "WickHermitian[m] represents a quadractic Hermitian operator (\[CapitalSigma]ij Dagger[ai] mij ajj, where m is a Hermitian matrix."

WickHermitian /:
MakeBoxes[op:WickHermitian[mat_?MatrixQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickHermitian, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", Length @ mat },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ mat }
    },
    { BoxForm`SummaryItem @ { "Matrix: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickHermitian /:
Normal[WickHermitian[mat_?MatrixQ, ___], rest___] :=
  Normal[mat, rest]

WickHermitian /:
MatrixForm[WickHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickHermitian /:
ArrayShort[WickHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


WickHermitian /:
ExpressionFor[WickHermitian[mat_?MatrixQ, ___], aa:{__?FermionQ}] :=
  Garner[ MultiplyDot[Dagger @ aa, mat . aa] ]

WickHermitian /:
Matrix[op:WickHermitian[mat_?MatrixQ, ___]] := Module[
  { n = Length[mat],
    xy, mm },
  xy = JordanWignerTransform[n];
  mm = Transpose[ConjugateTranspose /@ xy, {3, 1, 2}] . mat . xy;
  TensorContract[mm, {{2, 3}}]
]
(**** </WickHermitian> ****)


RandomWickHermitian[n_Integer, opts___?OptionQ] := 
  WickHermitian[RandomHermitian @ n, opts]


(**** <WickOdds> ****)
WickOdds::usage = "WickOdds[spec] represents probability for the fermionic Gaussian process specified by spec. See WickJump for spec."

WickOdds[jmp:{__?patternWickJumpQ}][in_WickState] := Module[
  { odds },
  odds = Through[Map[WickOdds, jmp][in]];
  Merge[odds, Total]
]

(* on the null state *)
WickOdds[_][in:WickState[{Null, _}, ___]] = Rule[in, 0]


(* annihilator on the vacuuum state *)
WickOdds[_?VectorQ -> 0|2][WickState[{0, n_Integer}, rest___]] = 
  Rule[WickState[{0, n}, rest], 0]

(* annihilator on Wick state *)
WickOdds[vec_?VectorQ -> 0][WickState[trs_?MatrixQ, rest___]] := Module[
  { ovr = Dot[vec, ConjugateTranspose @ trs] },
  If[ ArrayZeroQ[ovr], (* null state *)
    Return @ Rule[WickState[{Null, Length @ vec}, rest], 0]
  ];
  hhd = HouseholderMatrix[ovr];
  new = Rest[ConjugateTranspose[hhd] . trs];
  If[new == {}, new = {0, Length @ vec}]; (* the vacuum state *)
  Rule[WickState[new, rest], NormSquare @ ovr]
]


(* creator on fully occupied state *)
WickOdds[vec_?VectorQ -> 1|3][WickState[trs_?MatrixQ, rest___]] := 
  Rule[WickState[{Null, Length @ vec}, rest], 0] /; (* the null state *)
  Length[trs] == Length[vec]

(* creator on the vacuuum state *)
WickOdds[vec_?VectorQ -> 1][WickState[{0, _Integer}, rest___]] := Rule[
  WickState[SparseArray @ {Normalize @ vec}, rest],
  NormSquare[vec]
]

(* creattor on the Wick state *)
WickOdds[vec_?VectorQ -> 1][WickState[trs_?MatrixQ, rest___]] := Module[
  { qq = Prepend[trs, vec],
    rr },
  {qq, rr} = QRDecomposition[N @ ConjugateTranspose @ qq];
  Rule[
    WickState[qq, rest], 
    AbsSquare[Whole @ Diagonal @ rr]
  ]
]


(* Dagger[d]**d on Wick state *)
WickOdds[vec_?VectorQ -> 2][WickState[trs_?MatrixQ, rest___]] := Module[
  { ovr = Dot[vec, ConjugateTranspose @ trs],
    hhd, new, rmd },
  hhd = HouseholderMatrix[ovr];
  new = Rest[ConjugateTranspose[hhd] . trs];
  new = Prepend[new, vec];
  {new, rmd} = QRDecomposition[N @ ConjugateTranspose @ new];
  Rule[
    WickState[new, rest],
    NormSquare[ovr] * AbsSquare[Whole @ Diagonal @ rmd]
  ]
]


(* d**Dagger[d] on the vacuuum state *)
WickOdds[vec_?VectorQ -> 3][in:WickState[{0, _Integer}, rest___]] :=
  Rule[in, NormSquare[vec]^2]

(* d**Dagger[d] on the Wick state *)
WickOdds[vec_?VectorQ -> 3][WickState[trs_?MatrixQ, rest___]] := Module[
  { new = Prepend[trs, vec], 
    rmd, ovr, prb },
  {new, rmd} = QRDecomposition[N @ ConjugateTranspose @ new];
  prb = AbsSquare[Whole @ Diagonal @ rmd];
  If[ ZeroQ[prb], (* null state *)
    Return @ Rule[WickState[{Null, Length @ vec}, rest], 0]
  ];
  ovr = Dot[vec, ConjugateTranspose @ new];
  hhd = HouseholderMatrix[ovr];
  new = Rest[ConjugateTranspose[hhd] . new];
  Rule[WickState[new, rest], NormSquare[ovr] * prb]
]


(* WickNonunitary on WickState *)
WickOdds[non_?SquareMatrixQ -> fac_?NumericQ][in_WickState] := Module[
  { new, rmd },
  new = non . ConjugateTranspose[First @ in];
  {new, rmd} = QRDecomposition[N @ new];
  Rule[
    WickState[new],
    AbsSquare[fac] * AbsSquare[Whole @ Diagonal @ rmd]
  ]
] /; MatrixQ[First @ in]

(* WickNonunitary on the vacuum state  *)
WickOdds[non_?SquareMatrixQ -> fac_?NumericQ][in_WickState] :=
  Rule[in, AbsSquare @ fac] /; in[[1, 1]] == 0

(* WickNonunitary on the null state  *)
WickOdds[non_?SquareMatrixQ -> fac_?NumericQ][in_WickState] = 
  Rule[in, 0]


(* Nesting WickNonunitary *)
WickOdds[spec_Rule][in_WickState -> prb_?NumericQ] := Module[
  { res = WickOdds[spec][in] },
  MapAt[Times[#, prb]&, res, 2]
]
(**** </WickOdds> ****)


patternWickJumpQ::usage = "patternWickJumpQ[pat] returns True if pat is a pattern of the form v -> k, v is a vector and k = 0, 1, 2, 3."

patternWickJumpQ[_?VectorQ -> (0|1|2|3)] = True

patternWickJumpQ[_] = False


(**** <WickJump> ****)
WickJump::usage = "WickJump[mat] represents a set of quantum jump operators, which are linear combinations of bare fermion modes with coefficients given by the elements of complex matrix mat."

WickJump /:
MakeBoxes[jmp:WickJump[spec:{__?patternWickJumpQ}, ___], fmt_] := Module[
  { m = Length[spec], 
    n = Length @ spec[[1, 1]] },
  BoxForm`ArrangeSummaryBox[
    WickJump, jmp, None,
    { BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", MatrixForm @ Map[ArrayShort, spec, {2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* conversion *)
WickJump[WickMeasurement[msr_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickJump[
    Riffle[Thread[mat -> 2], Thread[mat -> 3]],
    more, opts
  ]


WickJump /:
ExpressionFor[jmp_WickJump, ss:{__?SpeciesQ}] := Module[
  { cc = Select[ss, FermionQ] },
  Map[ExpressionFor[#, cc]&, Matrix @ jmp]
]


WickJump /:
Matrix[jmp_WickJump, ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ jmp, Select[ss, FermionQ], ss]

WickJump /:
Matrix[WickJump[jmp_List]] := Map[matWickJump, jmp]
(* Returns the list of the matrices representing the jump operators. *)

(* d ** rho ** Dagger[d] *)
matWickJump[vec_?VectorQ -> 0] := 
  Dot[vec, JordanWignerTransform @ Length @ vec]

(* Dagger[d] ** rho ** d *)
matWickJump[vec_?VectorQ -> 1] := 
  ConjugateTranspose @ matWickJump[vec -> 0]


(* Dagger[d] ** d ** rho ** Dagger[d] ** d *)
matWickJump[vec_?VectorQ -> 2] := With[
  { mat = matWickJump[vec -> 0] },
  Dot[ConjugateTranspose @ mat, mat]
]

(* d ** Dagger[d] ** rho ** d ** Dagger[d] *)
matWickJump[vec_?VectorQ -> 3] := With[
  { mat = matWickJump[vec -> 0] },
  Dot[mat, ConjugateTranspose @ mat]
]


WickJump /: 
NonCommutativeQ[_WickJump] = True

WickJump /:
MultiplyKind[_WickJump] = Fermion

WickJump /:
Multiply[pre___, jmp_WickJump, ws_WickState] := Multiply[pre, jmp @ ws]

WickJump[jmp:{__?patternWickJumpQ}, ___][in_WickState] := Module[
  { odds },
  odds = WickOdds[jmp][in];
  RandomChoice[Values[odds] -> Keys[odds]]
]

WickJump /:
WickOdds[jmp_WickJump] := WickOdds[First @ jmp]
(**** </WickJump> ****)


RandomWickJump::usage = "RandomWickJump[{k_Integer, n_Integer}] returns WickJump consisting of k linear combinations of n Dirac fermion operators.\nRandomWickJump[n] chooses k randomly from 1 through n."

RandomWickJump[{k_Integer, n_Integer}, opts___?OptionQ] := Module[
  { vv = Table[RandomReal[] * RandomVector[n], k],
    ss = RandomChoice[{0, 1, 2, 3}, k] },
  WickJump[Thread[vv -> ss], opts]
]

RandomWickJump[n_Integer, opts___?OptionQ] :=
  RandomWickJump[{RandomInteger[{1, n}], n}, opts]


(**** <WickFlop> ****)
WickFlop::usage = "WickFlop[v -> 0] represents annihilation operator d := Sum[v[i]*c[i], i].\nWickFlop[v -> 1] represents creation operator Dagger[d].\nWickFlop[v -> 2] represents Dagger[d] ** d.\nWickFlop[v -> 3] represents d ** Dagger[d].\n WickFlop[{\[Ellipsis], vi -> ki, \[Ellipsis]}] represents a series of consecutive operations in the reversed order.\nWickFlop is not essential for an efficient classical simulation; merely a utility for convenience."

WickFlop /:
MakeBoxes[jmp:WickFlop[spec:{__?patternWickJumpQ}, ___], fmt_] := Module[
  { m = Length[spec], 
    n = Length @ spec[[1, 1]] },
  BoxForm`ArrangeSummaryBox[
    WickFlop, jmp, None,
    { BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", MatrixForm @ Map[ArrayShort, spec, {2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

WickFlop[op_?patternWickJumpQ][in_WickState] :=
  First[WickOdds[op] @ in]

WickFlop[ops:{___?patternWickJumpQ}][in_WickState] :=
  Fold[#2[#1]&, in, Map[WickFlop, ops]]
(**** </WickFlop> ****)


RandomWickFlop::usage = "RandomWickFlop[{k_Integer, n_Integer}] returns WickFlop consisting of k linear combinations of n Dirac fermion operators.\nRandomWickFlop[n] chooses k randomly from 1 through n."

RandomWickFlop[spec_] := Apply[WickFlop, RandomWickJump[spec]]


(**** <WickMeasurement> ****)
WickMeasurement::usage = "WickMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nWickMeasurement[{k1, k2, \[Ellipsis]}, n] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nWickMeasurement[mat] represents a sequence of measurement on the dressed Dirac fermion modes b[i] := Sum[m[[i,j]] c[j], {j, n}] expressed in terms of Dirac fermion modes c[k].\nWickMeasurement[spec][ws] simulates the measurement on Wick state ws, and returns the post-measurement state."

WickMeasurement::odd = "The second dimension of the input matrix `` is odd: ``."

WickMeasurement::dressed = "A vector of coefficients `` cannot describe a proper dressed Dirac fermion mode."


WickMeasurement /:
MakeBoxes[msr:WickMeasurement[mat_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    WickMeasurement, msr, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", n },
      BoxForm`SummaryItem @ { "Dressed modes: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]


(* canonicalization *)
WickMeasurement[k_Integer, n_Integer, rest___] :=
  WickMeasurement[{k}, n, rest]

(* canonicalization *)
(* NOTE: kk = {} may happen, e.g., in RandomWickCircuit. *)
WickMeasurement[kk:{___Integer}, n_Integer, rest___] :=
  WickMeasurement @ One[n][[kk]]

(* canonicalization *)
WickMeasurement[mat_?MatrixQ, rest___] :=
  WickMeasurement[SparseArray @ mat, rest] /;
  Head[mat] =!= SparseArray

WickMeasurement /:
ExpressionFor[WickMeasurement[mat_?MatrixQ, ___], rest___] := Module[
  { jmp = WickJump @ Thread[mat -> 0] },
  ExpressionFor[jmp, rest]
]

WickMeasurement /:
Matrix[WickMeasurement[mat_?MatrixQ, ___], rest___] := Module[
  { jmp = WickJump @ Thread[mat -> 0] },
  Matrix[jmp, rest]
  (* NOTE: Returned are UNNORMALIZED projection operators. *)
]

WickMeasurement /:
Normalize[WickMeasurement[mat_?MatrixQ, rest___], ___] :=
  WickMeasurement[Map[Normalize, mat], rest]

WickMeasurement /:
Dagger @ WickMeasurement[mat_?MatrixQ, rest___] :=
  WickMeasurement[Reverse @ mat, rest]

WickMeasurement /:
Times[z_, WickMeasurement[mm_, rest___]] :=
  WickMeasurement[z * mm, rest]


WickMeasurement /:
MatrixForm[WickMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickMeasurement /:
ArrayShort[WickMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


WickMeasurement /:
NonCommutativeQ[_WickMeasurement] = True

WickMeasurement /:
MultiplyKind[_WickMeasurement] = Fermion

WickMeasurement /:
Multiply[pre___, msr_WickMeasurement, ws_WickState] := Multiply[pre, msr @ ws]


(* NOTE: This may happen, e.g., in RandomWickCircuit. *)
WickMeasurement[{}, ___][in_WickState] = in


WickMeasurement[mat_?MatrixQ, ___][in_WickState] :=
  Fold[theWickMeasurement, in, Identity /@ mat]

theWickMeasurement[in:WickState[trs_?MatrixQ, rest___], vec_?VectorQ] := Module[
  { odds, pick },
  odds = WickOdds[{vec -> 2, vec -> 3}] @ in;
  pick = RandomChoice[Values[odds] -> Keys[odds]];
  $MeasurementOut[vec] = pick /. Thread[Keys[odds] -> {1, 0}];
  pick
]


WickMeasurement[any__][c_?FermionQ] := WickMeasurement[any]

WickMeasurement[mat_?MatrixQ, opts___?OptionQ][c_?FermionQ] := Module[
  { mm = Normal[ZeroQ @ mat],
    kk, cc },
  kk = Last @ Transpose @ Position[mm, False, {2}];
  WickMeasurement[mat, c @ kk, opts]
]
(* TODO: Currently, it is assumed that the measurements are local. *)

WickMeasurement /:
ParseGate[WickMeasurement[{}, ___]] = "Spacer"

WickMeasurement /:
ParseGate[
  WickMeasurement[mat_?MatrixQ, cc:{__?FermionQ}, opts___?OptionQ], 
  more___?OptionQ
] :=
  Map[Gate[{#}, "Shape" -> "Measurement", more, opts]&, cc]


Readout[WickMeasurement[m_?MatrixQ, ___]] := 
  Readout[First @ m] /; Length[m] == 1

Readout[WickMeasurement[m_?MatrixQ, ___]] := 
  Map[Readout, m]
(**** </WickMeasurement> ****)


RandomWickMeasurement::usage = "RandomWickMeasurement[{k, n}] randomly generates a WickMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomWickMeasurement[n] randomly selects k from {1, 2, \[Ellipsis], n}."

RandomWickMeasurement[{k_Integer, n_Integer}] :=
  WickMeasurement @ Table[RandomVector @ n, k]

RandomWickMeasurement[n_Integer] :=
  RandomWickMeasurement @ {RandomInteger @ {1, n}, n}


(**** <WickGreen> ****)
WickGreen::usage = "WickGreen[ws, {k1, k2, \[Ellipsis], km}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis], km} with respect to WickState ws.\nWickGreen[data] or WickGreen[data, {k1, k2, \[Ellipsis], km}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Wick or BdG states.\nWickGreen[{k1, k2, \[Ellipsis], km}] represents an operator form of WickGreen to be applied to Wick or Nambu state."

(* shortcut *)
WickGreen[ws_WickState] :=
  WickGreen[ws, Range @ FermionCount @ ws]

(* vacuum state *)
WickGreen[WickState[{0, _Integer}, ___], kk:{___Integer}] :=
  One[Length @ kk]

(* null state *)
WickGreen[WickState[{Null, _Integer}, ___], kk:{___Integer}] = {{}}

WickGreen[WickState[trs_?MatrixQ, ___], kk:{___Integer}] := Module[
  { n = Length[kk],
    alt = trs[[All, kk]] },
  One[n] - ConjugateTranspose[alt].alt
]


(* for large data *)
WickGreen[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := 
  arrayMap[WickGreen[#, kk]&, data] /;
  ArrayQ[data, _, MatchQ[#, _WickState]&]
(**** </WickGreen> ****)


RandomWickGreen::usage = "RandomWickGreen[n] generates a ..."

RandomWickGreen[n_Integer] := Module[
  { dd, uu },
  dd = RandomReal[{0, 1}, n];
  uu = RandomUnitary[n];
  uu . DiagonalMatrix[dd] . Conjugate[uu]
]


(**** <WickOccupation> ****)
WickOccupation::usage = "WickOccupation[in, {k1, k2, \[Ellipsis]}] returns a list of the expectation values of occupation on fermion modes in {k1, k2, \[Ellipsis]} with respect to WickState in.\nWickOccupation[in] is equivalent to WickOccupation[in, Range[n]], where n is the number of fermion modes for which input Wick state in is defined for."

(* shortcut *)
WickOccupation[ws_WickState] :=
  WickOccupation[ws, Range @ FermionCount @ ws]

(* canonical form for normal models *)
WickOccupation[ws_WickState, kk:{___Integer}] := Module[
  { grn = WickGreen[ws, kk] },
  grn = 1 - Diagonal[grn];
  grn[[kk]]
]

(* for large data *)
WickOccupation[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := 
  arrayMap[WickOccupation[#, kk]&, data] /;
  ArrayQ[data, _, MatchQ[#, _WickState]&]
(**** </WickOccupation> ****)


(**** <WickPureQ> ****)
WickPureQ::usage = "WickPureQ[grn] returns True if the single-particle Green's function matrix grn represents a prue state; False, otherwise.\nWickPureQ[ws] always return True for a Wick state ws."

WickPureQ[ws_WickState] = True

WickPureQ[grn_?SquareMatrixQ] := Module[
  { one = One[Dimensions @ grn],
    new },
  new = one - 2*grn;
  ArrayZeroQ[one - new.new]
]

WickPureQ[_] = False
(**** </WickPureQ> ****)


(**** <WickDensityMatrix> ****)
WickDensityMatrix::usage = "WickDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function matrix grn associated with a fermionic Gaussian state.\nWickDensityMatrix[ws] returns the density matrix corresponding to Wick state ws."

WickDensityMatrix::num = "Only numerical matrices are allowed."

WickDensityMatrix[ws_?WickState] := WickDensityMatrix[WickGreen @ ws]

WickDensityMatrix[grn_?MatrixQ] := Module[
  { n = Length[grn],
    cc, gg, uu, id },  
  (* Jordan-Wigner transformation *)
  cc = JordanWignerTransform[n];
  id = One @ Power[2, n];
  {gg, uu} = Eigensystem[N @ grn];
  (* NOTE: N[...] is to avoid additional normaliztaion of uu and sorting. *)
  cc = Conjugate[uu] . cc; (* dressed modes *)
  cc = MapThread[Dot, {ConjugateTranspose /@ cc, cc}];
  cc = MapThread[#1*id + (1-2*#1)*#2&, {gg, cc}];
  Dot @@ cc
] /; If[ MatrixQ[grn, NumericQ], True,
  Message[WickDensityMatrix::num];
  False
]
(**** </WickDensityMatrix> ****)


(**** <WickCircuit> ****)
WickCircuit::usage = "WickCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit consisting of fermionic Gaussian gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes without pairing correlation."

WickCircuit /:
MakeBoxes[wc:WickCircuit[gg_List, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", FermionCount @ wc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", Short @ gg }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickCircuit /: 
NonCommutativeQ[_WickCircuit] = True

WickCircuit /:
MultiplyKind[_WickCircuit] = Fermion

WickCircuit /:
Multiply[pre___, wc_WickCircuit, in_WickState] :=
  Multiply[pre, wc @ in]

WickCircuit[gg_List, ___][in_WickState] :=
  Fold[#2[#1]&, in, gg]


WickCircuit /:
Show[wc_WickCircuit, rest___] := Graphics[wc, rest]

WickCircuit /:
Graphics[wc:WickCircuit[gg_List], more___?OptionQ] := Module[
  { c },
  Let[Fermion, c];
  Graphics[wc, c, more]
]

WickCircuit /:
Graphics[wc:WickCircuit[gg_List, opts___?OptionQ], c_Symbol?FermionQ, more___?OptionQ] := Module[
  { n = FermionCount[wc],
    cc, qc },
  cc = c[Range @ n];
  qc = gg /. {
    WickCircuit[{}] -> "Spacer",
    elm_WickCircuit :> Graphics[elm],
    elm_WickState :> ExpressionFor[elm, cc],
    elm_WickMeasurement :> ParseGate[elm @ c],
    elm_WickUnitary :> ParseGate[elm @ c],
    elm_WickNonunitary :> ParseGate[elm @ c]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]
(**** </WickCircuit> ****)


(**** <RandomWickCircuit> ****)
RandomWickCircuit::usage = "RandomWickCircuit[{uni, p}, dep] generate a random quantum circuit on non-interacting fermion modes, where layers of unitary gate uni (WickUnitary[\[Ellipsis]]) alternate with layers of measurements (WickMeasurement[\[Ellipsis]]) on fermion modes selected randomly with probability p to form an overall depth dep.\nRandomWickCircuit[{ham, pdf, p}, k] unitary layers of random unitary gate uni=Exp[-\[ImaginaryI] ham \[Tau]] with single-particle Hamiltonian ham ( n\[Times]n Hermitian matrix or WickHermitian[\[Ellipsis]]) and the random evolution time \[Tau] distributed according to the probability distribution function pdf.\nRandomWickCircuit[{ham, p}, dep] assumes that the evolution time is uniformly distributed over the interval [0,2\[Pi] n/max], where max is the maximum of the absolute values of the entries of ham.\nRandomWickCircuit[ham, dep] generates a circuit for n fermion modes where each unitary layer corresponds to time evolution U=exp[-\[ImaginaryI] ham \[Tau]] with the evolution time \[Tau] distributed by P(\[Tau])\[Proportional]exp[-n \[Tau]] and each measurement layer measures a fermion mode with probability p=1/n."

(* fixed interaction time *)
RandomWickCircuit[{uu_WickUnitary, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[uu],
      mm },
    mm = RandomPick[Range @ n, p, k];
    WickCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[WickMeasurement[#, n]&, mm]
    ]
  ]

(* arbitrary distribution of evolution time *)
RandomWickCircuit[{ham_WickHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      ab, tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = Map[WickUnitary[MatrixExp[-I*hh*#]]&, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[WickMeasurement[#, n]&, mm];
    WickCircuit @ Riffle[uu, mm]
  ]

(* uniform distribution of evolution time *)
RandomWickCircuit[{ham_WickHermitian, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      max, pdf },
    max = Max[Abs @ First @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    RandomWickCircuit[{ham, pdf, p}, k]
  ]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
RandomWickCircuit[ham_WickHermitian, k_Integer] := Module[
  { n = FermionCount[ham] },
  RandomWickCircuit[{ham, ExponentialDistribution[n], 1./n}, k]
]
(**** </RandomWickCircuit> ****)


(**** <RandomWickCircuitSimulate> ****)
RandomWickCircuitSimulate::usage = "RandomWickCircuitSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomWickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

Options[RandomWickCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RWC"
}

$RandomWickCircuitPatterns = Alternatives[
  {_WickUnitary, _?NumericQ}, 
  {_WickNonunitary, _?NumericQ}, 
  {_WickHermitian, _, _?NumericQ},
  {_WickHermitian, _?NumericQ},
  _WickHermitian
];

RandomWickCircuitSimulate[in_, spec_, depth_Integer, opts___?OptionQ] := 
  RandomWickCircuitSimulate[in, spec, {depth, 2}, opts]

RandomWickCircuitSimulate[
  in_WickState,
  spec:$RandomWickCircuitPatterns,
  {depth_Integer, ds:(_Integer|All)},
  opts:OptionsPattern[{RandomWickCircuit, RandomWickCircuitSimulate}]
] := 
Module[
  { progress = k = 0,
    data, more, qc, n, m },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  data = Table[
    qc = RandomWickCircuit[spec, depth];
    Table[
      progress = ++k / N[n*m];
      FoldList[Construct[#2, #1]&, in, First @ qc][[1;;All;;ds]],
      (* NOTE: No explicit normalization here because both the unitary and measurement layers produce NORMALIZED states. *)
      m 
    ],
    n
  ];
  (* save data *)
  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ RandomWickCircuitSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
]
(**** </RandomWickCircuitSimulate> ****)


(**** <WickNonunitary> ****)
WickNonunitary::usage = "WickNonunitary[{fac, non}] represents a fermionic Gaussian gate (without pairing correlation) characterized by the damping factor fac := Exp[-gmm*\[Tau]] and n\[Times]n non-unitary matrix non := MatrixExp[-\[ImaginaryI](ham - \[ImaginaryI] dmp)\[Tau]].\nWickNonunitary[{ham, jmp}, \[Tau]] is a shortcut to construct WickNonunitary using WickDamping."

WickNonunitary /:
MakeBoxes[op:WickNonunitary[{fac_?NumericQ, non_?MatrixQ}, rest___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickNonunitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ non },
      If[Not[globalGateQ @ op], BoxForm`SummaryItem @ {"Acting on: ", op[[2]]}, Nothing],
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Transformation: ", ArrayShort @ non }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickNonunitary[{ham_?MatrixQ, jmp_}, dt_?NumericQ, rest___] :=
  WickNonunitary[{WickHermitian @ ham, jmp}, dt, rest]

WickNonunitary[{ham_WickHermitian, jmp:{__?patternWickJumpQ}}, dt_?NumericQ, rest___] :=
  WickNonunitary[{ham, WickJump @ jmp}, dt, rest]

(* shortcut *)
WickNonunitary[
  {WickHermitian[ham_?MatrixQ], jmp_WickJump},
  dt_?NumericQ, 
  rest___
] := Module[
  {dmp, gmm},
  {dmp, gmm} = WickDamping[jmp];
  WickNonunitary[
    { Exp[-dt*gmm], 
      MatrixExp[-I*dt*(ham - I*dmp)] 
    },
    rest
  ]
]

WickNonunitary /:
MatrixForm @ WickNonunitary[{fac_?NumericQ, non_?MatrixQ}, rest___] :=
  MatrixForm[non]

WickNonunitary /:
ArrayShort @ WickNonunitary[{fac_?NumericQ, non_?MatrixQ}, rest___] :=
  ArrayShort[non]

WickNonunitary /:
Dagger @ WickNonunitary[{
  fac_?NumericQ, non_?MatrixQ},
  kk:Repeated[{___Integer}, {0, 1}], 
  opts___?OptionQ
] := WickNonunitary[
    {fac, ConjugateTranspose @ non}, kk,
    ReplaceRulesBy[{opts}, "Label" -> auxSuperDagger]
  ]


WickNonunitary /:
Matrix[
  op:WickNonunitary[{_?NumericQ, _?MatrixQ}, kk:{__Integer}, ___], 
  n_Integer
] := MatrixEmbed[Matrix @ op, kk, n]

WickNonunitary /:
Matrix[op:WickNonunitary[{fac_?NumericQ, non_?MatrixQ}, ___]] := Module[
  { n = FermionCount[non],
    log = MatrixLog[non],
    mat, wjt },
  wjt = JordanWignerTransform[n];
  mat = Dot[Transpose[Conjugate @ wjt, {3, 1, 2}], log, wjt];
  mat = TensorContract[mat, {{1, 3}}];
  SparseArray[fac * MatrixExp[mat]]
]


(* acting on WickState *)
WickNonunitary[{fac_?NumericQ, non_?MatrixQ}, kk:{__Integer}, ___][in_WickState] :=
  Module[
    { new = One[FermionCount @ in] },
    new[[kk, kk]] = non;
    WickNonunitary[{fac, new}] @ in
  ]

WickNonunitary[{fac_?NumericQ, non_?MatrixQ}, ___?OptionQ][in_WickState] := 
  First[WickOdds[non -> fac] @ in]


(* shortcut *)
WickNonunitary /:
WickOdds[WickNonunitary[{fac_, non_}, ___]] := WickOdds[non -> fac]


WickNonunitary[spec_, opts___?OptionQ][c_?FermionQ] :=
  WickNonunitary[spec, c[Range @ FermionCount @ Last @ spec], opts]

WickNonunitary[spec_, kk:{__Integer}, opts___?OptionQ][c_?FermionQ] :=
  WickNonunitary[spec, c @ kk, opts]

WickNonunitary /:
ParseGate[WickNonunitary[_, cc:{__?FermionQ}, rest___]] :=
  Gate[cc, rest, "Label" -> "W"]
(**** </WickNonunitary> ****)


RandomWickNonunitary::usage = "RandomWickNonunitary[n] randomly constructs a WickNonunitary operator on n fermion modes."

RandomWickNonunitary[n_Integer, opts___?OptionQ] := Module[
  { ham = RandomHermitian[n],
    dmp = RandomPositive[n] },
  WickNonunitary[
    {RandomReal[], MatrixExp[-I*ham - dmp]},
    opts
  ]
]

RandomWickNonunitary[kk:{__Integer}, opts___?OptionQ] := With[
  { tmp = RandomWickNonunitary[Length @ kk] },
  WickNonunitary[First @ tmp, kk, opts]
]


(**** <WickDamping> ****)
WickDamping::usage = "WickDamping[jmp] returns a pair {dmp, gmm} of the quadratic kernel dmp and remaining constant term gmm of the effective damping operator that corresponds to to quantum jump operators jmp."

WickDamping[jmp:{___?patternWickJumpQ}] :=
  WickDamping[WickJump @ jmp]

WickDamping[WickJump[jmp_List]] := Module[
  { cls },
  cls = Merge[Reverse /@ jmp, SparseArray];
  Total @ KeyValueMap[theWickDamping, cls]
]

theWickDamping[0, mat_] := {
  Dot[ConjugateTranspose @ mat, mat],
  0
} / 2

theWickDamping[1, mat_] := Module[
  { new },
  new = Dot[ConjugateTranspose @ mat, mat];
  {-new, Re @ Tr @ new} / 2 
]

theWickDamping[2, mat_] := Module[
  { new },
  new = Dot[
    ConjugateTranspose @ mat,
    Map[NormSquare, mat] * mat
  ];
  {new, 0} / 2
]

theWickDamping[3, mat_] := Module[
  { new },
  new = Dot[
    ConjugateTranspose @ mat,
    Map[NormSquare, mat] * mat
  ];
  {-new, Re @ Tr @ new} / 2
]
(**** </WickDamping> ****)


(**** <WickSimulate> ****)
$WickMinorSteps::usage = "$WickMinorSteps is a parameter that controls the behavior of WickSimulate by setting the number of minor steps for the non-unitary gate to make between major steps to update the quantum state."

$WickMinorSteps = 20;

WickSimulate::usage = "WickSimulate[in, ham, jmp, {\[Tau], dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian ham in the WickHermitian form and the quantum jump operators are specified by jmp in the WickJump form. The simulation starts from the initial state IN in the WickState at time 0 and runs to time \[Tau] in steps of size dt."

WickSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

Options[WickSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NWS"
}

WickSimulate[in_WickState, ham_?MatrixQ, rest__] :=
  WickSimulate[in, WickHermitian @ ham, rest]

WickSimulate[in_WickState, ham_WickHermitian, jmp:{__?patternWickJumpQ}, rest__] :=
  WickSimulate[in, ham, WickJump @ jmp, rest]

WickSimulate[in_, ham_, jmp_, {tau_?NumericQ, dt_?NumericQ}, opts___?OptionQ] :=
  WickSimulate[in, ham, jmp, {tau, dt, All}, opts]

WickSimulate[
  in_WickState, 
  ham_WickHermitian,
  jmp_WickJump,
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)}, 
  opts:OptionsPattern[]
] := Module[
  { ns = OptionValue["Samples"],
    progress = 0,
    non, data, more },
    
  non = WickNonunitary[{ham, jmp}, dt/$WickMinorSteps];

  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[ns];
    theWickSimulate[in, non, jmp, {tau, dt}][[1;;All;;ds]],
    {k, ns}
  ];

  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ WickSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
] /; If[ MatrixQ[First @ ham, NumericQ], True,
  Message[WickSimulate::ham, ham];
  False
]

theWickSimulate[in_WickState, non_WickNonunitary, jmp_WickJump, {tau_, dt_}] :=
  Module[
    { t = dt,
      res = {in},
      new = in,
      out },
    While[ t <= tau,
      (* non-unitary evolution *)
      out = Nest[WickOdds[non], new -> 1, $WickMinorSteps];
      If[ RandomReal[] < Last[out],
        new = First[out];
        AppendTo[res, new];
        t += dt;
        Continue[]
      ];
      (* quantum jumps *)
      new = jmp[new];
      AppendTo[res, new];
      t += dt;
    ];
    Return[res]
  ]
(**** </WickSimulate> ****)


(**** <WickMonitor> ****)
WickMonitor::usage = "WickMonitor[in, ham, msr, {nt, dt}] solves the problem of continuous monitoring of a non-interacting many-fermion system by using the Monte Carlo simulation method. The model is specified by the single-particle Hamiltonian ham in the WickHermitian form, and the dressed fermion modes the occupation numbers of which to be monitored are specified by measurement msr in the WickMeasurement form. The simulation starts from the initial state IN in the WickState form at time 0 and goes nt time steps of size dt."

WickMonitor::mat = "The matrix in the first argument of WickMonitor must be a real anti-symmetric matrix."

WickMonitor::num = "The Hamiltonian matrix `` needs to be numeric."

Options[WickMonitor] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "WM"
}

WickMonitor[in_WickState, ham_?MatrixQ, rest___] :=
  WickMonitor[in, WickHermitian @ ham, rest]

WickMonitor[in_WickState, ham_WickHermitian, msr_?MatrixQ, rest___] :=
  WickMonitor[in, ham, WickMeasurement @ msr, rest]

WickMonitor[in_WickState, ham_WickHermitian, msr_WickMeasurement, 
  {tau_, dt_}, rest___] :=
  WickMonitor[in, ham, msr, {tau, dt, All}, rest]

WickMonitor[
  in_WickState, 
  ham_WickHermitian,
  msr_WickMeasurement,
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)}, 
  opts:OptionsPattern[]
] := Module[
  { ns = OptionValue["Samples"],
    progress = 0,
    jmp, dmp, gmm, evo, data, more },
  
  (* NOTE: The unit of time is 1/\gamma, where \gamma is the monitoring rate. *)
  jmp = WickJump[msr];
  {dmp, gmm} = WickDamping[jmp];
  evo = WickUnitary[ham, dt];
  gmm = Exp[-gmm*dt];

  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[ns];
    theWickMonitor[in, evo, gmm, jmp, {tau, dt}][[1;;All;;ds]],
    {k, ns}
  ];

  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ WickSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
] /; If[ MatrixQ[First @ ham, NumericQ], True,
  Message[WickSimulate::ham, ham];
  False
]

theWickMonitor[in_WickState, evo_WickUnitary, prb_?NumericQ, jmp_WickJump, {tau_, dt_}] :=
  Module[
    { t = dt,
      res = {in},
      new = in,
      out },
    While[ t <= tau,
      If[ RandomReal[] < prb,
        new = evo[new];
        AppendTo[res, new];
        t += dt;
        Continue[]
      ];
      (* quantum jumps *)
      new = jmp[new];
      AppendTo[res, new];
      t += dt;
    ];
    Return[res]
  ]
(**** </WickMonitor> ****)


(**** <WickScramblingCircuit> ****)
WickScramblingCircuit::usage = "WickScramblingCircuit[op, spec, dep] generates the main part of a Wick scrambling circuit."

WickScramblingCircuit[a_Integer, rest__] :=
    WickScramblingCircuit[theWickX[a], spec, t]

(* fixed interaction time *)
WickScramblingCircuit[op_, {uu:(_WickUnitary|elm_WickNonunitary), p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[uu],
      vv, ma, mb },
    vv = ConstantArray[uu, k];
    ma = If[ ZeroQ @ p, Nothing, 
      Table[WickMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    mb = If[ ZeroQ @ p, Nothing, 
      Table[WickMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    WickCircuit @ Join[
      Riffle[vv, ma], {op},
      Riffle[Dagger @ vv, mb]
    ]
  ]

(* arbitrary distribution of evolution time *)
WickScramblingCircuit[op_, {ham_WickHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      tt, uu, dg, ma, mb },
    tt = RandomVariate[pdf, k];
    uu = Map[WickUnitary[MatrixExp[-I*hh*#]]&, tt];
    dg = Reverse[Dagger @ uu];
    ma = If[ ZeroQ @ p, Nothing, 
      Table[WickMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    mb = If[ ZeroQ @ p, Nothing, 
      Table[WickMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    WickCircuit @ Join[
      Riffle[uu, ma], {op},
      Riffle[dg, mb]
    ]
  ]

(* uniform distribution of evolution time *)
WickScramblingCircuit[op_, {ham_WickHermitian, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      max, pdf },
    max = Max[Abs @ First @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    WickScramblingCircuit[op, {ham, pdf, p}, k]
  ]

(* canonicalization *)
WickScramblingCircuit[op_, ham_NambuHermitian, k_Integer] :=
  WickScramblingCircuit[op, WickHermitian[ham], k]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
WickScramblingCircuit[op_, ham_WickHermitian, k_Integer] := Module[
    { n = FermionCount[ham] },
    WickScramblingCircuit[op, {ham, ExponentialDistribution[n], 1./n}, k]
  ]

theWickZ::usage = "theWickZ[k] returns the default local unitary operator, A := 1 - 2*Dagger[a[k]]**a[k], for the OTOC."

theWickZ[k_Integer] := WickUnitary[{{-1}}, {k}, "Label" -> Z]

theWickX::usage = "theWickX[k] returns the default local unitary operator, B := Exp[(Pi/2)*(Dagger[a[k]]**a[k+1] - Dagger[a[k+1]]**a[k])], for the OTOC."

theWickX[k_Integer] := WickUnitary[
  SparseArray @ { 
    {0, -1},
    {1,  0}
  },
  {k, k + 1},
  "Label" -> "X"
]
(**** </WickScramblingCircuit> ****)


(**** <WickScramblingSimulate> ****)
WickScramblingSimulate::usage = "WickScramblingSimulate[in, spec, dep] simulates a quantum information scrambling circuit specified by spec (see RandomWickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

Options[WickScramblingSimulate] = {
  "Samples" -> {10, 3}
}

WickScramblingSimulate[in_, a_Integer, rest__] :=
  WickScramblingSimulate[in, {a, 1}, rest]

WickScramblingSimulate[in_, {a_Integer, b_Integer}, 
  spec:$RandomWickCircuitPatterns, rest__] := Module[
    { n = spec },
    If[ListQ @ spec, n = First @ spec];
    n = FermionCount[n];
    WickScramblingSimulate[in, {theWickX[a], theWickZ[b]}, spec, rest]
  ]

WickScramblingSimulate[in_, ua_WickUnitary, rest__] :=
  WickScramblingSimulate[in, {ua, theWickZ[1]}, rest]

WickScramblingSimulate[
  in_WickState,
  {ua_WickUnitary, ub_WickUnitary},
  spec:$RandomWickCircuitPatterns,
  depth_Integer,
  OptionsPattern[]
] := 
Module[
  { qc, n, m },
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  Mean @ Flatten @ Table[
    qc = WickScramblingCircuit[ua, spec, depth];
    Table[theWickOTOC[in, ub, qc], m],
    n
  ]
]

theWickOTOC[in_, ub_, qc_WickCircuit] := Module[
  { va, vb },
  va = Fold[Construct[#2, #1]&, in, First @ qc];
  vb = Join[{ub}, First @ qc, Dagger @ {ub}];
  vb = Fold[Construct[#2, #1]&, in, vb];
  Sqrt @ WickFidelity[va, vb]
]
(**** </WickScramblingSimulate> ****)


(**** <WickFidelity> ****)
WickFidelity::usage = "WickFidelity[a, b] returns the fidelity, i.e., |<a|b>|, between two Wick states a and b."

SetAttributes[WickFidelity, Orderless];

WickFidelity[WickState[{Null, _}, ___], WickState] = 0


WickFidelity[WickState[{0, _}, ___], WickState[{0, _}, ___]] = 1

WickFidelity[WickState[{0, _}, ___], _WickState] = 0


WickFidelity[a_WickState, b_WickState] := 0 /;
  Length[First @ a] != Length[First @ b]

WickFidelity[WickState[m_?MatrixQ, ___], WickState[m_?MatrixQ, ___]] = 1

WickFidelity[a_WickState, b_WickState] := Module[
  { jmp, prb },
  jmp = Thread[First[a] -> 0];
  prb = FoldPairList[theWickFidelity, b, jmp];
  Sqrt[Whole @ prb]
]

theWickFidelity[in_WickState, jmp_?patternWickJumpQ] := With[
  { odds = WickOdds[jmp] @ in },
  {Last @ odds, First @ odds}
]
(**** </WickFidelity> ****)


(**** <WickLindbladSolve> ****)
WickLindbladSolve::usage = "WickLindbladSolve[ham, jmp, in, t] solves the Lindblad equation associated with the Hamiltonia ham (either n\[Times]n matrix or WickHermitian) and a set of quantum jump operators jmp (WickJump), and returns the single-particle Green's function matrix characterizing a fermionic Gaussian mixed state at t. The initial state in may be given in the WickState form or n\[Times]n Green's function matrix."

WickLindbladSolve::chk = "Something is wrong: vector `` is supposed to be zero."

WickLindbladSolve[ham_?MatrixQ, rest__] :=
  WickLindbladSolve[WickHermitian @ ham, rest]

WickLindbladSolve[ham_WickHermitian, jmp:{__?patternWickJumpQ}, rest__] :=
  WickLindbladSolve[ham, WickJump @ jmp, rest]


WickLindbladSolve[ham_, jmp_, in_, t_?NumericQ, rest___] :=
  First @ WickLindbladSolve[ham, jmp, in, {{t}}, rest]

WickLindbladSolve[ham_, jmp_, in_, {t0_?NumericQ, tn_?NumericQ}, rest___] :=
  WickLindbladSolve[ham, jmp, in, {Range[t0, tn]}, rest]

WickLindbladSolve[ham_, jmp_, in_,
  {ti_?NumericQ, tf_?NumericQ, dt_?NumericQ},
  rest___
] := WickLindbladSolve[ham, jmp, in, {Range[ti, tf, dt]}, rest]

WickLindbladSolve[ham_, jmp_, in_WickState, rest__] :=
  WickLindbladSolve[ham, jmp, WickGreen @ in, rest]


(* projective case *)
(* In this case, the equation of motion for G takes the Lindblad form. Furthermore, \varL(I)=0, where \varL is the Lindbland generator. *)
WickLindbladSolve[
  ham_WickHermitian,
  jmp_WickJump,
  grn_?MatrixQ,
  {tt_?VectorQ}
] := Module[
  { n = Length[First @ ham],
    lop, krn, chk, trs, evo },
  (* Lindblad operators *)
  lop = Keys[First @ jmp];
  lop = Map[KroneckerProduct[Conjugate @ #, #]&, lop];
  {krn, chk} = LindbladConvert[First @ ham, lop];
  (* \varL(I) =  0 *)
  If[ Not[ArrayZeroQ @ chk], 
    Message[WickLindbladSolve::chk, ArrayShort @ chk]
  ];
  evo = Map[MatrixExp[krn*#]&, tt];
  trs = LieBasisMatrix[n];
  in = ConjugateTranspose[trs].Flatten[grn];
  out = evo . Rest[in];
  out = ArrayPad[out, {{0, 0}, {1, 0}}, First @ in];
  out = out . Transpose[trs];
  ArrayReshape[out, {Length @ out, n, n}]
] /; ContainsOnly[Values @ First @ jmp, {2, 3}]


(* dissipative case *)
WickLindbladSolve[
  ham_WickHermitian,
  jmp_WickJump,
  grn_?MatrixQ,
  {tt_?VectorQ}
] := Module[
  { xx, yy },
  {xx, yy} = WickLyapunov[First @ ham, First @ jmp];
  LyapunovFunction[xx, yy][grn, tt]
] /; ContainsOnly[Values @ First @ jmp, {0, 1}]

WickLyapunov::usage = "WickLyapunov[ham, jmp] returns a pair {X, Y} of matrics for the Lyapunov equation D[G[t], t] == X.G + G.ConjugateTranspose[X] + Y."

WickLyapunov[ham_?MatrixQ, jmp:{__?patternWickJumpQ}] := Module[
  { cls, xx, yy },
  cls = Merge[Reverse /@ jmp, SparseArray];
  cls = KeyDrop[cls, {2, 3}];
  {xx, yy} = Total @ KeyValueMap[theWickLyapunov, cls];
  {-I*ham - xx, yy}
]

theWickLyapunov[0, mat_?MatrixQ] := Module[
  { dmp },
  dmp = Dot[ConjugateTranspose @ mat, mat];
  {dmp/2, dmp}
]

theWickLyapunov[1, mat_?MatrixQ] := Module[
  { dmp },
   (* effective non-Hermitian Hamiltonian *)
  dmp = Dot[ConjugateTranspose @ mat, mat];
  {dmp/2, Zero[Dimensions @ dmp]}
]
(**** </WickLindbladSolve> ****)


(**** <WickSteadyState> ****)
WickSteadyState::usage = "WickSteadyState[ham, jmp] returns the steady-state solution (i.e., a fermionic Gaussian mixed state) to the Lindblad equation associated with the Hamiltonian ham and a set of quantum jump operators jmp.\nWickSteadyState[ham, msr] assumes that the Lindblad operators are projective and given by Wick measurement msr."

WickSteadyState::more = "The Lindblad equation has additional steady states."

(* canonicalization *)
WickSteadyState[ham_WickHermitian, jmp_WickJump, ws_WickState] :=
  WickSteadyState[ham, jmp, WickGreen @ ws]

(* dissipative case *)
WickSteadyState[ham_WickHermitian, jmp_WickJump, _] := Module[
  { xx, yy },
  {xx, yy} = WickLyapunov[First @ ham, First @ jmp];
  If[ZeroQ[Det @ xx], Message[WickSteadyState::more]];
  LyapunovSolve[xx, -yy]
] /; ContainsOnly[Values @ First @ jmp, {0, 1}]

(* projective case *)
WickSteadyState[ham_WickHermitian, jmp_WickJump, grn_?MatrixQ] := Module[
  { n = Length[First @ ham],
    lop, krn, chk, trs, evo },
  (* Lindblad operators *)
  lop = Keys[First @ jmp];
  lop = Map[KroneckerProduct[Conjugate @ #, #]&, lop];
  {krn, chk} = LindbladConvert[First @ ham, lop];
  (* \varL(I) = 0 *)
  If[ Not[ArrayZeroQ @ chk], 
    Message[WickLindbladSolve::chk, ArrayShort @ chk]
  ];
  evo = Eigenvectors[krn];
  trs = LieBasisMatrix[n];
  in = ConjugateTranspose[trs].Flatten[grn];
  out = Inverse[Transpose @ evo] . Rest[in];
  out = Last[evo] * Last[out];
  out = Prepend[out, First @ in];
  out = out . Transpose[trs];
  ArrayReshape[out, {n, n}]
] /; ContainsOnly[Values @ First @ jmp, {2, 3}]
(**** </WickSteadyState> ****)


(**** <FermionCount> ****)
FermionCount[WickState[{_?NumericQ, n_Integer}, ___]] = n

FermionCount[WickState[trs_?MatrixQ, ___]] := 
  Last[Dimensions @ trs]

FermionCount[WickHermitian[mat_?MatrixQ, ___]] := 
  Last[Dimensions @ mat]

FermionCount[WickUnitary[mat_?MatrixQ, ___]] := 
  Last[Dimensions @ mat]

FermionCount[WickUnitary[_?MatrixQ, kk:{__Integer}, ___?OptionQ]] :=
  AtLeast[Max @ kk]

FermionCount[WickNonunitary[{_?NumericQ, non_?MatrixQ}, ___]] := 
  Last[Dimensions @ non]

FermionCount[WickNonunitary[_, kk:{__Integer}, ___?OptionQ]] :=
  AtLeast[Max @ kk]

FermionCount[WickJump[jmp:{__?patternWickJumpQ}, ___]] := 
  Last[Dimensions @ Keys @ jmp]

(* NOTE: This happens when no measurement is performed such as in RandomWickCircuit. *)
FermionCount[WickMeasurement[{}, ___?OptionQ]] = 0

FermionCount[WickMeasurement[mat_?MatrixQ, ___?OptionQ]] := 
  Last[Dimensions @ mat]

FermionCount[WickCircuit[gg_List, ___?OptionQ]] := 
  Max @ ReplaceAll[FermionCount /@ Flatten[gg], AtLeast -> Identity]
(**** </FermionCount> ****)

End[] (* Fermionic quantum computation *)


(**********************************************************************)
(**** quantum information theory for fermionic Gaussian states     ****)
(**********************************************************************)

Begin["`Private`"] 

(**** <WickLogarithmicNegtivity> ****)
WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[grn, {k1, k2, \[Ellipsis]}] returns the logarithmic entanglement negativity between the subsystem consisting of fermion modes {k1, k2,\[Ellipsis]}\[Subset]{1,2,\[Ellipsis],n} in the fermionic Gaussian state characterized by n\[Times]n matrix grn of single-particle Green's function.\nWickLogarithmicNegativity[ws, {k1, k2,\[Ellipsis]}] calculates the logarithmic negativity for the Wick state (fermionic Gaussian pure state without pairing correlation) ws.\n WickLogarithmicNegativity[data, {k1,k2,\[Ellipsis]}] calculates the logarithmic negativities of elements of data, which may be an array of Green's function matices or Wick states."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

(* operator form *)
WickLogarithmicNegativity[kk:{__Integer}][any_] :=
  WickLogarithmicNegativity[any, kk]

(* special case *)
WickLogarithmicNegativity[obj_, {}, ___] = 0

(* shortcut *)
WickLogarithmicNegativity[ws_WickState, kk:{___Integer}] :=
  WickLogarithmicNegativity[WickGreen @ ws, kk]

(* normal models *)
WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}] := 0 /;
  And[MatrixQ[gnr, NumericQ], Length[grn] == Length[kk]]

(* Canonical form for normal models *)
(* SEE ALSO: Shpurian and Ryu (2019b) and  Alba and Carollo (2023) *)
WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}] := Module[
  { n = Length[grn],
    ll, gg, gp, gm, cx, id },
  ll = Supplement[Range @ n, kk];
  id = One[{n, n}];
  gg = 2*Transpose[grn] - id;
  gp = ArrayFlatten @ {
    { -gg[[kk, kk]], +I*gg[[kk, ll]] },
    { +I*gg[[ll, kk]], +gg[[ll, ll]] }
  };
  gm = ArrayFlatten @ {
    { -gg[[kk, kk]], -I*gg[[kk, ll]] },
    { -I*gg[[ll, kk]], +gg[[ll, ll]] }
  };
  cx = (id - Inverse[id + gp.gm] . (gp + gm)) / 2;
  cx = Eigenvalues[cx];
  gg = Eigenvalues[id - Transpose[grn]];
  Total[Log[2, Sqrt[cx] + Sqrt[1-cx]]] + Total[Log[2, gg^2 + (1-gg)^2]]/2
] /; MatrixQ[grn, NumericQ]

(* for an array of Wick states *)
WickLogarithmicNegativity[data_?ArrayQ, kk:{___Integer}] := 
  arrayMap[WickLogarithmicNegativity @ kk, data] /; 
  ArrayQ[data, _, MatchQ[#, _WickState]&]

(* for an array of Green's function matrices *)
WickLogarithmicNegativity[data_?ArrayQ, kk:{___Integer}] := 
  arrayMap[WickLogarithmicNegativity @ kk, data, {-2}] /; 
  And[ArrayDepth[data] > 2, ArrayQ[data, _, NumericQ]]
(**** </WickLogarithmicNegtivity> ****)


(**** <WickEntropy> ****)
WickEntropy::usage = "WickEntropy[grn] returns the von Neumann entropy of a fermionic Gaussian state characterized by the matrix grn of single-particle Green's functions. WickEntropy[NambuGreen[{grn, anm}]] or WickEntropy[{grn, anm}] considers a fermionic Gaussian state characterized by matrices grn and anm of normal and anomalous Green's functions."
(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

(* canonical form for normal models *)
WickEntropy[grn_?MatrixQ] :=
  QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn]

WickEntropy[in_WickState] :=
  WickEntropy[WickGreen @ in]
(**** </WickEntropy> ****)


(**** <WickEntanglementEntropy> ****)
WickEntanglementEntropy::usage = "WickEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} and the rest in the fermionic Gaussian state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] calculates the entanglement entropy for the Wick state (i.e., fermionic Gaussian pure state) ws."
(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

(* operator form *)
WickEntanglementEntropy[kk:{___Integer}][any_] :=
  WickEntanglementEntropy[any, kk]

(* special case *)
WickEntanglementEntropy[any_, {}] = 0

(* shortcut *)
WickEntanglementEntropy[in_WickState, kk:{___Integer}] :=
  WickEntanglementEntropy[WickGreen @ in, kk]

(* for normal models *)
WickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  WickEntropy @ grn[[kk, kk]] /; 
  MatrixQ[grn, NumericQ]

(* for an array of Wick states *)
WickEntanglementEntropy[data_, kk:{___Integer}] := 
  arrayMap[WickEntanglementEntropy @ kk, data] /; 
  ArrayQ[data, _, MatchQ[#, _WickState]&]

(* for an array of Green's function matrices *)
WickEntanglementEntropy[data_, kk:{___Integer}] := 
  arrayMap[WickEntanglementEntropy @ kk, data, {-2}] /;
  And[ArrayDepth[data] > 2, ArrayQ[data, _, NumericQ]]
(**** </WickEntanglementEntropy> ****)


(**** <WickMutualInformation> ****)
WickMutualInformation::usage = "WickMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the mutual information between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} and the rest in the fermionic Gaussian state (without pairing correlation) characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickMutualInformation[ws, {k1, k2, \[Ellipsis]}] is equivalent to WickMutualInformation[WickGreen[state], {k1, k2, \[Ellipsis]}] for Wick state ws.\nWickMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of nWickMutualInformation"
(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

(* operator form *)
WickMutualInformation[kk:{__Integer}][any_] :=
  WickMutualInformation[any, kk]

(* shortcut *)
WickMutualInformation[ws_WickState, kk:{__Integer}] :=
  WickMutualInformation[WickGreen @ ws, kk]

(* canonical form for normal models *)
WickMutualInformation[gg_?MatrixQ, kk:{__Integer}] :=With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  WickEntropy[ gg[[kk, kk]] ] + WickEntropy[ gg[[ll, ll]] ] - WickEntropy[ gg ]
] /; MatrixQ[gg, NumericQ]

(* for an array of Wick states *)
WickMutualInformation[data_, kk:{___Integer}] := 
  arrayMap[WickMutualInformation @ kk, data] /; 
  ArrayQ[data, _, MatchQ[#, _WickState]&]

(* for an array of Green's function matrices *)
WickMutualInformation[data_, kk:{___Integer}] := 
  arrayMap[WickMutualInformation @ kk, data, {-2}] /; 
  And[ArrayDepth[data] > 2, ArrayQ[data, _, NumericQ]]
(**** </WickMutualInformation> ****)

End[] (* quantum information theory for fermionic Gaussian states *)


EndPackage[]
