(* Fermionic Quantum Computing *)

BeginPackage["Q3`"]

{ WickState, RandomWickState };
{ WickCovariance, FromWickCovariance };
{ WickPureQ, WickSingleQ };
{ WickDensityMatrix };

{ WickUnitary, RandomWickUnitary };
{ WickJump, WickJumpOdds, $WickJumpOut,
  RandomWickJump };
{ WickOperator, RandomWickOperator,
  WickJumpFrom, WickOperatorFrom, WickElements };

{ WickMeasurement, WickCollapse };

{ WickNonunitary, RandomWickNonunitary };

{ WickGreenFunction, WickOccupation };

{ WickCircuit, RandomWickCircuit, RandomWickCircuitSimulate };
{ WickSimulate, WickDampingOperator };
{ WickMonitor };

{ WickLogarithmicNegativity, WickTimeReversalMoment };
{ WickEntropy, WickEntanglementEntropy, WickMutualInformation };

{ FermionCount };

(* VonNeumann.wl *)
{ QuantumLog };


Begin["`Private`"] (* Fermionic quantum computation *)

AddElaborationPatterns[_WickState, _WickOperator, _WickUnitary, _WickNonunitary];

(**** <WickState> ****)

WickState::usage = "WickState[uv, trs] represents a many-body quantum state for non-interacting fermion modes that has undergone the overall Bogoliubov-de Gennes (BdG) type time evolution in the Nambu space specified by reduced Nambu matrix uv and decoherence processes (including measurements) specified by matrix trs."

WickState::complex = "The covariance matrix `` must be a real anti-symmetric matrix."

WickState::bad = "Unsupported form of Nambu state ``."

WickState /:
MakeBoxes[ws:WickState[{fac_?NumericQ, cvr_?MatrixQ}, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ws },
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Covariance matrix: ", ArrayShort @ cvr }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; EvenQ[Length @ cvr]

(* initialization by occupation numbers *)
WickState[vv_/;VectorQ[vv, BinaryQ], n_Integer, rest___] := Module[
  { ww = DiagonalMatrix @ PadRight[vv, n, vv],
    gg, cv },
  gg = NambuGreen @ {One[n] - ww, 0};
  cv = WickCovariance[gg];
  WickState[{1, cv}, rest]
]

WickState[{fac_, cvr_?MatrixQ}, rest___] := With[
  { re = Re[cvr] },
  If[ ArrayZeroQ[Im @ cvr], 
    WickState[{fac, Re @ cvr}, rest],
    Message[WickState::complex, ArrayShort @ cvr];
    WickState[{fac, (re - Transpose[re])/2}, rest]
  ]
] /; Not[arrayRealQ @ cvr]


(* initialization *)
WickState[Rule[n_Integer, vv_/;VectorQ[vv, BinaryQ]], rest___] :=
  WickState[vv, n, rest]

(* initialization *)
WickState[Rule[cc:{__?FermionQ}, vv_/;VectorQ[vv, BinaryQ]], rest___] :=
  WickState[vv, Length @ cc, rest]

(* initialization *)
WickState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  WickState[Lookup[aa, cc], Length @ cc]
]


WickState /:
NormSquare[WickState[{fac_?NumericQ, _?MatrixQ}, ___]] := Abs[fac]

WickState /:
Norm[WickState[{fac_?NumericQ, _?MatrixQ}, ___]] := Sqrt[Abs @ fac]


WickState /:
Normalize[WickState[{_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  WickState[{1, cvr}, rest]


WickState /:
Times[z_?NumericQ, WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  WickState[{fac * AbsSquare[z], cvr}, rest]


WickState /:
ExpressionFor[ws:WickState[{_?NumericQ, _?MatrixQ}, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ ws, cc]


WickState /:
Matrix[ws:WickState[{_?NumericQ, _?MatrixQ}, ___], ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ ws, Select[ss, FermionQ], ss]

WickState /: (* mixed states *)
Matrix[WickState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] :=
  fac * WickDensityMatrix[FromWickCovariance @ cvr]
(* NOTE: It might be more efficient to use the Murnaghan's canonical form; see Paardekooper (1971) and Humeniuk and Mitrik (2018). Here, we do not try it because this function is intended for elementary tests anyway. *)

WickState /: (* pure states *)
Matrix[ws:WickState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] := Module[
  { n = FermionCount[ws],
    xy, vv, mm, pp, id },
  xy = theWignerJordanMajorana[n];

  (* NOTE: This method works only for pure states. *)
  {vv, mm, pp} = SkewTridiagonalize[cvr];
  vv = Diagonal[vv, 1][[1;; ;;2]];
  xy = Transpose[mm] . xy; (* dressed modes *)

  id = One @ Power[2, n];
  mm = Table[id + I*vv[[k]]*Dot[xy[[2k-1]], xy[[2k]]], {k, n}];
  mm = Apply[Dot, mm] / Power[2, n];
  
  {vv, mm} = Eigensystem[mm];
  pp = First @ PositionLargest[IntegerChop @ vv];
  CanonicalizeVector[ mm[[pp]] ] * Sqrt[Abs @ fac]
] /; WickPureQ[cvr]


WickState /:
NonCommutativeQ[_WickState] = True

WickState /:
MultiplyKind[_WickState] = Fermion

(**** </WickState> ****)


(**** <WickPureQ> ****)

WickPureQ::usage = "WickPureQ[cvr] returns True if Majorana covariance matrix cvr represents a prue state; False, otherwise./nWickPureQ[bdg] tests the BdG state."

WickPureQ[cvr_?MatrixQ] := Module[
  { val },
  val = First @ SkewTridiagonalize[cvr];
  val = Diagonal[val, 1][[1;; ;;2]];
  ArrayZeroQ[Abs[val] - 1]
]

WickPureQ[WickState[{_, cvr_?MatrixQ}, ___]] :=
  WickPureQ[cvr]

(**** </WickPureQ> ****)


(**** <WickSingleQ> ****)

WickSingleQ::usage = "WickSingleQ[cvr] returns True if Majorana covariance matrix cvr represents a fermion Gaussian state resulting from single-particle potential only (without pairing potential); False, otherwise./nWickSingleQ[bdg] tests the BdG state."

WickSingleQ[cvr_?MatrixQ] := Module[
  { aa, bb },
  aa = Transpose[cvr[[1 ;; ;; 2]]][[1 ;; ;; 2]];
  bb = Transpose[cvr[[2 ;; ;; 2]]][[2 ;; ;; 2]];
  ArrayZeroQ[aa - bb]
]

WickSingleQ[WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] :=
  WickSingleQ[cvr]

WickSingleQ[NambuGreen[{_?MatrixQ, anm_?MatrixQ}]] :=
  ArrayZeroQ[anm]

(**** </WickSingleQ> ****)


(**** <WickCovariance> ****)

WickCovariance::usage = "WickCovariance[grn] returns the Majorana covariance matrix corresponding to the Green's function grn, given in the NambuGreen[...] form, of Dirac fermion modes."

WickCovariance[grn_NambuGreen] := Module[
  { crr = 4*ToMajorana[Normal @ grn] },
  (* NOTE: Notice the factor of 4. *)
  Re[ I * (crr - One[Dimensions @ crr]) ]
]

(* shortcut *)
WickCovariance[ws_WickState] := ws[[1, 2]]


FromWickCovariance::usage = "FromWickCovariance[cvr] returns the Green's function of Dirac fermions corresponding to the Majorana covariance matrix cvr."

FromWickCovariance[cvr_?MatrixQ] := Module[
  { crr = One[Dimensions @ cvr] - I*cvr },
  NambuGreen[ToDirac @ crr] / 4
  (* NOTE: Notice the factor of 1/4. *)
] /; If[ arrayRealQ[cvr], True,
    Message[WickState::complex, ArrayShort @ cvr];
    False
  ]

(**** </WickCovariance> ****)


RandomWickState::usage = "RandomWickState[k, n] randomly generates a depth-k BdG state with half filling on n fermion modes\nRandomWickState[n] selects depth k randomly from {1, 2,\[Ellipsis], n}."

RandomWickState[n_Integer] := Module[
  { yy, mm, in },
  yy = CircleTimes[One[n], I*ThePauli[2]];
  mm = RandomOrthogonal[2n];
  mm = Transpose[mm] . yy . mm;
  WickState[{1, Chop @ mm}]
]

(* backward compatibility *)
RandomWickState[cc:{__?FermionQ}] :=
  RandomWickState[Length @ cc]


(**** <WickConjugateReverse> ****)

WickConjugateReverse::usage = "WickConjugateReverse[mat] returns the reverse of {Conjugate[B], Conjugate[A]} for matrix mat with block structure mat = {A, B}."

WickConjugateReverse[ops_?MatrixQ] := Conjugate[Reverse @ ops]

(**** </WickConjugateReverse> ****)


(**** <WickUnitary> ****)

WickUnitary::usage = "WickUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Nambu space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively."

WickUnitary /:
MakeBoxes[op:WickUnitary[uu_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ uu }
    },
    { BoxForm`SummaryItem @ { "Transformation matrix: ", ArrayShort @ uu }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* zero in the Nambu space *)
WickUnitary[0, n_Integer, rest___] :=
  WickUnitary[Zero @ {2n, 2n}, rest]

(* identity in the Nambu space *)
WickUnitary[1, n_Integer, rest___] :=
  WickUnitary[One[2n], rest]

WickUnitary[WickUnitary[mat_?MatrixQ, rest___], more___] :=
  WickUnitary[mat, more, rest]


WickUnitary /:
Normal[WickUnitary[mm_?MatrixQ, ___], rest___] :=
  Normal[mm, rest]

WickUnitary /:
MatrixForm[WickUnitary[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickUnitary /:
ArrayShort[WickUnitary[mm_?MatrixQ, rest___], opts__?OptionQ] :=
  ArrayShort[mm, opts]

WickUnitary /:
Dagger @ WickUnitary[mat_?MatrixQ, rest___] :=
  WickUnitary[Transpose @ mat, rest] /;
  If[ arrayRealQ[mat], True,
    Message[WickUnitary::complex, ArrayShort @ mat];
    False    
  ]

WickUnitary /:
Plus[WickUnitary[a_, any___], WickUnitary[b_, other___]] :=
  WickUnitary[a + b, any, other]

WickUnitary /:
Times[z_, WickUnitary[mm_, rest___]] :=
  WickUnitary[z * mm, rest]

WickUnitary /:
Dot[WickUnitary[a_, any___], WickUnitary[b_, other___]] :=
  WickUnitary[Dot[a, b], any, other]


WickUnitary /:
ExpressionFor[op:WickUnitary[_?MatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

WickUnitary /: (* fallback *)
ExpressionFor[op_WickUnitary, ___] = op


WickUnitary /:
Matrix[WickUnitary[mat_?MatrixQ, ___]] := Module[
  { ham = MatrixLog[mat] },
  ham = ToDirac[ham] * I/2;
  MatrixExp[-I*Matrix[NambuHermitian @ ham]]
]

WickUnitary /:
Matrix[uu:WickUnitary[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := 
  MatrixEmbed[Matrix[uu], Select[ss, FermionQ], ss]

WickUnitary /: (* fallback *)
Matrix[op_WickUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


WickUnitary /:
NonCommutativeQ[_WickUnitary] = True

WickUnitary /:
MultiplyKind[_WickUnitary] = Fermion

WickUnitary /:
Multiply[pre___, opr_WickUnitary, ws_WickState] := Multiply[pre, opr[ws]]

WickUnitary /:
Multiply[pre___, opr_WickUnitary, fs_Ket] := Multiply[pre, opr[WickState @ fs]]

WickUnitary[trs_?MatrixQ, ___][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { new = trs . cvr . Transpose[trs] },
  WickState[{fac, new}, rest]
]

(* conversion *)
WickUnitary[uv:NambuUnitary[_?NambuMatrixQ, opts___?OptionQ], more___?OptionQ] := 
  WickUnitary[Re[2 * ToMajorana @ Normal @ uv], more, opts]
(* NOTE: Notice the factor of 2 to keep the result to be unitary. *)

(* conversion *)
NambuUnitary[WickUnitary[rot_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuUnitary[ToDirac[rot] / 2, more, opts]

(**** </WickUnitary> ****)


(**** <NambuUnitary> ****)

NambuUnitary /:
Multiply[pre___, opr_NambuUnitary, fs_Ket] := Multiply[pre, opr[WickState @ fs]]

NambuUnitary /:
Multiply[pre___, opr_NambuUnitary, ws_WickState] := Multiply[pre, opr[ws]]

NambuUnitary[uv_?NambuMatrixQ, ___][in:WickState[{_?NumericQ, _?MatrixQ}, ___]] :=
  WickUnitary[uv][in]

(**** </NambuUnitary> ****)


RandomWickUnitary[n_Integer, rest___] := Module[
  { mat = RandomOrthogonal[2n] },
  mat[[1, ;;]] *= Det[mat];
  (* NOTE: Make sure to have a SU(2n) matrix. *)
  WickUnitary[mat, rest]
]


(**** <WickOperator> ****)

WickOperator::usage = "WickOperator[mat] represents a sequence of linear combinations of Majorana fermion operators with coefficients given by the elements of matrix mat."

WickOperator::flag = "Invalid flags ``; the flags must be binary digits."

WickOperator /:
MakeBoxes[op:WickOperator[mat_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest},
    m, n },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    WickOperator, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Transforms: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* canonicalization *)
WickOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  WickOperatorFrom[ops, cc, rest]


(* shortcut *)
WickOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  { id = One[2n],
    mm = ToDiracMatrix[n],
    ii, kk, flag },
  {kk, flag} = Transpose[spec];
  ii = n*flag + kk;
  mm = id[[ii]] . mm;
  WickOperator[mm, opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[WickOperator::flag, flag]; False 
  ]
]

(* shortcut *)
WickOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  WickOperator[{spec}, n]


WickOperator[{}, ___][any_] = any

WickOperator[spec__][fs_Ket] := WickOperator[spec][WickState @ fs]

WickOperator[mat_?MatrixQ, ___][in:WickState[{_?NumericQ, _?MatrixQ}, ___]] :=
  Fold[#2[#1]&, in, Reverse @ Map[WickFlop, mat]]


WickOperator /:
Dagger @ WickOperator[ops_?MatrixQ, rest___] :=
  WickOperator[WickConjugateReverse @ ops, rest]


WickOperator /: 
NonCommutativeQ[_WickOperator] = True

WickOperator /:
MultiplyKind[_WickOperator] = Fermion

WickOperator /:
Multiply[pre___, opr_WickOperator, ws_WickState] := Multiply[pre, opr @ ws]

WickOperator /:
Multiply[pre___, opr_WickOperator, fs_Ket] := Multiply[pre, opr[WickState @ fs]]


WickOperator /:
Matrix[op:WickOperator[mat_?MatrixQ, ___]] := Module[
  { c, cc },
  Let[Fermion,c];
  cc = c @ Range[FermionCount @ op];
  Matrix[op, cc]
]

WickOperator /:
Matrix[in:WickOperator[_?MatrixQ, ___]] := Module[
  { c, cc },
  Let[Fermion, c]
  cc = c @ Range[FermionCount @ in];
  Matrix[in, cc]
]

WickOperator /:
Matrix[WickOperator[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Dot @@ Matrix[WickElements[mat, cc], ss]
]

WickOperator /: (* fallback *)
Matrix[op_WickOperator, rest___] := op * Matrix[1, rest]


WickOperator /:
ExpressionFor[WickOperator[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Apply[Multiply, WickElements[mat, cc]]  
]

WickOperator /: (* fallback *)
ExpressionFor[op_WickOperator, ___] = op 


WickOperator /:
VacuumExpectation @ WickOperator[trs_?MatrixQ, ___] :=
  Pfaffian @ WickMatrix[trs]

(**** </WickOperator> ****)


(**** <WickFlop> ****)
(* NOTE: WickFlop may be integrated into WickOperator, but separating this feature keeps better the performance of WickOperator. *)

WickFlop::usage = "WickFlop[vec] represents a single linear combination of Majorana operators."

WickFlop[vec_?VectorQ, ___][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, id, mm, prb, new },
  {aa, bb, nn} = WickJumpAction[vec];
  id = One[Dimensions @ aa];
  mm = id + aa . cvr;
  prb = nn * Sqrt[Det @ mm];
  If[ ZeroQ[prb],
    new = One[Dimensions @ mm],
    new = aa + bb . cvr . Inverse[mm] . Transpose[bb]
  ];
  WickState[{fac * prb, new}, rest]
]

(**** </WickFlop> ****)


RandomWickOperator::usage = "RandomWickOperator[k_Integer, n_Integer] returns WickOperator consisting of k linear combinations of Majorana operators."

RandomWickOperator[k_Integer, n_Integer, opts___?OptionQ] :=
  WickOperator[RandomMatrix[{k, 2n}], opts]

RandomWickOperator[n_Integer] :=
  RandomWickOperator[RandomInteger[{1, n}], n]


(**** <WickJump> ****)

WickJump::usage = "WickJump[mat] represents a sequence of quantum jump operators, which are linear combinations of Majorana fermion modes with coefficients given by the elements of matrix mat."

WickJump::flag = "Invalid flags ``; the flags must be binary digits."

WickJump /:
MakeBoxes[jmp:WickJump[mat_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest},
    m, n },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    WickJump, jmp, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* canonicalization *)
WickJump[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  WickJump @@ WickOperator[ops, cc, rest]

(* shortcut *)
WickJump[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := 
  WickJump @@ WickOperator[spec, n, opts]

(* shortcut *)
WickJump[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  WickJump[{spec}, n, opts]


WickJump /:
MatrixForm[WickJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickJump /:
ArrayShort[WickJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


WickJump /:
Dagger @ WickJump[mat_?MatrixQ, rest___] :=
  WickJump[Conjugate @ mat, rest]

WickJump /:
Plus[WickJump[a_, any___], WickJump[b_, other___]] :=
  WickJump[a + b, any, other]

WickJump /:
Times[z_, WickJump[mm_, rest___]] :=
  WickJump[z * mm, rest]


WickJump[mat_?MatrixQ, ___][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, mm, id, pp, new, k },
  {aa, bb, nn} = Transpose @ WickJumpAction[mat];
  id = ConstantArray[One[Length @ cvr], Length @ mat];
  mm = id + aa . cvr;
  Quiet[pp = nn * Sqrt[Det /@ mm], Det::luc];
  pp /= Total[pp];

  k = RandomChoice[pp -> Range[Length @ mat]];
  $WickJumpOut = k;

  aa = aa[[k]];
  bb = bb[[k]];
  nn = nn[[k]];
  mm = mm[[k]];
  new = aa + bb . cvr . Inverse[mm] . Transpose[bb];
  WickState[{1, new}, rest]
]


$WickJumpOut::usage = "$WickJumpOut returs the index of quantum jump that has occurred at the last instance of WickJump."

WickJumpOdds::usage = "WickJumpOdds[{v1,v2,\[Ellipsis]}] returns the probabilities for the quantum jump processes, specified by a list {v1,v2,\[Ellipsis]} of coefficient vectors, to occur."

WickJumpOdds[mat_?MatrixQ, ___][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, mm, id, pp, new, k },
  {aa, bb, nn} = Transpose @ WickJumpAction[mat];
  id = One[Length @ cvr];
  mm = Map[(id + #.cvr)&, aa];
  pp = nn * Sqrt[Det /@ mm];
  pp / Total[pp]
]


WickJumpAction::usage = "WickJumpAction[vec] returns {a, b, nrm}, where a and b are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{a, b}, {-Transpose[b], a}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] c \[Rho] Dagger[c], where c := vec . {c1, c2, \[Ellipsis], c(2n-1), c2n} is a linear combination of Majorana modes ck."

WickJumpAction[vec_?VectorQ] := Module[
  { nn = NormSquare[vec],
    re = Re[vec],
    im = Im[vec],
    id, aa, bb },
  aa = Dyad[re, im] - Dyad[im, re];
  bb = Dyad[re, re] + Dyad[im, im];
  id = One[Dimensions @ aa];
  aa *= -2 / nn;
  bb = id - (bb * 2 / nn);
  {aa, bb, nn}
]

WickJumpAction[mat_?MatrixQ] := Map[WickJumpAction, mat]

(**** </WickJump> ****)


RandomWickJump::usage = "RandomWickJump[k_Integer, n_Integer] returns WickJump consisting of k linear combinations of Majorana operators."

RandomWickJump[k_Integer, n_Integer, opts___?OptionQ] :=
  WickJump[RandomMatrix[{k, 2n}], opts]

RandomWickJump[n_Integer, opts___?OptionQ] :=
  RandomWickJump[RandomInteger[{1, n}], n, opts]


(**** <WickElements> ****)

WickElements::usage = "WickElements[mat, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion or Majorana operators {c1, c2, \[Ellipsis]}.\nNOTE: The input matrix mat is the coefficients of Majorana modes, and when ck are fermion modes, it is automatically converted to the coefficients of the fermion modes."

WickElements[mat_?MatrixQ, cc:{__?MajoranaQ}] := mat . cc

WickElements[mat_?MatrixQ, cc:{__?FermionQ}] := Module[
  { trs = ToMajoranaMatrix[Length @ cc] },
  mat . trs . Join[cc, Dagger @ cc]
]


WickElements[WickOperator[mat_?MatrixQ, ___], cc:{__?MajoranaQ}] :=
  WickElements[mat, cc]

WickElements[WickOperator[mat_?MatrixQ, ___], cc:{__?FermionQ}] :=
  WickElements[mat, cc]

WickElements[WickJump[mat_?MatrixQ, ___], cc:{__?MajoranaQ}] :=
  WickElements[mat, cc]

WickElements[WickJump[mat_?MatrixQ, ___], cc:{__?FermionQ}] :=
  WickElements[mat, cc]

(**** </WickElements> ****)


(**** <WickOperatorFrom> ****)
(* NOTE: In principle, WickOperatorFrom may be integrated into WickOperator, but separating this feature keeps better the performance of WickOperator. *)

WickOperatorFrom::usage = "WickOperatorFrom[expr, {c1,c2,\[Ellipsis]}] constructs WickOperator from expr. If {c1,c2,\[Ellipsis]} are Dirac fermion modes, expr is a linear combination or a list of linear combinations of the creation and annihilation operators of the fermion modes. If {c1,c2,\[Ellipsis]} are Majorana fermion modes, expr is supposed to be a linear combination of Majorana fermion operators."

WickOperatorFrom[spec__] := WickOperator @@ WickJumpFrom[spec]

(**** </WickOperatorFrom> ****)


(**** <WickJumpFrom> ****)
(* NOTE: In principle, WickJumpFrom may be integrated into WickJump, but separating this feature keeps better the performance of WickJump. *)

WickJumpFrom::usage = "WickJumpFrom[expr, {c1,c2,\[Ellipsis]}] constructs WickOperator from expr, which is supposed to be a linear combination or a list of linear combinations in the creation and annihilation operators of fermion modes {c1, c2, \[Ellipsis]}."

WickJumpFrom::nlin = "`` is not a linear combination of Dirac or Majorana fermion operators of modes ``."

WickJumpFrom[expr_, cc:({__?FermionQ}|{__?MajoranaQ}), rest___] :=
  WickJump[theWickJump[expr, cc], rest] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[WickJumpFrom::nlin, expr, cc];
    False
  ]

theWickJump[expr_List, cc:{__?FermionQ}] :=
  ToMajorana /@ Map[Coefficient[#, Join[cc, Dagger @ cc]]&, expr]

theWickJump[expr_List, cc:{__?MajoranaQ}] :=
  Map[Coefficient[#, cc]&, expr]

theWickJump[expr_, spec_] :=
  theWickJump[{expr}, spec]


theWickLinearQ::usage = "theWickLinearQ[expr, {c1, c2, \[Ellipsis]}] returns True if expr is a linear combination of the creation and annihilation operators of fermion modes {c1, c2, \[Ellipsis]}, and False otherwise."

theWickLinearQ[expr_List, spec_] :=
  AllTrue[expr, theWickLinearQ[#, spec]&]

theWickLinearQ[expr_, cc:{__?FermionQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ Join[cc, Dagger @ cc], ___]
  ]
]

theWickLinearQ[expr_, cc:{__?MajoranaQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ cc, ___]
  ]
]

(**** </WickJumpFrom> ****)


(**** <WickMeasurement> ****)

WickMeasurement::usage = "FermiMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nFermiMeasurement[{k1, k2, \[Ellipsis]}] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nFermiMeasurement[spec][ws] simulates the measurement on Wick state ws, and returns the post-measurement state."


WickMeasurement::improper = "The first and second halves u and v of vector `` must be orthogonal, i.e., Dot[u, v]==0."

Readout[WickMeasurement[op_]] := Readout[op]

WickMeasurement[k_Integer][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  WickState[{1, theWickMeasurement[k, cvr]}, rest]

WickMeasurement[kk:{___Integer}][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  Fold[#2[#1]&, in, WickMeasurement /@ kk]


(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
WickMeasurement[{vv_?VectorQ}][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { n = Length[cvr] / 2,
    ww, xx, yy, trs, new },
  (* ww = vv . ToDiracMatrix[n]; *) (* the vector represents a dressed Dirac fermion modes *)
  ww = vv; (* the vector represents a dressed Majorana modes *)
  xx = Re[ww];
  yy = Im[ww];
  If[ Not @ ZeroQ[xx . yy],
    Message[WickMeasurement::improper, vv];
    Return[{1, cvr}]
  ];
  (* The Cartan-Dieudonné theorem *)
  trs = HouseholderMatrix[xx];
  trs = HouseholderMatrix[trs . yy, 2] . trs;
  new = trs . cvr . Transpose[trs];
  new = theWickMeasurement[1, new];
  $MeasurementOut[vv] = $MeasurementOut[1];
  KeyDrop[$MeasurementOut, 1];
  new = Transpose[trs] . new . trs;
  WickState[{1, new}, rest]
]

WickMeasurement[mm_?MatrixQ][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  Fold[#2[#1]&, in, WickMeasurement /@ List /@ mm] /; Length[mm] > 1

WickMeasurement[mm_?MatrixQ][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  WickMeasurement[{First @ mm}] /; Length[mm] == 1
(* NOTE: mm can be a structured array such as SparseArray. *)


theWickMeasurement[k_Integer, cvr_?MatrixQ] := Module[
  { n = Length[cvr] / 2,
    aa, bb, id, mm },
  aa = SparseArray[
    { {2k-1, 2k} ->  1,
      {2k, 2k-1} -> -1,
      {_, _} -> 0 },
    {2n, 2n}
  ]; (* for measurement outcome = 1 *)
  bb = SparseArray[
    { {2k-1, 2k-1} -> 0,
      {2k, 2k} -> 0,
      {i_, i_} -> 1,
      {_, _} -> 0 },
    {2n, 2n}
  ];
  id = One[2n];
  mm = id - aa . cvr; 
  (* NOTE: Notice the minus sign since D = -A in this case. *)
  Quiet[prb = Sqrt[Det @ mm] / 2, {Det::luc}];
  If[ RandomReal[] < Chop[prb], (* Chop to avoid a small imaginary part *)
    $MeasurementOut[k] = 1,
    $MeasurementOut[k] = 0;
    aa *= -1;
    mm = id - aa . cvr
  ];
  Quiet[aa + bb . cvr . Inverse[mm] . bb, {Inverse::luc}]
]

(**** <WickMeasurement> ****)


(**** <BdGCollampse> ****)

WickCollapse::usage = "WickCollapse[{k, m}] represents the projection to the subspace of occupation number m (0 or 1) of fermion mode k.\n WickCollapse[{vec, m}] deals with the occupation number of the dressed mode vec . {a1, a2, \[Ellipsis]}."

WickCollapse::improper = "The first and second halves u and v of vector `` must be orthogonal, i.e., Dot[u, v]==0."


WickCollapse[flag:(0|1), k_Integer][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { prb, new },
  {prb, new} = theWickCollapse[flag, k, cvr];
  WickState[{fac * prb, new}, rest]
]

WickCollapse[flag:(0|1), vec_?VectorQ][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { prb, new },
  {prb, new} = theWickCollapse[flag, vec, cvr];
  WickState[{fac * prb, new}, rest]
]


theWickCollapse[flag:(0|1), k_Integer, cvr_?MatrixQ] := Module[
  { n = Length[cvr] / 2,
    aa, bb, id, mm },
  aa = SparseArray[
    { {2k-1, 2k} ->  1,
      {2k, 2k-1} -> -1,
      {_, _} -> 0 },
    {2n, 2n}
  ] * (2*flag - 1);
  bb = SparseArray[
    { {2k-1, 2k-1} -> 0,
      {2k, 2k} -> 0,
      {i_, i_} -> 1,
      {_, _} -> 0 },
    {2n, 2n}
  ];
  id = One[2n];
  mm = id - aa . cvr; 
  (* NOTE: Notice the minus sign since D = -A in this case. *)
  prb = Sqrt[Det @ mm] / 2;
  If[ ZeroQ[prb],
    new = One[2n],
    new = aa + bb . cvr . Inverse[mm] . bb
  ];
  {prb, new}
]

(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
theWickCollapse[flag:(0|1), vv_?VectorQ, cvr_?MatrixQ] := Module[
  { n = Length[cvr] / 2,
    ww, xx, yy, trs, prb, new },
  (* ww = vv . ToDiracMatrix[n]; *) (* the vector represents a dressed Dirac fermion modes *)
  ww = vv; (* the vector represents a dressed Majorana modes *)
  xx = Re[ww];
  yy = Im[ww];
  If[ Not @ ZeroQ[xx . yy],
    Message[WickCollapse::improper, vv];
    Return[{1, cvr}]
  ];
  (* The Cartan-Dieudonné theorem *)
  trs = HouseholderMatrix[xx];
  trs = HouseholderMatrix[trs . yy, 2] . trs;
  new = trs . cvr . Transpose[trs];
  {prb, new} = theWickCollapse[flag, 1, new];
  new = Transpose[trs] . new . trs;
  {prb, new}
]

(**** </BdGCollampse> ****)


(**** <WickGreenFunction> ****)

WickGreenFunction::usage = "WickGreenFunction[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to WickState ws.\nWickGreenFunction[ns, {k1, k2, \[Ellipsis]}] returns NambuGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NambuState ns.\nWickGreenFunction[in] is equivalent to WickGreenFunction[in, Range[n]], where n is the number of fermion modes for which input Wick or Nambu state in is defined for.\nWickGreenFunction[data] or WickGreenFunction[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Wick or BdG states.\nWickGreenFunction[{k1, k2, \[Ellipsis]}] represents an operator form of WickGreenFunction to be applied to Wick or Nambu state."

(* shortcut *)
WickGreenFunction[ws_WickState] :=
  WickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for BdG modelsl *)
WickGreenFunction[WickState[{_, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  {grn, anm},
  {grn, anm} = First @ FromWickCovariance[cvr];
  NambuGreen @ {grn[[kk, kk]], anm[[kk, kk]]}
]

(* for large data *)
WickGreenFunction[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = Aggregate[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickGreenFunction[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState]&]

(**** </WickGreenFunction> ****)


(**** <WickOccupation> ****)

WickOccupation::usage = "WickOccupation[in, {k1, k2, \[Ellipsis]}] returns a list of the expectation values of occupation on fermion modes in {k1, k2, \[Ellipsis]} with respect to WickState or NambuState in.\nWickOccupation[in] is equivalent to WickOccupation[in, Range[n]], where n is the number of fermion modes for which input Wick or Nambu state in is defined for.\nWickOccupation[data] or WickOccupation[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating the occupation for an (typically large) array data of Wick or BdG states.\nWickOccupation[{k1, k2, \[Ellipsis]}] represents an operator form of WickOccupation to be applied to Wick or BdG state."

(* operator form *)
WickOccupation[kk:{___Integer}][in_] :=
  WickOccupation[in, kk]

(* shortcut *)
WickOccupation[in_WickState] :=
  WickOccupation[in, Range @ FermionCount @ in]

(* canonical form for normal models *)
WickOccupation[WickState[{_?NumericQ, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  { grn = FromWickCovariance[cvr] },
  grn = 1 - Diagonal[ grn[[1, 1]] ];
  grn[[kk]]
]


(* for large data *)
WickOccupation[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = N @ Aggregate @ Dimensions[data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickOccupation[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState]&]

(**** </WickOccupation> ****)



(**** <WickDensityMatrix> ****)

WickDensityMatrix::usage = "WickDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function grn associated with a fermionic Gaussian state.\nWickDensityMatrix[ws] returns the density matrix corresponding to Wick state ws."

WickDensityMatrix::num = "Only numerical matrices are allowed."

(* canonical form for normal models *)
WickDensityMatrix[grn_?MatrixQ] := Module[
  { n = Length[grn],
    cc, gg, uu, id },  
  (* Jordan-Wigner transformation *)
  cc = SparseArray[
    { {i_, i_} -> 4,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  cc = ThePauli /@ Normal[cc]; (* bare modes *)

  id = One @ Power[2, n];

  {gg, uu} = Eigensystem[N @ grn];
  (* NOTE: N[...] is to avoid additional normaliztaion of uu and sorting. *)
  cc = Conjugate[uu] . cc; (* dressed modes *)
  cc = MapThread[Dot, {Topple /@ cc, cc}];
  (* cc = MapThread[#1*id + (1-2*#1)*#2&, {gg, cc}]; *)
  cc = gg . id + (1-2gg) . cc;
  Dot @@ cc
] /; If[ MatrixQ[grn, NumericQ], True,
  Message[WickDensityMatrix::num];
  False
]

(* essentially normal models *)
WickDensityMatrix[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  WickDensityMatrix[grn] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
WickDensityMatrix[grn_NambuGreen] := Module[
  { n = FermionCount[grn],
    cc, gg, uu, id },  
  (* Jordan-Wigner transformation *)
  cc = SparseArray[
    { {i_, i_} -> 4,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  cc = ThePauli /@ Normal[cc]; (* bare modes *)
  cc = Join[cc, Topple /@ cc];

  id = One @ Power[2, n];

  {gg, uu} = Eigensystem[N @ Normal @ grn];
  (* NOTE: N[...] is to avoid additional normaliztaion of uu and sorting. *)
  gg = Take[gg, n]; (* gg is supposed to be sorted. *)
  cc = Take[Conjugate[uu] . cc, n]; (* dressed modes *)
  cc = MapThread[Dot, {Topple /@ cc, cc}];
  cc = MapThread[#1*id + (1-2*#1)*#2&, {gg, cc}];
  (* cc = (Take[cc, n] + Take[Reverse @ cc, n])/2; *)
  Apply[Dot, cc]
] /; If[ ArrayQ[First @ grn, 3, NumericQ], True,
  Message[WickDensityMatrix::num];
  False
]

(* canonicalization *)
WickDensityMatrix[grn_?NambuMatrixQ] := WickDensityMatrix[NambuGreen @ grn]

(* shortcut for BdG models *)
WickDensityMatrix[ws_WickState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
]

(**** </WickDensityMatrix> ****)


(**** <WickCircuit> ****)

WickCircuit::usage = "WickCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit consisting of BdG gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes."

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
    ws_WickCircuit :> Graphics[ws],
    ws_WickState :> ExpressionFor[ws, cc],
    WickUnitary[_?MatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    WickUnitary[_?MatrixQ, any___?OptionQ] :> Gate[cc, any],
    WickUnitary[_?MatrixQ, _, any___?OptionQ] :> Gate[cc, any],
    WickMeasurement[{}, ___] -> "Spacer",
    WickMeasurement[k_Integer, any___?OptionQ] :> Gate[c @ {k}, any, "Shape" -> "Measurement"],
    WickMeasurement[kk:{_Integer}, any___?OptionQ] :> Gate[c[kk], any, "Shape" -> "Measurement"],
    WickMeasurement[kk:{_, __Integer}, any___?OptionQ] :> 
      Map[Gate[{c[#]}, any, "Shape" -> "Measurement"]&, kk]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]

(**** </WickCircuit> ****)


(**** <RandomWickCircuit> ****)

RandomWickCircuit::usage = "RandomWickCircuit[{uni, p}, dep] generate a random quantum circuit on non-interacting fermion modes, where layers of unitary gate uni (either WickUnitary[\[Ellipsis]] or NambuUnitary[\[Ellipsis]]) alternate with layers of measurements (WickMeasurement[\[Ellipsis]]) on fermion modes selected randomly with probability p to form an overall depth dep.\nRandomWickCircuit[{ham, pdf, p}, k] unitary layers of random unitary gate uni=Exp[-I ham \[Tau]] with single-particle Hamiltonian ham (either n\[Times]n Hermitian matrix or NambuHermitian[\[Ellipsis]]) and the random evolution time \[Tau] distributed according to the probability distribution function pdf.\nRandomWickCircuit[{ham, p}, dep] assumes that the evolution time is uniformly distributed over the interval [0,2\[Pi] n/max], where max is the maximum of the absolute values of the entries of ham.\nRandomWickCircuit[ham, dep] generates a circuit for n fermion modes where each unitary layer corresponds to time evolution U=exp[-I ham \[Tau]] with the evolution time \[Tau] distributed by P(\[Tau])\[Proportional]exp[-n \[Tau]] and each measurement layer measures a fermion mode with probability p=1/n."

(* canonicalization *)
RandomWickCircuit[{uu_NambuUintary, p_?NumericQ}, k_Integer] :=
  RandomWickCircuit[{WickUnitary @ uu, p}, k]

(* fixed interaction time *)
RandomWickCircuit[{uu_WickUnitary, p_?NumericQ}, k_Integer] :=
  Module[
    { mm },
    mm = RandomPick[Range @ FermionCount @ uu, p, k];
    WickCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[WickMeasurement, mm]
    ]
  ]

(* canonicalization *)
(* NOTE: U := exp(-I H) *)
(* NOTE: H := \frac{i}{4} c_i ham_{ij} c_j for Majorana modes c. *)
(* NOTE: H := (1/2) Dagger[a_i] ham_{ij} a_j for Dirac fermion modes a. *)
RandomWickCircuit[{ham_NambuHermitian, spec__}, k_Integer] :=
  RandomWickCircuit[{-2I*ToMajorana[ham], spec}, k]

(* arbitrary distribution of evolution time *)
RandomWickCircuit[{ham_?MatrixQ, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = Length[ham]/2,
      ab, tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = Map[WickUnitary[MatrixExp[ham*#]]&, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[WickMeasurement, mm];
    WickCircuit @ Riffle[uu, mm]
  ]

(* uniform distribution of evolution time *)
RandomWickCircuit[{ham_?MatrixQ, p_?NumericQ}, k_Integer] :=
  Module[
    { n = Length[ham]/2,
      max, pdf },
    max = Max[Abs @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    RandomWickCircuit[{ham, pdf, p}, k]
  ]

(* canonicalization *)
RandomWickCircuit[ham_NambuHermitian, k_Integer] :=
  RandomWickCircuit[-2I*ToMajorana[ham], k]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
RandomWickCircuit[ham_?MatrixQ, k_Integer] := Module[
    { n = Length[ham]/2 },
    RandomWickCircuit[{ham, ExponentialDistribution[n], 1./n}, k]
  ]

(**** </RandomWickCircuit> ****)


(**** <RandomWickCircuitSimulate> ****)

RandomWickCircuitSimulate::usage = "RandomWickCircuitSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomWickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

RandomWickCircuitSimulate::save = "The result could not be saved."

Options[RandomWickCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RWC"
}

$RandomWickCircuitPatterns = Alternatives[
  {_WickUnitary, _?NumericQ}, 
  {_NambuUnitary, _?NumericQ},
  {_?MatrixQ, _, _?NumericQ},
  {_?MatrixQ, _?NumericQ},
  {_NambuHermitian, _, _?NumericQ},
  {_NambuHermitian, _?NumericQ},
  _?MatrixQ,
  _NambuHermitian
];

RandomWickCircuitSimulate[
  in_WickState,
  spec:$RandomWickCircuitPatterns,
  t_Integer, 
  opts:OptionsPattern[{RandomWickCircuit, RandomWickCircuitSimulate}]
] := 
Module[
  { progress = k = 0,
    data, more, qc, n, m },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];

  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    qc = RandomWickCircuit[spec, t];
    { Table[
        progress = ++k / N[n*m];
        FoldList[Construct[#2, #1]&, in, First @ qc],
        (* NOTE: No explicit normalization here because both the unitary and measurement layers produce NORMALIZED states. *)
        m 
      ],
      qc
    },
    n
  ];

  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ RandomWickCircuitSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
]

(**** </RandomWickCircuitSimulate> ****)


theWignerJordanMajorana::usage = "theWignerJordanMajorana[n] returns a list of matrices representing 2n Majorana nodes."

theWignerJordanMajorana[n_Integer] := Module[
  { xx, yy },
  (* bare odd modes *)
  xx = SparseArray[
    { {i_, i_} -> 1,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  xx = ThePauli /@ Normal[xx];
  (* bare even modes *)
  yy = SparseArray[
    { {i_, i_} -> 2,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  yy = ThePauli /@ Normal[yy];
  Riffle[xx, yy]
]


(**** <WickNonunitary> ****)

WickNonunitary::usage = "WickNonunitary[{ham, dmp}] represents a non-unitary time evolution operator MatrixExp[-I*(ham - I*dmp)] governed by the non-Hermitian Hamiltonian ham - I*dmp. The 2n\[Times]2n antisymmetic matrices ham and dmp refer to the coefficients matrices in the bilinear combination of Majorana operators (not Dirac fermion operators).\nIf ham and dmp are given in the NambuHermitian form, they are automatically converted to the coefficients matrices of Majorana operators."

WickNonunitary::icmp = "WickNonunitary for `` fermion modes cannot act on WickState for `` modes."

WickNonunitary /:
MakeBoxes[op:WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, rest___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickNonunitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op },
      BoxForm`SummaryItem @ { "Constant: ", gmm }
    },
    { BoxForm`SummaryItem @ { "Hamiltonian: ", ArrayShort @ ham },
      BoxForm`SummaryItem @ { "Damping: ", ArrayShort @ dmp }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* canonicalization *)
WickNonunitary[{ham_NambuHermitian, dmp_NambuHermitian, gmm_}, rest___] :=
  WickNonunitary[{-2I*ToMajorana[ham], -2I*ToMajorana[dmp], gmm}, rest]
(* CONVENTION: (1/2) (a^\dag, a) H (a, a^\dag) = (i/4) c A c. *)

(* canonicalization *)
WickNonunitary[{ham_, dmp_}, rest___] :=
  WickNonunitary[{ham, dmp, 0}, rest]

WickNonunitary /:
MatrixForm @ WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_}, rest___] :=
  MatrixForm /@ {ham, dmp}

WickNonunitary /:
ArrayShort @ WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_}, rest___] :=
  ArrayShort /@ {ham, dmp}

WickNonunitary /:
Dagger @ WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_}, rest___] :=
  WickNonunitary[{-ham, dmp, gmm}, rest]
(* NOTE: gmm is supposed to be real. *)

WickNonunitary /:
Matrix[op:WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, ___]] := Module[
  { n = FermionCount[op],
    non = ham - I*dmp,
    mat, wjm },
  n = FermionCount[op];
  wjm = theWignerJordanMajorana[n];
  mat = Dot[Transpose[wjm, {3, 1, 2}], non, wjm] * I/4;
  mat = TensorContract[mat, {{2, 3}}];
  mat -= I*gmm*One[Power[2, n]];
  SparseArray @ MatrixExp[-I*mat]
]

WickNonunitary /:
Matrix[op:WickNonunitary[{_?MatrixQ, _?MatrixQ, _?NumericQ}, ___], ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ op, Select[ss, FermionQ], ss]


WickNonunitary /:
NonCommutativeQ[_WickNonunitary] = True

WickNonunitary /:
MultiplyKind[_WickNonunitary] = Fermion

WickNonunitary /:
Multiply[pre___, opr_WickNonunitary, ws_WickState] := Multiply[pre, opr[ws]]

WickNonunitary /:
Multiply[pre___, opr_WickNonunitary, fs_Ket] := Multiply[pre, opr[WickState @ fs]]


WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, rest___][in_WickState] :=
  nonUnitaryEvolution[WickNonunitary @ {ham, dmp, gmm}, in, {1, 0.01}]

(* Based on the Runge-Kutta method *)
nonUnitaryEvolution[non_WickNonunitary, in_WickState, {t_?NumericQ, dt_?NumericQ}] := 
  Nest[nonUnitaryStep[non, dt], in, Round[t/dt]]

(* Single Runge-Kutta step *)
nonUnitaryStep[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, dt_?NumericQ][
  WickState[{nrm_?NumericQ, cvr_?MatrixQ}, rest___]
] := Module[
  { prb = nrm,
    new = cvr,
    aa1, aa2, aa3, aa4, bb1, bb2, bb3, bb4, trs },

  aa1 = -2*gmm*prb + Tr[dmp.new]*prb/2;
  bb1 = (ham.new - new.ham) - dmp - new.dmp.new;

  prb = nrm + aa1*dt/2;
  new = cvr + bb1*dt/2;
  aa2 = -2*gmm*prb + Tr[dmp.new]*prb/2;
  bb2 = (ham.new - new.ham) - dmp - new.dmp.new;

  prb = nrm + aa2*dt/2;
  new = cvr + bb2*dt/2;
  aa3 = -2*gmm*prb + Tr[dmp.new]*prb/2;
  bb3 = (ham.new - new.ham) - dmp - new.dmp.new;

  prb = nrm + aa3*dt;
  new = cvr + bb3*dt;
  aa4 = -2*gmm*prb + Tr[dmp.new]*prb/2;
  bb4 = (ham.new - new.ham) - dmp - new.dmp.new;

  prb = nrm + (aa1 + 2*aa2 + 2*aa3 + aa4)*dt/6;
  new = cvr + (bb1 + 2*bb2 + 2*bb3 + bb4)*dt/6;
  WickState[{prb, new}, rest]
]

(* canonicalization *)
nonUnitaryStep[non_WickNonunitary, dt_?NumericQ] :=
  nonUnitaryStep[First @ non, dt]

(**** </WickNonunitary> ****)


RandomWickNonunitary::usage = "RandomWickNonunitary[n] randomly constructs a WickNonunitary operator on n fermion modes."

RandomWickNonunitary[n_Integer, opts___?OptionQ] :=
  WickNonunitary[Re @ {RandomAntisymmetric[2n], RandomAntisymmetric[2n], 0}, opts]


(**** <FermionCount> ****)

FermionCount::usage = "FermionCount[obj] returns the number of fermion modes involved in object obj."

FermionCount[mat_?MatrixQ] := Last[Dimensions @ mat]

FermionCount[obj_?NambuMatrixQ] := Length[First @ obj]

FermionCount[NambuUnitary[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuUnitary[uv_?NambuMatrixQ, ___]] := Length[First @ uv]

FermionCount[NambuHermitian[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuHermitian[ham_?NambuMatrixQ, ___]] := Length[First @ ham]

FermionCount[NambuGreen[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuGreen[grn_?NambuMatrixQ, ___]] := Length[First @ grn]

FermionCount[WickUnitary[mat_?MatrixQ, ___]] := Last[Dimensions @ mat] / 2

FermionCount[WickNonunitary[{ham_?MatrixQ, _?MatrixQ, _}, ___]] := Last[Dimensions @ ham] / 2

FermionCount[WickJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat] / 2

FermionCount[WickOperator[mat_?MatrixQ, ___]] := Last[Dimensions @ mat] / 2

FermionCount[WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] := Length[cvr] / 2

FermionCount[WickMeasurement[k_Integer, ___?OptionQ]] = k

FermionCount[WickMeasurement[kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[WickMeasurement[{}, ___?OptionQ]] = 0

FermionCount[WickCircuit[gg_List, ___?OptionQ]] := Max[FermionCount /@ gg]

(**** </FermionCount> ****)


(**** <WickDampingOperator> ****)

WickDampingOperator::usage = "WickDampingOperator[jmp] returns a pair {mat, const} of the quadratic kernel mat and remaining constant term const of the effective damping operator in the normal ordering that corresponds to the list jmp of quantum jump operators."

WickDampingOperator::jmp = "Quantum jump operators for different number of fermion modes: ``."

WickDampingOperator[jmp_WickJump] :=
  WickDampingOperator[First @ jmp]

WickDampingOperator[jmp:{__WickJump}] :=
  WickDampingOperator @ Join[First /@ jmp] /;
    If[ Equal @@ Map[FermionCount, jmp], True,
      Message[WickDampingOperator::jmp, FermionCount /@ jmp];
      False
    ]

WickDampingOperator[jmp_?MatrixQ] := With[
  { mat = Topple[jmp].jmp },
  Re @ { -2I*(mat - Transpose[mat]), Tr[mat] } / 2
]

(**** </WickDampingOperator> ****)


(**** <WickSimulate> ****)

WickSimulate::usage = "WickSimulate[ham, jmp, in, {nt, dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian matrix ham and the list jmp of quantum jump operators. The simulation starts from the initial WickState in at time 0 and goes nt time steps by interval dt."

WickSimulate::null = "The null state is encountered."

WickSimulate::save = "The result could not be saved."

WickSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

Options[WickSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NWS"
}

WickSimulate[ham_NambuHermitian, rest__] :=
  WickSimulate[-2I*ToMajorana[ham], rest]

WickSimulate[ham_?MatrixQ, jmp_WickJump, in_WickState, {nT_Integer, dt_}, opts:OptionsPattern[]] :=
  Module[
    { n = OptionValue["Samples"],
      progress = 0,
      dmp, gmm, non, data, more },
    
    {dmp, gmm} = WickDampingOperator[jmp];
    non = WickNonunitary[{ham, dmp, gmm}];

    PrintTemporary[ProgressIndicator @ Dynamic @ progress];
    data = Table[
      progress = k / N[n];
      theWickSimulate[non, jmp, in, {nT, dt}],
      {k, n}
    ];

    If[ OptionValue["SaveData"],
      more = Join[{opts}, Options @ WickSimulate];
      SaveData[data, FilterRules[{more}, Options @ SaveData]]
    ];
    Return[data]
  ] /; If[ MatrixQ[ham, NumericQ], True,
    Message[WickSimulate::ham, ham];
    False
  ]

theWickSimulate[non_WickNonunitary, jmp_WickJump, in_WickState, {nT_Integer, dt_}] :=
  Module[
    { n = FermionCount[non],
      res = {in},
      new = in,
      out, prb, t },
    t = 1;
    While[ t <= nT,
      prb = RandomReal[];
      
      (* non-unitary evolution *)
      (* out = nonUnitaryStep[non, dt][new]; *)
      out = nonUnitaryEvolution[non, new, {dt, dt/10}];
      If[ prb < NormSquare[out],
        new = Normalize @ out;
        AppendTo[res, new];
        t += 1;
        Continue[]
      ];
      
      (* quantum jumps *)
      new = jmp[new];
      AppendTo[res, new];
      t += 1;
    ];
    Return[res]
  ]

(**** </WickSimulate> ****)


(**** <WickMonitor> ****)

WickMonitor::usage = "WickMonitor[ham, in, {nt, dt}] solves the problem of continuous monitoring of the occupation number of a non-interacting many-fermion system by using the Monte Carlo simulation method. The model is specified by the single-particle Hamiltonian ham (an n\[Times]n Hermitian matrix for models without pairing or a pair {ham, del} of matrices or NambuHermitian for BdG models). The simulation starts from the initial in (either WickState or NambState) at time 0 and goes nt time steps of size dt."

WickMonitor::save = "The result could not be saved."

WickMonitor::ham = "The Hamiltonian matrix `` needs to be numeric."

Options[WickMonitor] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "WM"
}

WickMonitor[ham_?NambuMatrixQ, rest___] :=
  WickMonitor[NambuHermitian @ ham, rest]

WickMonitor[
  ham:(_?MatrixQ|_NambuHermitian),
  in_WickState,
  {nT_Integer, dt_?NumericQ},
  opts:OptionsPattern[]
] :=
  Module[
    { n = OptionValue["Samples"],
      progress = 0,
      uni, data, more },
    uni = theWickEvolution[ham, dt];
    If[FailureQ[uni], Message[WickMonitor::ham]; Return @ $Failed];

    PrintTemporary[ProgressIndicator @ Dynamic @ progress];
    data = Table[
      progress = k / N[n];
      theWickMonitor[uni, in, {nT, dt}],
      {k, n}
    ];
    
    If[ OptionValue["SaveData"],
      more = Join[{opts}, Options @ WickMonitor];
      SaveData[data, FilterRules[{more}, Options @ SaveData]]
    ];
    Return[data]
  ]


(* NOTE: H = \frac{i}{4} c_i ham_{ij} c_j *)
theWickEvolution[ham_?MatrixQ, dt_] :=
  If[ MatrixQ[ham, NumericQ],
    WickUnitary @ MatrixExp[ham*dt],
    $Failed
  ]

theWickEvolution[ham_?NambuMatrixQ, dt_] :=
  theWickEvolution[NambuHermitian @ ham, dt]

theWickEvolution[ham_NambuHermitian, dt_] :=
  theWickEvolution[-2I*ToMajorana[Normal @ ham], dt]


theWickMonitor[uni_WickUnitary, in_WickState, {nT_Integer, dt_?NumericQ}] :=
  Module[
    { n = FermionCount[uni],
      t = 1,
      res = {in},
      new = in,
      (* non = 0, *)
      nrm, prb, occ, pos },
    (* squared norm *)
    nrm = Exp[-n*dt];
    While[ t <= nT,      
      (* non-unitary evolution *)
      If[ RandomReal[] < nrm,
        (* non++; *)
        new = uni[new];
        AppendTo[res, new];
        t += 1;
        Continue[]
      ];
      
      (* quantum jumps *)
      occ = WickOccupation[new];
      prb = Riffle[1-occ, occ] / n;
      prb = Chop[Accumulate @ prb];
      prb = prb - RandomReal[];
      pos = First @ FirstPosition[prb, _?NonNegative];
      If[ OddQ[pos],
        pos = (pos + 1)/2;
        new = WickOperator[{{pos, 0}, {pos, 1}}, n][new] / Sqrt[1-occ[[pos]]],
        pos = pos/2;
        new = WickOperator[{{pos, 1}, {pos, 0}}, n][new] / Sqrt[occ[[pos]]]
      ];
      AppendTo[res, new];
      t += 1;
    ];
    (* Echo[N[non/nT], "non"]; *)
    Return[res]
  ]

(**** </WickMonitor> ****)


End[] (* Fermionic quantum computation *)


(**********************************************************************)
(**********************************************************************)


Begin["`Private`"] (* quantum information theory for fermionic Gaussian states *)

(**** <WickTimeReversalMoment> ****)

WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

WickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[WickTimeReversalMoment] = { "Epsilon" -> 1.25*^-8 }
(* 1.0*^-8 is also a reasonable choice *)

(* canoncialization *)
WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  WickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk, opts]

(* canoncialization *)
WickTimeReversalMoment[alpha_, NambuGreen[{g_?MatrixQ, f_?MatrixQ}, ___], rest__] := 
  WickTimeReversalMoment[alpha, {g, f}, rest]

(* canoncial form *)
WickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts___?OptionQ] := 
  Quiet[theTimeReversalMoment[alpha, {grn, anm}, kk, opts], Inverse::luc]
(* 2024-08-11: Inverse::luc is silenced; the warning message does not seem to be serious in most cases, but goes off too often. *)

(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)
theTimeReversalMoment[
  alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer},
  OptionsPattern[WickTimeReversalMoment]
] := Module[
  { dd = Length[grn],
    gg, oo, id, xx, zz, uu, ww, pf1, pf2, dgn, off
  },
  oo = Zero[{dd, dd}];
  id = One[dd];
  xx = CircleTimes[ThePauli[1], id];
  zz = CircleTimes[ThePauli[3], id];

  (* \Gamma *)
  gg = id - N[grn];
  (* NOTE: N[grn] is to avoid additional normalization (or even orthonormalization) of the eigenvectors of grn. *)
  gg = Normal @ NambuHermitian[{gg, -anm}];
  gg -= OptionValue["Epsilon"] * zz;
  (* NOTE: When there is a fermion mode that is unoccuppied with certainty, the coherent-state representation becomes unusual, and one needs to handle such cases separately. While this is possible, Q3 offers a ditry trick. *)
  
  (* pf1 = Power[Pfaffian[Inverse[gg.xx]], 2]; *)
  (* pf1 = Power[-1, dd] / Det[gg]; *)
  pf1 = Quiet[Det[gg], Det::luc];

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
  (* pf2 = Pfaffian[(off - zz).xx]; *)
  pf2 = Quiet[Det[ id + ww[[dd+1;;, ;;dd]].ww[[;;dd, dd+1;;]] ], Det::luc];
  pf2 = Sqrt[pf2];
  Check[pf2 *= pf1, Message[WickTimeReversalMoment::infy, pf2*pf1]; pf2 = 0];

  (* effective \Omega of \Xi *)
  ww = Inverse[zz - off];
  ww = off + dgn . ww . dgn;
  pf2 *= Pfaffian[xx.(ww + zz)];

  (* effective \Gamma *)
  gg = Inverse[ww + zz];
  (* effective Green's function Gij *)
  gg = CircleTimes[ThePauli[10], id] - gg;

  (* Recall the particle-hole symmetry. *)
  gg = Take[Eigenvalues @ gg, dd];
  Total[Log[2, Power[gg, alpha] + Power[1-gg, alpha]]] + Log[2, Power[pf2, alpha]]
]

(**** </WickTimeReversalMoment> ****)


(**** <WickLogarithmicNegtivity> ****)

WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[grn, {k1, k2, \[Ellipsis]}] returns the logarithmic entanglement negativity between the subsystem consisting of fermion modes {k1, k2,\[Ellipsis]}\[Subset]{1,2,\[Ellipsis],n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickLogarithmicNegativity[NambuGreen[{grn, anm}], {k1, k2,\[Ellipsis]}] or WickLogarithmicNegativity[{grn, anm}, {k1, k2,\[Ellipsis]}] returns the logarithmic negativity in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickLogarithmicNegativity[state, {k1, k2, \[Ellipsis]}] is equivalent to WickLogarithmicNegativity[WickGreenFunction[state], {k1, k2,\[Ellipsis]}] for state = WickState or NambuState."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

Options[WickLogarithmicNegativity] = Options[WickTimeReversalMoment]

(* operator form *)
WickLogarithmicNegativity[kk:{__Integer}][any_] :=
  WickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[WickLogarithmicNegativity, "Epsilon"]]

(* normal models *)

WickLogarithmicNegativity[grn_?MatrixQ, kk:{}, ___?OptionQ] = 0

WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___?OptionQ] := 0 /;
  Length[grn] == Length[kk]

(* Canonical form for normal models *)
(* SEE ALSO: Shpurian and Ryu (2019b) and  Alba and Carollo (2023) *)
WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___?OptionQ] := Module[
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
  cx = (id - Inverse[id + gp.gm].(gp + gm)) / 2;
  cx = Eigenvalues[cx];
  gg = Eigenvalues[id - Transpose[grn]];
  Total[Log[2, Sqrt[cx] + Sqrt[1-cx]]] + Total[Log[2, gg^2 + (1-gg)^2]]/2
]

(* BdG models *)

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, ___?OptionQ] :=
  WickLogarithmicNegativity[grn, kk] /; ArrayZeroQ[anm] 

(* canonical form for BdG models *)
WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(* canonicalization *)
WickLogarithmicNegativity[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], rest__] :=
  WickLogarithmicNegativity[{gg, ff}, rest]

(* shortcut *)
WickLogarithmicNegativity[WickState[{_?NumericQ, cvr_?MatrixQ}, ___], kk:{__Integer}, opts:OptionsPattern[]] :=
  WickLogarithmicNegativity[
    FromWickCovariance[cvr], kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]

(**** </WickLogarithmicNegtivity> ****)

(**** <WickEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickEntropy::usage = "WickEntropy[grn] returns the von Neumann entropy of a fermionic Gaussian state characterized by the matrix grn of single-particle Green's functions. WickEntropy[NambuGreen[{grn, anm}]] or WickEntropy[{grn, anm}] considers a fermionic Gaussian state characterized by matrices grn and anm of normal and anomalous Green's functions."

(* canonical form for normal models *)
WickEntropy[grn_?MatrixQ] :=
  QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn]

(* for BdG models *)
WickEntropy[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  WickEntropy[grn] /; ArrayZeroQ[anm]

(* for BdG models *)
WickEntropy[{grn_?MatrixQ, anm_?MatrixQ}] :=
  WickEntropy[grn] /; ArrayZeroQ[anm]

(* for BdG models *)
WickEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___]] :=
  WickEntropy[Normal @ grn] / 2

(* for BdG models *)
WickEntropy[grn:{_?MatrixQ, _?MatrixQ}] :=
  WickEntropy[Normal @ NambuGreen @ grn] / 2


(* shortcut *)
WickEntropy[in_WickState] := 0 /; WickPureQ[in]

(**** </WickEntropy> ****)


(**** <WickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickEntanglementEntropy::usage = "WickEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickEntanglementEntropy[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or WickEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] is equivalent to WickEntanglementEntropy[WickGreenFunction[state, {k1, k2, \[Ellipsis]}], {k1, k2, \[Ellipsis]}] for Wick or BdG state.\nWickEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of WickEntanglementEtropy to be applied to Green's functions, Wick or Nambu state."

(* special case for normal models *)
WickEntanglementEntropy[grn_?MatrixQ, {}] = 0

(* canonical form for normal models *)
WickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  WickEntropy @ grn[[kk, kk]]

(* special case for normal models *)
WickEntanglementEntropy[_?NambuMatrixQ, {}] = 0

(* BdG models *)
WickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] :=
  WickEntanglementEntropy[grn, kk] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
WickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  WickEntropy @ Normal @ NambuGreen[{gg, ff}] / 2
]

(* canonicalization for BdG models *)
WickEntanglementEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___], kk:{__Integer}] :=
  WickEntanglementEntropy[First @ grn, kk]


(* operator form *)
WickEntanglementEntropy[kk:{___Integer}][any_] :=
  WickEntanglementEntropy[any, kk]

(* shortcut *)
WickEntanglementEntropy[in_WickState, kk:{___Integer}] :=
  WickEntanglementEntropy[WickGreenFunction[in, kk], kk]

(**** </WickEntanglementEntropy> ****)


(**** <WickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickMutualInformation::usage = "WickMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickMutualInformation[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or WickMutualInformation[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickMutualInformation[state, {k1, k2, \[Ellipsis]}] is equivalent to WickMutualInformation[WickGreenFunction[state], {k1, k2, \[Ellipsis]}] for Wick or BdG state.\nWickMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of WickEntanglementEtropy to be applied to Green's functions, Wick or Nambu state."

(* canonical form for normal models *)
WickMutualInformation[gg_?MatrixQ, kk:{__Integer}] :=With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  WickEntropy[ gg[[kk, kk]] ] + WickEntropy[ gg[[ll, ll]] ] - WickEntropy[ gg ]
]

(* BdG models *)
WickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] :=
  WickMutualInformation[gg, kk] /; ArrayZeroQ[ff]

(* canonical form for BdG models *)
WickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] := With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  ( WickEntropy[Normal @ NambuGreen @ {gg[[kk, kk]], ff[[kk, kk]]}] +
    WickEntropy[Normal @ NambuGreen @ {gg[[ll, ll]], ff[[ll, ll]]}] -
    WickEntropy[Normal @ NambuGreen @ {gg, ff}]
  ) / 2
]

(* canonicalization for BdG models *)
WickMutualInformation[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], kk:{__Integer}] :=
  WickMutualInformation[{gg, ff}, kk]

(* operator form *)
WickMutualInformation[kk:{__Integer}][any_] :=
  WickMutualInformation[any, kk]

(* shortcut for normal models *)
WickMutualInformation[in_WickState, kk:{__Integer}] := 
  WickMutualInformation[WickGreenFunction @ in, kk]

(**** </WickMutualInformation> ****)

End[] (* quantum information theory for fermionic Gaussian states *)


EndPackage[]
