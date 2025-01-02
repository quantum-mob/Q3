(* Fermionic Quantum Computing *)

BeginPackage["Q3`"]

{ WickState, RandomWickState };
{ WickPureQ, WickPurity, 
  WickNullQ, WickSingleQ };
{ WickDensityMatrix };

{ WickUnitary, WickHermitian, WickCovariance,
  RandomWickUnitary, RandomWickHermitian, RandomWickCovariance };
{ WickJump, WickJumpOdds, $WickJumpOut,
  RandomWickJump };
{ WickMeasurement, WickMeasurementOdds,
  RandomWickMeasurement };
{ WickOperator, RandomWickOperator };
{ WickElements, WickCoefficients };
{ WickNonunitary, RandomWickNonunitary };

{ WickMap, WickMapOdds, $WickMapOut };

{ WickGreenFunction, WickOccupation,
  WickMean };

{ WickCircuit, RandomWickCircuit, RandomWickCircuitSimulate };
{ WickSimulate, WickDampingOperator };
{ WickMonitor };

{ WickLogarithmicNegativity, WickTimeReversalMoment };
{ WickEntropy, WickEntanglementEntropy, WickMutualInformation };

{ NambuMeasurement, NambuNonunitary, NambuJump, NambuOperator };
{ RandomNambuMeasurement };

(* VonNeumann.wl *)
{ QuantumLog };


Begin["`Private`"] (* Fermionic quantum computation *)

AddElaborationPatterns[_WickState, _WickOperator, _WickUnitary, _WickNonunitary];

(**** <WickState> ****)

WickState::usage = "WickState[uv, trs] represents a many-body quantum state for non-interacting fermion modes that has undergone the overall Bogoliubov-de Gennes (BdG) type time evolution in the Nambu space specified by reduced Nambu matrix uv and decoherence processes (including measurements) specified by matrix trs."

WickState::complex = "The covariance matrix `` must be a real anti-symmetric matrix."

WickState::cvr = "Matrix `` is not a valid covariance matrix; it must be a even-dimensional real anti-symmetric matrix."

WickState::convex = "Attemp non-convex linear superposition of Gaussian states."

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

(* canonicalization *)
WickState[cvr_WickCovariance, opts___?OptionQ] :=
  WickState[{1, cvr}, opts]

(* canonicalization *)
WickState[{fac_, cvr_WickCovariance}, rest___?OptionQ] :=
  WickState[{fac, First @ cvr}, rest]

(* canonicalization *)
WickState[{fac_, cvr_?MatrixQ}, rest___?OptionQ] :=
  WickState[{fac, SparseArray @ cvr}, rest] /;
    Head[cvr] =!= SparseArray

(* canonicalization *)
WickState[{fac_, cvr_?MatrixQ}, rest___?OptionQ] := If[
  ArrayZeroQ[Im @ cvr], 
  WickState[Re @ {fac, cvr}, rest],
  With[
    { re = Re[cvr] },
    Message[WickState::complex, ArrayShort @ cvr];
    WickState[{fac, (re - Transpose[re])/2}, rest]
  ]
] /; Not[arrayRealQ @ cvr]


(* initialization by occupation numbers *)
WickState[vv_?VectorQ, n_Integer, rest___?OptionQ] := Module[
  { ww = DiagonalMatrix @ PadRight[vv, n, vv],
    gg },
  gg = NambuGreen @ {One[n] - ww, 0};
  WickState[{1, WickCovariance @ gg}, rest]
] /; VectorQ[vv, BinaryQ]

(* initialization *)
WickState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  WickState[Lookup[aa, cc], Length @ cc]
]


WickState /:
Re[WickState[data:{_?NumericQ, _?MatrixQ}, rest___]] :=
  WickState[Re[data], rest]

WickState /:
Im[WickState[data:{_?NumericQ, _?MatrixQ}, rest___]] :=
  WickState[Im[data], rest]

WickState /:
NormSquare[WickState[{fac_?NumericQ, _?MatrixQ}, ___]] := Abs[fac]

WickState /:
Norm[WickState[{fac_?NumericQ, _?MatrixQ}, ___]] := Sqrt[Abs @ fac]


WickState /:
Normalize[WickState[{_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  WickState[{1, cvr}, rest]


(* convex linear superposition *)
WickState /:
Plus[WickState[{fa_, va_}, any___], WickState[{fb_, vb_}, other___]] :=
  WickState[{fa + fb, (fa*va + fb*vb)/(fa+fb)}, any, other]

WickState /:
Times[z_?NumericQ, WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  WickState[{z*fac, cvr}, rest] /;
    If[ RealQ[z], True,
      Message[WickState::convex, z];
      False
    ]
(* NOTE: This feature is to support convex linear superposition of two Gaussian states as mixed states. In principle, the numerical factor must be in [0, 1]. Here, any real number is allowed for convenience. *)


WickState /:
ExpressionFor[ws:WickState[{_?NumericQ, _?MatrixQ}, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ ws, cc]


WickState /:
Matrix[ws:WickState[{_?NumericQ, _?MatrixQ}, ___], ss:{___?SpeciesQ}] :=
  MatrixEmbed[Matrix @ ws, Select[ss, FermionQ], ss]

WickState /: (* null state *)
Matrix[WickState[{0, cvr_?MatrixQ}, ___]] :=
  Zero[Length @ cvr]

WickState /: (* mixed states *)
Matrix[WickState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] :=
  fac * WickDensityMatrix[WickCovariance @ cvr]
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


RandomWickState::usage = "RandomWickState[n] randomly generates a Gaussian pure state of n fermion modes."

RandomWickState[n_Integer, opts___?OptionQ] :=
  WickState[{1, RandomWickCovariance @ n}, opts]


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


(**** <WickNullQ> ****)

WickNullQ::usage = "WickNullQ[ws] returns True if Wick state ws is the null state; False, otherwise."

WickNullQ[ws_WickState] := ZeroQ[ws[[1, 1]]]

(**** </WickNullQ> ****)


(**** <WickSingleQ> ****)

WickSingleQ::usage = "WickSingleQ[cvr] returns True if Majorana covariance matrix cvr represents a fermion Gaussian state resulting from single-particle potential only (without pairing potential); False, otherwise./nWickSingleQ[bdg] tests the BdG state."

WickSingleQ[cvr_?MatrixQ] := Module[
  { aa, bb },
  aa = Transpose[ cvr[[1 ;; ;; 2]] ][[1 ;; ;; 2]];
  bb = Transpose[ cvr[[2 ;; ;; 2]] ][[2 ;; ;; 2]];
  ArrayZeroQ[aa - bb]
]

WickSingleQ[WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] :=
  WickSingleQ[cvr]

WickSingleQ[NambuGreen[{_?MatrixQ, anm_?MatrixQ}]] :=
  ArrayZeroQ[anm]

(**** </WickSingleQ> ****)


(**** <WickCovariance> ****)

WickCovariance::usage = "WickCovariance[mat] is a wrapper of the covariance matrix mat in the Majorana spinor space.\nWickCovariance[grn] converts Green's function grn, given in the NambuGreen[...] form, to equivalent covariance matrix in the Majorana spinor space."

WickCovariance /:
MakeBoxes[vv:WickCovariance[mat_?MatrixQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickCovariance, vv, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ vv },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ mat }
    },
    { BoxForm`SummaryItem @ { "Matrix: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* shortcut *)
WickCovariance /:
Normal[WickCovariance[mat_?MatrixQ, ___], rest___] := Normal[mat, rest]

(* shortcut *)
WickCovariance[ws_WickState] := WickCovariance[ ws[[1, 2]] ]

(* conversion *)
WickCovariance[grn_NambuGreen] := Module[
  { crr = 4*ToMajorana[Normal @ grn] },
  (* NOTE: Notice the factor of 4. *)
  WickCovariance @ Re[ I * (crr - One[Dimensions @ crr]) ]
]

(* conversion *)
NambuGreen[cvr_WickCovariance] := Module[
  { crr = One[2*FermionCount[cvr]] - I*First[cvr] },
  NambuGreen[ToDirac @ crr] / 4
  (* NOTE: Notice the factor of 1/4. *)
]

WickCovariance /:
Normal[WickCovariance[mm_?MatrixQ, ___], rest___] :=
  Normal[mm, rest]

WickCovariance /:
MatrixForm[WickCovariance[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickCovariance /:
ArrayShort[WickCovariance[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

WickCovariance /:
Plus[WickCovariance[a_, any___], WickCovariance[b_, other___]] :=
  WickCovariance[a + b, any, other]

WickCovariance /:
Times[z_, WickCovariance[mat_, rest___]] :=
  WickCovariance[z*mat, rest]

(**** </WickCovariance> ****)


RandomWickCovariance::usage = "RandomWickCovariance[n] randomly generates a coveriance matrix for a Gaussian pure state of 2n Majorana modes."

RandomWickCovariance[n_Integer] := Module[
  { yy, mm, in },
  yy = CircleTimes[One[n], I*ThePauli[2]];
  mm = RandomOrthogonal[2n];
  WickCovariance @ Chop[ Transpose[mm] . yy . mm ]
]


(**** <WickMean> ****)

WickMean::usage = "WickMean[data] returns the average of the Wick states or Majorana covariance matrices in array data."

WickMean[data_?ArrayQ] := Module[
  { cvr },
  cvr = Mean @ ReplaceAll[ data,
    { ws_WickState :> ws[[1, 2]],
      cv_WickCovariance :> First[cv] }
  ];
  Map[WickCovariance, cvr, {ArrayDepth[cvr] - 2}]
] /; ArrayQ[data, _, MatchQ[#, _WickState | _WickCovariance]&]

(**** <WickMean> ****)


(**** <WickConjugateReverse> ****)

WickConjugateReverse::usage = "WickConjugateReverse[mat] returns the reverse of {Conjugate[B], Conjugate[A]} for matrix mat with block structure mat = {A, B}."

WickConjugateReverse[ops_?MatrixQ] := Conjugate[Reverse @ ops]

(**** </WickConjugateReverse> ****)


(**** <WickUnitary> ****)

WickUnitary::usage = "WickUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Nambu space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively."

WickUnitary /:
MakeBoxes[op:WickUnitary[uu_?MatrixQ, rest___], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ uu }
    },
    { BoxForm`SummaryItem @ { "Transformation matrix: ", ArrayShort @ uu }
    },
    fmt,
    "Interpretable" -> Automatic
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
MatrixForm[WickUnitary[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickUnitary /:
ArrayShort[WickUnitary[mm_?MatrixQ, ___], opts___?OptionQ] :=
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
NambuUnitary /:
ToMajorana[uv:NambuUnitary[_?NambuMatrixQ, opts___?OptionQ], more___?OptionQ] := 
  WickUnitary[2*Re[ToMajorana @ Normal @ uv], more, opts]
(* NOTE: Notice the factor of 2 to keep the result to be unitary. *)

(* conversion *)
NambuUnitary /:
WickUnitary[op_NambuUnitary] := ToMajorana[op]

(* conversion *)
WickUnitary /:
ToDirac[WickUnitary[rot_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuUnitary[ToDirac[rot]/2, more, opts]

(* conversion *)
WickUnitary /:
NambuUnitary[op_WickUnitary] := ToDirac[op]

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


(**** <WickHermitian> ****)

WickHermitian::usage = "WickHermitian[m] represents a quadractic Hermitian operator (\[ImaginaryI]/4) \[CapitalSigma]ij ci mij cj in the Majorana spinor space, where m is a real anti-symmetric matrix."

WickHermitian /:
MakeBoxes[op:WickHermitian[mm_?MatrixQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickHermitian, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ mm }
    },
    { BoxForm`SummaryItem @ { "Matrix: ", ArrayShort @ mm }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickHermitian /:
Normal[WickHermitian[mat_?MatrixQ, ___], rest___] :=
  Normal[mat, rest]

(* conversion *)
NambuHermitian /:
ToMajorana[ham_NambuHermitian, opts___?OptionQ] :=
  WickHermitian[-2I*ToMajorana[Normal @ ham], opts]

(* conversion *)
NambuHermitian /:
WickHermitian[op_NambuHermitian] := ToMajorana[op]

(* conversion *)
WickHermitian /:
ToDirac[ham_WickHermitian, opts___?OptionQ] :=
  NambuHermitian[ToDirac[First @ ham]*I/2, opts]

(* conversion *)
WickHermitian /:
NambuHermitian[op_WickHermitian] := ToDirac[op]


WickHermitian /:
MatrixForm[WickHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickHermitian /:
ArrayShort[WickHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

WickHermitian /:
Dagger[op_WickHermitian] = op
  WickHermitian[Transpose @ mat, rest]

WickHermitian /:
Plus[WickHermitian[a_, any___], WickHermitian[b_, other___]] :=
  WickHermitian[a + b, any, other]

WickHermitian /:
Times[z_, WickHermitian[mm_, rest___]] :=
  WickHermitian[z * mm, rest]


WickHermitian /:
ExpressionFor[WickHermitian[mat_?MatrixQ, ___], cc:{__?MajoranaQ}] :=
  Garner[ MultiplyDot[cc, mat, cc] * (I/4) ]

WickHermitian /:
Matrix[op:WickHermitian[mat_?MatrixQ, ___]] := Module[
  { n = FermionCount[op],
    xy, mm },
  xy = theWignerJordanMajorana[n];
  mm = Transpose[xy, {3, 1, 2}] . mat . xy;
  TensorContract[mm * I/4, {{2,3}}]
]
  
(**** </WickHermitian> ****)


RandomWickHermitian[n_Integer, opts___?OptionQ] := 
  WickHermitian[Re @ RandomAntisymmetric[2n], opts]


(**** <WickElements> ****)

WickElements::usage = "WickElements[mat, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of Majorana operators {c1, c2, \[Ellipsis]} with the coefficients specified by elements of complex matrix mat.\nWickElements[mat, {a1, a2, \[Ellipsis]}] returns a list of linear combinations of the annihilation and creation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}], where the elements of complex matrix mat are the coefficients in the equivalent linear combinations of Majorana fermion operators (not the Dirac fermion operators themselves) corresponding to the Dirac fermion modes."

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


(**** <WickCoefficients> ****)

WickCoefficients::usage = "WickCoefficients[expr, {c1,c2,\[Ellipsis]}] returns a vector or matrix of coefficients in a linear combination or linear combinations of Majorana fermion operators {c1,c2,\[Ellipsis]}.\nWickCoefficients[expr, {a1,a2,\[Ellipsis]}] gets a vector of matrix of coefficients in a linear combination or linear combinations of the annihilation and creation operators of Dirac fermion modes {a1,a2,\[Ellipsis]}, and transforms it to a vector or matrix of coefficients in the equivalent linear combination(s) of the Majorana operators corresponding to the Dirac fermion modes."

WickCoefficients::nlin = "`` is not a linear combination of Dirac or Majorana fermion operators of modes ``."

WickCoefficients[spec:({__?FermionQ} | {__?MajoranaQ})][expr_] :=
  WickCoefficients[expr, spec]

WickCoefficients[expr_List, spec:({__?FermionQ} | {__?MajoranaQ})] :=
  Map[WickCoefficients[spec], expr]

WickCoefficients[expr_, cc:{__?MajoranaQ}] :=
  Coefficient[expr, cc, 1] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[WickCoefficients::nlin, expr, cc];
    False
  ]

WickCoefficients[expr_, aa:{__?FermionQ}] :=
  ToMajorana @ Coefficient[expr, Join[aa, Dagger @ aa], 1] /;
  If[ theWickLinearQ[expr, aa], True,
    Message[WickCoefficients::nlin, expr, aa];
    False
  ]


theWickLinearQ::usage = "theWickLinearQ[expr, {c1, c2, \[Ellipsis]}] returns True if expr is a linear combination of Majorana fermion operators {c1, c2, \[Ellipsis]}, and False otherwise.\ntheWickLinearQ[expr, {a1, a2, \[Ellipsis]}] returns True if expr is a linear combination of the creation and annihilation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}, and False otherwise."

theWickLinearQ[expr_List, spec_] :=
  AllTrue[expr, theWickLinearQ[#, spec]&]

theWickLinearQ[expr_, aa:{__?FermionQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[aa -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ Join[aa, Dagger @ aa], ___]
  ]
]

theWickLinearQ[expr_, cc:{__?MajoranaQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ cc, ___]
  ]
]

(**** </WickCoefficients> ****)


(**** <WickOperator> ****)

WickOperator::usage = "WickOperator[mat] represents a sequence of linear combinations of Majorana fermion operators with coefficients given by the elements of matrix mat."

WickOperator::flag = "Invalid flags ``; the flags must be binary digits."

WickOperator /:
MakeBoxes[op:WickOperator[mat_?MatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    WickOperator, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", n/2 },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* shortcut *)
WickOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  WickOperator[{spec}, n]

(* shortcut *)
WickOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, opts___?OptionQ] :=
  WickOperator[WickCoefficients[ops, cc], opts]

(* shortcut *)
WickOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  { id = One[2n],
    mm, kk, flag },
  {kk, flag} = Transpose[spec];
  kk = n*flag + kk;
  mm = NambuOperator[ id[[kk]] ];
  WickOperator[mm, opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[WickOperator::flag, flag]; False 
  ]
]


(* conversion *)
WickOperator[jmp_WickJump] := Apply[WickOperator, jmp]


(* canonicalization *)
WickOperator[mat_?MatrixQ, opts___?OptionQ] :=
  WickOperator[SparseArray @ mat, opts] /; Head[mat] =!= SparseArray
(* NOTE: In many physical cases, the linear combinations are rather simple. *)

WickOperator /:
MatrixForm[WickOperator[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickOperator /:
ArrayShort[WickOperator[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

WickOperator /:
Dagger @ WickOperator[ops_?MatrixQ, rest___] :=
  WickOperator[WickConjugateReverse @ ops, rest]


WickOperator /:
Matrix[WickOperator[mat_?MatrixQ, ___]] := 
  Apply[Dot, Identity /@ Matrix[WickJump @ mat]]
(* NOTE: Identity /@ ... to put a whole SparseArray into a list of matrices. *)

WickOperator /:
Matrix[op_WickOperator, ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ op, Select[ss, FermionQ], ss]


WickOperator /:
ExpressionFor[WickOperator[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Apply[Multiply, WickElements[mat, cc]]  
]

WickOperator /: (* fallback *)
ExpressionFor[op_WickOperator, ___] = op 


WickOperator /: 
NonCommutativeQ[_WickOperator] = True

WickOperator /:
MultiplyKind[_WickOperator] = Fermion

WickOperator /:
Multiply[pre___, opr_WickOperator, ws_WickState] := Multiply[pre, opr @ ws]

WickOperator[{}, ___][any_] = any

WickOperator[mat_?MatrixQ, ___][in:WickState[{_?NumericQ, _?MatrixQ}, ___]] :=
  Fold[#2[#1]&, in, Reverse @ Map[WickFlop, mat]]

(**** </WickOperator> ****)


(**** <WickFlop> ****)
(* NOTE: WickFlop may be integrated into WickOperator, but separating this feature keeps better the performance of WickOperator. *)

WickFlop::usage = "WickFlop[vec] represents a single linear combination of Majorana operators."

WickFlop[vec_?VectorQ, ___][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, id, mm, prb, new },
  {aa, bb, nn} = WickJumpKernel[vec];
  id = One[Dimensions @ aa];
  mm = id + aa.cvr;
  prb = nn * Sqrt[Det @ mm];
  If[ ZeroQ[prb],
    new = Zero[Dimensions @ mm], (* null state *)
    new = aa + bb.cvr.Inverse[mm].Transpose[bb]
  ];
  WickState[{fac*prb, new}, rest]
]

(**** </WickFlop> ****)


RandomWickOperator::usage = "RandomWickOperator[k_Integer, n_Integer] returns WickOperator consisting of k linear combinations of Majorana operators."

RandomWickOperator[k_Integer, n_Integer, opts___?OptionQ] :=
  WickOperator[RandomMatrix[{k, 2n}], opts]

RandomWickOperator[n_Integer] :=
  RandomWickOperator[RandomInteger[{1, n}], n]


(**** <WickJump> ****)

$WickJumpOut::usage = "$WickJumpOut returs the index of quantum jump that has occurred at the last instance of WickJump."

WickJump::usage = "WickJump[mat] represents a set of quantum jump operators, which are linear combinations of Majorana fermion operators with coefficients given by the elements of complex matrix mat."

WickJump::null = "The quantum operation returns the null state."

WickJump /:
MakeBoxes[jmp:WickJump[mat_?MatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    WickJump, jmp, None,
    { BoxForm`SummaryItem @ { "Modes: ", n/2 },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* conversion *)
WickJump[op_WickOperator] := Apply[WickJump, op]

(* canonicalization *)
WickJump[mat_?MatrixQ, opts___?OptionQ] :=
  WickJump[SparseArray @ mat, opts] /; Head[mat] =!= SparseArray
(* NOTE: In many physical cases, the linear combinations are rather simple. *)


(* shortcut *)
WickJump[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, opts___?OptionQ] :=
  WickJump @ WickOperator[ops, cc, opts]

(* shortcut *)
WickJump[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := 
  WickJump @ WickOperator[spec, n, opts]

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


WickJump /:
Matrix[jmp:WickJump[mat_?MatrixQ, ___]] := Module[
  { xy = theWignerJordanMajorana[FermionCount @ jmp] },
  Identity /@ Dot[mat, xy]
  (* NOTE: Identoity /@ ... to put the results into a list of matrices rather than a single large SparseArray. *)
]

WickJump /:
Matrix[jmp_WickJump, ss:{___?SpeciesQ}] := With[
  { mm = Matrix[jmp],
    cc = Select[ss, FermionQ] },
  Map[MatrixEmbed[#, cc, ss]&, mm]
]


WickJump /: 
NonCommutativeQ[_WickJump] = True

WickJump /:
MultiplyKind[_WickJump] = Fermion

WickJump /:
Multiply[pre___, jmp_WickJump, ws_WickState] := Multiply[pre, jmp @ ws]

WickJump[mat_?MatrixQ, ___][in_WickState] := (* null state *)
  WickState[{0, Zero[2*FermionCount[in]*{1, 1}]}, Rest @ in] /;
  WickNullQ[in]

WickJump[mat_?MatrixQ, ___][WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, mm, id, pp, new, k },
  {aa, bb, nn} = Transpose @ WickJumpKernel[mat];
  id = ConstantArray[One[Length @ cvr], Length @ mat];
  mm = id + aa.cvr;
  Quiet[pp = nn*Sqrt[Det /@ mm], Det::luc];
  pp = Ramp[Re @ pp]; (* Ramp and Re to quickly handle numerical errors. *)
  If[ ArrayZeroQ[pp],
    Message[WickJump::null];
    $WickJumpOut = Indeterminate;
    Return @ WickState[{0, Zero[Dimensions @ cvr]}, rest]
  ];

  k = RandomChoice[pp -> Range[Length @ mat]];
  $WickJumpOut = k;

  aa = aa[[k]];
  bb = bb[[k]];
  nn = nn[[k]];
  mm = mm[[k]];
  new = aa + bb . cvr . Inverse[mm] . Transpose[bb];
  WickState[{1, new}, rest]
]

(**** </WickJump> ****)


(**** <WickJumpOdds> ****)

WickJumpOdds::usage = "WickJumpOdds[mat][\[Rho]] returns the probabilities for the quantum jump processes \[Rho] \[RightTeeArrow] b[i]**\[Rho]**Dagger[b[i]], where b[i]:=Sum[mat[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of 2n bare Majorana fermion modes c[j]."

WickJumpOdds[jmp_WickJump, ___] :=
  WickJumpOdds[First @ jmp]

WickJumpOdds[mat_?MatrixQ, ___][WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] :=
  WickJumpOdds[mat][cvr]

WickJumpOdds[mat_?MatrixQ, ___][cvr_?MatrixQ] := Module[
  { aa, bb, nn, mm, id, pp },
  {aa, bb, nn} = Transpose @ WickJumpKernel[mat];
  id = One[Length @ cvr];
  mm = Map[(id + #.cvr)&, aa];
  Quiet[pp = nn*Sqrt[Det /@ mm], Det::luc];
  Normalize[Ramp @ Re @ pp, Norm[#, 1]&]
  (* NOTE: Ramp and Re to quickly handle numerical errors, and Normalize[...] instead of pp/Total[pp] to handle a rare case of zero vector. *)
]

(**** </WickJumpOdds> ****)


(**** <WickJumpKernel> ****)

WickJumpKernel::usage = "WickJumpKernel[vec] returns {A, B, nrm}, where A and B are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] b \[Rho] Dagger[b], where b := Sum[vec[[k]] c[k], {k, 2n}] is a linear combination of bare Majorana modes c[k]."

WickJumpKernel[vec_?VectorQ] := Module[
  { nn = NormSquare[vec],
    re = Re[vec],
    im = Im[vec],
    id, aa, bb },
  aa = Dyad[re, im] - Dyad[im, re];
  bb = Dyad[re, re] + Dyad[im, im];
  id = One[Dimensions @ aa];
  aa = -aa*2/nn;
  bb = id - (bb*2/nn);
  {aa, bb, nn}
]

WickJumpKernel[mat_?MatrixQ] := Map[WickJumpKernel, mat]

(**** </WickJumpKernel> ****)


RandomWickJump::usage = "RandomWickJump[k_Integer, n_Integer] returns WickJump consisting of k linear combinations of Majorana operators."

RandomWickJump[k_Integer, n_Integer, opts___?OptionQ] :=
  WickJump[RandomMatrix[{k, 2n}], opts]

RandomWickJump[n_Integer, opts___?OptionQ] :=
  RandomWickJump[RandomInteger[{1, n}], n, opts]


(**** <WickMeasurement> ****)

WickMeasurement::usage = "WickMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nWickMeasurement[{k1, k2, \[Ellipsis]}] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nWickMeasurement[mat] represents a sequence of measurement on the dressed Dirac fermion modes b[i] := Sum[m[[i,j]] c[j], {j, 2n}] expressed in terms of Majorana fermion modes c[k].\nWickMeasurement[spec][ws] simulates the measurement on Wick state ws, and returns the post-measurement state."

WickMeasurement::odd = "The second dimension of the input matrix `` is odd: ``."

WickMeasurement::dressed = "A vector of coefficients `` cannot describe a proper dressed Dirac fermion mode."

WickMeasurement /:
MakeBoxes[msr:WickMeasurement[mat_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    WickMeasurement, msr, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", n/2 },
      BoxForm`SummaryItem @ { "Dressed modes: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

Readout[WickMeasurement[op_]] := Readout[op]

WickMeasurement /:
Matrix[WickMeasurement[mat_?MatrixQ, ___], rest___] :=
  Matrix[WickJump @ mat, rest]

WickMeasurement /:
NonCommutativeQ[_WickMeasurement] = True

WickMeasurement /:
MultiplyKind[_WickMeasurement] = Fermion

WickMeasurement /:
Multiply[pre___, msr_WickMeasurement, ws_WickState] := Multiply[pre, msr @ ws]


WickMeasurement[mat_?MatrixQ, rest___] :=
  WickMeasurement[SparseArray @ mat, rest] /;
  Head[mat] =!= SparseArray

WickMeasurement /:
MatrixForm[WickMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickMeasurement /:
ArrayShort[WickMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


WickMeasurement[k_Integer][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  {aa, bb, new},
  {aa, bb} = WickMeasurementKernel[k, Length[cvr]/2];
  new = theWickMeasurement[aa, bb, cvr];
  $MeasurementOut[k] = $MeasurementOut[0];
  KeyDrop[$MeasurementOut, 0];
  WickState[{1, new}, rest]
]

WickMeasurement[kk:{___Integer}][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  Fold[#2[#1]&, in, WickMeasurement /@ kk]


(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
(* The vector vec := mat[[1]] describes a dressed Dirac fermion mode
      b := Sum[vec[[jj]] c[j], {j, 2n}]
   in terms of Majorana modes c[k]. *)
WickMeasurement[mat_?MatrixQ][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { vv = First[mat],
    aa, bb, new },
  {aa, bb} = WickMeasurementKernel[N @ vv];
  new = theWickMeasurement[aa, bb, cvr];
  $MeasurementOut[vv] = $MeasurementOut[0];
  KeyDrop[$MeasurementOut, 0];
  WickState[{1, new}, rest]
] /; Length[mat] == 1

(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
(* The matrix mat describes a list of dressed Dirac fermion modes
      b[j] := Sum[mat[[i,j]] c[j], {j, 2n}]
   in terms of Majorana fermion modes c[k]. *)
WickMeasurement[mat_?MatrixQ][in_WickState] :=
  Fold[WickMeasurement[{#2}][#1]&, in, Identity /@ mat] /;
  Length[mat] > 1
(* NOTE: Identity /@ mat is necessary because mat is usually a SparseArray. *)
(* NOTE: The dressed fermion modes associated with different rows in matrix mat do not have to be mutually orthogonal. Only required is that each row gives a proper dressed fermion mode, independently of other rows. *)


theWickMeasurement[aa_?MatrixQ, bb_?MatrixQ, cvr_?MatrixQ] := Module[
  { dd = -aa,
    id, mm, pp },
  id = One[Dimensions @ cvr];
  mm = id + dd.cvr;
  pp = Quiet[Sqrt[Det @ mm]/2, {Det::luc}];
  If[ RandomReal[] < Re[pp], (* Re[...] to quickly handle numerical errors. *)
    $MeasurementOut[0] = 1,
    $MeasurementOut[0] = 0;
    dd *= -1;
    mm = id + dd.cvr
  ];
  Quiet[-dd + bb.cvr.Inverse[mm].bb, {Inverse::luc}]
  (* NOTE: A = -D *)
]

(**** </WickMeasurement> ****)


(**** <WickMeasurementOdds> ****)

WickMeasurementOdds::usage = "WickMeasurementOdds[msr] represents the probability distribution for the occupations of the dressed modes."

WickMeasurementOdds[msr_WickMeasurement] :=
  WickMeasurementOdds[First @ msr]

WickMeasurementOdds[mat_?MatrixQ][in_WickState] :=
  WickMeasurementOdds[mat][ in[[1, 2]] ]

WickMeasurementOdds[mat_?MatrixQ][cvr_?MatrixQ] := Module[
  { mm = theWickMeasurementOdds /@ mat,
    pp },
  pp = Through[ mm[cvr] ];
  pp = AssociationThread[
    Tuples[{0, 1}, Length @ mat],
    Times @@@ Tuples[pp]  
  ];
  If[Length[mm] == 1, KeyMap[First, pp], pp]
]

theWickMeasurementOdds[vec_?VectorQ][cvr_?MatrixQ] := Module[
  { aa, bb, dd, mm, pp },
  {aa, bb} = WickMeasurementKernel[N @ vec];
  dd = -aa;
  mm = One[Dimensions @ cvr] + dd.cvr;
  pp = Quiet[Sqrt[Det @ mm]/2, {Det::luc}];
  {1- pp, pp}
]

(**** </WickMeasurementOdds> ****)


(**** <WickMeasurementKernel> ****)

WickMeasurementKernel::usage = "WickMeasurementKernel[vec] returns {A, B, nrm}, where A and B are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], -A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] Dagger[b]**b \[Rho] Dagger[b]**b, where b := Sum[vec[[k]] c[k], {k, 2n}] is a dressed Dirac fermion mode superposed of bare Majorana modes c[k]."

(* For measurement outcome = 1 *)
WickMeasurementKernel[k_Integer, n_Integer] := {
  SparseArray[
    { {2k-1, 2k} ->  1,
      {2k, 2k-1} -> -1,
      {_, _} -> 0 },
    {2n, 2n}
  ],
  SparseArray[
    { {2k-1, 2k-1} -> 0,
      {2k, 2k} -> 0,
      {i_, i_} -> 1,
      {_, _} -> 0 },
    {2n, 2n}
  ]
}

WickMeasurementKernel[kk:{___Integer}, n_Integer] := 
  Map[WickMeasurementKernel[#, n]&, kk]


(* For measurement outcome = 1 *)
WickMeasurementKernel[vec_?VectorQ] := Module[
  { n = Length[vec]/2,
    xx, yy, aa, bb, trs },
  xx = Re[N @ vec];  (* Notice N[...]; otherwise, it may take very long *)
  yy = Im[N @ vec];
  (* verify the dressed fermion mode *)
  If[ OddQ[Length @ vec] || Not @ ZeroQ[xx.yy],
    Message[WickMeasurement::dressed, First @ mat];
    Return @ {One[2n], One[2n], 0}
  ];
  (* The Cartan-Dieudonné theorem *)
  trs = HouseholderMatrix[xx];
  trs = HouseholderMatrix[trs.yy, 2] . trs;
  {aa, bb} = WickMeasurementKernel[1, n];
  {Transpose[trs].aa.trs, Transpose[trs].bb.trs}
]

WickMeasurementKernel[mat_?MatrixQ] := Map[WickMeasurementKernel, mat]

(**** </WickMeasurementKernel> ****)


RandomWickMeasurement::usage = "RandomWickMeasurement[k, n] randomly generates a WickMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomWickMeasurement[n] randomly selects k from {1,2,\[Ellipsis],n}."

RandomWickMeasurement[k_Integer, n_Integer] :=
  WickMeasurement @ RandomNambuMeasurement[k, n]

RandomWickMeasurement[n_Integer] :=
  WickMeasurement @ RandomNambuMeasurement[n]


(**** <WickMap> ****)

WickMap::usage = "WickMap[mat] or WickMap[mat, True] represents a projective quantum operation \[Rho] \[RightTeeArrow] Sum[p[i]**\[Rho]**p[i], {i, m}] + Sum[(1-p[i])**\[Rho]**(1-p[i]), {j, m}], where m is the number of rows in mat, p[i]:=Dagger[b[i]]**b[i] are projection operators, and b[i]:=Sum[mat[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of n bare Majorana fermion modes c[j].\nWickMap[mat, False] represents \[Rho] \[RightTeeArrow] Sum[p[i]**\[Rho]**p[i], {i, m}]."

WickMap::null = "The quantum operation returns the null state."

(* alias *)
WickMap[jmp_WickJump, ___] = jmp


WickMap[kk:{___Integer}] := WickMap[kk, True]

WickMap[WickMeasurement[k_Integer, ___], flag___] :=
  WickMap[{k}, flag]

WickMap[WickMeasurement[kk:{___Integer}, ___], flag___] :=
  WickMap[kk, flag]

WickMap[kk:{___Integer}, flag:(True|False)][
  WickState[{_?NumericQ, cvr_?MatrixQ}, rest___]
] := WickState[{1, WickMap[kk, flag] @ cvr}, rest]

WickMap[kk:{___Integer}, flag:(True|False)][cvr_?MatrixQ] := Module[
  {aa, bb },
  {aa, bb} = Transpose @ WickMeasurementKernel[kk, Length[cvr]/2];
  theWickMap[aa, bb, cvr, flag]
]


WickMap[mat_?MatrixQ] := WickMap[mat, True]

WickMap[WickMeasurement[mat_?MatrixQ, ___], flag___] :=
  WickMap[mat, flag]

WickMap[mat_?MatrixQ, flag:(True|False)][
  WickState[{_?NumericQ, cvr_?MatrixQ}, rest___]
] := WickState[{1, WickMap[mat, flag] @ cvr}, rest]

WickMap[mat_?MatrixQ, flag:(True|False)][cvr_?MatrixQ] := Module[
  {aa, bb },
  {aa, bb} = Transpose @ WickMeasurementKernel[mat];
  theWickMap[aa, bb, cvr, flag]
]

theWickMap[aa_?ArrayQ, bb_?ArrayQ, cvr_?MatrixQ, True] := Module[
  { m = Length[aa],
    k, an, bn, dd, mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], Length @ aa];
  dd = -aa;
  mm = id + dd.cvr;
  Quiet[pp = Sqrt[Det /@ mm]/2, Det::luc];
  pp = Ramp[Re @ pp]; (* Ramp and Re to quickly handle numerical errors. *)
  pp = Join[Ramp[1 - pp], pp];
  k = RandomChoice[pp -> Range[2m]];
  If[ k <= m,
    (* projection by a**Dagger[a] *)
    $WickMapOut = {k, 0};
    an = -aa[[k]];
    bn = bb[[k]],
    (* projection by Dagger[a]**a *)
    k -= m;
    $WickMapOut = {k, 1};
    an = aa[[k]];
    bn = bb[[k]]
  ];
  dd = -an;
  mm = One[Dimensions @ dd] + dd.cvr;
  an + bn.cvr.Inverse[mm].Transpose[bn]
]

theWickMap[aa_?ArrayQ, bb_?ArrayQ, cvr_?MatrixQ, False] := Module[
  { m = Length[aa],
    k, dd, mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], m];
  dd = -aa;
  mm = id + dd.cvr;
  Quiet[pp = Sqrt[Det /@ mm]/2, Det::luc];
  pp = Ramp[Re @ pp]; (* Ramp and Re to quickly handle numerical errors. *)
  If[ ArrayZeroQ[pp],
    Message[WickMap::null];
    $WickMapOut = Indeterminate;
    Return @ Zero[Dimensions @ cvr]
  ];
  k = RandomChoice[pp -> Range[m]];
  $WickMapOut = k;
  aa[[k]] + bb[[k]].cvr.Inverse[mm[[k]]].Transpose[bb[[k]]]
]

(**** </WickMap> ****)


(**** <WickMapOdds> ****)

WickMapOdds::usage = "WickMapOdds[mat][in] returns the probabilities for the projective process \[Rho] \[RightTeeArrow] p[i]**\[Rho]**p[i], where p[i]:=Dagger[b[i]]**b[i] and b[i]:=Sum[mat[[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of bare Majorana fermion modes c[j]."

WickMapOdds[kk:{___Integer}] := WickMapOdds[kk, True]

WickMapOdds[WickMeasurement[k_Integer, ___], flag___] :=
  WickMapOdds[{k}, flag]

WickMapOdds[WickMeasurement[kk:{___Integer}, ___], flag___] :=
  WickMapOdds[kk, flag]

WickMapOdds[kk:{___Integer}, flag:(True|False)][in_WickState] :=
  WickMapOdds[kk, flag][ in[[1, 2]] ]

WickMapOdds[kk:{___Integer}, flag:(True|False)][cvr_?MatrixQ] := Module[
  {aa, bb},
  {aa, bb} = Transpose @ WickMeasurementKernel[kk, Length[cvr]/2];
  theWickMapOdds[aa, bb, cvr, flag]
]


WickMapOdds[mat_?MatrixQ] := WickMapOdds[mat, True]

WickMapOdds[WickMeasurement[mat_?MatrixQ, ___], rest___] :=
  WickMapOdds[mat, rest]

WickMapOdds[mat_?MatrixQ, flag:(True|False)][in_WickState] :=
  WickMapOdds[mat, flag][ in[[1, 2]] ]

WickMapOdds[mat_?MatrixQ, flag:(True|False)][cvr_?MatrixQ] := Module[
  {aa, bb},
  {aa, bb} = Transpose @ WickMeasurementKernel[mat];
  theWickMapOdds[aa, bb, cvr, flag]
]


theWickMapOdds[aa_?ArrayQ, bb_?ArrayQ, cvr_?MatrixQ, flag:(True|False)] := Module[
  { dd = -aa,
    mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], Length @ aa];
  mm = id + dd.cvr;
  pp = Quiet[Sqrt[Det /@ mm]/2, Det::luc];
  pp = Ramp[Re @ pp];
  pp = If[flag, Join[Ramp[1-pp], pp], pp];
  Normalize[pp, Norm[#, 1]&]
]

(**** </WickMapOdds> ****)


(**** <WickGreenFunction> ****)

WickGreenFunction::usage = "WickGreenFunction[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to WickState ws.\nWickGreenFunction[ns, {k1, k2, \[Ellipsis]}] returns NambuGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NambuState ns.\nWickGreenFunction[in] is equivalent to WickGreenFunction[in, Range[n]], where n is the number of fermion modes for which input Wick or Nambu state in is defined for.\nWickGreenFunction[data] or WickGreenFunction[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Wick or BdG states.\nWickGreenFunction[{k1, k2, \[Ellipsis]}] represents an operator form of WickGreenFunction to be applied to Wick or Nambu state."

(* shortcut *)
WickGreenFunction[ws_WickState] :=
  WickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for BdG modelsl *)
WickGreenFunction[WickState[{_, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  {grn, anm},
  {grn, anm} = First @ NambuGreen[WickCovariance @ cvr];
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
  { grn = NambuGreen[WickCovariance @ cvr] },
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


(**** <WickPurity> ****)

WickPurity::usage = "WickPurity[ws] returns the purity of Wick state ws."

WickPurity[ws_WickState] := Module[
  { val = Eigenvalues[I*ws[[1, 2]]] },
  Power[2, -FermionCount[ws]] * Sqrt[Aggregate[1 + val^2]]
]

(**** </WickPurity> ****)


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

WickDensityMatrix[cvr_WickCovariance] :=
  WickDensityMatrix[NambuGreen @ cvr]

(* shortcut for BdG models *)
WickDensityMatrix[ws_WickState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
] /; WickPureQ[ws]

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
RandomWickCircuit[{uu_NambuUnitary, p_?NumericQ}, k_Integer] :=
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
RandomWickCircuit[{ham_NambuHermitian, spec__}, k_Integer] :=
  RandomWickCircuit[{WickHermitian @ ham, spec}, k]

(* arbitrary distribution of evolution time *)
RandomWickCircuit[{ham_WickHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      ab, tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = Map[WickUnitary[MatrixExp[hh*#]]&, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[WickMeasurement, mm];
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

(* canonicalization *)
RandomWickCircuit[ham_NambuHermitian, k_Integer] :=
  RandomWickCircuit[WickHermitian[ham], k]

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
  {_NambuUnitary, _?NumericQ},
  {_WickHermitian, _, _?NumericQ},
  {_WickHermitian, _?NumericQ},
  {_NambuHermitian, _, _?NumericQ},
  {_NambuHermitian, _?NumericQ},
  _WickHermitian,
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


theWignerJordanMajorana::usage = "theWignerJordanMajorana[n] returns a list of matrices representing 2n Majorana nodes, taking into account the Wigner-Jordan transformation."

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
  SparseArray @ Riffle[xx, yy]
]


(**** <WickNonunitary> ****)

WickNonunitary::usage = "WickNonunitary[{ham, dmp, gmm}] represents a non-unitary time evolution operator Exp[-gmm/2]*MatrixExp[-I*(ham - I*dmp)] governed by the non-Hermitian Hamiltonian ham - I*dmp. The 2n\[Times]2n antisymmetic matrices ham and dmp refer to the coefficients matrices in the bilinear combination of Majorana operators (not Dirac fermion operators).\nIf ham and dmp are given in the NambuHermitian form, they are automatically converted to the coefficients matrices of Majorana operators."

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

(* conversion *)
WickNonunitary[{ham_NambuHermitian, dmp_NambuHermitian, gmm_}, rest___] :=
  WickNonunitary[{WickHermitian @ ham, WickHermitian @ dmp, gmm}, rest]
(* CONVENTION: (1/2) (a^\dag, a) H (a, a^\dag) = (i/4) c A c. *)

(* canonicalization *)
WickNonunitary[{ham_WickHermitian, dmp_WickHermitian, gmm_}, rest___] :=
  WickNonunitary[{First @ ham, First @ dmp, gmm}, rest]

(* shortcut *)
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
  Re @ Nest[nonUnitaryStep[non, dt], in, Round[t/dt]]

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
  { WickHermitian @ Re[ -I*(mat - Transpose[mat]) ],
    Re @ Tr[mat]/2 }
]

(**** </WickDampingOperator> ****)


(**** <WickSimulate> ****)

WickSimulate::usage = "WickSimulate[in, ham, jmp, {nt, dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian ham in the WickHermitian form and the quantum jump operators are specified by jmp in the WickJump form. The simulation starts from the initial state IN in the WickState at time 0 and goes nt time steps of size dt."

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

WickSimulate[in_WickState, ham_NambuHermitian, rest__] :=
  WickSimulate[in, WickHermitian @ ham, rest]

WickSimulate[
  in_WickState, 
  ham_WickHermitian, 
  jmp_WickJump, 
  {nT_Integer, dt_}, 
  opts:OptionsPattern[]
] := Module[
  { n = OptionValue["Samples"],
    progress = 0,
    dmp, gmm, non, data, more },
    
  {dmp, gmm} = WickDampingOperator[jmp];
  non = WickNonunitary[{ham, dmp, gmm}];

  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[n];
    theWickSimulate[in, non, jmp, {nT, dt}],
    {k, n}
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

theWickSimulate[in_WickState, non_WickNonunitary, jmp_WickJump, {nT_Integer, dt_}] :=
  Module[
    { n = FermionCount[non],
      res = {in},
      new = in,
      out, prb, t },
    t = 1;
    While[ t <= nT,
      prb = RandomReal[];
      
      (* non-unitary evolution *)
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
  WickMonitor[in, WickHermition @ ham, rest] /;
  If[ EvenQ[Length @ ham] && arrayRealQ[ham] && AntisymmetricMatrixQ[ham],
    True,
    Message[WickNonitor::mat];
    False
  ]

WickMonitor[in_WickState, ham_?NambuMatrixQ, rest___] :=
  WickMonitor[in, WickHermition @ NambuHermitian @ ham, rest]

WickMonitor[
  in_WickState,
  ham_WickHermitian,
  {nT_Integer, dt_?NumericQ}, 
  opts___?OptionQ
] := WickMonitor[in, ham, 
  WickMeasurement[Range @ FermionCount @ in], 
  {nT, dt}, 
  opts
]

WickMonitor[
  in_WickState,
  ham_WickHermitian,
  msr_WickMeasurement,
  {nT_Integer, dt_?NumericQ},
  opts:OptionsPattern[]
] := Module[
  { n = OptionValue["Samples"],
    progress = 0,
    map = WickMap[msr],
    uni, data, more },
  uni = WickUnitary @ MatrixExp[N @ First[ham]*dt];

  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[n];
    theWickMonitor[in, uni, map, {nT, dt}],
    {k, n}
  ];
    
  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ WickMonitor];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
] /; If[ MatrixQ[First @ ham, NumericQ], True,
  Message[WickNonitor::num, First @ ham];
  False
]


theWickMonitor[
  in_WickState,
  uni_WickUnitary,
  map_WickMap,
  {nT_Integer, dt_?NumericQ}
] := Module[
  { n = Length[First @ map], (* the number of projective measurements *)
    t = 1,
    res = {in},
    new = in,
    nrm },
  nrm = Exp[-n*dt]; (* squared norm *)
  While[ t <= nT,      
    (* non-unitary (yet practically unitary) evolution *)
    If[ RandomReal[] < nrm,
        new = uni[new];
        AppendTo[res, new];
        t += 1;
        Continue[]
    ];
    (* quantum jumps *)
    new = map[new];
    AppendTo[res, new];
    t += 1;
  ];
    (* Echo[N[non/nT], "non"]; *)
  Return[res]
]

(**** </WickMonitor> ****)


(**** <NambuNonunitary> ****)

NambuNonunitary::usage = "NambuNonunitary[{ham, dmp, gmm}] is like WickNonunitary, but matrices ham and dmp refer to the coefficients of the Dirac fermion operators rather than the Majorana fermion operators.\nIt merely provides a shortcut tool for convenience as most calculations in fermionic quantum computing are based on Majorana operators for efficiency while sometimes the Dirac fermion representation is more intuitive."

NambuNonunitary /:
MakeBoxes[op:NambuNonunitary[{ham_NambuHermitian, dmp_NambuHermitian, gmm_?NumericQ}, rest___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NambuNonunitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ham },
      BoxForm`SummaryItem @ { "Constant: ", gmm }
    },
    { BoxForm`SummaryItem @ { "Hamiltonian: ", ArrayShort @ ham },
      BoxForm`SummaryItem @ { "Damping: ", ArrayShort @ dmp }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

NambuNonunitary /:
ToMajorana[
  NambuNonunitary[
    {ham_NambuHermitian, dmp_NambuHermitian, gmm_?NumericQ},
    opts___?OptionQ
  ],
  more___?OptionQ
] :=
  WickNonunitary[{WickHermitian @ ham, WickHermitian @ dmp, gmm}, more, opts]

NambuNonunitary /:
WickNonunitary[non_NambuNonunitary] := ToMajorana[non]

(**** </NambuNonunitary> ****)


(**** <NambuJump> ****)

NambuJump::usage = "NambuJump[mat] is like WickJump, but matrix mat refers to the coefficients of the Dirac fermion operators rather than the Majorana fermion operators.\nIt merely provides a shortcut tool for convenience as most calculations in fermionic quantum computing are based on Majorana operators for efficiency while sometimes the Dirac fermion representation is more intuitive."

NambuJump::odd = "The second dimension of the input matrix `` is odd: ``."

NambuJump /:
MakeBoxes[jmp:NambuJump[mat_?MatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    NambuJump, jmp, None,
    { BoxForm`SummaryItem @ { "Modes: ", n/2 },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* conversion *)
NambuJump /:
ToMajorana[NambuJump[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickJump[ToMajorana /@ mat, more, opts] /; (* NOT ToMajorana @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[NambuJump::odd, ArrayShort @ mat, Dimensions @ mat];
    False
  ]

(* conversion *)
NambuJump /:
WickJump[non_NambuJump] := ToMajorana[non]

NambuJump /:
Matrix[jmp_NambuJump, rest___] :=
  Matrix[ToMajorana @ jmp, rest]

(**** </NambuJump> ****)


(**** <NambuOperator> ****)

NambuOperator::usage = "NambuOperator[mat] is like WickOperator, but matrices ham and dmp refer to the coefficients of the Dirac fermion operators rather than the Majorana fermion operators.\nIt merely provides a shortcut tool for convenience as most calculations in fermionic quantum computing are based on Majorana operators for efficiency while sometimes the Dirac fermion representation is more intuitive."

NambuOperator::odd = "The second dimension of the input matrix `` is odd: ``."

NambuOperator /:
MakeBoxes[op:NambuOperator[mat_?MatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    NambuOperator, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", n/2 },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuOperator /:
ToMajorana[NambuOperator[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickOperator[ToMajorana /@ mat, more, opts] /;   (* NOT ToMajorana @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[NambuOperator::odd, ArrayShort @ mat, Dimensions @ mat];
    False
  ]

NambuOperator /:
WickOperator[non_NambuOperator] := ToMajorana[non]

NambuOperator /:
Matrix[opr_NambuOperator, rest___] :=
  Matrix[ToMajorana @ opr, rest]

(**** </NambuOperator> ****)


(**** <NambuMeasurement> ****)

NambuMeasurement::usage = "NambuMeasurement[mat] is like WickMeasurement, but matrix mat refers to the coefficients of the Dirac fermion operators rather than the Majorana fermion operators.\nIt merely provides a shortcut tool for convenience as most calculations in fermionic quantum computing are based on Majorana operators for efficiency while sometimes the Dirac fermion representation is more intuitive."

NambuMeasurement::odd = "The second dimension of the input matrix `` is odd: ``."

NambuMeasurement::dressed = "Matrix `` cannot describe a set of orthogonal dressed Dirac fermion modes."

NambuMeasurement /:
MakeBoxes[msr:NambuMeasurement[mat_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    NambuMeasurement, msr, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", n/2 },
      BoxForm`SummaryItem @ { "Dressed modes: ", m }
    },
    { BoxForm`SummaryItem @ { "Matrix: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuMeasurement /:
Matrix[msr_NambuMeasurement, rest___] :=
  Matrix[ToMajorana @ msr, rest]

(* alias *)
NambuMeasurement[kk:(_Integer | {___Integer}), rest___] :=
  WickMeasurement[kk, rest]

(* conversion *)
NambuMeasurement /:
WickMeasurement[msr_NambuMeasurement] := ToMajorana[msr]

(* conversion *)
NambuMeasurement /:
ToMajorana @ NambuMeasurement[mat_?MatrixQ, opts___?OptionQ] :=
  WickMeasurement[ToMajorana /@ mat, opts] /;   (* NOT ToMajorana @ mat. *)
  theNambuMeasurementQ[mat]

theNambuMeasurementQ::usage = "theNambuMeasurementQ[m] returns True if each linear combination \
  b[i] = Sum[m[[i, j]] a[j], {j, n}] + Sum[m[[i,n+j]] Dagger[a[j]], {j, n}] \
  of Dirac fermion operators a[j] and Dagger[a[j]] is individually a proper dressed Dirac fermion modes. Note that the different dressed fermion modes associated with different rows of m do not have to be mutually orthogonal."

theNambuMeasurementQ[mat_?MatrixQ] :=
  ArrayZeroQ[Dot @@@ Map[PartitionInto[#,2]&, mat]]

(**** </NambuMeasurement> ****)


RandomNambuMeasurement::usage = "RandomNambuMeasurement[k, n] randomly generates a NambuMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomNambuMeasurement[n] randomly selects k from {1,2,\[Ellipsis],n}."

RandomNambuMeasurement[k_Integer, n_Integer] := Module[
  { kk = RandomSelection[n, k],
    uv = RandomNambuUnitary[n] },
  uv = ArrayFlatten @ {First @ uv};
  NambuMeasurement[ uv[[kk]] ]  
]

RandomNambuMeasurement[n_Integer] :=
  RandomNambuMeasurement[RandomInteger @ {1, n}, n]


(**** <FermionCount> ****)

FermionCount::usage = "FermionCount[obj] returns the number of fermion modes involved in object obj."

FermionCount[mat_?MatrixQ] := Last[Dimensions @ mat]

FermionCount[obj_?NambuMatrixQ] := Length[First @ obj]

FermionCount[NambuUnitary[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuUnitary[uv_?NambuMatrixQ, ___]] := Length[First @ uv]

FermionCount[WickNonunitary[{ham_NambuHermitian, _NambuHermitian, _}, ___]] :=
  FermionCount[ham]

FermionCount[NambuHermitian[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuHermitian[ham_?NambuMatrixQ, ___]] := Length[First @ ham]

FermionCount[NambuGreen[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuGreen[grn_?NambuMatrixQ, ___]] := Length[First @ grn]

FermionCount[NambuJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickHermitian[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickUnitary[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickNonunitary[{ham_?MatrixQ, _?MatrixQ, _}, ___]] := Last[Dimensions @ ham]/2

FermionCount[WickJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickOperator[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] := Length[cvr]/2

FermionCount[WickCovariance[cvr_?MatrixQ, ___]] := Length[cvr]/2

FermionCount[WickMeasurement[k_Integer, ___?OptionQ]] = k

FermionCount[WickMeasurement[kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[WickMeasurement[mat_?MatrixQ, ___?OptionQ]] := Last[Dimensions @ mat]/2

FermionCount[WickMeasurement[{}, ___?OptionQ]] = 0

FermionCount[WickCircuit[gg_List, ___?OptionQ]] := Max[FermionCount /@ gg]

(**** </FermionCount> ****)

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

(* special case *)
WickLogarithmicNegativity[obj_, {}, ___] = 0

(* for large data *)
WickLogarithmicNegativity[data_?ArrayQ, kk:{___Integer}] := Module[
  { progress = i = 0,
    dim = Aggregate[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickLogarithmicNegativity[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState | _WickCovariance | _NambuGreen]&]

(* shortcut *)
WickLogarithmicNegativity[ws_WickState, rest__] :=
  WickLogarithmicNegativity[WickCovariance @ ws, rest]

(* shortcut *)
WickLogarithmicNegativity[cvr_WickCovariance, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickLogarithmicNegativity[ NambuGreen[cvr], kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]


(* normal models *)
WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___] := 0 /;
  Length[grn] == Length[kk]

(* Canonical form for normal models *)
(* SEE ALSO: Shpurian and Ryu (2019b) and  Alba and Carollo (2023) *)
WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___] := Module[
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
WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, ___] :=
  WickLogarithmicNegativity[grn, kk] /; ArrayZeroQ[anm] 

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, ___] := 0 /;
  Length[grn] == Length[kk]

(* Canonical form for BdG models *)
WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(* canonicalization *)
WickLogarithmicNegativity[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], rest__] :=
  WickLogarithmicNegativity[{gg, ff}, rest]

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


WickEntropy[cvr_WickCovariance] := Module[
  { vv = First[cvr],
    id },
  id = One[Dimensions @ vv];
  (QuantumLog[2, (id - I*vv)/2] + QuantumLog[2, (id + I*vv)/2]) / 2
]

WickEntropy[in_WickState] :=
  WickEntropy[WickCovariance @ in]

(**** </WickEntropy> ****)


(**** <WickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickEntanglementEntropy::usage = "WickEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickEntanglementEntropy[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or WickEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] is equivalent to WickEntanglementEntropy[WickGreenFunction[state, {k1, k2, \[Ellipsis]}], {k1, k2, \[Ellipsis]}] for Wick or BdG state.\nWickEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of WickEntanglementEtropy to be applied to Green's functions, Wick or Nambu state."

(* operator form *)
WickEntanglementEntropy[kk:{___Integer}][any_] :=
  WickEntanglementEntropy[any, kk]

(* special case *)
WickEntanglementEntropy[any_, {}] = 0

(* for large data *)
WickEntanglementEntropy[data_?ArrayQ, kk:{___Integer}] := Module[
  { progress = i = 0,
    dim = Aggregate[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickEntanglementEntropy[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState | _WickCovariance | _NambuGreen]&]

(* directly from covariance matrix *)
WickEntanglementEntropy[WickCovariance[cvr_?MatrixQ, ___], kk:{__Integer}] := Module[
  { jj = Riffle[2kk-1, 2kk] },
  WickEntropy[ WickCovariance @ cvr[[jj, jj]] ]
]

(* shortcut *)
WickEntanglementEntropy[in_WickState, kk:{___Integer}] :=
  WickEntanglementEntropy[WickCovariance @ in, kk]

(* for normal models *)
WickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  WickEntropy @ grn[[kk, kk]]

(* for BdG models *)
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

(**** </WickEntanglementEntropy> ****)


(**** <WickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickMutualInformation::usage = "WickMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickMutualInformation[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or WickMutualInformation[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickMutualInformation[state, {k1, k2, \[Ellipsis]}] is equivalent to WickMutualInformation[WickGreenFunction[state], {k1, k2, \[Ellipsis]}] for Wick or BdG state.\nWickMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of WickEntanglementEtropy to be applied to Green's functions, Wick or Nambu state."

(* operator form *)
WickMutualInformation[kk:{__Integer}][any_] :=
  WickMutualInformation[any, kk]

(* shortcut *)
WickMutualInformation[ws_WickState, kk:{__Integer}] :=
  WickMutualInformation[WickCovariance @ ws, kk]

(* directly from covariance matrix *)
WickMutualInformation[cvr:WickCovariance[vv_?MatrixQ, ___], kk:{__Integer}] := Module[
  { ll = Supplement[Range @ FermionCount @ cvr, kk],
    ii, jj },
  ii = Riffle[2kk-1, 2kk];
  jj = Riffle[2ll-1, 2ll];
  ( WickEntropy[ WickCovariance @ vv[[ii, ii]] ] + 
    WickEntropy[ WickCovariance @ vv[[jj, jj]] ] -
    WickEntropy[ WickCovariance @ vv ]
  ) / 2
]

(* for large data *)
WickMutualInformation[data_?ArrayQ, kk:{___Integer}] := Module[
  { progress = i = 0,
    dim = Aggregate[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickMutualInformation[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState | _WickCovariance | _NambuGreen]&]


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

(**** </WickMutualInformation> ****)

End[] (* quantum information theory for fermionic Gaussian states *)


EndPackage[]
