(* ::Package:: *)

(* Fermionic Quantum Computing *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ WickState, RandomWickState,
  WickCovariance, WickCount };
{ WickPureQ, WickPurity, 
  WickNullQ, WickSingleQ };
{ WickTranspose };
{ WickDensityMatrix };

{ BCSState, BCSStateQ };

{ WickUnitary, WickHermitian,
  RandomWickUnitary, RandomWickHermitian, RandomWickCovariance };
{ WickJump, WickJumpOdds,RandomWickJump };
{ WickMeasurement, WickMeasurementOdds,
  RandomWickMeasurement };
{ WickOperator, RandomWickOperator };
{ WickElements, WickCoefficients };
{ WickNonunitary, RandomWickNonunitary };

{ WickMap, WickMapOdds, $WickMapOut };

{ WickGreenFunction, WickOccupation,
  WickMean, WickCanonicalize };

{ WickCircuit, RandomWickCircuit, RandomWickCircuitSimulate };
{ WickSimulate, WickDamping, $WickMinorSteps };
{ WickMonitor };

{ WickScramblingCircuit, WickScramblingSimulate };

{ WickLindbladSolve,
  WickSteadyState };

{ WickLogarithmicNegativity, WickTimeReversalMoment };
{ WickEntropy, WickEntanglementEntropy, WickMutualInformation };

(* VonNeumann.wl *)
{ QuantumLog };


Begin["`Private`"] (* Fermionic quantum computation *)

(**** <BCSState> ****)
(* See Russomanno (2023) and Zanca and Santoro (2016). *)

BCSState::usage = "BCSState[pair] represents a generalized BCS ground state characterized by the pairing matrix pair."

BCSState::noBCS = "`` is orthogonal to the vacuum state and cannot be a generalized BCS state; see the Thouless theorem."

BCSState::mixed = "A mixed state `` is encountered."

BCSState /:
MakeBoxes[bcs:BCSState[{fac_?NumericQ, pair_?MatrixQ}, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BCSState, bcs, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ bcs },
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Pairing matrix: ", ArrayShort @ pair }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

BCSState /:
FermionCount[BCSState[{ff_?NumericQ, zz_?MatrixQ}, ___]] := Length[zz]

BCSState /:
Norm[in_BCSState] := Sqrt[NormSquare @ in]

BCSState /:
NormSquare[BCSState[{ff_?NumericQ, zz_?MatrixQ}, ___]] := With[
  { mat = One[Dimensions @ zz] + zz.ConjugateTranspose[zz] },
  Re[ Abs[ff]^2 * Sqrt[Det @ mat] ]
]

BCSState /:
Normalize[BCSState[{_?NumericQ, zz_?MatrixQ}, rest___]] := With[
  { nrm = Norm[BCSState @ zz] },
  BCSState[{1/nrm, zz}, rest]
]

BCSState /:
NambuGreen[BCSState[{_?NumericQ, zz_?MatrixQ}, ___]] := Module[
  { id = One[Dimensions @ zz],
    gg },
  gg = Inverse[id + zz.ConjugateTranspose[zz]];
  NambuGreen @ {gg, -gg.zz}
]

BCSState /:
WickState[in_BCSState] := With[
  { nrm = NormSquare[in],
    grn = NambuGreen[in] },
  WickState[{nrm, WickCovariance @ grn}, Options @ in]
]

BCSState /:
ExpressionFor[in:BCSState[{_?NumericQ, _?MatrixQ}, ___], ss:{___?SpeciesQ}] :=
  ExpressionFor[Matrix[in, ss], ss]

BCSState /:
Matrix[BCSState[{ff_?NumericQ, zz_?MatrixQ}, ___]] := Module[
  { mm = ConjugateTranspose /@ theWignerJordan[Length @ zz],
    op },
  op = TensorContract[
    Transpose[mm, {3, 1, 2}] . zz . mm,
    {{2, 3}}
  ] / 2;
  SparseArray[ MatrixExp[op][[;; , 1]] ]
]

BCSState /:
Matrix[in:BCSState[{_?NumericQ, _?MatrixQ}, ___], ss:{___?SpeciesQ}] :=
  MatrixEmbed[Matrix @ in, Select[ss, FermionQ], ss]

BCSState /: (* null state *)
Matrix[BCSState[{0, zz_?MatrixQ}, ___]] :=
  Zero[Length @ zz]


(* canonicalization *)
BCSState[pair_?MatrixQ, opts___?OptionQ] := BCSState[{1, pair}, opts]

(* See also the Thouless theorem in Ring80a. *)
BCSState[ws_WickState] := Module[
  { gg, ff, ww },
  {gg, ff} = First[NambuGreen @ ws];
  ww = -Inverse[gg].ff;
  Normalize[BCSState @ ww]
] /; 
If[ WickPureQ[ws],
  If[ BCSStateQ[ws], True,
    Message[BCSState::noBCS, ws]; 
    False
  ],
  Message[BCSState::mixed, ws];
  False
]

(**** </BCSState> ****)


(**** <BCSStateQ> ****)

BCSStateQ::usage = "BCSStateQ[grn] returns True if the single-particle Green's function grn charaterizes a valid BCS state. First of all, grn must correspond to a pure Gaussian state. Second, the normal part must be non-singular."

BCSStateQ[ws_WickState] :=
  BCSStateQ[NambuGreen @ ws]

(* See also the Thouless theorem (Appendix E.3) in Ring80a. *)
BCSStateQ[grn_NambuGreen] :=
  Not[ ZeroQ @  Det @ grn[[1, 1]] ] /; WickPureQ[grn]

BCSStateQ[grn_NambuGreen] = False

(**** </BCSStateQ> ****)


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
WickState[cvr_?MatrixQ, opts___?OptionQ] :=
  WickState[{1, cvr}, opts] /; If[
    WickHermitianQ[cvr], True,
    Message[WickState::cvr, cvr]; False
  ]

(* canonicalization *)
WickState[cvr_WickCovariance, opts___?OptionQ] :=
  WickState[{1, First @ cvr}, opts]

(* canonicalization *)
WickState[grn_NambuGreen, opts___?OptionQ] :=
  WickState[{1, WickCovariance @ grn}, opts]

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
NambuGreen[WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] :=
  NambuGreen[WickCovariance @ cvr]

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
    If[ QuantumMob`Q3`RealQ[z], True,
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

(* NOTE: This was originally for cvr in the (2k-1, 2k)-encoding of Majorana modes. However, it still works for cvr in the (k, n+k)-encoding. *)
WickState /: (* pure states *)
Matrix[ws:WickState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] := Module[
  { n = FermionCount[ws],
    xy, vv, mm, pp, id },
  xy = theWignerJordanMajorana[n]; (* now both cvr and xy in the (k,n+k)-encoding *)

  (* NOTE: This method works only for pure states. *)
  {vv, mm, pp} = SkewTridiagonalize[cvr];
  vv = Diagonal[vv, 1][[1;;All;;2]];
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

WickPureQ[cvr_?MatrixQ] := ArrayZeroQ[
  One[Dimensions @ cvr] + cvr.cvr
]

WickPureQ[WickState[{_, cvr_?MatrixQ}, ___]] :=
  WickPureQ[cvr]

(**** </WickPureQ> ****)


(**** <WickNullQ> ****)

WickNullQ::usage = "WickNullQ[ws] returns True if Wick state ws is the null state; False, otherwise."

WickNullQ[ws_WickState] := ZeroQ[ws[[1, 1]]]

(**** </WickNullQ> ****)


(**** <WickSingleQ> ****)

WickSingleQ::usage = "WickSingleQ[cvr] returns True if Majorana covariance matrix cvr represents a fermion Gaussian state resulting from single-particle potential only (without pairing potential); False, otherwise.\nWickSingleQ[ws] tests the Wick state ws.\nWickState[grn] tests the Green function grn."

WickSingleQ[cvr_?MatrixQ] := Module[
  { aa, bb },
  aa = Transpose[ cvr[[1;;All;;2]] ][[1;;All;;2]];
  bb = Transpose[ cvr[[2;;All;;2]] ][[2;;All;;2]];
  ArrayZeroQ[aa - bb]
]

WickSingleQ[cvr_WickCovariance] :=
  WickSingleQ[First @ cvr]

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
  { crr = 4*ToMajorana[Normal @ grn],
    cvr },
  (* NOTE: Notice the factor of 4. *)
  cvr = I*(crr - One[Dimensions @ crr]);
  If[MatrixQ[cvr, NumericQ], cvr = Re[cvr]];
  WickCovariance[cvr]
]

(* conversion *)
NambuGreen[cvr_WickCovariance] := Module[
  { crr = One[2*FermionCount[cvr]] - I*First[cvr] },
  NambuGreen[ToDirac @ crr] / 4
  (* NOTE: Notice the factor of 1/4. *)
]

(* conversion from "correlation matrix" (see NambuGreen) *)
WickCovariance[crr_NambuHermitian] := Module[
  { n = FermionCount[crr],
    mat },
  mat = NambuHermitian[1, n]/2 - crr;
  WickCovariance @ Re[4I*ToMajorana[Normal @ mat]]
  (* NOTE: Notice the factor of 4. *)
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


(**** <WickCanonicalize> ****)

WickCanonicalize::usage = "WickCanonicalize[obj] converts object obj (such as WickJump and WickMeasurement) into a canonical form."

WickCanonicalize[WickJump[mat_?MatrixQ, rest___]] := With[
  { max = Sqrt[2]*Max[Norm /@ mat] },
  (* NOTE: Notice the factor of Sqrpt[2]. *)
  WickJump[mat/max, rest]
]

WickCanonicalize[WickMeasurement[mat_?MatrixQ, rest___]] := With[
  { max = Sqrt[2]*Max[Norm /@ mat] },
  (* NOTE: Notice the factor of Sqrpt[2]. *)
  WickMeasurement[mat/max, rest]
]

WickCanonicalize[NambuJump[mat_?MatrixQ, rest___]] := With[
  { max = Max[Norm /@ mat] },
  NambuJump[mat/max, rest]
]

WickCanonicalize[NambuMeasurement[mat_?MatrixQ, rest___]] := With[
  { max = Max[Norm /@ mat] },
  NambuMeasurement[mat/max, rest]
]

(**** </WickCanonicalize> ****)


(**** <WickTranspose> ****)

WickTranspose::usage = "WickTranspose[cvr] returns the Majorana covariance matrix of the partial transpose of the Gaussian state specified by the Majorana covariance matrix cvr.\nNote that the resulting covariance matrix is not real any longer (though still anti-symmetric), implying that the corresponding Gaussian operator is not Hermitian any longer."
(* SEE ALSO: Bravyi (2005) and Shapourian and Ryu (2017, 2019) *)

WickTranspose[WickState[{fac_, cvr_}, rest___], kk:{___Integer}] :=
  WickState[{fac, WickTranspose[cvr, kk]}, rest]

WickTranspose[cvr_WickCovariance, kk:{___Integer}] :=
  WickCovariance[WickTranspose[Normal @ cvr, kk], Options @ cvr]

WickTranspose[cvr_?MatrixQ, kk:{___Integer}] := Module[
  { n = Length[cvr]/2,
    mat },
  mat = ReplacePart[ConstantArray[1, n], Thread[kk -> I]];
  mat = SparseArray @ DiagonalMatrix @ Join[mat, mat];
  mat . cvr. mat
]

(**** </WickTranspose> ****)


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

WickConjugateReverse::usage = "WickConjugateReverse[mat] is equivalent to Conjugate[Reverse @ mat].\nIt is useful to handle the Hermitian conjugate of WickOperator, WickJump, and WickMeasurement."

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
WickUnitary[uv:NambuUnitary[_?NambuMatrixQ, opts___?OptionQ], more___?OptionQ] := 
  WickUnitary[2*Re[ToMajorana @ Normal @ uv], more, opts]
(* NOTE: Notice the factor of 2 to keep the result to be unitary. *)

(* conversion *)
NambuUnitary /:
ToMajorana[op_NambuUnitary] := WickUnitary[op]

(* conversion *)
WickUnitary /:
NambuUnitary[WickUnitary[rot_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuUnitary[ToDirac[rot]/2, more, opts]

(* conversion *)
WickUnitary /:
ToDirac[op_WickUnitary] := NambuUnitary[op]

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
WickHermitian[ham:NambuHermitian[_?NambuMatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickHermitian[-2I*ToMajorana[Normal @ ham], more, opts]

(* conversion *)
NambuHermitian /:
ToMajorana[op_NambuHermitian] := WickHermitian[op]

(* conversion *)
WickHermitian /:
NambuHermitian[WickHermitian[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuHermitian[ToDirac[mat]*I/2, more, opts]

(* conversion *)
WickHermitian /:
ToDirac[op_WickHermitian] := NambuHermitian[op]


WickHermitian /:
MatrixForm[WickHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickHermitian /:
ArrayShort[WickHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

WickHermitian /:
Dagger[op_WickHermitian] = op

WickHermitian /:
Plus[WickHermitian[a_, any___], WickHermitian[b_, other___]] :=
  WickHermitian[a + b, any, other]

WickHermitian /:
Times[z_, WickHermitian[mm_, rest___]] :=
  WickHermitian[z * mm, rest]


WickHermitian /:
ExpressionFor[op:WickHermitian[_?MatrixQ, ___], aa:{__?FermionQ}] := Module[
  { mat = Normal[NambuHermitian @ op],
    aaa = Join[aa, Dagger @ aa] },
  Garner[ MultiplyDot[Dagger @ aaa, mat.aaa] / 2 ]
]

WickHermitian /:
ExpressionFor[WickHermitian[mat_?MatrixQ, ___], cc:{__?MajoranaQ}] :=
  Garner[ MultiplyDot[cc, mat, cc] * (I/4) ]

WickHermitian /:
Matrix[op:WickHermitian[mat_?MatrixQ, ___]] := Module[
  { n = FermionCount[op],
    xy, mm },
  xy = theWignerJordanMajorana[n];
  mm = Transpose[xy, {3, 1, 2}] . mat . xy;
  TensorContract[mm * I/4, {{2, 3}}]
]


WickHermitianQ::usage = "WickHermitianQ[mat] returns True if matrix mat is an even-dimensional real anti-symmetric matrix, which can represent a Hermitian operator quadratic in Majorana fermion operators."

WickHermitianQ[mat_?SquareMatrixQ] := And[
  EvenQ[Length @ mat],
  arrayRealQ[mat],
  AntisymmetricMatrixQ[mat]
]

WickHermitianQ[_] = False

(**** </WickHermitian> ****)


RandomWickHermitian[n_Integer, opts___?OptionQ] := 
  WickHermitian[Re @ RandomAntisymmetric[2n], opts]


(**** <WickElements> ****)

WickElements::usage = "WickElements[mat, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of Majorana operators {c1, c2, \[Ellipsis]} with the coefficients specified by elements of complex matrix mat.\nWickElements[mat, {a1, a2, \[Ellipsis]}] returns a list of linear combinations of the annihilation and creation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}, where the elements of complex matrix mat are the coefficients in the equivalent linear combinations of Majorana fermion operators (not the Dirac fermion operators themselves) corresponding to the Dirac fermion modes."

WickElements[mat_?MatrixQ, cc:{__?MajoranaQ}] :=
  Dot[mat, cc]

WickElements[mat_?MatrixQ, aa:{__?FermionQ}] := 
  Dot[ToDirac /@ mat, Join[aa, Dagger @ aa]]

WickElements[
  (WickOperator|WickJump|WickMeasurement)[mat_?MatrixQ, ___],
  spec:({__?MajoranaQ} | {__?FermionQ} )
] := WickElements[mat, spec]

(**** </WickElements> ****)


(**** <WickCoefficients> ****)

WickCoefficients::usage = "WickCoefficients[expr, {c1,c2,\[Ellipsis]}] returns a vector or matrix of coefficients in a linear combination or linear combinations of Majorana fermion operators {c1,c2,\[Ellipsis]}.\nWickCoefficients[expr, {a1,a2,\[Ellipsis]}] gets a vector or matrix of coefficients in a linear combination or linear combinations of the annihilation and creation operators of Dirac fermion modes {a1,a2,\[Ellipsis]}, and transforms it to a vector or matrix of coefficients in the equivalent linear combination(s) of the Majorana operators corresponding to the Dirac fermion modes."

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
  {aa, bb, nn} = WickFlopKernel[vec];
  id = One[Dimensions @ aa];
  mm = id + aa . cvr;
  prb = nn * Sqrt[Det @ mm];
  If[ ZeroQ[prb],
    new = Zero[Dimensions @ mm], (* null state *)
    new = aa + bb . cvr . Inverse[mm] . Transpose[bb]
  ];
  WickState[{fac*prb, new}, rest]
]

WickFlopKernel::usage = "WickFlopKernel[vec] returns {A, B, nrm}, where A and B are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] b \[Rho] Dagger[b], where b := Sum[vec[[k]] c[k], {k, 2n}] is a linear combination of bare Majorana modes c[k]."

WickFlopKernel[vec_?VectorQ] := Module[
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

(**** </WickFlop> ****)


RandomWickOperator::usage = "RandomWickOperator[k_Integer, n_Integer] returns WickOperator consisting of k linear combinations of Majorana operators."

RandomWickOperator[k_Integer, n_Integer, opts___?OptionQ] :=
  WickOperator[RandomMatrix[{k, 2n}], opts]

RandomWickOperator[n_Integer] :=
  RandomWickOperator[RandomInteger[{1, n}], n]


(**** <WickJump> ****)

WickJump::usage = "WickJump[mat] represents a set of quantum jump operators, which are linear combinations of Majorana fermion operators with coefficients given by the elements of complex matrix mat."

WickJump::odd = "The second dimension of the input matrix `` is odd: ``."

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

(* conversion *)
WickJump /:
NambuJump[WickJump[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuJump[ToDirac /@ mat, more, opts] /; (* NOT ToDiract @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[WickJump::odd, ArrayShort @ mat, Dimensions @ mat];
    False
]

(* conversion *)
WickJump /:
ToDirac[jmp_WickJump] := NambuJump[jmp]

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
Normalize[WickJump[mat_?MatrixQ, rest___], ___] := Module[
  { new = Map[Normalize, mat]/Sqrt[2] },
  (* NOTE: Notice the factor of 1/Sqrt[2]. *)
  WickJump[new, rest]
]

WickJump /:
MatrixForm[WickJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickJump /:
ArrayShort[WickJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


WickJump /:
Dagger @ WickJump[mat_?MatrixQ, rest___] :=
  WickJump[WickConjugateReverse @ mat, rest]

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

WickJump[mat_?MatrixQ, ___][in_WickState] := WickMap[WickJump @ mat][in]

(**** </WickJump> ****)


(**** <WickJumpOdds> ****)

WickJumpOdds::usage = "WickJumpOdds[mat][\[Rho]] returns the probabilities for the quantum jump processes \[Rho] \[RightTeeArrow] b[i]**\[Rho]**Dagger[b[i]], where b[i]:=Sum[mat[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of 2n bare Majorana fermion modes c[j]."

WickJumpOdds[jmp_WickJump, ___] :=
  WickMapOdds[First @ WickMap @ jmp]

(**** </WickJumpOdds> ****)


RandomWickJump::usage = "RandomWickJump[k_Integer, n_Integer] returns WickJump consisting of k linear combinations of Majorana operators."

RandomWickJump[k_Integer, n_Integer, opts___?OptionQ] :=
  WickJump[RandomMatrix @ {k, 2n}, opts]

RandomWickJump[n_Integer, opts___?OptionQ] :=
  RandomWickJump[RandomInteger @ {1, n}, n, opts]


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


(* canonicalization *)
WickMeasurement[k_Integer, n_Integer, rest___] :=
  WickMeasurement[{k}, n, rest]

(* canonicalization *)
(* NOTE: kk = {} may happen, e.g., in RandomWickCircuit. *)
WickMeasurement[kk:{___Integer}, n_Integer, rest___] := With[
  { mm = One[{n, 2*n}] },
  WickMeasurement @ NambuMeasurement @ mm[[kk]]
]

(* canonicalization *)
WickMeasurement[mat_?MatrixQ, rest___] :=
  WickMeasurement[SparseArray @ mat, rest] /;
  Head[mat] =!= SparseArray

WickMeasurement /:
Matrix[WickMeasurement[mat_?MatrixQ, ___], rest___] := Module[
  { ops = Matrix[WickJump @ mat, rest] },
  MapThread[Dot, {ConjugateTranspose /@ ops, ops}]
  (* NOTE: Returned are UNNORMALIZED projection operators. *)
]

WickMeasurement /:
Normalize[WickMeasurement[mat_?MatrixQ, rest___], ___] := Module[
  { new = Map[Normalize, mat]/Sqrt[2] },
  (* NOTE: Notice the factor of 1/Sqrt[2]. *)
  WickMeasurement[new, rest]
]

WickMeasurement /:
Dagger @ WickMeasurement[mat_?MatrixQ, rest___] :=
  WickMeasurement[WickConjugateReverse @ mat, rest]

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

(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
(* The vector vec := mat[[1]] describes a dressed Dirac fermion mode
      b := Sum[vec[[jj]] c[j], {j, 2n}]
   in terms of Majorana modes c[k]. *)
WickMeasurement[mat_?MatrixQ, ___][in:WickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { vv = First[mat],
    aa, bb, new },
  {aa, bb} = WickMeasurementKernel[N @ vv];
  new = theWickMeasurement[{aa, bb}, cvr];
  $MeasurementOut[vv] = $MeasurementOut[0];
  KeyDrop[$MeasurementOut, 0];
  WickState[{1, new}, rest]
] /; Length[mat] == 1

(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
(* The matrix mat describes a list of dressed Dirac fermion modes
      b[j] := Sum[mat[[i,j]] c[j], {j, 2n}]
   in terms of Majorana fermion modes c[k]. *)
WickMeasurement[mat_?MatrixQ, ___][in_WickState] :=
  Fold[WickMeasurement[{#2}][#1]&, in, Identity /@ mat] /;
  Length[mat] > 1
(* NOTE: Identity /@ mat is necessary because mat is usually a SparseArray. *)
(* NOTE: The dressed fermion modes associated with different rows in matrix mat do not have to be mutually orthogonal. Only required is that each row gives a proper dressed fermion mode, independently of other rows. *)


theWickMeasurement[{aa_?MatrixQ, bb_?MatrixQ}, cvr_?MatrixQ] := Module[
  { dd = -aa,
    id, mm, pp },
  id = One[Dimensions @ cvr];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det @ mm]/2, {Det::luc}]; (* prefactor = 1/2 *)
  If[ RandomReal[] < Re[pp], (* Re[...] to quickly handle numerical errors. *)
    $MeasurementOut[0] = 1,
    $MeasurementOut[0] = 0;
    dd *= -1;
    mm = id + dd . cvr
  ];
  Quiet[-dd + bb . cvr . Inverse[mm] . bb, {Inverse::luc}]
  (* NOTE: A = -D *)
]


(* conversion *)
WickMeasurement /:
ToDirac[msr_WickMeasurement] := NambuMeasurement[msr]

(* conversion *)
WickMeasurement /:
NambuMeasurement[WickMeasurement[mat:({}|_?MatrixQ), opts___?OptionQ], more___?OptionQ] :=
  NambuMeasurement[ToDirac /@ mat, more, opts]   (* NOT ToDirac @ mat. *)


(* NOTE: This happens when no measurement is performed such as in RandomWickCircuit. *)
FermionCount[WickMeasurement[{}, ___?OptionQ]] = 0

FermionCount[WickMeasurement[mat_?MatrixQ, ___?OptionQ]] := 
  Last[Dimensions @ mat]/2

Readout[WickMeasurement[m_?MatrixQ, ___]] := 
  Readout[First @ m] /; Length[m] == 1

Readout[WickMeasurement[m_?MatrixQ, ___]] := 
  Map[Readout, m]


theFermionModes::usage = "theFermionModes[msr] returns the list of Dirac fermion modes being probed by WickMeasurement msr. Used in Graphics[WickCircuit[...], ...]."

theFermionModes[WickMeasurement[{}, ___]] = {}

theFermionModes[msr:WickMeasurement[_?MatrixQ, ___]] := Module[
  { mat = First[NambuMeasurement @ msr] },
  mat = First @ PartitionInto[mat, {1, 2}];
  mat = Map[ZeroQ, mat, {3}];
  Union @ Flatten @ Map[Position[#, False]&, mat, {2}]
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
  mm = One[Dimensions @ cvr] - aa . cvr; (* D = -A *)
  pp = Quiet[Sqrt[Det @ mm]/2, {Det::luc}]; (* prefactor = 1/2 *)
  pp = Ramp[Re @ pp]; (* Ramp and Re to quickly handle numerical errors. *)
  {Ramp[1 - pp], pp}
]

(**** </WickMeasurementOdds> ****)


(**** <WickMeasurementKernel> ****)

WickMeasurementKernel::usage = "WickMeasurementKernel[vec] returns {A, B, nrm}, where A and B are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], -A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] Dagger[b]**b \[Rho] Dagger[b]**b, where b := Sum[vec[[k]] c[k], {k, 2n}] is a dressed Dirac fermion mode superposed of bare Majorana modes c[k]."
(* NOTE: The following two code pieces were for vec in the (2k-1, 2k)-encoding of Majorana modes in WickMeasurementKernel[vec]. However, they still work for vec in the (k, n+k)-encoding. *)

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
(* NOTE: This is intended for WickMeasurement (rather than WickMap), and returns only matrices A and B (but not D). *)

WickMeasurementKernel[vec_?VectorQ] := Module[
  { n = Length[vec]/2,
    xx, yy, aa, bb, nn, trs },
  xx = Re[N @ vec];  (* Notice N[...]; otherwise, it may take very long *)
  yy = Im[N @ vec];
  (* verify the dressed fermion mode *)
  If[ OddQ[Length @ vec] || Not @ ZeroQ[xx . yy] || Norm[xx] != Norm[yy],
    Message[WickMeasurement::dressed, vec];
    Return @ {One[2n], One[2n], 0}
  ];
  (* The Cartan-Dieudonné theorem *)
  {aa, bb} = WickMeasurementKernel[1, n]; (* nn is ignored *)
  trs = HouseholderMatrix[{xx, yy}];
  { trs . aa . Transpose[trs],
    trs . bb . Transpose[trs] }
]
(* NOTE: This is intended for WickMeasurement (rather than WickMap), and for efficiency, it does NOT calculate the NormSquare of vec. Furthermore, it returns only matrices A and B (but not D). *)

(**** </WickMeasurementKernel> ****)


RandomWickMeasurement::usage = "RandomWickMeasurement[k, n] randomly generates a WickMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomWickMeasurement[n] randomly selects k from {1,2,\[Ellipsis],n}."

RandomWickMeasurement[k_Integer, n_Integer] :=
  WickMeasurement @ RandomNambuMeasurement[k, n]

RandomWickMeasurement[n_Integer] :=
  WickMeasurement @ RandomNambuMeasurement[n]


(**** <WickMapKernel> ****)

WickMapKernel::usage = "WickMapKernel[type, mat] returns {A, B, D, nrm}, where A, B and D are 2n\[Times]2n real matrices and nrm is a list of prefactors. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] Sum[L[k]**\[Rho]**Dagger[L[k]], {k, m}]. For type=1, L[k] are linear combination of Majorana operators. For type=2, L[k] are bilinear combination of Majorana operators."

(* L[k] := b[k] *)
WickMapKernel[1, mat_?MatrixQ] := Module[
  {aa, bb, nn},
  {aa, bb, nn} = Transpose @ Map[WickFlopKernel, mat];
  aa = SparseArray[aa];
  {aa, SparseArray @ bb, aa, nn}
]

(* L[k] := Dagger[a[k]]**a[k], where a[k] are bare Dirac fermion mode. *)
WickMapKernel[2, kk:{___Integer}, n_Integer] := Module[
  {aa, bb},
  {aa, bb} = Transpose @ Map[WickMeasurementKernel[#, n]&, kk];
  aa = SparseArray[aa];
  {aa, SparseArray @ bb, -aa, ConstantArray[1/2, Length @ kk]}
]

(* L[k] := Dagger[b[k]]**b[k], b[i] := Sum[mat[[i, j]]**c[j], {j, 2n}] *)
WickMapKernel[2, mat_?MatrixQ] := Module[
  { nn = Map[NormSquare, mat],
    aa, bb },
  {aa, bb} = Transpose @ Map[WickMeasurementKernel, mat];
  aa = SparseArray[aa];
  {aa, SparseArray @ bb, -aa, 2*nn^2}
  (* Notice the power of 2 (rathern than just nn) and the factor of 2. *)
]
(* NOTE: This is intended for WickMap (rather than WickMeasurement), and returns all matrices A, B, and D as well as the squared norms of rows of matrix mat. *)

(**** </WickMapKernel> ****)


(**** <WickMap> ****)

WickMap::usage = "WickMap[mat] or WickMap[mat, True] represents a projective quantum operation \[Rho] \[RightTeeArrow] Sum[p[i]**\[Rho]**p[i], {i, m}] + Sum[(1-p[i])**\[Rho]**(1-p[i]), {j, m}], where m is the number of rows in mat, p[i]:=Dagger[b[i]]**b[i] are projection operators, and b[i]:=Sum[mat[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of n bare Majorana fermion modes c[j].\nWickMap[mat, False] represents \[Rho] \[RightTeeArrow] Sum[p[i]**\[Rho]**p[i], {i, m}]."

WickMap::null = "The quantum operation returns the null state."

WickMap /:
MakeBoxes[map:WickMap[{aa_?ArrayQ, bb_?ArrayQ, dd_?ArrayQ, nn_?VectorQ}, flag_], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    WickMap, msr, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", Length[First @ aa]/2 },
      BoxForm`SummaryItem @ { "Kraus elements: ", Length[nn] },
      BoxForm`SummaryItem @ { "Completion: ", flag }
    },
    { BoxForm`SummaryItem @ { "Block A: ", ArrayShort /@ aa },
      BoxForm`SummaryItem @ { "Block B: ", ArrayShort /@ bb },
      BoxForm`SummaryItem @ { "Block D: ", ArrayShort /@ dd }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* conversion *)
WickMap[jmp_WickJump, ___] :=
  WickMap[WickMapKernel[1, First @ jmp], False]

(* conversion *)
WickMap[msr_WickMeasurement, flag___] :=
  WickMap[WickMapKernel[2, First @ msr], flag]

(* default flag *)
WickMap[spec_] = WickMap[spec, False]

(* On WickState *)
WickMap[spec_, flag_][WickState[{_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  WickState[{1, WickMap[spec, flag] @ cvr}, rest]

(* On the covariance matrix *)
WickMap[{aa_?ArrayQ, bb_?ArrayQ, dd_?ArrayQ, nn_?VectorQ}, False][cvr_?MatrixQ] := Module[
  { m = Length[nn],
    mm, id, pp, k },
  id = ConstantArray[One[Dimensions @ cvr], m];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm], Det::luc];
  pp = nn*Ramp[Re @ pp];
  (* NOTE: Ramp and Re to quickly handle numerical errors. *)
  If[ ArrayZeroQ[pp],
    Message[WickMap::null];
    $WickMapOut = Indeterminate;
    Return @ Zero[Dimensions @ cvr]
  ];
  k = RandomChoice[pp -> Range[m]];
  $WickMapOut = k;
  aa[[k]] + bb[[k]] . cvr . Inverse[mm[[k]]] . Transpose[bb[[k]]]
]

(* On the covariance matrix *)
WickMap[{aa_?ArrayQ, bb_?ArrayQ, dd_?ArrayQ, nn_?VectorQ}, True][cvr_?MatrixQ] := Module[
  { m = Length[nn],
    ak, bk, dk, mm, id, pp, k },
  id = ConstantArray[One[Dimensions @ cvr], m];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm]/2, Det::luc];
  (* NOTE: A factor of 1/2 because this case is supposed to be the measurement of a fermion mode. *)
  pp = Ramp[Re @ pp];
  pp = Join[nn*Ramp[1-pp], nn*pp];
  (* NOTE: More precisely, here needs to be an additional factor 2 because the prefactors nn from WickMapKernel[2, ...] already contains the factor of 1/2. It is ignored because it is a global factor anyway. *)
  k = RandomChoice[pp -> Range[2m]];
  If[ k <= m,
    (* projection by a**Dagger[a] *)
    $WickMapOut = {k, 0};
    ak = -aa[[k]];
    dk = -dd[[k]],
    (* projection by Dagger[a]**a *)
    k -= m;
    $WickMapOut = {k, 1};
    ak = aa[[k]];
    dk = dd[[k]];
  ];
  bk = bb[[k]];
  mm = One[Dimensions @ dk] + dk . cvr;
  ak + bk . cvr . Inverse[mm] . Transpose[bk]
]

(**** </WickMap> ****)


(**** <WickMapOdds> ****)

WickMapOdds::usage = "WickMapOdds[mat][in] returns the probabilities for the projective process \[Rho] \[RightTeeArrow] p[i]**\[Rho]**p[i], where p[i]:=Dagger[b[i]]**b[i] and b[i]:=Sum[mat[[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of bare Majorana fermion modes c[j]."

(* conversion *)
WickMapOdds[jmp_WickJump, ___] :=
  WickMapOdds[WickMapKernel[1, First @ jmp], False]

(* conversion *)
WickMapOdds[WickMeasurement[mat_?MatrixQ, ___], flag___] :=
  WickMapOdds[WickMapKernel[2, mat], flag]

(* default flag *)
WickMapOdds[spec_] = WickMapOdds[spec, False]

(* canonicalize *)
WickMapOdds[{_?ArrayQ, _?ArrayQ, dd_?ArrayQ, nn_?VectorQ}, flag_] :=
  WickMapOdds[{dd, nn}, flag]

(* On WickState *)
WickMapOdds[WickMeasurement[kk:{__Integer}, ___], flag_][in_WickState] := 
  WickMapOdds[WickMapKernel[2, kk, FermionCount @ in], flag][in]

(* On WickState *)
WickMapOdds[spec_, flag_][WickState[{_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  WickMapOdds[spec, flag][cvr]

(* On covariance matrix *)
WickMapOdds[{dd_?ArrayQ, nn_?VectorQ}, False][cvr_?MatrixQ] := Module[
  { mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], Length @ nn];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm], Det::luc];
  pp = nn*Ramp[Re @ pp];
  Normalize[pp, Norm[#, 1]&]
]

WickMapOdds[{dd_?ArrayQ, nn_?VectorQ}, True][cvr_?MatrixQ] := Module[
  { mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], Length @ nn];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm]/2, Det::luc];
  pp = Ramp[Re @ pp];
  pp = Join[nn*Ramp[1-pp], nn*pp];
  Normalize[pp, Norm[#, 1]&]
]

(**** </WickMapOdds> ****)


(**** <WickGreenFunction> ****)

WickGreenFunction::usage = "WickGreenFunction[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to WickState ws.\nWickGreenFunction[ns, {k1, k2, \[Ellipsis]}] returns NambuGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NambuState ns.\nWickGreenFunction[in] is equivalent to WickGreenFunction[in, Range[n]], where n is the number of fermion modes for which input Wick or Nambu state in is defined for.\nWickGreenFunction[data] or WickGreenFunction[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Wick or BdG states.\nWickGreenFunction[{k1, k2, \[Ellipsis]}] represents an operator form of WickGreenFunction to be applied to Wick or Nambu state."

(* shortcut *)
WickGreenFunction[bc_BCSState] := NambuGreen[bc]

(* shortcut *)
WickGreenFunction[ws_WickState] := NambuGreen[ws]

(* canonical form for BdG modelsl *)
WickGreenFunction[WickState[{_, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  {grn, anm},
  {grn, anm} = First @ NambuGreen[WickCovariance @ cvr];
  NambuGreen @ {grn[[kk, kk]], anm[[kk, kk]]}
]

(* for large data *)
WickGreenFunction[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
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
    dim = N @ Whole @ Dimensions[data],
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
  Power[2, -FermionCount[ws]] * Sqrt[Whole[1 + val^2]]
]

(**** </WickPurity> ****)


(**** <WickDensityMatrix> ****)

WickDensityMatrix::usage = "WickDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function grn associated with a fermionic Gaussian state.\nWickDensityMatrix[ws] returns the density matrix corresponding to Wick state ws."

WickDensityMatrix::num = "Only numerical matrices are allowed."

(* canonical form for normal models *)
WickDensityMatrix[grn_?MatrixQ] := Module[
  { n = Length[grn],
    cc, gg, uu, id },  
  cc = theWignerJordan[n];
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

(* essentially normal models *)
WickDensityMatrix[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  WickDensityMatrix[grn] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
WickDensityMatrix[grn_NambuGreen] := Module[
  { n = FermionCount[grn],
    cc, gg, uu, id },  
  cc = theWignerJordanNambu[n];
  id = One @ Power[2, n];

  {gg, uu} = Eigensystem[N @ Normal @ grn];
  (* NOTE: N[...] is to avoid additional normaliztaion of uu and sorting. *)
  gg = Take[gg, n]; (* gg is supposed to be sorted. *)
  cc = Take[Conjugate[uu] . cc, n]; (* dressed modes *)
  cc = MapThread[Dot, {ConjugateTranspose /@ cc, cc}];
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
Dagger @ WickCircuit[gg_List, rest___] :=
  WickCircuit[Reverse @ Dagger @ gg, rest]

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
    WickMeasurement[{}, ___] -> "Spacer",
    ws_WickMeasurement :> Map[Gate[{c[#]}, "Shape" -> "Measurement"]&, theFermionModes @ ws],
    WickUnitary[_?MatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    WickUnitary[_?MatrixQ, any___?OptionQ] :> Gate[cc, any],
    WickUnitary[_?MatrixQ, _, any___?OptionQ] :> Gate[cc, any]
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
    { n = FermionCount[uu],
      mm },
    mm = RandomPick[Range @ n, p, k];
    WickCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[WickMeasurement[#, n]&, mm]
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
      tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = Map[WickUnitary[MatrixExp[hh*#]]&, tt];
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

RandomWickCircuitSimulate[in_, spec_, depth_Integer, opts___?OptionQ] := 
  RandomWickCircuitSimulate[in, spec, {depth, 2}, opts]

RandomWickCircuitSimulate[
  in_WickState,
  spec:$RandomWickCircuitPatterns,
  {depth_Integer, ds:(_Integer|All)},
  opts:OptionsPattern[]
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


theWignerJordanMajorana::usage = "theWignerJordanMajorana[n] returns a list of matrices representing 2n Majorana modes, taking into account the Wigner-Jordan transformation."

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
  SparseArray @ Join[xx, yy]
]


(**** <WickScramblingCircuit> ****)

WickScramblingCircuit::usage = "WickScramblingCircuit[op, spec, dep] generates the main part of a Wick scrambling circuit."

(* 1 - 2*Dagger[a[k]]**a[k] *)
theWickZ[k_Integer, n_Integer] := WickUnitary[
  SparseArray[
    { {k, k} -> -1,
      {n+k, n+k} -> -1,
      {i_, i_} -> 1,
      {_, _} -> 0
    },
    {2n, 2n}
  ],
  "Label" -> Subscript["Z", k]
]

(* Dagger[a[k]] + a[k] *)
theWickX[k_Integer, n_Integer] := WickUnitary[
  SparseArray[
    { {k, k} -> 1,
      {i_, i_} -> -1,
      {_, _} -> 0
    },
    {2n, 2n}
  ],
  "Label" -> Subscript["X", k]
]


WickScramblingCircuit[a_Integer, 
  spec:$RandomWickCircuitPatterns, t_Integer] := Module[
    { n = spec },
    If[ListQ @ spec, n = First @ spec];
    n = FermionCount[n];
    WickScramblingCircuit[theWickX[a, n], spec, t]
  ]


(* canonicalization *)
WickScramblingCircuit[op_, {uu_NambuUnitary, p_?NumericQ}, k_Integer] :=
  WickScramblingCircuit[op, {WickUnitary @ uu, p}, k]

(* fixed interaction time *)
WickScramblingCircuit[op_, {uu_WickUnitary, p_?NumericQ}, k_Integer] :=
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

(* canonicalization *)
WickScramblingCircuit[op_, {ham_NambuHermitian, spec__}, k_Integer] :=
  WickScramblingCircuit[{WickHermitian @ ham, spec}, k]

(* arbitrary distribution of evolution time *)
WickScramblingCircuit[op_, {ham_WickHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      tt, uu, dg, ma, mb },
    tt = RandomVariate[pdf, k];
    uu = Map[WickUnitary[MatrixExp[hh*#]]&, tt];
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

(**** </WickScramblingCircuit> ****)


(**** <WickScramblingSimulate> ****)

WickScramblingSimulate::usage = "WickScramblingSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomWickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

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
    WickScramblingSimulate[in, {theWickX[a, n], theWickZ[1, n]}, spec, rest]
  ]

WickScramblingSimulate[in_, ua_WickUnitary, rest__] :=
  WickScramblingSimulate[in, {ua, theWickZ[1, FermionCount @ ua]}, rest]

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
  va = First @ WickCovariance[va];
  vb = First @ WickCovariance[vb];
  Sqrt @ Quiet[Sqrt[Det[va + vb]] / Power[2, FermionCount @ qc], Det::luc]
]

(**** </WickScramblingSimulate> ****)


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

(* canonicalization *)
WickNonunitary[{ham_NambuHermitian, more__}, rest___] :=
  WickNonunitary[{First @ WickHermitian @ ham, more}, rest]
(* CONVENTION: (1/2) (a^\dag, a) H (a, a^\dag) = (i/4) c A c. *)

(* canonicalization *)
WickNonunitary[{ham_, dmp_NambuHermitian, gmm___}, rest___] :=
  WickNonunitary[{ham, First @ WickHermitian @ dmp, gmm}, rest]
(* CONVENTION: (1/2) (a^\dag, a) H (a, a^\dag) = (i/4) c A c. *)

(* canonicalization *)
WickNonunitary[{ham:WickHermitian[_?MatrixQ, ___], more__}, rest___] :=
  WickNonunitary[{First @ ham, more}, rest]

(* canonicalization *)
WickNonunitary[{ham_, dmp_WickHermitian, gmm___}, rest___] :=
  WickNonunitary[{ham, First @ dmp, gmm}, rest]

(* conversion *)
WickNonunitary[{ham_?MatrixQ, WickMeasurement[kk:{__Integer}, ___]}, rest___] := Module[
  { msr = One[Dimensions @ ham] },
  msr = WickMeasurement[NambuMeasurement @ msr[[kk]]];
  WickNonunitary[{ham, msr}, rest]
]

(* conversion *)
WickNonunitary[{ham_?MatrixQ, jmp:(_WickJump|_WickMeasurement)}, rest___] := Module[
  {dmp, gmm},
  {dmp, gmm} = WickDamping[jmp];
  WickNonunitary[{ham, dmp, gmm}, rest]
]

(* shortcut *)
WickNonunitary[{ham_?MatrixQ, dmp_?MatrixQ}, rest___] :=
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

  aa1 = -2*gmm*prb + Tr[dmp . new]*prb/2;
  bb1 = (ham . new - new . ham) - dmp - new . dmp . new;

  prb = nrm + aa1*dt/2;
  new = cvr + bb1*dt/2;
  aa2 = -2*gmm*prb + Tr[dmp . new]*prb/2;
  bb2 = (ham . new - new . ham) - dmp - new . dmp . new;

  prb = nrm + aa2*dt/2;
  new = cvr + bb2*dt/2;
  aa3 = -2*gmm*prb + Tr[dmp . new]*prb/2;
  bb3 = (ham . new - new . ham) - dmp - new . dmp . new;

  prb = nrm + aa3*dt;
  new = cvr + bb3*dt;
  aa4 = -2*gmm*prb + Tr[dmp . new]*prb/2;
  bb4 = (ham . new - new . ham) - dmp - new . dmp . new;

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


(**** <WickDamping> ****)

WickDamping::usage = "WickDamping[jmp] returns a pair {dmp, gmm} of the quadratic kernel dmp and remaining constant term gmm of the effective damping operator that corresponds to to quantum jump operators jmp in the WickJump or WickMeasurement form."

WickDamping[WickJump[jmp_?MatrixQ, ___]] := With[
  { mat = ConjugateTranspose[jmp] . jmp },
  { WickHermitian @ Re[ -I*(mat - Transpose[mat]) ],
    Re @ Tr[mat]/2 }
]

WickDamping[WickMeasurement[msr_?MatrixQ, ___]] := Module[
  { dig, mat },
  dig = 2*Map[NormSquare, msr];
  mat = Dot[ConjugateTranspose @ msr, dig*msr];
  { WickHermitian @ Re[ -I*(mat - Transpose[mat]) ],
    Re @ Tr[mat]/2 }
]

(**** </WickDamping> ****)


(**** <WickSimulate> ****)

$WickMinorSteps::usage = "$WickMinorSteps is a parameter that controls the behavior of WickSimulate by setting the number of minor steps for the non-unitary gate to make between major steps of update the quantum state."

$WickMinorSteps = 10;

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

WickSimulate[in_WickState, ham_NambuHermitian, rest__] :=
  WickSimulate[in, WickHermitian @ ham, rest]

WickSimulate[in_WickState, ham_WickHermitian, jmp_NambuJump, rest__] :=
  WickSimulate[in, ham, WickJump @ jmp, rest]

WickSimulate[in_WickState, ham_WickHermitian, msr_NambuMeasurement, rest__] :=
  WickSimulate[in, ham, WickMeasurement @ msr, rest]

WickSimulate[in_, ham_, jmp_, {tau_?NumericQ, dt_?NumericQ}, opts___?OptionQ] :=
  WickSimulate[in, ham, jmp, {tau, dt, All}, opts]

WickSimulate[
  in_WickState, 
  ham_WickHermitian, 
  jmp:(_WickJump | _WickMeasurement),
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)}, 
  opts:OptionsPattern[]
] := Module[
  { ns = OptionValue["Samples"],
    progress = 0,
    non, map, data, more },
    
  non = WickNonunitary[{ham, jmp}];
  map = WickMap[jmp, False];

  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[ns];
    theWickSimulate[in, non, map, {tau, dt}][[1;;All;;ds]],
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

theWickSimulate[in_WickState, non_WickNonunitary, map_WickMap, {tau_, dt_}] :=
  Module[
    { t = dt,
      res = {in},
      new = in,
      out, prb },
    While[ t <= tau,
      prb = RandomReal[];
      (* non-unitary evolution *)
      out = nonUnitaryEvolution[non, new, {dt, dt/$WickMinorSteps}];
      If[ prb < NormSquare[out],
        new = Normalize @ out;
        AppendTo[res, new];
        t += dt;
        Continue[]
      ];
      (* quantum jumps *)
      new = map[new];
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
  WickMonitor[in, WickHermitian @ ham, rest] /;
  If[ WickHermitianQ[ham], True,
    Message[WickNonitor::mat]; False
  ]

WickMonitor[in_WickState, ham_?NambuMatrixQ, rest___] :=
  WickMonitor[in, WickHermitian @ NambuHermitian @ ham, rest]

WickMonitor[in_WickState, ham_NambuHermitian, rest___] :=
  WickMonitor[in, WickHermitian @ ham, rest]

WickMonitor[in_WickState, ham_WickHermitian, msr_NambuMeasurement, rest___] :=
  WickMonitor[in, ham, WickMeasurement @ msr, rest]

WickMonitor[
  in_WickState,
  ham_WickHermitian,
  spec:{_?NumericQ, _?NumericQ, ___},
  opts___?OptionQ
] := Module[
  { n = FermionCount[in],
    map },
  map = WickMap[WickMapKernel[2, Range @ n, n], True];
  WickMonitor[in, ham, map, spec, opts]
]

WickMonitor[
  in_WickState,
  ham_WickHermitian,
  msr_WickMeasurement,
  spec:{_?NumericQ, _?NumericQ, ___},
  opts___?OptionQ
] := WickMonitor[in, ham, WickMap[msr, True], spec, opts]

WickMonitor[
  in_WickState,
  ham_WickHermitian,
  map_WickMap,
  {tau_?NumericQ, dt_?NumericQ},
  opts___?OptionQ
] := WickMonitor[in, ham, map, {tau, dt, All}, opts]

WickMonitor[
  in_WickState,
  ham_WickHermitian,
  map_WickMap,
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)},
  opts:OptionsPattern[]
] := Module[
  { n = OptionValue["Samples"],
    progress = 0,
    uni, data, more },
  uni = WickUnitary @ MatrixExp[N @ First[ham]*dt];
  (* simulation *)
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[n];
    theWickMonitor[in, uni, map, {tau, dt}][[1;;All;;ds]],
    {k, n}
  ];
  (* save data *)
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
  {tau_?NumericQ, dt_?NumericQ}
] := Module[
  { t = dt,
    res = {in},
    new = in,
    gmm },
  gmm = 2 * Total @ map[[1, 4]];
  (* NOTE: Here, the additional factor 2 is required because the prefactors map[[1, 4]] from WickMapKernel[2, ...] already contains the factor of 1/2 associated with projection Dagger[b]**b. *)
  gmm = Exp[-gmm*dt];
  While[ t <= tau,
    (* non-unitary (yet practically unitary) evolution *)
    If[ RandomReal[] < gmm,
        new = uni[new];
        AppendTo[res, new];
        t += dt;
        Continue[]
    ];
    (* quantum jumps *)
    new = map[new];
    AppendTo[res, new];
    t += dt;
  ];
  Return[res]
]

(**** </WickMonitor> ****)


(**** <WickLindbladSolve> ****)
(* See also Bravyi (2012a). *)

WickLindbladSolve::usage = "WickLindbladSolve[ham, jmp, in, t] solves the Lindblad equation associated with the Hamiltonia ham and a set of quantum jump operators jmp, and returns the fermionic Gaussian mixed state at t."

WickLindbladSolve[ham_NambuHermitian, rest__] :=
  WickLindbladSolve[WickHermitian @ ham, rest]

WickLindbladSolve[ham_WickHermitian, jmp_NambuJump, rest__] :=
  WickLindbladSolve[ham, WickJump @ jmp, rest]

WickLindbladSolve[ham_WickHermitian, msr_NambuMeasurement, rest__] :=
  WickLindbladSolve[ham, WickMeasurement @ msr, rest]


WickLindbladSolve[ham_, jmp_, in_, t_?NumericQ, rest___] :=
  First @ WickLindbladSolve[ham, jmp, in, {{t}}, rest]

WickLindbladSolve[ham_, jmp_, in_, {t0_?NumericQ, tn_?NumericQ}, rest___] :=
  WickLindbladSolve[ham, jmp, in, {Range[t0, tn]}, rest]

WickLindbladSolve[ham_, jmp_, in_,
  {ti_?NumericQ, tf_?NumericQ, dt_?NumericQ},
  rest___
] := WickLindbladSolve[ham, jmp, in, {Range[ti, tf, dt]}, rest]

WickLindbladSolve[ham_WickHermitian, jmp_, in_WickState, rest__] :=
  Map[WickState, WickLindbladSolve[ham, jmp, in[[1, 2]], rest]]

WickLindbladSolve[ham_WickHermitian, jmp_, in_WickCovariance, rest__] :=
  Map[WickCovariance, WickLindbladSolve[ham, jmp, First @ in, rest]]

WickLindbladSolve[ham_, msr_WickMeasurement, cvr_, {tt_?VectorQ}] :=
 WickLindbladSolve[ham, msr, cvr, {tt}, False]


(* quantum jump operators are linear in fermion operators *)
WickLindbladSolve[
  ham_WickHermitian,
  jmp_WickJump,
  cvr_?MatrixQ,
  {tt_?VectorQ}
] := Module[
  { xx, vp, vv },
  {xx, vp} = WickLindbladKernel[ham, jmp];
  vv = cvr - vp;
  xx = Map[MatrixExp[xx*#]&, tt];
  vv = Map[vp + # . vv . Transpose[#]&, xx];
  Map[(# - Transpose[#])/2&, vv]
]

(* quantum jump operators are projection operators *)
WickLindbladSolve[
  ham_WickHermitian,
  msr_WickMeasurement,
  cvr_?MatrixQ,
  {tt_?VectorQ},
  flag:(True | False)
] := Module[
  { vec = UpperTriangular[cvr, 1],
    spr, out },
  spr = WickLindbladKernel[ham, msr, flag];
  out = Map[MatrixExp[spr*#] . vec&, tt];
  Map[AntisymmetricMatrix, out]
]


WickLindbladKernel::usage = "WickLindbladKernel[ham, jmp] returns a pair {krn, sol}, where krn is the kernel of the vectorized equation for the Majorana covariance matrix and sol is a stationary solution.\nWickLindbladKernel[ham, msr] or WickLindbladKernel[ham, msr, flag] returns krn."

WickLindbladKernel[ham_NambuHermitian, jmp_] :=
  WickLindbladKernel[WickHermitian @ ham, jmp]

WickLindbladKernel[ham_, jmp_NambuJump] :=
  WickLindbladKernel[ham, WickJump @ jmp]

WickLindbladKernel[ham_, msr_NambuMeasurement] :=
  WickLindbladKernel[ham, WickMeasurement @ msr]


(* WickJump *)
WickLindbladKernel[ham_WickHermitian, jmp_WickJump] := Module[
  { mm = First[jmp],
    xx, yy },
  mm = Transpose[mm] . Conjugate[mm];
  xx = First[ham] - (mm + Conjugate[mm]) // Re;
  yy = -2I*(mm - Conjugate[mm]) // Re;
  mm = LyapunovSolve[xx, -yy];
  {xx, (mm - Transpose[mm])/2}
]
(* NOTE: Matrix ham is supposed to be a even-dimensional real anti-symmetric matrix. *)
(* NOTE: If ham is 2nx2n, then jmp must be mx2n. *)

(* WickMeasurement *)
WickLindbladKernel[ham_WickHermitian, msr_WickMeasurement] := Module[
  { yy = First[msr],
    mm = First[msr],
    nn = 2*Map[NormSquare, First @ msr],
    xx, id, kk, ll, m, n },
  mm = Dot[Transpose @ mm, nn*Conjugate[mm]];
  xx = First[ham] - (mm + Conjugate[mm]) // Re;
  (* Constructs the SuperMatrix. *)
  {m, n} = Dimensions[yy];
  kk = Flatten[Table[{i, j}, {i, n-1}, {j, i+1, n}], 1];
  kk = Map[FromDigits[#-1, n]+1&, kk];
  ll = IntegerReverse[kk-1, n, 2] + 1;
  id = One[n];
  xx = KroneckerProduct[xx, id] + KroneckerProduct[id, xx];
  xx = xx[[kk, kk]] - xx[[kk, ll]];
  (* the first term *)
  yy = Flatten /@ Table[
    yy[[k,i]]*Conjugate[yy[[k,j]]] - yy[[k,j]]*Conjugate[yy[[k,i]]],
    {k, m},
    {i, n-1},
    {j, i+1, n}
  ];
  yy = -4*Transpose[yy] . yy;
  Re[xx + yy]
]

WickLindbladKernel[ham_WickHermitian, msr_WickMeasurement, False] :=
  WickLindbladKernel[ham, msr]

WickLindbladKernel[ham_WickHermitian, msr_WickMeasurement, True] :=
  WickLindbladKernel[ham, Surd[2, 4]*msr]

(**** </WickLindbladSolve> ****)


(**** <WickSteadyState> ****)
(* See also Bravyi (2012a). *)

WickSteadyState::usage = "WickSteadyState[ham, jmp, in] returns the steady-state solution (i.e., a fermionic Gaussian mixed state) to the Lindblad equation associated with the Hamiltonian ham and a set of quantum jump operators jmp.\nWickSteadyState[ham, msr, in] assumes that the Lindblad operators are projective and given by Wick measurement msr."

WickSteadyState::more = "The Lindblad equation has additional steady states."

WickSteadyState[ham_NambuHermitian, rest__] :=
  WickSteadyState[WickHermitian @ ham, rest]

WickSteadyState[ham_WickHermitian, jmp_NambuJump, rest__] :=
  WickSteadyState[ham, WickJump @ jmp, rest]

WickSteadyState[ham_WickHermitian, msr_NambuMeasurement, rest__] :=
  WickSteadyState[ham, WickMeasurement @ msr, rest]


WickSteadyState[ham_WickHermitian, jmp_, in_WickState, rest___] :=
  WickState @ WickSteadyState[ham, jmp, in[[1, 2]], rest]

WickSteadyState[ham_WickHermitian, jmp_, in_WickCovariance, rest___] :=
  WickCovariance @ WickSteadyState[ham, jmp, First @ in, rest]

WickSteadyState[ham_, msr_WickMeasurement, cvr_] :=
 WickSteadyState[ham, msr, cvr, False]


(* quantum jump operators are linear in fermion operators *)
WickSteadyState[
  ham_WickHermitian,
  jmp_WickJump,
  cvr_?MatrixQ
] := Module[
  { xx, vp, vv },
  {xx, vp} = WickLindbladKernel[ham, jmp];
  If[ZeroQ[Det @ xx], Message[WickSteadyState::more]];
  Return[vp]
]

(* quantum jump operators are projection operators *)
WickSteadyState[
  ham_WickHermitian,
  msr_WickMeasurement,
  cvr_?MatrixQ,
  flag:(True | False)
] := Module[
  { in = UpperTriangular[cvr, 1],
    spr, vec, out },
  spr = WickLindbladKernel[ham, msr, flag];
  vec = Eigenvectors[N @ spr];
  out = Inverse[Transpose @ vec] . in;
  out = Last[vec] * Last[out];
  AntisymmetricMatrix[Re @ out]
]

(**** </WickSteadyState> ****)


(**** <FermionCount> ****)

FermionCount[WickState[{_?NumericQ, cvr_?MatrixQ}, ___]] := Length[cvr]/2

FermionCount[WickCovariance[cvr_?MatrixQ, ___]] := Length[cvr]/2

FermionCount[WickHermitian[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickUnitary[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickNonunitary[{ham_?MatrixQ, _?MatrixQ, _}, ___]] := Last[Dimensions @ ham]/2

FermionCount[WickJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[WickOperator[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

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

Options[WickTimeReversalMoment] = { 
  "Epsilon" -> 1.25*^-16
  (* "Epsilon" -> 1.25*^-20 *)
}

(* canoncialization *)
WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  WickTimeReversalMoment[alpha, NambuGreen @ {grn, 0}, kk, opts]

(* canoncialization *)
WickTimeReversalMoment[alpha_, grn_?NambuMatrixQ, rest__] := 
  WickTimeReversalMoment[alpha, NambuGreen @ grn, rest]

(* canoncial form *)
WickTimeReversalMoment[
  alpha_, grn_NambuGreen, kk:{__Integer},
  opts___?OptionQ
] := Quiet[
  theTimeReversalMoment[alpha, grn, kk, opts],
  {Det::luc, Inverse::luc}
]
(* 2024-08-11: Dot::luc and Inverse::luc are silenced; the warning message goes off too often while it does not seem to be serious in most cases. *)
(* 2025-01-18 (v3.8.2): All Pfaffian is replaced by Sqrt@*Det because the current implementation of Pfaffian is slow and racks accuracy. *)

(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)
theTimeReversalMoment[
  alpha_, grn_NambuGreen, kk:{__Integer},
  OptionsPattern[WickTimeReversalMoment]
] := Module[
  { n = FermionCount[grn],
    gg, id, xx, zz, uu, ww, pf1, pf2, pf3, dgn, off
  },
  id = One[n];
  xx = KroneckerProduct[ThePauli[1], id];
  zz = KroneckerProduct[ThePauli[3], id];
  (* \Gamma *)
  gg = Normal[N @ NambuHermitian @ grn];
  gg -= I * OptionValue["Epsilon"] * One[Dimensions @ gg];
  (* NOTE: When there is a fermion mode that is unoccuppied with certainty, the coherent-state representation becomes unusual, and one needs to handle such cases separately. While this is possible, Q3 offers a ditry trick. *)  
  pf1 = Det[gg];
  (* \Omega *)
  ww = Inverse[gg] - zz;
  (* \Omega of partial TR *)
  uu = theTimeReversalUnitary[kk, n];
  ww = ConjugateTranspose[uu] . ww . uu;
  (* \Xi *)
  dgn = CirclePlus[ww[[;;n, ;;n]], ww[[n+1;;, n+1;;]]];
  off = ArrayFlatten @ {
    {0, ww[[;;n, n+1;;]]},
    {ww[[n+1;;, ;;n]], 0}
  };
  pf2 = Sqrt @ Det[id + ww[[n+1;;, ;;n]] . ww[[;;n, n+1;;]]];
  (* effective \Omega of \Xi *)
  ww = Inverse[zz - off];
  ww = off + dgn . ww . dgn;
  pf3 = Sqrt @ Det[xx . (ww + zz)];
  (* effective \Gamma of \Xi *)
  gg = Inverse[ww + zz];
  (* effective Green's function of \Xi *)
  gg = NambuGreen[NambuHermitian @ gg];
  gg = Take[Eigenvalues @ Normal @ gg, n];
  (* Recall the particle-hole symmetry. *)
  Total[Log[2, Power[gg, alpha] + Power[1-gg, alpha]]] + 
    Log[2, Power[Abs[pf1*pf2*pf3], alpha]]
  (* NOTE: Abs[...] to prevent a spurious imaginary part. *)
]

theTimeReversalUnitary[kk:{__Integer}, n_Integer] := SparseArray[
  Flatten @ {
    Thread[Transpose@{kk, kk} -> 0],
    Thread[Transpose@{kk, n+kk} ->  I],
    Thread[Transpose@{n+kk, kk} -> -I],
    Thread[Transpose@{n+kk, n+kk} -> 0],
    {i_, i_} -> 1,
    {_, _} -> 0
  },
  {2n, 2n}
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
WickLogarithmicNegativity[data_?ArrayQ, kk:{___Integer}, opts___?OptionQ] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickLogarithmicNegativity[#, kk, opts])&, data, {dep}]
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
  cx = (id - Inverse[id + gp . gm] . (gp + gm)) / 2;
  cx = Eigenvalues[cx];
  gg = Eigenvalues[id - Transpose[grn]];
  Total[Log[2, Sqrt[cx] + Sqrt[1-cx]]] + Total[Log[2, gg^2 + (1-gg)^2]]/2
]

(* BdG models *)
WickLogarithmicNegativity[grn_NambuGreen, kk:{__Integer}, ___] :=
  WickLogarithmicNegativity[grn[[1, 1]], kk] /; ArrayZeroQ[grn[[1, 2]]] 

WickLogarithmicNegativity[grn_NambuGreen, kk:{__Integer}, ___] := 0 /;
  FermionCount[grn] == Length[kk]

(* Canonical form for BdG models *)
WickLogarithmicNegativity[
  grn_NambuGreen, kk:{__Integer}, 
  opts:OptionsPattern[]
] := WickTimeReversalMoment[1/2, grn, kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]

(* canonicalization *)
WickLogarithmicNegativity[grn_?NambuMatrixQ, rest__] :=
  WickLogarithmicNegativity[NambuGreen @ grn, rest]

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
    dim = Whole[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickEntanglementEntropy[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState | _WickCovariance | _NambuGreen]&]

(* directly from covariance matrix *)
WickEntanglementEntropy[WickCovariance[cvr_?MatrixQ, ___], kk:{__Integer}] := Module[
  { jj = Join[kk, kk + Length[cvr]/2] },
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
  { n = FermionCount[cvr],
    ii, jj, ll },
  ll = Supplement[Range @ n, kk];
  ii = Riffle[kk, n + kk];
  jj = Riffle[ll, n + ll];
  ( WickEntropy[ WickCovariance @ vv[[ii, ii]] ] + 
    WickEntropy[ WickCovariance @ vv[[jj, jj]] ] -
    WickEntropy[ WickCovariance @ vv ]
  ) / 2
]

(* for large data *)
WickMutualInformation[data_?ArrayQ, kk:{___Integer}] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
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
