(* ::Package:: *)

(* Fermionic Quantum Computing *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ BravyiState, RandomBravyiState,
  BravyiCovariance, BravyiCount };
{ BravyiPureQ, BravyiPurity, 
  BravyiNullQ, BravyiSingleQ };
{ BravyiInner, BravyiTranspose };
{ BravyiDensityMatrix };

{ BCSState, BCSStateQ };

{ BravyiUnitary, BravyiHermitian,
  RandomBravyiUnitary, RandomBravyiHermitian, RandomBravyiCovariance };
{ BravyiNonunitary, RandomBravyiNonunitary };

{ BravyiMap };
{ BravyiJump, RandomBravyiJump };
{ BravyiMeasurement, RandomBravyiMeasurement };
{ BravyiOdds, BravyiKernel };

{ BravyiElements, BravyiCoefficients };

{ BravyiGreen, BravyiOccupation,
  BravyiMean, BravyiCanonicalize };

{ BravyiCircuit, RandomBravyiCircuit, RandomBravyiCircuitSimulate };
{ BravyiSimulate, BravyiDamping, $BravyiMinorSteps };
{ BravyiMonitor };

{ BravyiScramblingCircuit, BravyiScramblingSimulate };

{ BravyiLindbladSolve,
  BravyiSteadyState };

{ BravyiLogarithmicNegativity, BravyiTimeReversalMoment };
{ BravyiEntropy, BravyiEntanglementEntropy, BravyiMutualInformation };

{ WickDensityMatrix,
  WickEntropy, WickEntanglementEntropy, WickMutualInformation,
  WickLogarithmicNegativity }; (* Wick.wl *)

(* VonNeumann.wl *)
{ QuantumLog };


Begin["`Private`"] (* Fermionic quantum computation *)

(**** <BCSState> ****)
BCSState::usage = "BCSState[pair] represents a generalized BCS ground state characterized by the pairing matrix pair."
(* See Russomanno (2023) and Zanca and Santoro (2016). *)

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
BravyiState[in_BCSState] := With[
  { nrm = NormSquare[in],
    grn = NambuGreen[in] },
  BravyiState[{nrm, BravyiCovariance @ grn}, Options @ in]
]

BCSState /:
ExpressionFor[in:BCSState[{_?NumericQ, _?MatrixQ}, ___], ss:{___?SpeciesQ}] :=
  ExpressionFor[Matrix[in, ss], ss]

BCSState /:
Matrix[BCSState[{ff_?NumericQ, zz_?MatrixQ}, ___]] := Module[
  { mm = ConjugateTranspose /@ JordanWignerTransform[Length @ zz],
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
BCSState[ws_BravyiState] := Module[
  { gg, ff, ww },
  {gg, ff} = First[NambuGreen @ ws];
  ww = -Inverse[gg].ff;
  Normalize[BCSState @ ww]
] /; 
If[ BravyiPureQ[ws],
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

BCSStateQ[ws_BravyiState] :=
  BCSStateQ[NambuGreen @ ws]

(* See also the Thouless theorem (Appendix E.3) in Ring80a. *)
BCSStateQ[grn_NambuGreen] :=
  Not[ ZeroQ @  Det @ grn[[1, 1]] ] /; BravyiPureQ[grn]

BCSStateQ[grn_NambuGreen] = False
(**** </BCSStateQ> ****)


(**** <BravyiState> ****)
BravyiState::usage = "BravyiState[uv, trs] represents a many-body quantum state for non-interacting fermion modes that has undergone the overall Bogoliubov-de Gennes (BdG) type time evolution in the Nambu space specified by reduced Nambu matrix uv and decoherence processes (including measurements) specified by matrix trs."

BravyiState::complex = "The covariance matrix `` must be a real anti-symmetric matrix."

BravyiState::cvr = "Matrix `` is not a valid covariance matrix; it must be a even-dimensional real anti-symmetric matrix."

BravyiState::convex = "Attemp non-convex linear superposition of Gaussian states."

BravyiState::bad = "Unsupported form of Nambu state ``."

BravyiState /:
MakeBoxes[ws:BravyiState[{fac_?NumericQ, cvr_?MatrixQ}, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BravyiState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ws },
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Covariance: ", ArrayShort @ cvr }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; EvenQ[Length @ cvr]

(* canonicalization *)
BravyiState[cvr_?MatrixQ, opts___?OptionQ] :=
  BravyiState[{1, cvr}, opts] /; If[
    BravyiHermitianQ[cvr], True,
    Message[BravyiState::cvr, cvr]; False
  ]

(* canonicalization *)
BravyiState[cvr_BravyiCovariance, opts___?OptionQ] :=
  BravyiState[{1, First @ cvr}, opts]

(* canonicalization *)
BravyiState[grn_NambuGreen, opts___?OptionQ] :=
  BravyiState[{1, BravyiCovariance @ grn}, opts]

(* canonicalization *)
BravyiState[{fac_, cvr_BravyiCovariance}, rest___?OptionQ] :=
  BravyiState[{fac, First @ cvr}, rest]

(* canonicalization *)
BravyiState[{fac_, cvr_?MatrixQ}, rest___?OptionQ] :=
  BravyiState[{fac, SparseArray @ cvr}, rest] /;
    Head[cvr] =!= SparseArray

(* canonicalization *)
BravyiState[{fac_, cvr_?MatrixQ}, rest___?OptionQ] := If[
  ArrayZeroQ[Im @ cvr], 
  BravyiState[Re @ {fac, cvr}, rest],
  With[
    { re = Re[cvr] },
    Message[BravyiState::complex, ArrayShort @ cvr];
    BravyiState[{fac, (re - Transpose[re])/2}, rest]
  ]
] /; Not[arrayRealQ @ cvr]


(* initialization by occupation numbers *)
BravyiState[vv_?VectorQ, n_Integer, rest___?OptionQ] := Module[
  { ww = DiagonalMatrix @ PadRight[vv, n, vv],
    gg },
  gg = NambuGreen @ {One[n] - ww, 0};
  BravyiState[{1, BravyiCovariance @ gg}, rest]
] /; VectorQ[vv, BinaryQ]

(* initialization *)
BravyiState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  BravyiState[Lookup[aa, cc], Length @ cc]
]

BravyiState /:
NambuGreen[BravyiState[{_?NumericQ, cvr_?MatrixQ}, ___]] :=
  NambuGreen[BravyiCovariance @ cvr]

BravyiState /:
Re[BravyiState[data:{_?NumericQ, _?MatrixQ}, rest___]] :=
  BravyiState[Re[data], rest]

BravyiState /:
Im[BravyiState[data:{_?NumericQ, _?MatrixQ}, rest___]] :=
  BravyiState[Im[data], rest]

BravyiState /:
NormSquare[BravyiState[{fac_?NumericQ, _?MatrixQ}, ___]] := Abs[fac]

BravyiState /:
Norm[BravyiState[{fac_?NumericQ, _?MatrixQ}, ___]] := Sqrt[Abs @ fac]


BravyiState /:
Normalize[BravyiState[{_?NumericQ, cvr_?MatrixQ}, rest___]] :=
  BravyiState[{1, cvr}, rest]


(* convex linear superposition *)
BravyiState /:
Plus[BravyiState[{fa_, va_}, any___], BravyiState[{fb_, vb_}, other___]] :=
  BravyiState[{fa + fb, (fa*va + fb*vb)/(fa+fb)}, any, other]

BravyiState /:
Times[z_?NumericQ, BravyiState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  BravyiState[{z*fac, cvr}, rest] /;
    If[ QuantumMob`Q3`RealQ[z], True,
      Message[BravyiState::convex, z];
      False
    ]
(* NOTE: This feature is to support convex linear superposition of two Gaussian states as mixed states. In principle, the numerical factor must be in [0, 1]. Here, any real number is allowed for convenience. *)


BravyiState /:
Elaborate[ws:BravyiState[{_?NumericQ, _?MatrixQ}, ___]] :=
  ExpressionFor[Matrix @ ws]

BravyiState /:
ExpressionFor[ws:BravyiState[{_?NumericQ, _?MatrixQ}, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ ws, cc]


BravyiState /:
Matrix[ws:BravyiState[{_?NumericQ, _?MatrixQ}, ___], ss:{___?SpeciesQ}] :=
  MatrixEmbed[Matrix @ ws, Select[ss, FermionQ], ss]

BravyiState /: (* null state *)
Matrix[BravyiState[{0, cvr_?MatrixQ}, ___]] :=
  Zero @ Power[2, Length[cvr]/2]

BravyiState /: (* mixed states *)
Matrix[BravyiState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] :=
  fac * BravyiDensityMatrix[BravyiCovariance @ cvr]
(* NOTE: It might be more efficient to use the Murnaghan's canonical form; see Paardekooper (1971) and Humeniuk and Mitrik (2018). Here, we do not try it because this function is intended for elementary tests anyway. *)

(* NOTE: This was originally for cvr in the (2k-1, 2k)-encoding of Majorana modes. However, it still works for cvr in the (k, n+k)-encoding. *)
BravyiState /: (* pure states *)
Matrix[ws:BravyiState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] := Module[
  { n = FermionCount[ws],
    xy, vv, mm, pp, id },
  xy = theJordanWignerMajorana[n]; (* now both cvr and xy in the (k,n+k)-encoding *)

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
] /; BravyiPureQ[cvr]


BravyiState /:
NonCommutativeQ[_BravyiState] = True

BravyiState /:
MultiplyKind[_BravyiState] = Fermion
(**** </BravyiState> ****)


RandomBravyiState::usage = "RandomBravyiState[n] randomly generates a Gaussian pure state of n fermion modes."

RandomBravyiState[n_Integer, opts___?OptionQ] :=
  BravyiState[{1, RandomBravyiCovariance @ n}, opts]


(**** <BravyiPureQ> ****)
BravyiPureQ::usage = "BravyiPureQ[cvr] returns True if Majorana covariance matrix cvr represents a prue state; False, otherwise./nBravyiPureQ[bdg] tests the BdG state."

BravyiPureQ[cvr_?MatrixQ] := ArrayZeroQ[
  One[Dimensions @ cvr] + cvr.cvr
]

BravyiPureQ[cvr_BravyiCovariance] :=
  BravyiPureQ[First @ cvr]

BravyiPureQ[BravyiState[{_, cvr_?MatrixQ}, ___]] :=
  BravyiPureQ[cvr]
(**** </BravyiPureQ> ****)


(**** <BravyiNullQ> ****)
BravyiNullQ::usage = "BravyiNullQ[ws] returns True if Bravyi state ws is the null state; False, otherwise."

BravyiNullQ[ws_BravyiState] := ZeroQ[ws[[1, 1]]]
(**** </BravyiNullQ> ****)


(**** <BravyiSingleQ> ****)
BravyiSingleQ::usage = "BravyiSingleQ[cvr] returns True if Majorana covariance matrix cvr represents a fermion Gaussian state resulting from single-particle potential only (without pairing potential); False, otherwise.\nBravyiSingleQ[ws] tests the Bravyi state ws.\nBravyiState[grn] tests the Green function grn."

BravyiSingleQ[cvr_?MatrixQ] := Module[
  { aa, bb },
  aa = Transpose[ cvr[[1;;All;;2]] ][[1;;All;;2]];
  bb = Transpose[ cvr[[2;;All;;2]] ][[2;;All;;2]];
  ArrayZeroQ[aa - bb]
]

BravyiSingleQ[cvr_BravyiCovariance] :=
  BravyiSingleQ[First @ cvr]

BravyiSingleQ[BravyiState[{_?NumericQ, cvr_?MatrixQ}, ___]] :=
  BravyiSingleQ[cvr]

BravyiSingleQ[NambuGreen[{_?MatrixQ, anm_?MatrixQ}]] :=
  ArrayZeroQ[anm]
(**** </BravyiSingleQ> ****)


(**** <BravyiCovariance> ****)
BravyiCovariance::usage = "BravyiCovariance[mat] is a wrapper of the covariance matrix mat in the Majorana spinor space.\nBravyiCovariance[grn] converts Green's function grn, given in the NambuGreen[...] form, to equivalent covariance matrix in the Majorana spinor space."

BravyiCovariance /:
MakeBoxes[vv:BravyiCovariance[mat_?MatrixQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BravyiCovariance, vv, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ vv },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ mat }
    },
    { BoxForm`SummaryItem @ { "Matrix: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* shortcut *)
BravyiCovariance /:
Normal[BravyiCovariance[mat_?MatrixQ, ___], rest___] := Normal[mat, rest]

(* shortcut *)
BravyiCovariance[ws_BravyiState] := BravyiCovariance[ ws[[1, 2]] ]

(* conversion *)
BravyiCovariance[grn_NambuGreen] := Module[
  { crr = 4*ToMajorana[Normal @ grn],
    cvr },
  (* NOTE: Notice the factor of 4. *)
  cvr = I*(crr - One[Dimensions @ crr]);
  If[MatrixQ[cvr, NumericQ], cvr = Re[cvr]];
  BravyiCovariance[cvr]
]

(* conversion *)
NambuGreen[cvr_BravyiCovariance] := Module[
  { crr = One[2*FermionCount[cvr]] - I*First[cvr] },
  NambuGreen[ToDirac @ crr] / 4
  (* NOTE: Notice the factor of 1/4. *)
]

(* conversion from "correlation matrix" (see NambuGreen) *)
BravyiCovariance[crr_NambuHermitian] := Module[
  { n = FermionCount[crr],
    mat },
  mat = NambuHermitian[1, n]/2 - crr;
  BravyiCovariance @ Re[4I*ToMajorana[Normal @ mat]]
  (* NOTE: Notice the factor of 4. *)
]


BravyiCovariance /:
Normal[BravyiCovariance[mm_?MatrixQ, ___], rest___] :=
  Normal[mm, rest]

BravyiCovariance /:
MatrixForm[BravyiCovariance[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

BravyiCovariance /:
ArrayShort[BravyiCovariance[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

BravyiCovariance /:
Plus[BravyiCovariance[a_, any___], BravyiCovariance[b_, other___]] :=
  BravyiCovariance[a + b, any, other]

BravyiCovariance /:
Times[z_, BravyiCovariance[mat_, rest___]] :=
  BravyiCovariance[z*mat, rest]
(**** </BravyiCovariance> ****)


RandomBravyiCovariance::usage = "RandomBravyiCovariance[n] randomly generates a coveriance matrix for a Gaussian pure state of 2n Majorana modes."

RandomBravyiCovariance[n_Integer] := Module[
  { yy, mm, in },
  yy = CircleTimes[One[n], I*ThePauli[2]];
  mm = RandomOrthogonal[2n];
  BravyiCovariance @ Chop[ Transpose[mm] . yy . mm ]
]


(**** <BravyiCanonicalize> ****)
BravyiCanonicalize::usage = "BravyiCanonicalize[obj] converts object obj (such as BravyiJump and BravyiMeasurement) into a canonical form."

BravyiCanonicalize[BravyiJump[mat_?MatrixQ, rest___]] := With[
  { max = Sqrt[2]*Max[Norm /@ mat] },
  (* NOTE: Notice the factor of Sqrpt[2]. *)
  BravyiJump[mat/max, rest]
]

BravyiCanonicalize[BravyiMeasurement[mat_?MatrixQ, rest___]] := With[
  { max = Sqrt[2]*Max[Norm /@ mat] },
  (* NOTE: Notice the factor of Sqrpt[2]. *)
  BravyiMeasurement[mat/max, rest]
]

BravyiCanonicalize[NambuJump[mat_?MatrixQ, rest___]] := With[
  { max = Max[Norm /@ mat] },
  NambuJump[mat/max, rest]
]

BravyiCanonicalize[NambuMeasurement[mat_?MatrixQ, rest___]] := With[
  { max = Max[Norm /@ mat] },
  NambuMeasurement[mat/max, rest]
]
(**** </BravyiCanonicalize> ****)


(**** <BravyiInner> ****)
BravyiInner::usage = "BravyiInner[a, b] calculate the Hilbert-Schmidt product Tr[Dagger[\[Rho]]\[Sigma]] of two density matrices \[Rho] and \[Sigma] corresponding to Bravyi state a and b."

BravyiInner[a_BravyiState, b_BravyiState] :=
  theBravyiInner[ a[[1, 2]], b[[1, 2]] ]

BravyiInner[a_BravyiCovariance, b_BravyiCovariance] :=
  theBravyiInner[First @ a, First @ b]

(* Assuming va and vb are 2n x 2n real anti-symmetric matrices. *)
theBravyiInner[va_?MatrixQ, vb_?MatrixQ] := Quiet[
  Sqrt[Det[One[Dimensions @ va] - Dot[va, vb]] / Power[2, Length @ va]]
]
(**** </BravyiInner> ****)


(**** <BravyiTranspose> ****)
BravyiTranspose::usage = "BravyiTranspose[cvr] returns the Majorana covariance matrix of the partial transpose of the Gaussian state specified by the Majorana covariance matrix cvr.\nNote that the resulting covariance matrix is not real any longer (though still anti-symmetric), implying that the corresponding Gaussian operator is not Hermitian any longer."
(* SEE ALSO: Bravyi (2005) and Shapourian and Ryu (2017, 2019) *)

BravyiTranspose[BravyiState[{fac_, cvr_}, rest___], kk:{___Integer}] :=
  BravyiState[{fac, BravyiTranspose[cvr, kk]}, rest]

BravyiTranspose[cvr_BravyiCovariance, kk:{___Integer}] :=
  BravyiCovariance[BravyiTranspose[Normal @ cvr, kk], Options @ cvr]

BravyiTranspose[cvr_?MatrixQ, kk:{___Integer}] := Module[
  { n = Length[cvr]/2,
    mat },
  mat = ReplacePart[ConstantArray[1, n], Thread[kk -> I]];
  mat = DiagonalMatrix[Join[mat, mat], TargetStructure -> "Sparse"];
  Dot[mat, cvr, mat]
]
(**** </BravyiTranspose> ****)


(**** <BravyiMean> ****)
BravyiMean::usage = "BravyiMean[data] returns the average of the Bravyi states or Majorana covariance matrices in array data."

BravyiMean[data_?ArrayQ] := Module[
  { cvr },
  cvr = Mean @ ReplaceAll[ data,
    { ws_BravyiState :> ws[[1, 2]],
      cv_BravyiCovariance :> First[cv] }
  ];
  Map[BravyiCovariance, cvr, {ArrayDepth[cvr] - 2}]
] /; ArrayQ[data, _, MatchQ[#, _BravyiState | _BravyiCovariance]&]
(**** <BravyiMean> ****)


(**** <BravyiConjugateReverse> ****)
BravyiConjugateReverse::usage = "BravyiConjugateReverse[mat] is equivalent to Conjugate[Reverse @ mat].\nIt is useful to handle the Hermitian conjugate of BravyiJump and BravyiMeasurement."

BravyiConjugateReverse[ops_?MatrixQ] := Conjugate[Reverse @ ops]
(**** </BravyiConjugateReverse> ****)


(**** <BravyiUnitary> ****)
BravyiUnitary::usage = "BravyiUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Nambu space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively."

BravyiUnitary /:
MakeBoxes[op:BravyiUnitary[uu_?MatrixQ, rest___], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    BravyiUnitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ uu }
    },
    { BoxForm`SummaryItem @ { "Transformation matrix: ", ArrayShort @ uu }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* zero in the Nambu space *)
BravyiUnitary[0, n_Integer, rest___] :=
  BravyiUnitary[Zero @ {2n, 2n}, rest]

(* identity in the Nambu space *)
BravyiUnitary[1, n_Integer, rest___] :=
  BravyiUnitary[One[2n], rest]

BravyiUnitary[BravyiUnitary[mat_?MatrixQ, rest___], more___] :=
  BravyiUnitary[mat, more, rest]


BravyiUnitary /:
Normal[BravyiUnitary[mm_?MatrixQ, ___], rest___] :=
  Normal[mm, rest]

BravyiUnitary /:
MatrixForm[BravyiUnitary[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

BravyiUnitary /:
ArrayShort[BravyiUnitary[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

BravyiUnitary /:
Dagger @ BravyiUnitary[mat_?MatrixQ, rest___] :=
  BravyiUnitary[Transpose @ mat, rest] /;
  If[ arrayRealQ[mat], True,
    Message[BravyiUnitary::complex, ArrayShort @ mat];
    False    
  ]

BravyiUnitary /:
Plus[BravyiUnitary[a_, any___], BravyiUnitary[b_, other___]] :=
  BravyiUnitary[a + b, any, other]

BravyiUnitary /:
Times[z_, BravyiUnitary[mm_, rest___]] :=
  BravyiUnitary[z * mm, rest]

BravyiUnitary /:
Dot[BravyiUnitary[a_, any___], BravyiUnitary[b_, other___]] :=
  BravyiUnitary[Dot[a, b], any, other]


BravyiUnitary /:
ExpressionFor[op:BravyiUnitary[_?MatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

BravyiUnitary /: (* fallback *)
ExpressionFor[op_BravyiUnitary, ___] = op


BravyiUnitary /:
Matrix[BravyiUnitary[mat_?MatrixQ, ___]] := Module[
  { ham = MatrixLog[mat] },
  ham = ToDirac[ham] * I/2;
  MatrixExp[-I*Matrix[NambuHermitian @ ham]]
]

BravyiUnitary /:
Matrix[uu:BravyiUnitary[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := 
  MatrixEmbed[Matrix[uu], Select[ss, FermionQ], ss]

BravyiUnitary /: (* fallback *)
Matrix[op_BravyiUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


BravyiUnitary /:
NonCommutativeQ[_BravyiUnitary] = True

BravyiUnitary /:
MultiplyKind[_BravyiUnitary] = Fermion

BravyiUnitary /:
Multiply[pre___, opr_BravyiUnitary, ws_BravyiState] := Multiply[pre, opr[ws]]

BravyiUnitary /:
Multiply[pre___, opr_BravyiUnitary, fs_Ket] := Multiply[pre, opr[BravyiState @ fs]]

BravyiUnitary[trs_?MatrixQ, ___][BravyiState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { new = trs . cvr . Transpose[trs] },
  BravyiState[{fac, new}, rest]
]

(* conversion *)
NambuUnitary /:
BravyiUnitary[uv:NambuUnitary[_?NambuMatrixQ, opts___?OptionQ], more___?OptionQ] := 
  BravyiUnitary[2*Re[ToMajorana @ Normal @ uv], more, opts]
(* NOTE: Notice the factor of 2 to keep the result to be unitary. *)

(* conversion *)
NambuUnitary /:
ToMajorana[op_NambuUnitary] := BravyiUnitary[op]

(* conversion *)
BravyiUnitary /:
NambuUnitary[BravyiUnitary[rot_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuUnitary[ToDirac[rot]/2, more, opts]

(* conversion *)
BravyiUnitary /:
ToDirac[op_BravyiUnitary] := NambuUnitary[op]
(**** </BravyiUnitary> ****)


(**** <NambuUnitary> ****)
NambuUnitary /:
Multiply[pre___, opr_NambuUnitary, fs_Ket] := Multiply[pre, opr[BravyiState @ fs]]

NambuUnitary /:
Multiply[pre___, opr_NambuUnitary, ws_BravyiState] := Multiply[pre, opr[ws]]

NambuUnitary[uv_?NambuMatrixQ, ___][in:BravyiState[{_?NumericQ, _?MatrixQ}, ___]] :=
  BravyiUnitary[uv][in]
(**** </NambuUnitary> ****)


RandomBravyiUnitary[n_Integer, rest___] := Module[
  { mat = RandomOrthogonal[2n] },
  mat[[1, ;;]] *= Det[mat];
  (* NOTE: Make sure to have a SU(2n) matrix. *)
  BravyiUnitary[mat, rest]
]


(**** <BravyiHermitian> ****)
BravyiHermitian::usage = "BravyiHermitian[m] represents a quadractic Hermitian operator (\[ImaginaryI]/4) \[CapitalSigma]ij ci mij cj in the Majorana spinor space, where m is a real anti-symmetric matrix."

BravyiHermitian /:
MakeBoxes[op:BravyiHermitian[mm_?MatrixQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BravyiHermitian, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ mm }
    },
    { BoxForm`SummaryItem @ { "Matrix: ", ArrayShort @ mm }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

BravyiHermitian /:
Normal[BravyiHermitian[mat_?MatrixQ, ___], rest___] :=
  Normal[mat, rest]

(* conversion *)
NambuHermitian /:
BravyiHermitian[ham:NambuHermitian[_?NambuMatrixQ, opts___?OptionQ], more___?OptionQ] :=
  BravyiHermitian[-2I*ToMajorana[Normal @ ham], more, opts]

(* conversion *)
NambuHermitian /:
ToMajorana[op_NambuHermitian] := BravyiHermitian[op]

(* conversion *)
BravyiHermitian /:
NambuHermitian[BravyiHermitian[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuHermitian[ToDirac[mat]*I/2, more, opts]

(* conversion *)
BravyiHermitian /:
ToDirac[op_BravyiHermitian] := NambuHermitian[op]


BravyiHermitian /:
MatrixForm[BravyiHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

BravyiHermitian /:
ArrayShort[BravyiHermitian[mm_?MatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

BravyiHermitian /:
Dagger[op_BravyiHermitian] = op

BravyiHermitian /:
Plus[BravyiHermitian[a_, any___], BravyiHermitian[b_, other___]] :=
  BravyiHermitian[a + b, any, other]

BravyiHermitian /:
Times[z_, BravyiHermitian[mm_, rest___]] :=
  BravyiHermitian[z * mm, rest]


BravyiHermitian /:
ExpressionFor[op:BravyiHermitian[_?MatrixQ, ___], aa:{__?FermionQ}] := Module[
  { mat = Normal[NambuHermitian @ op],
    aaa = Join[aa, Dagger @ aa] },
  Garner[ MultiplyDot[Dagger @ aaa, mat.aaa] / 2 ]
]

BravyiHermitian /:
ExpressionFor[BravyiHermitian[mat_?MatrixQ, ___], cc:{__?MajoranaQ}] :=
  Garner[ MultiplyDot[cc, mat, cc] * (I/4) ]

BravyiHermitian /:
Matrix[op:BravyiHermitian[mat_?MatrixQ, ___]] := Module[
  { n = FermionCount[op],
    xy, mm },
  xy = theJordanWignerMajorana[n];
  mm = Transpose[xy, {3, 1, 2}] . mat . xy;
  TensorContract[mm * I/4, {{2, 3}}]
]


BravyiHermitianQ::usage = "BravyiHermitianQ[mat] returns True if matrix mat is an even-dimensional real anti-symmetric matrix, which can represent a Hermitian operator quadratic in Majorana fermion operators."

BravyiHermitianQ[mat_?SquareMatrixQ] := And[
  EvenQ[Length @ mat],
  arrayRealQ[mat],
  AntisymmetricMatrixQ[mat]
]

BravyiHermitianQ[_] = False
(**** </BravyiHermitian> ****)


RandomBravyiHermitian[n_Integer, opts___?OptionQ] := 
  BravyiHermitian[Re @ RandomAntisymmetric[2n], opts]


(**** <BravyiElements> ****)
BravyiElements::usage = "BravyiElements[mat, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of Majorana operators {c1, c2, \[Ellipsis]} with the coefficients specified by elements of complex matrix mat.\nBravyiElements[mat, {a1, a2, \[Ellipsis]}] returns a list of linear combinations of the annihilation and creation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}, where the elements of complex matrix mat are the coefficients in the equivalent linear combinations of Majorana fermion operators (not the Dirac fermion operators themselves) corresponding to the Dirac fermion modes."

BravyiElements[mat_?MatrixQ, cc:{__?MajoranaQ}] :=
  Dot[mat, cc]

BravyiElements[mat_?MatrixQ, aa:{__?FermionQ}] := 
  Dot[ToDirac /@ mat, Join[aa, Dagger @ aa]]

BravyiElements[
  (BravyiJump|BravyiMeasurement)[mat_?MatrixQ, ___],
  spec:({__?MajoranaQ} | {__?FermionQ} )
] := BravyiElements[mat, spec]
(**** </BravyiElements> ****)


(**** <BravyiCoefficients> ****)
BravyiCoefficients::usage = "BravyiCoefficients[expr, {c1,c2,\[Ellipsis]}] returns a vector or matrix of coefficients in a linear combination or linear combinations of Majorana fermion operators {c1,c2,\[Ellipsis]}.\nBravyiCoefficients[expr, {a1,a2,\[Ellipsis]}] gets a vector or matrix of coefficients in a linear combination or linear combinations of the annihilation and creation operators of Dirac fermion modes {a1,a2,\[Ellipsis]}, and transforms it to a vector or matrix of coefficients in the equivalent linear combination(s) of the Majorana operators corresponding to the Dirac fermion modes."

BravyiCoefficients::nlin = "`` is not a linear combination of Dirac or Majorana fermion operators of modes ``."

BravyiCoefficients[spec:({__?FermionQ} | {__?MajoranaQ})][expr_] :=
  BravyiCoefficients[expr, spec]

BravyiCoefficients[expr_List, spec:({__?FermionQ} | {__?MajoranaQ})] :=
  Map[BravyiCoefficients[spec], expr]

BravyiCoefficients[expr_, cc:{__?MajoranaQ}] :=
  Coefficient[expr, cc, 1] /;
  If[ theBravyiLinearQ[expr, cc], True,
    Message[BravyiCoefficients::nlin, expr, cc];
    False
  ]

BravyiCoefficients[expr_, aa:{__?FermionQ}] :=
  ToMajorana @ Coefficient[expr, Join[aa, Dagger @ aa], 1] /;
  If[ theBravyiLinearQ[expr, aa], True,
    Message[BravyiCoefficients::nlin, expr, aa];
    False
  ]


theBravyiLinearQ::usage = "theBravyiLinearQ[expr, {c1, c2, \[Ellipsis]}] returns True if expr is a linear combination of Majorana fermion operators {c1, c2, \[Ellipsis]}, and False otherwise.\ntheBravyiLinearQ[expr, {a1, a2, \[Ellipsis]}] returns True if expr is a linear combination of the creation and annihilation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}, and False otherwise."

theBravyiLinearQ[expr_List, spec_] :=
  AllTrue[expr, theBravyiLinearQ[#, spec]&]

theBravyiLinearQ[expr_, aa:{__?FermionQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[aa -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ Join[aa, Dagger @ aa], ___]
  ]
]

theBravyiLinearQ[expr_, cc:{__?MajoranaQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ cc, ___]
  ]
]
(**** </BravyiCoefficients> ****)


(**** <BravyiKernel> ****)
BravyiKernel::usage = "BravyiKernel[vec -> 1] returns {A, B} -> {1, nrm}, where A and B are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] b \[Rho] Dagger[b], where b := Sum[vec[[k]] c[k], {k, 2n}] is a linear combination of bare Majorana modes c[k].\nBravyiKernel[vec -> 2] returns {A, B} -> {-1, nrm}. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], -A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] Dagger[b]**b \[Rho] Dagger[b]**b, where b := Sum[vec[[k]] c[k], {k, 2n}] is a dressed Dirac fermion mode superposed of bare Majorana modes c[k]."

BravyiKernel[jmp:{__?patternBravyiJumpQ}] := 
  Map[BravyiKernel, jmp]


BravyiKernel[vec_?VectorQ -> 1] := Module[
  { nn = NormSquare[vec],
    re = Re[vec],
    im = Im[vec],
    id, aa, bb },
  aa = Dyad[re, im] - Dyad[im, re];
  bb = Dyad[re, re] + Dyad[im, im];
  id = One[Dimensions @ aa];
  aa = -aa*2/nn;
  bb = id - (bb*2/nn);
  {aa, bb} -> {1, 2*nn}
]


BravyiKernel[vec_?VectorQ -> 2] := Module[
  {aa, bb},
  {aa, bb} = theBravyiKernel[vec -> 2];
  nn = NormSquare[vec];
  {aa, bb} -> {-1, 2*NormSquare[vec]^2} 
  (* NOTE: Here, factor of 1/4 since BravyiOdds[v -> 2] do not put the factor of 1/2. *)
]

theBravyiKernel[vec_?VectorQ -> 2] := Module[
  { n = Length[vec]/2,
    vv = Normalize[N @ vec] / Sqrt[2],
    xx, yy, aa, bb, nn, uu },
  xx = Re[vv];
  yy = Im[vv];
  (* verify the dressed fermion mode *)
  If[ Not @ AllTrue[{xx . yy, Norm[xx] - Norm[yy]}, ZeroQ],
    Message[BravyiMeasurement::dressed, vec]
  ];
  (* The Cartan-Dieudonné theorem *)
  {aa, bb} = theBravyiKernel[1, n];
  uu = HouseholderMatrix[{xx, yy}];
  aa = uu . aa . Transpose[uu];
  bb = uu . bb . Transpose[uu];
  {aa, bb}
]

(* For measurement outcome = 1 of Dagger[a[k]]**a[k] of BARE fermion mode a[k] *)
theBravyiKernel[k_Integer, n_Integer] := {
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
(**** </BravyiKernel> ****)


(**** <BravyiOdds> ****)
BravyiOdds::usage = "BravyiOdds[spec] represents probability for the fermionic Gaussian process specified by spec. See BravyiJump for spec."

(* shortcut *)
BravyiOdds[jmp_?patternBravyiJumpQ] :=
  BravyiOdds[BravyiKernel @ jmp]

(* shortcut *)
BravyiOdds[jmp:{__?patternBravyiJumpQ}] :=
  BravyiOdds @ Map[BravyiKernel, jmp];

(* shortcut  *)
BravyiOdds[jmp_BravyiJump] := 
  BravyiOdds @ Thread[First[jmp] -> 1]

(* shortcut *)
BravyiOdds[map_BravyiMap] := BravyiOdds[First @ map]


(* sgn = +1: dissipative (linear) type L = b *)
(* sgn = -1: projective (quadratic) type L = Dagger[b] ** b *)
BravyiOdds[{aa_?ArrayQ, bb_?ArrayQ} -> {sgn:(1|-1), nrm_?NumericQ}] :=
  BravyiOdds[{aa, bb, sgn*aa} -> nrm]


(* on BravyiState *)
BravyiOdds[map:{__?patternBravyiMapQ}][in_BravyiState] := Module[
  { odds },
  odds = Through[Map[BravyiOdds, map] @ in];
  Merge[odds, Total]
]

(* on BravyiState *)
BravyiOdds[{aa_?MatrixQ, bb_?MatrixQ, dd_?MatrixQ} -> nrm_?NumericQ][
  BravyiState[{_, cvr_?MatrixQ}, rest___]
] := Module[
  { mm, id, pp },
  id = One[Dimensions @ cvr];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det @ mm], Det::luc];
  pp = Ramp @ Re[nrm * pp];
  (* NOTE 1: Ramp and Re to quickly handle numerical errors. *)
  (* NOTE 2: No factor of 1/2 even in the measurement case (sign = -1) since nrm from BravyiKernel[v -> 2] gives an additional factor of only 2 (not 4). *)
  If[ ZeroQ[pp],
    Return[BravyiState[{0, Zero @ Dimensions @ cvr}, rest] -> 0]
  ];
  new = aa + bb . cvr . Inverse[mm] . Transpose[bb];
  BravyiState[{1, new}] -> pp
]
(**** </BravyiOdds> ****)


(**** <BravyiFlop> ****)
BravyiFlop::usage = "BravyiFlop[vec] represents a single linear combination of Majorana operators."

BravyiFlop[jmp_?patternBravyiJumpQ, ___][in_BravyiState] := 
  First[BravyiOdds[jmp] @ in]
(**** </BravyiFlop> ****)


patternBravyiJumpQ::usage = "patternBravyiJumpQ[pat] returns True if pat is a pattern of the form v -> k, v is a even-dimensional vector and k = 1 or 2 for linear (dissipative) or quadratic (projective) type, respectively."

patternBravyiJumpQ[_?VectorQ -> (1|2)] = True

patternBravyiJumpQ[_] = False


patternBravyiMapQ::usage = "patternBravyiMapQ[pat] returns True if pat is a pattern of the form {a, b} -> {sgn, nrm} or {a, b, d} -> nrm, where a, b and d are 2n\[Times]2n matrices and sgn = 1 or -1 for linear (dissipative) or quadratic (projective) type, respectively."

patternBravyiMapQ[{_?MatrixQ, _?MatrixQ} -> {-1|1, _?NumericQ}] = True

patternBravyiMapQ[{_?MatrixQ, _?MatrixQ, _?MatrixQ} -> _?NumericQ] = True

patternBravyiMapQ[_] = False


(**** <BravyiJump> ****)
BravyiJump::usage = "BravyiJump[mat] represents a set of quantum jump operators, which are linear combinations of Majorana fermion operators with coefficients given by the elements of complex matrix mat."

BravyiJump::odd = "The second dimension of the input matrix `` is odd: ``."

BravyiJump /:
MakeBoxes[jmp:BravyiJump[mat_?MatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    BravyiJump, jmp, None,
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
BravyiJump /:
NambuJump[BravyiJump[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuJump[ToDirac /@ mat, more, opts] /; (* NOT ToDiract @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[BravyiJump::odd, ArrayShort @ mat, Dimensions @ mat];
    False
]

(* conversion *)
BravyiJump /:
ToDirac[jmp_BravyiJump] := NambuJump[jmp]

(* canonicalization *)
BravyiJump[mat_?MatrixQ, opts___?OptionQ] :=
  BravyiJump[SparseArray @ mat, opts] /; Head[mat] =!= SparseArray
(* NOTE: In many physical cases, the linear combinations are rather simple. *)


BravyiJump /:
Normalize[BravyiJump[mat_?MatrixQ, rest___], ___] := Module[
  { new = Map[Normalize, mat]/Sqrt[2] },
  (* NOTE: Notice the factor of 1/Sqrt[2]. *)
  BravyiJump[new, rest]
]

BravyiJump /:
MatrixForm[BravyiJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

BravyiJump /:
ArrayShort[BravyiJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


BravyiJump /:
Dagger @ BravyiJump[mat_?MatrixQ, rest___] :=
  BravyiJump[BravyiConjugateReverse @ mat, rest]

BravyiJump /:
Plus[BravyiJump[a_, any___], BravyiJump[b_, other___]] :=
  BravyiJump[a + b, any, other]

BravyiJump /:
Times[z_, BravyiJump[mm_, rest___]] :=
  BravyiJump[z * mm, rest]


BravyiJump /:
Matrix[jmp:BravyiJump[mat_?MatrixQ, ___]] := Module[
  { xy = theJordanWignerMajorana[FermionCount @ jmp] },
  Identity /@ Dot[mat, xy]
  (* NOTE: Identoity /@ ... to put the results into a list of matrices rather than a single large SparseArray. *)
]

BravyiJump /:
Matrix[jmp_BravyiJump, ss:{___?SpeciesQ}] := With[
  { mm = Matrix[jmp],
    cc = Select[ss, FermionQ] },
  Map[MatrixEmbed[#, cc, ss]&, mm]
]


BravyiJump /: 
NonCommutativeQ[_BravyiJump] = True

BravyiJump /:
MultiplyKind[_BravyiJump] = Fermion

BravyiJump /:
Multiply[pre___, jmp_BravyiJump, ws_BravyiState] := Multiply[pre, jmp @ ws]

BravyiJump[mat_?MatrixQ, ___][in_BravyiState] := (* null state *)
  BravyiState[{0, Zero[2*FermionCount[in]*{1, 1}]}, Rest @ in] /;
  BravyiNullQ[in]

BravyiJump[mat_?MatrixQ, ___][in_BravyiState] := BravyiMap[BravyiJump @ mat][in]
(**** </BravyiJump> ****)


RandomBravyiJump::usage = "RandomBravyiJump[{k_Integer, n_Integer}] returns BravyiJump consisting of k linear combinations of 2n Majorana operators."

RandomBravyiJump[{k_Integer, n_Integer}, opts___?OptionQ] :=
  BravyiJump[RandomMatrix @ {k, 2n}, opts]

RandomBravyiJump[n_Integer, opts___?OptionQ] :=
  RandomBravyiJump[{RandomInteger @ {1, n}, n}, opts]


(**** <BravyiMeasurement> ****)
BravyiMeasurement::usage = "BravyiMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nBravyiMeasurement[{k1, k2, \[Ellipsis]}] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nBravyiMeasurement[mat] represents a sequence of measurement on the dressed Dirac fermion modes b[i] := Sum[m[[i,j]] c[j], {j, 2n}] expressed in terms of Majorana fermion modes c[k].\nBravyiMeasurement[spec][ws] simulates the measurement on Bravyi state ws, and returns the post-measurement state."

BravyiMeasurement::odd = "The second dimension of the input matrix `` is odd: ``."

BravyiMeasurement::dressed = "A vector of coefficients `` cannot describe a proper dressed Dirac fermion mode."


BravyiMeasurement /:
MakeBoxes[msr:BravyiMeasurement[mat_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    BravyiMeasurement, msr, None,
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
BravyiMeasurement[k_Integer, n_Integer, rest___] :=
  BravyiMeasurement[{k}, n, rest]

(* canonicalization *)
(* NOTE: kk = {} may happen, e.g., in RandomBravyiCircuit. *)
BravyiMeasurement[kk:{___Integer}, n_Integer, rest___] := With[
  { mm = One[{n, 2*n}] },
  BravyiMeasurement @ NambuMeasurement @ mm[[kk]]
]

(* canonicalization *)
BravyiMeasurement[mat_?MatrixQ, rest___] :=
  BravyiMeasurement[SparseArray @ mat, rest] /;
  Head[mat] =!= SparseArray

BravyiMeasurement /:
Matrix[BravyiMeasurement[mat_?MatrixQ, ___], rest___] := Module[
  { ops = Matrix[BravyiJump @ mat, rest] },
  MapThread[Dot, {ConjugateTranspose /@ ops, ops}]
  (* NOTE: Returned are UNNORMALIZED projection operators. *)
]

BravyiMeasurement /:
Normalize[BravyiMeasurement[mat_?MatrixQ, rest___], ___] := Module[
  { new = Map[Normalize, mat]/Sqrt[2] },
  (* NOTE: Notice the factor of 1/Sqrt[2]. *)
  BravyiMeasurement[new, rest]
]

BravyiMeasurement /:
Dagger @ BravyiMeasurement[mat_?MatrixQ, rest___] :=
  BravyiMeasurement[BravyiConjugateReverse @ mat, rest]

BravyiMeasurement /:
Times[z_, BravyiMeasurement[mm_, rest___]] :=
  BravyiMeasurement[z * mm, rest]


BravyiMeasurement /:
MatrixForm[BravyiMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

BravyiMeasurement /:
ArrayShort[BravyiMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


BravyiMeasurement /:
NonCommutativeQ[_BravyiMeasurement] = True

BravyiMeasurement /:
MultiplyKind[_BravyiMeasurement] = Fermion

BravyiMeasurement /:
Multiply[pre___, msr_BravyiMeasurement, ws_BravyiState] := Multiply[pre, msr @ ws]


(* NOTE: This may happen, e.g., in RandomBravyiCircuit. *)
BravyiMeasurement[{}, ___][in_BravyiState] = in

(* Dagger[d] ** d, where d := Sum[v[[j]] c[j], {j, 2n}] and c[k] are bare Majorana modes. *)
BravyiMeasurement[mat_?MatrixQ, ___][in_BravyiState] :=
  Fold[theBravyiMeasurement, in, Identity /@ mat]

theBravyiMeasurement[in:BravyiState[{_, cvr_?MatrixQ}, rest___], vec_?VectorQ] := Module[
  { vv = Normalize[N @ vec]/Sqrt[2], (* just in case *)
    aa, bb, id, mm, pp, new },
  {aa, bb} = theBravyiKernel[vv -> 2];
  id = One[Dimensions @ cvr];
  mm = id - aa. cvr; (* D = -A *)
  pp = Quiet[Sqrt[Det @ mm]/2, {Det::luc}];
  If[ RandomReal[] < Re[pp], (* Re[...] to quickly handle numerical errors. *)
    $MeasurementOut[vec] = 1,
    $MeasurementOut[vec] = 0;
    aa *= -1;
    mm = id - aa . cvr (* D = -A *)
  ];
  new = Quiet[aa + bb . cvr . Inverse[mm] . bb, {Inverse::luc}];
  BravyiState[{1, new}, rest]
]


(* conversion *)
BravyiMeasurement /:
ToDirac[msr_BravyiMeasurement] := NambuMeasurement[msr]

(* conversion *)
BravyiMeasurement /:
NambuMeasurement[BravyiMeasurement[mat:({}|_?MatrixQ), opts___?OptionQ], more___?OptionQ] :=
  NambuMeasurement[ToDirac /@ mat, more, opts]   (* NOT ToDirac @ mat. *)


(* NOTE: This happens when no measurement is performed such as in RandomBravyiCircuit. *)
FermionCount[BravyiMeasurement[{}, ___?OptionQ]] = 0

FermionCount[BravyiMeasurement[mat_?MatrixQ, ___?OptionQ]] := 
  Last[Dimensions @ mat]/2

Readout[BravyiMeasurement[m_?MatrixQ, ___]] := 
  Readout[First @ m] /; Length[m] == 1

Readout[BravyiMeasurement[m_?MatrixQ, ___]] := 
  Map[Readout, m]


theFermionModes::usage = "theFermionModes[msr] returns the list of Dirac fermion modes being probed by BravyiMeasurement msr. Used in Graphics[BravyiCircuit[...], ...]."

theFermionModes[BravyiMeasurement[{}, ___]] = {}

theFermionModes[msr:BravyiMeasurement[_?MatrixQ, ___]] := Module[
  { mat = First[NambuMeasurement @ msr] },
  mat = First @ PartitionInto[mat, {1, 2}];
  mat = Map[ZeroQ, mat, {3}];
  Union @ Flatten @ Map[Position[#, False]&, mat, {2}]
]
(**** </BravyiMeasurement> ****)


RandomBravyiMeasurement::usage = "RandomBravyiMeasurement[{k, n}] randomly generates a BravyiMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomBravyiMeasurement[n] randomly selects k from {1,2,\[Ellipsis],n}."

RandomBravyiMeasurement[{k_Integer, n_Integer}] :=
  BravyiMeasurement @ RandomNambuMeasurement[{k, n}]

RandomBravyiMeasurement[n_Integer] :=
  BravyiMeasurement @ RandomNambuMeasurement[n]


(**** <BravyiMap> ****)
BravyiMap::usage = "BravyiMap[mat] or BravyiMap[mat, True] represents a projective quantum operation \[Rho] \[RightTeeArrow] Sum[p[i]**\[Rho]**p[i], {i, m}] + Sum[(1-p[i])**\[Rho]**(1-p[i]), {j, m}], where m is the number of rows in mat, p[i]:=Dagger[b[i]]**b[i] are projection operators, and b[i]:=Sum[mat[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of n bare Majorana fermion modes c[j].\nBravyiMap[mat, False] represents \[Rho] \[RightTeeArrow] Sum[p[i]**\[Rho]**p[i], {i, m}]."

BravyiMap::null = "The quantum operation returns the null state."

BravyiMap /:
MakeBoxes[map:BravyiMap[krn:{__?patternBravyiMapQ}], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    BravyiMap, msr, None,
    { BoxForm`SummaryItem @ { "Bare modes: ", Length[ krn[[1, 1, 1]] ]/2 },
      BoxForm`SummaryItem @ { "Kraus elements: ", Length[krn] }
    },
    {},
    fmt,
    "Interpretable" -> Automatic
  ]

(* conversion *)
BravyiMap[jmp_BravyiJump, ___] :=
  BravyiMap @ BravyiKernel @ Thread[First[jmp] -> 1];

(* conversion *)
BravyiMap[msr_BravyiMeasurement] := BravyiMap[msr, False]

BravyiMap[msr_BravyiMeasurement, False] :=
  BravyiMap @ BravyiKernel @ Thread[First[msr] -> 2]

BravyiMap[msr_BravyiMeasurement, True] :=
  BravyiMap @ BravyiKernel @ Riffle[
    Thread[Conjugate[First @ msr] -> 2], (* outcome: 0*)
    Thread[First[msr] -> 2] (* outcome: 1 *)
  ]

(* On BravyiState *)
BravyiMap[spec_, flag_][BravyiState[{_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  BravyiState[{1, BravyiMap[spec, flag] @ cvr}, rest]


BravyiMap[map:{__?patternBravyiMapQ}][in_BravyiState] := Module[
  { odds = BravyiOdds[map][in] },
  If[ ArrayZeroQ[Values @ odds], 
    Message[BravyiMap::null];
    Return[First @ Keys @ odds]
  ];
  RandomChoice[Values[odds] -> Keys[odds]]
]
(**** </BravyiMap> ****)


(**** <BravyiGreen> ****)
BravyiGreen::usage = "BravyiGreen[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to BravyiState ws.\nBravyiGreen[ns, {k1, k2, \[Ellipsis]}] returns NambuGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NambuState ns.\nBravyiGreen[in] is equivalent to BravyiGreen[in, Range[n]], where n is the number of fermion modes for which input Bravyi or Nambu state in is defined for.\nBravyiGreen[data] or BravyiGreen[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Bravyi or BdG states.\nBravyiGreen[{k1, k2, \[Ellipsis]}] represents an operator form of BravyiGreen to be applied to Bravyi or Nambu state."

(* shortcut *)
BravyiGreen[bc_BCSState] := NambuGreen[bc]

(* shortcut *)
BravyiGreen[ws_BravyiState] := NambuGreen[ws]

(* canonical form for BdG modelsl *)
BravyiGreen[BravyiState[{_, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  {grn, anm},
  {grn, anm} = First @ NambuGreen[BravyiCovariance @ cvr];
  NambuGreen @ {grn[[kk, kk]], anm[[kk, kk]]}
]

(* for large data *)
BravyiGreen[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := 
  arrayMap[BravyiGreen[#, kk]&, data] /;
  ArrayQ[data, _, MatchQ[#, _BravyiState]&]
(**** </BravyiGreen> ****)


(**** <BravyiOccupation> ****)
BravyiOccupation::usage = "BravyiOccupation[in, {k1, k2, \[Ellipsis]}] returns a list of the expectation values of occupation on fermion modes in {k1, k2, \[Ellipsis]} with respect to BravyiState or NambuState in.\nBravyiOccupation[in] is equivalent to BravyiOccupation[in, Range[n]], where n is the number of fermion modes for which input Bravyi or Nambu state in is defined for.\nBravyiOccupation[data] or BravyiOccupation[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating the occupation for an (typically large) array data of Bravyi or BdG states.\nBravyiOccupation[{k1, k2, \[Ellipsis]}] represents an operator form of BravyiOccupation to be applied to Bravyi or BdG state."

(* operator form *)
BravyiOccupation[kk:{___Integer}][in_] :=
  BravyiOccupation[in, kk]

(* shortcut *)
BravyiOccupation[in_BravyiState] :=
  BravyiOccupation[in, Range @ FermionCount @ in]

(* canonical form for normal models *)
BravyiOccupation[BravyiState[{_?NumericQ, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  { grn = NambuGreen[BravyiCovariance @ cvr] },
  grn = 1 - Diagonal[ grn[[1, 1]] ];
  grn[[kk]]
]


(* for large data *)
BravyiOccupation[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = N @ Whole @ Dimensions[data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; BravyiOccupation[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _BravyiState]&]
(**** </BravyiOccupation> ****)


(**** <BravyiPurity> ****)
BravyiPurity::usage = "BravyiPurity[ws] returns the purity of Bravyi state ws."

BravyiPurity[ws_BravyiState] := Module[
  { val = Eigenvalues[I*ws[[1, 2]]] },
  Power[2, -FermionCount[ws]] * Sqrt[Whole[1 + val^2]]
]
(**** </BravyiPurity> ****)


(**** <BravyiDensityMatrix> ****)
BravyiDensityMatrix::usage = "BravyiDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function grn associated with a fermionic Gaussian state.\nBravyiDensityMatrix[ws] returns the density matrix corresponding to Bravyi state ws."

BravyiDensityMatrix::num = "Only numerical matrices are allowed."

(* canonical form for normal models *)
BravyiDensityMatrix[grn_?MatrixQ] := WickDensityMatrix[grn]

(* essentially normal models *)
BravyiDensityMatrix[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  BravyiDensityMatrix[grn] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
BravyiDensityMatrix[grn_NambuGreen] := Module[
  { n = FermionCount[grn],
    cc, gg, uu, id },  
  cc = theJordanWignerNambu[n];
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
  Message[BravyiDensityMatrix::num];
  False
]

(* canonicalization *)
BravyiDensityMatrix[grn_?NambuMatrixQ] := BravyiDensityMatrix[NambuGreen @ grn]

BravyiDensityMatrix[cvr_BravyiCovariance] :=
  BravyiDensityMatrix[NambuGreen @ cvr]

(* shortcut for BdG models *)
BravyiDensityMatrix[ws_BravyiState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
] /; BravyiPureQ[ws]
(**** </BravyiDensityMatrix> ****)


(**** <BravyiCircuit> ****)
BravyiCircuit::usage = "BravyiCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit consisting of BdG gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes."

BravyiCircuit /:
MakeBoxes[wc:BravyiCircuit[gg_List, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BravyiCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", FermionCount @ wc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", Short @ gg }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

BravyiCircuit /: 
NonCommutativeQ[_BravyiCircuit] = True

BravyiCircuit /:
MultiplyKind[_BravyiCircuit] = Fermion

BravyiCircuit /:
Multiply[pre___, wc_BravyiCircuit, in_BravyiState] :=
  Multiply[pre, wc @ in]

BravyiCircuit[gg_List, ___][in_BravyiState] :=
  Fold[#2[#1]&, in, gg]

BravyiCircuit /:
Dagger @ BravyiCircuit[gg_List, rest___] :=
  BravyiCircuit[Reverse @ Dagger @ gg, rest]

BravyiCircuit /:
Show[wc_BravyiCircuit, rest___] := Graphics[wc, rest]

BravyiCircuit /:
Graphics[wc:BravyiCircuit[gg_List], more___?OptionQ] := Module[
  { c },
  Let[Fermion, c];
  Graphics[wc, c, more]
]

BravyiCircuit /:
Graphics[wc:BravyiCircuit[gg_List, opts___?OptionQ], c_Symbol?FermionQ, more___?OptionQ] := Module[
  { n = FermionCount[wc],
    cc, qc },
  cc = c[Range @ n];
  qc = gg /. {
    BravyiCircuit[{}] -> "Spacer",
    ws_BravyiCircuit :> Graphics[ws],
    ws_BravyiState :> ExpressionFor[ws, cc],
    BravyiMeasurement[{}, ___] -> "Spacer",
    ws_BravyiMeasurement :> Map[Gate[{c[#]}, "Shape" -> "Measurement"]&, theFermionModes @ ws],
    BravyiUnitary[_?MatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    BravyiUnitary[_?MatrixQ, any___?OptionQ] :> Gate[cc, any],
    BravyiUnitary[_?MatrixQ, _, any___?OptionQ] :> Gate[cc, any]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]
(**** </BravyiCircuit> ****)


(**** <RandomBravyiCircuit> ****)
RandomBravyiCircuit::usage = "RandomBravyiCircuit[{uni, p}, dep] generate a random quantum circuit on non-interacting fermion modes, where layers of unitary gate uni (either BravyiUnitary[\[Ellipsis]] or NambuUnitary[\[Ellipsis]]) alternate with layers of measurements (BravyiMeasurement[\[Ellipsis]]) on fermion modes selected randomly with probability p to form an overall depth dep.\nRandomBravyiCircuit[{ham, pdf, p}, k] unitary layers of random unitary gate uni=Exp[-I ham \[Tau]] with single-particle Hamiltonian ham (either n\[Times]n Hermitian matrix or NambuHermitian[\[Ellipsis]]) and the random evolution time \[Tau] distributed according to the probability distribution function pdf.\nRandomBravyiCircuit[{ham, p}, dep] assumes that the evolution time is uniformly distributed over the interval [0,2\[Pi] n/max], where max is the maximum of the absolute values of the entries of ham.\nRandomBravyiCircuit[ham, dep] generates a circuit for n fermion modes where each unitary layer corresponds to time evolution U=exp[-I ham \[Tau]] with the evolution time \[Tau] distributed by P(\[Tau])\[Proportional]exp[-n \[Tau]] and each measurement layer measures a fermion mode with probability p=1/n."

(* canonicalization *)
RandomBravyiCircuit[{uu_NambuUnitary, p_?NumericQ}, k_Integer] :=
  RandomBravyiCircuit[{BravyiUnitary @ uu, p}, k]

(* fixed interaction time *)
RandomBravyiCircuit[{uu_BravyiUnitary, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[uu],
      mm },
    mm = RandomPick[Range @ n, p, k];
    BravyiCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[BravyiMeasurement[#, n]&, mm]
    ]
  ]

(* canonicalization *)
RandomBravyiCircuit[{ham_NambuHermitian, spec__}, k_Integer] :=
  RandomBravyiCircuit[{BravyiHermitian @ ham, spec}, k]

(* arbitrary distribution of evolution time *)
RandomBravyiCircuit[{ham_BravyiHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = Map[BravyiUnitary[MatrixExp[hh*#]]&, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[BravyiMeasurement[#, n]&, mm];
    BravyiCircuit @ Riffle[uu, mm]
  ]

(* uniform distribution of evolution time *)
RandomBravyiCircuit[{ham_BravyiHermitian, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      max, pdf },
    max = Max[Abs @ First @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    RandomBravyiCircuit[{ham, pdf, p}, k]
  ]

(* canonicalization *)
RandomBravyiCircuit[ham_NambuHermitian, k_Integer] :=
  RandomBravyiCircuit[BravyiHermitian[ham], k]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
RandomBravyiCircuit[ham_BravyiHermitian, k_Integer] := Module[
    { n = FermionCount[ham] },
    RandomBravyiCircuit[{ham, ExponentialDistribution[n], 1./n}, k]
  ]
(**** </RandomBravyiCircuit> ****)


(**** <RandomBravyiCircuitSimulate> ****)
RandomBravyiCircuitSimulate::usage = "RandomBravyiCircuitSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomBravyiCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

Options[RandomBravyiCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RBC"
}

$RandomBravyiCircuitPatterns = Alternatives[
  {_BravyiUnitary, _?NumericQ}, 
  {_NambuUnitary, _?NumericQ},
  {_BravyiHermitian, _, _?NumericQ},
  {_BravyiHermitian, _?NumericQ},
  {_NambuHermitian, _, _?NumericQ},
  {_NambuHermitian, _?NumericQ},
  _BravyiHermitian,
  _NambuHermitian
];

RandomBravyiCircuitSimulate[in_, spec_, depth_Integer, opts___?OptionQ] := 
  RandomBravyiCircuitSimulate[in, spec, {depth, 2}, opts]

RandomBravyiCircuitSimulate[
  in_BravyiState,
  spec:$RandomBravyiCircuitPatterns,
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
    qc = RandomBravyiCircuit[spec, depth];
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
    more = Join[{opts}, Options @ RandomBravyiCircuitSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
]
(**** </RandomBravyiCircuitSimulate> ****)


theJordanWignerMajorana::usage = "theJordanWignerMajorana[n] returns a list of matrices representing 2n Majorana modes, taking into account the Wigner-Jordan transformation."

theJordanWignerMajorana[n_Integer] := Module[
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


(**** <BravyiScramblingCircuit> ****)
BravyiScramblingCircuit::usage = "BravyiScramblingCircuit[op, spec, dep] generates the main part of a Bravyi scrambling circuit."

(* 1 - 2*Dagger[a[k]]**a[k] *)
theBravyiZ[k_Integer, n_Integer] := BravyiUnitary[
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
theBravyiX[k_Integer, n_Integer] := BravyiUnitary[
  SparseArray[
    { {k, k} -> 1,
      {i_, i_} -> -1,
      {_, _} -> 0
    },
    {2n, 2n}
  ],
  "Label" -> Subscript["X", k]
]


BravyiScramblingCircuit[a_Integer, 
  spec:$RandomBravyiCircuitPatterns, t_Integer] := Module[
    { n = spec },
    If[ListQ @ spec, n = First @ spec];
    n = FermionCount[n];
    BravyiScramblingCircuit[theBravyiX[a, n], spec, t]
  ]


(* canonicalization *)
BravyiScramblingCircuit[op_, {uu_NambuUnitary, p_?NumericQ}, k_Integer] :=
  BravyiScramblingCircuit[op, {BravyiUnitary @ uu, p}, k]

(* fixed interaction time *)
BravyiScramblingCircuit[op_, {uu_BravyiUnitary, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[uu],
      vv, ma, mb },
    vv = ConstantArray[uu, k];
    ma = If[ ZeroQ @ p, Nothing, 
      Table[BravyiMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    mb = If[ ZeroQ @ p, Nothing, 
      Table[BravyiMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    BravyiCircuit @ Join[
      Riffle[vv, ma], {op},
      Riffle[Dagger @ vv, mb]
    ]
  ]

(* canonicalization *)
BravyiScramblingCircuit[op_, {ham_NambuHermitian, spec__}, k_Integer] :=
  BravyiScramblingCircuit[{BravyiHermitian @ ham, spec}, k]

(* arbitrary distribution of evolution time *)
BravyiScramblingCircuit[op_, {ham_BravyiHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      tt, uu, dg, ma, mb },
    tt = RandomVariate[pdf, k];
    uu = Map[BravyiUnitary[MatrixExp[hh*#]]&, tt];
    dg = Reverse[Dagger @ uu];
    ma = If[ ZeroQ @ p, Nothing, 
      Table[BravyiMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    mb = If[ ZeroQ @ p, Nothing, 
      Table[BravyiMeasurement[RandomPick[Range @ n, p], n], k]
    ];
    BravyiCircuit @ Join[
      Riffle[uu, ma], {op},
      Riffle[dg, mb]
    ]
  ]

(* uniform distribution of evolution time *)
BravyiScramblingCircuit[op_, {ham_BravyiHermitian, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      max, pdf },
    max = Max[Abs @ First @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    BravyiScramblingCircuit[op, {ham, pdf, p}, k]
  ]

(* canonicalization *)
BravyiScramblingCircuit[op_, ham_NambuHermitian, k_Integer] :=
  BravyiScramblingCircuit[op, BravyiHermitian[ham], k]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
BravyiScramblingCircuit[op_, ham_BravyiHermitian, k_Integer] := Module[
    { n = FermionCount[ham] },
    BravyiScramblingCircuit[op, {ham, ExponentialDistribution[n], 1./n}, k]
  ]
(**** </BravyiScramblingCircuit> ****)


(**** <BravyiScramblingSimulate> ****)
BravyiScramblingSimulate::usage = "BravyiScramblingSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomBravyiCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

Options[BravyiScramblingSimulate] = {
  "Samples" -> {10, 3}
}

BravyiScramblingSimulate[in_, a_Integer, rest__] :=
  BravyiScramblingSimulate[in, {a, 1}, rest]

BravyiScramblingSimulate[in_, {a_Integer, b_Integer}, 
  spec:$RandomBravyiCircuitPatterns, rest__] := Module[
    { n = spec },
    If[ListQ @ spec, n = First @ spec];
    n = FermionCount[n];
    BravyiScramblingSimulate[in, {theBravyiX[a, n], theBravyiZ[b, n]}, spec, rest]
  ]

BravyiScramblingSimulate[in_, ua_BravyiUnitary, rest__] :=
  BravyiScramblingSimulate[in, {ua, theBravyiZ[1, FermionCount @ ua]}, rest]

BravyiScramblingSimulate[
  in_BravyiState,
  {ua_BravyiUnitary, ub_BravyiUnitary},
  spec:$RandomBravyiCircuitPatterns,
  depth_Integer,
  OptionsPattern[]
] := 
Module[
  { qc, n, m },
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  Mean @ Flatten @ Table[
    qc = BravyiScramblingCircuit[ua, spec, depth];
    Table[theBravyiOTOC[in, ub, qc], m],
    n
  ]
]

theBravyiOTOC[in_, ub_, qc_BravyiCircuit] := Module[
  { va, vb },
  va = Fold[Construct[#2, #1]&, in, First @ qc];
  vb = Join[{ub}, First @ qc, Dagger @ {ub}];
  vb = Fold[Construct[#2, #1]&, in, vb];
  Sqrt @ BravyiInner[va, vb]
]
(**** </BravyiScramblingSimulate> ****)


(**** <BravyiNonunitary> ****)
BravyiNonunitary::usage = "BravyiNonunitary[{ham, dmp, gmm}] represents a non-unitary time evolution operator Exp[-gmm/2]*MatrixExp[-I*(ham - I*dmp)] governed by the non-Hermitian Hamiltonian ham - I*dmp. The 2n\[Times]2n antisymmetic matrices ham and dmp refer to the coefficients matrices in the bilinear combination of Majorana operators (not Dirac fermion operators).\nIf ham and dmp are given in the NambuHermitian form, they are automatically converted to the coefficients matrices of Majorana operators."

BravyiNonunitary::icmp = "BravyiNonunitary for `` fermion modes cannot act on BravyiState for `` modes."

BravyiNonunitary /:
MakeBoxes[op:BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, rest___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BravyiNonunitary, op, None,
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
BravyiNonunitary[{ham_NambuHermitian, more__}, rest___] :=
  BravyiNonunitary[{First @ BravyiHermitian @ ham, more}, rest]
(* CONVENTION: (1/2) (a^\dag, a) H (a, a^\dag) = (i/4) c A c. *)

(* canonicalization *)
BravyiNonunitary[{ham_, dmp_NambuHermitian, gmm___}, rest___] :=
  BravyiNonunitary[{ham, First @ BravyiHermitian @ dmp, gmm}, rest]
(* CONVENTION: (1/2) (a^\dag, a) H (a, a^\dag) = (i/4) c A c. *)

(* canonicalization *)
BravyiNonunitary[{ham:BravyiHermitian[_?MatrixQ, ___], more__}, rest___] :=
  BravyiNonunitary[{First @ ham, more}, rest]

(* canonicalization *)
BravyiNonunitary[{ham_, dmp_BravyiHermitian, gmm___}, rest___] :=
  BravyiNonunitary[{ham, First @ dmp, gmm}, rest]

(* conversion *)
BravyiNonunitary[{ham_?MatrixQ, BravyiMeasurement[kk:{__Integer}, ___]}, rest___] := Module[
  { msr = One[Dimensions @ ham] },
  msr = BravyiMeasurement[NambuMeasurement @ msr[[kk]]];
  BravyiNonunitary[{ham, msr}, rest]
]

(* conversion *)
BravyiNonunitary[{ham_?MatrixQ, jmp:(_BravyiJump|_BravyiMeasurement)}, rest___] := Module[
  {dmp, gmm},
  {dmp, gmm} = BravyiDamping[jmp];
  BravyiNonunitary[{ham, dmp, gmm}, rest]
]

(* shortcut *)
BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ}, rest___] :=
  BravyiNonunitary[{ham, dmp, 0}, rest]

BravyiNonunitary /:
MatrixForm @ BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_}, rest___] :=
  MatrixForm /@ {ham, dmp}

BravyiNonunitary /:
ArrayShort @ BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_}, rest___] :=
  ArrayShort /@ {ham, dmp}

BravyiNonunitary /:
Dagger @ BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_}, rest___] :=
  BravyiNonunitary[{-ham, dmp, gmm}, rest]
(* NOTE: gmm is supposed to be real. *)

BravyiNonunitary /:
Matrix[op:BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, ___]] := Module[
  { n = FermionCount[op],
    non = ham - I*dmp,
    mat, wjm },
  wjm = theJordanWignerMajorana[n];
  mat = Dot[Transpose[wjm, {3, 1, 2}], non, wjm] * I/4;
  mat = TensorContract[mat, {{2, 3}}];
  mat -= I*gmm*One[Power[2, n]];
  SparseArray @ MatrixExp[-I*mat]
]

BravyiNonunitary /:
Matrix[op:BravyiNonunitary[{_?MatrixQ, _?MatrixQ, _?NumericQ}, ___], ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ op, Select[ss, FermionQ], ss]


BravyiNonunitary /:
NonCommutativeQ[_BravyiNonunitary] = True

BravyiNonunitary /:
MultiplyKind[_BravyiNonunitary] = Fermion

BravyiNonunitary /:
Multiply[pre___, opr_BravyiNonunitary, ws_BravyiState] := Multiply[pre, opr[ws]]

BravyiNonunitary /:
Multiply[pre___, opr_BravyiNonunitary, fs_Ket] := Multiply[pre, opr[BravyiState @ fs]]


BravyiNonunitary[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, rest___][in_BravyiState] :=
  nonUnitaryEvolution[BravyiNonunitary @ {ham, dmp, gmm}, in, {1, 0.01}]

(* Based on the Runge-Kutta method *)
nonUnitaryEvolution[non_BravyiNonunitary, in_BravyiState, {t_?NumericQ, dt_?NumericQ}] := 
  Re @ Nest[nonUnitaryStep[non, dt], in, Round[t/dt]]

(* Single Runge-Kutta step *)
nonUnitaryStep[{ham_?MatrixQ, dmp_?MatrixQ, gmm_?NumericQ}, dt_?NumericQ][
  BravyiState[{nrm_?NumericQ, cvr_?MatrixQ}, rest___]
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
  BravyiState[{prb, new}, rest]
]

(* canonicalization *)
nonUnitaryStep[non_BravyiNonunitary, dt_?NumericQ] :=
  nonUnitaryStep[First @ non, dt]
(**** </BravyiNonunitary> ****)


RandomBravyiNonunitary::usage = "RandomBravyiNonunitary[n] randomly constructs a BravyiNonunitary operator on n fermion modes."

RandomBravyiNonunitary[n_Integer, opts___?OptionQ] :=
  BravyiNonunitary[Re @ {RandomAntisymmetric[2n], RandomAntisymmetric[2n], 0}, opts]


(**** <BravyiDamping> ****)
BravyiDamping::usage = "BravyiDamping[jmp] returns a pair {dmp, gmm} of the quadratic kernel dmp and remaining constant term gmm of the effective damping operator that corresponds to to quantum jump operators jmp in the BravyiJump or BravyiMeasurement form."

BravyiDamping[BravyiJump[jmp_?MatrixQ, ___]] := With[
  { mat = ConjugateTranspose[jmp] . jmp },
  { BravyiHermitian @ Re[ -I*(mat - Transpose[mat]) ],
    Re @ Tr[mat]/2 }
]

BravyiDamping[BravyiMeasurement[msr_?MatrixQ, ___]] := Module[
  { dig, mat },
  dig = 2*Map[NormSquare, msr];
  mat = Dot[ConjugateTranspose @ msr, dig*msr];
  { BravyiHermitian @ Re[ -I*(mat - Transpose[mat]) ],
    Re @ Tr[mat]/2 }
]
(**** </BravyiDamping> ****)


(**** <BravyiSimulate> ****)
$BravyiMinorSteps::usage = "$BravyiMinorSteps is a parameter that controls the behavior of BravyiSimulate by setting the number of minor steps for the non-unitary gate to make between major steps of update the quantum state."

$BravyiMinorSteps = 10;

BravyiSimulate::usage = "BravyiSimulate[in, ham, jmp, {\[Tau], dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian ham in the BravyiHermitian form and the quantum jump operators are specified by jmp in the BravyiJump form. The simulation starts from the initial state IN in the BravyiState at time 0 and runs to time \[Tau] in steps of size dt."

BravyiSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

Options[BravyiSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NBS"
}

BravyiSimulate[in_BravyiState, ham_?MatrixQ, rest__] :=
  BravyiSimulate[in, BravyiHermitian @ ham, rest]

BravyiSimulate[in_BravyiState, ham_NambuHermitian, rest__] :=
  BravyiSimulate[in, BravyiHermitian @ ham, rest]

BravyiSimulate[in_BravyiState, ham_BravyiHermitian, jmp_NambuJump, rest__] :=
  BravyiSimulate[in, ham, BravyiJump @ jmp, rest]

BravyiSimulate[in_BravyiState, ham_BravyiHermitian, msr_NambuMeasurement, rest__] :=
  BravyiSimulate[in, ham, BravyiMeasurement @ msr, rest]

BravyiSimulate[in_, ham_, jmp_, {tau_?NumericQ, dt_?NumericQ}, opts___?OptionQ] :=
  BravyiSimulate[in, ham, jmp, {tau, dt, All}, opts]

BravyiSimulate[
  in_BravyiState, 
  ham_BravyiHermitian, 
  jmp:(_BravyiJump | _BravyiMeasurement),
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)}, 
  opts:OptionsPattern[]
] := Module[
  { ns = OptionValue["Samples"],
    progress = 0,
    non, map, data, more },
    
  non = BravyiNonunitary[{ham, jmp}];
  map = BravyiMap[jmp, False];

  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[ns];
    theBravyiSimulate[in, non, map, {tau, dt}][[1;;All;;ds]],
    {k, ns}
  ];

  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ BravyiSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
] /; If[ MatrixQ[First @ ham, NumericQ], True,
  Message[BravyiSimulate::ham, ham];
  False
]

theBravyiSimulate[in_BravyiState, non_BravyiNonunitary, map_BravyiMap, {tau_, dt_}] :=
  Module[
    { t = dt,
      res = {in},
      new = in,
      out, prb },
    While[ t <= tau,
      prb = RandomReal[];
      (* non-unitary evolution *)
      out = nonUnitaryEvolution[non, new, {dt, dt/$BravyiMinorSteps}];
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
(**** </BravyiSimulate> ****)


(**** <BravyiMonitor> ****)
BravyiMonitor::usage = "BravyiMonitor[in, ham, msr, {nt, dt}] solves the problem of continuous monitoring of a non-interacting many-fermion system by using the Monte Carlo simulation method. The model is specified by the single-particle Hamiltonian ham in the BravyiHermitian form, and the dressed fermion modes the occupation numbers of which to be monitored are specified by measurement msr in the BravyiMeasurement form. The simulation starts from the initial state IN in the BravyiState form at time 0 and goes nt time steps of size dt."

BravyiMonitor::mat = "The matrix in the first argument of BravyiMonitor must be a real anti-symmetric matrix."

BravyiMonitor::num = "The Hamiltonian matrix `` needs to be numeric."

Options[BravyiMonitor] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "BM"
}

BravyiMonitor[in_BravyiState, ham_?MatrixQ, rest___] :=
  BravyiMonitor[in, BravyiHermitian @ ham, rest] /;
  If[ BravyiHermitianQ[ham], True,
    Message[BravyiNonitor::mat]; False
  ]

BravyiMonitor[in_BravyiState, ham_?NambuMatrixQ, rest___] :=
  BravyiMonitor[in, BravyiHermitian @ NambuHermitian @ ham, rest]

BravyiMonitor[in_BravyiState, ham_NambuHermitian, rest___] :=
  BravyiMonitor[in, BravyiHermitian @ ham, rest]

BravyiMonitor[in_BravyiState, ham_BravyiHermitian, msr_NambuMeasurement, rest___] :=
  BravyiMonitor[in, ham, BravyiMeasurement @ msr, rest]

BravyiMonitor[
  in_BravyiState,
  ham_BravyiHermitian,
  spec:{_?NumericQ, _?NumericQ, ___},
  opts___?OptionQ
] := Module[
  { n = FermionCount[in],
    map },
  map = BravyiMap[BravyiMapKernel[2, Range @ n, n], True];
  BravyiMonitor[in, ham, map, spec, opts]
]

BravyiMonitor[
  in_BravyiState,
  ham_BravyiHermitian,
  msr_BravyiMeasurement,
  spec:{_?NumericQ, _?NumericQ, ___},
  opts___?OptionQ
] := BravyiMonitor[in, ham, BravyiMap[msr, True], spec, opts]

BravyiMonitor[
  in_BravyiState,
  ham_BravyiHermitian,
  map_BravyiMap,
  {tau_?NumericQ, dt_?NumericQ},
  opts___?OptionQ
] := BravyiMonitor[in, ham, map, {tau, dt, All}, opts]

BravyiMonitor[
  in_BravyiState,
  ham_BravyiHermitian,
  map_BravyiMap,
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)},
  opts:OptionsPattern[]
] := Module[
  { n = OptionValue["Samples"],
    progress = 0,
    uni, data, more },
  uni = BravyiUnitary @ MatrixExp[N @ First[ham]*dt];
  (* simulation *)
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[n];
    theBravyiMonitor[in, uni, map, {tau, dt}][[1;;All;;ds]],
    {k, n}
  ];
  (* save data *)
  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ BravyiMonitor];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
] /; If[ MatrixQ[First @ ham, NumericQ], True,
  Message[BravyiNonitor::num, First @ ham];
  False
]

theBravyiMonitor[
  in_BravyiState,
  uni_BravyiUnitary,
  map_BravyiMap,
  {tau_?NumericQ, dt_?NumericQ}
] := Module[
  { t = dt,
    res = {in},
    new = in,
    gmm },
  gmm = 2 * Total @ map[[1, 4]];
  (* NOTE: Here, the additional factor 2 is required because the prefactors map[[1, 4]] from BravyiMapKernel[2, ...] already contains the factor of 1/2 associated with projection Dagger[b]**b. *)
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
(**** </BravyiMonitor> ****)


(**** <BravyiLindbladSolve> ****)
BravyiLindbladSolve::usage = "BravyiLindbladSolve[ham, jmp, in, t] solves the Lindblad equation associated with the Hamiltonia ham and a set of quantum jump operators jmp, and returns the fermionic Gaussian mixed state at t."
(* See also Bravyi (2012a). *)

BravyiLindbladSolve[ham_NambuHermitian, rest__] :=
  BravyiLindbladSolve[BravyiHermitian @ ham, rest]

BravyiLindbladSolve[ham_BravyiHermitian, jmp_NambuJump, rest__] :=
  BravyiLindbladSolve[ham, BravyiJump @ jmp, rest]

BravyiLindbladSolve[ham_BravyiHermitian, msr_NambuMeasurement, rest__] :=
  BravyiLindbladSolve[ham, BravyiMeasurement @ msr, rest]


BravyiLindbladSolve[ham_, jmp_, in_, t_?NumericQ, rest___] :=
  First @ BravyiLindbladSolve[ham, jmp, in, {{t}}, rest]

BravyiLindbladSolve[ham_, jmp_, in_, {t0_?NumericQ, tn_?NumericQ}, rest___] :=
  BravyiLindbladSolve[ham, jmp, in, {Range[t0, tn]}, rest]

BravyiLindbladSolve[ham_, jmp_, in_,
  {ti_?NumericQ, tf_?NumericQ, dt_?NumericQ},
  rest___
] := BravyiLindbladSolve[ham, jmp, in, {Range[ti, tf, dt]}, rest]

BravyiLindbladSolve[ham_BravyiHermitian, jmp_, in_BravyiState, rest__] :=
  Map[BravyiState, BravyiLindbladSolve[ham, jmp, in[[1, 2]], rest]]

BravyiLindbladSolve[ham_BravyiHermitian, jmp_, in_BravyiCovariance, rest__] :=
  Map[BravyiCovariance, BravyiLindbladSolve[ham, jmp, First @ in, rest]]

BravyiLindbladSolve[ham_, msr_BravyiMeasurement, cvr_, {tt_?VectorQ}] :=
 BravyiLindbladSolve[ham, msr, cvr, {tt}, False]


(* quantum jump operators are linear in fermion operators *)
BravyiLindbladSolve[
  ham_BravyiHermitian,
  jmp_BravyiJump,
  cvr_?MatrixQ,
  {tt_?VectorQ}
] := Module[
  { xx, vp, vv },
  {xx, vp} = BravyiLindbladKernel[ham, jmp];
  vv = cvr - vp;
  xx = Map[MatrixExp[xx*#]&, tt];
  vv = Map[vp + # . vv . Transpose[#]&, xx];
  Map[(# - Transpose[#])/2&, vv]
]

(* quantum jump operators are projection operators *)
BravyiLindbladSolve[
  ham_BravyiHermitian,
  msr_BravyiMeasurement,
  cvr_?MatrixQ,
  {tt_?VectorQ},
  flag:(True | False)
] := Module[
  { vec = UpperTriangular[cvr, 1],
    spr, out },
  spr = BravyiLindbladKernel[ham, msr, flag];
  out = Map[MatrixExp[spr*#] . vec&, tt];
  Map[AntisymmetricMatrix, out]
]


BravyiLindbladKernel::usage = "BravyiLindbladKernel[ham, jmp] returns a pair {krn, sol}, where krn is the kernel of the vectorized equation for the Majorana covariance matrix and sol is a stationary solution.\nBravyiLindbladKernel[ham, msr] or BravyiLindbladKernel[ham, msr, flag] returns krn."

BravyiLindbladKernel[ham_NambuHermitian, jmp_] :=
  BravyiLindbladKernel[BravyiHermitian @ ham, jmp]

BravyiLindbladKernel[ham_, jmp_NambuJump] :=
  BravyiLindbladKernel[ham, BravyiJump @ jmp]

BravyiLindbladKernel[ham_, msr_NambuMeasurement] :=
  BravyiLindbladKernel[ham, BravyiMeasurement @ msr]


(* BravyiJump *)
BravyiLindbladKernel[ham_BravyiHermitian, jmp_BravyiJump] := Module[
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

(* BravyiMeasurement *)
BravyiLindbladKernel[ham_BravyiHermitian, msr_BravyiMeasurement] := Module[
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

BravyiLindbladKernel[ham_BravyiHermitian, msr_BravyiMeasurement, False] :=
  BravyiLindbladKernel[ham, msr]

BravyiLindbladKernel[ham_BravyiHermitian, msr_BravyiMeasurement, True] :=
  BravyiLindbladKernel[ham, Surd[2, 4]*msr]
(**** </BravyiLindbladSolve> ****)


(**** <BravyiSteadyState> ****)
BravyiSteadyState::usage = "BravyiSteadyState[ham, jmp, in] returns the steady-state solution (i.e., a fermionic Gaussian mixed state) to the Lindblad equation associated with the Hamiltonian ham and a set of quantum jump operators jmp.\nBravyiSteadyState[ham, msr, in] assumes that the Lindblad operators are projective and given by Bravyi measurement msr."
(* See also Bravyi (2012a). *)

BravyiSteadyState::more = "The Lindblad equation has additional steady states."

BravyiSteadyState[ham_NambuHermitian, rest__] :=
  BravyiSteadyState[BravyiHermitian @ ham, rest]

BravyiSteadyState[ham_BravyiHermitian, jmp_NambuJump, rest__] :=
  BravyiSteadyState[ham, BravyiJump @ jmp, rest]

BravyiSteadyState[ham_BravyiHermitian, msr_NambuMeasurement, rest__] :=
  BravyiSteadyState[ham, BravyiMeasurement @ msr, rest]


BravyiSteadyState[ham_BravyiHermitian, jmp_, in_BravyiState, rest___] :=
  BravyiState @ BravyiSteadyState[ham, jmp, in[[1, 2]], rest]

BravyiSteadyState[ham_BravyiHermitian, jmp_, in_BravyiCovariance, rest___] :=
  BravyiCovariance @ BravyiSteadyState[ham, jmp, First @ in, rest]

BravyiSteadyState[ham_, msr_BravyiMeasurement, cvr_] :=
 BravyiSteadyState[ham, msr, cvr, False]


(* quantum jump operators are linear in fermion operators *)
BravyiSteadyState[
  ham_BravyiHermitian,
  jmp_BravyiJump,
  cvr_?MatrixQ
] := Module[
  { xx, vp, vv },
  {xx, vp} = BravyiLindbladKernel[ham, jmp];
  If[ZeroQ[Det @ xx], Message[BravyiSteadyState::more]];
  Return[vp]
]

(* quantum jump operators are projection operators *)
BravyiSteadyState[
  ham_BravyiHermitian,
  msr_BravyiMeasurement,
  cvr_?MatrixQ,
  flag:(True | False)
] := Module[
  { in = UpperTriangular[cvr, 1],
    spr, vec, out },
  spr = BravyiLindbladKernel[ham, msr, flag];
  vec = Eigenvectors[N @ spr];
  out = Inverse[Transpose @ vec] . in;
  out = Last[vec] * Last[out];
  AntisymmetricMatrix[Re @ out]
]
(**** </BravyiSteadyState> ****)


(**** <FermionCount> ****)
FermionCount[BravyiState[{_?NumericQ, cvr_?MatrixQ}, ___]] := Length[cvr]/2

FermionCount[BravyiCovariance[cvr_?MatrixQ, ___]] := Length[cvr]/2

FermionCount[BravyiHermitian[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[BravyiUnitary[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[BravyiNonunitary[{ham_?MatrixQ, _?MatrixQ, _}, ___]] := Last[Dimensions @ ham]/2

FermionCount[BravyiJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[BravyiCircuit[gg_List, ___?OptionQ]] := Max[FermionCount /@ gg]
(**** </FermionCount> ****)

End[] (* Fermionic quantum computation *)


(**********************************************************************)
(**** quantum information theory for fermionic Gaussian states     ****)
(**********************************************************************)

Begin["`Private`"]

(**** <BravyiTimeReversalMoment> ****)
BravyiTimeReversalMoment::usage = "BravyiTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nBravyiTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to BravyiTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

BravyiTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[BravyiTimeReversalMoment] = { 
  "Epsilon" -> 1.25*^-16
  (* "Epsilon" -> 1.25*^-20 *)
}

(* canoncialization *)
BravyiTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  BravyiTimeReversalMoment[alpha, NambuGreen @ {grn, 0}, kk, opts]

(* canoncialization *)
BravyiTimeReversalMoment[alpha_, grn_?NambuMatrixQ, rest__] := 
  BravyiTimeReversalMoment[alpha, NambuGreen @ grn, rest]

(* canoncial form *)
BravyiTimeReversalMoment[
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
  OptionsPattern[BravyiTimeReversalMoment]
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
(**** </BravyiTimeReversalMoment> ****)


(**** <BravyiLogarithmicNegtivity> ****)
BravyiLogarithmicNegativity::usage = "BravyiLogarithmicNegativity[grn, {k1, k2, \[Ellipsis]}] returns the logarithmic entanglement negativity between the subsystem consisting of fermion modes {k1, k2,\[Ellipsis]}\[Subset]{1,2,\[Ellipsis],n} in the Bravyi state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nBravyiLogarithmicNegativity[NambuGreen[{grn, anm}], {k1, k2,\[Ellipsis]}] or BravyiLogarithmicNegativity[{grn, anm}, {k1, k2,\[Ellipsis]}] returns the logarithmic negativity in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nBravyiLogarithmicNegativity[state, {k1, k2, \[Ellipsis]}] is equivalent to BravyiLogarithmicNegativity[BravyiGreen[state], {k1, k2,\[Ellipsis]}] for state = BravyiState or NambuState."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

Options[BravyiLogarithmicNegativity] = Options[BravyiTimeReversalMoment]

(* operator form *)
BravyiLogarithmicNegativity[kk:{__Integer}][any_] :=
  BravyiLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[BravyiLogarithmicNegativity, "Epsilon"]]

(* special case *)
BravyiLogarithmicNegativity[obj_, {}, ___] = 0

(* for large data *)
BravyiLogarithmicNegativity[data_?ArrayQ, kk:{___Integer}, opts___?OptionQ] := 
  arrayMap[BravyiLogarithmicNegativity[kk], data] /; 
  ArrayQ[data, _, MatchQ[#, _BravyiState | _BravyiCovariance | _NambuGreen]&]

(* shortcut *)
BravyiLogarithmicNegativity[ws_BravyiState, rest__] :=
  BravyiLogarithmicNegativity[BravyiCovariance @ ws, rest]

(* shortcut *)
BravyiLogarithmicNegativity[cvr_BravyiCovariance, kk:{__Integer}, opts:OptionsPattern[]] :=
  BravyiLogarithmicNegativity[ NambuGreen[cvr], kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]


(* Canonical form for normal models *)
BravyiLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___] := 
  WickLogarithmicNegativity[grn, kk]

(* BdG models *)
BravyiLogarithmicNegativity[grn_NambuGreen, kk:{__Integer}, ___] :=
  BravyiLogarithmicNegativity[grn[[1, 1]], kk] /; ArrayZeroQ[grn[[1, 2]]] 

BravyiLogarithmicNegativity[grn_NambuGreen, kk:{__Integer}, ___] := 0 /;
  FermionCount[grn] == Length[kk]

(* Canonical form for BdG models *)
BravyiLogarithmicNegativity[
  grn_NambuGreen, kk:{__Integer}, 
  opts:OptionsPattern[]
] := BravyiTimeReversalMoment[1/2, grn, kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]

(* canonicalization *)
BravyiLogarithmicNegativity[grn_?NambuMatrixQ, rest__] :=
  BravyiLogarithmicNegativity[NambuGreen @ grn, rest]
(**** </BravyiLogarithmicNegtivity> ****)


(**** <BravyiEntropy> ****)
BravyiEntropy::usage = "BravyiEntropy[grn] returns the von Neumann entropy of a fermionic Gaussian state characterized by the matrix grn of single-particle Green's functions. BravyiEntropy[NambuGreen[{grn, anm}]] or BravyiEntropy[{grn, anm}] considers a fermionic Gaussian state characterized by matrices grn and anm of normal and anomalous Green's functions."
(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

(* canonical form for normal models *)
BravyiEntropy[grn_?MatrixQ] := WickEntropy[grn]

(* for BdG models *)
BravyiEntropy[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  BravyiEntropy[grn] /; ArrayZeroQ[anm]

(* for BdG models *)
BravyiEntropy[{grn_?MatrixQ, anm_?MatrixQ}] :=
  BravyiEntropy[grn] /; ArrayZeroQ[anm]

(* for BdG models *)
BravyiEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___]] :=
  BravyiEntropy[Normal @ grn] / 2

(* for BdG models *)
BravyiEntropy[grn:{_?MatrixQ, _?MatrixQ}] :=
  BravyiEntropy[Normal @ NambuGreen @ grn] / 2


BravyiEntropy[cvr_BravyiCovariance] := Module[
  { vv = First[cvr],
    id },
  id = One[Dimensions @ vv];
  (QuantumLog[2, (id - I*vv)/2] + QuantumLog[2, (id + I*vv)/2]) / 2
]

BravyiEntropy[in_BravyiState] :=
  BravyiEntropy[BravyiCovariance @ in]
(**** </BravyiEntropy> ****)


(**** <BravyiEntanglementEntropy> ****)
BravyiEntanglementEntropy::usage = "BravyiEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Bravyi state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nBravyiEntanglementEntropy[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or BravyiEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nBravyiEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] is equivalent to BravyiEntanglementEntropy[BravyiGreen[state, {k1, k2, \[Ellipsis]}], {k1, k2, \[Ellipsis]}] for Bravyi or BdG state.\nBravyiEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of BravyiEntanglementEtropy to be applied to Green's functions, Bravyi or Nambu state."
(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

(* operator form *)
BravyiEntanglementEntropy[kk:{___Integer}][any_] :=
  BravyiEntanglementEntropy[any, kk]

(* special case *)
BravyiEntanglementEntropy[any_, {}] = 0

(* for large data *)
BravyiEntanglementEntropy[data_?ArrayQ, kk:{___Integer}] := 
  arrayMap[BravyiEntanglementEntropy[kk], data] /; 
  ArrayQ[data, _, MatchQ[#, _BravyiState | _BravyiCovariance | _NambuGreen]&]

(* directly from covariance matrix *)
BravyiEntanglementEntropy[BravyiCovariance[cvr_?MatrixQ, ___], kk:{__Integer}] := Module[
  { jj = Join[kk, kk + Length[cvr]/2] },
  BravyiEntropy[ BravyiCovariance @ cvr[[jj, jj]] ]
]

(* shortcut *)
BravyiEntanglementEntropy[in_BravyiState, kk:{___Integer}] :=
  BravyiEntanglementEntropy[BravyiCovariance @ in, kk]

(* for normal models *)
BravyiEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  WickEntropy @ grn[[kk, kk]]

(* for BdG models *)
BravyiEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] :=
  BravyiEntanglementEntropy[grn, kk] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
BravyiEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  BravyiEntropy @ Normal @ NambuGreen[{gg, ff}] / 2
]

(* canonicalization for BdG models *)
BravyiEntanglementEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___], kk:{__Integer}] :=
  BravyiEntanglementEntropy[First @ grn, kk]
(**** </BravyiEntanglementEntropy> ****)


(**** <BravyiMutualInformation> ****)
BravyiMutualInformation::usage = "BravyiMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Bravyi state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nBravyiMutualInformation[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or BravyiMutualInformation[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nBravyiMutualInformation[state, {k1, k2, \[Ellipsis]}] is equivalent to BravyiMutualInformation[BravyiGreen[state], {k1, k2, \[Ellipsis]}] for Bravyi or BdG state.\nBravyiMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of BravyiEntanglementEtropy to be applied to Green's functions, Bravyi or Nambu state."
(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)

(* operator form *)
BravyiMutualInformation[kk:{__Integer}][any_] :=
  BravyiMutualInformation[any, kk]

(* shortcut *)
BravyiMutualInformation[ws_BravyiState, kk:{__Integer}] :=
  BravyiMutualInformation[BravyiCovariance @ ws, kk]

(* directly from covariance matrix *)
BravyiMutualInformation[cvr:BravyiCovariance[vv_?MatrixQ, ___], kk:{__Integer}] := Module[
  { n = FermionCount[cvr],
    ii, jj, ll },
  ll = Supplement[Range @ n, kk];
  ii = Riffle[kk, n + kk];
  jj = Riffle[ll, n + ll];
  ( BravyiEntropy[ BravyiCovariance @ vv[[ii, ii]] ] + 
    BravyiEntropy[ BravyiCovariance @ vv[[jj, jj]] ] -
    BravyiEntropy[ BravyiCovariance @ vv ]
  ) / 2
]

(* for large data *)
BravyiMutualInformation[data_?ArrayQ, kk:{___Integer}] := 
  arrayMap[BravyiMutualInformation[kk], data] /; 
  ArrayQ[data, _, MatchQ[#, _BravyiState | _BravyiCovariance | _NambuGreen]&]

(* canonical form for normal models *)
BravyiMutualInformation[gg_?MatrixQ, kk:{__Integer}] :=
  WickMutualInformation[gg, kk]

(* BdG models *)
BravyiMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] :=
  BravyiMutualInformation[gg, kk] /; ArrayZeroQ[ff]

(* canonical form for BdG models *)
BravyiMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] := With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  ( BravyiEntropy[Normal @ NambuGreen @ {gg[[kk, kk]], ff[[kk, kk]]}] +
    BravyiEntropy[Normal @ NambuGreen @ {gg[[ll, ll]], ff[[ll, ll]]}] -
    BravyiEntropy[Normal @ NambuGreen @ {gg, ff}]
  ) / 2
]

(* canonicalization for BdG models *)
BravyiMutualInformation[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], kk:{__Integer}] :=
  BravyiMutualInformation[{gg, ff}, kk]
(**** </BravyiMutualInformation> ****)

End[] (* quantum information theory for fermionic Gaussian states *)

EndPackage[]
