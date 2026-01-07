(* ::Package:: *)

(* Fermionic quantum computation without pairing potential *)
(* See Appendix B in Feng & Chen (2024). *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

Begin["`Private`"] (* Fermionic quantum computation *)

barrenMatrix[{n_Integer, 0}] := One[n]

barrenMatrix[{m_?MatrixQ, 0}] = m


FermionCount[{m_?MatrixQ, 0}] := Last[Dimensions @ m]


(**** <barrenMatrixQ> ****)

barrenMatrixQ::usage = "barrenMatrixQ[{m, 0}] or barrenMatrixQ[{0, m}] returns True if m is a complex matrix.\nbarrenMatrixQ[{m, 0}, test] or barrenMatrixQ[{0, m}, test] requires also that test yield True when applied to each of the array elements in m. "

barrenMatrixQ[{_?MatrixQ, 0}] = True

barrenMatrixQ[{m_?MatrixQ, 0}, test_] := MatrixQ[m, test]

barrenMatrixQ[_] = False

barrenMatrixQ[_, _] = False


barrenIntegerQ[{_Integer, 0}] = True

barrenIntegerQ[_] = False


barrenJumpQ[{None|{}|_?MatrixQ, None|{}|_?MatrixQ}] = True

barrenJumpQ[{a:None|{}|_?MatrixQ, b:None|{}|_?MatrixQ}, test] :=
  MatrixQ[Join[a, b], test]

barrenJumpQ[_] = False

barrenJumpQ[_, _] = False

(**** </barrenMatrixQ> ****)


(**** <WickState> ****)

WickState /:
MakeBoxes[ws:WickState[{fac_?NumericQ, trs:{_Integer|_?MatrixQ, 0}},  ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ws },
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Transformation: ",
      If[MatrixQ[First @ trs], ArrayShort[First @ trs], None] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* canonicalization *)
WickState[trs_?barrenMatrixQ, opts___?OptionQ] :=
  WickState[{1, trs}, opts]

(* canonicalization *)
WickState[{fac_, {trs_?MatrixQ, 0}}, rest___?OptionQ] :=
  WickState[{fac, {SparseArray @ trs, 0}}, rest] /;
    Head[trs] =!= SparseArray

(* initialization by occupation numbers *)
WickState[vv_?VectorQ, {n_Integer, 0}, rest___?OptionQ] := Module[
  { ww = PadRight[vv, n, vv],
    kk },
  kk = Flatten @ Position[ww, 1];
  WickState[{1, {One[n][[kk]], 0}}, rest]
]


WickState /:
NambuGreen[ws:WickState[{_?NumericQ, _?barrenMatrixQ}, ___]] :=
  NambuGreen[{WickGreenFunction @ ws, 0}]


WickGreenFunction[ws:WickState[{_?NumericQ, {_Integer|_?MatrixQ, 0}}, ___]] :=
  WickGreenFunction[ws, Range @ FermionCount @ ws]

(* vacuum state *)
WickGreenFunction[WickState[{_?NumericQ, {_Integer, 0}}, ___], kk:{___Integer}] :=
  One[Length @ kk]

WickGreenFunction[WickState[{_?NumericQ, {trs_?MatrixQ, 0}}, ___], kk:{___Integer}] := Module[
  { n = Length[kk],
    alt = trs[[All, kk]] },
  One[n] - ConjugateTranspose[alt].alt
]


WickState /:
NormSquare[WickState[{fac_?NumericQ, _?barrenMatrixQ}, ___]] := Abs[fac]

WickState /:
Norm[WickState[{fac_?NumericQ, _?barrenMatrixQ}, ___]] := Sqrt[Abs @ fac]


WickState /:
Normalize[WickState[{_?NumericQ, grn_?barrenMatrixQ}, rest___]] :=
  WickState[{1, grn}, rest]


(* CONVEX linear superposition; but NOT a general linear superposition *)
WickState /:
Plus[WickState[{fa_, {ga_, 0}}, any___], WickState[{fb_, {gb_, 0}}, more___]] :=
  WickState[{(fa*ga + fb*gb)/(fa + fb), 0}, fa + fb, any, more]

WickState /:
Times[z_?NumericQ, WickState[{fac_?NumericQ, trs:{_Integer|_?MatrixQ, 0}}, rest___]] := 
  WickState[{z*fac, trs}, rest] /;
    If[ RealQ[z], True,
      Message[WickState::convex, z];
      False
    ]
(* NOTE: This feature is to support convex linear superposition of two Gaussian states as mixed states. In principle, the numerical factor must be in [0, 1]. Here, any real number is allowed for convenience. *)


WickState /:
ExpressionFor[ws:WickState[{_?NumericQ, {_Integer|_?MatrixQ, 0}}, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ ws, cc]


WickState /:
Matrix[ws:WickState[{_?NumericQ, _?barrenMatrixQ}, ___], ss:{___?SpeciesQ}] :=
  MatrixEmbed[Matrix @ ws, Select[ss, FermionQ], ss]

WickState /: (* null state *)
Matrix[ws:WickState[{0, _?barrenMatrixQ}, ___]] :=
  Zero @ Power[2, FermionCount @ ws]

WickState /: (* vacuum state *)
Matrix[ws:WickState[{fac_?NumericQ, {n_Integer, 0}}, ___]] :=
  PadRight[{fac}, Power[2, n]]

WickState /: (* pure state without pairing *)
Matrix[ws:WickState[{fac_?NumericQ, {trs_?MatrixQ, 0}}, ___]] := Module[
  { n = FermionCount[ws], 
    mm, vv },
  mm = theWignerJordan[n]; (* fermion annihilators *)
  vv = ConjugateTranspose[Apply[Dot, trs.mm]] . PadRight[{1}, Power[2, n]];
  CanonicalizeVector[vv] * Sqrt[Abs @ fac]
]

(**** </WickState> ****)


RandomWickState::usage = "RandomWickState[{n, 0}] randomly generates a Gaussian pure state of n fermion modes."

RandomWickState[{n_Integer, 0}, opts___?OptionQ] := Module[
  { uu, kk },
  kk = RandomInteger[{0, n}];
  If[kk == 0, Return @ WickState[{1, {n, 0}}, opts]];
  kk = RandomSample[Range @ n, kk];
  uu = RandomUnitary[n];
  WickState[{1, {uu[[kk]], 0}}]
]


WickCount::usage = "WickCount[ws] returns the average number of particles in the Wick state ws."

WickCount[ws_WickState] := WickCount[ ws[[1, 2]] ]

WickCount[{_Integer, 0}] = 0 (* the vacuum state *)

WickCount[{trs_?MatrixQ, 0}] := Length[trs]

WickCount[cvr_?MatrixQ] := Module[
  { grn = NambuGreen[WickCovariance @ cvr][[1, 1]] },
  Length[grn] - Tr[grn]
]


(**** <WickPureQ> ****)

WickPureQ[WickState[{_?NumericQ, {_Integer|_?MatrixQ, 0}}, ___]] := True

(**** </WickPureQ> ****)


(**** <WickSingleQ> ****)

WickSingleQ[{_?MatrixQ, 0}, ___] = True

WickSingleQ[WickState[{_?NumericQ, {_Integer|_?barrenMatrixQ, 0}}, ___]] = True

(**** </WickSingleQ> ****)


(**** <VickMean> ****)

WickMean[data_?ArrayQ] := Mean @ ReplaceAll[ 
  data,
  WickState[{_?NumericQ, trs_?barrenMatrixQ}, ___] :> barrenMatrix[trs]
] /; ArrayQ[data, _, MatchQ[#, _WickState]&]

(**** <VickMean> ****)


(**** <WickUnitary> ****)

WickUnitary /:
MakeBoxes[op:WickUnitary[uu_?barrenMatrixQ, rest___], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ uu },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ barrenMatrix @ uu }
    },
    { BoxForm`SummaryItem @ { "Transformation matrix: ", 
      ArrayShort @ barrenMatrix @ uu }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickUnitary[WickUnitary[mat_?barrenMatrixQ, rest___], more___] :=
  WickUnitary[mat, more, rest]


WickUnitary /:
Normal[WickUnitary[mm_?barrenMatrixQ, ___], rest___] :=
  Normal[barrenMatrix @ mm, rest]

WickUnitary /:
MatrixForm[WickUnitary[mm_?barrenMatrixQ, ___], opts___?OptionQ] :=
  MatrixForm[barrenMatrix @ mm, opts]

WickUnitary /:
ArrayShort[WickUnitary[mm_?barrenMatrixQ, ___], opts___?OptionQ] :=
  ArrayShort[barrenMatrix @ mm, opts]

WickUnitary /:
Dagger @ WickUnitary[{mat_?MatrixQ, 0}, rest___] :=
  WickUnitary[{ConjugateTranspose @ mat, 0}, rest]

WickUnitary /:
Dot[
  WickUnitary[{a_?MatrixQ, 0}, any___], 
  WickUnitary[{b_?MatrixQ, 0}, other___]
] :=
  WickUnitary[{Dot[a, b], 0}, any, other]


WickUnitary /:
ExpressionFor[op:WickUnitary[_?barrenMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

WickUnitary /: (* fallback *)
ExpressionFor[op_WickUnitary, ___] = op


WickUnitary /:
Matrix[WickUnitary[{mat_?MatrixQ, 0}, ___]] := Module[
  { n = Last[Dimensions @ mat],
    hh = MatrixLog[mat],
    mm },
  mm = theWignerJordan[n];
  mm = TensorContract[
    Transpose[ConjugateTranspose /@ mm, {3, 1, 2}] . hh . mm,
    {{2, 3}}
  ];
  MatrixExp[mm]
]

WickUnitary /:
Matrix[op:WickUnitary[_?barrenMatrixQ, ___], ss:{__?SpeciesQ}] := 
  MatrixEmbed[Matrix[op], Select[ss, FermionQ], ss]

WickUnitary /: (* fallback *)
Matrix[op_WickUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


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


RandomWickUnitary[{n_Integer, 0}, rest___] :=
  WickUnitary[{RandomUnitary @ n, 0}, rest]


(**** <WickHermitian> ****)

WickHermitian /:
MakeBoxes[op:WickHermitian[{mat_?MatrixQ, 0}, ___], fmt_] :=
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
Normal[WickHermitian[{mat_?MatrixQ, 0}, ___], rest___] :=
  Normal[mat, rest]

(* conversion *)
WickHermitian /:
NambuHermitian[WickHermitian[mat:{_?MatrixQ, 0}, opts___?OptionQ], more___?OptionQ] :=
  NambuHermitian[mat, more, opts]

(* conversion *)
WickHermitian /:
ToDirac[op_WickHermitian] := NambuHermitian[op]


WickHermitian /:
MatrixForm[WickHermitian[{mm_?MatrixQ, 0}, ___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

WickHermitian /:
ArrayShort[WickHermitian[{mm_?MatrixQ, 0}, ___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


WickHermitian /:
ExpressionFor[WickHermitian[{mat_?MatrixQ, 0}, ___], aa:{__?FermionQ}] :=
  Garner[ MultiplyDot[Dagger @ aa, mat, aa] ]

WickHermitian /:
ExpressionFor[WickHermitian[{m_?MatrixQ, 0}, ___], cc:{__?MajoranaQ}] := 
  ExpressionFor[WickHermitian[NambuHermitian @ {m, 0}], cc] + Tr[m]/2

WickHermitian /:
Matrix[op:WickHermitian[{mat_?MatrixQ, 0}, ___]] := Module[
  { n = Length[mat],
    xy, mm },
  xy = theWignerJordan[n];
  mm = Transpose[ConjugateTranspose /@ xy, {3, 1, 2}] . mat . xy;
  TensorContract[mm, {{2, 3}}]
]

(**** </WickHermitian> ****)


RandomWickHermitian[{n_Integer, 0}, opts___?OptionQ] := 
  WickHermitian[{RandomHermitian @ n, 0}, opts]


(**** <VickElements> ****)

VickElements::usage = "VickElements[mat, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of Majorana operators {c1, c2, \[Ellipsis]} with the coefficients specified by elements of complex matrix mat.\nVickElements[mat, {a1, a2, \[Ellipsis]}] returns a list of linear combinations of the annihilation and creation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}, where the elements of complex matrix mat are the coefficients in the equivalent linear combinations of Majorana fermion operators (not the Dirac fermion operators themselves) corresponding to the Dirac fermion modes."

VickElements[mat_?MatrixQ, cc:{__?MajoranaQ}] :=
  Dot[ToMajorana /@ ArrayFlatten[{{mat, 0}}], cc]

VickElements[{mat_?MatrixQ, 0}, aa:{__?FermionQ}] := 
  Dot[mat, aa]

VickElements[{0, mat_?MatrixQ}, aa:{__?FermionQ}] := 
  Dot[mat, Dagger @ aa]

VickElements[
  (VickOperator|VickJump|VickMeasurement)[mat_?VickMatrixQ, ___],
  spec:({__?MajoranaQ} | {__?FermionQ} )
] := VickElements[mat, spec]

(**** </VickElements> ****)


(**** <VickCoefficients> ****)

VickCoefficients::usage = "VickCoefficients[expr, {c1,c2,\[Ellipsis]}] returns a vector or matrix of coefficients in a linear combination or linear combinations of Majorana fermion operators {c1,c2,\[Ellipsis]}, and transforms it to a vector or matrix of coefficients in the equivalent linear combination(s) of the Dirac fermion operators corresponding to the Majorana fermion modes.\nVickCoefficients[expr, {a1,a2,\[Ellipsis]}] gets a vector or matrix of coefficients in a linear combination or linear combinations of the annihilation and creation operators of Dirac fermion modes {a1,a2,\[Ellipsis]}."

VickCoefficients::nlin = "`` is not a linear combination of Dirac or Majorana fermion operators of modes ``."

VickCoefficients[spec:({__?FermionQ} | {__?MajoranaQ})][expr_] :=
  VickCoefficients[expr, spec]

VickCoefficients[expr_List, spec:({__?FermionQ} | {__?MajoranaQ})] :=
  Map[VickCoefficients[spec], expr]

VickCoefficients[expr_, cc:{__?MajoranaQ}] :=
  ToDirac @ Coefficient[expr, cc, 1] /;
  If[ theVickLinearQ[expr, cc], True,
    Message[VickCoefficients::nlin, expr, cc];
    False
  ]

VickCoefficients[expr_, aa:{__?FermionQ}] :=
  Coefficient[expr, Join[aa, Dagger @ aa], 1] /;
  If[ theVickLinearQ[expr, aa], True,
    Message[VickCoefficients::nlin, expr, aa];
    False
  ]


theVickLinearQ::usage = "theVickLinearQ[expr, {c1, c2, \[Ellipsis]}] returns True if expr is a linear combination of Majorana fermion operators {c1, c2, \[Ellipsis]}, and False otherwise.\ntheVickLinearQ[expr, {a1, a2, \[Ellipsis]}] returns True if expr is a linear combination of the creation and annihilation operators of Dirac fermion modes {a1, a2, \[Ellipsis]}, and False otherwise."

theVickLinearQ[expr_List, spec_] :=
  AllTrue[expr, theVickLinearQ[#, spec]&]

theVickLinearQ[expr_, aa:{__?FermionQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[aa -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ Join[aa, Dagger @ aa], ___]
  ]
]

theVickLinearQ[expr_, cc:{__?MajoranaQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ cc, ___]
  ]
]

(**** </VickCoefficients> ****)


(**** <VickOperator> ****)

VickOperator::usage = "VickOperator[mat] represents a sequence of linear combinations of Majorana fermion operators with coefficients given by the elements of matrix mat."

VickOperator::flag = "Invalid flags ``; the flags must be binary digits."

VickOperator /:
MakeBoxes[op:VickOperator[mat_?VickMatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[VickMatrix @ mat];
  BoxForm`ArrangeSummaryBox[
    VickOperator, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* shortcut *)
VickOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  VickOperator[{spec}, n]

(* shortcut *)
VickOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, opts___?OptionQ] :=
  VickOperator[VickCoefficients[ops, cc], opts]

(* shortcut *)
VickOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  { id = One[2n],
    mm, kk, flag },
  {kk, flag} = Transpose[spec];
  kk = n*flag + kk;
  mm = NambuOperator[ id[[kk]] ];
  VickOperator[mm, opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[VickOperator::flag, flag]; False 
  ]
]


(* conversion *)
VickOperator[jmp_VickJump] := Apply[VickOperator, jmp]


(* canonicalization *)
VickOperator[mat_?MatrixQ, opts___?OptionQ] :=
  VickOperator[SparseArray @ mat, opts] /; Head[mat] =!= SparseArray
(* NOTE: In many physical cases, the linear combinations are rather simple. *)

VickOperator /:
MatrixForm[VickOperator[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

VickOperator /:
ArrayShort[VickOperator[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]

VickOperator /:
Dagger @ VickOperator[ops_?MatrixQ, rest___] :=
  VickOperator[VickConjugateReverse @ ops, rest]


VickOperator /:
Matrix[VickOperator[mat_?MatrixQ, ___]] := 
  Apply[Dot, Identity /@ Matrix[VickJump @ mat]]
(* NOTE: Identity /@ ... to put a whole SparseArray into a list of matrices. *)

VickOperator /:
Matrix[op_VickOperator, ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ op, Select[ss, FermionQ], ss]


VickOperator /:
ExpressionFor[VickOperator[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Apply[Multiply, VickElements[mat, cc]]  
]

VickOperator /: (* fallback *)
ExpressionFor[op_VickOperator, ___] = op 


VickOperator /: 
NonCommutativeQ[_VickOperator] = True

VickOperator /:
MultiplyKind[_VickOperator] = Fermion

VickOperator /:
Multiply[pre___, opr_VickOperator, ws_VickState] := Multiply[pre, opr @ ws]

VickOperator[{}, ___][any_] = any

VickOperator[mat_?VickMatrixQ, ___][in:VickState[{_?NumericQ, _?MatrixQ}, ___]] :=
  Fold[#2[#1]&, in, Reverse @ Map[VickFlop, Thread @ mat]]

(**** </VickOperator> ****)


(**** <WickFlop> ****)
(* NOTE: WickFlop may be integrated into WickOperator, but separating this feature keeps better the performance of WickOperator. *)

(* annihilator on the vacuuum state *)
WickFlop[{_?VectorQ, 0}, ___][WickState[{_, {_Integer, 0}}, ____]] :=
  WickState[{0, {Length @ vec, 0}}, rest] (* the null state *)

WickFlop[{vec_?VectorQ, 0}, ___][WickState[{fac_?NumericQ, {trs_?MatrixQ, 0}}, rest___]] := Module[
  { ovr = vec . ConjugateTranspose[trs],
    prb, hhd, new },
  prb = NormSquare[ovr];
  If[ZeroQ[prb], Return @ WickState[{0, {Length @ vec, 0}}, rest]]; (* the null state *)
  hhd = HouseholderMatrix[ovr];
  new = Rest[ConjugateTranspose[hhd].trs];
  If[ new == {},
    Return @ WickState[{fac*prb, {Length @ vec, 0}}, rest] (* the vacuum state *)
  ];
  WickState[{fac*prb, {new, 0}}, rest]
]


(* creator on the vacuuum state *)
WickFlop[{0, vec_?VectorQ}, ___][WickState[{fac_, {_Integer, 0}}, rest___]] :=
  WickState[{fac * NormSquare[vec], {{Normalize @ Conjugate @ vec}, 0}}, rest] 

(* all fermion modes are occupied *)
WickFlop[{0, vec_?VectorQ}, ___][WickState[{fac_?NumericQ, {trs_?MatrixQ, 0}}, rest___]] := 
  WickState[{0, {Length @ vec, 0}}, rest] /; (* the null state *)
  Length[trs] == Length[vec]

WickFlop[{0, vec_?VectorQ}, ___][WickState[{fac_?NumericQ, {trs_?MatrixQ, 0}}, rest___]] := Module[
  { qq, rr },
  qq = Prepend[trs, Conjugate @ vec];
  {qq, rr} = QRDecomposition[ConjugateTranspose @ qq];
  Echo[MatrixForm @ Chop @ qq, "qq:2"];
  Echo[MatrixForm @ Chop @ rr, "rr"];
  WickState[{fac*AbsSquare[Det @ rr], {qq, 0}}, rest]
]


VickFlopKernel[{vec_?VectorQ, 0}] := Module[
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


RandomVickOperator::usage = "RandomVickOperator[k_Integer, n_Integer] returns VickOperator consisting of k linear combinations of Majorana operators."

RandomVickOperator[k_Integer, n_Integer, opts___?OptionQ] :=
  VickOperator[RandomMatrix[{k, 2n}], opts]

RandomVickOperator[n_Integer] :=
  RandomVickOperator[RandomInteger[{1, n}], n]


(**** <VickJump> ****)

VickJump /:
MakeBoxes[jmp:VickJump[mat_?MatrixQ, rest___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    VickJump, jmp, None,
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
VickJump[op_VickOperator] := Apply[VickJump, op]

(* conversion *)
VickJump /:
NambuJump[VickJump[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  NambuJump[ToDirac /@ mat, more, opts] /; (* NOT ToDiract @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[VickJump::odd, ArrayShort @ mat, Dimensions @ mat];
    False
]

(* conversion *)
VickJump /:
ToDirac[jmp_VickJump] := NambuJump[jmp]

(* canonicalization *)
VickJump[mat_?MatrixQ, opts___?OptionQ] :=
  VickJump[SparseArray @ mat, opts] /; Head[mat] =!= SparseArray
(* NOTE: In many physical cases, the linear combinations are rather simple. *)


(* shortcut *)
VickJump[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, opts___?OptionQ] :=
  VickJump @ VickOperator[ops, cc, opts]

(* shortcut *)
VickJump[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := 
  VickJump @ VickOperator[spec, n, opts]

(* shortcut *)
VickJump[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  VickJump[{spec}, n, opts]


VickJump /:
Normalize[VickJump[mat_?MatrixQ, rest___], ___] := Module[
  { new = Map[Normalize, mat]/Sqrt[2] },
  (* NOTE: Notice the factor of 1/Sqrt[2]. *)
  VickJump[new, rest]
]

VickJump /:
MatrixForm[VickJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

VickJump /:
ArrayShort[VickJump[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


VickJump /:
Dagger @ VickJump[mat_?MatrixQ, rest___] :=
  VickJump[VickConjugateReverse @ mat, rest]

VickJump /:
Plus[VickJump[a_, any___], VickJump[b_, other___]] :=
  VickJump[a + b, any, other]

VickJump /:
Times[z_, VickJump[mm_, rest___]] :=
  VickJump[z * mm, rest]


VickJump /:
Matrix[jmp:VickJump[mat_?MatrixQ, ___]] := Module[
  { xy = theWignerJordanMajorana[FermionCount @ jmp] },
  Identity /@ Dot[mat, xy]
  (* NOTE: Identoity /@ ... to put the results into a list of matrices rather than a single large SparseArray. *)
]

VickJump /:
Matrix[jmp_VickJump, ss:{___?SpeciesQ}] := With[
  { mm = Matrix[jmp],
    cc = Select[ss, FermionQ] },
  Map[MatrixEmbed[#, cc, ss]&, mm]
]


VickJump /: 
NonCommutativeQ[_VickJump] = True

VickJump /:
MultiplyKind[_VickJump] = Fermion

VickJump /:
Multiply[pre___, jmp_VickJump, ws_VickState] := Multiply[pre, jmp @ ws]

VickJump[mat_?MatrixQ, ___][in_VickState] := (* null state *)
  VickState[{0, Zero[2*FermionCount[in]*{1, 1}]}, Rest @ in] /;
  VickNullQ[in]

VickJump[mat_?MatrixQ, ___][in_VickState] := VickMap[VickJump @ mat][in]

(**** </VickJump> ****)


(**** <VickJumpOdds> ****)

VickJumpOdds::usage = "VickJumpOdds[mat][\[Rho]] returns the probabilities for the quantum jump processes \[Rho] \[RightTeeArrow] b[i]**\[Rho]**Dagger[b[i]], where b[i]:=Sum[mat[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of 2n bare Majorana fermion modes c[j]."

VickJumpOdds[jmp_VickJump, ___] :=
  VickMapOdds[First @ VickMap @ jmp]

(**** </VickJumpOdds> ****)


RandomVickJump::usage = "RandomVickJump[k_Integer, n_Integer] returns VickJump consisting of k linear combinations of Majorana operators."

RandomVickJump[k_Integer, n_Integer, opts___?OptionQ] :=
  VickJump[RandomMatrix @ {k, 2n}, opts]

RandomVickJump[n_Integer, opts___?OptionQ] :=
  RandomVickJump[RandomInteger @ {1, n}, n, opts]


(**** <VickMeasurement> ****)

VickMeasurement::usage = "VickMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nVickMeasurement[{k1, k2, \[Ellipsis]}] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nVickMeasurement[mat] represents a sequence of measurement on the dressed Dirac fermion modes b[i] := Sum[m[[i,j]] c[j], {j, 2n}] expressed in terms of Majorana fermion modes c[k].\nVickMeasurement[spec][ws] simulates the measurement on Vick state ws, and returns the post-measurement state."

VickMeasurement::odd = "The second dimension of the input matrix `` is odd: ``."

VickMeasurement::dressed = "A vector of coefficients `` cannot describe a proper dressed Dirac fermion mode."


VickMeasurement /:
MakeBoxes[msr:VickMeasurement[mat_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    VickMeasurement, msr, None,
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
VickMeasurement[k_Integer, n_Integer, rest___] :=
  VickMeasurement[{k}, n, rest]

(* canonicalization *)
(* NOTE: kk = {} may happen, e.g., in RandomVickCircuit. *)
VickMeasurement[kk:{___Integer}, n_Integer, rest___] := With[
  { mm = One[{n, 2*n}] },
  VickMeasurement @ NambuMeasurement @ mm[[kk]]
]

(* canonicalization *)
VickMeasurement[mat_?MatrixQ, rest___] :=
  VickMeasurement[SparseArray @ mat, rest] /;
  Head[mat] =!= SparseArray

VickMeasurement /:
Matrix[VickMeasurement[mat_?MatrixQ, ___], rest___] := Module[
  { ops = Matrix[VickJump @ mat, rest] },
  MapThread[Dot, {ConjugateTranspose /@ ops, ops}]
  (* NOTE: Returned are UNNORMALIZED projection operators. *)
]

VickMeasurement /:
Normalize[VickMeasurement[mat_?MatrixQ, rest___], ___] := Module[
  { new = Map[Normalize, mat]/Sqrt[2] },
  (* NOTE: Notice the factor of 1/Sqrt[2]. *)
  VickMeasurement[new, rest]
]

VickMeasurement /:
Dagger @ VickMeasurement[mat_?MatrixQ, rest___] :=
  VickMeasurement[VickConjugateReverse @ mat, rest]

VickMeasurement /:
Times[z_, VickMeasurement[mm_, rest___]] :=
  VickMeasurement[z * mm, rest]


VickMeasurement /:
MatrixForm[VickMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  MatrixForm[mm, opts]

VickMeasurement /:
ArrayShort[VickMeasurement[mm_?MatrixQ, rest___], opts___?OptionQ] :=
  ArrayShort[mm, opts]


VickMeasurement /:
NonCommutativeQ[_VickMeasurement] = True

VickMeasurement /:
MultiplyKind[_VickMeasurement] = Fermion

VickMeasurement /:
Multiply[pre___, msr_VickMeasurement, ws_VickState] := Multiply[pre, msr @ ws]


(* NOTE: This may happen, e.g., in RandomVickCircuit. *)
VickMeasurement[{}, ___][in_VickState] = in

(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
(* The vector vec := mat[[1]] describes a dressed Dirac fermion mode
      b := Sum[vec[[jj]] c[j], {j, 2n}]
   in terms of Majorana modes c[k]. *)
VickMeasurement[mat_?MatrixQ, ___][in:VickState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { vv = First[mat],
    aa, bb, new },
  {aa, bb} = VickMeasurementKernel[N @ vv];
  new = theVickMeasurement[{aa, bb}, cvr];
  $MeasurementOut[vv] = $MeasurementOut[0];
  KeyDrop[$MeasurementOut, 0];
  VickState[{1, new}, rest]
] /; Length[mat] == 1

(* See, e.g., Gallier (2001) for the Cartan-Dieudonné theorem. *)
(* The matrix mat describes a list of dressed Dirac fermion modes
      b[j] := Sum[mat[[i,j]] c[j], {j, 2n}]
   in terms of Majorana fermion modes c[k]. *)
VickMeasurement[mat_?MatrixQ, ___][in_VickState] :=
  Fold[VickMeasurement[{#2}][#1]&, in, Identity /@ mat] /;
  Length[mat] > 1
(* NOTE: Identity /@ mat is necessary because mat is usually a SparseArray. *)
(* NOTE: The dressed fermion modes associated with different rows in matrix mat do not have to be mutually orthogonal. Only required is that each row gives a proper dressed fermion mode, independently of other rows. *)


theVickMeasurement[{aa_?MatrixQ, bb_?MatrixQ}, cvr_?MatrixQ] := Module[
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
VickMeasurement /:
ToDirac[msr_VickMeasurement] := NambuMeasurement[msr]

(* conversion *)
VickMeasurement /:
NambuMeasurement[VickMeasurement[mat:({}|_?MatrixQ), opts___?OptionQ], more___?OptionQ] :=
  NambuMeasurement[ToDirac /@ mat, more, opts]   (* NOT ToDirac @ mat. *)


(* NOTE: This happens when no measurement is performed such as in RandomVickCircuit. *)
FermionCount[VickMeasurement[{}, ___?OptionQ]] = 0

FermionCount[VickMeasurement[mat_?MatrixQ, ___?OptionQ]] := 
  Last[Dimensions @ mat]/2

Readout[VickMeasurement[m_?MatrixQ, ___]] := 
  Readout[First @ m] /; Length[m] == 1

Readout[VickMeasurement[m_?MatrixQ, ___]] := 
  Map[Readout, m]


theFermionModes::usage = "theFermionModes[msr] returns the list of Dirac fermion modes being probed by VickMeasurement msr. Used in Graphics[VickCircuit[...], ...]."

theFermionModes[VickMeasurement[{}, ___]] = {}

theFermionModes[msr:VickMeasurement[_?MatrixQ, ___]] := Module[
  { mat = First[NambuMeasurement @ msr] },
  mat = First @ PartitionInto[mat, {1, 2}];
  mat = Map[ZeroQ, mat, {3}];
  Union @ Flatten @ Map[Position[#, False]&, mat, {2}]
]

(**** </VickMeasurement> ****)


(**** <VickMeasurementOdds> ****)

VickMeasurementOdds::usage = "VickMeasurementOdds[msr] represents the probability distribution for the occupations of the dressed modes."

VickMeasurementOdds[msr_VickMeasurement] :=
  VickMeasurementOdds[First @ msr]

VickMeasurementOdds[mat_?MatrixQ][in_VickState] :=
  VickMeasurementOdds[mat][ in[[1, 2]] ]

VickMeasurementOdds[mat_?MatrixQ][cvr_?MatrixQ] := Module[
  { mm = theVickMeasurementOdds /@ mat,
    pp },
  pp = Through[ mm[cvr] ];
  pp = AssociationThread[
    Tuples[{0, 1}, Length @ mat],
    Times @@@ Tuples[pp]  
  ];
  If[Length[mm] == 1, KeyMap[First, pp], pp]
]

theVickMeasurementOdds[vec_?VectorQ][cvr_?MatrixQ] := Module[
  { aa, bb, dd, mm, pp },
  {aa, bb} = VickMeasurementKernel[N @ vec];
  mm = One[Dimensions @ cvr] - aa . cvr; (* D = -A *)
  pp = Quiet[Sqrt[Det @ mm]/2, {Det::luc}]; (* prefactor = 1/2 *)
  pp = Ramp[Re @ pp]; (* Ramp and Re to quickly handle numerical errors. *)
  {Ramp[1 - pp], pp}
]

(**** </VickMeasurementOdds> ****)


(**** <VickMeasurementKernel> ****)

VickMeasurementKernel::usage = "VickMeasurementKernel[vec] returns {A, B, nrm}, where A and B are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], -A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] Dagger[b]**b \[Rho] Dagger[b]**b, where b := Sum[vec[[k]] c[k], {k, 2n}] is a dressed Dirac fermion mode superposed of bare Majorana modes c[k]."
(* NOTE: The following two code pieces were for vec in the (2k-1, 2k)-encoding of Majorana modes in VickMeasurementKernel[vec]. However, they still work for vec in the (k, n+k)-encoding. *)

(* For measurement outcome = 1 *)
VickMeasurementKernel[k_Integer, n_Integer] := {
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
(* NOTE: This is intended for VickMeasurement (rather than VickMap), and returns only matrices A and B (but not D). *)

VickMeasurementKernel[vec_?VectorQ] := Module[
  { n = Length[vec]/2,
    xx, yy, aa, bb, nn, trs },
  xx = Re[N @ vec];  (* Notice N[...]; otherwise, it may take very long *)
  yy = Im[N @ vec];
  (* verify the dressed fermion mode *)
  If[ OddQ[Length @ vec] || Not @ ZeroQ[xx . yy] || Norm[xx] != Norm[yy],
    Message[VickMeasurement::dressed, vec];
    Return @ {One[2n], One[2n], 0}
  ];
  (* The Cartan-Dieudonné theorem *)
  {aa, bb} = VickMeasurementKernel[1, n]; (* nn is ignored *)
  trs = HouseholderMatrix[{xx, yy}];
  { trs . aa . Transpose[trs],
    trs . bb . Transpose[trs] }
]
(* NOTE: This is intended for VickMeasurement (rather than VickMap), and for efficiency, it does NOT calculate the NormSquare of vec. Furthermore, it returns only matrices A and B (but not D). *)

(**** </VickMeasurementKernel> ****)


RandomVickMeasurement::usage = "RandomVickMeasurement[k, n] randomly generates a VickMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomVickMeasurement[n] randomly selects k from {1,2,\[Ellipsis],n}."

RandomVickMeasurement[k_Integer, n_Integer] :=
  VickMeasurement @ RandomNambuMeasurement[k, n]

RandomVickMeasurement[n_Integer] :=
  VickMeasurement @ RandomNambuMeasurement[n]


(**** <VickMapKernel> ****)

VickMapKernel::usage = "VickMapKernel[type, mat] returns {A, B, D, nrm}, where A, B and D are 2n\[Times]2n real matrices and nrm is a list of prefactors. The 4n\[Times]4n matrix {{A, B}, {-Transpose[B], A}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] Sum[L[k]**\[Rho]**Dagger[L[k]], {k, m}]. For type=1, L[k] are linear combination of Majorana operators. For type=2, L[k] are bilinear combination of Majorana operators."

(* L[k] := b[k] *)
VickMapKernel[1, mat_?MatrixQ] := Module[
  {aa, bb, nn},
  {aa, bb, nn} = Transpose @ Map[VickFlopKernel, mat];
  aa = SparseArray[aa];
  {aa, SparseArray @ bb, aa, nn}
]

(* L[k] := Dagger[a[k]]**a[k], where a[k] are bare Dirac fermion mode. *)
VickMapKernel[2, kk:{___Integer}, n_Integer] := Module[
  {aa, bb},
  {aa, bb} = Transpose @ Map[VickMeasurementKernel[#, n]&, kk];
  aa = SparseArray[aa];
  {aa, SparseArray @ bb, -aa, ConstantArray[1/2, Length @ kk]}
]

(* L[k] := Dagger[b[k]]**b[k], b[i] := Sum[mat[[i, j]]**c[j], {j, 2n}] *)
VickMapKernel[2, mat_?MatrixQ] := Module[
  { nn = Map[NormSquare, mat],
    aa, bb },
  {aa, bb} = Transpose @ Map[VickMeasurementKernel, mat];
  aa = SparseArray[aa];
  {aa, SparseArray @ bb, -aa, 2*nn^2}
  (* Notice the power of 2 (rathern than just nn) and the factor of 2. *)
]
(* NOTE: This is intended for VickMap (rather than VickMeasurement), and returns all matrices A, B, and D as well as the squared norms of rows of matrix mat. *)

(**** </VickMapKernel> ****)


(**** <VickMap> ****)

(* conversion *)
VickMap[jmp_VickJump, ___] :=
  VickMap[VickMapKernel[1, First @ jmp], False]

(* conversion *)
VickMap[msr_VickMeasurement, flag___] :=
  VickMap[VickMapKernel[2, First @ msr], flag]

(* default flag *)
VickMap[spec_] = VickMap[spec, False]

(* On VickState *)
VickMap[spec_, flag_][VickState[{_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  VickState[{1, VickMap[spec, flag] @ cvr}, rest]

(* On the covariance matrix *)
VickMap[{aa_?ArrayQ, bb_?ArrayQ, dd_?ArrayQ, nn_?VectorQ}, True][cvr_?MatrixQ] := Module[
  { m = Length[nn],
    ak, bk, dk, mm, id, pp, k },
  id = ConstantArray[One[Dimensions @ cvr], m];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm]/2, Det::luc];
  (* NOTE: A factor of 1/2 because this case is supposed to be the measurement of a fermion mode. *)
  pp = Ramp[Re @ pp];
  pp = Join[nn*Ramp[1-pp], nn*pp];
  (* NOTE: More precisely, here needs to be an additional factor 2 because the prefactors nn from VickMapKernel[2, ...] already contains the factor of 1/2. It is ignored because it is a global factor anyway. *)
  k = RandomChoice[pp -> Range[2m]];
  If[ k <= m,
    (* projection by a**Dagger[a] *)
    $VickMapOut = {k, 0};
    ak = -aa[[k]];
    dk = -dd[[k]],
    (* projection by Dagger[a]**a *)
    k -= m;
    $VickMapOut = {k, 1};
    ak = aa[[k]];
    dk = dd[[k]];
  ];
  bk = bb[[k]];
  mm = One[Dimensions @ dk] + dk . cvr;
  ak + bk . cvr . Inverse[mm] . Transpose[bk]
]

(**** </VickMap> ****)


(**** <VickMapOdds> ****)

VickMapOdds::usage = "VickMapOdds[mat][in] returns the probabilities for the projective process \[Rho] \[RightTeeArrow] p[i]**\[Rho]**p[i], where p[i]:=Dagger[b[i]]**b[i] and b[i]:=Sum[mat[[[i,j]] c[j], {j, 2n}] are the dressed Dirac fermion modes consisting of bare Majorana fermion modes c[j]."

(* conversion *)
VickMapOdds[jmp_VickJump, ___] :=
  VickMapOdds[VickMapKernel[1, First @ jmp], False]

(* conversion *)
VickMapOdds[VickMeasurement[mat_?MatrixQ, ___], flag___] :=
  VickMapOdds[VickMapKernel[2, mat], flag]

(* default flag *)
VickMapOdds[spec_] = VickMapOdds[spec, False]

(* canonicalize *)
VickMapOdds[{_?ArrayQ, _?ArrayQ, dd_?ArrayQ, nn_?VectorQ}, flag_] :=
  VickMapOdds[{dd, nn}, flag]

(* On VickState *)
VickMapOdds[VickMeasurement[kk:{__Integer}, ___], flag_][in_VickState] := 
  VickMapOdds[VickMapKernel[2, kk, FermionCount @ in], flag][in]

(* On VickState *)
VickMapOdds[spec_, flag_][VickState[{_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  VickMapOdds[spec, flag][cvr]

(* On covariance matrix *)
VickMapOdds[{dd_?ArrayQ, nn_?VectorQ}, False][cvr_?MatrixQ] := Module[
  { mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], Length @ nn];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm], Det::luc];
  pp = nn*Ramp[Re @ pp];
  Normalize[pp, Norm[#, 1]&]
]

VickMapOdds[{dd_?ArrayQ, nn_?VectorQ}, True][cvr_?MatrixQ] := Module[
  { mm, id, pp },
  id = ConstantArray[One[Dimensions @ cvr], Length @ nn];
  mm = id + dd . cvr;
  pp = Quiet[Sqrt[Det /@ mm]/2, Det::luc];
  pp = Ramp[Re @ pp];
  pp = Join[nn*Ramp[1-pp], nn*pp];
  Normalize[pp, Norm[#, 1]&]
]

(**** </VickMapOdds> ****)


(**** <VickGreenFunction> ****)

VickGreenFunction::usage = "VickGreenFunction[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to VickState ws.\nVickGreenFunction[ns, {k1, k2, \[Ellipsis]}] returns NambuGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NambuState ns.\nVickGreenFunction[in] is equivalent to VickGreenFunction[in, Range[n]], where n is the number of fermion modes for which input Vick or Nambu state in is defined for.\nVickGreenFunction[data] or VickGreenFunction[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Vick or BdG states.\nVickGreenFunction[{k1, k2, \[Ellipsis]}] represents an operator form of VickGreenFunction to be applied to Vick or Nambu state."

(* shortcut *)
VickGreenFunction[ws_VickState] :=
  VickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for BdG modelsl *)
VickGreenFunction[VickState[{_, cvr_?MatrixQ}, ___], kk:{___Integer}] := Module[
  {grn, anm},
  {grn, anm} = First @ NambuGreen[VickCovariance @ cvr];
  NambuGreen @ {grn[[kk, kk]], anm[[kk, kk]]}
]

(* for large data *)
VickGreenFunction[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickGreenFunction[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState]&]

(**** </VickGreenFunction> ****)


(**** <VickOccupation> ****)

(* canonical form for normal models *)
VickOccupation[ws:VickState[{_?NumericQ, _?barrenSpecQ}, ___], kk:{___Integer}] := Module[
  { grn = WickGreenFunction[ws, kk] },
  grn = 1 - Diagonal[grn];
  grn[[kk]]
]


(* for large data *)
VickOccupation[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = N @ Whole @ Dimensions[data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickOccupation[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState]&]

(**** </VickOccupation> ****)


(**** <VickPurity> ****)

VickPurity::usage = "VickPurity[ws] returns the purity of Vick state ws."

VickPurity[ws_VickState] := Module[
  { grn = NambuGreen[ws],
    val },
  val = Eigenvalues[Normal @ grn];
  val = 2*val - 1;
  Power[2, -FermionCount[ws]] * Sqrt[Whole[1 + val^2]]
]

(**** </VickPurity> ****)


(**** <VickDensityMatrix> ****)

VickDensityMatrix::usage = "VickDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function grn associated with a fermionic Gaussian state.\nVickDensityMatrix[ws] returns the density matrix corresponding to Vick state ws."

VickDensityMatrix::num = "Only numerical matrices are allowed."

(* canonical form for normal models *)
VickDensityMatrix[grn_?MatrixQ] := Module[
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
  cc = MapThread[Dot, {ConjugateTranspose /@ cc, cc}];
  cc = MapThread[#1*id + (1-2*#1)*#2&, {gg, cc}];
  Dot @@ cc
] /; If[ MatrixQ[grn, NumericQ], True,
  Message[VickDensityMatrix::num];
  False
]

(* essentially normal models *)
VickDensityMatrix[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  VickDensityMatrix[grn] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
VickDensityMatrix[grn_NambuGreen] := Module[
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
  cc = Join[cc, ConjugateTranspose /@ cc];

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
  Message[VickDensityMatrix::num];
  False
]

(* canonicalization *)
VickDensityMatrix[grn_?NambuMatrixQ] := VickDensityMatrix[NambuGreen @ grn]

VickDensityMatrix[cvr_VickCovariance] :=
  VickDensityMatrix[NambuGreen @ cvr]

(**** </VickDensityMatrix> ****)


(**** <VickCircuit> ****)

VickCircuit::usage = "VickCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit consisting of BdG gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes."

VickCircuit /:
MakeBoxes[wc:VickCircuit[gg_List, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    VickCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", FermionCount @ wc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", Short @ gg }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

VickCircuit /: 
NonCommutativeQ[_VickCircuit] = True

VickCircuit /:
MultiplyKind[_VickCircuit] = Fermion

VickCircuit /:
Multiply[pre___, wc_VickCircuit, in_VickState] :=
  Multiply[pre, wc @ in]

VickCircuit[gg_List, ___][in_VickState] :=
  Fold[#2[#1]&, in, gg]


VickCircuit /:
Show[wc_VickCircuit, rest___] := Graphics[wc, rest]

VickCircuit /:
Graphics[wc:VickCircuit[gg_List], more___?OptionQ] := Module[
  { c },
  Let[Fermion, c];
  Graphics[wc, c, more]
]

VickCircuit /:
Graphics[wc:VickCircuit[gg_List, opts___?OptionQ], c_Symbol?FermionQ, more___?OptionQ] := Module[
  { n = FermionCount[wc],
    cc, qc },
  cc = c[Range @ n];
  qc = gg /. {
    VickCircuit[{}] -> "Spacer",
    ws_VickCircuit :> Graphics[ws],
    ws_VickState :> ExpressionFor[ws, cc],
    VickMeasurement[{}, ___] -> "Spacer",
    ws_VickMeasurement :> Map[Gate[{c[#]}, "Shape" -> "Measurement"]&, theFermionModes @ ws],
    VickUnitary[_?MatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    VickUnitary[_?MatrixQ, any___?OptionQ] :> Gate[cc, any],
    VickUnitary[_?MatrixQ, _, any___?OptionQ] :> Gate[cc, any]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]

(**** </VickCircuit> ****)


(**** <RandomVickCircuit> ****)

RandomVickCircuit::usage = "RandomVickCircuit[{uni, p}, dep] generate a random quantum circuit on non-interacting fermion modes, where layers of unitary gate uni (either VickUnitary[\[Ellipsis]] or NambuUnitary[\[Ellipsis]]) alternate with layers of measurements (VickMeasurement[\[Ellipsis]]) on fermion modes selected randomly with probability p to form an overall depth dep.\nRandomVickCircuit[{ham, pdf, p}, k] unitary layers of random unitary gate uni=Exp[-I ham \[Tau]] with single-particle Hamiltonian ham (either n\[Times]n Hermitian matrix or NambuHermitian[\[Ellipsis]]) and the random evolution time \[Tau] distributed according to the probability distribution function pdf.\nRandomVickCircuit[{ham, p}, dep] assumes that the evolution time is uniformly distributed over the interval [0,2\[Pi] n/max], where max is the maximum of the absolute values of the entries of ham.\nRandomVickCircuit[ham, dep] generates a circuit for n fermion modes where each unitary layer corresponds to time evolution U=exp[-I ham \[Tau]] with the evolution time \[Tau] distributed by P(\[Tau])\[Proportional]exp[-n \[Tau]] and each measurement layer measures a fermion mode with probability p=1/n."

(* canonicalization *)
RandomVickCircuit[{uu_NambuUnitary, p_?NumericQ}, k_Integer] :=
  RandomVickCircuit[{VickUnitary @ uu, p}, k]

(* fixed interaction time *)
RandomVickCircuit[{uu_VickUnitary, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[uu],
      mm },
    mm = RandomPick[Range @ n, p, k];
    VickCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[VickMeasurement[#, n]&, mm]
    ]
  ]

(* canonicalization *)
RandomVickCircuit[{ham_NambuHermitian, spec__}, k_Integer] :=
  RandomVickCircuit[{VickHermitian @ ham, spec}, k]

(* arbitrary distribution of evolution time *)
RandomVickCircuit[{ham_VickHermitian, pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      hh = First[ham],
      ab, tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = Map[VickUnitary[MatrixExp[hh*#]]&, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[VickMeasurement[#, n]&, mm];
    VickCircuit @ Riffle[uu, mm]
  ]

(* uniform distribution of evolution time *)
RandomVickCircuit[{ham_VickHermitian, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      max, pdf },
    max = Max[Abs @ First @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    RandomVickCircuit[{ham, pdf, p}, k]
  ]

(* canonicalization *)
RandomVickCircuit[ham_NambuHermitian, k_Integer] :=
  RandomVickCircuit[VickHermitian[ham], k]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
RandomVickCircuit[ham_VickHermitian, k_Integer] := Module[
    { n = FermionCount[ham] },
    RandomVickCircuit[{ham, ExponentialDistribution[n], 1./n}, k]
  ]

(**** </RandomVickCircuit> ****)


(**** <RandomVickCircuitSimulate> ****)

RandomVickCircuitSimulate::usage = "RandomVickCircuitSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomVickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

Options[RandomVickCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RWC"
}

$RandomVickCircuitPatterns = Alternatives[
  {_VickUnitary, _?NumericQ}, 
  {_NambuUnitary, _?NumericQ},
  {_VickHermitian, _, _?NumericQ},
  {_VickHermitian, _?NumericQ},
  {_NambuHermitian, _, _?NumericQ},
  {_NambuHermitian, _?NumericQ},
  _VickHermitian,
  _NambuHermitian
];

RandomVickCircuitSimulate[in_, spec_, depth_Integer, opts___?OptionQ] := 
  RandomVickCircuitSimulate[in, spec, {depth, 2}, opts]

RandomVickCircuitSimulate[
  in_VickState,
  spec:$RandomVickCircuitPatterns,
  {depth_Integer, ds:(_Integer|All)},
  opts:OptionsPattern[{RandomVickCircuit, RandomVickCircuitSimulate}]
] := 
Module[
  { progress = k = 0,
    data, more, qc, n, m },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  data = Table[
    qc = RandomVickCircuit[spec, depth];
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
    more = Join[{opts}, Options @ RandomVickCircuitSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
]

(**** </RandomVickCircuitSimulate> ****)


(**** <WickNonunitary> ****)

WickNonunitary /:
MakeBoxes[op:WickNonunitary[{fac_?NumericQ, non_?barrenMatrixQ}, rest___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickNonunitary, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ non },
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Transformation: ", ArrayShort @ First @ non }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* shortcut *)
WickNonunitary[{ham:{_?MatrixQ, 0}, dmp:{_?MatrixQ, 0}}, rest___] :=
  WickNonunitary[{1, {MatrixExp[-I*(ham - I*dmp)], 0}}, rest]

(* shortcut *)
WickNonunitary[
  { {ham_?MatrixQ, 0}, 
    jmp:(_WickJump|_VickMeasurement)
  }, rest___
] := WickNonunitary[{WickHermitian @ {ham, 0}, jmp}, rest]

(* shortcut *)
WickNonunitary[
  { WickHermitian[{ham_?MatrixQ, 0}, ___], 
    jmp:(WickJump|WickMeasurement)[_?barrenJumpQ, ___]
  }, rest___
] := Module[
  {dmp, gmm},
  {dmp, gmm} = WickDamping[jmp];
  WickNonunitary[
    { Exp[-gmm],
      {MatrixExp[-I*(ham-I*dmp)], 0}
    },
    rest ]
]

WickNonunitary /:
MatrixForm @ WickNonunitary[{fac_?NumericQ, {non_?MatrixQ, 0}}, rest___] :=
  MatrixForm[non]

WickNonunitary /:
ArrayShort @ WickNonunitary[{fac_?NumericQ, {non_?MatrixQ, 0}}, rest___] :=
  ArrayShort[non]

WickNonunitary /:
Dagger @ WickNonunitary[{fac_?NumericQ, {non_?MatrixQ, 0}}, rest___] :=
  WickNonunitary[{Conjugate @ fac, {ConjugateTranspose @ non, 0}}, rest]

WickNonunitary /:
Matrix[WickNonunitary[{fac_?NumericQ, {non_?MatrixQ, 0}}, ___]] := Module[
  { n = FermionCount @ {non, 0},
    log = MatrixLog[non],
    mat, wjt },
  wjt = theWignerJordan[n];
  mat = Dot[Transpose[Conjugate @ wjt, {3, 1, 2}], log, wjt];
  mat = TensorContract[mat, {{1, 3}}];
  SparseArray[fac * MatrixExp[mat]]
]

(* acting on WickState *)
WickNonunitary[{fac_?NumericQ, {non_?MatrixQ, 0}}, rest___][in_WickState] := Module[
  { trs = in[[1, 2, 1]],
    nrm = in[[1, 1]],
    rmt },
  trs = non . ConjugateTranspose[trs];
  {trs, rmt} = QRDecomposition[trs];
  nrm *= AbsSquare[fac] * AbsSquare[Det @ rmt];
  WickState[{nrm, {trs, 0}}, Options[in]]
] /; MatrixQ[ in[[1, 2, 1]] ]

(* vacuum state *)
WickNonunitary[{fac_?NumericQ, {_?MatrixQ, 0}}, rest___][in_WickState] :=
  fac * in

(**** </WickNonunitary> ****)


RandomWickNonunitary::usage = "RandomWickNonunitary[n] randomly constructs a WickNonunitary operator on n fermion modes."

RandomWickNonunitary[n_Integer, opts___?OptionQ] :=
  WickNonunitary[Re @ {RandomAntisymmetric[2n], RandomAntisymmetric[2n], 0}, opts]


(**** <WickDamping> ****)

WickDamping[WickJump[jmp_?barrenJumpQ, ___]] := Module[
  { aa = jmp[[1]] /. {None -> {}},
    bb = jmp[[2]] /. {None -> {}} },
  aa = ConjugateTranspose[aa] . aa / 2;
  bb = Transpose[bb] . Conjugate[bb] / 2;
  {aa - bb, If[bb === 0, 0, Re @ Tr @ bb]}
]

WickDamping[WickMeasurement[msr_?barrenJumpQ, ___]] := Module[
  { aa = msr[[1]] /. {None -> {}},
    bb = msr[[2]] /. {None -> {}},
    nn },
  nn = NormSquare /@ aa;
  aa = Dot[ConjugateTranspose @ aa, nn * aa] / 2;
  nn = NormSquare /@ bb;
  bb = Dot[Transpose @ bb, nn * Conjugate[bb]] / 2;
  {aa - bb, If[bb === 0, 0, Re @ Tr @ bb]}
]

(**** </WickDamping> ****)


(**** <WickSimulate> ****)

(* canonicalization *)
WickSimulate[in_WickState, ham:{_?MatrixQ, 0}, rest__] :=
  WickSimulate[in, WickHermitian @ ham, rest]

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


(**** <VickMonitor> ****)

VickMonitor::usage = "VickMonitor[in, ham, msr, {nt, dt}] solves the problem of continuous monitoring of a non-interacting many-fermion system by using the Monte Carlo simulation method. The model is specified by the single-particle Hamiltonian ham in the VickHermitian form, and the dressed fermion modes the occupation numbers of which to be monitored are specified by measurement msr in the VickMeasurement form. The simulation starts from the initial state IN in the VickState form at time 0 and goes nt time steps of size dt."

VickMonitor::mat = "The matrix in the first argument of VickMonitor must be a real anti-symmetric matrix."

VickMonitor::num = "The Hamiltonian matrix `` needs to be numeric."

Options[VickMonitor] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "WM"
}

VickMonitor[in_VickState, ham_?MatrixQ, rest___] :=
  VickMonitor[in, VickHermitian @ ham, rest] /;
  If[ VickHermitianQ[ham], True,
    Message[VickNonitor::mat]; False
  ]

VickMonitor[in_VickState, ham_?NambuMatrixQ, rest___] :=
  VickMonitor[in, VickHermitian @ NambuHermitian @ ham, rest]

VickMonitor[in_VickState, ham_NambuHermitian, rest___] :=
  VickMonitor[in, VickHermitian @ ham, rest]

VickMonitor[in_VickState, ham_VickHermitian, msr_NambuMeasurement, rest___] :=
  VickMonitor[in, ham, VickMeasurement @ msr, rest]

VickMonitor[
  in_VickState,
  ham_VickHermitian,
  spec:{_?NumericQ, _?NumericQ, ___},
  opts___?OptionQ
] := Module[
  { n = FermionCount[in],
    map },
  map = VickMap[VickMapKernel[2, Range @ n, n], True];
  VickMonitor[in, ham, map, spec, opts]
]

VickMonitor[
  in_VickState,
  ham_VickHermitian,
  msr_VickMeasurement,
  spec:{_?NumericQ, _?NumericQ, ___},
  opts___?OptionQ
] := VickMonitor[in, ham, VickMap[msr, True], spec, opts]

VickMonitor[
  in_VickState,
  ham_VickHermitian,
  map_VickMap,
  {tau_?NumericQ, dt_?NumericQ},
  opts___?OptionQ
] := VickMonitor[in, ham, map, {tau, dt, All}, opts]

VickMonitor[
  in_VickState,
  ham_VickHermitian,
  map_VickMap,
  {tau_?NumericQ, dt_?NumericQ, ds:(_Integer|All)},
  opts:OptionsPattern[]
] := Module[
  { n = OptionValue["Samples"],
    progress = 0,
    uni, data, more },
  uni = VickUnitary @ MatrixExp[N @ First[ham]*dt];
  (* simulation *)
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  data = Table[
    progress = k / N[n];
    theVickMonitor[in, uni, map, {tau, dt}][[1;;All;;ds]],
    {k, n}
  ];
  (* save data *)
  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ VickMonitor];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
] /; If[ MatrixQ[First @ ham, NumericQ], True,
  Message[VickNonitor::num, First @ ham];
  False
]

theVickMonitor[
  in_VickState,
  uni_VickUnitary,
  map_VickMap,
  {tau_?NumericQ, dt_?NumericQ}
] := Module[
  { t = dt,
    res = {in},
    new = in,
    gmm },
  gmm = 2 * Total @ map[[1, 4]];
  (* NOTE: Here, the additional factor 2 is required because the prefactors map[[1, 4]] from VickMapKernel[2, ...] already contains the factor of 1/2 associated with projection Dagger[b]**b. *)
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

(**** </VickMonitor> ****)


(**** <VickLindbladSolve> ****)
(* See also Bravyi (2012a). *)

VickLindbladSolve::usage = "VickLindbladSolve[ham, jmp, in, t] solves the Lindblad equation associated with the Hamiltonia ham and a set of quantum jump operators jmp, and returns the fermionic Gaussian mixed state at t."

VickLindbladSolve[ham_NambuHermitian, rest__] :=
  VickLindbladSolve[VickHermitian @ ham, rest]

VickLindbladSolve[ham_VickHermitian, jmp_NambuJump, rest__] :=
  VickLindbladSolve[ham, VickJump @ jmp, rest]

VickLindbladSolve[ham_VickHermitian, msr_NambuMeasurement, rest__] :=
  VickLindbladSolve[ham, VickMeasurement @ msr, rest]


VickLindbladSolve[ham_, jmp_, in_, t_?NumericQ, rest___] :=
  First @ VickLindbladSolve[ham, jmp, in, {{t}}, rest]

VickLindbladSolve[ham_, jmp_, in_, {t0_?NumericQ, tn_?NumericQ}, rest___] :=
  VickLindbladSolve[ham, jmp, in, {Range[t0, tn]}, rest]

VickLindbladSolve[ham_, jmp_, in_,
  {ti_?NumericQ, tf_?NumericQ, dt_?NumericQ},
  rest___
] := VickLindbladSolve[ham, jmp, in, {Range[ti, tf, dt]}, rest]

VickLindbladSolve[ham_VickHermitian, jmp_, in_VickState, rest__] :=
  Map[VickState, VickLindbladSolve[ham, jmp, in[[1, 2]], rest]]

VickLindbladSolve[ham_VickHermitian, jmp_, in_VickCovariance, rest__] :=
  Map[VickCovariance, VickLindbladSolve[ham, jmp, First @ in, rest]]

VickLindbladSolve[ham_, msr_VickMeasurement, cvr_, {tt_?VectorQ}] :=
 VickLindbladSolve[ham, msr, cvr, {tt}, False]


(* quantum jump operators are linear in fermion operators *)
VickLindbladSolve[
  ham_VickHermitian,
  jmp_VickJump,
  cvr_?MatrixQ,
  {tt_?VectorQ}
] := Module[
  { xx, vp, vv },
  {xx, vp} = VickLindbladKernel[ham, jmp];
  vv = cvr - vp;
  xx = Map[MatrixExp[xx*#]&, tt];
  vv = Map[vp + # . vv . Transpose[#]&, xx];
  Map[(# - Transpose[#])/2&, vv]
]

(* quantum jump operators are projection operators *)
VickLindbladSolve[
  ham_VickHermitian,
  msr_VickMeasurement,
  cvr_?MatrixQ,
  {tt_?VectorQ},
  flag:(True | False)
] := Module[
  { vec = UpperTriangular[cvr, 1],
    spr, out },
  spr = VickLindbladKernel[ham, msr, flag];
  out = Map[MatrixExp[spr*#] . vec&, tt];
  Map[AntisymmetricMatrix, out]
]


VickLindbladKernel::usage = "VickLindbladKernel[ham, jmp] returns a pair {krn, sol}, where krn is the kernel of the vectorized equation for the Majorana covariance matrix and sol is a stationary solution.\nVickLindbladKernel[ham, msr] or VickLindbladKernel[ham, msr, flag] returns krn."

VickLindbladKernel[ham_NambuHermitian, jmp_] :=
  VickLindbladKernel[VickHermitian @ ham, jmp]

VickLindbladKernel[ham_, jmp_NambuJump] :=
  VickLindbladKernel[ham, VickJump @ jmp]

VickLindbladKernel[ham_, msr_NambuMeasurement] :=
  VickLindbladKernel[ham, VickMeasurement @ msr]


(* VickJump *)
VickLindbladKernel[ham_VickHermitian, jmp_VickJump] := Module[
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

(* VickMeasurement *)
VickLindbladKernel[ham_VickHermitian, msr_VickMeasurement] := Module[
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

VickLindbladKernel[ham_VickHermitian, msr_VickMeasurement, False] :=
  VickLindbladKernel[ham, msr]

VickLindbladKernel[ham_VickHermitian, msr_VickMeasurement, True] :=
  VickLindbladKernel[ham, Surd[2, 4]*msr]

(**** </VickLindbladSolve> ****)


(**** <VickSteadyState> ****)
(* See also Bravyi (2012a). *)

VickSteadyState::usage = "VickSteadyState[ham, jmp, in] returns the steady-state solution (i.e., a fermionic Gaussian mixed state) to the Lindblad equation associated with the Hamiltonian ham and a set of quantum jump operators jmp.\nVickSteadyState[ham, msr, in] assumes that the Lindblad operators are projective and given by Vick measurement msr."

VickSteadyState::more = "The Lindblad equation has additional steady states."

VickSteadyState[ham_NambuHermitian, rest__] :=
  VickSteadyState[VickHermitian @ ham, rest]

VickSteadyState[ham_VickHermitian, jmp_NambuJump, rest__] :=
  VickSteadyState[ham, VickJump @ jmp, rest]

VickSteadyState[ham_VickHermitian, msr_NambuMeasurement, rest__] :=
  VickSteadyState[ham, VickMeasurement @ msr, rest]


VickSteadyState[ham_VickHermitian, jmp_, in_VickState, rest___] :=
  VickState @ VickSteadyState[ham, jmp, in[[1, 2]], rest]

VickSteadyState[ham_VickHermitian, jmp_, in_VickCovariance, rest___] :=
  VickCovariance @ VickSteadyState[ham, jmp, First @ in, rest]

VickSteadyState[ham_, msr_VickMeasurement, cvr_] :=
 VickSteadyState[ham, msr, cvr, False]


(* quantum jump operators are linear in fermion operators *)
VickSteadyState[
  ham_VickHermitian,
  jmp_VickJump,
  cvr_?MatrixQ
] := Module[
  { xx, vp, vv },
  {xx, vp} = VickLindbladKernel[ham, jmp];
  If[ZeroQ[Det @ xx], Message[VickSteadyState::more]];
  Return[vp]
]

(* quantum jump operators are projection operators *)
VickSteadyState[
  ham_VickHermitian,
  msr_VickMeasurement,
  cvr_?MatrixQ,
  flag:(True | False)
] := Module[
  { in = UpperTriangular[cvr, 1],
    spr, vec, out },
  spr = VickLindbladKernel[ham, msr, flag];
  vec = Eigenvectors[N @ spr];
  out = Inverse[Transpose @ vec] . in;
  out = Last[vec] * Last[out];
  AntisymmetricMatrix[Re @ out]
]

(**** </VickSteadyState> ****)


(**** <FermionCount> ****)

FermionCount[WickNonunitary[{_?NumericQ, {non_?MatrixQ, 0}}, ___]] := 
  Last[Dimensions @ non]

FermionCount[WickState[{_?NumericQ, {n_Integer, 0}}, ___]] = n

FermionCount[WickState[{_?NumericQ, {trs_?MatrixQ, 0}}, ___]] := 
  Last[Dimensions @ trs]


FermionCount[VickHermitian[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[VickUnitary[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[VickJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[VickOperator[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[VickCircuit[gg_List, ___?OptionQ]] := Max[FermionCount /@ gg]

(**** </FermionCount> ****)

End[] (* Fermionic quantum computation *)


(**********************************************************************)
(**********************************************************************)


Begin["`Private`"] (* quantum information theory for fermionic Gaussian states *)

(**** <VickTimeReversalMoment> ****)

VickTimeReversalMoment::usage = "VickTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nVickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to VickTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

VickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[VickTimeReversalMoment] = { 
  "Epsilon" -> 1.25*^-16
  (* "Epsilon" -> 1.25*^-20 *)
}

(* canoncialization *)
VickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  VickTimeReversalMoment[alpha, NambuGreen @ {grn, 0}, kk, opts]

(* canoncialization *)
VickTimeReversalMoment[alpha_, grn_?NambuMatrixQ, rest__] := 
  VickTimeReversalMoment[alpha, NambuGreen @ grn, rest]

(* canoncial form *)
VickTimeReversalMoment[
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
  OptionsPattern[VickTimeReversalMoment]
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

(**** </VickTimeReversalMoment> ****)


(**** <VickLogarithmicNegtivity> ****)

VickLogarithmicNegativity::usage = "VickLogarithmicNegativity[grn, {k1, k2, \[Ellipsis]}] returns the logarithmic entanglement negativity between the subsystem consisting of fermion modes {k1, k2,\[Ellipsis]}\[Subset]{1,2,\[Ellipsis],n} in the Vick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nVickLogarithmicNegativity[NambuGreen[{grn, anm}], {k1, k2,\[Ellipsis]}] or VickLogarithmicNegativity[{grn, anm}, {k1, k2,\[Ellipsis]}] returns the logarithmic negativity in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nVickLogarithmicNegativity[state, {k1, k2, \[Ellipsis]}] is equivalent to VickLogarithmicNegativity[VickGreenFunction[state], {k1, k2,\[Ellipsis]}] for state = VickState or NambuState."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

Options[VickLogarithmicNegativity] = Options[VickTimeReversalMoment]

(* operator form *)
VickLogarithmicNegativity[kk:{__Integer}][any_] :=
  VickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[VickLogarithmicNegativity, "Epsilon"]]

(* special case *)
VickLogarithmicNegativity[obj_, {}, ___] = 0

(* for large data *)
VickLogarithmicNegativity[data_?ArrayQ, kk:{___Integer}, opts___?OptionQ] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickLogarithmicNegativity[#, kk, opts])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState | _VickCovariance | _NambuGreen]&]

(* shortcut *)
VickLogarithmicNegativity[ws_VickState, rest__] :=
  VickLogarithmicNegativity[VickCovariance @ ws, rest]

(* shortcut *)
VickLogarithmicNegativity[cvr_VickCovariance, kk:{__Integer}, opts:OptionsPattern[]] :=
  VickLogarithmicNegativity[ NambuGreen[cvr], kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]


(* normal models *)
VickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___] := 0 /;
  Length[grn] == Length[kk]

(* Canonical form for normal models *)
(* SEE ALSO: Shpurian and Ryu (2019b) and  Alba and Carollo (2023) *)
VickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___] := Module[
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
VickLogarithmicNegativity[grn_NambuGreen, kk:{__Integer}, ___] :=
  VickLogarithmicNegativity[grn[[1, 1]], kk] /; ArrayZeroQ[grn[[1, 2]]] 

VickLogarithmicNegativity[grn_NambuGreen, kk:{__Integer}, ___] := 0 /;
  FermionCount[grn] == Length[kk]

(* Canonical form for BdG models *)
VickLogarithmicNegativity[
  grn_NambuGreen, kk:{__Integer}, 
  opts:OptionsPattern[]
] := VickTimeReversalMoment[1/2, grn, kk, opts,
    "Epsilon" -> OptionValue["Epsilon"]
  ]

(* canonicalization *)
VickLogarithmicNegativity[grn_?NambuMatrixQ, rest__] :=
  VickLogarithmicNegativity[NambuGreen @ grn, rest]

(**** </VickLogarithmicNegtivity> ****)

(**** <VickEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
VickEntropy::usage = "VickEntropy[grn] returns the von Neumann entropy of a fermionic Gaussian state characterized by the matrix grn of single-particle Green's functions. VickEntropy[NambuGreen[{grn, anm}]] or VickEntropy[{grn, anm}] considers a fermionic Gaussian state characterized by matrices grn and anm of normal and anomalous Green's functions."

(* canonical form for normal models *)
VickEntropy[grn_?MatrixQ] :=
  QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn]

(* for BdG models *)
VickEntropy[NambuGreen[{grn_?MatrixQ, anm_?MatrixQ}, ___]] :=
  VickEntropy[grn] /; ArrayZeroQ[anm]

(* for BdG models *)
VickEntropy[{grn_?MatrixQ, anm_?MatrixQ}] :=
  VickEntropy[grn] /; ArrayZeroQ[anm]

(* for BdG models *)
VickEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___]] :=
  VickEntropy[Normal @ grn] / 2

(* for BdG models *)
VickEntropy[grn:{_?MatrixQ, _?MatrixQ}] :=
  VickEntropy[Normal @ NambuGreen @ grn] / 2


VickEntropy[cvr_VickCovariance] := Module[
  { vv = First[cvr],
    id },
  id = One[Dimensions @ vv];
  (QuantumLog[2, (id - I*vv)/2] + QuantumLog[2, (id + I*vv)/2]) / 2
]

VickEntropy[in_VickState] :=
  VickEntropy[VickCovariance @ in]

(**** </VickEntropy> ****)


(**** <VickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
VickEntanglementEntropy::usage = "VickEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Vick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nVickEntanglementEntropy[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or VickEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nVickEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] is equivalent to VickEntanglementEntropy[VickGreenFunction[state, {k1, k2, \[Ellipsis]}], {k1, k2, \[Ellipsis]}] for Vick or BdG state.\nVickEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of VickEntanglementEtropy to be applied to Green's functions, Vick or Nambu state."

(* operator form *)
VickEntanglementEntropy[kk:{___Integer}][any_] :=
  VickEntanglementEntropy[any, kk]

(* special case *)
VickEntanglementEntropy[any_, {}] = 0

(* for large data *)
VickEntanglementEntropy[data_?ArrayQ, kk:{___Integer}] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickEntanglementEntropy[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState | _VickCovariance | _NambuGreen]&]

(* directly from covariance matrix *)
VickEntanglementEntropy[VickCovariance[cvr_?MatrixQ, ___], kk:{__Integer}] := Module[
  { jj = Join[kk, kk + Length[cvr]/2] },
  VickEntropy[ VickCovariance @ cvr[[jj, jj]] ]
]

(* shortcut *)
VickEntanglementEntropy[in_VickState, kk:{___Integer}] :=
  VickEntanglementEntropy[VickCovariance @ in, kk]

(* for normal models *)
VickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  VickEntropy @ grn[[kk, kk]]

(* for BdG models *)
VickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] :=
  VickEntanglementEntropy[grn, kk] /; ArrayZeroQ[anm]

(* canonical form for BdG models *)
VickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  VickEntropy @ Normal @ NambuGreen[{gg, ff}] / 2
]

(* canonicalization for BdG models *)
VickEntanglementEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___], kk:{__Integer}] :=
  VickEntanglementEntropy[First @ grn, kk]

(**** </VickEntanglementEntropy> ****)


(**** <VickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
VickMutualInformation::usage = "VickMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Vick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nVickMutualInformation[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or VickMutualInformation[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nVickMutualInformation[state, {k1, k2, \[Ellipsis]}] is equivalent to VickMutualInformation[VickGreenFunction[state], {k1, k2, \[Ellipsis]}] for Vick or BdG state.\nVickMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of VickEntanglementEtropy to be applied to Green's functions, Vick or Nambu state."

(* operator form *)
VickMutualInformation[kk:{__Integer}][any_] :=
  VickMutualInformation[any, kk]

(* shortcut *)
VickMutualInformation[ws_VickState, kk:{__Integer}] :=
  VickMutualInformation[VickCovariance @ ws, kk]

(* directly from covariance matrix *)
VickMutualInformation[cvr:VickCovariance[vv_?MatrixQ, ___], kk:{__Integer}] := Module[
  { n = FermionCount[cvr],
    ii, jj, ll },
  ll = Supplement[Range @ n, kk];
  ii = Riffle[kk, n + kk];
  jj = Riffle[ll, n + ll];
  ( VickEntropy[ VickCovariance @ vv[[ii, ii]] ] + 
    VickEntropy[ VickCovariance @ vv[[jj, jj]] ] -
    VickEntropy[ VickCovariance @ vv ]
  ) / 2
]

(* for large data *)
VickMutualInformation[data_?ArrayQ, kk:{___Integer}] := Module[
  { progress = i = 0,
    dim = Whole[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickMutualInformation[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState | _VickCovariance | _NambuGreen]&]


(* canonical form for normal models *)
VickMutualInformation[gg_?MatrixQ, kk:{__Integer}] :=With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  VickEntropy[ gg[[kk, kk]] ] + VickEntropy[ gg[[ll, ll]] ] - VickEntropy[ gg ]
]

(* BdG models *)
VickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] :=
  VickMutualInformation[gg, kk] /; ArrayZeroQ[ff]

(* canonical form for BdG models *)
VickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] := With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  ( VickEntropy[Normal @ NambuGreen @ {gg[[kk, kk]], ff[[kk, kk]]}] +
    VickEntropy[Normal @ NambuGreen @ {gg[[ll, ll]], ff[[ll, ll]]}] -
    VickEntropy[Normal @ NambuGreen @ {gg, ff}]
  ) / 2
]

(* canonicalization for BdG models *)
VickMutualInformation[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], kk:{__Integer}] :=
  VickMutualInformation[{gg, ff}, kk]

(**** </VickMutualInformation> ****)

End[] (* quantum information theory for fermionic Gaussian states *)


EndPackage[]
