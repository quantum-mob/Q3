BeginPackage["Q3`"]

{ NamvoMatrix, NamvoMatrixQ };
{ NamvoGaussian, NamvoUnitary, NamvoHermitian, NamvoGreen };
{ NamvoOne, NamvoZero };
{ NamvoGaussian, NamvoUnitary, NamvoHermitian, NamvoGreen };
{ RandomNamvoGaussian, RandomNamvoUnitary, RandomNamvoHermitian, RandomNamvoGreen };

{ ToDiracMatrix, ToMajoranaMatrix };

{ BdGState, RandomBdGState };
{ BdGUnitary, RandomBdGUnitary };
{ BdGJump, BdGOperator, BdGOperatorFrom, BdGElements };
{ RandomBdGOperator };

{ BdGCollapse };

{ BdGCovariance, FromBdGCovariance };
{ BdGPureQ };

{ HouseholderMatrix };

Begin["`Private`"] (* Tools for Namvo matrices *)

AddElaborationPatterns[_BdGOperator, _NamvoUnitary, _NamvoGaussian];

(**** <NamvoMatrix> ****)

NamvoMatrix::usage = "NamvoMatrix[mat] r the two n\[Times]n independent blocks at the upper-left and upper-right corners of the 2n\[Times]2n matrix mat."

NamvoMatrix::odd = "Matrix `` has odd dimenions."

NamvoMatrix[mat_?SquareMatrixQ] := Module[
  { n = (Length[mat] + 1) / 2 },
  Message[NamvoMatrix::odd, mat];
  { mat[[ ;;n, ;;n]], Zero[n] }
] /; OddQ[Length @ mat]

NamvoMatrix[mat_?SquareMatrixQ] := 
  First @ PartitionInto[mat, {2, 2}]

NamvoMatrix[{mat_?SquareMatrixQ, 0}] :=
  {mat, Zero @ Dimensions @ mat}

(**** </NamvoMatrix> ****)


(**** <NamvoMatrixQ> ****)

NamvoMatrixQ::usage = "NamvoMatrixQ[{u, v}] returns True if the pair {u, v} of square matrices are compatible in size.\nNamvoMatrixQ[{u, v}, test] requires also that test yield True when applied to each of the array elements in {u, v}. "

NamvoMatrixQ[uv:{_?SquareMatrixQ, _?SquareMatrixQ}] := ArrayQ[uv]

NamvoMatrixQ[uv:{_?SquareMatrixQ, _?SquareMatrixQ}, test_] := ArrayQ[uv, 3, test]

NamvoMatrixQ[_] = False

NamvoMatrixQ[_, _] = False

(**** </NamvoMatrixQ> ****)


NamvoOne::usage = "NamvoOne[n] returns the pair {One[n], Zero[{n, n}]}, which represents the identity matrix in the Namvo space."

NamvoOne[n_Integer] := {One @ n, Zero @ {n, n}}


NamvoZero::usage = "NamvoZero[n] returns the pair {Zero[{n, n}], Zero[{n, n}]}, which represents the zero matrix in the Namvo space."

NamvoZero[n_Integer] := {Zero @ {n, n}, Zero @ {n, n}}


(**** <NamvoHermitian> ****)

NamvoHermitian::usage = "NamvoHermitian[{ham, del}] represents a quadratic Hermitian operator in the Namvo space that is characterized by an n\[Times]n Hamitian matrix ham and an n\[Times]n anti-symmetric matrix del."

NamvoHermitian /:
MakeBoxes[op:NamvoHermitian[mm_?NamvoMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    NamvoHermitian, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ mm }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, mm] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[mm]

(* zero in the Namvo space *)
NamvoHermitian[0, n_Integer, rest___] :=
  NamvoHermitian[NamvoZero[n], rest]

(* zero in the Namvo space *)
(* backward compatibility *)
NamvoHermitian[0, cc:{___?FermionQ}, rest___] :=
  NamvoHermitian[0, Length @ cc, rest]

(* identity in the Namvo space *)
NamvoHermitian[1, n_Integer, rest___] :=
  NamvoHermitian[NamvoOne[n], rest]

(* identity in the Namvo space *)
(* backward compatibility *)
NamvoHermitian[1, cc:{___?FermionQ}, rest___] :=
  NamvoHermitian[1, Length @ cc, rest]

NamvoHermitian[mat_?SquareMatrixQ, rest___] :=
  NamvoHermitian[NamvoMatrix @ mat, rest]

NamvoHermitian[{mat_?SquareMatrixQ, 0}, rest___] :=
  NamvoHermitian[NamvoMatrix @ {mat, 0}, rest]

NamvoHermitian[NamvoHermitian[uv_?NamvoMatrixQ, rest___], more___] :=
  NamvoHermitian[uv, more, rest]


NamvoHermitian /:
MatrixForm @ NamvoHermitian[mm_?NamvoMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NamvoHermitian /:
ArrayShort @ NamvoHermitian[mm_?NamvoMatrixQ, rest___] :=
  Map[ArrayShort, mm]

NamvoHermitian /:
Normal @ NamvoHermitian[{ham_, del_}, ___] :=
  ArrayFlatten @ {
    {ham, del},
    {Topple[del], -Transpose[ham]}
  }

NamvoHermitian /:
Dagger[ham:NamvoHermitian[{_?MatrixQ, _?MatrixQ}, rest___]] = ham

NamvoHermitian /:
Plus[NamvoHermitian[a_, any___], NamvoHermitian[b_, other___]] :=
  NamvoHermitian[a + b, any, other]

NamvoHermitian /:
Times[z_, NamvoHermitian[mm_, rest___]] :=
  NamvoHermitian[z * mm, rest]

NamvoHermitian /:
Dot[NamvoHermitian[a_, any___], NamvoHermitian[b_, other___]] :=
  NamvoHermitian[theNamvoDot[a, b], any, other]


NamvoHermitian /:
ExpressionFor[op:NamvoHermitian[_?NamvoMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

NamvoHermitian /: (* fallback *)
ExpressionFor[op_NamvoHermitian, ___] = op


NamvoHermitian /:
Matrix[NamvoHermitian[ham_?NamvoMatrixQ, ___], ss:{__?SpeciesQ}] := Module[
  { ff = Select[ss, FermionQ],
    rr = Select[ss, Not @* FermionQ],
    mm, nf },
  nf = Length[ff];
  
  (* Jordan-Wigner transformation *)
  mm = Table[PadRight[Table[3, k-1], nf], {k, nf}] + 4*One[nf];
  mm = ThePauli /@ mm;
  mm = Join[mm, Topple /@ mm];

  TensorContract[
    Transpose[Topple /@ mm, {3, 1, 2}] . Normal[NamvoHermitian @ ham] . mm / 2,
    {{2, 3}}
  ]
]

NamvoHermitian /: (* fallback *)
Matrix[op_NamvoHermitian, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


NamvoHermitian /:
NonCommutativeQ[_NamvoHermitian] = True

NamvoHermitian /:
MultiplyKind[_NamvoHermitian] = Fermion

(**** </NamvoHermitian> ****)


(**** <NamvoUnitary> ****)

NamvoUnitary::usage = "NamvoUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Namvo space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively."

NamvoUnitary /:
MakeBoxes[op:NamvoUnitary[uv_?NamvoMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    NamvoUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ uv }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, uv] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[uv]

(* zero in the Namvo space *)
NamvoUnitary[0, n_Integer, rest___] :=
  NamvoUnitary[NamvoZero[n], rest]

(* zero in the Namvo space *)
(* backward compatibility *)
NamvoUnitary[0, cc:{___?FermionQ}, rest___] :=
  NamvoUnitary[0, Length @ cc, rest]

(* identity in the Namvo space *)
NamvoUnitary[1, n_Integer, rest___] :=
  NamvoUnitary[NamvoOne[n], rest]

(* identity in the Namvo space *)
(* backward compatibility *)
NamvoUnitary[1, cc:{___?FermionQ}, rest___] :=
  NamvoUnitary[1, Length @ cc, rest]

NamvoUnitary[mat_?SquareMatrixQ, rest___] :=
  NamvoUnitary[NamvoMatrix @ mat, rest]

NamvoUnitary[{mat_?SquareMatrixQ, 0}, rest___] :=
  NamvoUnitary[NamvoMatrix @ {mat, 0}, rest]

NamvoUnitary[NamvoUnitary[uv_?NamvoMatrixQ, rest___], more___] :=
  NamvoUnitary[uv, more, rest]


NamvoUnitary /:
MatrixForm @ NamvoUnitary[mm_?NamvoMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NamvoUnitary /:
ArrayShort @ NamvoUnitary[mm_?NamvoMatrixQ, rest___] :=
  Map[ArrayShort, mm]

NamvoUnitary /:
Normal @ NamvoUnitary[{u_?MatrixQ, v_?MatrixQ}, ___] :=
  ArrayFlatten @ {
    {u, v},
    Conjugate @ {v, u}
  }

NamvoUnitary /:
Dagger @ NamvoUnitary[{u_?MatrixQ, v_?MatrixQ}, rest___] :=
  NamvoUnitary[{Topple @ u, Transpose @ v}, rest]

NamvoUnitary /:
Plus[NamvoUnitary[a_, any___], NamvoUnitary[b_, other___]] :=
  NamvoUnitary[a + b, any, other]

NamvoUnitary /:
Times[z_, NamvoUnitary[mm_, rest___]] :=
  NamvoUnitary[z * mm, rest]

NamvoUnitary /:
Dot[NamvoUnitary[a_, any___], NamvoUnitary[b_, other___]] :=
  NamvoUnitary[theNamvoDot[a, b], any, other]


NamvoUnitary /:
ExpressionFor[op:NamvoUnitary[uv_?NamvoMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

NamvoUnitary /: (* fallback *)
ExpressionFor[op_NamvoUnitary, ___] = op


NamvoUnitary /:
Matrix[op:NamvoUnitary[uv_?NamvoMatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { barH = -I*MatrixLog[Normal @ op] },
  MatrixExp[I*Matrix[NamvoHermitian @ barH, ss]]
]

NamvoUnitary /: (* fallback *)
Matrix[op_NamvoUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


NamvoUnitary /:
NonCommutativeQ[_NamvoUnitary] = True

NamvoUnitary /:
MultiplyKind[_NamvoUnitary] = Fermion

NamvoUnitary /:
Multiply[pre___, opr_NamvoUnitary, fs_Ket] := Multiply[pre, opr[BdGState @ fs]]

NamvoUnitary /:
Multiply[pre___, opr_NamvoUnitary, ws_BdGState] := Multiply[pre, opr[ws]]

NamvoUnitary[uv_?NamvoMatrixQ, ___][in:BdGState[{_?NumericQ, _?MatrixQ}, ___]] :=
  BdGUnitary[uv][in]

(**** </NamvoUnitary> ****)


(**** <NamvoGreen> ****)

NamvoGreen::usage = "NamvoGreen[{grn, anm}] represents the matrix of single-particle Green's functions in the Namvo space that is characterized by the n\[Times]n matrix grn of normal Green's functions and the n\[Times]n matrix anm of anomalous Green's functions."

NamvoGreen /:
MakeBoxes[grn:NamvoGreen[mm_?NamvoMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    NamvoGreen, grn, None,
    { BoxForm`SummaryItem @ { "Modes: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ mm }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, mm] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[mm]

(* zero in the Namvo space *)
NamvoGreen[0, n_Integer, rest___] :=
  NamvoGreen[NamvoZero[n], rest]

(* zero in the Namvo space *)
(* backward compatibility *)
NamvoGreen[0, cc:{___?FermionQ}, rest___] :=
  NamvoGreen[0, Length @ cc, rest]

(* identity in the Namvo space *)
NamvoGreen[1, n_Integer, rest___] :=
  NamvoGreen[NamvoOne[n], cc, rest]

(* identity in the Namvo space *)
(* backward compatibility *)
NamvoGreen[1, cc:{___?FermionQ}, rest___] :=
  NamvoGreen[1, Length @ cc]


NamvoGreen[mat_?SquareMatrixQ, rest___] :=
  NamvoGreen[NamvoMatrix @ mat, rest]

NamvoGreen[{mat_?SquareMatrixQ, 0}, rest___] :=
  NamvoGreen[NamvoMatrix @ {mat, 0}, rest]

NamvoGreen[NamvoGreen[grn_?NamvoMatrixQ, rest___], more___] :=
  NamvoGreen[grn, more, rest]


NamvoGreen /:
MatrixForm @ NamvoGreen[mm_?NamvoMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NamvoGreen /:
ArrayShort @ NamvoGreen[mm_?NamvoMatrixQ, rest___] :=
  Map[ArrayShort, mm]

NamvoGreen /:
Normal @ NamvoGreen[{g_, f_}, ___] :=
  ArrayFlatten @ {
    {g, f},
    {Topple[f], One[Dimensions @ g] - Transpose[g]}
  }

NamvoGreen /:
Dagger[grn:NamvoGreen[{_?MatrixQ, _?MatrixQ}, rest___]] = grn

NamvoGreen /:
Plus[NamvoGreen[a_, any___], NamvoGreen[b_, other___]] :=
  NamvoGreen[a + b, any, other]

NamvoGreen /:
Times[z_, NamvoGreen[mm_, rest___]] :=
  NamvoGreen[z * mm, rest]

(**** </NamvoGreen> ****)


RandomNamvoUnitary::usage = "RandomNamvoUnitary[n] returns a random NamvoUnitary[{u, v}], where u and v are the n\[Times]n upper-left and upper-right blocks of the resulting Bogoliubov-de Gennes transformation matrix."

RandomNamvoUnitary[n_Integer, rest___] := With[
  { barH = Normal[RandomNamvoHermitian @ n] },
  NamvoUnitary[MatrixExp[I barH], rest]
]

(* backward compatibility *)
RandomNamvoUnitary[cc:{__?FermionQ}, rest___] :=
  RandomNamvoUnitary[Length @ cc]


RandomNamvoHermitian::usage = "RandomNamvoHermitian[n] returns a random NamvoHermitian[{ham, del}], where ham is an n\[Times]n Hermitian matrix and del is an n\[Times]n anti-symmetric matrix."

RandomNamvoHermitian[n_Integer, rest___] :=
  NamvoHermitian[{RandomHermitian[n], RandomAntisymmetric[n]}, rest]

(* backward compatibility *)
RandomNamvoHermitian[cc:{__?FermionQ}, rest___] :=
  RandomNamvoHermitian[Length @ cc, rest]


RandomNamvoGreen::usage = "RandomNamvoGreen[n] returns a random NamvoGreen[{grn, anm}], where grn is an n\[Times]n matrix representing the normal Green's function and anm is an n\[Times]n anti-symmetric matrix representing the anomalous Green's function."

RandomNamvoGreen[n_Integer, rest___] := Module[
  { trs = Normal @ RandomNamvoUnitary[n],
    val = RandomReal[{0, 1}, n] },
  val = DiagonalMatrix @ Join[val, 1 - val];
  NamvoGreen[trs . val . Topple[trs], rest]
]

(* backward compatibility *)
RandomNamvoGreen[cc:{__?FermionQ}, rest___] :=
  RandomNamvoGreen[Length @ cc, rest]


(**** <theNamvoDot> ****)

theNamvoDot::usage = "theNamvoDot[{u1,v1}, {u2,v2}] returns the reduced Namvo matrix corresponding to the matrix multiplication of two full Namvo matrices corresponding to {u1, v1} and {u2, v2}, respectively."

SetAttributes[theNamvoDot, Flat]

theNamvoDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

theNamvoDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barU := {{U, V}, Conjugate @ {V, U}} *)

(**** </theNamvoDot> ****)


(**** <HouseholderMatrix> ****)

HouseholderMatrix::usage = "HouseholderMatrix[v] returns the Householder reflection matrix m = (2|w><w|-1) such that m.v is proportional to {1, 0, 0, \[Ellipsis]}.\nHouseholderMatrix[v, k] returns the Householder reflection matrix that brings vector v to the k'th unit vector."

HouseholderMatrix::numeric = "`` is supposed to be a numeric vector."

HouseholderMatrix::neg = "The second input argument `` must be larger than 1."

HouseholderMatrix[vec_?VectorQ] := Module[
  { fac = Norm[vec],
    phs = Exp[I * Arg[First @ vec]],
    new },
  fac *= phs;
  new = vec;
  new[[1]] += fac;
  new = Normalize[new];
  (2*Dyad[new, new] - One[Length @ vec]) * Conjugate[phs]
] /; If[ VectorQ[vec, NumericQ], True,
    Message[HouseholderMatrix::numeric, ArrayShort @ vec];
    False
  ]

HouseholderMatrix[vec_?VectorQ, k_Integer] := With[
  { mat = HouseholderMatrix[Drop[vec, k-1]] },
  CirclePlus[One[k-1], mat]
] /; If[ k > 1, True,
    Message[HouseholderMatrix::neg, k];
    False
  ]

(**** </HouseholderMatrix> ****)


End[] (* Tools for Namvo matrices *)



Begin["`Private`"] (* Fermionic quantum computation in the Namvo space *)

AddElaborationPatterns[_BdGState];


(**** <ToDiracMatrix> ****)

ToDiracMatrix::usage = "ToDiracMatrix[n] returns the 2n\[Times]2n matrix representing the canonical transformation from Majorana to Dirac fermions."

ToDiracMatrix[n_Integer] := With[
  { trs = CircleTimes[One[n], {{1, I}}] },
  Join[trs, Conjugate @ trs]
] / 2
(* NOTE: The returned matrix U is NOT unitary; Topple[U].U = 1/2 *)


ToMajoranaMatrix::usage = "ToMajoranaMatrix[n] returns the 2n\[Times]2n matrix representing the canonical transformation from Dirac to Majorana fermions."

ToMajoranaMatrix[n_Integer] :=
  2 * Topple[ToDiracMatrix @ n]

(**** </ToDiracMatrix> ****)


(**** <BdGState> ****)

BdGState::usage = "BdGState[uv, trs] represents a many-body quantum state for non-interacting fermion modes that has undergone the overall Bogoliubov-de Gennes (BdG) type time evolution in the Namvo space specified by reduced Namvo matrix uv and decoherence processes (including measurements) specified by matrix trs."

BdGState::complex = "The covariance matrix `` must be a real anti-symmetric matrix."

BdGState::bad = "Unsupported form of Namvo state ``."

BdGState /:
MakeBoxes[ws:BdGState[{fac_?NumericQ, cvr_?MatrixQ}, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BdGState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ws },
      BoxForm`SummaryItem @ { "Prefactor: ", fac }
    },
    { BoxForm`SummaryItem @ { "Covariance matrix: ", ArrayShort @ cvr }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; EvenQ[Length @ cvr]

(* initialization by occupation numbers *)
BdGState[vv_/;VectorQ[vv, BinaryQ], n_Integer, rest___] := Module[
  { ww = DiagonalMatrix @ PadRight[vv, n, vv],
    gg, cv },
  gg = NamvoGreen @ {One[n] - ww, 0};
  cv = BdGCovariance[gg];
  BdGState[{1, cv}, rest]
]

BdGState[{fac_, cvr_?MatrixQ}, rest___] := With[
  { re = Re[cvr] },
  If[ ArrayZeroQ[Im @ cvr], 
    BdGState[{fac, Re @ cvr}, rest],
    Message[BdGState::complex, ArrayShort @ cvr];
    BdGState[{fac, (re - Transpose[re])/2}, rest]
  ]
] /; Not[arrayRealQ @ cvr]


(* initialization *)
BdGState[Rule[n_Integer, vv_/;VectorQ[vv, BinaryQ]], rest___] :=
  BdGState[vv, n, rest]

(* initialization *)
BdGState[Rule[cc:{__?FermionQ}, vv_/;VectorQ[vv, BinaryQ]], rest___] :=
  BdGState[vv, Length @ cc, rest]

(* initialization *)
BdGState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  BdGState[Lookup[aa, cc], Length @ cc]
]


BdGState /:
NormSquare[BdGState[{fac_?NumericQ, _?MatrixQ}, ___]] := fac

BdGState /:
Norm[BdGState[{fac_?NumericQ, _?MatrixQ}, ___]] := Sqrt[fac]


BdGState /:
Normalize[BdGState[{fac_?NumericQ, _?MatrixQ}, rest___]] :=
  BdGState[{1, cvr}, rest]


BdGState /:
Times[z_?NumericQ, BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := 
  BdGState[{fac * AbsSquare[z], cvr}, rest]


BdGState /:
ExpressionFor[ws:BdGState[{_?NumericQ, _?MatrixQ}, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ ws, cc]


BdGState /: (* mixed states *)
Matrix[BdGState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] :=
  fac * WickDensityMatrix[FromBdGCovariance @ cvr]
(* NOTE: It might be more efficient to use the Murnaghan's canonical form; see Paardekooper (1971) and Humeniuk and Mitrik (2018). Here, we do not try it because this function is intended for elementary tests anyway. *)

BdGState /: (* pure states *)
Matrix[ws:BdGState[{fac_?NumericQ, cvr_?MatrixQ}, ___]] := Module[
  { n = FermionCount[ws],
    xx, yy, xy,
    vv, mm, pp, id },
  (* Jordan-Wigner transformation *)
  xx = SparseArray[
    { {i_, i_} -> 1,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  xx = ThePauli /@ Normal[xx]; (* bare odd modes *)
  
  yy = SparseArray[
    { {i_, i_} -> 2,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  yy = ThePauli /@ Normal[yy]; (* bare even modes *)
  
  xy = Riffle[xx, yy];

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
] /; BdGPureQ[cvr]


BdGState /:
NonCommutativeQ[_BdGState] = True

BdGState /:
MultiplyKind[_BdGState] = Fermion

(**** </BdGState> ****)


(**** <BdGPureQ> ****)

BdGPureQ[BdGState[{_, cvr_?MatrixQ}, ___]] :=
  BdGPureQ[cvr]

BdGPureQ[cvr_?MatrixQ] := Module[
  { val },
  val = First @ SkewTridiagonalize[cvr];
  val = Diagonal[val, 1][[1;; ;;2]];
  ArrayZeroQ[Abs[val] - 1]
]

(**** </BdGPureQ> ****)


RandomBdGState::usage = "RandomBdGState[k, n] randomly generates a depth-k BdG state with half filling on n fermion modes\nRandomBdGState[n] selects depth k randomly from {1, 2,\[Ellipsis], n}."

RandomBdGState[n_Integer] := Module[
  { yy, mm, in },
  yy = CircleTimes[One[n], I*ThePauli[2]];
  mm = RandomOrthogonal[2n];
  mm = Transpose[mm] . yy . mm;
  BdGState[{1, mm}]
]

(* backward compatibility *)
RandomBdGState[cc:{__?FermionQ}] :=
  RandomBdGState[Length @ cc]


(**** <BdGConjugateReverse> ****)

BdGConjugateReverse::usage = "BdGConjugateReverse[mat] returns the reverse of {Conjugate[B], Conjugate[A]} for matrix mat with block structure mat = {A, B}."

BdGConjugateReverse[ops_?MatrixQ] := Conjugate[Reverse @ ops]

(**** </BdGConjugateReverse> ****)


(**** <BdGUnitary> ****)

BdGUnitary::usage = "BdGUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Namvo space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively."

BdGUnitary /:
MakeBoxes[op:BdGUnitary[uu_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    BdGUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ uu }
    },
    { BoxForm`SummaryItem @ { "Transformation matrix: ", ArrayShort @ uu }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

(* zero in the Namvo space *)
BdGUnitary[0, n_Integer, rest___] :=
  BdGUnitary[Zero @ {2n, 2n}, rest]

(* identity in the Namvo space *)
BdGUnitary[1, n_Integer, rest___] :=
  BdGUnitary[One[2n], rest]

BdGUnitary[BdGUnitary[mat_?MatrixQ, rest___], more___] :=
  BdGUnitary[mat, more, rest]


BdGUnitary /:
MatrixForm @ BdGUnitary[mm_?MatrixQ, rest___] :=
  MatrixForm[mm]

BdGUnitary /:
ArrayShort @ BdGUnitary[mm_?MatrixQ, rest___] :=
  ArrayShort[mm]


BdGUnitary /:
Dagger @ BdGUnitary[mat_?MatrixQ, rest___] :=
  BdGUnitary[Transpose @ mat, rest] /;
  If[ arrayRealQ[mat], True,
    Message[BdGUnitary::complex, ArrayShort @ mat];
    False    
  ]

BdGUnitary /:
Plus[BdGUnitary[a_, any___], BdGUnitary[b_, other___]] :=
  BdGUnitary[a + b, any, other]

BdGUnitary /:
Times[z_, BdGUnitary[mm_, rest___]] :=
  BdGUnitary[z * mm, rest]

BdGUnitary /:
Dot[BdGUnitary[a_, any___], BdGUnitary[b_, other___]] :=
  BdGUnitary[Dot[a, b], any, other]


BdGUnitary /:
ExpressionFor[op:BdGUnitary[_?MatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

BdGUnitary /: (* fallback *)
ExpressionFor[op_BdGUnitary, ___] = op


BdGUnitary /:
Matrix[uu:BdGUnitary[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := Module[
  { trs = Sqrt[2] * ToDiracMatrix[FermionCount @ uu],
    ham },
  ham = trs . mat . Topple[trs];
  ham = -I*MatrixLog[ham];
  MatrixExp[I*Matrix[NamvoHermitian @ ham, ss]]
]

BdGUnitary /: (* fallback *)
Matrix[op_BdGUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


BdGUnitary /:
NonCommutativeQ[_BdGUnitary] = True

BdGUnitary /:
MultiplyKind[_BdGUnitary] = Fermion

BdGUnitary /:
Multiply[pre___, opr_BdGUnitary, ws_BdGState] := Multiply[pre, opr[ws]]

BdGUnitary /:
Multiply[pre___, opr_BdGUnitary, fs_Ket] := Multiply[pre, opr[BdGState @ fs]]

BdGUnitary[trs_?MatrixQ, ___][BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { new = trs . cvr . Transpose[trs] },
  BdGState[{fac, new}, rest]
]


BdGUnitary[uv:NamvoUnitary[_?NamvoMatrixQ, ___]] := Module[
  { trs = Sqrt[2] * ToDiracMatrix[FermionCount @ uv] },
  trs = Topple[trs] . Normal[uv] . trs;
  BdGUnitary[trs, rest]
]

BdGUnitary[uv_?NamvoMatrixQ, rest___] :=
  BdGUnitary[NamvoUnitary @ uv]

(**** </BdGUnitary> ****)


RandomBdGUnitary[n_Integer, rest___] := Module[
  { mat = RandomOrthogonal[2n] },
  mat[[1, ;;]] *= Det[mat];
  (* NOTE: Make sure to have a SO(2n) matrix. *)
  BdGUnitary[mat, rest]
]


(**** <BdGCovariance> ****)

BdGCovariance::usage = "BdGCovariance[grn] returns the Majorana covariance matrix corresponding to the Green's function grn, given in the NambuGreen[...] form, of Dirac fermion modes."

BdGCovariance[grn_NamvoGreen] := Module[
  { n = FermionCount[grn],
    trs, cvr },
  trs = ToMajoranaMatrix[n];
  cvr = trs . Normal[grn] . Topple[trs];
  I * (cvr - One[2n])
]


FromBdGCovariance::usage = "FromBdGCovariance[cvr] returns the Green's function of Dirac fermions corresponding to the Majorana covariance matrix cvr."

FromBdGCovariance[cvr_?MatrixQ] := Module[
  { n = Length[cvr] / 2,
    trs },
  trs = ToDiracMatrix[n];
  NamvoGreen @ Dot[trs, One[2n] - I*cvr, Topple @ trs]
] /; If[ arrayRealQ[cvr], True,
    Message[BdGState::complex, ArrayShort @ cvr];
    False
  ]

(**** </BdGCovariance> ****)


(**** <FermionCount> ****)

FermionCount[BdGUnitary[mat_?MatrixQ, ___]] := Last[Dimensions @ mat] / 2

FermionCount[BdGOperator[mat_?MatrixQ, ___]] := Last[Dimensions @ mat] / 2

FermionCount[BdGState[{_?NumericQ, cvr_?MatrixQ}, ___]] := Length[cvr] / 2

(**** </FermionCount> ****)


(**** <BdGOperator> ****)

BdGOperator::usage = "BdGOperator[mat] represents a sequence of quantum operations that are linear combinations in the creation and annihilation operators of the fermion modes with coefficients given by the elements of matrix mat."

BdGOperator::flag = "Invalid flags ``; the flags must be binary digits."

BdGOperator /:
MakeBoxes[op:BdGOperator[mat_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest},
    m, n },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    BdGOperator, op, None,
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
BdGOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  BdGOperatorFrom[ops, cc, rest]


(* shortcut *)
BdGOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  { id = One[2n],
    mm = ToDiracMatrix[n],
    ii, kk, flag },
  {kk, flag} = Transpose[spec];
  ii = n*flag + kk;
  mm = id[[ii]] . mm;
  BdGOperator[mm, opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[BdGOperator::flag, flag]; False 
  ]
]

(* shortcut *)
BdGOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  BdGOperator[{spec}, n]


BdGOperator[{}, ___][any_] = any

BdGOperator[spec__][fs_Ket] := BdGOperator[spec][BdGState @ fs]

BdGOperator[mat_?MatrixQ, ___][in:BdGState[{_?NumericQ, _?MatrixQ}, ___]] :=
  Fold[#2[#1]&, in, Reverse @ Map[BdGFlop, mat]]


BdGOperator /:
Dagger @ BdGOperator[ops_?MatrixQ, rest___] :=
  BdGOperator[BdGConjugateReverse @ ops, rest]


BdGOperator /: 
NonCommutativeQ[_BdGOperator] = True

BdGOperator /:
MultiplyKind[_BdGOperator] = Fermion

BdGOperator /:
Multiply[pre___, opr_BdGOperator, ws_BdGState] := Multiply[pre, opr @ ws]

BdGOperator /:
Multiply[pre___, opr_BdGOperator, fs_Ket] := Multiply[pre, opr[BdGState @ fs]]


BdGOperator /:
Matrix[op:BdGOperator[mat_?MatrixQ, ___]] := Module[
  { c, cc },
  Let[Fermion,c];
  cc = c @ Range[FermionCount @ op];
  Matrix[op, cc]
]

BdGOperator /:
Matrix[in:BdGOperator[_?MatrixQ, ___]] := Module[
  { c, cc },
  Let[Fermion, c]
  cc = c @ Range[FermionCount @ in];
  Matrix[in, cc]
]

BdGOperator /:
Matrix[BdGOperator[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Dot @@ Matrix[BdGElements[mat, cc], ss]
]

BdGOperator /: (* fallback *)
Matrix[op_BdGOperator, rest___] := op * Matrix[1, rest]


BdGOperator /:
ExpressionFor[BdGOperator[mat_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Apply[Multiply, BdGElements[mat, cc]]  
]

BdGOperator /: (* fallback *)
ExpressionFor[op_BdGOperator, ___] = op 


BdGOperator /:
VacuumExpectation @ BdGOperator[trs_?MatrixQ, ___] :=
  Pfaffian @ WickMatrix[trs]

(**** </BdGOperator> ****)


RandomBdGOperator::usage = "RandomBdGOperator[k_Integer, n_Integer] ..."

RandomBdGOperator[k_Integer, n_Integer] :=
  BdGOperator[RandomMatrix[{k, 2n}]]

RandomBdGOperator[n_Integer] :=
  RandomBdGOperator[RandomInteger[{1, n}], n]


(**** <BdGJump> ****)

BdGJump /:
MakeBoxes[jmp:BdGJump[mat_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest},
    m, n },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    BdGJump, jmp, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Coefficients: ", ArrayShort @ ops }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]


(* canonicalization *)
BdGJump[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  BdGJump @@ BdGOperator[ops, cc, rest]


(* shortcut *)
BdGJump[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := 
  BdGJump @@ BdGOperator[spec, n, opts]

(* shortcut *)
BdGJump[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  BdGJump[{spec}, n, opts]


BdGJump[mat_?MatrixQ, ___][BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, mm, id, pp, new, k },
  {aa, bb, nn} = Transpose @ BdGJumpAction[mat];
  id = ConstantArray[One[Length @ cvr], Length @ mat];
  mm = id + aa . cvr;
  pp = nn * Sqrt[Det /@ mm];
  pp /= Total[pp];

  k = RandomChoice[pp -> Range[Length @ mat]];
  $BdGJumpOut = k;

  aa = aa[[k]];
  bb = bb[[k]];
  nn = nn[[k]];
  mm = mm[[k]];
  new = aa + bb . cvr . Inverse[mm] . Transpose[bb];
  BdGState[{1, new}, rest]
]


BdGJumpOdds[mat_?MatrixQ, ___][BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, mm, id, pp, new, k },
  {aa, bb, nn} = Transpose @ BdGJumpAction[mat];
  id = One[Length @ cvr];
  mm = Map[(id + #.cvr)&, aa];
  pp = nn * Sqrt[Det /@ mm];
  pp / Total[pp]
]


BdGFlop::usage = "BdGFlop[vec] represents ..."

BdGFlop[vec_?VectorQ, ___][BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { aa, bb, nn, id, mm, prb, new },
  {aa, bb, nn} = BdGJumpAction[vec];
  id = One[Dimensions @ aa];
  mm = id + aa . cvr;
  prb = nn * Sqrt[Det @ mm];
  If[ ZeroQ[prb],
    new = One[Dimensions @ mm],
    new = aa + bb . cvr . Inverse[mm] . Transpose[bb]
  ];
  BdGState[{fac * prb, new}, rest]
]


BdGJumpAction::usage = "BdGJumpAction[vec] returns {a, b, nrm}, where a and b are 2n\[Times]2n real matrices and nrm is the norm square of vec. The 4n\[Times]4n matrix {{a, b}, {-Transpose[b], a}} gives the Gaussian kernel of the Grassmann representation of the Gaussian map \[Rho] \[RightTeeArrow] c \[Rho] Dagger[c] with c := vec . {c1, c2, \[Ellipsis]}."

BdGJumpAction[vec_?VectorQ] := Module[
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

BdGJumpAction[mat_?MatrixQ] := Map[BdGJumpAction, mat]

(**** </BdGJump> ****)


(**** <BdGCollampse> ****)

BdGCollapse::usage = "BdGCollapse[{k, m}] represents the projection to the subspace of occupation number m (0 or 1) of fermion mode k.\n BdGCollapse[{vec, m}] deals with the occupation number of the dressed mode vec . {a1, a2, \[Ellipsis]}."

BdGCollapse::improper = "The first and second halves u and v of vector `` must be orthogonal, i.e., Dot[u, v]==0."


BdGCollapse[flag:(0|1), k_Integer][BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { prb, new },
  {prb, new} = theBdGCollapse[flag, k, cvr];
  BdGState[{fac * prb, new}, rest]
]

BdGCollapse[flag:(0|1), vec_?VectorQ][in:BdGState[{fac_?NumericQ, cvr_?MatrixQ}, rest___]] := Module[
  { prb, new },
  {prb, new} = theBdGCollapse[flag, vec, cvr];
  BdGState[{fac * prb, new}, rest]
]


theBdGCollapse[flag:(0|1), k_Integer, cvr_?MatrixQ] := Module[
  { n = Length[cvr] / 2,
    jj, ii, aa, bb, id, mm },
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
theBdGCollapse[flag:(0|1), vv_?VectorQ, cvr_?MatrixQ] := Module[
  { n = Length[cvr] / 2,
    ww, xx, yy, trs, prb, new },
  ww = vv . ToDiracMatrix[n];
  xx = Re[ww];
  yy = Im[ww];
  If[ Not @ ZeroQ[xx . yy],
    Message[BdGCollapse::improper, vv];
    Return[{1, cvr}]
  ];
  (* The Cartan-Dieudonné theorem *)
  trs = HouseholderMatrix[xx];
  trs = HouseholderMatrix[trs . yy, 2] . trs;
  new = trs . cvr . Transpose[trs];
  {prb, new} = theBdGCollapse[flag, 1, new];
  new = Transpose[trs] . new . trs;
  {prb, new}
]

(**** </BdGCollampse> ****)


(**** <BdGElements> ****)

BdGElements::usage = "BdGElements[spec, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion operators corresponding to specification spec."

BdGElements[mat_?MatrixQ, cc:{__?MajoranaQ}] := mat . cc

BdGElements[mat_?MatrixQ, cc:{__?FermionQ}] := Module[
  { trs = ToMajoranaMatrix[Length @ cc] },
  mat . trs . Join[cc, Dagger @ cc]
]


BdGElements[BdGOperator[trs_?MatrixQ, ___], cc:{__?MajoranaQ}] :=
  BdGElements[trs, cc]

BdGElements[BdGOperator[trs_?MatrixQ, ___], cc:{__?FermionQ}] :=
  BdGElements[trs, cc]

(**** </BdGElements> ****)


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


(**** <FermiMeasurement> ****)

FermiMeasurement /:
Multiply[pre___, msr:FermiMeasurement[_Integer|{__Integer}], ws_BdGState] :=
  Multiply[pre, msr @ ws]

FermiMeasurement[k_Integer][ws:BdGState[{fac_, cvr_}, ___]] := Module[
  { n = FermionCount[ws],
    nrm = NormSquare[ws],
    msr, dgr, mat, prb },
  msr = First @ BdGOperator[{{k, 0}, {k, 1}}, n]; (* c ** Dagger[c] *)
  msr = msr . Normal[NamvoUnitary @ uv];

  dgr = BdGConjugateReverse[trs];

  mat = WickMatrix @ Join[dgr, msr, trs];
  prb = Re @ Sqrt @ Quiet[Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= nrm;
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[k] = 0;
    BdGOperator[{{k, 0}, {k, 1}}, n][ws] / Sqrt[prb*nrm],
    $MeasurementOut[k] = 1;
    BdGOperator[{{k, 1}, {k, 0}}, n][ws] / Sqrt[(1-prb)*nrm]
  ]
]

(**** </FermiMeasurement> ****)


(**** <WickLogarithmicNegativity> ****)

(* canonical form for BdG models *)
WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(* canonicalization *)
WickLogarithmicNegativity[NamvoGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], rest__] :=
  WickLogarithmicNegativity[{gg, ff}, rest]

(* shortcut *)
WickLogarithmicNegativity[ws_BdGState, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickLogarithmicNegativity[WickGreenFunction[ws], kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(**** </WickLogarithmicNegativity> ****)


WickExpectation[ws:BdGState[uv_, bb_, ___]][BdGOperator[ops_?MatrixQ, ___]] := Module[
  { aa = BdGConjugateReverse[bb],
    mat },
  mat = WickMatrix @ Join[aa, ops . Normal[NamvoUnitary @ uv], bb];
  Pfaffian[mat] (* NOTE: The Namvo state is assumed to be normalized. *)
]


(**** <WickOccupation> ****)

(* shortcut *)
WickOccupation[ws_BdGState] :=
  WickOccupation[ws, Range @ FermionCount @ ws]

(* canonical form for BdG modelsl *)
WickOccupation[ws:BdGState[uv_?NamvoMatrixQ, qq_?MatrixQ, ___], kk:{___Integer}] := Module[
  { uu = Normal @ NamvoUnitary[uv],
    pp = BdGConjugateReverse[qq],
    aa, bb, wm, gg, nc },
  nc = FermionCount[ws];
  aa = uu[[ kk + nc ]];
  bb = uu[[ kk ]];

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = WickMatrix[pp];
  wm[[1, 3]] = WickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = WickMatrix[qq];

  nc = Length[kk];
  gg = Normal @ Zero[nc];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[i]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[i]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[i]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i]] = Quiet[Re @ Sqrt @ Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, nc}
  ];
  Return[gg]
  (* NOTE: The Namvo state is assumed to be normalized. *)
]

(* vacuum state *)
WickOccupation[ws:BdGState[uv_?NamvoMatrixQ, z_?NumericQ, ___], kk:{___Integer}] := Module[
  { uu = Normal @ NamvoUnitary[uv],
    aa, bb, wm, gg, nc },
  nc = FermionCount[ws];
  aa = uu[[ kk + nc ]];
  bb = uu[[ kk ]];

  nc = Length[kk];
  gg = Normal @ Zero[nc];
  Table[
    wm = N @ WickMatrix[{aa[[i]], bb[[i]]}];
    gg[[i]] = Quiet[Re @ Sqrt @ Det @ wm, Det::luc],
    {i, 1, nc}
  ];
  Return[gg]
]

(**** </WickOccupation> ****)


(**** <WickGreenFunction> ****)

(* shortcut *)
WickGreenFunction[ws_BdGState] :=
  WickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for BdG modelsl *)
WickGreenFunction[ws:BdGState[uv_?NamvoMatrixQ, qq_?MatrixQ, ___], kk:{___Integer}] := Module[
  { uu = Normal @ NamvoUnitary[uv],
    pp = BdGConjugateReverse[qq],
    aa, bb, wm, ff, gg, nn },
  nn = FermionCount[ws];
  aa = uu[[ kk ]];
  bb = uu[[ kk + nn ]];

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = WickMatrix[pp];
  wm[[1, 3]] = WickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = WickMatrix[qq];

  nn = Length[kk];
  gg = Normal @ Zero[{nn, nn}];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[i]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[i]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[i]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, nn}
  ];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, nn-1},
    {j, i+1, nn}
  ];

  ff = Normal @ Zero[{nn, nn}];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], aa[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], aa[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], aa[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    ff[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, nn-1},
    {j, i+1, nn}
  ];
  NamvoGreen[{gg, ff}, cc]
  (* NOTE: The Namvo state is assumed to be normalized. *)
]

(* vacuum state *)
WickGreenFunction[ws:BdGState[uv_?NamvoMatrixQ, z_?NumericQ, ___], kk:{___Integer}] := Module[
  { uu = Normal @ NamvoUnitary[uv],
    aa, bb, wm, ff, gg, nn },
  nn = FermionCount[ws];
  aa = uu[[ kk ]];
  bb = uu[[ kk + nn ]];

  nn = Length[kk];
  gg = Normal @ Zero[{nn, nn}];
  Table[
    wm = N @ WickMatrix[{aa[[i]], bb[[i]]}];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ wm, Det::luc],
    {i, 1, nn}
  ];
  Table[
    wm = N @ WickMatrix[{aa[[i]], bb[[j]]}];
    gg[[i, j]] = Pfaffian @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, nn-1},
    {j, i+1, nn}
  ];

  ff = Normal @ Zero[{nn, nn}];
  Table[
    wm = N @ WickMatrix[{aa[[i]], aa[[j]]}];
    ff[[i, j]] = Pfaffian @ wm;
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, nn-1},
    {j, i+1, nn}
  ];
  NamvoGreen[{gg, ff}, cc]
]

(**** </WickGreenFunction> ****)


(**** <WickDensityMatrix> ****)

(* canonical form for BdG models *)
WickDensityMatrix[grn_NamvoGreen] := Module[
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
WickDensityMatrix[grn_?NamvoMatrixQ] := WickDensityMatrix[NamvoGreen @ grn]

(* shortcut for BdG models *)
WickDensityMatrix[ws_BdGState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
]

(**** </WickDensityMatrix> ****)


End[] (* Fermionic quantum computation in the Namvo space *)


EndPackage[]
