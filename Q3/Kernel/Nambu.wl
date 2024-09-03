BeginPackage["Q3`"]


{ NambuMatrix, NambuMatrixQ };
{ NambuUnitary, NambuGaussian, NambuHermitian, NambuGreen };
{ NambuOne, NambuZero };

{ NambuState, RandomNambuState };
{ NambuOperator, NambuOperatorFrom };
{ NambuGaussian, NambuUnitary, NambuHermitian, NambuGreen };
{ RandomNambuGaussian, RandomNambuUnitary, RandomNambuHermitian, RandomNambuGreen };

Begin["`Private`"] (* Tools for Nambu matrices *)

(**** <NambuMatrix> ****)

NambuMatrix::usage = "NambuMatrix[mat] r the two n\[Times]n independent blocks at the upper-left and upper-right corners of the 2n\[Times]2n matrix mat."

NambuMatrix::odd = "Matrix `` has odd dimenions."

NambuMatrix[mat_?SquareMatrixQ] := Module[
  { n = (Length[mat] + 1) / 2 },
  Message[NambuMatrix::odd, mat];
  { mat[[ ;;n, ;;n]], Zero[n] }
] /; OddQ[Length @ mat]

NambuMatrix[mat_?SquareMatrixQ] := 
  First @ PartitionInto[mat, {2, 2}]

NambuMatrix[{mat_?SquareMatrixQ, 0}] :=
  {mat, Zero @ Dimensions @ mat}

(**** </NambuMatrix> ****)


(**** <NambuMatrixQ> ****)

NambuMatrixQ::usage = "NambuMatrixQ[{u, v}] returns True if the pair {a, b} of square matrices are compatible in size."

NambuMatrixQ[uv:{_?MatrixQ, _?MatrixQ}] := ArrayQ[uv]

NambuMatrixQ[_] = False

(**** </NambuMatrixQ> ****)


NambuOne::usage = "NambuOne[n] returns the pair {One[n], Zero[{n, n}]}, which represents the identity matrix in the Nambu space."

NambuOne[n_Integer] := {One @ n, Zero @ {n, n}}


NambuZero::usage = "NambuZero[n] returns the pair {Zero[{n, n}], Zero[{n, n}]}, which represents the zero matrix in the Nambu space."

NambuZero[n_Integer] := {Zero @ {n, n}, Zero @ {n, n}}


(**** <theNambuDot> ****)

theNambuDot::usage = "theNambuDot[{u1,v1}, {u2,v2}] returns the reduced Nambu matrix corresponding to the matrix multiplication of two full Nambu matrices corresponding to {u1, v1} and {u2, v2}, respectively."

SetAttributes[theNambuDot, Flat]

theNambuDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

theNambuDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barU := {{U, V}, Conjugate @ {V, U}} *)

(**** </theNambuDot> ****)

End[] (* Tools for Nambu matrices *)



Begin["`Private`"] (* Fermionic quantum computation in the Nambu space *)

AddElaborationPatterns[_NambuState, _NambuOperator, _NambuUnitary, _NambuGaussian];

(**** <NambuState> ****)

NambuState::usage = "NambuState[uv, trs, {c1, c2, \[Ellipsis]}] represents a many-fermion quantum state for fermion modes {c1, c2, \[Ellipsis]} that has undergone the overall Bogoliubov-de Gennes type evolution specified by reduced Nambu matrix uv and quantum decoherence process (including measurements) specified by matrix trs."

NambuState::bad = "Unsupported form of Wick state ``."

NambuState /:
MakeBoxes[ws:NambuState[uv:{_?MatrixQ, _?MatrixQ}, ops:(_?MatrixQ|{}), cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NambuState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", cc },
      BoxForm`SummaryItem @ { "Depth: ", Length @ ops}
    },
    { BoxForm`SummaryItem @ { "Overall unitary: ", ArrayShort /@ uv },
      BoxForm`SummaryItem @ { "Operator transforms: ",
        If[ops == {}, {}, ArrayShort /@ First @ PartitionInto[ops, {1, 2}]] }   
    },
    fmt,
    "Interpretable" -> Automatic
  ]

NambuState[cc:{__?FermionQ}] :=
  NambuState[NambuOne[Length @ cc], {}, cc]

NambuState[ops_?MatrixQ, cc:{__?FermionQ}] :=
  NambuState[NambuOne[Length @ cc], ops, cc]

NambuState[Ket[aa_Association]] := Module[
  { cc = Select[Keys @ aa, FermionQ],
    dd = Select[Keys @ theKetTrim @ aa, FermionQ] },
  NambuState[
    NambuOne[Length @ cc],
    First @ NambuOperatorFrom[Dagger @ dd, cc],
    cc
  ]
]

NambuState[ops:{__Dagger?AnyFermionQ}, cc:{__?FermionQ}] :=
  NambuState @ Ket[cc -> 0, Peel[ops] -> 1]


NambuState /:
NormSquare[NambuState[_, {}, cc:{___?FermionQ}]] = 1

NambuState /:
NormSquare[NambuState[_, ops_?MatrixQ, cc:{__?FermionQ}]] := 
  Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[theConjugateReverse @ ops, ops], Det::luc]

NambuState /:
Norm[ws:NambuState[_, _?MatrixQ, {__?FermionQ}]] := Sqrt[NormSquare @ ws]


NambuState /:
Normalize[ws:NambuState[_, {}, {__?FermionQ}]] = ws

NambuState /:
Normalize[ws:NambuState[uv_?NambuMatrixQ, ops_?MatrixQ, cc:{___?FermionQ}]] := Module[
  { trs = uv,
    new },
  Quiet @ Check[
    new = ops * Power[Norm @ ws, -1/Length[ops]],
    trs = NambuOne[Length @ cc];
    new = Zero @ {1, 2 * Length[cc]}
  ];
  NambuState[trs, new, cc]
]


NambuState /:
Expand[ws:NambuState[_?NambuMatrixQ, _?MatrixQ, cc:{___?FermionQ}]] :=
  State[Matrix[ws, cc], cc]


NambuState /:
Elaborate[ws:NambuState[_?NambuMatrixQ, _?MatrixQ, cc:{__?FermionQ}]] :=
  ExpressionFor[Matrix[ws, cc], cc]

NambuState /:
Elaborate[ws_NambuState] = ws (* fallback *)


NambuState /:
Matrix[ws:NambuState[_, _, cc:{__?FermionQ}]] := Matrix[ws, cc]

NambuState /:
Matrix[ws:NambuState[uv_?NambuMatrixQ, trs_?MatrixQ, cc:{__?FermionQ}], ss:{__?SpeciesQ}] :=
  Module[
    { ops = WickElements[trs, cc],
      vec },
    vec = SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ops, ss]
    ];
    Matrix[NambuUnitary[uv, cc], ss] . vec
  ]

NambuState /: (* fallback *)
Matrix[ws_NambuState, rest___] := (
  Message[NambuState::bad, ws];
  Matrix[Ket[], rest]
)


NambuState /:
NonCommutativeQ[_NambuState] = True

NambuState /:
MultiplyKind[_NambuState] = Fermion

(**** </NambuState> ****)


RandomNambuState::usage = "RandomNambuState[k, {c1, c2, \[Ellipsis]}] randomly generates a depth-k BdG state with half filling on fermion modes {c1, c2, \[Ellipsis]}.\nNambuState[{c1, c2, \[Ellipsis]}] chooses depth k randomly from {1, 2, \[Ellipsis], 10}."

RandomNambuState[cc:{__?FermionQ}] :=
  RandomNambuState[RandomInteger[{1, 10}], cc]

RandomNambuState[k_Integer?Positive, cc:{__?FermionQ}] := Module[
  { mm, in },
  mm = Table[RandomVector[2 Length @ cc], k];
  in = NambuState[Dagger @ cc[[;; ;;2]], cc];
  Normalize[ RandomNambuUnitary[cc] ** NambuOperator[mm, cc][in] ]
]


(**** <NambuUnitary> ****)

NambuUnitary::usage = "NambuUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Nambu space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively.\nNambuUnitary[spec, {c1,c2,\[Ellipsis]}] indicates that the operator is acting on fermion modes {c1,c2,\[Ellipsis]}."

NambuUnitary /:
MakeBoxes[op:NambuUnitary[uv_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    NambuUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ uv }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, uv] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[uv]

NambuUnitary[0, cc:{___?FermionQ}, rest___] := (* zero in the Nambu space *)
  NambuUnitary[NambuZero[Length @ cc], cc, rest]

NambuUnitary[1, cc:{___?FermionQ}, rest___] := (* identity in the Nambu space *)
  NambuUnitary[NambuOne[Length @ cc], cc, rest]

NambuUnitary[mat_?SquareMatrixQ, rest___] :=
  NambuUnitary[NambuMatrix @ mat, rest]

NambuUnitary[{mat_?SquareMatrixQ, 0}, rest___] :=
  NambuUnitary[NambuMatrix @ {mat, 0}, rest]

NambuUnitary[NambuUnitary[uv_?NambuMatrixQ, ___], rest___] :=
  NambuUnitary[uv, rest]


NambuUnitary /:
MatrixForm @ NambuUnitary[mm_?NambuMatrixQ, rest___] := Map[MatrixForm, mm]

NambuUnitary /:
ArrayShort @ NambuUnitary[mm_?NambuMatrixQ, rest___] := Map[ArrayShort, mm]

NambuUnitary /:
Normal @ NambuUnitary[{u_?MatrixQ, v_?MatrixQ}, ___] :=
  ArrayFlatten @ {
    {u, v},
    Conjugate @ {v, u}
  }

NambuUnitary /:
Dagger @ NambuUnitary[{u_?MatrixQ, v_?MatrixQ}, rest___] :=
  NambuUnitary[{Topple @ u, Transpose @ v}, rest]

NambuUnitary /:
Plus[NambuUnitary[a_, opts___?OptionQ], NambuUnitary[b_, more___?OptionQ]] :=
  NambuUnitary[a + b, opts, more]

NambuUnitary /:
Plus[NambuUnitary[a_, cc_, any___], NambuUnitary[b_, cc_, other___]] :=
  NambuUnitary[a + b, cc, any, other]

NambuUnitary /:
Times[z_, NambuUnitary[mm_, rest___]] :=
  NambuUnitary[z * mm, rest]

NambuUnitary /:
Dot[NambuUnitary[a_, opts___?OptionQ], NambuUnitary[b_, more___?OptionQ]] :=
  NambuUnitary[theNambuDot[a, b], opts, more]

NambuUnitary /:
Dot[NambuUnitary[a_, cc_, any___], NambuUnitary[b_, cc_, other___]] :=
  NambuUnitary[theNambuDot[a, b], any, other]


NambuUnitary /:
Elaborate[op:NambuUnitary[uv_?NambuMatrixQ, cc:{__?FermionQ}, ___]] :=
  ExpressionFor[Matrix[op, cc], cc]

NambuUnitary /: (* fallback *)
Elaborate[op_NambuUnitary] = op


NambuUnitary /:
Matrix[op:NambuUnitary[uv_?NambuMatrixQ, cc:{__?FermionQ}, ___], ss:{__?SpeciesQ}] := 
  MatrixExp[I*Matrix[NambuHermitian[-I*MatrixLog[Normal @ op], cc], ss]]

NambuUnitary /: (* fallback *)
Matrix[op_NambuUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


NambuUnitary /:
NonCommutativeQ[_NambuUnitary] = True

NambuUnitary /:
MultiplyKind[_NambuUnitary] = Fermion

NambuUnitary /:
Multiply[pre___, opr_NambuUnitary, ws_NambuState] := Multiply[pre, opr[ws]]

NambuUnitary /:
Multiply[pre___, opr_NambuUnitary, fs_Ket] := Multiply[pre, opr[NambuState @ fs]]

NambuUnitary[new_?NambuMatrixQ, cc_, ___][NambuState[uv_, ops_, cc_]] :=
  NambuState[theNambuDot[new, uv], ops, cc]


NambuUnitary /:
ParseGate[NambuUnitary[uv_?NambuMatrixQ, cc:{___?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[cc, more, opts, "Label" -> "U"]

(**** </NambuUnitary> ****)


(**** <NambuHermitian> ****)

NambuHermitian::usage = "NambuHermitian[{ham, del}] represents a quadratic Hermitian operator in the Nambu space that is characterized by an n\[Times]n Hamitian matrix ham and an n\[Times]n anti-symmetric matrix del.\nNambuHermitian[spec, {c1,c2,\[Ellipsis]}] indicates that the operator is acting on fermion modes {c1,c2,\[Ellipsis]}."

NambuHermitian /:
MakeBoxes[op:NambuHermitian[mm_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    NambuHermitian, op, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ mm }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, mm] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[mm]

NambuHermitian[0, cc:{___?FermionQ}, rest___] := (* zero in the Nambu space *)
  NambuHermitian[NambuZero[Length @ cc], cc, rest]

NambuHermitian[1, cc:{___?FermionQ}, rest___] := (* identity in the Nambu space *)
  NambuHermitian[NambuOne[Length @ cc], cc, rest]

NambuHermitian[mat_?SquareMatrixQ, rest___] :=
  NambuHermitian[NambuMatrix @ mat, rest]

NambuHermitian[{mat_?SquareMatrixQ, 0}, rest___] :=
  NambuHermitian[NambuMatrix @ {mat, 0}, rest]

NambuHermitian[NambuHermitian[uv_?NambuMatrixQ, ___], rest___] :=
  NambuHermitian[uv, rest]


NambuHermitian /:
MatrixForm @ NambuHermitian[mm_?NambuMatrixQ, rest___] := Map[MatrixForm, mm]

NambuHermitian /:
ArrayShort @ NambuHermitian[mm_?NambuMatrixQ, rest___] := Map[ArrayShort, mm]

NambuHermitian /:
Normal @ NambuHermitian[{ham_, del_}, ___] :=
  ArrayFlatten @ {
    {ham, del},
    {Topple[del], -Transpose[ham]}
  }

NambuHermitian /:
Dagger[ham:NambuHermitian[{_?MatrixQ, _?MatrixQ}, rest___]] = ham

NambuHermitian /:
Plus[NambuHermitian[a_, opts___?OptionQ], NambuHermitian[b_, more___?OptionQ]] :=
  NambuHermitian[a + b, opts, more]

NambuHermitian /:
Plus[NambuHermitian[a_, cc_, any___], NambuHermitian[b_, cc_, other___]] :=
  NambuHermitian[a + b, cc, any, other]

NambuHermitian /:
Times[z_, NambuHermitian[mm_, rest___]] :=
  NambuHermitian[z * mm, rest]

NambuHermitian /:
Dot[NambuHermitian[a_, cc_, any___], NambuHermitian[b_, cc_, other___]] :=
  NambuHermitian[theNambuDot[a, b], any, other]


NambuHermitian /:
Elaborate[op:NambuHermitian[uv_?NambuMatrixQ, cc:{__?FermionQ}, ___]] :=
  ExpressionFor[Matrix[op, cc], cc]

NambuHermitian /: (* fallback *)
Elaborate[op_NambuHermitian] = op


NambuHermitian /:
Matrix[NambuHermitian[ham_?NambuMatrixQ, cc:{__?FermionQ}, ___], ss:{__?SpeciesQ}] := Module[
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

  TensorContract[
    Transpose[Topple /@ mm, {3, 1, 2}] . Normal[NambuHermitian @ ham] . mm / 2,
    {{2, 3}}
  ]
]

NambuHermitian /: (* fallback *)
Matrix[op_NambuHermitian, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


NambuHermitian /:
NonCommutativeQ[_NambuHermitian] = True

NambuHermitian /:
MultiplyKind[_NambuHermitian] = Fermion

NambuHermitian /:
Multiply[pre___, opr_NambuHermitian, ws_NambuState] := Multiply[pre, opr[ws]]

NambuHermitian /:
Multiply[pre___, opr_NambuHermitian, fs_Ket] := Multiply[pre, opr[NambuState @ fs]]

NambuHermitian[new_?NambuMatrixQ, cc_, ___][NambuState[uv_, ops_, cc_]] :=
  NambuState[theNambuDot[new, uv], ops, cc]


NambuHermitian /:
ParseGate[NambuHermitian[uv_?NambuMatrixQ, cc:{___?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[cc, more, opts, "Label" -> "U"]

(**** </NambuHermitian> ****)


(**** <NambuGreen> ****)

NambuGreen::usage = "NambuGreen[{grn, anm}] represents the matrix of a single-particle Green's functions in the Nambu space that is characterized by the n\[Times]n matrix grn of normal Green's functions and the n\[Times]n matrix anm of anomalous Green's functions.\nNambuGreen[spec, {c1,c2,\[Ellipsis]}] indicates that the Green's functions are for fermion modes {c1,c2,\[Ellipsis]}."

NambuGreen /:
MakeBoxes[op:NambuGreen[mm_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    NambuGreen, op, None,
    { BoxForm`SummaryItem @ { "Modes: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ mm }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, mm] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[mm]

NambuGreen[0, cc:{___?FermionQ}, rest___] := (* zero in the Nambu space *)
  NambuGreen[NambuZero[Length @ cc], cc, rest]

NambuGreen[1, cc:{___?FermionQ}, rest___] := (* identity in the Nambu space *)
  NambuGreen[NambuOne[Length @ cc], cc, rest]

NambuGreen[mat_?SquareMatrixQ, rest___] :=
  NambuGreen[NambuMatrix @ mat, rest]

NambuGreen[{mat_?SquareMatrixQ, 0}, rest___] :=
  NambuGreen[NambuMatrix @ {mat, 0}, rest]

NambuGreen[NambuGreen[grn_?NambuMatrixQ, ___], rest___] :=
  NambuGreen[grn, rest]


NambuGreen /:
MatrixForm @ NambuGreen[mm_?NambuMatrixQ, rest___] := Map[MatrixForm, mm]

NambuGreen /:
ArrayShort @ NambuGreen[mm_?NambuMatrixQ, rest___] := Map[ArrayShort, mm]

NambuGreen /:
Normal @ NambuGreen[{g_, f_}, ___] :=
  ArrayFlatten @ {
    {g, f},
    {Topple[f], One[Dimensions @ g] - Transpose[g]}
  }

NambuGreen /:
Dagger[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, rest___]] = grn

NambuGreen /:
Plus[NambuGreen[a_], NambuGreen[b_]] :=
  NambuGreen[a + b, opts, more]

NambuGreen /:
Plus[NambuGreen[a_, cc_], NambuGreen[b_, cc_]] :=
  NambuGreen[a + b, cc, any, other]

NambuGreen /:
Times[z_, NambuGreen[mm_, rest___]] :=
  NambuGreen[z * mm, rest]

(**** </NambuGreen> ****)


RandomNambuUnitary::usage = "RandomNambuUnitary[n] returns a random NambuUnitary[{u, v}], where u and v are the n\[Times]n upper-left and upper-right blocks of the resulting Bogoliubov-de Gennes transformation matrix.\nRandomNambuUnitary[{c1, c2, \[Ellipsis], cn}] returns a random NambuUnitary[{u, v}, {c1, c2, \[Ellipsis], cn}]."

RandomNambuUnitary[cc:{__?FermionQ}, rest___] :=
  NambuUnitary[RandomNambuUnitary[Length @ cc], cc, rest]

RandomNambuUnitary[n_Integer] := With[
  { barH = Normal[RandomNambuHermitian @ n] },
  NambuUnitary @ MatrixExp[I barH]
]


RandomNambuHermitian::usage = "RandomNambuHermitian[n] returns a random NambuHermitian[{ham, del}], where ham is an n\[Times]n Hermitian matrix and del is an n\[Times]n anti-symmetric matrix.\nRandomNambuHermitian[{c1, c2, \[Ellipsis], cn}] returns a random NambuHermitian[{ham, del}, {c1, c2, \[Ellipsis], cn}]."

RandomNambuHermitian[cc:{__?FermionQ}, rest___] :=
  NambuHermitian[RandomNambuHermitian[Length @ cc], cc, rest]

RandomNambuHermitian[n_Integer, rest___] :=
  NambuHermitian[{RandomHermitian[n], RandomAntisymmetric[n]}, rest]


RandomNambuGreen::usage = "RandomNambuGreen[n] returns a random NambuGreen[{grn, anm}], where grn is an n\[Times]n matrix representing the normal Green's function and anm is an n\[Times]n anti-symmetric matrix representing the anomalous Green's function.\nRandomNambuGreen[{c1, c2, \[Ellipsis], cn}] returns a ramdom NambuGreen[{grn, anm}, {c1, c2, \[Ellipsis], cn}]."

RandomNambuGreen[cc:{__?FermionQ}, rest___] :=
  NambuGreen[RandomNambuGreen[Length @ cc], cc, rest]

RandomNambuGreen[n_Integer, rest___] := Module[
  { trs = Normal @ RandomNambuUnitary[n],
    val = RandomReal[{0, 1}, n] },
  val = DiagonalMatrix @ Join[val, 1 - val];
  NambuGreen[trs . val . Topple[trs], rest]
]


(**** <NambuOperator> ****)

NambuOperator::usage = "NambuOperator[m, {c1,c2,\[Ellipsis]}] represents a sequence of quantum operations that are described linear combinations in the creation and annihilation operators of the fermion modes {Subscript[c, 1],Subscript[c, 2],\[Ellipsis]} with coefficients given by the elements of matrix m."

NambuOperator /:
MakeBoxes[NambuOperator[ops_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest}, 
    m, n },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  {m, n} = Dimensions[ops];
  BoxForm`ArrangeSummaryBox[
    NambuOperator, mat, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Transforms: ", ArrayShort /@ First @ PartitionInto[ops, {1, 2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuOperator[msr_Measurement] = msr

NambuOperator[trs_NambuUnitary] = trs

(* canonicalization *)
NambuOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  NambuOperatorFrom[ops, cc, rest]


NambuOperator[{}, ___][any_] = any

NambuOperator[spec__][fs_Ket] := NambuOperator[spec][NambuState @ fs]

NambuOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___][NambuState[uv_, mm_, cc_]] :=
  NambuState[uv, Join[trs . Normal[NambuUnitary @ uv], mm], cc]


NambuOperator /:
Dagger @ NambuOperator[ops_?MatrixQ, rest___] :=
  NambuOperator[theConjugateReverse @ ops, rest]


NambuOperator /: 
NonCommutativeQ[_NambuOperator] = True

NambuOperator /:
MultiplyKind[_NambuOperator] = Fermion

NambuOperator /:
Multiply[pre___, opr_NambuOperator, ws_NambuState] := Multiply[pre, opr[ws]]

NambuOperator /:
Multiply[pre___, opr_NambuOperator, fs_Ket] := Multiply[pre, opr[NambuState @ fs]]


NambuOperator /:
Matrix[NambuOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___], rest___] :=
  Dot @@ Matrix[WickElements[trs, cc], rest]

NambuOperator /: (* fallback *)
Matrix[op_NambuOperator, rest___] := op * Matrix[1, rest]


NambuOperator /:
Elaborate[NambuOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___]] :=
  Apply[Multiply, WickElements[trs, cc]]

NambuOperator /: (* fallback *)
Elaborate[op_NambuOperator] = op 


NambuOperator /:
VacuumExpectation @ NambuOperator[trs_?MatrixQ, cc:{__?FermionQ}, ___] :=
  Pfaffian @ WickMatrix[trs]


NambuOperator /:
ParseGate[NambuOperator[trs_, cc:{__?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[cc, more, opts]

(**** </NambuOperator> ****)


(**** <NambuOperatorFrom> ****)

(* NOTE: In principle, NambuOperatorFrom may be integrated into NambuOperator, but separating this feature keeps better the performance of NambuOperator. *)

NambuOperatorFrom::usage = "NambuOperatorFrom[expr, {c1,c2,\[Ellipsis]}] constructs NambuOperator from expr, which is supposed to be a linear combination or a list of linear combinations in the creation and annihilation operators of fermion modes {c1, c2, \[Ellipsis]}."

NambuOperatorFrom::nlin = WickOperatorFrom::nlin

NambuOperatorFrom[expr_, cc:{__?FermionQ}, rest___] :=
  NambuOperator[theNambuOperator[expr, cc], cc, rest] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[NambuOperatorFrom::nlin, expr, cc];
    False
  ]


theNambuOperator[expr_List, cc:{__?FermionQ}] :=
  Map[Coefficient[#, Join[cc, Dagger @ cc]] &, expr]

theNambuOperator[expr_, cc:{__?FermionQ}] :=
  { Coefficient[expr, Join[cc, Dagger @ cc]] }


(**** </NambuOperatorFrom> ****)


(**** <Measurement> ****)

Measurement /:
Multiply[pre___, msr:Measurement[_?FermionQ|{__?FermionQ}], ws_NambuState] :=
  Multiply[pre, msr[ws]]

theMeasurement[ws:NambuState[uv_, trs_, cc_], c_?FermionQ] := Module[
  { msr, dgr, mat, prb },
  msr = First @ NambuOperator[{c, Dagger @ c}, cc];
  msr = msr . Normal[NambuUnitary @ uv];

  dgr = theConjugateReverse[trs];

  mat = WickMatrix @ Join[dgr, msr, trs];
  prb = Re @ Sqrt @ Quiet[Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= NormSquare[ws];
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[c] = 0;
    NambuOperator[{c, Dagger @ c}, cc][ws],
    $MeasurementOut[c] = 1;
    NambuOperator[{Dagger @ c, c}, cc][ws]
  ]
]

(**** </Measurement> ****)


(**** <WickLogarithmicNegativity> ****)
(* for BdG models *)

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], rest__] :=
  WickLogarithmicNegativity[{gg, ff}, rest]


WickEntanglementEntropy[ws_NambuState, dd:{__?FermionQ}] :=
  WickEntanglementEntropy[WickGreenFunction[ws, dd], Range[Length @ dd]]

WickMutualInformation[ws_NambuState, dd:{__?FermionQ}] := 
  WickMutualInformation[
    WickGreenFunction[ws], 
    Lookup[First /@ PositionIndex[Last @ ws], dd]
  ]

WickLogarithmicNegativity[ws_NambuState, dd:{__?FermionQ}, opts:OptionsPattern[]] := Module[
  { gg = WickGreenFunction[ws],
    cc = Last[ws],
    kk },
  kk = dd /. Thread[cc -> Range[Length @ cc]];
  WickTimeReversalMoment[1/2, gg, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]
]


WickExpectation[ws_NambuState][HoldPattern @ Multiply[ops__?AnyFermionQ]] :=
  WickExpectation[ws] @ NambuOperatorFrom[{ops}, Last @ ws]

WickExpectation[ws:NambuState[uv_, bb_, cc_]][NambuOperator[ops_?MatrixQ, ___]] := Module[
  { aa = theConjugateReverse[bb],
    mat },
  mat = WickMatrix @ Join[aa, ops . Normal[NambuUnitary @ uv], bb];
  Pfaffian[mat] (* NOTE: The Nambu state is assumed to be normalized. *)
]

(**** </WickLogarithmicNegativity> ****)


(**** <WickGreenFunction> ****)

WickGreenFunction[ws_NambuState] :=
  WickGreenFunction[ws, Last @ ws]

WickGreenFunction[ws:NambuState[uv_, qq_, cc_], dd:{___?FermionQ}] := Module[
  { uu = Normal @ NambuUnitary[uv],
    pp = theConjugateReverse[qq],
    aa, bb, wm, ff, gg, kk, n },
  kk = First /@ PositionIndex @ Join[cc, Dagger @ cc];
  aa = uu[[ Lookup[kk, dd] ]];
  bb = uu[[ Lookup[kk, Dagger @ dd] ]];

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = WickMatrix[pp];
  wm[[1, 3]] = WickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = WickMatrix[qq];

  n = Length[dd];
  gg = Normal @ Zero[{n, n}];
  Table[
    (* gg[[i, i]] = Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[pp, {aa[[i]], bb[[i]]}, qq], Det::luc], *)
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[i]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[i]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[i]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, n}
  ];
  Table[
    (* gg[[i, j]] = Pfaffian @ WickMatrix @ Join[pp, {aa[[i]], bb[[j]]}, qq]; *)
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];

  ff = Normal @ Zero[{n, n}];
  Table[
    (* ff[[i, j]] = Pfaffian @ WickMatrix @ Join[pp, {aa[[i]], aa[[j]]}, qq]; *)
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], aa[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], aa[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], aa[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    ff[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];
  NambuGreen[{gg, ff}, cc]
  (* NOTE: The Nambu state is assumed to be normalized. *)
]

(**** </WickGreenFunction> ****)


(**** <WickDensityOpeator> ****)

WickDensityMatrix[grn_?NambuMatrixQ] := WickDensityMatrix[NambuGreen @ grn]

WickDensityMatrix[grn_NambuGreen] := Module[
  { n = Length[First @ First @ grn],
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

WickDensityMatrix[ws_NambuState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
]

(**** </WickDensityOpeator> ****)


End[] (* Fermionic quantum computation in the Nambu space *)


EndPackage[]
