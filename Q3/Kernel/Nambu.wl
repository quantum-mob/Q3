BeginPackage["Q3`"]

{ NambuMatrix, NambuMatrixQ };
{ NambuGaussian, NambuUnitary, NambuHermitian, NambuGreen };
{ NambuOne, NambuZero };

{ NambuState, RandomNambuState };
{ NambuOperator, NambuOperatorFrom, NambuElements };
{ NambuGaussian, NambuUnitary, NambuHermitian, NambuGreen };
{ RandomNambuGaussian, RandomNambuUnitary, RandomNambuHermitian, RandomNambuGreen, RandomNambuOperator };

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

NambuState::usage = "NambuState[uv, trs] represents a many-body quantum state for non-interacting fermion modes that has undergone the overall Bogoliubov-de Gennes (BdG) type time evolution in the Nambu space specified by reduced Nambu matrix uv and decoherence processes (including measurements) specified by matrix trs."

NambuState::bad = "Unsupported form of Nambu state ``."

NambuState /:
MakeBoxes[ws:NambuState[uv_?NambuMatrixQ, ops_?MatrixQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NambuState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", FermionCount @ ws },
      BoxForm`SummaryItem @ { "Depth: ", Length @ ops}
    },
    { BoxForm`SummaryItem @ { "Overall unitary: ", ArrayShort /@ uv },
      BoxForm`SummaryItem @ { "Operator transforms: ", ArrayShort /@ First @ PartitionInto[ops, {1, 2}] }   
    },
    fmt,
    "Interpretable" -> Automatic
  ]

NambuState /: (* vacuum state times a constant *)
MakeBoxes[ws:NambuState[uv_?NambuMatrixQ, z_?NumericQ, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NambuState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", Length[First @ uv] },
      BoxForm`SummaryItem @ { "Type: ", Switch[z, 0, Null, _, Vacuum] }
    },
    { BoxForm`SummaryItem @ { "Overall unitary: ", ArrayShort /@ uv },
      BoxForm`SummaryItem @ { "Norm: ", Abs[z] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]


(* vacuum & null states *)
(* NambuState[{u, v}, 0]: the null state *)
(* NambuState[{u, v}, 1]: the vacuum state *)
(* NambuState[{u, v}, z]: the vacuum state with overall phase factor z *)
NambuState[{z_?NumericQ, n_Integer}] :=
  NambuState[NambuOne[n], z]

(* vacuum state *)
NambuState[n_Integer] :=
  NambuState[NambuOne[n], 1]

(* vacuum state *)
NambuState[uv_?NambuMatrixQ, {}] :=
  NambuState[NambuOne[Length @ First @ uv], 1]
(* NOTE: The left-hand form cannot handle the multiplication by a global factor. *)

(* canonicalization *)
NambuState[ops_?MatrixQ] :=
  NambuState[NambuOne[Last @ Dimensions @ ops], ops]

(* initialization *)
NambuState[vv_/;VectorQ[vv, BinaryQ], n_Integer, rest___] := Module[
  { ww = PadRight[vv, n, vv],
    kk },
  kk = Flatten @ Position[ww, 1];
  NambuState[NambuOne[n], One[2n][[n+kk]], rest]
]

(* initialization *)
NambuState[Rule[n_Integer, vv_/;VectorQ[vv, BinaryQ]], rest___] :=
  NambuState[vv, n, rest]

(* initialization *)
NambuState[Rule[cc:{__?FermionQ}, vv_/;VectorQ[vv, BinaryQ]], rest___] :=
  NambuState[vv, Length @ cc, rest]

(* initialization *)
NambuState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  NambuState[Lookup[aa, cc], Length @ cc]
]


NambuState /: (* vacuum state *)
NormSquare[NambuState[_?NambuMatrixQ, z_?NumericQ, ___]] :=
  AbsSquare[z]

NambuState /:
NormSquare[NambuState[_?NambuMatrixQ, ops_?MatrixQ, ___]] := 
  Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[NambuConjugateReverse @ ops, ops], Det::luc]

NambuState /:
Norm[ws:NambuState[_?NambuMatrixQ, _, ___]] :=
  Sqrt[NormSquare @ ws]
(* NOTE: Both form vacuum and non-vacuum states *)


NambuState /: (* vacuum state *)
Normalize[NambuState[uv_?NambuMatrixQ, _?NumericQ, rest___]] :=
  NambuState[uv, 1, rest]

NambuState /:
Normalize[in:NambuState[uv_?NambuMatrixQ, ops_?MatrixQ, rest___]] := Module[
  { trs = uv,
    new },
  Quiet @ Check[
    new = ops * Power[Norm @ in, -1/Length[ops]],
    trs = NambuOne[Length @ First @ uv];
    new = 0 (* null state *)
  ];
  NambuState[trs, new, rest]
]


NambuState /:
Times[z_?NumericQ, NambuState[uv_?NambuMatrixQ, ops_?MatrixQ, rest___]] := Module[
  { new },
  new = ops * Power[z, 1/Length[ops]];
  NambuState[uv, new, rest]
]

NambuState /:
Times[z_?NumericQ, NambuState[uv_?NambuMatrixQ, val_?NumericQ, rest___]] :=
  NambuState[uv, z val, rest]


NambuState /: (* vacuum state *)
ExpressionFor[NambuState[_, z_?NumericQ, ___], cc:{__?FermionQ}] :=
  z * Ket[cc]

NambuState /:
ExpressionFor[ws:NambuState[_?NambuMatrixQ, _?MatrixQ, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix[ws, cc], cc]

NambuState /:
ExpressionFor[ws_NambuState, ___] = ws (* fallback *)


NambuState /: (* vacuum state *)
Matrix[NambuState[_?NambuMatrixQ, z_?NumericQ], ss:{__?SpeciesQ}] :=
  z * Matrix[Ket @ ss, ss]

NambuState /:
Matrix[NambuState[uv_?NambuMatrixQ, trs_?MatrixQ, ___], ss:{__?SpeciesQ}] :=
  Module[
    { cc = Fermions[ss],
      ops, vec },
    ops = NambuElements[trs, cc];
    vec = SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ops, ss]
    ];
    Matrix[NambuUnitary @ uv, ss] . vec
  ]

NambuState /:
Matrix[ws_NambuState] := Module[
  { c, cc },
  Let[Fermion, c];
  cc = c[Range @ FermionCount @ ws],
  Matrix[ws, cc]
]


NambuState /:
NonCommutativeQ[_NambuState] = True

NambuState /:
MultiplyKind[_NambuState] = Fermion

(**** </NambuState> ****)


RandomNambuState::usage = "RandomNambuState[k, n] randomly generates a depth-k BdG state with half filling on n fermion modes\nRandomNambuState[n] selects depth k randomly from {1, 2,\[Ellipsis], n}."

RandomNambuState[k_Integer?Positive, n_Integer] := Module[
  { mm, in },
  mm = RandomMatrix[{k, 2 n}];
  in = NambuState[{1, 0}, n];
  Normalize[ RandomNambuUnitary[n] ** NambuOperator[mm][in] ]
]

RandomNambuState[n_Integer] :=
  RandomNambuState[RandomChoice @ Range[2, n, 2], n]

(* backward compatibility *)
RandomNambuState[k_Integer?Positive, cc:{__?FermionQ}] :=
  RandomNambuState[k, Length @ cc]

(* backward compatibility *)
RandomNambuState[cc:{__?FermionQ}] :=
  RandomNambuState[Length @ cc]


(**** <NambuConjugateReverse> ****)

NambuConjugateReverse::usage = "NambuConjugateReverse[mat] returns the reverse of {Conjugate[B], Conjugate[A]} for matrix mat with block structure mat = {A, B}."

(* for the BdG models *)
NambuConjugateReverse[ops_?MatrixQ] := With[
  { new = ArrayFlatten[Reverse /@ PartitionInto[ops, {1, 2}]] },
  Conjugate @ Reverse @ new
]

(**** </NambuConjugateReverse> ****)


(**** <NambuUnitary> ****)

NambuUnitary::usage = "NambuUnitary[{u, v}] represents a Bogoliubov-de Gennes transform in the Nambu space that is characterized by the n\[Times]n upper-left and upper-right blocks u and v, respectively."

NambuUnitary /:
MakeBoxes[op:NambuUnitary[uv_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    NambuUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ uv }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, uv] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[uv]

(* zero in the Nambu space *)
NambuUnitary[0, n_Integer, rest___] :=
  NambuUnitary[NambuZero[n], rest]

(* zero in the Nambu space *)
(* backward compatibility *)
NambuUnitary[0, cc:{___?FermionQ}, rest___] :=
  NambuUnitary[0, Length @ cc, rest]

(* identity in the Nambu space *)
NambuUnitary[1, n_Integer, rest___] :=
  NambuUnitary[NambuOne[n], rest]

(* identity in the Nambu space *)
(* backward compatibility *)
NambuUnitary[1, cc:{___?FermionQ}, rest___] :=
  NambuUnitary[1, Length @ cc, rest]

NambuUnitary[mat_?SquareMatrixQ, rest___] :=
  NambuUnitary[NambuMatrix @ mat, rest]

NambuUnitary[{mat_?SquareMatrixQ, 0}, rest___] :=
  NambuUnitary[NambuMatrix @ {mat, 0}, rest]

NambuUnitary[NambuUnitary[uv_?NambuMatrixQ, rest___], more___] :=
  NambuUnitary[uv, more, rest]


NambuUnitary /:
MatrixForm @ NambuUnitary[mm_?NambuMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NambuUnitary /:
ArrayShort @ NambuUnitary[mm_?NambuMatrixQ, rest___] :=
  Map[ArrayShort, mm]

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
Plus[NambuUnitary[a_, any___], NambuUnitary[b_, other___]] :=
  NambuUnitary[a + b, any, other]

NambuUnitary /:
Times[z_, NambuUnitary[mm_, rest___]] :=
  NambuUnitary[z * mm, rest]

NambuUnitary /:
Dot[NambuUnitary[a_, any___], NambuUnitary[b_, other___]] :=
  NambuUnitary[theNambuDot[a, b], any, other]


NambuUnitary /:
ExpressionFor[op:NambuUnitary[uv_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

NambuUnitary /: (* fallback *)
ExpressionFor[op_NambuUnitary, ___] = op


NambuUnitary /:
Matrix[op:NambuUnitary[uv_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { barH = -I*MatrixLog[Normal @ op] },
  MatrixExp[I*Matrix[NambuHermitian @ barH, ss]]
]

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

NambuUnitary[new_?NambuMatrixQ, ___][NambuState[uv_, ops_, rest___]] :=
  NambuState[theNambuDot[new, uv], ops, rest]
(* NOTE: This works also for vacuum state. *)

(**** </NambuUnitary> ****)


(**** <NambuHermitian> ****)

NambuHermitian::usage = "NambuHermitian[{ham, del}] represents a quadratic Hermitian operator in the Nambu space that is characterized by an n\[Times]n Hamitian matrix ham and an n\[Times]n anti-symmetric matrix del."

NambuHermitian /:
MakeBoxes[op:NambuHermitian[mm_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    NambuHermitian, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ mm }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, mm] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[mm]

(* zero in the Nambu space *)
NambuHermitian[0, n_Integer, rest___] :=
  NambuHermitian[NambuZero[n], rest]

(* zero in the Nambu space *)
(* backward compatibility *)
NambuHermitian[0, cc:{___?FermionQ}, rest___] :=
  NambuHermitian[0, Length @ cc, rest]

(* identity in the Nambu space *)
NambuHermitian[1, n_Integer, rest___] :=
  NambuHermitian[NambuOne[n], rest]

(* identity in the Nambu space *)
(* backward compatibility *)
NambuHermitian[1, cc:{___?FermionQ}, rest___] :=
  NambuHermitian[1, Length @ cc, rest]

NambuHermitian[mat_?SquareMatrixQ, rest___] :=
  NambuHermitian[NambuMatrix @ mat, rest]

NambuHermitian[{mat_?SquareMatrixQ, 0}, rest___] :=
  NambuHermitian[NambuMatrix @ {mat, 0}, rest]

NambuHermitian[NambuHermitian[uv_?NambuMatrixQ, rest___], more___] :=
  NambuHermitian[uv, more, rest]


NambuHermitian /:
MatrixForm @ NambuHermitian[mm_?NambuMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NambuHermitian /:
ArrayShort @ NambuHermitian[mm_?NambuMatrixQ, rest___] :=
  Map[ArrayShort, mm]

NambuHermitian /:
Normal @ NambuHermitian[{ham_, del_}, ___] :=
  ArrayFlatten @ {
    {ham, del},
    {Topple[del], -Transpose[ham]}
  }

NambuHermitian /:
Dagger[ham:NambuHermitian[{_?MatrixQ, _?MatrixQ}, rest___]] = ham

NambuHermitian /:
Plus[NambuHermitian[a_, any___], NambuHermitian[b_, other___]] :=
  NambuHermitian[a + b, any, other]

NambuHermitian /:
Times[z_, NambuHermitian[mm_, rest___]] :=
  NambuHermitian[z * mm, rest]

NambuHermitian /:
Dot[NambuHermitian[a_, any___], NambuHermitian[b_, other___]] :=
  NambuHermitian[theNambuDot[a, b], any, other]


NambuHermitian /:
ExpressionFor[op:NambuHermitian[_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

NambuHermitian /: (* fallback *)
ExpressionFor[op_NambuHermitian, ___] = op


NambuHermitian /:
Matrix[NambuHermitian[ham_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] := Module[
  { ff = Select[ss, FermionQ],
    rr = Select[ss, Not @* FermionQ],
    mm, nf },
  nf = Length[ff];
  
  (* Jordan-Wigner transformation *)
  mm = Table[PadRight[Table[3, k-1], nf], {k, nf}] + 4*One[nf];
  mm = ThePauli /@ mm;
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
Multiply[pre___, opr_NambuHermitian, ws_NambuState] := Multiply[pre, opr @ ws]

NambuHermitian /:
Multiply[pre___, opr_NambuHermitian, fs_Ket] := Multiply[pre, opr[NambuState @ fs]]

(*
NambuHermitian[new_?NambuMatrixQ, ___][NambuState[uv_, ops_, rest___]] :=
  NambuState[theNambuDot[new, uv], ops, rest]
  *)
(* NOTE: This is dangerous, the resulting uv is not unitary any longer. *)
(* NOTE: As long as syntax is concerned, this works also for vacuum state. *)

(**** </NambuHermitian> ****)


(**** <NambuGreen> ****)

NambuGreen::usage = "NambuGreen[{grn, anm}] represents the matrix of single-particle Green's functions in the Nambu space that is characterized by the n\[Times]n matrix grn of normal Green's functions and the n\[Times]n matrix anm of anomalous Green's functions."

NambuGreen /:
MakeBoxes[grn:NambuGreen[mm_?NambuMatrixQ, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    NambuGreen, grn, None,
    { BoxForm`SummaryItem @ { "Modes: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ mm }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, mm] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[mm]

(* zero in the Nambu space *)
NambuGreen[0, n_Integer, rest___] :=
  NambuGreen[NambuZero[n], rest]

(* zero in the Nambu space *)
(* backward compatibility *)
NambuGreen[0, cc:{___?FermionQ}, rest___] :=
  NambuGreen[0, Length @ cc, rest]

(* identity in the Nambu space *)
NambuGreen[1, n_Integer, rest___] :=
  NambuGreen[NambuOne[n], cc, rest]

(* identity in the Nambu space *)
(* backward compatibility *)
NambuGreen[1, cc:{___?FermionQ}, rest___] :=
  NambuGreen[1, Length @ cc]


NambuGreen[mat_?SquareMatrixQ, rest___] :=
  NambuGreen[NambuMatrix @ mat, rest]

NambuGreen[{mat_?SquareMatrixQ, 0}, rest___] :=
  NambuGreen[NambuMatrix @ {mat, 0}, rest]

NambuGreen[NambuGreen[grn_?NambuMatrixQ, rest___], more___] :=
  NambuGreen[grn, more, rest]


NambuGreen /:
MatrixForm @ NambuGreen[mm_?NambuMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NambuGreen /:
ArrayShort @ NambuGreen[mm_?NambuMatrixQ, rest___] :=
  Map[ArrayShort, mm]

NambuGreen /:
Normal @ NambuGreen[{g_, f_}, ___] :=
  ArrayFlatten @ {
    {g, f},
    {Topple[f], One[Dimensions @ g] - Transpose[g]}
  }

NambuGreen /:
Dagger[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, rest___]] = grn

NambuGreen /:
Plus[NambuGreen[a_, any___], NambuGreen[b_, other___]] :=
  NambuGreen[a + b, any, other]

NambuGreen /:
Times[z_, NambuGreen[mm_, rest___]] :=
  NambuGreen[z * mm, rest]

(**** </NambuGreen> ****)


RandomNambuUnitary::usage = "RandomNambuUnitary[n] returns a random NambuUnitary[{u, v}], where u and v are the n\[Times]n upper-left and upper-right blocks of the resulting Bogoliubov-de Gennes transformation matrix."

RandomNambuUnitary[n_Integer, rest___] := With[
  { barH = Normal[RandomNambuHermitian @ n] },
  NambuUnitary[MatrixExp[I barH], rest]
]

(* backward compatibility *)
RandomNambuUnitary[cc:{__?FermionQ}, rest___] :=
  RandomNambuUnitary[Length @ cc]


RandomNambuHermitian::usage = "RandomNambuHermitian[n] returns a random NambuHermitian[{ham, del}], where ham is an n\[Times]n Hermitian matrix and del is an n\[Times]n anti-symmetric matrix."

RandomNambuHermitian[n_Integer, rest___] :=
  NambuHermitian[{RandomHermitian[n], RandomAntisymmetric[n]}, rest]

(* backward compatibility *)
RandomNambuHermitian[cc:{__?FermionQ}, rest___] :=
  RandomNambuHermitian[Length @ cc, rest]


RandomNambuGreen::usage = "RandomNambuGreen[n] returns a random NambuGreen[{grn, anm}], where grn is an n\[Times]n matrix representing the normal Green's function and anm is an n\[Times]n anti-symmetric matrix representing the anomalous Green's function."

RandomNambuGreen[n_Integer, rest___] := Module[
  { trs = Normal @ RandomNambuUnitary[n],
    val = RandomReal[{0, 1}, n] },
  val = DiagonalMatrix @ Join[val, 1 - val];
  NambuGreen[trs . val . Topple[trs], rest]
]

(* backward compatibility *)
RandomNambuGreen[cc:{__?FermionQ}, rest___] :=
  RandomNambuGreen[Length @ cc, rest]


(**** <NambuOperator> ****)

NambuOperator::usage = "NambuOperator[mat] represents a sequence of quantum operations that are linear combinations in the creation and annihilation operators of the fermion modes with coefficients given by the elements of matrix mat."

NambuOperator /:
MakeBoxes[NambuOperator[ops_?MatrixQ, rest___], fmt_] := Module[
  { cc = {rest}, 
    m, n },
  cc = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ cc, {__Integer}], First[cc],
    True, All
  ];
  {m, n} = Dimensions[ops];
  BoxForm`ArrangeSummaryBox[
    NambuOperator, mat, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Operators: ", m }
    },
    { BoxForm`SummaryItem @ { "Transforms: ", ArrayShort /@ First @ PartitionInto[ops, {1, 2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuOperator[msr_FermiMeasurement] = msr

NambuOperator[trs_NambuUnitary] = trs

(* canonicalization *)
NambuOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  NambuOperatorFrom[ops, cc, rest]


(* shortcut *)
NambuOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  { id = One[2n],
    ii, kk, flag},
  {kk, flag} = Transpose[spec];
  ii = n*flag + kk;
  NambuOperator[id[[ii]], opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[NambuOperator::flag, flag]; False 
  ]
]

(* shortcut *)
NambuOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  NambuOperator[{spec}, n]


NambuOperator[{}, ___][any_] = any

NambuOperator[spec__][fs_Ket] := NambuOperator[spec][NambuState @ fs]

NambuOperator[trs_?MatrixQ, ___][NambuState[uv_?NambuMatrixQ, mm_, rest___]] :=
  NambuState[uv, Join[trs . Normal[NambuUnitary @ uv], mm], rest]
(* NOTE: This works also for vacuum state. *)

NambuOperator /:
Dagger @ NambuOperator[ops_?MatrixQ, rest___] :=
  NambuOperator[NambuConjugateReverse @ ops, rest]


NambuOperator /: 
NonCommutativeQ[_NambuOperator] = True

NambuOperator /:
MultiplyKind[_NambuOperator] = Fermion

NambuOperator /:
Multiply[pre___, opr_NambuOperator, ws_NambuState] := Multiply[pre, opr @ ws]

NambuOperator /:
Multiply[pre___, opr_NambuOperator, fs_Ket] := Multiply[pre, opr[NambuState @ fs]]


NambuOperator /:
Matrix[NambuOperator[trs_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Dot @@ Matrix[NambuElements[trs, cc], ss]
]

NambuOperator /: (* fallback *)
Matrix[op_NambuOperator, rest___] := op * Matrix[1, rest]


NambuOperator /:
ExpressionFor[NambuOperator[trs_?MatrixQ, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Apply[Multiply, NambuElements[trs, cc]]  
]

NambuOperator /: (* fallback *)
ExpressionFor[op_NambuOperator, ___] = op 


NambuOperator /:
VacuumExpectation @ NambuOperator[trs_?MatrixQ, ___] :=
  Pfaffian @ WickMatrix[trs]

(**** </NambuOperator> ****)


RandomNambuOperator::usage = "RandomNambuOperator[k_Integer, n_Integer] ..."

RandomNambuOperator[k_Integer, n_Integer] :=
  NambuOperator[RandomMatrix[{k, 2n}]]

RandomNambuOperator[n_Integer] :=
  RandomNambuOperator[RandomInteger[{1, n}], n]


(**** <NambuElements> ****)

NambuElements::usage = "NambuElements[spec, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion operators corresponding to specification spec."

NambuElements[ops_?MatrixQ, cc:{__?FermionQ}] :=
  ops . Join[cc, Dagger @ cc]

NambuElements[NambuState[_?NambuMatrixQ, ops_?MatrixQ, ___], cc:{__?FermionQ}] :=
  NambuElements[ops, cc]

NambuElements[NambuOperator[trs_?MatrixQ, ___], cc:{__?FermionQ}] :=
  NambuElements[trs, cc]

(**** </NambuElements> ****)


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


(**** <FermiMeasurement> ****)

FermiMeasurement /:
Multiply[pre___, msr:FermiMeasurement[_Integer|{__Integer}], ws_NambuState] :=
  Multiply[pre, msr @ ws]

FermiMeasurement[k_Integer][ws:NambuState[uv_, trs_, ___]] := Module[
  { n = FermionCount[ws],
    nrm = NormSquare[ws],
    msr, dgr, mat, prb },
  msr = First @ NambuOperator[{{k, 0}, {k, 1}}, n]; (* c ** Dagger[c] *)
  msr = msr . Normal[NambuUnitary @ uv];

  dgr = NambuConjugateReverse[trs];

  mat = WickMatrix @ Join[dgr, msr, trs];
  prb = Re @ Sqrt @ Quiet[Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= nrm;
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[k] = 0;
    NambuOperator[{{k, 0}, {k, 1}}, n][ws] / Sqrt[prb*nrm],
    $MeasurementOut[k] = 1;
    NambuOperator[{{k, 1}, {k, 0}}, n][ws] / Sqrt[(1-prb)*nrm]
  ]
]

(**** </FermiMeasurement> ****)


(**** <WickLogarithmicNegativity> ****)

(* canonical form for BdG models *)
WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(* canonicalization *)
WickLogarithmicNegativity[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], rest__] :=
  WickLogarithmicNegativity[{gg, ff}, rest]

(* shortcut *)
WickLogarithmicNegativity[ws_NambuState, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickLogarithmicNegativity[WickGreenFunction[ws], kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

(**** </WickLogarithmicNegativity> ****)


WickExpectation[ws:NambuState[uv_, bb_, ___]][NambuOperator[ops_?MatrixQ, ___]] := Module[
  { aa = NambuConjugateReverse[bb],
    mat },
  mat = WickMatrix @ Join[aa, ops . Normal[NambuUnitary @ uv], bb];
  Pfaffian[mat] (* NOTE: The Nambu state is assumed to be normalized. *)
]


(**** <WickGreenFunction> ****)

(* shortcut *)
WickGreenFunction[ws_NambuState] :=
  WickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for BdG modelsl *)
WickGreenFunction[ws:NambuState[uv_?NambuMatrixQ, qq_?MatrixQ, ___], kk:{___Integer}] := Module[
  { uu = Normal @ NambuUnitary[uv],
    pp = NambuConjugateReverse[qq],
    aa, bb, wm, ff, gg, nc },
  nc = FermionCount[ws];
  aa = uu[[ kk ]];
  bb = uu[[ kk + nc ]];

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = WickMatrix[pp];
  wm[[1, 3]] = WickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = WickMatrix[qq];

  nc = Length[kk];
  gg = Normal @ Zero[{nc, nc}];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[i]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[i]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[i]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, nc}
  ];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, nc},
    {j, i+1, nc}
  ];

  ff = Normal @ Zero[{nc, nc}];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], aa[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], aa[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], aa[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    ff[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, nc},
    {j, i+1, nc}
  ];
  NambuGreen[{gg, ff}, cc]
  (* NOTE: The Nambu state is assumed to be normalized. *)
]

(* vacuum state *)
WickGreenFunction[ws:NambuState[uv_?NambuMatrixQ, z_?NumericQ, ___], kk:{___Integer}] := Module[
  { uu = Normal @ NambuUnitary[uv],
    aa, bb, wm, ff, gg, nc },
  nc = FermionCount[ws];
  aa = uu[[ kk ]];
  bb = uu[[ kk + nc ]];

  nc = Length[kk];
  gg = Normal @ Zero[{nc, nc}];
  Table[
    wm = N @ WickMatrix[{aa[[i]], bb[[i]]}];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ wm, Det::luc],
    {i, 1, nc}
  ];
  Table[
    wm = N @ WickMatrix[{aa[[i]], bb[[j]]}];
    gg[[i, j]] = Pfaffian @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, nc},
    {j, i+1, nc}
  ];

  ff = Normal @ Zero[{nc, nc}];
  Table[
    wm = N @ WickMatrix[{aa[[i]], aa[[j]]}];
    ff[[i, j]] = Pfaffian @ wm;
    ff[[j, i]] = -ff[[i, j]],
    {i, 1, nc},
    {j, i+1, nc}
  ];
  NambuGreen[{gg, ff}, cc]
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
