(* Tools for Nambu matrices *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ NambuMatrix, NambuMatrixQ };
{ NambuOne, NambuZero };
{ NambuUnitary, NambuHermitian, NambuGreen };
{ RandomNambuUnitary, RandomNambuHermitian, RandomNambuGreen };

{ NambuNonunitary, NambuJump, NambuOperator, NambuMeasurement };
{ RandomNambuNonunitary, RandomNambuJump, RandomNambuOperator, RandomNambuMeasurement };
{ NambuDampingOperator };

{ NambuElements, NambuCoefficients };

{ WickNonunitary, WickHermitian, WickJump, WickOperator, WickMeasurement };

Begin["`Private`"] (* Tools for Nambu matrices *)

(**** <NambuMatrix> ****)

NambuMatrix::usage = "NambuMatrix[mat] retruns the two n\[Times]n independent blocks at the upper-left and upper-right corners of the 2n\[Times]2n matrix mat."

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

NambuMatrixQ::usage = "NambuMatrixQ[{u, v}] returns True if the pair {u, v} of square matrices are compatible in size.\nNambuMatrixQ[{u, v}, test] requires also that test yield True when applied to each of the array elements in {u, v}. "

NambuMatrixQ[uv:{_?SquareMatrixQ, _?SquareMatrixQ}] := ArrayQ[uv]

NambuMatrixQ[uv:{_?SquareMatrixQ, _?SquareMatrixQ}, test_] := ArrayQ[uv, 3, test]

NambuMatrixQ[_] = False

NambuMatrixQ[_, _] = False

(**** </NambuMatrixQ> ****)


NambuOne::usage = "NambuOne[n] returns the pair {One[n], Zero[{n, n}]}, which represents the identity matrix in the Nambu space."

NambuOne[n_Integer] := {One @ n, Zero @ {n, n}}


NambuZero::usage = "NambuZero[n] returns the pair {Zero[{n, n}], Zero[{n, n}]}, which represents the zero matrix in the Nambu space."

NambuZero[n_Integer] := {Zero @ {n, n}, Zero @ {n, n}}


ToMajorana[mat_NambuHermitian] := ToMajorana[Normal @ mat]

ToMajorana[mat_NambuUnitary] := ToMajorana[Normal @ mat]

ToMajorana[mat_NambuGreen] := ToMajorana[Normal @ mat]


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
      BoxForm`SummaryItem @ { "Modes: ", FermionCount @ op }
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
MatrixForm[NambuHermitian[mm_?NambuMatrixQ, ___], opts___?OptionQ] :=
  Map[MatrixForm[#, opts]&, mm]

NambuHermitian /:
ArrayShort[NambuHermitian[mm_?NambuMatrixQ, ___], opts___?OptionQ] :=
  Map[ArrayShort[#, opts]&, mm]

NambuHermitian /:
Normal @ NambuHermitian[{ham_?MatrixQ, del_?MatrixQ}, ___] :=
  SparseArray @ ArrayFlatten @ {
    {ham, del},
    {ConjugateTranspose @ del, -Transpose[ham]}
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
  NambuHermitian[NambuDot[a, b], any, other]


NambuHermitian /:
ExpressionFor[op:NambuHermitian[_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

NambuHermitian /: (* fallback *)
ExpressionFor[op_NambuHermitian, ___] = op


NambuHermitian /:
Matrix[ham:NambuHermitian[_?NambuMatrixQ, ___]] := Module[
  { n = FermionCount[ham],
    mm },
  mm = theWignerJordanNambu[n];
  TensorContract[
    Transpose[ConjugateTranspose /@ mm, {3, 1, 2}] . Normal[ham] . mm / 2,
    {{2, 3}}
  ]
]

NambuHermitian /:
Matrix[ham:NambuHermitian[_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] := 
  MatrixEmbed[Matrix @ ham, Select[ss, FermionQ], ss]

NambuHermitian /: (* fallback *)
Matrix[op_NambuHermitian, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


NambuHermitian /:
NonCommutativeQ[_NambuHermitian] = True

NambuHermitian /:
MultiplyKind[_NambuHermitian] = Fermion

(**** </NambuHermitian> ****)


theWignerJordanNambu::usage = "theWignerJordanNambu[n] returns a list of matrix representations (in a single SparseArray) of spin operators that are associated with n fermion annihilation and creations operators under the Wigner-Joran transformation."

theWignerJordanNambu[n_Integer] := Module[
  { mm },
  mm = Table[PadRight[Table[3, k-1], n], {k, n}] + 4*One[n];
  mm = ThePauli /@ mm;
  SparseArray @ Join[mm, ConjugateTranspose /@ mm]
]


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
      BoxForm`SummaryItem @ { "Modes: ", Length @ First @ uv }
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
  SparseArray @ ArrayFlatten @ {
    {u, v},
    Conjugate @ {v, u}
  }

NambuUnitary /:
Dagger @ NambuUnitary[{u_?MatrixQ, v_?MatrixQ}, rest___] :=
  NambuUnitary[{ConjugateTranspose @ u, Transpose @ v}, rest]

NambuUnitary /:
Plus[NambuUnitary[a_, any___], NambuUnitary[b_, other___]] :=
  NambuUnitary[a + b, any, other]

NambuUnitary /:
Times[z_, NambuUnitary[mm_, rest___]] :=
  NambuUnitary[z * mm, rest]

NambuUnitary /:
Dot[NambuUnitary[a_, any___], NambuUnitary[b_, other___]] :=
  NambuUnitary[NambuDot[a, b], any, other]


NambuUnitary /:
ExpressionFor[op:NambuUnitary[uv_?NambuMatrixQ, ___], ss:{__?SpeciesQ}] :=
  ExpressionFor[Matrix[op, ss], ss]

NambuUnitary /: (* fallback *)
ExpressionFor[op_NambuUnitary, ___] = op


NambuUnitary /:
Matrix[op:NambuUnitary[uv_?NambuMatrixQ, ___]] := With[
  { barH = -I*MatrixLog[Normal @ op] },
  MatrixExp[I*Matrix[NambuHermitian @ barH]]
]

NambuUnitary /:
Matrix[op_NambuUnitary, ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ op, Select[ss, FermionQ], ss]

NambuUnitary /: (* fallback *)
Matrix[op_NambuUnitary, ss:{__?SpeciesQ}] := op * Matrix[1, ss]


NambuUnitary /:
NonCommutativeQ[_NambuUnitary] = True

NambuUnitary /:
MultiplyKind[_NambuUnitary] = Fermion

(**** </NambuUnitary> ****)


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
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ cc },
      BoxForm`SummaryItem @ { "Modes: ", Length @ First @ mm }
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


(* conversion to correlation matrix *)
NambuHermitian[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, rest___], more___] :=
  NambuHermitian[{One[Dimensions @ gg] - gg, -ff}, more, rest]

(* conversion to green's Funciton matrix *)
NambuGreen[NambuHermitian[{cc_?MatrixQ, ff_?MatrixQ}, rest___], more___] :=
  NambuGreen[{One[Dimensions @ cc] - cc, -ff}, more, rest]


NambuGreen /:
MatrixForm @ NambuGreen[mm_?NambuMatrixQ, rest___] :=
  Map[MatrixForm, mm]

NambuGreen /:
ArrayShort @ NambuGreen[mm_?NambuMatrixQ, rest___] :=
  Map[ArrayShort, mm]

NambuGreen /:
Normal @ NambuGreen[{g_, f_}, ___] :=
  SparseArray @ ArrayFlatten @ {
    {g, f},
    {ConjugateTranspose @ f, One[Dimensions @ g] - Transpose[g]}
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
  NambuGreen[trs . val . ConjugateTranspose[trs], rest]
]

(* backward compatibility *)
RandomNambuGreen[cc:{__?FermionQ}, rest___] :=
  RandomNambuGreen[Length @ cc, rest]


(**** <NambuDot> ****)

NambuDot::usage = "NambuDot[{u1,v1}, {u2,v2}] returns the reduced Nambu matrix corresponding to the matrix multiplication of two full Nambu matrices corresponding to {u1, v1} and {u2, v2}, respectively."

SetAttributes[NambuDot, Flat]

NambuDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

NambuDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barU := {{U, V}, Conjugate @ {V, U}} *)

(**** </NambuDot> ****)


(**** <NambuConjugateReverse> ****)

NambuConjugateReverse::usage = "NambuConjugateReverse[mat] returns the reverse of {Conjugate[B], Conjugate[A]} for matrix mat with block structure mat = {A, B}."

NambuConjugateReverse[mat_?MatrixQ] :=
  Conjugate @ Reverse @ ArrayFlatten[ 
    Reverse /@ PartitionInto[mat, {1, 2}] 
  ]

(**** </NambuConjugateReverse> ****)


(**** <NambuDampingOperator> ****)

NambuDampingOperator::usage = "NambuDampingOperator[jmp] returns a pair {dmp, gmm} of the quadratic kernel dmp and remaining constant term gmm of the effective damping operator in the Nambu normal ordering that corresponds to the quantum jump operators jmp in the NambuJump or NambuMeasurement form.\nThis function is intended for self-consistency checks. Most calculations concerning fermionic quantum computation are more efficient with  WickDampingOperator."

NambuDampingOperator[NambuJump[jmp_?MatrixQ, ___]] := Module[
  {uu, vv, aa, bb, dd},
  {uu, vv} = First @ PartitionInto[jmp, {1, 2}];
  aa = ConjugateTranspose[uu] . uu / 2;
  bb = ConjugateTranspose[uu] . vv / 2;
  dd = ConjugateTranspose[vv] . vv / 2;
  { NambuHermitian @ {aa - Transpose[dd], bb - Transpose[bb]},
    Re[Tr[aa] + Tr[dd]]/2 }
]

NambuDampingOperator[NambuMeasurement[msr_?MatrixQ, ___]] := Module[
  {uu, vv, aa, bb, dd, nn},
  {uu, vv} = First @ PartitionInto[msr, {1, 2}];
  nn = Map[NormSquare, msr];
  nn = SparseArray[DiagonalMatrix @ nn];
  aa = ConjugateTranspose[uu] . nn . uu / 2;
  bb = ConjugateTranspose[uu] . nn . vv / 2;
  dd = ConjugateTranspose[vv] . nn . vv / 2;
  { NambuHermitian @ {aa - Transpose[dd], bb - Transpose[bb]},
    Re[Tr[aa] + Tr[dd]]/2 }
]

(**** </NambuDampingOperator> ****)


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

(* conversion *)
NambuNonunitary /:
WickNonunitary[
  NambuNonunitary[
    {ham_NambuHermitian, dmp_NambuHermitian, gmm_?NumericQ},
    opts___?OptionQ
  ],
  more___?OptionQ
] := WickNonunitary[{WickHermitian @ ham, WickHermitian @ dmp, gmm}, more, opts]

(* conversion *)
NambuNonunitary /:
ToMajorana[non_NambuNonunitary] := WickNonunitary[non]

(**** </NambuNonunitary> ****)


RandomNambuNonunitary::usage = "RandomNambuNonunitary[n] randomly generates a NambuNonunitary object."

RandomNambuNonunitary[n_Integer, opts___?OptionQ] := NambuNonunitary[
  { RandomNambuHermitian @ n, RandomNambuHermitian @ n, RandomReal @ {0, 1} },
  opts
]


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
    { BoxForm`SummaryItem @ { "Coefficients: ",
        ArrayShort /@ First @ PartitionInto[mat, {1, 2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuJump /:
Normalize[NambuJump[mat_?MatrixQ, rest___], ___] :=
  NambuJump[Normalize /@ mat, rest]

(* conversion *)
NambuJump /:
WickJump[NambuJump[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickJump[ToMajorana /@ mat, more, opts] /; (* NOT ToMajorana @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[NambuJump::odd, ArrayShort @ mat, Dimensions @ mat];
    False
  ]

(* conversion *)
NambuJump /:
ToMajorana[non_NambuJump] := WickJump[non]

NambuJump /:
Matrix[jmp_NambuJump, rest___] :=
  Matrix[ToMajorana @ jmp, rest]

NambuJump /:
Dagger @ NambuJump[mat_?MatrixQ, rest___] := 
  NambuJump[NambuConjugateReverse @ mat, rest]

NambuJump /:
MatrixForm[NambuJump[mat_?MatrixQ, rest___], opts___?OptionQ] :=
  Map[MatrixForm[#, opts]&, First @ PartitionInto[mat, {1, 2}]]

NambuJump /:
ArrayShort[NambuJump[mat_?MatrixQ, rest___], opts___?OptionQ] :=
  Map[ArrayShort[#, opts]&, First @ PartitionInto[mat, {1, 2}]]

NambuJump /:
Plus[NambuJump[a_, any___], NambuJump[b_, other___]] :=
  NambuJump[a + b, any, other]

NambuJump /:
Times[z_, NambuJump[mm_, rest___]] :=
  NambuJump[z * mm, rest]

(**** </NambuJump> ****)


RandomNambuJump::usage = "RandomNambuJump[k_Integer, n_Integer] returns NambuJump consisting of k linear combinations of Dirac fermion operators."

RandomNambuJump[k_Integer, n_Integer, opts___?OptionQ] :=
  NambuJump[RandomMatrix @ {k, 2n}, opts]

RandomNambuJump[n_Integer, opts___?OptionQ] :=
  RandomNambuJump[RandomInteger @ {1, n}, n, opts]


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
    { BoxForm`SummaryItem @ { "Coefficients: ",
        ArrayShort /@ First @ PartitionInto[mat, {1, 2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuOperator /:
WickOperator[NambuOperator[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickOperator[ToMajorana /@ mat, more, opts] /;   (* NOT ToMajorana @ mat. *)
  If[ EvenQ[Last @ Dimensions @ mat], True,
    Message[NambuOperator::odd, ArrayShort @ mat, Dimensions @ mat];
    False
  ]

NambuOperator /:
ToMajorana[non_NambuOperator] := WickOperator[non]

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
    { BoxForm`SummaryItem @ { "Coefficients: ",
        ArrayShort /@ First @ PartitionInto[mat, {1, 2}] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

NambuMeasurement /:
Normalize[NambuMeasurement[mat_?MatrixQ, rest___], ___] :=
  NambuMeasurement[Normalize /@ mat, rest]

NambuMeasurement /:
Times[z_, NambuMeasurement[mm_, rest___]] :=
  NambuMeasurement[z * mm, rest]

NambuMeasurement /:
Dagger @ NambuMeasurement[mat_?MatrixQ, rest___] := 
  NambuMeasurement[NambuConjugateReverse @ mat, rest]

NambuMeasurement /:
MatrixForm[NambuMeasurement[mat_?MatrixQ, rest___], opts___?OptionQ] :=
  Map[MatrixForm[#, opts]&, First @ PartitionInto[mat, {1, 2}]]

NambuMeasurement /:
ArrayShort[NambuMeasurement[mat_?MatrixQ, rest___], opts___?OptionQ] :=
  Map[ArrayShort[#, opts]&, First @ PartitionInto[mat, {1, 2}]]

NambuMeasurement /:
Matrix[msr_NambuMeasurement, rest___] :=
  Matrix[ToMajorana @ msr, rest]

(* alias *)
NambuMeasurement[kk:(_Integer | {___Integer}), rest___] :=
  WickMeasurement[kk, rest]

(* conversion *)
NambuMeasurement /:
ToMajorana[msr_NambuMeasurement] := WickMeasurement[msr]

(* conversion *)
NambuMeasurement /:
WickMeasurement[NambuMeasurement[mat_?MatrixQ, opts___?OptionQ], more___?OptionQ] :=
  WickMeasurement[ToMajorana /@ mat, more, opts] /;   (* NOT ToMajorana @ mat. *)
  theNambuMeasurementQ[mat]

theNambuMeasurementQ::usage = "theNambuMeasurementQ[m] returns True if each linear combination \
  b[i] = Sum[m[[i, j]] a[j], {j, n}] + Sum[m[[i,n+j]] Dagger[a[j]], {j, n}] \
  of Dirac fermion operators a[j] and Dagger[a[j]] is individually a proper dressed Dirac fermion modes. Note that the different dressed fermion modes associated with different rows of m do not have to be mutually orthogonal."

theNambuMeasurementQ[mat_?MatrixQ] :=
  ArrayZeroQ[Dot @@@ Map[PartitionInto[#,2]&, mat]]

(**** </NambuMeasurement> ****)


RandomNambuMeasurement::usage = "RandomNambuMeasurement[k, n] randomly generates a NambuMeaurement for k dressed fermion modes from n bare fermion modes.\nRandomNambuMeasurement[n] randomly selects k from {1,2,\[Ellipsis],n}."

RandomNambuMeasurement[k_Integer, n_Integer] := 
  NambuMeasurement @ Table[RandomChoice @ Normal @ RandomNambuUnitary[n], k]

RandomNambuMeasurement[n_Integer] :=
  RandomNambuMeasurement[RandomInteger @ {1, n}, n]


(**** <NambuElements> ****)

NambuElements::usage = "NambuElements[mat,{a1,\[Ellipsis],an}] returns a list of linear combinations of the annihilation and creation operators of Dirac fermion modes {a1,\[Ellipsis],an} with the coefficients specified by the elements of matrix mat.\nNambuElements[mat, {c1,c2,\[Ellipsis],c2n}] returns a list of linear combinations of Majorana fermion operators {c1, c2, \[Ellipsis]}, where the elements of complex matrix mat are the coefficients in the equivalent linear combinations of Dirac fermion operators (not the Majorana fermion operators themselves) corresponding to the Majorana fermion modes."

NambuElements[mat_?MatrixQ, aa:{__?FermionQ}] :=
  Dot[mat, Join[aa, Dagger @ aa]]

NambuElements[mat_?MatrixQ, cc:{__?MajoranaQ}] :=
  Dot[ToMajorana /@ mat, cc]

NambuElements[
  (WickOperator|WickJump|WickMeasurement)[mat_?MatrixQ, ___],
  spec:({__?FermionQ} | {__?MajoranaQ})
] := NambuElements[mat, spec]

(**** </NambuElements> ****)


(**** <NambuCoefficients> ****)

NambuCoefficients::usage = "NambuCoefficients[expr, {a1,\[Ellipsis],an}] gets a vector or matrix of coefficients in a linear combination or linear combinations of the annihilation and creation operators of Dirac fermion modes {a1,\[Ellipsis],an}.\nNambuCoefficients[expr, {c1,c2,\[Ellipsis],c2n} returns a vector or matrix of coefficients in a linear combination or linear combinations of Majorana fermion operators {c1,c2,\[Ellipsis]}, and transforms it to a vector or matrix of coefficients in the equivalent linear combination(s) of the Majorana operators corresponding to the Dirac fermion modes."

NambuCoefficients::nlin = "`` is not a linear combination of Dirac or Majorana fermion operators of modes ``."

NambuCoefficients[spec:({__?FermionQ} | {__?MajoranaQ})][expr_] :=
  NambuCoefficients[expr, spec]

NambuCoefficients[expr_List, spec:({__?FermionQ} | {__?MajoranaQ})] :=
  Map[NambuCoefficients[spec], expr]

NambuCoefficients[expr_, cc:{__?MajoranaQ}] :=
  ToDirac @ Coefficient[expr, cc, 1] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[NambuCoefficients::nlin, expr, cc];
    False
  ]

NambuCoefficients[expr_, aa:{__?FermionQ}] :=
  Coefficient[expr, Join[aa, Dagger @ aa], 1] /;
  If[ theWickLinearQ[expr, aa], True,
    Message[NambuCoefficients::nlin, expr, aa];
    False
  ]

(**** </NambuCoefficients> ****)


(**** <FermionCount> ****)

FermionCount[obj_?NambuMatrixQ] := Length[First @ obj]

FermionCount[NambuUnitary[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuUnitary[uv_?NambuMatrixQ, ___]] := Length[First @ uv]

FermionCount[NambuHermitian[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuHermitian[ham_?NambuMatrixQ, ___]] := Length[First @ ham]

FermionCount[NambuGreen[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuGreen[grn_?NambuMatrixQ, ___]] := Length[First @ grn]

FermionCount[NambuJump[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[NambuMeasurement[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

FermionCount[NambuOperator[mat_?MatrixQ, ___]] := Last[Dimensions @ mat]/2

(**** </FermionCount> ****)

End[]

EndPackage[]
