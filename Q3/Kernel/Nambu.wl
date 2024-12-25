(* Tools for Nambu matrices *)

BeginPackage["Q3`"]

{ NambuMatrix, NambuMatrixQ };
{ NambuOne, NambuZero };
{ NambuUnitary, NambuHermitian, NambuGreen };
{ RandomNambuUnitary, RandomNambuHermitian, RandomNambuGreen };


Begin["`Private`"] (* Tools for Nambu matrices *)

AddElaborationPatterns[_NambuUnitary];

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
Matrix[ham:NambuHermitian[_?NambuMatrixQ, ___]] := Module[
  { n = FermionCount[ham],
    mm },
  
  (* Jordan-Wigner transformation *)
  mm = Table[PadRight[Table[3, k-1], n], {k, n}] + 4*One[n];
  mm = ThePauli /@ mm;
  mm = Join[mm, Topple /@ mm];

  TensorContract[
    Transpose[Topple /@ mm, {3, 1, 2}] . Normal[ham] . mm / 2,
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


(**** <theNambuDot> ****)

theNambuDot::usage = "theNambuDot[{u1,v1}, {u2,v2}] returns the reduced Nambu matrix corresponding to the matrix multiplication of two full Nambu matrices corresponding to {u1, v1} and {u2, v2}, respectively."

SetAttributes[theNambuDot, Flat]

theNambuDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

theNambuDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barU := {{U, V}, Conjugate @ {V, U}} *)

(**** </theNambuDot> ****)

End[]

EndPackage[]
