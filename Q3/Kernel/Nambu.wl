BeginPackage["Q3`"]

{ NambuMatrix, NambuMatrixQ };
{ NambuOne, NambuZero };
{ NambuRandomMatrix };

Begin["`Private`"]

(**** <NambuMatrix> ****)

NambuMatrix::usage = "NambuMatrix[{a, b}, type] represents a 2n\[Times]2n matrix of type in the Nambu space, the n\[Times]n upper-left and upper-right blocks of which are given by a and b, respectively.\nNambuMatrix[mat] returns the pair {a, b}, where a and b are the n\[Times]n upper-left and upper-right blocks, respectively, of 2n\[Times]2n matrix mat.\nNambuMatrix[mat, type] returns NambuMatrix[{a, b}, type], where a and b are as above.\nNambuMatrix[{mat, 0}] returns the pair {mat, Zero @ Dimenions @ mat}.\nNambuMatrix[{mat, 0}, type] is equivalent to NambuMatrix[NambuMatrix[{mat, 0}], type]."

NambuMatrix::odd = "Matrix `` has odd dimenions."

NambuMatrix /:
MakeBoxes[op:NambuMatrix[trs_?NambuMatrixQ, type_], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NambuMatrix, op, None,
    { BoxForm`SummaryItem @ { "Type: ", type },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ First @ trs }
    },
    { BoxForm`SummaryItem @ { "Blocks: ", Map[ArrayShort, trs] }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; ArrayQ[trs]


NambuMatrix[mat_?SquareMatrixQ] := Module[
  { n = (Length[mat] + 1) / 2 },
  Message[NambuMatrix::odd, mat];
  { mat[[ ;;n, ;;n]], Zero[n] }
] /; OddQ[Length @ mat]

NambuMatrix[mat_?SquareMatrixQ] := With[
  { n = Length[mat] / 2 },
  { mat[[ ;;n, ;;n]], mat[[ ;;n, n+1;; ]] }
]

NambuMatrix[mat_?SquareMatrixQ, type_] :=
  NambuMatrix[NambuMatrix[mat], type]


NambuMatrix[{mat_?SquareMatrixQ, 0}] :=
  {mat, Zero @ Dimensions @ mat}

NambuMatrix[{mat_?SquareMatrixQ, 0}, type_] :=
  NambuMatrix[{mat, Zero @ Dimensions @ mat}, type]


NambuMatrix /:
MatrixForm @ NambuMatrix[mm:{_, _}, _] := Map[MatrixForm, mm]

NambuMatrix /:
Part[NambuMatrix[{a_?MatrixQ, b_?MatrixQ}, type_], spec__] :=
  NambuMatrix[{Part[a, spec], Part[b, spec]}, type]


NambuMatrix /:
Normal @ NambuMatrix[{u_, v_}, "Unitary"] :=
  ArrayFlatten @ {
    {u, v},
    Conjugate @ {v, u}
  }

NambuMatrix /:
Normal @ NambuMatrix[{ham_, del_}, "Hermitian"] :=
  ArrayFlatten @ {
    {ham, del},
    {Topple[del], -Transpose[ham]}
  }

NambuMatrix /:
Normal @ NambuMatrix[{g_, f_}, "Green's"] :=
  ArrayFlatten @ {
    {g, f},
    {Topple[f], One[Dimensions @ g] - Transpose[g]}
  }


NambuMatrix /:
Topple[NambuMatrix[mm_?NambuMatrixQ, "Unitary"]] :=
  NambuMatrix[theNambuTopple @ mm, "Unitary"]

NambuMatrix /:
Topple[NambuMatrix[{ham_?MatrixQ, del_?MatrixQ}, "Hermitian"]] :=
  NambuMatrix[{Topple @ ham, del}, "Hermitian"]

NambuMatrix /:
Topple[NambuMatrix[{g_?MatrixQ, f_?MatrixQ}, "Green's"]] :=
  NambuMatrix[{Topple @ g, f}, "Green's"]


NambuMatrix /:
  Plus[NambuMatrix[a_, type_], NambuMatrix[b_, type_]] :=
    NambuMatrix[a + b, type]

NambuMatrix /:
  Times[z_, NambuMatrix[mm_, type_]] :=
    NambuMatrix[z * mm, type]

NambuMatrix /:
Dot[NambuMatrix[a_, type_], NambuMatrix[b_, type_]] :=
  NambuMatrix[theNambuDot[a, b], type]

(**** </NambuMatrix> ****)


(**** <NambuMatrixQ> ****)

NambuMatrixQ::usage = "NambuMatrixQ[{u, v}] returns True if the pair {a, b} of square matrices are compatible in size."

NambuMatrixQ[uv:{_?MatrixQ, _?MatrixQ}] := ArrayQ[uv]

NambuMatrixQ[_] = False

(**** </NambuMatrixQ> ****)


NambuOne::usage = "NambuOne[n] returns the pair {One[n], Zero[{n, n}]}, which represents the identity matrix in the Nambu space."

NambuOne[n_Integer] := {One @ n, Zero @ {n, n}}

NambuOne[n_Integer, type_] := NambuMatrix[NambuOne @ n, type]


NambuZero::usage = "NambuZero[n] returns the pair {Zero[{n, n}], Zero[{n, n}]}, which represents the zero matrix in the Nambu space."

NambuZero[n_Integer] := {Zero @ {n, n}, Zero @ {n, n}}

NambuZero[n_Integer, type_] := NambuMatrix[NambuZero @ n, type]


(**** <theNambuDot> ****)

theNambuDot::usage = "theNambuDot[{u1,v1}, {u2,v2}] returns the reduced Nambu matrix corresponding to the matrix multiplication of two full Nambu matrices corresponding to {u1, v1} and {u2, v2}, respectively."

SetAttributes[theNambuDot, Flat]

theNambuDot[u_?MatrixQ, v_?MatrixQ] := Dot[u, v]

theNambuDot[{u1_?MatrixQ, v1_?MatrixQ}, {u2_?MatrixQ, v2_?MatrixQ}] :=
  {u1.u2 + v1.Conjugate[v2], u1.v2 + v1.Conjugate[u2]}
(* Convention: barU := {{U, V}, Conjugate @ {V, U}} *)

(**** </theNambuDot> ****)


(**** <theNambuTopple> ****)

theNambuTopple::usage = "theNambuTopple[{u, v}] ..."

theNambuTopple[{u_?MatrixQ, v_?MatrixQ}] := {Topple @ u, Transpose @ v}
(* NOTE: This works only for UNITARY matrices of the form {{u, v}, {Conjugate[v], Conjugate[u]}}in the Nambu space. *)

(**** </theNambuTopple> ****)


(**** <NambuRandomMatrix> ****)

NambuRandomMatrix::usage = "NambuRandomMatrix[n, type] returns a randomly generated matrix of type in the Nambu space with the n\[Times]n upper-left and upper-right blocks."

NambuRandomMatrix[n_Integer, "Hermitian"] :=
  NambuMatrix[
    { RandomHermitian[n], RandomAntisymmetric[n] },
    "Hermitian"
  ]

NambuRandomMatrix[n_Integer, "Unitary"] := With[
  { barH = NambuRandomMatrix[n, "Hermitian"] },
  NambuMatrix[MatrixExp[I * Normal[barH]], "Unitary"]
]

(**** </NambuRandomMatrix> ****)

End[]

EndPackage[]
