(* -*- mode:math -*- *)
BeginPackage["QuantumMob`Q3`", {"System`"}];

{ Supermap, ChoiMatrix, ChoiMatrixQ,
  SuperMatrixQ, ToSuperMatrix, ToChoiMatrix };

{ ChoiMultiply, ChoiTopple };

{ Lindbladian, DampingOperator };

{ LieBasisSupermap, LieBasisMatrix };

{ LindbladSolve, NLindbladSolve,
  LindbladConvert };

{ LindbladSteady };

{ LindbladSimulate };


Begin["`Private`"];

(**** <Supermap> ****)
Supermap::usage = "Supermap[{op1, op2, \[Ellipsis]}] represents a completely positive supermap specified by the Kraus elements op1, op2, \[Ellipsis], which may be matrices or operators.";

Supermap::incmp = "The operators/matrices `` are not compatible with each other.";

Supermap::wrong = "`` trying to operate on a wrong object ``.";

(* In terms of Choi matrix *)
Supermap /:
Dagger @ Supermap[tsr_?ChoiMatrixQ] :=
  Supermap[ChoiTopple @ tsr]

Supermap[tsr_?ChoiMatrixQ] := Supermap[SparseArray @ tsr] /;
  Head[tsr] =!= SparseArray

Supermap[tsr_?ChoiMatrixQ][rho_?SquareMatrixQ] :=
  ChoiMultiply[tsr, rho] /;
  Part[Dimensions @ tsr, {2, 4}] == Dimensions[rho]

Supermap[tsr_?ChoiMatrixQ][rho_?SquareMatrixQ] := (
  Message[Supermap::wrong, Supermap[tsr], rho];
  rho
)


(* In terms of matrices *)
Supermap[a_?MatrixQ, b_?MatrixQ] := (
  Message[Supermap::incmp, Normal @ {a, b}];
  Identity
) /; Not @ ArrayQ @ {a, b}

Supermap[ops:{__?MatrixQ}, cc_?VectorQ] := (
  Message[Supermap::incmp, Normal @ {ops}];
  Identity
) /; Not @ And[ArrayQ @ ops, Length[ops] == Length[cc]]

Supermap[ops:{__?MatrixQ}, cc_?MatrixQ] :=  (
  Message[Supermap::incmp, Normal @ {ops, cc}];
  Identity
) /; Not @ And[
    ArrayQ @ ops,
    Equal @@ Flatten @ {Length @ ops, Dimensions @ cc}
  ]

Supermap[ops:{__?MatrixQ}] :=  (
  Message[Supermap::incmp, Normal @ {ops}];
  Identity
) /; Not @ ArrayQ @ {ops}


Supermap[a_?MatrixQ] := Supermap @ ChoiMatrix[a]

Supermap[a_?MatrixQ, b_?MatrixQ] := Supermap @ ChoiMatrix[a, b]

Supermap[ops:{__?MatrixQ}] :=
  Supermap @ ChoiMatrix[ops]

Supermap[ops:{__?MatrixQ}, cc_?VectorQ] :=
  Supermap @ ChoiMatrix[ops, cc]

Supermap[ops:{__?MatrixQ}, cc_?MatrixQ] :=
  Supermap @ ChoiMatrix[ops, cc]


(* In terms of operator expressions *)
Supermap[a_] := Supermap[{a}] /; Not @ Or[ListQ @ a, ChoiMatrixQ @ a]

Supermap[a_, b_] := Supermap[{a, b}, ThePauli[4]] /; Not[ListQ @ a]

HoldPattern @ Supermap[ops:{__}][rho_] :=
  Garner @ Total @ Multiply[ops, rho, Dagger @ ops]

HoldPattern @ Supermap[ops:{__}, cc_?VectorQ][rho_] :=
  Garner[ cc . Multiply[ops, rho, Dagger @ ops] ]

HoldPattern @ Supermap[ops:{__}, cc_?MatrixQ][rho_] := Garner @ Total @ Total[
  cc * Outer[Multiply, ops, Multiply[rho, Dagger @ ops]]
]


(* Formatting *)
Supermap /:
MakeBoxes[spr:Supermap[ops:{__}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    Supermap, spr, None,
    { BoxForm`SummaryItem @ {"Type: ", "completely positive"},
      BoxForm`SummaryItem @ {"Kraus elements: ", Length @ ops} },
    { BoxForm`SummaryItem @ {"Kraus elements: ", ops} },
    fmt, "Interpretable" -> Automatic ] /;
  Not[ChoiMatrixQ @ ops]

Supermap /:
MakeBoxes[spr:Supermap[ops:{__}, cc_?VectorQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    Supermap, spr, None,
    { BoxForm`SummaryItem @ {"Operators: ", Length @ ops},
      BoxForm`SummaryItem @ {"Factors: ", Length @ cc} },
    { BoxForm`SummaryItem @ {"Operators: ", ops},
      BoxForm`SummaryItem @ {"Factors: ", cc} },
    fmt, "Interpretable" -> Automatic ]

Supermap /:
MakeBoxes[spr:Supermap[ops:{__}, cc_?MatrixQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    Supermap, spr, None,
    { BoxForm`SummaryItem @ {"Operators: ", Length @ ops},
      BoxForm`SummaryItem @ {"Factors: ",
        StringForm[
          "``\[ThinSpace]\[Times]\[ThinSpace]``",
          Sequence @@ Dimensions @ cc ] } },
    { BoxForm`SummaryItem @ {"Operators: ", ops},
      BoxForm`SummaryItem @ {"Factors: ", MatrixForm @ cc} },
    fmt, "Interpretable" -> Automatic ]
(**** </Supermap> ****)


(**** <ChoiMultiply> ****)
ChoiMultiply::usage = "ChoiMultiply[a,b,\[Ellipsis]] returns the successive multiplication of Choi matrices a, b, \[Ellipsis].";

ChoiMultiply[a_?ChoiMatrixQ, b_?ChoiMatrixQ] :=
  ToChoiMatrix[ToSuperMatrix[a] . ToSuperMatrix[b]]

(* 2022-07-23: This is too slow. Probably because TensorContract and
   TensorProduct does not take advantage of SparseArray? *)
(*
ChoiMultiply[a_?ChoiMatrixQ, b_?ChoiMatrixQ] :=
  Transpose[TensorContract[TensorProduct[a, b], {{2, 5}, {4,7}}], 2<->3]
 *)

ChoiMultiply[tsr_?ChoiMatrixQ, rho_?SquareMatrixQ] :=
  ArrayReshape[ToSuperMatrix[tsr] . Flatten[rho], Dimensions @ rho]

(* 2022-07-23: This is also slower. *)
(*
ChoiMultiply[a_?ChoiMatrixQ, b_?SquareMatrixQ] :=
  TensorContract[TensorProduct[a, b], {{2, 5}, {4,6}}]
 *)

ChoiMultiply[a_?ChoiMatrixQ, bb__?ChoiMatrixQ, rest___] :=
  ChoiMultiply[Fold[ChoiMultiply, a, {bb}], rest]


ChoiTopple::usage = "ChoiTopple[tsr] returns the Hermitian conjugate of Choi matrix tsr.";
ChoiTopple[tsr_?ChoiMatrixQ] := Transpose[Conjugate @ tsr, {2, 1, 4, 3}]
(**** </ChoiMultiply> ****)


(**** <ChoiMatrix> ****)
ChoiMatrix::usage = "ChoiMatrix[op1, op2, \[Ellipsis]] returns the Choi matrix corresponding to the superoperator represented by the Kraus elements op1, op2, \[Ellipsis].";

ChoiMatrix[Supermap[tsr_?ChoiMatrixQ]] := tsr;

ChoiMatrix[Supermap[spec__]] := ChoiMatrix[spec];


ChoiMatrix[a_?MatrixQ] := TensorProduct[a, Conjugate @ a]

ChoiMatrix[a_?MatrixQ, b_?MatrixQ] :=
  TensorProduct[a, Conjugate @ b] /; ArrayQ @ {a, b}

ChoiMatrix[array_?(ArrayQ[#, 3]&)] := With[
  { tsr = SparseArray[array] },
  Dot[Transpose[tsr, {3, 1, 2}], Conjugate @ tsr]
];

ChoiMatrix[array_?(ArrayQ[#, 3]&), cc_?VectorQ] :=
  ChoiMatrix[array, DiagonalMatrix @ cc];

ChoiMatrix[array_?(ArrayQ[#, 3]&), cc_?MatrixQ] := With[
  { tsr = SparseArray[array] },
  Dot[Transpose[tsr, {3, 1, 2}], SparseArray @ cc, Conjugate @ tsr]
 ];


ChoiMatrix[most__, S_?SpeciesQ] := ChoiMatrix[most, FlavorCap @ {S}]

ChoiMatrix[most__, ss:{__?SpeciesQ}] :=
  ChoiMatrix[most, FlavorCap @ ss] /;
  Not[FlavorCapQ @ ss]


ChoiMatrix[ops:{__}, ss:{__?SpeciesQ}] := With[
  { qq = Agents @ Join[ops, ss] },
  ChoiMatrix @ Matrix[ops, qq]
 ]

ChoiMatrix[ops:{__}] := With[
  { qq = Agents[ops] },
  ChoiMatrix @ Matrix[ops, qq]
 ] /; FreeQ[ops, _Pauli]

ChoiMatrix[ops:{__}] := ChoiMatrix @ Matrix[ops]


ChoiMatrix[ops:{__}, cc:(_?MatrixQ|_?VectorQ), ss:{__?SpeciesQ}] := With[
  { qq = Agents @ Join[ops, ss] },
  ChoiMatrix[Matrix[ops, qq], cc]
 ]

ChoiMatrix[ops:{__}, cc:(_?MatrixQ|_?VectorQ)] := With[
  { qq = Agents[ops] },
  ChoiMatrix[Matrix[ops, qq], cc]
 ] /; FreeQ[ops, _Pauli]

ChoiMatrix[ops:{__}, cc:(_?MatrixQ|_?VectorQ)] := ChoiMatrix[Matrix[ops], cc]


HoldPattern @ ChoiMatrix @ Lindbladian[ops:{_, __}] :=
  ChoiMatrix @ Lindbladian @ Matrix[ops]
(**** </ChoiMatrix> ****)


ChoiMatrixQ::usage = "ChoiMatrixQ[tensor] returns True if tensor has the structure of Choi matrix, i.e., a tensor of rank four with dimensions m x n x m x n.";

ChoiMatrixQ[tsr_?ArrayQ] := And[
  TensorRank[tsr] == 4,
  AllTrue[Transpose @ Partition[Dimensions @ tsr, 2], Apply[Equal]]
 ]

(* Too dangerous! *)
(* ChoiMatrixQ[assoc_Association] := AllTrue[assoc, ChoiMatrixQ] *)
ChoiMatrixQ[_] = False


SuperMatrixQ::usage = "SuperMatrixQ[mat] returns True if matrix mat is a super-matrix, i.e., a matrix with dimensions of m^2 x n^2.";

SuperMatrixQ[mat_?MatrixQ] := AllTrue[Sqrt[Dimensions @ mat], IntegerQ]

(* Too dangerous! *)
(* SuperMatrixQ[assoc_Association] := AllTrue[assoc, SuperMatrixQ] *)

SuperMatrixQ[_] = False


ToSuperMatrix::usage = "ToSuperMatrix[cm] converts Choi matrix cm to a regular matrix form; C[i,j;k,l] -> M[{i,k},{j,l}].";

ToSuperMatrix[cm_?ChoiMatrixQ] := Module[
  { dd = Times @@@ Transpose @ Partition[Dimensions @ cm, 2] },
  ArrayReshape[Transpose[cm, 2 <-> 3], dd]
 ]

ToSuperMatrix[assoc_Association] := Map[ToSuperMatrix, assoc] /;
  AllTrue[assoc, ChoiMatrixQ]


ToChoiMatrix::usage = "ToChoiMatrix[sm] converts super-matrix sm to a Choi matrix form;  M[{i,k},{j,l}] -> C[i,j;k,l].";

ToChoiMatrix[sm_?SuperMatrixQ] := Module[
  { dd = Sqrt @ Dimensions @ sm },
  dd = Flatten @ Transpose @ Table[dd, 2];
  Transpose[ArrayReshape[sm, dd], 2 <-> 3]
 ]

ToChoiMatrix[assoc_Association] := Map[ToChoiMatrix, assoc] /;
  AllTrue[assoc, SuperMatrixQ]


(**** <LieBasisSupermap> ****)
LieBasisSupermap::usage = "LieBasisSupermap[n] returns the supermap that changes the standard basis of \[ScriptCapitalL](n) to the Lie basis.\n LieBasisSupermap[{m1,m2,\[Ellipsis]}] returns the supermap that changes the standard basis of \[ScriptCapitalL](n) to the given basis {m1, m2, \[Ellipsis]}, which is supposed to be complete in \[ScriptCapitalL](n).";

LieBasisSupermap[n_] := LieBasisSupermap @ LieBasis[n]

LieBasisSupermap[lbs:{__?SquareMatrixQ}] := With[
  { d = Length @ First @ lbs },
  Supermap @ SparseArray @ Transpose[
    ArrayReshape[SparseArray @ lbs, {d, d, d, d}],
    {2, 4, 1, 3}
   ]
 ] /; ArrayQ[lbs]
(* NOTE: lbs is supposed to be complete. *)
(**** </LieBasisSupermap> ****)


(**** <LieBasisMatrix> ****)
LieBasisMatrix::usage = "LieBasisMatrix[n] returns the supermatrix that changes the standard basis of \[ScriptCapitalL](n) to the Lie basis.\n LieBasisMatrix[{m1,m2,\[Ellipsis]}] returns the supermatrix that changes the standard basis of \[ScriptCapitalL](n) to the given basis {m1, m2, \[Ellipsis]}.";

LieBasisMatrix[n_] := LieBasisMatrix @ LieBasis[n]

LieBasisMatrix[lbs:{__?SquareMatrixQ}] :=
  Transpose[Flatten /@ lbs] /; ArrayQ[lbs]
(**** </LieBasisMatrix> ****)


DampingOperator::usage = "DampingOperator[{b1, b2, \[Ellipsis]}] or DampingOperator[b1, b2, \[Ellipsis]]  returns the effective damping operator corresponding to the Lindblad operators b1, b2, \[Ellipsis].";

DampingOperator[opL_?(ArrayQ[#, 3]&)] := SparseArray[
  Plus @@ MapThread[Dot, {Topple /@ opL, opL}] / 2
];

DampingOperator[opL__] := DampingOperator @ {opL};

DampingOperator[opL_List] :=
  Garner[ MultiplyDot[Dagger @ opL, opL] / 2 ];

DampingOperator[{}] = 0;


(***** <Lindbladian> *****)
Lindbladian::usage = "Lindbladian[opH, opL1, opL2, \[Ellipsis]] represents a superoperator generating the Lindblad equation specified by the effective Hamiltonian opH and the Lindblad operators opL1, opL2, \[Ellipsis].\nLindbladian[opH, opL1, opL2, \[Ellipsis]][rho] transforms the matrix rho.";
  
Lindbladian[opH_, opL_] := 
  Lindbladian @ Prepend[opL, opH] /; ArrayQ[opL, 1|3];

Lindbladian[opH_, None] := Lindbladian[{opH, None}];

Lindbladian[{opH_?MatrixQ, None}] :=
  Lindbladian @ {opH, Zero @ Dimensions @ opH}

Lindbladian[{opH_, None}] := Lindbladian @ {opH, 0}

Lindbladian[{None, opL__?MatrixQ}] :=
  Lindbladian @ {Zero @ Dimensions @ First @ {opL}, opL}

Lindbladian[{None, opL__}] := Lindbladian @ {0, opL}

(* for matrices *)
Lindbladian[array_] := Module[
  { opH = First[array],
    opL = Rest[array],
    one, non },
  one = One[Dimensions @ opH];
  non = -I*(opH - I*DampingOperator[opL]);
  Supermap[ChoiMatrix[non, one] + ChoiMatrix[one, non] + ChoiMatrix[opL]]
] /; ArrayQ[array, 3];

(* for operator expressions *)
Lindbladian[{opH_, opL__}] := Module[
  { non = -I*(opH - I*DampingOperator[opL]),
    cff = One[Length @ {opL}] },
  cff = BlockDiagonalMatrix[{ThePauli[1], cff}, TargetStructure -> "Sparse"];
  Supermap[{1, Garner @ non, opL}, cff]
];
(***** </Lindbladian> *****)


(**** <LindbladConvert> ****)
LindbladConvert::usage = "LindbladConvert[{opH,L1,L2,\[Ellipsis]}] or LindbladConvert[opH, {L1,L2,\[Ellipsis]}] converts the Lindblad equation into an ordinary differential equation for the column vector consisting of the components of the density operator in the so-called Lindblad basis.\nLindbladConvert[cm] assumes that Choi matrix cm corresponds to the Lindblad generator.\nIt returns the pair {generator matrix, offset vector}.";

LindbladConvert::incmp = "The matrices `` are not compatible with each other.";

LindbladConvert::badcm = "The given Choi matrix corresponds to a supermap between two spaces of different dimenions: ``.";

LindbladConvert[Supermap[tsr_?ChoiMatrixQ]] := 
  LindbladConvert[tsr];

LindbladConvert[tsr_?ChoiMatrixQ] := Module[
  { dim = First @ Dimensions[tsr],
    gen = ToSuperMatrix[tsr],
    mat },
  mat = LieBasisMatrix[dim];
  gen = ConjugateTranspose[mat] . ToSuperMatrix[tsr] . mat;
  { gen[[2;;All, 2;;All]],
    gen[[2;;All, 1]] / Sqrt[dim]
  }
] /; If[ Equal @@ Dimensions[tsr], True,
    Message[LindbladConvert::badcm, Dimensions @ tsr];
    False
  ];

(* Lindblad equation specified by matrices *)
LindbladConvert[arr_] :=
  LindbladConvert[ChoiMatrix @ Lindbladian @ arr] /;
  ArrayQ[arr, 3];

(* Lindblad equation specified by operators *)
LindbladConvert[opH_, {opL__}] := LindbladConvert[{opH, opL}];

LindbladConvert[{None, opL__}] := LindbladConvert[{0, opL}];

LindbladConvert[ops:{_, __}] := LindbladConvert @ Matrix[ops];
(**** </LindbladConvert> ****)


(**** <LindbladSteady> ****)
LindbladSteady::usage = "LindbladSteady[{op, b1, b2, \[Ellipsis]}] returns the stationary state of the Lindblad equation specified by the effective Hamiltonian op and the Lindblad operators b1, b2, \[Ellipsis].";

LindbladSteady[array_] := Module[
  { dim = Length[First @ array],
    mat, gen, rho, lbs },
  { mat, gen } = LindbladConvert[array];
  rho = - Inverse[mat] . gen;
  rho = Prepend[rho, 1/Sqrt[dim]];
  lbs = LieBasis @ dim;
  Return[rho . lbs]
] /; ArrayQ[array, 3];

LindbladSteady[opH_, {opL__}] := LindbladSteady[{opH, opL}]

LindbladSteady[{None, opL__}] := LindbladSteady[{0, opL}]

LindbladSteady[ops:{_, __}] :=
  ExpressionFor @ LindbladSteady @ Matrix[ops] /;
  Not @ FreeQ[ops, _Pauli]

LindbladSteady[ops:{_, __}] := Module[
  { ss = Agents @ ops,
    rho },
  rho = LindbladSteady @ Matrix[ops, ss];
  ExpressionFor[rho, ss]
];
(**** </LindbladSteady> ****)


(**** <LindbladSolve> ****)
LindbladSolve::usage = "LindbladSolve[{opH, opL1, opL2, ...}, init, t] returns the solution of the Lindblad equation."

LindbladSolve::incmp = "The matrices `` are not compatible with each other."

LindbladSolve[opH_, {opL__}, in_, rest__] :=
  LindbladSolve[{opH, opL}, in, rest]


LindbladSolve[ops:{_?MatrixQ, __?MatrixQ}, in_?VectorQ, t_] :=
  LindbladSolve[ChoiMatrix @ Lindbladian @ ops, Dyad[in, in], t] /;
  ArrayQ[ops]

LindbladSolve[ops:{_?MatrixQ, __?MatrixQ}, in_?MatrixQ, t_] :=
  LindbladSolve[ChoiMatrix @ Lindbladian @ ops, in, t] /;
  ArrayQ @ Join[{in}, ops]

LindbladSolve[tsr_?ChoiMatrixQ, in_?MatrixQ, t_] := Module[
  { dim = Length[in],
    lbm, bgn, gen, off, sol, var, x },
  lbm = LieBasisMatrix[dim];
  bgn = Rest[Topple[lbm] . Flatten[in]];

  {gen, off} = LindbladConvert[tsr];

  var = Through[ Array[x, dim*dim-1][t] ];
  eqn = Join[
    Thread[ D[var, t] == gen.var + off ],
    Thread[ (var /. {t -> 0}) == bgn ]
   ];

  sol = First @ DSolve[eqn, var, t];
  
  var = Prepend[var, 1/Sqrt[dim]];
  ArrayReshape[lbm . var, {dim, dim}] /. sol
 ] /; Part[Dimensions @ tsr, {2, 4}] == Dimensions[in]

LindbladSolve[ops:{_, __}, in_?MatrixQ, _] :=
  Message[LindbladSolve::incmp, Normal @ Append[ops, in]] 


LindbladSolve[Lindbladian[ops_], in_, t_] :=
  LindbladSolve[ops, in, t]

LindbladSolve[ops:{_, __}, in_, t_] :=
  ExpressionFor @ LindbladSolve[Matrix @ ops, Matrix @ in, t] /;
  Not @ FreeQ[Append[ops, in], _Pauli]

LindbladSolve[ops:{_, __}, in_, t_] := Module[
  { ss = Agents @ Append[ops, in],
    rho },
  rho = LindbladSolve[Matrix[ops, ss], Matrix[in, ss], t];
  ExpressionFor[rho, ss]
 ]
(**** </LindbladSolve> ****)


(**** <NLindbladSolve> ****)
(* TODO: Use the Schur decompoistion; see https://community.wolfram.com/groups/-/m/t/3529901 *)
NLindbladSolve::usage = "NLindbladSolve[{opH, opL1, opL2, ...}, init, {t, tmin, tmax}] finds a numerical solution to the Lindblad equation defined by Hamiltonian opH and Lindblad operators opL1, opL2, \[Ellipsis].NLindblad[tsr, init, {t, tmin, tmax}] assumes that the Lindblad generator is specified by Choi matrix tsr.\nInternally, it uses the NDSolve built-in function and hence takes all options of NDSolve.";

NLindbladSolve::incmp = "The matrices `` are not compatible with each other.";

NLindbladSolve[ops:{_?MatrixQ, __?MatrixQ}, in_, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  NLindbladSolve[ChoiMatrix @ Lindbladian @ ops, in, {t, tmin, tmax}, opts] /;
  ArrayQ @ Join[ops]

NLindbladSolve[HoldPattern @ Supermap[tsr_?ChoiMatrixQ], in_, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  NLindbladSolve[tsr, in, {t, tmin, tmax}, opts]

NLindbladSolve[tsr_?ChoiMatrixQ, in_?VectorQ, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  NLindbladSolve[tsr, Dyad[in, in], {t, tmin, tmax}, opts]

NLindbladSolve[tsr_?ChoiMatrixQ, init_?SquareMatrixQ, {t_Symbol, tmin_, tmax_}, opts___?OptionQ] :=
  Module[
    { dim = Length[init],
      lbm, bgn, gen, off, sol, var, x, f },
    lbm = LieBasisMatrix[dim];
    bgn = Rest[Topple[lbm] . Flatten[init]];

    {gen, off} = LindbladConvert[tsr];

    var = Through[ Array[x, dim*dim-1][t] ];
    eqn = Join[
      Thread[ D[var, t] == gen.var + off ],
      Thread[ (var /. {t -> 0}) == bgn ]
     ];

    var = Array[x, dim*dim-1];
    sol = First @ NDSolve[eqn, var, {t, tmin, tmax}, opts];

    var = Prepend[Through[var[t]], 1/Sqrt[dim]];
    ArrayReshape[lbm . var, {dim, dim}] /. sol
  ]


NLindbladSolve[opH_, {opL__}, init_, rest__] :=
  NLindbladSolve[{opH, opL}, init, rest]

NLindbladSolve[ops:{_, __}, init_?MatrixQ, _] :=
  Message[NLindbladSolve::incmp, Normal @ Append[ops, init]] 

NLindbladSolve[Lindbladian[ops_], in_, {t_, tmin_, tmax_}] :=
  NLindbladSolve[ops, in, {t, tmin, tmax}]

NLindbladSolve[ops:{_, __}, init_, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  ExpressionFor @ NLindbladSolve[
    Matrix @ ops,
    Matrix @ init,
    {t, tmin, tmax},
    opts
   ] /; Not @ FreeQ[Append[ops, init], _Pauli]

NLindbladSolve[ops:{_, __}, init_, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  Module[
    { ss = Agents @ Append[ops, init],
      rho },
    rho = NLindbladSolve[
      Matrix[ops, ss],
      Matrix[init, ss],
      {t, tmin, tmax},
      opts
     ];
    ExpressionFor[rho, ss]
   ]
(**** </NLindbladSolve> ****)


LindbladSolveNaive::usage = "LindbladSolveNaive[...] returns the solution of the Lindblad equation.";

LindbladSolveNaive::incmp = "The matrices `` are not compatible with each other.";

LindbladSolveNaive[opH_?MatrixQ, {opL__?MatrixQ}, init_?MatrixQ, t_] :=
  LindbladSolveNaive[{opH, opL}, init, t]

LindbladSolveNaive[ops:{_?MatrixQ, __?MatrixQ}, init_?MatrixQ, t_] := Module[
  { dim = Length[init],
    lbm, bgn, gen, off, var },
  lbm = LieBasisMatrix[dim];
  bgn = Rest[Topple[lbm] . Flatten[init]];

  {gen, off} = LindbladConvert[ops];
  
  off = Integrate[MatrixExp[s gen].off, {s, 0, t}];
  var = MatrixExp[t gen] . bgn + off;
  var = Prepend[var, 1/Sqrt[dim]];
  Return[lbm . var]
 ] /; ArrayQ @ Join[{init}, ops]

LindbladSolveNaive[ops:{_, __}, in_?MatrixQ, _] :=
  Message[LindbladSolveNaive::incmp, Normal @ Append[ops, in]] 


(**** <LindbladSimulate> ****)
LindbladSimulate::usage = "LindbladSimulate[h, {a1,a2,...}, in, {t1,t2,...}] simulates the dynamics governed by the Lindblad equation associated with the effective Hamiltonian h and the Lindblad operators a1, a2, \[Ellipsis] starting with the initial vector in and using the quantum jump approach, and returns the random trajectories of vector representation {c1,c2,\[Ellipsis],cd} in the computational basis of the Hilbert space of dimension d at each time instants t1, t2, \[Ellipsis].";

LindbladSimulate::numeric = "All elements of the matrices and initial vector as well as the final time must be numeric.";

LindbladSimulate::incmp = "The matrices and/or the initial vector are incompatible with each other.";

LindbladSimulate::null = "The null state is encountered.";

Options[LindbladSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "Carlo"
};

(* TODO: 2023-05-27 *)
(* LindbladSimulate[tsr_?ChoiMatrixQ, in_?VectorQ, tt_List,
   opts:OptionsPattern[]] *)
(* Note that since v2.39, Lindbladian[{__?MatrixQ}, ...] generates
   Supermap[_?ChoiMatrixQ]. *)

LindbladSimulate[opH_?MatrixQ, opL:{__?MatrixQ}, in_?VectorQ, tt_List,
  opts:OptionsPattern[]] := Module[
    { opG = DampingOperator[opL],
      n = OptionValue["Samples"],
      progress = 0,
      val, mat, inv,
      data, more },

    If[ Not @ AllTrue[Flatten @ {opH, opL, in, tt}, NumericQ],
      Message[LindbladSimulate::numeric];
      Return[$Failed]
    ];
    
    {val, mat} = Eigensystem @ Normal[opH - I*opG];
    mat = Transpose[mat];
    inv = Inverse[mat];

    PrintTemporary @ ProgressIndicator @ Dynamic[progress];
    data = SparseArray @ Table[
      progress = k / N[n];
      SparseArray @ Chop @ goMonteCarlo[{mat, val, inv}, opL, in, tt],
      {k, n}
    ];

    If[ OptionValue["SaveData"],
      more = Join[{opts}, Options @ LindbladSimulate];
      SaveData[
        Association @ {"Times" -> tt, "Data" -> data}, 
        FilterRules[{more}, Options @ SaveData]
      ]
    ];
    Return[data]
  ] /; And[ArrayQ @ Join[{opH}, opL], Length[opH] == Length[in]]


LindbladSimulate[_?MatrixQ, {__?MatrixQ}, _?VectorQ, ___] := (
  Message[LindbladSimulate::incmp];
  Return[$Failed]
)

LindbladSimulate[ops:{opH_?MatrixQ, opL__?MatrixQ}, in_?VectorQ, tt_List] :=
  LindbladSimulate[opH, {opL}, in, tt]

LindbladSimulate[opH_, opL:{__}, in_, tt_List, opts___?OptionQ] := Module[
  { ss = Agents @ {opH, opL, in} },
  LindbladSimulate[Matrix[opH, ss], Matrix[opL, ss], Matrix[in, ss], tt, opts]
] /; Not @ FreeQ[in, _Ket]

LindbladSimulate[{opH_, opL__}, in_, tt_List] :=
  LindbladSimulate[opH, {opL}, in, tt]

LindbladSimulate[spr_Lindbladian, in_, tt_List, opts___?OptionQ] :=
  LindbladSimulate[Sequence @@ spr, in, tt, opts] /;
  Not @ FreeQ[in, _Ket]


goMonteCarlo::usage = "goMonteCarlo[non, {a1,a2,...}, in, {t1,t2,...}] generates a quantum trajectory based on the non-Hermitian Hamiltonian non (see below) and Lindblad operators a1, a2, ..., starting from the initial state in at time instants t1, t2, ....\nIn fact, the non-Hermitian Hamiltonian is provided in the form {mat, val, inv}, where non = mat.DiagonalMatrix[val].inv.";

goMonteCarlo[{mat_?MatrixQ, val_?VectorQ, inv_?MatrixQ}, opL:{__?MatrixQ},
  in_?VectorQ, tt_List] := Module[
    { res = {in},
      new = in,
      tau = tt,
      prb, pos, out, tmp, pp, qq, t },

    While[ Length[tau] > 1,
      pp = RandomReal[];
      qq = RandomReal[];
      
      tau = Rest[tau - First[tau]];
      tmp = inv.new;
      While[ Length[tau] > 0,
        t = First[tau];
        out = mat.(Exp[-I*t*val]*tmp);
        If[ pp < Norm[out]^2,
          (* then *)
          AppendTo[res, Normalize @ out];
          new = out;
          tau = Rest[tau],
          (* else *)
          out = new;
          Break[]
        ]
      ];
      
      If[tau == {}, Return @ res];

      out = Map[(#.out)&, opL];

      prb = Chop @ Accumulate[(Norm /@ out)^2];
      Check[
        prb /= Last[prb],
        Message[LindbladSimulate::null];
        new = Zero[Length @ in]; (* null state *)
        AppendTo[res, new];
        t += 1;
        Break[],
        {Divide::indet}
      ];

      pos = First @ FirstPosition[prb - qq, _?NonNegative];
      new = Normalize @ Part[out, pos];
      AppendTo[res, new];
    ];
    Return[res];
  ]
(**** </LindbladSimulate> ****)

End[];
EndPackage[];
