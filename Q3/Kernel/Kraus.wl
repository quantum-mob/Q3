(* -*- mode:math -*- *)

Needs["Q3`"]

BeginPackage[ "Q3`Kraus`",
  { "Q3`Abel`",
    "Q3`Cauchy`",
    "Q3`Pauli`",
    "Q3`Quisso`",
    "Q3`Fock`",
    "Q3`Wigner`"
   }
 ]

`Information`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.24 $"][[2]], " (",
  StringSplit["$Date: 2021-05-06 20:30:45+09 $"][[2]], ") ",
  "Ha-Eum Kim, Mahn-Soo Choi"
 ];

{ Supermap, ChoiOperator, ChoiMatrix };

{ KrausProduct };


{ LindbladGenerator, DampingOperator };

{ LindbladBasis, LindbladBasisMatrix,
  LindbladConvert, LindbladSolve,
  LindbladStationary };

{ LindbladConvertOld, LindbladSolveNaive};

Begin["`Private`"]

Supermap::usage = "Supermap[op1, op2, \[Ellipsis]] represents a superoperator (or super-mapping, in general) specified by the Kraus elements op1, op2, \[Ellipsis], which may be matrices or operators."
  
Supermap::incmp = "The operators/matrices `` are not compatible with each other."

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


Supermap[a_?MatrixQ][rho_?MatrixQ] :=
  Dot[a, rho, Topple @ a]

Supermap[a_?MatrixQ, b_?MatrixQ][rho_?MatrixQ] :=
  Dot[a, rho, Topple @ b]

Supermap[ops:{__?MatrixQ}, cc_?VectorQ][rho_?MatrixQ] :=
  cc . Map[Dot[#, rho, Topple @ #]&, ops]

Supermap[ops:{__?MatrixQ}, cc_?MatrixQ][rho_?MatrixQ] := Total @ Total[
  cc * Outer[Dot[#1, rho, Topple @ #2]&, ops, ops, 1]
 ]

Supermap[ops:{__?MatrixQ}][rho_?MatrixQ] :=
  Plus @@ Map[Dot[#, rho, Topple @ #]&, ops]
 (* completely positive supermap *)


Supermap[a_][rho_] := a ** rho ** Dagger[a]

Supermap[a_, b_][rho_] := a ** rho ** Dagger[b]

Supermap[ops:{__}][rho_] :=
  Garner @ Total @ Multiply[ops, rho, Dagger @ ops]

Supermap[ops:{__}, cc_?VectorQ][rho_] :=
  Garner[ cc . Multiply[ops, rho, Dagger @ ops] ]

Supermap[ops:{__}, cc_][rho_] := Garner @ Total @ Total[
  cc * Outer[Multiply, ops, rho ** Dagger[ops]]
 ]


ChoiMatrix::usage = "ChoiMatrix[op1, op2, \[Ellipsis]] returns the Choi matrix corresponding to the superoperator represented by the Kraus elements op1, op2, \[Ellipsis]."

ChoiMatrix[Supermap[spec__]] := ChoiMatrix[spec]

ChoiMatrix[a_?MatrixQ] := TensorProduct[a, Conjugate @ a]

ChoiMatrix[a_?MatrixQ, b_?MatrixQ] :=
  TensorProduct[a, Conjugate @ b] /; ArrayQ @ {a, b}

ChoiMatrix[ops:{__?MatrixQ}] :=
  Plus @@ Map[ChoiMatrix, ops] /; ArrayQ @ {ops}

ChoiMatrix[ops:{__?MatrixQ}, cc_?VectorQ] :=
  cc . Map[ChoiMatrix, ops] /;
  ArrayQ @ ops

ChoiMatrix[ops:{__?MatrixQ}, cc_?MatrixQ] :=
  Apply[Plus, cc * Outer[ChoiMatrix, ops, ops, 1]] /; ArrayQ @ ops


KrausProduct::usage = "KrausProduct[a, b] returns the trace Hermitian product (also known as the Frobenius product) of two matrices (operators) a and b."

KrausProduct[a_?MatrixQ, b_?MatrixQ] := Tr[Topple[a] . b]

KrausProduct[a_, b_] := With[
  { ss = NonCommutativeSpecies @ {a, b} },
  KrausProduct[ Matrix[a, ss], Matrix[b, ss] ]
 ] /; NonTrue[{a, b}, CommutativeQ]

KrausProduct[a_?CommutativeQ, b_] := Conjugate[a] * Tr[Matrix @ b]

KrausProduct[a_, b_?CommutativeQ] := Conjugate[Tr @ Matrix @ a] * b


(**** <LindbladBasis> ****)

LindbladBasis::usage = "LindbladBasis[n] returns a basis of the vector space \[ScriptCapitalM](n) of n\[Times]n matrices.\nThe basis is orthonormal with respect to the trace Hermitian product, and all but one elements are traceless."
  
LindbladBasis[n_Integer] := Module[
  { dbs = SparseArray /@ DiagonalMatrix /@ theBasisX[n],
    obs = Subsets[Range[n], {2}] },
  obs = SparseArray[# -> 1, {n, n}]& /@ obs;
  obs = Join[ (Transpose /@ obs + obs), I(Transpose /@ obs - obs) ] / Sqrt[2];
  Join[dbs, obs]
 ] /; n > 1

LindbladBasis[op_?SpeciesQ] := LindbladBasis @ {op}

LindbladBasis[qq:{_?QubitQ}] := Module[
  { lbs = LindbladBasis[Times @@ Dimension[qq]] },
  QuissoExpression[#, qq]& /@ lbs
 ]

LindbladBasis[qq:{_?QuditQ}] := Module[
  { lbs = LindbladBasis[Times @@ Dimension[qq]] },
  QuditExpression[#, qq]& /@ lbs
 ]


theBasisX[2] = theKetX /@ {0, 1}

theBasisX[n_?EvenQ] := Flatten[
  Outer[CircleTimes, theBasisX[2], theBasisX[n/2], 1],
  1
 ]

theBasisX[n_?OddQ] := Module[
  { bb = Rest @ theBasisX[n - 1] },
  bb = ArrayPad[bb, {{0, 0}, {0, 1}}];
  Join[
    { ConstantArray[1, n]/Sqrt[n],
      Normalize@Append[ConstantArray[1, n - 1], 1 - n] },
    bb
   ]
 ]


theKetX[0] = {1, 1}/Sqrt[2]

theKetX[1] = {1, -1}/Sqrt[2]

theKetX[a:(0 | 1), bb:(0 | 1) ..] := CircleTimes @@ Map[theKetX]@{a, bb}


theVectorX[mat_?MatrixQ, mbs:{__?MatrixQ}] :=
  Map[ KrausProduct[#, mat]&, mbs ]

(**** </LindbladBasis> ****)

LindbladBasisMatrix::usage = "LindbladBasisMatrix[n] returns the Choi matrix of the supermap that maps the standard basis of \[ScriptCapitalL](n) to the Lindblad basis."

LindbladBasisMatrix[n_] := Module[
  { lbs = LindbladBasis[n] },
  SparseArray @ Transpose[ArrayReshape[lbs, {n, n, n, n}], {2, 4, 1, 3}]
 ]


DampingOperator::usage = "DampingOperator[{b1, b2, \[Ellipsis]}] or DampingOperator[b1, b2, \[Ellipsis]]  returns the effective damping operator corresponding to the Lindblad operators b1, b2, \[Ellipsis]."

DampingOperator[opL__] := DampingOperator @ {opL}

DampingOperator[opL:{__?MatrixQ}] :=
  Plus @@ MapThread[Dot, {Topple /@ opL, opL}] / 2 /;
  ArrayQ @ opL

DampingOperator[opL:{Except[_?ListQ]..}] := MultiplyDot[Dagger @ opL, opL] / 2

DampingOperator[{}] = 0


LindbladGenerator::usage = "LindbladGenerator[opH, opL1, opL2, \[Ellipsis]] represents a superoperator generating the Lindblad equation specified by the effective Hamiltonian opH and the Lindblad operators opL1, opL2, \[Ellipsis].\nLindbladGenerator[opH, opL1, opL2, \[Ellipsis]][rho] transforms the matrix rho."
  
LindbladGenerator::incmp = "The matrices `` are not compatible with each other."

LindbladGenerator[ops:{_?MatrixQ, __?MatrixQ}] := (
  Message[LindbladGenerator::incmp, Normal @ ops];
  (Zero @ Dimensions @ #)&
 ) /; Not @ ArrayQ @ ops

LindbladGenerator[opH_, {opL__}] := LindbladGenerator @ {opH, opL}

LindbladGenerator[opH_, None] := LindbladGenerator[{opH, None}]

LindbladGenerator[{opH_?MatrixQ, None}] :=
  LindbladGenerator @ {opH, Zero @ Dimensions @ opH}

LindbladGenerator[{opH_, None}] := LindbladGenerator @ {opH, 0}

LindbladGenerator[{None, opL__?MatrixQ}] :=
  LindbladGenerator @ {Zero @ Dimensions @ First @ opL, opL}

LindbladGenerator[{None, opL__}] := LindbladGenerator @ {0, opL}

LindbladGenerator[{opH_?MatrixQ, opL__?MatrixQ}][rho_?MatrixQ] := Module[
  { opG = DampingOperator[opL],
    gen },
  opG = -I(opH . rho - rho . opH) - (opG . rho + rho . opG);
  gen = Plus @@ Map[ (#.rho.Topple[#])&, {opL} ];
  opG + gen
 ]

LindbladGenerator[{opH_, opL__}][rho_] := Module[
  { opG = DampingOperator[opL],
    gen },
  opG = -I*Commutator[opH, rho] - Anticommutator[opG, rho];
  gen = Total @ Multiply[{opL}, rho, Dagger @ {opL}];
  Garner[opG + gen]
 ]


LindbladGenerator /:
ChoiMatrix @ LindbladGenerator @ {opH_?MatrixQ, opL__?MatrixQ} := Module[
  { one = One @ Length @ opH,
    opG = DampingOperator[opL] },
  -I(ChoiMatrix[opH, one] - ChoiMatrix[one, opH]) -
    (ChoiMatrix[opG, one] + ChoiMatrix[one, opG]) +
    ChoiMatrix @ {opL}
 ]

LindbladGenerator /:
HoldPattern @ ChoiMatrix @ LindbladGenerator[ops:{_, __}] := Module[
  { ss = NonCommutativeSpecies @ ops },
  ChoiMatrix @ LindbladGenerator @ Matrix[ops, ss]
 ]


LindbladConvertOld::usage = "See LindbladConvert."

LindbladConvertOld::incmp = "The matrices `` are not compatible with each other."

LindbladConvertOld[opH_, {opL__}] := LindbladConvertOld[{opH, opL}]

LindbladConvertOld[{opH_?MatrixQ, opL__?MatrixQ}] := Module[
  { len = Length[opH],
    mbs, var, rho, gen, x },
  mbs = LindbladBasis[len];
  var = Array[x, len*len, 0];
  rho = var . mbs;
  var = Rest @ var;

  gen = LindbladGenerator[{opH, opL}] @ rho;
  gen = Rest @ theVectorX[gen, mbs];
  
  { Transpose[ Coefficient[gen, #]& /@ var ],
    gen /. {x[0] -> 1/Sqrt[len], x[_] -> 0}
   }
 ] /; ArrayQ @ {opH, opL}

LindbladConvertOld[ops:{__?MatrixQ}] :=
  Message[LindbladConvertOld::incmp, Normal @ ops]

LindbladConvertOld[ops:{_, __}] := Module[
  { ss = NonCommutativeSpecies @ ops },
  LindbladConvertOld @ Matrix[ops, ss]
 ]


LindbladConvert::usage = "LindbladConvert[{opH, opL}] converts the Lindblad equation into an ordinary differential equation for the column vector consisting of the components of the density operator in the so-called Lindblad basis.\nIt returns the pair {generator matrix, offset vector}."

LindbladConvert::incmp = "The matrices `` are not compatible with each other."

LindbladConvert[opH_, {opL__}] := LindbladConvert[{opH, opL}]

LindbladConvert[{opH_?MatrixQ, opL__?MatrixQ}] := Module[
  { n = Length[opH],
    mat, gen },
  mat = LindbladBasisMatrix[n];
  mat = ArrayReshape[Transpose[mat, 2 <-> 3], {n*n, n*n}];

  gen = ChoiMatrix @ LindbladGenerator @ {opH, opL};
  gen = ArrayReshape[Transpose[gen, 2 <-> 3], {n*n, n*n}];

  gen = Topple[mat] . gen . mat;
  
  { gen[[2;;, 2;;]],
    gen[[2;;, 1]] / Sqrt[n]
   }
 ] /; ArrayQ @ {opH, opL}

LindbladConvert[ops:{__?MatrixQ}] :=
  Message[LindbladConvert::incmp, Normal @ ops]

LindbladConvert[{None, opL__}] := LindbladConvert[{0, opL}]

LindbladConvert[ops:{_, __}] := Module[
  { ss = NonCommutativeSpecies @ ops },
  LindbladConvert @ Matrix[ops, ss]
 ]


LindbladStationary::usage = "LindbladStationary[{op, b1, b2, \[Ellipsis]}] returns the stationary state of the Lindblad equation specified by the effective Hamiltonian op and the Lindblad operators b1, b2, \[Ellipsis]."

LindbladStationary::incmp = "The matrices `` are not compatible with each other."

LindbladStationary[opH_, {opL__}] := LindbladStationary[{opH, opL}]

LindbladStationary[{opH_?MatrixQ, opL__?MatrixQ}] := Module[
  { len = Length @ opH,
    mat, gen, lb, rho },
  { mat, gen } = LindbladConvert @ {opH, opL};
  rho = - Inverse[mat] . gen;
  rho = Prepend[rho, 1/Sqrt[len]];
  lbs = LindbladBasis @ len;
  Return[rho . lbs]
 ] /; ArrayQ @ {opH, opL}

LindbladStationary[ops:{__?MatrixQ}] :=
  Message[LindbladStationary::incmp, Normal @ ops]

LindbladStationary[{None, opL__}] := LindbladStationary[{0, opL}]

LindbladStationary[ops:{_, __}] :=
  PauliExpression @ LindbladStationary[Matrix /@ ops] /;
  Not @ FreeQ[ops, _Pauli]

LindbladStationary[ops:{_, __}] :=
  LindbladStationary[ops, QuissoExpression] /;
  AllTrue[NonCommutativeSpecies @ ops, QubitQ]

LindbladStationary[ops:{_, __}, func_] := Module[
  { ss = NonCommutativeSpecies @ ops,
    rho },
  rho = LindbladStationary @ Matrix[ops, ss];
  If[ func === None, rho, func[rho, ss] ]
 ]


LindbladSolve::usage = "LindbladSolve[{opH, opL1, opL2, ...}, init, t] returns the solution of the Lindblad equation."

LindbladSolve::incmp = "The matrices `` are not compatible with each other."

LindbladSolve[opH_, {opL__}, init_, rest__] :=
  LindbladSolve[{opH, opL}, init, rest]


LindbladSolve[ops:{_?MatrixQ, __?MatrixQ}, init_?MatrixQ, t_] := Module[
  { len = Length[init],
    kbs, bgn, gen, off, sol, var, x },
  kbs = LindbladBasis[len];
  bgn = Rest @ theVectorX[init, kbs];

  { gen, off } = LindbladConvert[ops];

  var = Through[ Array[x, len*len-1][t] ];
  eqn = Join[
    Thread[ D[var, t] == gen.var + off ],
    Thread[ (var /. {t -> 0}) == bgn ]
   ];

  sol = First @ DSolve[eqn, var, t];
  
  var = Prepend[var, 1/Sqrt[len]] /. sol;
  Return[var . kbs]
 ] /; ArrayQ @ Join[{init}, ops]

LindbladSolve[ops:{_, __}, init_?MatrixQ, _] :=
  Message[LindbladSolve::incmp, Normal @ Append[ops, init]] 


LindbladSolve[ops:{_, __}, init_, t_] :=
  LindbladSolve[ops, init, t, QuissoExpression] /;
  AllTrue[NonCommutativeSpecies @ Append[ops, init], QubitQ]

LindbladSolve[ops:{_, __}, init_, t_] :=
  PauliExpression @ LindbladSolve[Matrix /@ ops, Matrix @ init, t] /;
  Not @ FreeQ[Append[ops, init], _Pauli]

LindbladSolve[ops:{_, __}, init_, t_, PauliExpression] :=
  PauliExpression @ LindbladSolve[Matrix /@ ops, Matrix @ init, t]

LindbladSolve[ops:{_, __}, init_, t_, func_] := Module[
  { ss = NonCommutativeSpecies @ Append[ops, init],
    rho },
  Print["ss = ", ss];
  rho = LindbladSolve[Matrix[ops, ss], Matrix[init, ss], t];
  If[ func === None, rho, func[rho, ss] ]
 ]


LindbladSolveNaive::usage = "LindbladSolveNaive[...] returns the solution of the Lindblad equation."

LindbladSolveNaive::incmp = "The matrices `` are not compatible with each other."

LindbladSolveNaive[opH_?MatrixQ, {opL__?MatrixQ}, init_?MatrixQ, t_] :=
  LindbladSolveNaive[{opH, opL}, init, t]

LindbladSolveNaive[ops:{_?MatrixQ, __?MatrixQ}, init_?MatrixQ, t_] := Module[
  { len = Length[init],
    mbs, bgn, gen, off, var },
  mbs = LindbladBasis[len];
  bgn = Rest @ theVectorX[init, mbs];

  { gen, off } = LindbladConvert[ops];
  off = Integrate[MatrixExp[s gen].off, {s, 0, t}];
  var = MatrixExp[t gen] . bgn + off;
  var = Prepend[var, 1/Sqrt[len]];
  var . mbs
 ] /; ArrayQ @ Join[{init}, ops]

LindbladSolveNaive[ops:{_, __}, in_?MatrixQ, _] :=
  Message[LindbladSolveNaive::incmp, Normal @ Append[ops, in]] 


End[]

EndPackage[]
