(* -*- mode:math -*- *)

BeginPackage["Q3`"]

`Kraus`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.3 $"][[2]], " (",
  StringSplit["$Date: 2022-10-16 11:49:24+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ Supermap, ChoiMatrix, ChoiMatrixQ,
  SuperMatrixQ, ToSuperMatrix, ToChoiMatrix };

{ ChoiMultiply, ChoiTopple };

{ LindbladGenerator, DampingOperator };

{ LindbladBasis, LindbladBasisMatrix,
  LindbladConvert, LindbladSolve,
  LindbladStationary };

{ NLindbladSolve };

{ LindbladSimulate };


(**** Legacy, Excised, Renamed, Obsolete ****)

{ LindbladSolveNaive}; (* legacy *)

{ KrausProduct }; (* obsolete *)


Begin["`Private`"]

Supermap::usage = "Supermap[op1, op2, \[Ellipsis]] represents a superoperator (or super-mapping, in general) specified by the Kraus elements op1, op2, \[Ellipsis], which may be matrices or operators."
  
Supermap::incmp = "The operators/matrices `` are not compatible with each other."

Supermap::wrong = "`` trying to operate on a wrong object ``."

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


Supermap[a_?MatrixQ][rho_?SquareMatrixQ] :=
  Dot[a, rho, Topple @ a]

Supermap[a_?MatrixQ, b_?MatrixQ][rho_?SquareMatrixQ] :=
  Dot[a, rho, Topple @ b]

Supermap[ops:{__?MatrixQ}, cc_?VectorQ][rho_?SquareMatrixQ] :=
  cc . Map[Dot[#, rho, Topple @ #]&, ops]

Supermap[ops:{__?MatrixQ}, cc_?MatrixQ][rho_?SquareMatrixQ] :=
  Total @ Total[
    cc * Outer[Dot[#1, rho, Topple @ #2]&, ops, ops, 1]
   ]

(* completely positive supermap *)
Supermap[ops:{__?MatrixQ}][rho_?SquareMatrixQ] :=
  Plus @@ Map[Dot[#, rho, Topple @ #]&, ops]


Supermap /:
HoldPattern @ Dagger @ Supermap[tsr_?ChoiMatrixQ] :=
  Supermap[ChoiTopple @ tsr]

Supermap[tsr_?ChoiMatrixQ][rho_?SquareMatrixQ] :=
  ChoiMultiply[tsr, rho] /;
  Part[Dimensions[tsr], {2, 4}] == Dimensions[rho]

Supermap[tsr_?ChoiMatrixQ][rho_?SquareMatrixQ] := (
  Message[Supermap::wrong, Supermap[tsr], rho];
  rho
 )

(*
Supermap[tsr_?ChoiMatrixQ][rho_] := (
  Message[Supermap::wrong, Supermap[tsr], rho];
  rho
 )
 *)


Supermap[a_][rho_] := a ** rho ** Dagger[a]

Supermap[a_, b_][rho_] := a ** rho ** Dagger[b]

Supermap[ops:{__}][rho_] :=
  Garner @ Total @ Multiply[ops, rho, Dagger @ ops]

Supermap[ops:{__}, cc_?VectorQ][rho_] :=
  Garner[ cc . Multiply[ops, rho, Dagger @ ops] ]

Supermap[ops:{__}, cc_][rho_] := Garner @ Total @ Total[
  cc * Outer[Multiply, ops, rho ** Dagger[ops]]
 ]


(**** <ChoiMultiply> ****)

ChoiMultiply::usage = "ChoiMultiply[a,b,\[Ellipsis]] returns the successive multiplication of Choi matrices a, b, \[Ellipsis]."

ChoiMultiply[a_?ChoiMatrixQ, b_?ChoiMatrixQ] :=
  ToChoiMatrix[ToSuperMatrix[a] . ToSuperMatrix[b]]

(* 2022-07-23: This is too slow. Probably because TensorContract and
   TensorProduct does not take advantage of SparseArray? *)
(*
ChoiMultiply[a_?ChoiMatrixQ, b_?ChoiMatrixQ] :=
  Transpose[TensorContract[TensorProduct[a, b], {{2, 5}, {4,7}}], 2<->3]
 *)

ChoiMultiply[tsr_?ChoiMatrixQ, rho_?SquareMatrixQ] :=
  ArrayReshape[ToSuperMatrix[tsr] . Flatten[rho], Dimensions@rho]

(* 2022-07-23: This is also slower. *)
(*
ChoiMultiply[a_?ChoiMatrixQ, b_?SquareMatrixQ] :=
  TensorContract[TensorProduct[a, b], {{2, 5}, {4,6}}]
 *)

ChoiMultiply[a_?ChoiMatrixQ, bb__?ChoiMatrixQ, rest___] :=
  ChoiMultiply[Fold[ChoiMultiply, a, {bb}], rest]


ChoiTopple::usage = "ChoiTopple[tsr] returns the Hermitian conjugate of Choi matrix tsr."
ChoiTopple[tsr_?ChoiMatrixQ] := Transpose[Conjugate @ tsr, {2, 1, 4, 3}]

(**** </ChoiMultiply> ****)


(**** <ChoiMatrix> ****)

ChoiMatrix::usage = "ChoiMatrix[op1, op2, \[Ellipsis]] returns the Choi matrix corresponding to the superoperator represented by the Kraus elements op1, op2, \[Ellipsis]."

ChoiMatrix[Supermap[spec__]] := ChoiMatrix[spec]

ChoiMatrix[a_?MatrixQ] := TensorProduct[a, Conjugate @ a]

ChoiMatrix[a_?MatrixQ, b_?MatrixQ] :=
  TensorProduct[a, Conjugate @ b] /; ArrayQ @ {a, b}

ChoiMatrix[ops:{__?MatrixQ}] :=
  Total @ Map[ChoiMatrix, ops] /; ArrayQ @ {ops}

ChoiMatrix[ops:{__?MatrixQ}, cc_?VectorQ] :=
  cc . Map[ChoiMatrix, ops] /;
  ArrayQ @ ops

ChoiMatrix[ops:{__?MatrixQ}, cc_?MatrixQ] := (
  Plus @@ Flatten[cc * Outer[ChoiMatrix, ops, ops, 1], 1]
 ) /; ArrayQ @ ops


ChoiMatrix[most__, S_?SpeciesQ] := ChoiMatrix[most, FlavorNone @ {S}]

ChoiMatrix[most__, ss:{__?SpeciesQ}] :=
  ChoiMatrix[most, FlavorNone @ ss] /;
  Not @ FlavorNoneQ[ss]


ChoiMatrix[ops:{__}, ss:{__?SpeciesQ}] := With[
  { qq = NonCommutativeSpecies @ Join[ops, ss] },
  ChoiMatrix @ Matrix[ops, qq]
 ]

ChoiMatrix[ops:{__}] := With[
  { qq = NonCommutativeSpecies[ops] },
  ChoiMatrix @ Matrix[ops, qq]
 ] /; FreeQ[ops, _Pauli]

ChoiMatrix[ops:{__}] := ChoiMatrix @ Matrix[ops]


ChoiMatrix[ops:{__}, cc:(_?MatrixQ|_?VectorQ), ss:{__?SpeciesQ}] := With[
  { qq = NonCommutativeSpecies @ Join[ops, ss] },
  ChoiMatrix[Matrix[ops, qq], cc]
 ]

ChoiMatrix[ops:{__}, cc:(_?MatrixQ|_?VectorQ)] := With[
  { qq = NonCommutativeSpecies[ops] },
  ChoiMatrix[Matrix[ops, qq], cc]
 ] /; FreeQ[ops, _Pauli]

ChoiMatrix[ops:{__}, cc:(_?MatrixQ|_?VectorQ)] := ChoiMatrix[Matrix[ops], cc]


ChoiMatrixQ::usage = "ChoiMatrixQ[tensor] returns True if tensor has the structure of Choi matrix, i.e., a tensor of rank four with dimensions m x n x m x n."

ChoiMatrixQ[tsr_?ArrayQ] := And[
  TensorRank[tsr] == 4,
  AllTrue[Transpose @ Partition[Dimensions @ tsr, 2], Apply[Equal]]
 ]

(* Too dangerous! *)
(* ChoiMatrixQ[assoc_Association] := AllTrue[assoc, ChoiMatrixQ] *)

ChoiMatrixQ[_] = False


SuperMatrixQ::usage = "SuperMatrixQ[mat] returns True if matrix mat is a super-matrix, i.e., a matrix with dimensions of m^2 x n^2."

SuperMatrixQ[mat_?MatrixQ] := AllTrue[Sqrt[Dimensions @ mat], IntegerQ]

(* Too dangerous! *)
(* SuperMatrixQ[assoc_Association] := AllTrue[assoc, SuperMatrixQ] *)

SuperMatrixQ[_] = False


ToSuperMatrix::usage = "ToSuperMatrix[cm] converts Choi matrix cm to a regular matrix form; C[i,j;k,l] -> M[{i,k},{j,l}]."

ToSuperMatrix[cm_?ChoiMatrixQ] := Module[
  { dd = Times @@@ Transpose @ Partition[Dimensions @ cm, 2] },
  ArrayReshape[Transpose[cm, 2 <-> 3], dd]
 ]

ToSuperMatrix[assoc_Association] := Map[ToSuperMatrix, assoc] /;
  AllTrue[assoc, ChoiMatrixQ]


ToChoiMatrix::usage = "ToChoiMatrix[sm] converts super-matrix sm to a Choi matrix form;  M[{i,k},{j,l}] -> C[i,j;k,l]."

ToChoiMatrix[sm_?SuperMatrixQ] := Module[
  { dd = Sqrt @ Dimensions @ sm },
  dd = Flatten @ Transpose @ Table[dd, 2];
  Transpose[ArrayReshape[sm, dd], 2 <-> 3]
 ]

ToChoiMatrix[assoc_Association] := Map[ToChoiMatrix, assoc] /;
  AllTrue[assoc, SuperMatrixQ]

(**** </ChoiMatrix> ****)


KrausProduct::usage = "KrausProduct is now obsolete. Use HilbertSchmidtProduct insteas."

KrausProduct[args___] := (
  Message[Q3General::obsolete, "KrausProduct", "HilbertSchmidtProduct"];
  HilbertSchmidtProduct[args]
 )


(**** <LindbladBasis> ****)

LindbladBasis::usage = "LindbladBasis[n] returns a basis of the vector space \[ScriptCapitalM](n) of n\[Times]n matrices.\nThe basis is orthonormal with respect to the Hilbert-Schmidt product, and all but one elements are traceless."

LindbladBasis[op_?SpeciesQ] := LindbladBasis @ {op}

LindbladBasis[qq:{__?SpeciesQ}] := Module[
  { lbs = LindbladBasis[Times @@ Dimension[qq]] },
  ExpressionFor[#, qq]& /@ lbs
 ]

LindbladBasis[n_Integer?Positive] := LieBasis[n]


LindbladBasisMatrix::usage = "LindbladBasisMatrix[n] returns the Choi matrix of the supermap that changes the standard basis of \[ScriptCapitalL](n) to the Lindblad basis."

LindbladBasisMatrix[n_] := LindbladBasisMatrix @ LindbladBasis[n]

LindbladBasisMatrix[lbs:{__?SquareMatrixQ}] := With[
  { n = Length @ First @ lbs },
  SparseArray @ Transpose[
    ArrayReshape[SparseArray @ lbs, {n, n, n, n}],
    {2, 4, 1, 3}
   ]
 ] /; ArrayQ[lbs]

(**** </LindbladBasis> ****)


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
HoldPattern @ ChoiMatrix @ LindbladGenerator[ops:{_, __}] :=
  ChoiMatrix @ LindbladGenerator @ Matrix[ops]


(**** <LindbladConvert> ****)

LindbladConvert::usage = "LindbladConvert[{opH,L1,L2,\[Ellipsis]}] or LindbladConvert[opH, {L1,L2,\[Ellipsis]}] converts the Lindblad equation into an ordinary differential equation for the column vector consisting of the components of the density operator in the so-called Lindblad basis.\nLindbladConvert[cm] assumes that Choi matrix cm corresponds to the Lindblad generator.\nIt returns the pair {generator matrix, offset vector}."

LindbladConvert::incmp = "The matrices `` are not compatible with each other."

LindbladConvert::badcm = "The given Choi matrix corresponds to a supermap between two spaces of different dimenions: ``."

LindbladConvert[tsr_?ChoiMatrixQ] := Module[
  { dim = First @ Dimensions[tsr],
    gen = ToSuperMatrix[tsr],
    mat },
  mat = ToSuperMatrix @ LindbladBasisMatrix[dim];
  gen = Topple[mat] . ToSuperMatrix[tsr] . mat;
  { gen[[2;;, 2;;]],
    gen[[2;;, 1]] / Sqrt[dim]
   }
 ] /; Equal @@ Dimensions[tsr]

LindbladConvert[tsr_?ChoiMatrixQ] := (
  Message[LindbladConvert::badcm, Dimensions @ tsr];
  {{{}}, {}}
 )

LindbladConvert[opH_, {opL__}] := LindbladConvert[{opH, opL}]

LindbladConvert[{opH_?MatrixQ, opL__?MatrixQ}] :=
  LindbladConvert[ChoiMatrix @ LindbladGenerator @ {opH, opL}] /;
  ArrayQ @ {opH, opL}

LindbladConvert[ops:{__?MatrixQ}] :=
  Message[LindbladConvert::incmp, Normal @ ops]

LindbladConvert[{None, opL__}] := LindbladConvert[{0, opL}]

LindbladConvert[ops:{_, __}] := LindbladConvert @ Matrix[ops]

(**** </LindbladConvert> ****)


LindbladStationary::usage = "LindbladStationary[{op, b1, b2, \[Ellipsis]}] returns the stationary state of the Lindblad equation specified by the effective Hamiltonian op and the Lindblad operators b1, b2, \[Ellipsis]."

LindbladStationary::incmp = "The matrices `` are not compatible with each other."

LindbladStationary[opH_, {opL__}] := LindbladStationary[{opH, opL}]

LindbladStationary[{opH_?MatrixQ, opL__?MatrixQ}] := Module[
  { len = Length @ opH,
    mat, gen, rho, lbs },
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
  ExpressionFor @ LindbladStationary @ Matrix[ops] /;
  Not @ FreeQ[ops, _Pauli]

LindbladStationary[ops:{_, __}] := Module[
  { ss = NonCommutativeSpecies @ ops,
    rho },
  rho = LindbladStationary @ Matrix[ops, ss];
  ExpressionFor[rho, ss]
 ]


(**** <LindbladSolve> ****)

LindbladSolve::usage = "LindbladSolve[{opH, opL1, opL2, ...}, init, t] returns the solution of the Lindblad equation."

LindbladSolve::incmp = "The matrices `` are not compatible with each other."

LindbladSolve[opH_, {opL__}, init_, rest__] :=
  LindbladSolve[{opH, opL}, init, rest]


LindbladSolve[ops:{_?MatrixQ, __?MatrixQ}, init_?MatrixQ, t_] := Module[
  { dim = Length[init],
    lbm, bgn, gen, off, sol, var, x },
  lbm = ToSuperMatrix @ LindbladBasisMatrix[dim];
  bgn = Rest[Topple[lbm] . Flatten[init]];

  {gen, off} = LindbladConvert[ops];

  var = Through[ Array[x, dim*dim-1][t] ];
  eqn = Join[
    Thread[ D[var, t] == gen.var + off ],
    Thread[ (var /. {t -> 0}) == bgn ]
   ];

  sol = First @ DSolve[eqn, var, t];
  
  var = Prepend[var, 1/Sqrt[dim]];
  ArrayReshape[lbm . var, {dim, dim}] /. sol
 ] /; ArrayQ @ Join[{init}, ops]

LindbladSolve[ops:{_, __}, init_?MatrixQ, _] :=
  Message[LindbladSolve::incmp, Normal @ Append[ops, init]] 


LindbladSolve[ops:{_, __}, init_, t_] :=
  ExpressionFor @ LindbladSolve[Matrix @ ops, Matrix @ init, t] /;
  Not @ FreeQ[Append[ops, init], _Pauli]

LindbladSolve[ops:{_, __}, init_, t_] := Module[
  { ss = NonCommutativeSpecies @ Append[ops, init],
    rho },
  rho = LindbladSolve[Matrix[ops, ss], Matrix[init, ss], t];
  ExpressionFor[rho, ss]
 ]

(**** </LindbladSolve> ****)


(**** <NLindbladSolve> ****)

NLindbladSolve::usage = "NLindbladSolve[{opH, opL1, opL2, ...}, init, {t, tmin, tmax}] finds a numerical solution to the Lindblad equation defined by Hamiltonian opH and Lindblad operators opL1, opL2, \[Ellipsis].NLindblad[tsr, init, {t, tmin, tmax}] assumes that the Lindblad generator is specified by Choi matrix tsr.\nInternally, it uses the NDSolve built-in function and hence takes all options of NDSolve."

NLindbladSolve::incmp = "The matrices `` are not compatible with each other."

NLindbladSolve[tsr_?ChoiMatrixQ, init_?SquareMatrixQ, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  Module[
    { dim = Length[init],
      lbm, bgn, gen, off, sol, var, x, f },
    lbm = ToSuperMatrix @ LindbladBasisMatrix[dim];
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


NLindbladSolve[ops:{_?MatrixQ, __?MatrixQ}, init_?MatrixQ, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  NLindbladSolve[ChoiMatrix @ LindbladGenerator @ ops, init, {t, tmin, tmax}] /;
  ArrayQ @ Join[{init}, ops]

NLindbladSolve[ops:{_, __}, init_?MatrixQ, _] :=
  Message[NLindbladSolve::incmp, Normal @ Append[ops, init]] 


NLindbladSolve[ops:{_, __}, init_, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  ExpressionFor @ NLindbladSolve[
    Matrix @ ops,
    Matrix @ init,
    {t, tmin, tmax},
    opts
   ] /; Not @ FreeQ[Append[ops, init], _Pauli]

NLindbladSolve[ops:{_, __}, init_, {t_, tmin_, tmax_}, opts___?OptionQ] :=
  Module[
    { ss = NonCommutativeSpecies @ Append[ops, init],
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


LindbladSolveNaive::usage = "LindbladSolveNaive[...] returns the solution of the Lindblad equation."

LindbladSolveNaive::incmp = "The matrices `` are not compatible with each other."

LindbladSolveNaive[opH_?MatrixQ, {opL__?MatrixQ}, init_?MatrixQ, t_] :=
  LindbladSolveNaive[{opH, opL}, init, t]

LindbladSolveNaive[ops:{_?MatrixQ, __?MatrixQ}, init_?MatrixQ, t_] := Module[
  { dim = Length[init],
    lbm, bgn, gen, off, var },
  lbm = ToSuperMatrix @ LindbladBasisMatrix[dim];
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

LindbladSimulate::usage = "LindbladSimulate[h, {a1,a2,...}, in, {t1,t2,...}] simulates the dynamics governed by the Lindblad equation associated with the effective Hamiltonian h and the Lindblad operators a1, a2, \[Ellipsis] starting with the initial vector in and using the quantum jump approach, and returns the random trajectories of vector representation {c1,c2,\[Ellipsis],cd} in the computational basis of the Hilbert space of dimension d at each time instants t1, t2, \[Ellipsis]."

LindbladSimulate::numeric = "All elements of the matrices and initial vector as well as the final time must be numeric."

LindbladSimulate::incmp = "The matrices and/or the initial vector are incompatible with each other."

Options[LindbladSimulate] = {
  "Samples" -> 500,
  "SaveData" -> True,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "Carlo"
 }

LindbladSimulate[opH_?MatrixQ, opL:{__?MatrixQ}, in_?VectorQ, tt_List,
  opts:OptionsPattern[]] := Module[
    { opG = DampingOperator[opL],
      n = OptionValue["Samples"],
      k = 0,
      progress = 0,
      data, file },

    If[ Not @ AllTrue[Flatten @ {opH, opL, in, tt}, NumericQ],
      Message[LindbladSimulate::numeric];
      Return[$Failed]
     ];

    PrintTemporary @ ProgressIndicator @ Dynamic[progress];
    data = Transpose @ Table[
      progress = k++ / n;
      goMonteCarlo[opH-I*opG, opL, in, tt],
      n
     ];
    
    If[Not @ OptionValue["SaveData"], Return @ data];
    
    file = OptionValue["Filename"];
    If[ file === Automatic,
      file = FileNameJoin @ {
        Directory[],
        ToString[Unique @ OptionValue @ "Prefix"]
       };
      file = StringJoin[file, ".wlz"]
     ];
    
    If[OptionValue["Overwrite"] && FileExistsQ[file], DeleteFile @ file];
    
    PutAppend[
      Compress @ Association @ {"Times" -> tt, "Data" -> data},
      file
     ];

    file
   ] /; And[ArrayQ @ Join[{opH}, opL], Length[opH]==Length[in]]


LindbladSimulate[ops:{opH_?MatrixQ, opL__?MatrixQ}, in_?VectorQ, tt_List] :=
  LindbladSimulate[opH, {opL}, in, tt]

LindbladSimulate[_?MatrixQ, {__?MatrixQ}, _?VectorQ, ___] := (
  Message[LindbladSimulate::incmp];
  Return[$Failed]
 )


LindbladSimulate[opH_, opL:{__}, in_, tt_List, opts___?OptionQ] := Module[
  { ss = NonCommutativeSpecies @ {opH, opL, in} },
  LindbladSimulate[Matrix[opH, ss], Matrix[opL, ss], Matrix[in, ss], tt, opts]
 ] /; Not @ FreeQ[in, _Ket]

LindbladSimulate[{opH_, opL__}, in_, tt_List] :=
  LindbladSimulate[opH, {opL}, in, tt]

LindbladSimulate[spr_LindbladGenerator, in_, tt_List, opts___?OptionQ] :=
  LindbladSimulate[Sequence @@ spr, in, tt, opts] /;
  Not @ FreeQ[in, _Ket]


goMonteCarlo::usage = "goMonteCarlo[non, {a1,a2,...}, in, {t1,t2,...}] generates a quantum trajectory based on the non-Hermitian Hamiltonian non and Lindblad operators a1, a2, ..., starting from the initial state in at time instants t1, t2, ...."
goMonteCarlo[non_?MatrixQ, opL:{__?MatrixQ}, in_?VectorQ, tt_List] :=
  Module[
    { res = {},
      new = in,
      tau = tt,
      prb, pos, out, pp, qq, t },

    While[ Length[tau] > 1,
      pp = RandomReal[];
      qq = RandomReal[];
      
      tau = tau - First[tau];
      out = PadRight[{1}, Length @ new];
      While[ And[pp > 1-Norm[out]^2, Length[tau] > 0],
        {{t}, tau} = TakeDrop[tau, 1];
        out = MatrixExp[-I*t*non].new;
        AppendTo[res, Normalize @ out]
       ];
      
      If[tau == {}, Return[res]];

      out = Map[(#.out)&, opL];

      prb = Chop @ Accumulate[(Norm /@ out)^2];
      prb /= Last[prb];

      pos = First @ FirstPosition[prb - qq, _?NonNegative];
      new = Normalize @ Part[out, pos];
     ];
    AppendTo[res, new]
   ]

(**** </LindbladSimulate> ****)



End[]

EndPackage[]
