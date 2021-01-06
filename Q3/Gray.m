(* -*- mode:math -*- *)

(* Gray is a Mathematica package to simulate the universal quantum computation
   based on the Gray code. *)

(* Mahn-Soo Choi *)
(* $Date: 2021-01-06 12:43:42+09 $ *)
(* $Revision: 1.14 $ *)

BeginPackage[ "Q3`Gray`",
  { "Q3`Quisso`", "Q3`Pauli`", "Q3`Cauchy`" }
 ]

Unprotect[Evaluate[$Context<>"*"]]

Print @ StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.14 $"][[2]], " (",
  StringSplit["$Date: 2021-01-06 12:43:42+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ]

{ GrayCode, GrayCodeSubsets };

{ GrayControlledU, GrayControlledW };


Begin["`Private`"]

$symbs = Unprotect[]


GrayCode::usage = "GrayCode[n] returns the n-bit Gray code in binary digits."

GrayCode[1] = {{0}, {1}}

GrayCode[n_Integer] := Join[
  Map[Prepend[#, 0] &, GrayCode[n - 1]],
  Map[Prepend[#, 1] &, Reverse@GrayCode[n - 1]]
 ] /; n > 1


GrayCodeSubsets::usage = "GrayCodeSubsets[l] constructs a binary reflected Gray code on set l."

(* NOTE: The code has just been copied from Combinatorica package. *)

GrayCodeSubsets[n_Integer?Positive] := GrayCodeSubsets[Range[n]]

GrayCodeSubsets[ { } ] := { {} }

GrayCodeSubsets[l_List] := Block[
  { $RecursionLimit = Infinity,
    s }, 
  s = GrayCodeSubsets[Take[l, 1-Length[l]]];
  Join[s,  Map[Prepend[#, First[l]] &, Reverse[s]]]
 ]


GrayControlledU::usage = "GrayControlledU[qq, expr] decomposes the n-bit controlled expr into elementary gates, where qq is the list of control qubits and expr is supposed to be a unitary operator."

(* See Barenco et al. PRB (1995). *)

GrayControlledU[q_?QubitQ, expr_] := GrayControlledU[{q}, expr]

GrayControlledU[{q_?QubitQ}, expr_] := ControlledU[{q}, expr]

GrayControlledU[qq:{_?QubitQ, __?QubitQ}, expr_] := Module[
  { mm = Matrix[expr],
    nn = Power[2, Length[qq]-1], 
    op, rr, cc, dd, vv, ll, cV, cn },

  mm = FunctionExpand @ MatrixPower[mm, 1/nn];
  op = QuissoExpression[mm, Qubits @ expr];

  rr = Reverse /@ GrayCodeSubsets[ReverseSort @ FlavorNone @ qq];
  rr = Rest[rr];

  nq = Length @ qq;
  cc = Last /@ rr;
  vv = Riffle[ ConstantArray[op, nn], Dagger @ op ];
  ll = Riffle[
    ConstantArray["Label" -> "V", nn], 
    "Label" -> Superscript["V", "\[Dagger]"]
   ];
  cV = ControlledU @@@ Transpose[{cc, vv, ll}];

  dd = Flatten @ Successive[MutualComplement, Most /@ rr];
  cn = CNOT @@@ Transpose[{dd, Rest @ cc}];

  Riffle[cV, cn]
 ]

MutualComplement[a_, b_] := Union[Complement[a, b], Complement[b, a]]


GrayControlledW::usage = "GrayControlledW[qq, expr] decomposes the n-bit controlled expr into elementary gates, expr is supposed to be a unitary operator.\nThis version is merely for heuristic purposes. Use GrayControlledU instead."

GrayControlledW[q_?QubitQ, expr_] := ControlledU[{q}, expr]

GrayControlledW[{q_?QubitQ}, expr_] := ControlledU[{q}, expr]

GrayControlledW[qq:{__?QubitQ}, expr_] := Module[
  { mm = Matrix[expr],
    tt = Qubits[expr],
    rr = Reverse /@ GrayCodeSubsets[ReverseSort @ FlavorNone @ qq],
    ss, op, n, V },
  ss = Map[Length, rr];
  ss = -Power[-1, ss];
  
  n = Length @ qq;
  V = FunctionExpand @ MatrixPower[mm, Power[2, 1-n]];
  op = QuissoExpression[V, tt];

  Flatten @ MapThread[grayCtrl[#1, op, #2]&, {rr, ss}]
 ]


grayCtrl[qq_, op_,  1] := grayCtrl[qq, op, "V"]

grayCtrl[qq_, op_, -1] :=
  grayCtrl[qq, Dagger @ op, Superscript["V","\[Dagger]"]]


grayCtrl[{ }, op_, lbl_] := {}

grayCtrl[{q_?QubitQ}, op_, lbl_] := ControlledU[{q}, op, "Label"->lbl]

grayCtrl[{aa__?QubitQ, b_?QubitQ}, op_, lbl_] := With[
  { cn = Map[CNOT[#, b]&, {aa}] },
  Flatten @ { cn, ControlledU[{b}, op, "Label"->lbl], cn }
 ]


Protect[ Evaluate @ $symbs ]

End[]


Q3`Gray`Private`symbs = Protect[Evaluate[$Context<>"*"]]

SetAttributes[Evaluate[Q3`Gray`Private`symbs], ReadProtected]

EndPackage[]
