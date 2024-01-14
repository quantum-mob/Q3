(* -*- mode: math; -*- *)
(* SU(3) Algebra *)

Get["Q3`"]

BeginPackage["Q3`"]

ClearAll @@ Evaluate @ Unprotect[
  GellMann, TheGellMann,
  GellMannInner,
  GellMannExpression, GellMannMatrix
 ];


Begin["`Private`"]

ClearAll["`*"];

$symbs = Unprotect[Dot]

TheGellMann::usage="TheGellMann[n] (n=1,2,...,8) gives the original Gell-Mann matrices, a particular basis for the su(3) algebra by Murray Gell-Mann.\n TheGellMann[{i,j}] ..."

TheGellMann[{1|2|3,0}] = IdentityMatrix[3];

TheGellMann[{1,1}] = {
  {0, 1, 0},
  {1, 0, 0},
  {0, 0, 0}};
TheGellMann[{1,2}] = {
  {0,-I, 0},
  {I, 0, 0},
  {0, 0, 0}};
TheGellMann[{1,3}] = {
  {1, 0, 0},
  {0,-1, 0},
  {0, 0, 0}};
TheGellMann[{1,4}] = {
  {0,1,0},
  {0,0,0},
  {0,0,0}};
TheGellMann[{1,5}] = {
  {0,0,0},
  {1,0,0},
  {0,0,0}};

TheGellMann[{2,1}] = {
  {0, 0, 0},
  {0, 0, 1},
  {0, 1, 0}};
TheGellMann[{2,2}] = {
  {0, 0, 0},
  {0, 0,-I},
  {0, I, 0}};
TheGellMann[{2,3}] = {
  {0, 0, 0},
  {0, 1, 0},
  {0, 0,-1}};
TheGellMann[{2,4}] = {
  {0, 0, 0},
  {0, 0, 1},
  {0, 0, 0}};
TheGellMann[{2,5}] = {
  {0, 0, 0},
  {0, 0, 0},
  {0, 1, 0}};

TheGellMann[{3,1}] = {
  {0, 0, 1},
  {0, 0, 0},
  {1, 0, 0}};
TheGellMann[{3,2}] = {
  { 0, 0, I},
  { 0, 0, 0},
  {-I, 0, 0}};
TheGellMann[{3,3}] = {
  {-1, 0, 0},
  { 0, 0, 0},
  { 0, 0, 1}};
TheGellMann[{3,4}] = {
  {0, 0, 0},
  {0, 0, 0},
  {1, 0, 0}};
TheGellMann[{3,5}] = {
  {0, 0, 1},
  {0, 0, 0},
  {0, 0, 0}};

(* The original Gell-Mann matrices *)

TheGellMann[0] = IdentityMatrix[3] Sqrt[2/3];

TheGellMann[1] = {
  {0, 1, 0},
  {1, 0, 0},
  {0, 0, 0}};
TheGellMann[2] = {
  {0,-I, 0},
  {I, 0, 0},
  {0, 0, 0}};
TheGellMann[3] = {
  {1, 0, 0},
  {0,-1, 0},
  {0, 0, 0}};
TheGellMann[4] = {
  {0, 0, 1},
  {0, 0, 0},
  {1, 0, 0}};
TheGellMann[5] = {
  {0, 0,-I},
  {0, 0, 0},
  {I, 0, 0}};
TheGellMann[6] = {
  {0, 0, 0},
  {0, 0, 1},
  {0, 1, 0}};
TheGellMann[7] = {
  {0, 0, 0},
  {0, 0,-I},
  {0, I, 0}};
TheGellMann[8] = {
  {1, 0, 0},
  {0, 1, 0},
  {0, 0,-2}} / Sqrt[3];

TheGellMann[ nn:(0|1|2|3|4|5|6|7|8).. ] :=
  CircleTimes @@ Map[TheGellMann] @ {nn}


GellMann::usage = "GellMann[n] represents the Gell-Mann matrix."

AddGarnerPatterns[_GellMann]

Format @ GellMann[a:(0|1|2|3|4|5|6|7|8)..] := Interpretation[
  CircleTimes @@ Map[SuperscriptBox["\[Lambda]",#]&, {a}],
  GelMann @ a
 ]

GellMann[0] = Sqrt[2 / 3]

GellMann /:
CircleTimes[a_GellMann, b__GellMann] := GellMann @@ Catenate[List @@@ {a, b}]
(* CircleTimes[ GellMann[a], GellMann[b], ... ] are stored into GellMann[a, b, ...], where a, b, ... are elementry (0,1,2,3). *)


GellMannInner::usage = "GellMannInner[m1, m2] = Tr[BlockDagger[m1].m2] / Power[2, Log[3,Length[m2]]] returns the Hermitian product of two square matrices M1 and M2."

GellMannInner[m1_?MatrixQ, m2_?MatrixQ] :=
  Tr[ BlockDagger[m1].m2 ] / Power[ 2, Log[3,Length @ m2] ] /;
  Dimensions[m1] == Dimensions[m2]


GellMannExpression::usage = "GellMannExpression[m] returns an expression for the matrix M in terms of the GellMann matrices."

GellMannExpression[a_SparseArray?VectorQ] := Module[
  { n = Log[3, Length[a]],
    bits, vals },
  If[ !IntegerQ[n],
    Message[Ket::badLen];
    Return[a]
   ];
  bits = Cases[ Flatten @ Keys @ Association @ ArrayRules @ a, _Integer ];
  vals = a[[bits]];
  bits = IntegerDigits[bits-1, 3, n] /. {0 -> "r", 1 -> "b", 2 -> "g"};
  bits = Apply[Ket, bits, {1}];
  Garner @ Dot[vals, bits]
 ]

GellMannExpression[a_?VectorQ] :=
  GellMannExpression @ SparseArray[ ArrayRules[a], {Length @ a} ]

GellMannExpression[m_?MatrixQ] := Block[
  {nn, ss, vv, jj},
  nn = Log[3, Length[m]];
  ss = Tuples[ Range[0,8], nn ];
  vv = Map[ GellMannInner[TheGellMann@@#, m]&, ss ];
  jj = Flatten @ Position[vv, Except[0|0.], {1}, Heads->False];
  ss = Apply[GellMann, ss[[jj]], {1}];
  vv = vv[[jj]];
  Garner @ Dot[vv, ss]
 ]


GellMannMatrix::usage = "GellMannMatrix[expr] converts the expression expr, which may involve the Pauli operators and Kets and/or Bras, into the vector and/or matrix representation. It is done by replacing Ket by TheKet, Bra by TheBra, and Pauli by ThePauli."

SetAttributes[GellMannMatrix, {Listable, ReadProtected}]

GellMannMatrix[expr_] := expr /. {
  Ket -> TheKet,
  Bra -> TheBra,
  GellMann -> TheGellMann
 }
(* NOTE: 2020-01-05 Mathematica 12.0.0 Bug? DO NOT apply Simplify to the
   resulting SparseArray. The Mathematica Kernel will be frozen. *)


structureF::usage = "..."

structureF[1, 2, 3] = 1

structureF[1, 4, 7] =
  structureF[1, 6, 5] =
  structureF[2, 4, 6] =
  structureF[2, 5, 7] =
  structureF[3, 4, 5] = 1/2

structureF[1, 5, 6] =
  structureF[3, 6, 7] = -1/2

structureF[4, 5, 8] =
  structureF[6, 7, 8] = Sqrt[3] / 2

structureF[a_, b_, c_] := (
  Signature @ {a, b, c} * structureF @@ Sort @ {a, b, c}
 ) /; Not @ OrderedQ @ {a, b, c}

structureF[_, _, _] = 0


(* SU(3) Algebra *)

GellMann /:
Dot[ GellMann[0], GellMann[n:(0|1|2|3|4|5|6|7|8)] ] := GellMann[n]

GellMann /:
Dot[ GellMann[n:(0|1|2|3|4|5|6|7|8)], GellMann[0] ] := GellMann[n]

GellMann /:
Dot[ GellMann[a_], GellMann[b_] ] := I *
  Sum[ structureF[a, b, c] GellMann[c], {c, 1, 8} ]

GellMann /:
Dot[ GellMann[a_, b__], GellMann[c_, d__] ] :=
  CircleTimes @@ Dot @@@ Transpose[{ GellMann /@ {a,b}, GellMann /@ {c,d} }]

(* TheKet for GellMann *)

TheKet["r"] := {1, 0, 0}

TheKet["b"] := {0, 1, 0}

TheKet["g"] := {0, 0, 1}

TheKet[aa:{("r" | "b" | "g")..}] := Module[
  { bits = aa /. {"r" -> 0, "b" -> 1, "g" -> 2},
    j },
  j = 1 + FromDigits[bits, 3];
  SparseArray[ {j -> 1}, 3^Length[bits] ]
 ]


(* GellMann on Ket[] and Bra[] *)

GellMann /:
Dot[ GellMann[n:(1|2|3|4|5|6|7|8)], Ket["r"] ] :=
  Dot[ {Ket["r"], Ket["b"], Ket["g"]}, TheGellMann[n][[;;,1]] ]

GellMann /:
Dot[ GellMann[n:(1|2|3|4|5|6|7|8)], Ket["b"] ] :=
  Dot[ {Ket["r"], Ket["b"], Ket["g"]}, TheGellMann[n][[;;,2]] ]

GellMann /:
Dot[ GellMann[n:(1|2|3|4|5|6|7|8)], Ket["g"] ] :=
  Dot[ {Ket["r"], Ket["b"], Ket["g"]}, TheGellMann[n][[;;,3]] ]

GellMann /:
Dot[ Bra["r"], GellMann[n:(1|2|3|4|5|6|7|8)] ] :=
  Dot[ TheGellMann[n][[1,;;]], {Bra["r"], Bra["b"], Bra["g"]} ]

GellMann /:
Dot[ Bra["b"], GellMann[n:(1|2|3|4|5|6|7|8)] ] :=
  Dot[ TheGellMann[n][[2,;;]], {Bra["r"], Bra["b"], Bra["g"]} ]

GellMann /:
Dot[ Bra["g"], GellMann[n:(1|2|3|4|5|6|7|8)] ] :=
  Dot[ TheGellMann[n][[3,;;]], {Bra["r"], Bra["b"], Bra["g"]} ]

GellMann /:
Dot[ GellMann[a_, b__], Ket[c_, d__] ] := CircleTimes @@
  Dot @@@ Transpose[{ GellMann /@ {a,b}, Ket /@ {c,d} }]

GellMann /:
Dot[ Bra[c_, d__], GellMann[a_, b__] ] := CircleTimes @@
  Dot @@@ Transpose[{ Bra /@ {c,d}, GellMann /@ {a,b} }]


Protect[ Evaluate @ $symbs ]

End[]

EndPackage[]


BeginPackage["Q3`"]

Begin["`Private`"]

SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]

SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change variables. *)
Unprotect["`$*"];

(* Too dangerous to allow users to change these. *)
Protect[$GarnerPatterns, $ElaborationPatterns];

EndPackage[]


