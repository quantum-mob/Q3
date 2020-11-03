(* -*- mode:math -*- *)

(* Gray is a Mathematica package to simulate the universal quantum computation
   based on the Gray code. *)

(* Mahn-Soo Choi *)
(* $Date: 2020-11-04 02:16:15+09 $ *)
(* $Revision: 1.5 $ *)

BeginPackage[ "Q3`Gray`",
  { "Q3`Quisso`", "Q3`Pauli`", "Q3`Cauchy`" }
 ]

Unprotect[Evaluate[$Context<>"*"]]

Print @ StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.5 $"][[2]], " (",
  StringSplit["$Date: 2020-11-04 02:16:15+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ]

{ GrayCode, GrayCodeSubsets };

{ GrayControlled };


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


GrayControlled::usage = "GrayControlled[qq, U] decomposes the n-bit controlled U into elementary gates."

(* See Barenco et al. PRB (1995). *)

GrayControlled[qq:{__?QubitQ}, U_?MatrixQ] := Module[
  { rr = Reverse @ GrayCodeSubsets[Sort @ FlavorNone @ qq],
    ss, n, V },
  ss = Map[Length, rr];
  ss = -Power[-1, ss];
  
  n = Length @ qq;
  V = MatrixPower[U, 1/(n-1)];

  Print["rr = ", rr];
  Print["ss = ", ss];
  Flatten @ MapThread[grayCtrl[#1, V, #2]&, {rr, ss}]
 ]


grayCtrl[qq_, V_, 1] := grayCtrl[qq, V]

grayCtrl[qq_, V_, -1] := grayCtrl[qq, Topple @ V]


grayCtrl[{ }, V_] := {}

grayCtrl[{q_?QubitQ}, V_] := Controlled[{q}, V]

grayCtrl[{aa__?QubitQ, b_?QubitQ}, V_] := With[
  { cn = Map[CNOT[#, b]&, {aa}] },
  Flatten @ { cn, Controlled[{b}, V], cn }
 ]


Protect[ Evaluate @ $symbs ]

End[] (* `Qudit` *)


Q3`Gray`Private`symbs = Protect[Evaluate[$Context<>"*"]]

SetAttributes[Evaluate[Q3`Gray`Private`symbs], ReadProtected]

EndPackage[]
