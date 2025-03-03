(* -*- mode: math; -*- *)
(* See Gross (2006) and Singal et al. (2023) *)

BeginPackage["QuantumMob`Q3S`", {"System`"}]

{ Weyl, TheWeyl };

{ WeylBasis };


Begin["`Private`"]

(**** <Weyl> ****)

Weyl::usage = "Weyl[{m, n, d}] represents the generalized Pauli operator X^mZ^n on a d-dimensional Hilbert space.\nWeyl[{{m1,n1,d1},{m2,n2,d2},...}] represents (X^m1Z^n1)\[CircleTimes](X^m2Z^n2)\[CircleTimes]\[Ellipsis]."

SyntaxInformation[Weyl] = {"ArgumentsPattern" -> {_}}

Format[op:Weyl[{x:Except[_List], z:Except[_List], d:Except[_List]}]] :=
  Interpretation[DisplayForm @ theWeylFormat[{x, z, d}], op]

Format[op:Weyl[kk:{{_, _, _}..}]] := Interpretation[
  DisplayForm[CircleTimes @@ Map[theWeylFormat, kk]],
  op
 ]

theWeylFormat[{x_, 0, _}] := Superscript["X", x]

theWeylFormat[{0, z_, _}] := Superscript["Z", z]

theWeylFormat[{x_, z_, _}] :=
  RowBox @ {"(", Superscript["X", x], Superscript["Z", z], ")"}


Weyl /:
Matrix[Weyl[any_], ___] := TheWeyl[any]

Weyl /:
NonCommutativeQ[_Weyl] = True

Weyl /:
Multiply[pre___,
  Weyl[{a:Except[_List], b:Except[_List], d:Except[_List]}],
  Weyl[{x:Except[_List], z:Except[_List], d:Except[_List]}], post___] :=
  Multiply[pre, Weyl[{Mod[a+x, d], Mod[b+z, d], d}], post] *
  Exp[2*Pi*I * (b*x)/d]

Weyl /:
Multiply[pre___, aa:Weyl[{{_, _, _}..}], bb:Weyl[{{_, _, _}..}], post___] :=
  Multiply[ pre,
    Apply[Multiply, Thread[aa] ** Thread[bb]],
    post ]

Weyl /:
Multiply[pre___, Weyl[{x_, z_, d_}], Ket[s_]] :=
  Multiply[pre, Ket @ Mod[s + x, d]] * Exp[2*Pi*I * z*s/d] /;
  NoneTrue[{x, z, d}, ListQ]

Weyl /:
Multiply[pre___, op:Weyl[{{_, _, _}..}], Ket[ss__]] :=
  Multiply[pre, Apply[CircleTimes, Thread[op] ** Thread[Ket @ {ss}]]]

(**** </Weyl> ****)


(**** <TheWeyl> ****)

TheWeyl::usage = "TheWeyl[{m, n, d}] returns the matrix representation of the generalized Pauli operator X^mZ^n on a d-dimensional Hilbert space.\n TheWeyl[{{m1,n1,d1},{m2,n2,d2},...}] returns the matrix representaiton of (X^m1Z^n1)\[CircleTimes](X^m2Z^n2)\[CircleTimes]\[Ellipsis]."

SyntaxInformation[TheWeyl] = {"ArgumentsPattern" -> {_}}

TheWeyl[{x_, z_, d_}] := SparseArray @ Dot[
  RotateRight[One @ d, x],
  DiagonalMatrix @ Exp[2*Pi*I * Range[0, d-1] * z/d]
 ]

TheWeyl[kk:{{_, _, _}..}] := Apply[CircleTimes, TheWeyl /@ kk]

(**** </TheWeyl> ****)


(**** <WeylBasis> ****)

WeylBasis::usage = "WeylBasis[n] returns a generating set of matrices in GL(n).\nSee also Lie basis."

WeylBasis[d_Integer] :=
  TheWeyl /@ PadRight[Tuples[Range[0, d-1], 2], {d*d, 3}, d];

(**** </WeylBasis> ****)


End[]

EndPackage[]
