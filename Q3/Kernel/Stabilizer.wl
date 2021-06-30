(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

`Stabilizer`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.17 $"][[2]], " (",
  StringSplit["$Date: 2021-06-30 11:01:27+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ PauliGroup, CliffordGroup,
  PauliForm };


Begin["`Private`"]

(**** </PauliForm> ****)

PauliForm::usage = "PauliForm[expr] rewrites expr in a more conventional form, where the Pauli operators are denoted by I, X, Y, and Z."

PauliForm[expr_List] := Map[PauliForm, expr] /; Not @ FreeQ[expr, _Pauli]

PauliForm[expr_Plus] := Plus @@ Map[PauliForm, List @@ expr] /;
  Not @ FreeQ[expr, _Pauli]

PauliForm[z_?CommutativeQ op_] := z * PauliForm[op]

PauliForm[op_Pauli] :=
  CircleTimes @@ ReplaceAll[op, {0 -> "I", 1 -> "X", 2 -> "Y", 3 -> "Z"}]


PauliForm[expr_List, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, expr]

PauliForm[expr_Plus, qq:{__?QubitQ}] :=
  Plus @@ PauliForm[List @@ expr, qq]

PauliForm[z_?CommutativeQ, qq:{__?QubitQ}] :=
  z * PauliForm[Multiply @@ Through @ qq[0], qq]

PauliForm[z_?CommutativeQ op_, qq:{__?QubitQ}] := z * PauliForm[op, qq]

HoldPattern @ PauliForm[Multiply[ss__?QubitQ], qq:{__?QubitQ}] :=
  PauliForm[ss, qq]

PauliForm[ss__?QubitQ, qq:{__?QubitQ}] := Module[
  { jj = Lookup[PositionIndex[FlavorNone @ qq], FlavorMute @ {ss}],
    mm },
  mm = FlavorLast @ {ss} /. {0 -> "I", 1 -> "X", 2 -> "Y", 3 -> "Z"};
  CircleTimes @@ ReplacePart[
    ConstantArray["I", Length @ qq],
    Flatten[ Thread /@ Thread[jj -> mm] ]
   ]
 ]

PauliForm[expr_] := PauliForm[expr, Qubits @ expr] /; FreeQ[expr, _Pauli]

(**** </PauliForm> ****)


(**** <PauliGroup> ****)

PauliGroup::usage = "PauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators, on n qubits.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup /:
GroupElements @ PauliGroup[n_Integer] := Module[
  { op = Pauli @@@ Tuples[{0, 1, 2, 3}, n] },
  Union @ Catenate @ {op, -op, I op, -I op}
 ]

PauliGroup /:
GroupGenerators @ PauliGroup[n_Integer] := Module[
  { op = Pauli @@ ConstantArray[0, n],
    kk = Range[n] },
  kk = Flatten[ Thread /@ {kk -> 1, kk -> 2, kk ->3 } ];
  Sort @ Map[ReplacePart[op, #]&, kk]
 ]


PauliGroup /:
GroupElements @ PauliGroup[S_?QubitQ] :=
  GroupElements @ PauliGroup @ S @ {None}

PauliGroup /:
GroupElements @ PauliGroup[qq:{__?QubitQ}] := Module[
  { op = Elaborate @ Through @ qq[Full] },
  op = Multiply @@@ Tuples[op];
  Union @ Catenate @ {op, -op, I op, -I op}
 ]

PauliGroup /:
GroupGenerators @ PauliGroup[S_?QubitQ] :=
  GroupGenerators @ PauliGroup @ S @ {None}

PauliGroup /:
GroupGenerators @ PauliGroup[qq:{__?QubitQ}] :=
  Sort @ Flatten @ Through @ qq[All]

(**** </PauliGroup> ****)


(**** <CliffordGroup> ****)

CliffordGroup::usage = "CliffordGroup[n] represents the Clifford group, the normalizer group of the Pauli group, on n qubits.\nCliffordGroup[{s1, s2, ...}] represents the Clifford group, the normalizer group of the Pauli group, on the qubits {s1, s2, \[Ellipsis]}."

CliffordGroup::toobig = "Too many elements in the Clifford group on two or more qubits to list."

CliffordGroup /:
GroupGenerators @ CliffordGroup[n_Integer] := Module[
  { ss, cz, CZ, PP },
  ss = {
    PP = Pauli @@ PadRight[{6}, n];
    Table[RotateRight[PP, k], {k, 0, n-1}],
    PP = Pauli @@ PadRight[{7}, n];
    Table[RotateRight[PP, k], {k, 0, n-1}]
   };    
  
  cz = Subsets[Range[n], {2}];
  PP = Pauli @@ ConstantArray[0, n];
  CZ[i_, j_] := ( PP +
      ReplacePart[PP, i->3] + ReplacePart[PP, j->3] -
      ReplacePart[PP, {i->3, j->3}] ) / 2;
  Garner @ Flatten @ {ss, CZ @@@ cz}
 ]


CliffordGroup /:
GroupGenerators @ CliffordGroup[S_?QubitQ] :=
  GroupGenerators @ CliffordGroup @ S @ {None}

CliffordGroup /:
GroupGenerators @ CliffordGroup[qq:{__?QubitQ}] := Module[
  { ss = Through[qq @ {6, 7}],
    cn = CZ @@@ Subsets[FlavorNone @ qq, {2}] },
  Flatten @ {ss, cn}
 ]


CliffordGroup /:
GroupElements @ CliffordGroup[n_Integer] :=
  Message[CliffordGroup::toobig] /; n > 1

CliffordGroup /:
GroupElements @ CliffordGroup[1] := Module[
  { op, ff },
  op = Flatten @ {
    Rotation[#, 1] & /@ {Pi/2, -Pi/2, Pi},
    Rotation[#, 2] & /@ {Pi/2, -Pi/2, Pi},
    Rotation[#, 3] & /@ {Pi/2, -Pi/2, Pi},
    Rotation[Pi, {1, 1, 0}], Rotation[Pi, {-1, 1, 0}],
    Rotation[Pi, {1, 0, 1}], Rotation[Pi, {0, 1, 1}],
    Rotation[Pi, {-1, 0, 1}], Rotation[Pi, {0, -1, 1}],
    Rotation[2 Pi/3, {1, 1, 1}], Rotation[4 Pi/3, {1, 1, 1}],
    Rotation[2 Pi/3, {-1, 1, 1}], Rotation[4 Pi/3, {-1, 1, 1}],
    Rotation[2 Pi/3, {1, -1, 1}], Rotation[4 Pi/3, {1, -1, 1}],
    Rotation[2 Pi/3, {-1, -1, 1}], Rotation[4 Pi/3, {-1, -1, 1}],
    Pauli[0] };
  ff = {
    1, -1, I, -I,
    Exp[I Pi/4], -Exp[I Pi/4],
    Exp[-I Pi/4], -Exp[-I Pi/4] };
  Sort @ Garner @ ExpToTrig[ Times @@@ Tuples[{ff, op}] ]
 ]


CliffordGroup /:
GroupElements @ CliffordGroup[S_?QubitQ] :=
  GroupElements @ CliffordGroup @ S @ {None}

CliffordGroup /:
GroupElements @ CliffordGroup[{_?QubitQ, __?QubitQ}] :=
  Message[CliffordGroup::toobig]

CliffordGroup /:
GroupElements @ CliffordGroup[{S_?QubitQ}] := Module[
  { op, ff },
  op = Flatten @ {
    Rotation[#, S[1]] & /@ {Pi/2, -Pi/2, Pi},
    Rotation[#, S[2]] & /@ {Pi/2, -Pi/2, Pi},
    Rotation[#, S[3]] & /@ {Pi/2, -Pi/2, Pi},
    Rotation[Pi, S, {1, 1, 0}], Rotation[Pi, S, {-1, 1, 0}],
    Rotation[Pi, S, {1, 0, 1}], Rotation[Pi, S, {0, 1, 1}],
    Rotation[Pi, S, {-1, 0, 1}], Rotation[Pi, S, {0, -1, 1}],
    Rotation[2 Pi/3, S, {1, 1, 1}], Rotation[4 Pi/3, S, {1, 1, 1}],
    Rotation[2 Pi/3, S, {-1, 1, 1}], Rotation[4 Pi/3, S, {-1, 1, 1}],
    Rotation[2 Pi/3, S, {1, -1, 1}], Rotation[4 Pi/3, S, {1, -1, 1}],
    Rotation[2 Pi/3, S, {-1, -1, 1}], Rotation[4 Pi/3, S, {-1, -1, 1}],
    1 };
  ff = {
    1, -1, I, -I,
    Exp[I Pi/4], -Exp[I Pi/4],
    Exp[-I Pi/4], -Exp[-I Pi/4] };
  Times @@@ Tuples[{ff, op}]
 ]

(**** </CliffordGroup> ****)


End[]

EndPackage[]
