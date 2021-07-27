(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

`Stabilizer`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.31 $"][[2]], " (",
  StringSplit["$Date: 2021-07-27 14:04:28+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ PauliForm };

{ PauliGroup, CliffordGroup };

{ GottesmanVector, FromGottesmanVector,
  GottesmanTest };

{ Stabilizer };


Begin["`Private`"]

(**** <PauliForm> ****)

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

PauliGroup::todo = "Not supported yet."

PauliGroup[S_?QubitQ] := PauliGroup @ {S}

PauliGroup[ss:{__?QubitQ}] := PauliGroup[FlavorNone @ ss] /;
  Not @ ContainsOnly[FlavorLast @ ss, {None}]


PauliGroup /:
GroupOrder @ PauliGroup[n_Integer] := Power[4, n+1] /; n > 0

PauliGroup /:
GroupOrder @ PauliGroup[ss:{__?QubitQ}] :=
  GroupOrder @ PauliGroup @ Length @ ss


PauliGroup /:
GroupElements @ PauliGroup[n_Integer] := Module[
  { op = Pauli @@@ Tuples[{0, 1, 2, 3}, n] },
  Catenate @ {op, -op, I op, -I op}
 ] /; n > 0

PauliGroup /:
GroupGenerators @ PauliGroup[n_Integer] := Module[
  { op = Pauli @@ ConstantArray[0, n],
    kk = Range[n] },
  kk = Flatten[ Thread /@ {kk -> 1, kk -> 2, kk ->3 } ];
  Sort @ Map[ReplacePart[op, #]&, kk]
 ] /; n > 0


PauliGroup /:
GroupElements @ PauliGroup[qq:{__?QubitQ}] := Module[
  { op = Elaborate @ Through @ qq[Full] },
  op = Multiply @@@ Tuples[op];
  Catenate @ {op, -op, I op, -I op}
 ]

PauliGroup /:
GroupGenerators @ PauliGroup[qq:{__?QubitQ}] :=
  Sort @ Flatten @ Through @ qq[All]


PauliGroup /:
GroupMultiplicationTable @ PauliGroup[1] = {
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, 
  {2, 1, 12, 15, 6, 5, 16, 11, 10, 9, 8, 3, 14, 13, 4, 7}, 
  {3, 16, 1, 10, 7, 12, 5, 14, 11, 4, 9, 6, 15, 8, 13, 2}, 
  {4, 11, 14, 1, 8, 15, 10, 5, 12, 7, 2, 9, 16, 3, 6, 13}, 
  {5, 6, 7, 8, 1, 2, 3, 4, 13, 14, 15, 16, 9, 10, 11, 12}, 
  {6, 5, 16, 11, 2, 1, 12, 15, 14, 13, 4, 7, 10, 9, 8, 3}, 
  {7, 12, 5, 14, 3, 16, 1, 10, 15, 8, 13, 2, 11, 4, 9, 6}, 
  {8, 15, 10, 5, 4, 11, 14, 1, 16, 3, 6, 13, 12, 7, 2, 9}, 
  {9, 10, 11, 12, 13, 14, 15, 16, 5, 6, 7, 8, 1, 2, 3, 4}, 
  {10, 9, 8, 3, 14, 13, 4, 7, 6, 5, 16, 11, 2, 1, 12, 15}, 
  {11, 4, 9, 6, 15, 8, 13, 2, 7, 12, 5, 14, 3, 16, 1, 10}, 
  {12, 7, 2, 9, 16, 3, 6, 13, 8, 15, 10, 5, 4, 11, 14, 1}, 
  {13, 14, 15, 16, 9, 10, 11, 12, 1, 2, 3, 4, 5, 6, 7, 8}, 
  {14, 13, 4, 7, 10, 9, 8, 3, 2, 1, 12, 15, 6, 5, 16, 11}, 
  {15, 8, 13, 2, 11, 4, 9, 6, 3, 16, 1, 10, 7, 12, 5, 14}, 
  {16, 3, 6, 13, 12, 7, 2, 9, 4, 11, 14, 1, 8, 15, 10, 5}
 }

PauliGroup /:
GroupMultiplicationTable @ PauliGroup[n_Integer] := Module[
  { elm = GroupElements @ PauliGroup[n],
    mat },
  mat = Outer[Multiply, elm, elm];
  Map[First @ FirstPosition[elm, #]&, mat, {2}]
 ]

PauliGroup /:
GroupMultiplicationTable @ PauliGroup[ss:{__?QubitQ}] :=
  GroupMultiplicationTable @ PauliGroup @ Length @ ss
  
(**** </PauliGroup> ****)


(**** <CliffordGroup> ****)

CliffordGroup::usage = "CliffordGroup[n] represents the Clifford group, the normalizer group of the Pauli group, on n qubits.\nCliffordGroup[{s1, s2, ...}] represents the Clifford group, the normalizer group of the Pauli group, on the qubits {s1, s2, \[Ellipsis]}."

CliffordGroup::toobig = "Too many elements in the Clifford group on two or more qubits to list."

CliffordGroup::todo = "Not supported yet."

CliffordGroup[S_?QubitQ] := CliffordGroup @ {S}

CliffordGroup[ss:{__?QubitQ}] := CliffordGroup[FlavorNone @ ss] /;
  Not @ ContainsOnly[FlavorLast @ ss, {None}]


CliffordGroup /:
GroupOrder @ CliffordGroup[1] = 192 

CliffordGroup /:
GroupOrder @ CliffordGroup[n_Integer] :=
  Message[CliffordGroup::todo] /; n > 1

CliffordGroup /:
GroupOrder @ CliffordGroup[ss:{__?QubitQ}] :=
  GroupOrder @ CliffordGroup @ Length @ ss


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


(**** <GottesmanVector> ****)

GottesmanVector::usage = "Gottesmann[op] returns the vector in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\) corresponding to the coset represented by the Pauli operator op on n (unlabeled) qubits.\nGottesmann[op, {S1,S2,...,Sn}] returns the vector in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\) corresponding to the coset represented by the Pauli operator op on the (labeled) qubits {S1, S2, ..., Sn}."

GottesmanVector[_?CommutativeQ op_] := GottesmanVector[op]

GottesmanVector[op_Pauli] := Flatten @ ReplaceAll[
  List @@ op,
  { 0 -> {0, 0},
    1 -> {1, 0},
    2 -> {1, 1},
    3 -> {0, 1} }
 ]

GottesmanVector[_?CommutativeQ, ss:{__?QubitQ}] :=
  GottesmanVector[Pauli @@ ConstantArray[0, Length @ ss]]

GottesmanVector[_?CommutativeQ op_, ss:{__?QubitQ}] :=
  GottesmanVector[op, ss]

GottesmanVector[op_?QubitQ, ss:{__?QubitQ}] := With[
  { qq = FlavorNone[ss] },
  GottesmanVector @ Apply[
    Pauli,
    qq /. {FlavorMute[op] -> FlavorLast[op]} /. Thread[qq -> 0]
   ]
 ]

HoldPattern @ GottesmanVector[Multiply[op__?QubitQ], ss:{__?QubitQ}] := With[
  { qq = FlavorNone[ss] },
  GottesmanVector @ Apply[
    Pauli,
    qq /. Thread[FlavorMute @ {op} -> FlavorLast @ {op}] /. Thread[qq -> 0]
   ]
 ]

GottesmanVector[expr_] := GottesmanVector[expr, Qubits @ expr] /;
  FreeQ[expr, _Pauli]


FromGottesmanVector::usage = "FromGottesmanVector[vec] returns the Pauli operator on unlabeled qubits representing the coset corresponding to the GottesmanVector vec in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\), where n is the number of (unlabeled) qubits.\nFromGottesmanVector[vec, {S1,S2,...,Sn}] returns the Pauli operator on qubits {S1,S2,...,Sn} representing the coset corresponding to the GottesmanVector vec in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\)."

FromGottesmanVector::wrong = "Invalid Gottesman vector ``."

FromGottesmanVector[vec:{(0|1)..}] :=
  Message[FromGottesmanVector::wrong, vec] /;
  OddQ[Length @ vec]

FromGottesmanVector[vec:{(0|1)..}] := Pauli @@ ReplaceAll[
  Partition[vec, 2],
  { {0, 0} -> 0,
    {1, 0} -> 1,
    {1, 1} -> 2,
    {0, 1} -> 3 }
 ]


FromGottesmanVector[vec:{(0|1)..}, ss:{__?QubitQ}] :=
  Message[FromGottesmanVector::wrong, vec] /;
  Length[vec] != 2 Length[ss]

FromGottesmanVector[vec:{(0|1)..}, S_?QubitQ] :=
  FromGottesmanVector[vec, {S}]

FromGottesmanVector[vec:{(0|1)..}, ss:{__?QubitQ}] := Multiply @@ MapThread[
  Construct,
  { ss,
    ReplaceAll[
      Partition[vec, 2],
      { {0, 0} -> 0,
        {1, 0} -> 1,
        {1, 1} -> 2,
        {0, 1} -> 3 }
     ] }
 ]


GottesmanTest::usage = "GottesmanTest[a, b] returns 1 if the two operators a and b commute with each other, -1 if they anti-commute, and 0 otherwise."

GottesmanTest[a_, b_] := If[
  TrueQ[Commutator[a, b] == 0],
  1,
  If[Anticommutator[a, b] == 0, -1, 0, 0]
 ]


Stabilizer::usage = "Stabilizer[graph] returns a generating set of the stabilizer of the graph state associated with the graph.\nStabilizer[graph, vtx] gives the operator associated with the vertex vtx that stabilize the graph state associated with graph."

Stabilizer[grp_Graph] := Map[Stabilizer[grp, #] &, VertexList[grp]]

Stabilizer[grp_Graph, vtx_] := Module[
  { new = If[FlavorLast[vtx] === None, Drop[vtx, -1], vtx],
    adj },
  adj = AdjacencyList[grp, new|new[None]];
  vtx[1] ** Apply[Multiply, Through[adj[3]]]
 ]

(**** </GottesmanVector> ****)


End[]

EndPackage[]
