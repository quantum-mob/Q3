(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

`Gottesman`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.60 $"][[2]], " (",
  StringSplit["$Date: 2021-12-23 10:10:54+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ PauliGroup, CliffordGroup };

{ PauliMeasurement };

{ GottesmanVector, FromGottesmanVector,
  GottesmanTest,
  GottesmanInner,
  GottesmanBasis };

{ Stabilizer };

{ BinarySymplecticGroup,
  BinarySymplecticGroupElement };

{ Transvection,
  FindTransvections };


Begin["`Private`"]

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
GroupOrder @ CliffordGroup[n_Integer] := Module[
  {j},
  Power[2, n^2 + 2*n + 3] * Product[4^j-1, {j, 1, n}]
 ]
(* NOTE: See Koenig (2014a). *)

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


GottesmanInner::usage = "GottesmanInner[v, w] gives the symplectic inner product in the Gottesman vector space."

GottesmanInner::incon = "Inconsistent vectors `1` and `2`."

GottesmanInner::odd = "Odd-dimensional vectors `1` and `2`."

GottesmanInner[v_?VectorQ, w_?VectorQ] :=
  Mod[Dot[v, Flatten[Reverse /@ Partition[w, 2]]], 2] /;
  ArrayQ[{v, w}] && EvenQ[Length @ v]

GottesmanInner[v_?VectorQ, w_?VectorQ] := (
  Message[GottesmanInner::odd, v, w];
  0 ) /; ArrayQ[{v, w}] && OddQ[Length @ v]

GottesmanInner[v_?VectorQ, w_?VectorQ] := (
  Message[GottesmanInner::incon, v, w];
  0 ) /; Not @ ArrayQ @ {v, w}

GottesmanBasis::usage = "GottesmanBasis[{v1, v2, \[Ellipsis]}] returns a symplectic basis of the vector space spanned by {v1, v2, \[Ellipsis]}.\nGottesmanBasis[v] returns a symplectic basis {v, \[Ellipsis]} spanning the Gottesman vector space containing v.\nGottesmanBasis[n] returns the standard basis of the n-qubit (2n-dimensional) Gottesman vector space, which happens to be a symplectic basis with respect to GottesmanInner."

GottesmanBasis[bs:{__?VectorQ}] := Module[
  { v = First @ bs,
    w, new },
  w = Select[bs, GottesmanInner[v, #]==1&];
  If[ Length[w] == 0,
    Return[bs],
    w = First[w]
   ];
  new = Map[
    Mod[# + w * GottesmanInner[v, #] + v * GottesmanInner[w, #], 2]&,
    DeleteCases[Rest @ bs, w]
   ];
  Join[{v, w}, new]
 ] /; ArrayQ @ bs

GottesmanBasis[v_?VectorQ] := One[Length @ v] /;
  v == UnitVector[Length @ v, 1]

GottesmanBasis[v_?VectorQ] := With[
  { id = IdentityMatrix[Length @ v] },
  GottesmanBasis @ Join[{v}, Rest @ id]
 ]

GottesmanBasis[n_Integer] := One[2*n] /; n > 0

(**** </GottesmanVector> ****)


Stabilizer::usage = "Stabilizer[graph] returns a generating set of the stabilizer of the graph state associated with the graph.\nStabilizer[graph, vtx] gives the operator associated with the vertex vtx that stabilize the graph state associated with graph."

Stabilizer[grp_Graph] := Map[Stabilizer[grp, #] &, VertexList[grp]]

Stabilizer[grp_Graph, vtx_] := Module[
  { new = If[FlavorLast[vtx] === None, Drop[vtx, -1], vtx],
    adj },
  adj = AdjacencyList[grp, new|new[None]];
  vtx[1] ** Apply[Multiply, Through[adj[3]]]
 ]


(**** <BinarySymplecticGroup> ****)

BinarySymplecticGroup::usage = "BinarySymplecticGroup[n] represents the symplectic group Sp(2n, {0, 1}), that is, the group of 2n\[Times]2n symplectic matrices with elements 0 or 1."

BinarySymplecticGroup::toobig = "Too many elements to list in the binary symplectic group on two or more qubits."


BinarySymplecticGroup /:
GroupOrder @ BinarySymplecticGroup[n_Integer] := Module[
  { j },
  Power[2, n^2] * Product[4^j - 1, {j, 1, n}]
 ] /; n > 0


BinarySymplecticGroup /:
GroupElements @ BinarySymplecticGroup[1] :=
  BinarySymplecticGroupElement[1, Range[6]]

BinarySymplecticGroup /:
GroupElements @ BinarySymplecticGroup[n_Integer] := (
  Message[BinarySymplecticGroup::toobig];
  BinarySymplecticGroupElement[2, Range[6]]
 )


BinarySymplecticGroupElement::usage = "BinarySymplecticGroupElement[n, j] returns the j'th symplectic matrix in BinarySymplecticGroup[n], where j=1, 2, \[Ellipsis], (group order)."

SetAttributes[BinarySymplecticGroupElement, Listable];

(* See Koenig (2014a) for the algorithm. *)
BinarySymplecticGroupElement[n_Integer, j_Integer] := Module[
  { nn = 2*n, s, k,
    js, e1, f1, h0, tt, bb, ep, id, gg },
  (* step 1 *)
  s = BitShiftLeft[1, nn] - 1;
  k = Mod[j, s, 1]; (* NOTE: j start from 1. *)
  js = Quotient[j-1, s]; (* NOTE: j start from 1. *)

  (* step 2 *)
  f1 = IntegerDigits[k, 2, nn];

  (* step 3 *)
  e1 = UnitVector[nn, 1];
  tt = FindTransvections[e1, f1];

  (* step 4 *)
  bb = IntegerDigits[Mod[js, BitShiftLeft[1, nn-1]], 2, nn-1];

  (* step 5 *)
  ep = Join[e1[[;;2]], Rest @ bb];
  h0 = Transvection[tt[[2]], Transvection[tt[[1]], ep]];

  (* step 6 *)
  If[First[bb] == 1, f1 *= 0];

  (* step 7 *)
  id = One[2];
  gg = If[ n == 1,
    id,
    CirclePlus[
      id,
      BinarySymplecticGroupElement[n-1, 1 + BitShiftRight[js, nn-1]]
      (* NOTE: j starts from 1. *)
     ]
   ];
  Map[
    Transvection[f1,
      Transvection[h0,
        Transvection[tt[[2]],
          Transvection[tt[[1]], #]]]]&,
    gg
   ]
 ] /; n > 0 && (1 <= j <= GroupOrder[BinarySymplecticGroup[n]])

(**** </BinarySymplecticGroup> ****)



(**** <Transvection> ****)
(* See Koenig (2014a) *)

Transvection::usage = "Transvection[v, w] gives w + v\[LeftAngleBracket]v,w\[RightAngleBracket], where \[LeftAngleBracket]\[CenterDot],\[CenterDot]\[RightAngleBracket] is the Gottesman inner product. It is a symplectic Householder transformation."

Transvection::incon = "Inconsistent vectors `` and ``."

Transvection[v_?VectorQ, w_?VectorQ] :=
  Mod[w + v * GottesmanInner[v, w], 2] /;
  ArrayQ @ {v, w}

Transvection[v_?VectorQ, w_?VectorQ] := (
  Message[Transvection::incon, v, w];
  w
 )


FindTransvections::usage = "FindTransvections[v, w] returns a list of two vectors {u1, u2} such that w = Transvection[u1, Transvection[u2, v]]."

FindTransvections[m_?MatrixQ] := FindTransvections[m[[1]], m[[2]]]

FindTransvections[x_?VectorQ, y_?VectorQ] := Zero[2, Length @ x] /; x == y

FindTransvections[x_?VectorQ, y_?VectorQ] := {
  Mod[x + y, 2],
  Zero[Length @ x]
 } /; GottesmanInner[x, y] == 1

FindTransvections[x_?VectorQ, y_?VectorQ] := Module[
  { assoc, k, z },
  assoc = PositionIndex @ Transpose @ Map[
    Positive,
    {Total /@ Partition[x, 2], Total /@ Partition[y, 2]},
    {2}
   ];
  z = Zero[Length @ x];
  If[ KeyExistsQ[assoc, {True, True}],
    k = First @ assoc @ {True, True};
    z[[2*k-1;;2*k]] = solveBinaryEq[x[[2*k-1;;2*k]], y[[2*k-1;;2*k]]],
    k = First @ assoc @ {True, False};
    z[[2*k-1;;2*k]] = solveBinaryEq[x[[2*k-1;;2*k]]];
    k = First @ assoc @ {False, True};
    z[[2*k-1;;2*k]] = solveBinaryEq[y[[2*k-1;;2*k]]];
   ];
  {Mod[x+z, 2], Mod[y+z, 2]}
 ] /; ArrayQ @ {x, y}

(* Solves the set of equations
   x1 * b + x2 * a = 1;
   y1 * b + y2 * a = 1;
   *)
solveBinaryEq[x:{_, _}, y:{_, _}] := Module[
  { z = Mod[x + y, 2] },
  If[Total[z] == 0, z[[2]] = 1];
  z
 ]

(* Solve the quation
   x1 * b + x2 * a = 1
   *)
solveBinaryEq[x:{_, _}] := If[First[x] == 0, {1, 0}, {0, 1}]

(**** </Transvection> ****)


End[]

EndPackage[]
