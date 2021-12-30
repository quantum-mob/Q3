(* -*- mode:math -*- *)
(* Package for stabilizer formalism *)

BeginPackage["Q3`"]

`Gottesman`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.7 $"][[2]], " (",
  StringSplit["$Date: 2021-12-30 11:33:52+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ PauliGroup, FullPauliGroup,
  PauliGroupElements, FullPauliGroupElements,
  CliffordGroup, FullCliffordGroup,
  CliffordGroupElements, FullCliffordGroupElements };

{ GottesmanVector, FromGottesmanVector,
  GottesmanTest,
  GottesmanInner,
  GottesmanBasis };

{ GottesmanMatrix, FromGottesmanMatrix };

{ Stabilizer };

{ BinarySymplecticGroup,
  BinarySymplecticGroupElements };

Begin["`Private`"]

(**** <PauliGroup> ****)

FullPauliGroup::usage = "FullPauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators, on n qubits.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup::usage = "PauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators up to global phase factors, on n qubits. It is a factor group FullPauliGroup[n]/{Exp[\[ImaginaryI] m\[Pi]/2]:m=0,1,2,3}.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup::todo = "Not supported yet."

FullPauliGroup[S_?QubitQ] := FullPauliGroup @ {S}

FullPauliGroup[ss:{__?QubitQ}] := FullPauliGroup[FlavorNone @ ss] /;
  Not @ ContainsOnly[FlavorLast @ ss, {None}]

PauliGroup[S_?QubitQ] := PauliGroup @ {S}

PauliGroup[ss:{__?QubitQ}] := PauliGroup[FlavorNone @ ss] /;
  Not @ ContainsOnly[FlavorLast @ ss, {None}]


FullPauliGroup /:
GroupOrder @ FullPauliGroup[ss:{__?QubitQ}] :=
  4 * GroupOrder[PauliGroup @ ss]

FullPauliGroup /:
GroupOrder @ FullPauliGroup[n_Integer] :=
  4 * GroupOrder[PauliGroup @ n]

PauliGroup /:
GroupOrder @ PauliGroup[ss:{__?QubitQ}] :=
  GroupOrder @ PauliGroup @ Length @ ss

PauliGroup /:
GroupOrder @ PauliGroup[n_Integer] := Power[4, n] /; n >= 0


FullPauliGroup /:
GroupGenerators @ FullPauliGroup[qq:{__?QubitQ}] :=
  GroupGenerators[PauliGroup @ qq]

FullPauliGroup /:
GroupGenerators @ FullPauliGroup[n_Integer] :=
  GroupGenerators[PauliGroup @ n]

PauliGroup /:
GroupGenerators @ PauliGroup[qq:{__?QubitQ}] :=
  Sort @ Flatten @ Through @ qq[All]

PauliGroup /:
GroupGenerators @ PauliGroup[n_Integer] := Module[
  { op = Pauli @@ ConstantArray[0, n],
    kk = Range[n] },
  kk = Flatten[ Thread /@ {kk -> 1, kk -> 2, kk ->3 } ];
  Sort @ Map[ReplacePart[op, #]&, kk]
 ] /; n > 0


FullPauliGroup /:
GroupElements[FullPauliGroup[spec_], rest___] :=
  FullPauliGroupElements[spec, rest]

PauliGroup /:
GroupElements[PauliGroup[spec_], rest___] :=
  PauliGroupElements[spec, rest]


FullPauliGroupElements::usage = "FullPauliGroupElements[n] returns a list of all elements in the Pauli group on n qubits. FullPauliGroupElements[n, {k$1,k$2,$$}] gives a list of elements numbered k$1,k$2,$$. FullPauliGroupElements[{s$1,s$2,$$,s$n},{k$1,k$2,$$}] refers to the Pauli group on n labelled qubits {s$1,s$2,$$,s$n}."

FullPauliGroupElements[spec_] :=
  FullPauliGroupElements[spec, Range @ GroupOrder @ FullPauliGroup[spec]]

FullPauliGroupElements[spec:(_Integer|{__?QubitQ}), kk:{__Integer}] :=
  Module[
    { gn = GroupOrder[PauliGroup @ spec],
      ff = {1, -1, I, -I},
      qq, rr },
    qq = Quotient[kk-1, gn] + 1;
    rr = Mod[kk-1, gn] + 1;
    MapThread[Times, {ff[[qq]], PauliGroupElements[spec, rr]}]
   ]


PauliGroupElements::usage = "PauliGroupElements[n] returns a list of all elements in the Pauli group on n qubits. PauliGroupElements[n, {k$1,k$2,$$}] gives a list of elements numbered k$1,k$2,$$. PauliGroupElements[{s$1,s$2,$$,s$n},{k$1,k$2,$$}] refers to the Pauli group on n labelled qubits {s$1,s$2,$$,s$n}."

PauliGroupElements[ss:{__?QubitQ}] :=
  PauliGroupElements[ss, Range @ GroupOrder @ PauliGroup @ ss]

PauliGroupElements[ss:{__?QubitQ}, kk:{__Integer}] :=
  getPauliGroupElement[ss, #]& /@ kk

PauliGroupElements[n_Integer] :=
  PauliGroupElements[n, Range @ GroupOrder @ PauliGroup @ n]

PauliGroupElements[n_Integer, kk:{__Integer}] :=
  getPauliGroupElement[n, #]& /@ kk


getPauliGroupElement::usage = "getPauliGroupElement[n, k] ..."

getPauliGroupElement[n_Integer?Positive, k_Integer] :=
  FromGottesmanVector @ fPauliGroupElement[n, k]

getPauliGroupElement[ss:{__?QubitQ}, k_Integer] :=
  FromGottesmanVector[fPauliGroupElement[Length @ ss, k], ss] /.
  { _?QubitQ[___, 0] -> 1 }

fPauliGroupElement[n_Integer?Positive, k_Integer] := Module[
  { cc = IntegerDigits[k-1, 2, 2*n] },
  Flatten[Reverse /@ Reverse @ Partition[cc, 2]]
 ]


FullPauliGroup /:
GroupMultiplicationTable @ FullPauliGroup[n_Integer] := Module[
  { elm = GroupElements @ FullPauliGroup[n],
    mat },
  mat = Outer[Multiply, elm, elm];
  Map[First @ FirstPosition[elm, #]&, mat, {2}]
 ]

FullPauliGroup /:
GroupMultiplicationTable @ FullPauliGroup[ss:{__?QubitQ}] :=
  GroupMultiplicationTable @ FullPauliGroup @ Length @ ss
  

PauliGroup /:
GroupMultiplicationTable @ PauliGroup[n_Integer] := Module[
  { elm = GroupElements @ PauliGroup[n],
    mat },
  mat = Outer[Multiply, elm, elm] /. {_?CommutativeQ * op_ -> op};
  Map[First @ FirstPosition[elm, #]&, mat, {2}]
 ]

PauliGroup /:
GroupMultiplicationTable @ PauliGroup[ss:{__?QubitQ}] :=
  GroupMultiplicationTable @ PauliGroup @ Length @ ss
  
(**** </PauliGroup> ****)


(**** <CliffordGroup> ****)

FullCliffordGroup::usage = "FullCliffordGroup[n] represents the full Clifford group (taking into account the global phase factors), the normalizer group of the full Pauli group, on n qubits.\nCliffordGroup[{s1, s2, ...}] represents the full Clifford group on labelled qubits {s1, s2, \[Ellipsis]}."

CliffordGroup::usage = "CliffordGroup[n] represents the Clifford group (ignoring global phase factors), the normalizer group of the Pauli group, on n qubits.\nCliffordGroup[{s1, s2, ...}] represents the Clifford group on labelled qubits {s1, s2, \[Ellipsis]}.\nCliffordGroup[n] is a quotient group FullCliffordGroup[n] / {Exp[\[ImaginaryI] m \[Pi]/4] : m=0,1,2,\[Ellipsis],7}."

FullCliffordGroup::toobig = "There are about `` elements in the group. Only the first 10 elements are returned."

CliffordGroup::toobig = "There are about `` elements in the group. Only the first 10 elements are returned."

CliffordGroup::todo = "Not supported yet."

FullCliffordGroup[S_?QubitQ] := FullCliffordGroup @ {S}

FullCliffordGroup[ss:{__?QubitQ}] := FullCliffordGroup[FlavorNone @ ss] /;
  Not @ ContainsOnly[FlavorLast @ ss, {None}]

CliffordGroup[S_?QubitQ] := CliffordGroup @ {S}

CliffordGroup[ss:{__?QubitQ}] := CliffordGroup[FlavorNone @ ss] /;
  Not @ ContainsOnly[FlavorLast @ ss, {None}]


FullCliffordGroup /:
GroupOrder @ FullCliffordGroup[n_Integer] :=
  8 * GroupOrder[CliffordGroup @ n]

FullCliffordGroup /:
GroupOrder @ FullCliffordGroup[ss:{__?QubitQ}] :=
  8 * GroupOrder[CliffordGroup @ ss]

CliffordGroup /:
GroupOrder @ CliffordGroup[n_Integer] := Block[
  {k},
  Power[2, n^2 + 2*n] * Product[4^k-1, {k, 1, n}]
 ]

CliffordGroup /:
GroupOrder @ CliffordGroup[ss:{__?QubitQ}] :=
  GroupOrder @ CliffordGroup @ Length @ ss


FullCliffordGroup /:
GroupGenerators @ FullCliffordGroup[spec_] :=
  GroupGenerators[CliffordGroup @ spec]

CliffordGroup /:
GroupGenerators @ CliffordGroup[n_Integer] := Block[
  { S, ss },
  Let[Qubit, S];
  ss = S[Range @ n, None];
  gg = GroupGenerators[CliffordGroup @ ss];
  ExpressionFor /@ Matrix[gg, ss]
 ]

CliffordGroup /:
GroupGenerators @ CliffordGroup[qq:{__?QubitQ}] := Module[
  { ss = Through[qq @ {6, 7}],
    cn = CZ @@@ Subsets[FlavorNone @ qq, {2}] },
  Flatten @ {ss, cn}
 ]


FullCliffordGroup /:
GroupElements[grp_FullCliffordGroup] := (
  Message[FullCliffordGroup::toobig,
    ScientificForm[N @ GroupOrder @ grp, 2]];
  GroupElements[grp, Range @ 10]
 )

FullCliffordGroup /:
GroupElements[FullCliffordGroup[spec_], rest___] :=
  FullCliffordGroupElements[spec, rest]

CliffordGroup /:
GroupElements[grp_CliffordGroup] := (
  Message[CliffordGroup::toobig,
    ScientificForm[N @ GroupOrder @ grp, 2]];
  GroupElements[grp, Range @ 10]
 )

CliffordGroup /:
GroupElements[CliffordGroup[spec_], rest___] :=
  CliffordGroupElements[spec, rest]


FullCliffordGroupElements::usage = "CliffordGroupElements[n, {k$1,k$2,$$}] returns a list of the elements numbered k$1, k$2, $$ in the full Clifford group of degree n. FullCliffordGroupElements[{s$1,s$2,$$,s$n}, {k$1,k$2,$$}] refers to the group on n labelled qubits {s$1,s$2,$$}."

CliffordGroupElements::usage = "CliffordGroupElements[n, {k$1,k$2,$$}] returns a list of the elements numbered k$1, k$2, $$ in the Clifford group of degree n. CliffordGroupElements[{s$1,s$2,$$,s$n}, {k$1,k$2,$$}] refers to the group on n labelled qubits {s$1,s$2,$$}."

FullCliffordGroupElements[spec:(_Integer|{__?QubitQ}), kk:{__Integer}] :=
  Module[
    { gn = GroupOrder[CliffordGroup @ spec],
      ff, qq, rr, k },
    ff = Table[Exp[I k Pi/4], {k, 0, 7}];
    qq = Quotient[kk-1, gn] + 1;
    rr = Mod[kk-1, gn] + 1;
    MapThread[Times, {ff[[qq]], CliffordGroupElements[spec, rr]}]
   ]

CliffordGroupElements[spec:(_Integer|{__?QubitQ}), kk:{__Integer}] :=
  Module[
    { gn = GroupOrder @ BinarySymplecticGroup[spec],
      sp, qq, rr, ff },

    qq = Quotient[kk-1, gn] + 1;
    rr = Mod[kk-1, gn] + 1;

    ff = PauliGroupElements[spec, qq];
    sp = GroupElements[BinarySymplecticGroup[spec], rr];
    sp = FromGottesmanMatrix[#, spec]& /@ sp;
    Elaborate @ MapThread[Multiply, {ff, sp}]
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

HoldPattern @
  GottesmanVector[Multiply[op__?QubitQ], ss:{__?QubitQ}] := With[
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
 ] /. { _?QubitQ[___, 0] -> 1 }


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

BinarySymplecticGroup::degree = "The binary symplectic group is not defined for degree ``; defined only for a degree of positive integer."

BinarySymplecticGroup::toobig = "There are about `` elements in the group. Only the first 6 elements are returned."

BinarySymplecticGroup[ss:{__?QubitQ}] := BinarySymplecticGroup[Length @ ss]

BinarySymplecticGroup /:
GroupOrder @ BinarySymplecticGroup[n_Integer] :=
  BinarySymplecticGroupOrder[n]

BinarySymplecticGroupOrder[n_Integer?Positive] := Block[
  { k },
  Power[2, n^2] * Product[4^k - 1, {k, 1, n}]
 ]

BinarySymplecticGroupOrder[n_] :=
  (Message[BinarySymplecticGroup::degree, n]; 0)


BinarySymplecticGroup /:
GroupElements[BinarySymplecticGroup[n_], rest___] :=
  BinarySymplecticGroupElements[n, rest]

BinarySymplecticGroupElements[n_Integer?Positive] := (
  If[ n > 1,
    Message[BinarySymplecticGroup::toobig,
      ScientificForm[N @ GroupOrder @ BinarySymplecticGroup @ n, 2]] ];
  BinarySymplecticGroupElements[n, Range[6]]
 )

BinarySymplecticGroupElements[ss:{__?QubitQ}, kk:{__Integer}] :=
  getSpElement[Length @ ss, kk]

BinarySymplecticGroupElements[n_Integer?Positive, kk:{__Integer}] :=
  getSpElement[n, kk]

BinarySymplecticGroupElements[n_, kk:{__Integer}] :=
  (Message[BinarySymplecticGroup::degree, n]; {})

(**** </BinarySymplecticGroup> ****)


(**** <Koenig-Smolin Algorihm for BinarySymplecticGroup> ****)
(* See Koenig (2014a) *)

getSpElement::usage = "getSpElement[n, k] returns the k'th symplectic matrix in BinarySymplecticGroup[n]."

SetAttributes[getSpElement, Listable];

(* See Koenig (2014a) for the algorithm. *)
getSpElement[n_Integer, j_Integer] := Module[
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
  tt = FindGottesmanShears[e1, f1];

  (* step 4 *)
  bb = IntegerDigits[Mod[js, BitShiftLeft[1, nn-1]], 2, nn-1];

  (* step 5 *)
  ep = Join[e1[[;;2]], Rest @ bb];
  h0 = GottesmanShear[tt[[2]], GottesmanShear[tt[[1]], ep]];

  (* step 6 *)
  If[First[bb] == 1, f1 *= 0];

  (* step 7 *)
  id = One[2];
  gg = If[ n == 1,
    id,
    CirclePlus[
      id,
      getSpElement[n-1, 1 + BitShiftRight[js, nn-1]]
      (* NOTE: j starts from 1. *)
     ]
   ];
  Map[
    GottesmanShear[f1,
      GottesmanShear[h0,
        GottesmanShear[tt[[2]],
          GottesmanShear[tt[[1]], #]]]]&,
    gg
   ]
 ]


GottesmanShear::usage = "GottesmanShear[v, w] gives w + v\[LeftAngleBracket]v,w\[RightAngleBracket], where \[LeftAngleBracket]\[CenterDot],\[CenterDot]\[RightAngleBracket] is the Gottesman inner product. GottesmanShear is a shear transformation."

GottesmanShear::incon = "Inconsistent vectors `` and ``."

GottesmanShear[v_?VectorQ, w_?VectorQ] :=
  Mod[w + v * GottesmanInner[v, w], 2] /;
  ArrayQ @ {v, w}

GottesmanShear[v_?VectorQ, w_?VectorQ] := (
  Message[GottesmanShear::incon, v, w];
  w
 )


FindGottesmanShears::usage = "FindGottesmanShears[v, w] returns a list of two vectors {u1, u2} such that w = GottesmanShear[u1, GottesmanShear[u2, v]]."

FindGottesmanShears[m_?MatrixQ] := FindGottesmanShears[m[[1]], m[[2]]]

FindGottesmanShears[x_?VectorQ, y_?VectorQ] := Zero[2, Length @ x] /; x == y

FindGottesmanShears[x_?VectorQ, y_?VectorQ] := {
  Mod[x + y, 2],
  Zero[Length @ x]
 } /; GottesmanInner[x, y] == 1

FindGottesmanShears[x_?VectorQ, y_?VectorQ] := Module[
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

(**** </Koenig-Smolin Algorihm for BinarySymplecticGroup> ****)


(**** <GottesmanMatrix> ****)

GottesmanMatrix::usage = "GottesmanMatrix[op, {s$1,s$2,$$}] returns the binary symplectic matrix corresponding to Clifford operator op."

GottesmanMatrix[op_, S_?QubitQ] := GottesmanMatrix[op, {FlavorNone @ S}]

GottesmanMatrix[op_, ss:{__?QubitQ}] := Module[
  { n = Length @ ss,
    xz },
  xz = Flatten @ Through[ss @ {1, 3}];
  GottesmanVector[#, ss]& /@ Elaborate[Supermap[op] /@ xz]
 ]

GottesmanMatrix[op_] := Module[
  { n = Length @ First @ Cases[op, _Pauli, Infinity],
    xz },
  xz = Pauli @@@ Riffle[
    NestList[RotateRight, PadRight[{1}, n], n-1],
    NestList[RotateRight, PadRight[{3}, n], n-1]
   ];
  GottesmanVector /@ Elaborate[Supermap[op] /@ xz]
 ] /; Not @ FreeQ[op, _Pauli]


FromGottesmanMatrix::usage = "FromGottesmanMatrix[mat, {s$1,s$2,$$}] returns the Clifford operator corresponding to binary symplectic matrix mat."

FromGottesmanMatrix::badmat = "`` is not a valid binary symplectic matrix."

FromGottesmanMatrix[mat_?MatrixQ, ss:{_?QubitQ, __?QubitQ}] := Module[
  { n = Length @ ss,
    kk, qq, rr,
    ff, hh, aa, bb, vv,
    opf, oph, opa, opb, opv, cyc, new },

  ff = Transpose[Partition[#, 2]& /@ Take[mat, 2]];
  kk = FirstPosition[GottesmanInner @@@ ff, 1];
  
  If[ MissingQ[kk], 
    Message[FromGottesmanMatrix::badmat, MatrixForm @ mat];
    Return[1]
   ];

  If[ (kk = First[kk]) != 1,
    cyc = CircleTimes[
      Transpose @ PermutationMatrix[Cycles @ {{1, kk}}, n],
      One[2]
     ];
    new = Mod[mat . cyc, 2];
    opf = SWAP @@ Part[ss, {1, kk}];
    Return[opf ** FromGottesmanMatrix[new, ss]]
   ];

  {qq, rr} = TakeDrop[ss, 1];
  
  ff = First @ ff;
  ff = Mod[fSpInverse[ff] . ThePauli[1], 2];
  
  opf = FromGottesmanMatrix[ff, qq];

  new = CirclePlus[ff, One[2(n-1)]];
  new = Mod[mat . new, 2];

  aa = FromGottesmanVector[new[[2, 3;;]], rr];
  bb = FromGottesmanVector[new[[1, 3;;]], rr];
  aa = GottesmanMatrix[opa = ControlledU[qq, aa], ss];
  bb = GottesmanMatrix[opb = ControlledU[qq, bb], ss];
  hh = GottesmanMatrix[oph = First[qq][6], ss];

  vv = Mod[new . aa . hh . bb, 2];
  vv = vv[[3;;, 3;;]];

  opv = FromGottesmanMatrix[vv, rr];

  Elaborate[ Dagger[opf] ** opa ** oph ** opb ** opv ]
 ]

FromGottesmanMatrix[mat_?MatrixQ, S_?QubitQ] :=
  FromGottesmanMatrix[mat, {FlavorNone @ S}]

FromGottesmanMatrix[mat_?MatrixQ, {S_?QubitQ}] :=
  Elaborate @ Which[
    mat == ThePauli[1], S[6],
    mat == ThePauli[0], 1,
    mat == {{1, 1}, {0, 1}}, S[7],
    mat == {{0, 1}, {1, 1}}, S[7]**S[6],
    mat == {{1, 0}, {1, 1}}, S[7]**S[6]**Dagger[S[7]],
    mat == {{1, 1}, {1, 0}}, S[6]**Dagger[S[7]],
    True, 1
   ]

FromGottesmanMatrix[mat_?MatrixQ, _Integer] :=
  FromGottesmanMatrix[mat] (* for CliffordGroupElements *)

FromGottesmanMatrix[mat_?MatrixQ] := Block[
  { S, ss },
  Let[Qubit, S];
  ss = S[Range[Length[mat]/2], None];
  op = FromGottesmanMatrix[mat, ss];
  ExpressionFor @ Matrix[op, ss]
 ]


fSpInverse::usage = "fSpInverse[mat] returns the inverse of binary symplectic matrix mat (with respect to the Gottesman inner product)."

fSpInverse[mat_] := Module[
  { n = Length[mat] / 2,
    JX },
  JX = CircleTimes[One[n], ThePauli[1]];
  Mod[JX . Transpose[mat] . JX, 2]
 ]
  
(**** </GottesmanMatrix> ****)

End[]

EndPackage[]
