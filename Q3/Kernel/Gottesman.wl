(* stabilizer formalism *)

BeginPackage["Q3`"]

{ GottesmanVector, FullGottesmanVector,
  GottesmanVectorQ, FromGottesmanVector,
  GottesmanTest, GottesmanInner, GottesmanBasis,
  GottesmanSplit, GottesmanMerge, GottesmanFlip };

{ GottesmanTimes };

{ RandomGottesmanVector, RandomFullGottesmanVector };

{ GottesmanMatrix, FullGottesmanMatrix,
  FromGottesmanMatrix, GottesmanInverse,
  GottesmanMatrixQ };

{ RandomGottesmanMatrix, RandomFullGottesmanMatrix };

{ GottesmanStandard, GottesmanSolve };

{ CliffordDecompose = CliffordFactor };

{ Stabilizer, StabilizerGenerators, UpdateStabilizerGenerators };

{ StabilizerStateQ, StabilizerStateCount };

{ GottesmanGroup = BinarySymplecticGroup,
  GottesmanGroupOrder = BinarySymplecticGroupOrder,
  GottesmanGroupElements = BinarySymplecticGroupElements };

CliffordDecompose::usage = "CliffordDecompose is an alias of CliffordFactor."


Begin["`Private`"]

(**** <PauliGroup> ****)

FullPauliGroup::usage = "FullPauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators, on n qubits.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup::usage = "PauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators up to global phase factors, on n qubits. It is a factor group FullPauliGroup[n]/{Exp[\[ImaginaryI] m\[Pi]/2]:m=0,1,2,3}.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup::todo = "Not supported yet."

FullPauliGroup[S_?QubitQ] := FullPauliGroup @ {S}

FullPauliGroup[ss:{__?QubitQ}] := FullPauliGroup[FlavorCap @ ss] /;
  Not[FlavorCapQ @ {ss}]

PauliGroup[S_?QubitQ] := PauliGroup @ {S}

PauliGroup[ss:{__?QubitQ}] := PauliGroup[FlavorCap @ ss] /;
  Not[FlavorCapQ @ {ss}]


FullPauliGroup /:
GroupOrder @ FullPauliGroup[ss:{__?QubitQ}] :=
  4 * PauliGroupOrder[ss]

FullPauliGroup /:
GroupOrder @ FullPauliGroup[n_Integer] :=
  4 * PauliGroupOrder[n]

PauliGroup /:
GroupOrder @ PauliGroup[ss:{__?QubitQ}] :=
  PauliGroupOrder[Length @ ss]

PauliGroup /:
GroupOrder @ PauliGroup[n_Integer] :=
  PauliGroupOrder[n]


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
  { kk = {1,2,3} },
  kk = ArrayPad[{kk}, {{0, n - 1}, {0, 0}}];
  kk = Transpose /@ NestList[RotateRight, kk, n - 1];
  Pauli /@ Flatten[kk, 1]
 ] /; n > 0


FullPauliGroup /:
GroupElements[FullPauliGroup[spec_], rest___] :=
  FullPauliGroupElements[spec, rest]

PauliGroup /:
GroupElements[PauliGroup[spec_], rest___] :=
  PauliGroupElements[spec, rest]


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


FullPauliGroupOrder::usage = "FullPauliGroupOrder[n] returns the order of the Pauli group on n qubits."

FullPauliGroupOrder::neg = "Negative integer `` is given."

FullPauliGroupOrder[n_Integer] := Power[4, n+1] /; If[ n >= 0, True, 
  Message[FullPauliGroupOrder::neg, n];
  False
]

FullPauliGroupOrder[ss:{___?QubitQ}] := FullPauliGroupOrder[Length @ ss]


PauliGroupOrder::usage = "PauliGroupOrder[n] returns the order of the Pauli group on n qubits."

PauliGroupOrder::neg = "Negative integer `` is given."

PauliGroupOrder[n_Integer] := Power[4, n] /; If[ n >= 0, True, 
  Message[PauliGroupOrder::neg, n];
  False
]

PauliGroupOrder[ss:{___?QubitQ}] := PauliGroupOrder[Length @ ss]


FullPauliGroupElements::usage = "FullPauliGroupElements[n] returns a list of all elements in the Pauli group on n qubits. FullPauliGroupElements[n, {k$1,k$2,$$}] gives a list of elements numbered k$1,k$2,$$. FullPauliGroupElements[{s$1,s$2,$$,s$n},{k$1,k$2,$$}] refers to the Pauli group on n labelled qubits {s$1,s$2,$$,s$n}."

FullPauliGroupElements[spec_] :=
  FullPauliGroupElements[spec, Range @ GroupOrder @ FullPauliGroup[spec]]

FullPauliGroupElements[spec:(_Integer|{__?QubitQ}), k_Integer] :=
  First @ FullPauliGroupElements[spec, {k}]

FullPauliGroupElements[spec:(_Integer|{__?QubitQ}), kk:{__Integer}] :=
  Module[
    { gn = PauliGroupOrder[spec],
      ff = {1, -1, I, -I},
      qq, rr },
    qq = Quotient[kk-1, gn] + 1;
    rr = Mod[kk-1, gn] + 1;
    MapThread[Times, {ff[[qq]], PauliGroupElements[spec, rr]}]
  ]


PauliGroupElements::usage = "PauliGroupElements[n] returns the list of all elements in the Pauli group on n qubits.\nPauliGroupElements[n, k] returns the kth element.\nPauliGroupElements[n, {k1, k2, \[Ellipsis]}] gives a list of elements numbered k1, k2, \[Ellipsis].\nPauliGroupElements[{s1, s2, \[Ellipsis], sn}, {k1, k2, \[Ellipsis]}] refers to the Pauli group on n labelled qubits {s1, s2, \[Ellipsis], sn}."

PauliGroupElements[n_Integer] :=
  PauliGroupElements[n, Range @ GroupOrder @ PauliGroup @ n]

PauliGroupElements[n_Integer, kk:{__Integer}] :=
  Map[PauliGroupElements[n, #]&, kk]

PauliGroupElements[n_Integer?Positive, k_Integer] :=
  FromGottesmanVector[thePauliGroupElement[n, k], Pauli]


PauliGroupElements[ss:{__?QubitQ}] :=
  PauliGroupElements[ss, Range @ GroupOrder @ PauliGroup @ ss]

PauliGroupElements[ss:{__?QubitQ}, kk:{__Integer}] :=
  Map[PauliGroupElements[ss, #]&, kk]

PauliGroupElements[ss:{__?QubitQ}, k_Integer] :=
  FromGottesmanVector[thePauliGroupElement[Length @ ss, k], ss]


thePauliGroupElement[n_Integer?Positive, k_Integer] :=
  Reverse @ IntegerDigits[k-1, 2, 2*n]


(**** <PauliMatrixQ> ****)

PauliMatrixQ::usage = "PauliMatrixQ[mat] returns True if matrix mat is an element of the full Pauli group, and False otherwise."

(* NOTE: The previous method based on PauliCoefficients is slow for a large
   number of qubits, especially, 8 or more qubits. *)

PauliMatrixQ[mat_?SquareMatrixQ] := thePauliMatrixQ[mat] /; Length[mat] == 2

PauliMatrixQ[mat_?SquareMatrixQ] := Module[
  { tsr = Tensorize[mat],
    dim, kk, tt, n },
  dim = Dimensions[tsr];
  n = Length[dim] / 2;
  kk = NestList[RotateLeft[#, 2]&, Range[2*n], n-1];
  tt = Transpose[tsr, #]& /@ kk;
  tt = Map[
    Function[{x}, Flatten @ Map[thePauliMatrixQ, x, {2*(n-1)}]],
    tt
  ];
  If[ AllTrue[tt, (Length[#] == Power[2, n-1])&],
    AllTrue[Flatten @ tt, Identity],
    False
  ]
] /; IntegerPowerQ[2, Length @ mat] /; Length[mat] > 2

PauliMatrixQ[_List] = False

PauliMatrixQ[_Association] = False


thePauliMatrixQ::usage = "thePauliMatrixQ[mat] returns True if 2x2 matrix mat is one of the Pauli operators."

thePauliMatrixQ[mat_?SquareMatrixQ] := Module[
  { cc },
  cc = Chop @ {
    Tr @ mat,
    Tr @ Reverse @ mat,
    Subtract @@ Diagonal @ mat,
    Subtract @@ Diagonal @ Reverse @ mat
  };
  cc = DeleteCases[cc, 0];
  Switch[ Length[cc],
    0, Nothing,
    1, True,
    _, False
  ]
] /; Length[mat] == 2

thePauliMatrixQ[_] = False

(**** </PauliMatrixQ> ****)


(**** <PauliQ> ****)

(* NOTE: PauliQ and PauliMatrixQ may be combined to a single function. However, we keep them separate because PauliMatrixQ requires rather a large computational cost for large matrices. *)

PauliQ::usage = "PauliQ[op] returns True if operator op is an element of the full Pauli group, and False otherwise."

SetAttributes[PauliQ, Listable]


PauliQ[Pauli[{(0|1|2|3)..}]] = True


PauliQ[-1 | 1 | -I | I] = True

PauliQ[_?QubitQ[___, 0|1|2|3]] = True

PauliQ[HoldPattern @ Multiply[__?QubitQ]] = True


PauliQ[(-1|-I|I) * _?PauliQ] = True


PauliQ[expr_Plus] := PauliQ[Elaborate @ expr] /; 
  Not[FreeQ[expr, _?QubitQ[___, (4|5|6|7|8|9|10|11)] | _Pauli[___, (4|5|6|7|8|9|10|11), ____]]]

PauliQ[expr:HoldPattern[Times[__, _Plus]]] := PauliQ[Elaborate @ expr] /; 


PauliQ[_] = False

(**** </PauliQ> ****)


(**** <CliffordGroup> ****)

FullCliffordGroup::usage = "FullCliffordGroup[n] represents the full Clifford group (taking into account the global phase factors), the normalizer group of the full Pauli group, on n qubits.\nCliffordGroup[{s1, s2, ...}] represents the full Clifford group on labelled qubits {s1, s2, \[Ellipsis]}."

CliffordGroup::usage = "CliffordGroup[n] represents the Clifford group (ignoring global phase factors), the normalizer group of the Pauli group, on n qubits.\nCliffordGroup[{s1, s2, ...}] represents the Clifford group on labelled qubits {s1, s2, \[Ellipsis]}.\nCliffordGroup[n] is a quotient group FullCliffordGroup[n] / {Exp[\[ImaginaryI] m \[Pi]/4] : m=0,1,2,\[Ellipsis],7}."

FullCliffordGroup::toobig = "There are about `` elements in the group. Only the first 10 elements are returned."

CliffordGroup::toobig = "There are about `` elements in the group. Only the first 10 elements are returned."

CliffordGroup::todo = "Not supported yet."

FullCliffordGroup[S_?QubitQ] := FullCliffordGroup @ {S}

FullCliffordGroup[ss:{__?QubitQ}] := FullCliffordGroup[FlavorCap @ ss] /;
  Not[FlavorCapQ @ {ss}]

CliffordGroup[S_?QubitQ] := CliffordGroup @ {S}

CliffordGroup[ss:{__?QubitQ}] := CliffordGroup[FlavorCap @ ss] /;
  Not[FlavorCapQ @ {ss}]


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
  ss = S[Range @ n, $];
  gg = GroupGenerators[CliffordGroup @ ss];
  ExpressionFor /@ Matrix[gg, ss]
 ]

CliffordGroup /:
GroupGenerators @ CliffordGroup[qq:{__?QubitQ}] := Module[
  { ss = Through[qq @ {6, 7}],
    cn = CZ @@@ Subsets[FlavorCap @ qq, {2}] },
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

FullCliffordGroupElements[spec:(_Integer|{__?QubitQ}), k_Integer] :=
  First @ FullCliffordGroupElements[spec, {k}]

FullCliffordGroupElements[spec:(_Integer|{__?QubitQ}), kk:{__Integer}] :=
  Module[
    { gn = GroupOrder[CliffordGroup @ spec],
      ff, qq, rr, k },
    ff = Table[Exp[I k Pi/4], {k, 0, 7}];
    qq = Quotient[kk-1, gn] + 1;
    rr = Mod[kk-1, gn] + 1;
    MapThread[Times, {ff[[qq]], CliffordGroupElements[spec, rr]}]
  ]


CliffordGroupElements::usage = "CliffordGroupElements[n, {k$1,k$2,$$}] returns a list of the elements numbered k$1, k$2, $$ in the Clifford group of degree n. CliffordGroupElements[{s$1,s$2,$$,s$n}, {k$1,k$2,$$}] refers to the group on n labelled qubits {s$1,s$2,$$}."

CliffordGroupElements[spec:(_Integer|{__?QubitQ}), k_Integer] :=
  First @ CliffordGroupElements[spec, {k}]

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


(**** <CliffordMatrixQ> ****)

CliffordMatrixQ::usage = "CliffordMatrixQ[mat] returns True if matrix mat represents a Clifford operator, and False otherwise."

CliffordMatrixQ::notqbt = "Matrix `` does not represent an operator acting on qubits."


CliffordMatrixQ[mat_?MatrixQ] := (
  Message[CliffordMatrixQ::notqbt, vec];
  False
) /; Not @ AllTrue[Log[2, Dimensions @ mat], IntegerQ]

CliffordMatrixQ[mat_?MatrixQ] := Module[
  { n = Log[2, Length @ mat],
    spr = Supermap[mat],
    gnr },
  gnr = ThePauli /@ Join[
    NestList[RotateRight, PadRight[{1}, n], n-1],
    NestList[RotateRight, PadRight[{3}, n], n-1]
  ];
  AllTrue[spr /@ gnr, PauliMatrixQ]
]

(**** </CliffordMatrixQ> ****)


(**** <CliffordQ> ****)

(* NOTE: CliffordQ and CliffordMatrixQ may be combined to a single function. We separate them in consistency with PauliQ and PauliMatrixQ. *)

CliffordQ::usage = "CliffordQ[op] returns True if operator op is an element of the full Clifford group, and False otherwise."

SetAttributes[CliffordQ, Listable]


CliffordQ[expr_] := CliffordMatrixQ[Matrix @ expr]

CliffordQ[expr_, ss:{__?QubitQ}] := CliffordMatrixQ[Matrix @ expr]

(**** </CliffordQ> ****)


GottesmanVectorQ::usage = "GottesmanVectorQ[vec] returns True if vector vec is a (reduced) Gottesman vector."

GottesmanVectorQ[v_?VectorQ] := VectorQ[v, BinaryQ] && EvenQ[Length @ v]


(**** <GottesmanVector> ****)

GottesmanVector::usage = "GottesmanVector[mat] returns the Gottesman vector for the Pauli string corresponding to matrix mat.\nGottesmann[op] returns the vector in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\) corresponding to the coset represented by the Pauli operator op on n (unlabeled) qubits.\nGottesmann[op, {S1,S2,...,Sn}] returns the vector in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\) corresponding to the coset represented by the Pauli operator op on the (labeled) qubits {S1, S2, ..., Sn}."

GottesmanVector::pauli = "Matrix `` does not represent a Pauli string."

GottesmanVector[mat_?MatrixQ] := With[
  { mm = Keys[PauliCoefficients @ mat] },
  If[Length[mm] > 1, Message[GottesmanVector::pauli, mat]];
  Flatten[GottesmanDigits @ First @ mm]
] /; If[ MatrixQ[mat, NumericQ] && IntegerPowerQ[2, Length @ mat],
  True,
  Message[GottesmanVector::pauli, mat];
  False
]


GottesmanVector[op_Pauli] := Flatten[GottesmanDigits @ First @ op]

GottesmanVector[_?CommutativeQ op_] := GottesmanVector[op]


GottesmanVector[_?CommutativeQ, ss:{__?QubitQ}] :=
  Flatten @ GottesmanDigits @ ConstantArray[0, Length @ ss]

GottesmanVector[_?CommutativeQ op_, ss:{__?QubitQ}] :=
  GottesmanVector[op, ss]

GottesmanVector[op_?QubitQ, ss:{__?QubitQ}] := With[
  { qq = FlavorCap[ss] },
  GottesmanVector @ Pauli[
    qq /. {FlavorMute[op] -> FlavorLast[op]} /. Thread[qq -> 0]
   ]
]

GottesmanVector[HoldPattern @ Multiply[op__?QubitQ], ss:{__?QubitQ}] := With[
  { qq = FlavorCap[ss] },
  Flatten @ GottesmanDigits[
    qq /. Thread[FlavorMute @ {op} -> FlavorLast @ {op}] /. Thread[qq -> 0]
  ]
]


GottesmanVector[expr_, ss:{__?QubitQ}] := GottesmanVector @ Matrix[expr, ss]

GottesmanVector[expr:Except[_?MatrixQ]] := GottesmanVector[Matrix @ expr]

(**** </GottesmanVector> ****)


GottesmanDigits::usage = "GottesmanDigits[k] converts Pauli index k \[Element] {0, 1, 2, 3} into the corresponding two-bit code."

SetAttributes[GottesmanDigits, Listable]

GottesmanDigits[0] = {0, 0}

GottesmanDigits[1] = {1, 0}

GottesmanDigits[3] = {0, 1}

GottesmanDigits[2] = {1, 1}

GottesmanDigits[k_Integer] := GottesmanDigits @ Mod[k, 3]


fromGottesmanDigits::usage = "fromGottesmanDigits[{b1, b2}] converts a two-bit code {b1, b2} to the corresponding Pauli index 0, 1, 2, or 3."

fromGottesmanDigits[{0, 0}] = 0

fromGottesmanDigits[{1, 0}] = 1

fromGottesmanDigits[{0, 1}] = 3

fromGottesmanDigits[{1, 1}] = 2

fromGottesmanDigits[bb:{{_, _}...}] := Map[fromGottesmanDigits, bb]


(**** <FullGottesmanVector> ****)

FullGottesmanVector::usage = "FullGottesmanVector[spec] is similar to GottesmanVector, but returns a full Gottesman vector, i.e., a Gottesman vector with an additional sign entry at the end."

FullGottesmanVector[mat_?MatrixQ] := With[
  { mm = PauliCoefficients[mat] },
  If[Length[mm] > 1, Message[GottesmanVector::pauli, mat]];
  Append[
    Flatten[GottesmanDigits @ First @ Keys @ mm], 
    First[Values @ mm]
  ]
] /; If[ MatrixQ[mat, NumericQ] && IntegerPowerQ[2, Length @ mat],
  True,
  Message[GottesmanVector::pauli, mat];
  False
]


FullGottesmanVector[op_Pauli] := Append[GottesmanVector[op], 1]

FullGottesmanVector[z_ op_Pauli] := Append[GottesmanVector[op], z]

FullGottesmanVector[expr:Except[_?MatrixQ]] := FullGottesmanVector[Matrix @ expr]

FullGottesmanVector[expr_, ss:{__?QubitQ}] := FullGottesmanVector @ Matrix[expr, ss]

(**** </FullGottesmanVector> ****)


(**** <FromGottesmanVector> ****)

FromGottesmanVector::usage = "FromGottesmanVector[vec] returns the Pauli operator on unlabeled qubits representing the coset corresponding to the GottesmanVector vec in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\), where n is the number of (unlabeled) qubits.\nFromGottesmanVector[vec, {S1,S2,...,Sn}] returns the Pauli operator on qubits {S1,S2,...,Sn} representing the coset corresponding to the GottesmanVector vec in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\)."

(* from full Gottesman vector *)
FromGottesmanVector[vec_?VectorQ, spec___] := ( 
  FromGottesmanVector[Most @ vec, spec] * Last[vec]
) /; GottesmanVectorQ[Most @ vec]

(* from reduced Gottesman vector *)
FromGottesmanVector[vec_?VectorQ] := 
  ThePauli[fromGottesmanDigits @ Partition[vec, 2]] /; 
  GottesmanVectorQ[vec]

FromGottesmanVector[vec_?VectorQ, Pauli] := 
  Pauli[fromGottesmanDigits @ Partition[vec, 2]] /; 
  GottesmanVectorQ[vec]

FromGottesmanVector[vec_?VectorQ, ss:{__?QubitQ}] := Apply[
  Multiply,
  MapThread[Construct, {ss, fromGottesmanDigits @ Partition[vec, 2]}]
] /; GottesmanVectorQ[vec]

FromGottesmanVector[vec_?VectorQ, S_?QubitQ] :=
  FromGottesmanVector[vec, {S}]

(**** </FromGottesmanVector> ****)


(**** <RandomGottesmanVector> ****)

RandomGottesmanVector::usage = "RandomGottesmanVector[n] returns a uniformly distributed random Gottesman vector for n qubits."

RandomGottesmanVector[n_Integer] := 
  thePauliGroupElement[n, RandomInteger[{1, PauliGroupOrder @ n}]]

RandomGottesmanVector[n_Integer, k_Integer] := 
  Map[thePauliGroupElement[n, #]&, RandomInteger[{1, PauliGroupOrder @ n}, k]]


RandomFullGottesmanVector::usage = "RandomFullGottesmanVector[n] returns a uniformly distributed random full Gottesman vector for n qubits."

RandomFullGottesmanVector[n_Integer] :=
  Append[RandomGottesmanVector[n], RandomChoice[{1, -1, I, -I}]]

RandomFullGottesmanVector[n_Integer, k_Integer] :=
  Table[RandomFullGottesmanVector[n], k]

(**** </RandomGottesmanVector> ****)


GottesmanTest::usage = "GottesmanTest[a, b] returns 1 if the two operators a and b commute with each other, -1 if they anti-commute, and 0 otherwise."

GottesmanTest[a_, b_] := If[
  TrueQ[Commutator[a, b] == 0],
  1,
  If[Anticommutator[a, b] == 0, -1, 0, 0]
]


(**** <GottesmanInner> ****)

GottesmanInner::usage = "GottesmanInner[v, w] gives the symplectic inner product in the Gottesman vector space."

GottesmanInner::icmp = "Incompatible vectors `1` and `2`."

GottesmanInner[v_?VectorQ, w_?VectorQ] :=
  Mod[Dot[v, GottesmanFlip @ w], 2] /;
  ArrayQ[{v, w}, 2, BinaryQ] && EvenQ[Length @ v]

GottesmanInner[v_?VectorQ, w_?VectorQ] :=
  Mod[Dot[v, GottesmanFlip @ w], 2] /;
  If[ ArrayQ[{Most @ v, Most @ w}, 2, BinaryQ] && OddQ[Length @ v], True,
    Message[GottesmanInner::icmp, v, w]; False
  ]

(**** </GottesmanInner> ****)


GottesmanBasis::usage = "GottesmanBasis[{v1, v2, \[Ellipsis]}] returns a symplectic basis of the vector space spanned by {v1, v2, \[Ellipsis]}.\nGottesmanBasis[v] returns a symplectic basis {v, \[Ellipsis]} spanning the Gottesman vector space containing v.\nGottesmanBasis[n] returns the standard basis of the n-qubit (2n-dimensional) Gottesman vector space, which happens to be a symplectic basis with respect to GottesmanInner."
(* See: Koenig and Smolin (2021) *)

GottesmanBasis[{}] = {} (* fallback *)

GottesmanBasis[bs_?MatrixQ] := Module[
  { v = First @ bs,
    w, new },
  If[ContainsOnly[v, {0}], Return @ GottesmanBasis @ Rest @ bs];
  
  w = Select[bs, GottesmanInner[v, #]==1&];
  If[Length[w] == 0, Return[bs], w = First[w]];
  
  new = Map[
    Mod[# + w * GottesmanInner[v, #] + v * GottesmanInner[w, #], 2]&,
    DeleteCases[Rest @ bs, w]
  ];
  Join[{v, w}, GottesmanBasis @ DeleteCases[new, Table[0, Length @ v]]]
]

GottesmanBasis[v_?VectorQ] := IdentityMatrix[Length @ v] /;
  v == UnitVector[Length @ v, 1]

GottesmanBasis[v_?VectorQ] := With[
  { id = IdentityMatrix[Length @ v] },
  GottesmanBasis @ Join[{v}, id]
]

GottesmanBasis[n_Integer] := One[2*n] /; n > 0


GottesmanSplit::usage = "GottesmanSplit[vec] returns a list of two vectors {{x$1,x$2,$$,x$n},{z$1,z$2,$$,z$n}} for Gottesman vector vec={x$1,z$1,x$2,z$2,$$,x$1n,z$n}.\nGottesmanSplit[mat] returns a list of the X- and Z-part of the matrix of Gottesman vectors, mat={{x$11,z$11,x$12,z$12,$$,x$1n,z$1n},{x$21,z$21,x$22,z$22,$$,x$2n,z$2n},$$}.";

GottesmanSplit::odd = "`` is not a valid Gottesman vector (or a set of valid Gottesman vectors)."

GottesmanSplit[vec_?VectorQ] := (
  Message[GottesmanSplit::odd, vec];
  { vec[[1 ;; ;; 2]],
    vec[[2 ;; ;; 2]] }
) /; OddQ[Length @ vec]

GottesmanSplit[vec_?VectorQ] :=
  { vec[[1 ;; ;; 2]],
    vec[[2 ;; ;; 2]] }

GottesmanSplit[mat_?MatrixQ] := (
  Message[GottesmanSplit::odd, mat];
  { mat[[;;, 1 ;; ;; 2]],
    mat[[;;, 2 ;; ;; 2]] }
) /; OddQ[Last @ Dimensions @ mat]

GottesmanSplit[mat_?MatrixQ] :=
  { mat[[;;, 1 ;; ;; 2]],
    mat[[;;, 2 ;; ;; 2]] }


GottesmanMerge::usage = "GottesmanMerge[{x$1,x$2,$$,x$n}, {z$1,z$2,$$,z$n}] returns Gottesman vector {x$1,z$1,x$2,z$2,$$,x$n,z$n}.\nGottesmanMerge[xmat, zmat] returns the list of Gottesman vectors {{x$11,z$11,x$12,z$12,$$,x$1n,z$1n},{x$21,z$21,x$22,z$22,$$,x$2n,z$2n},$$} for xmat={{x$11,x$12,$$,x$1n},{x$21,x$22,$$,x$2n},$$} and zmat={{z$11,z$12,$$,z$1n},{z$21,z$22,$$,z$2n},$$}.";

GottesmanMerge::bad = "`` and `` cannot be the X- and Z-part of a valid Gottesman vector."

GottesmanMerge[xx_?VectorQ, zz_?VectorQ] := (
  Message[GottesmanMerge::bad, xx, zz];
  Riffle[xx, zz]
 ) /; Not[ArrayQ @ {xx, zz}]

GottesmanMerge[xx_?VectorQ, zz_?VectorQ] := Riffle[xx, zz]

GottesmanMerge[xx_?MatrixQ, zz_?MatrixQ] := (
  Message[GottesmanMerge::bad, xx, zz];
  MapThread[Riffle, {xx, xx}]
) /; Not[ArrayQ @ {xx, zz}]

GottesmanMerge[xx_?MatrixQ, zz_?MatrixQ] := MapThread[Riffle, {xx, zz}]


(**** <GottesmanFlip> ****)

GottesmanFlip::usage = "GottesmanFlip[vec] swaps the x-bit and z-bit of each qubit in Gottesman vector vec."

GottesmanFlip[vec_?VectorQ] := 
  Append[GottesmanFlip[Most @ vec], Last @ vec] /;
  OddQ[Length @ vec]

GottesmanFlip[vec_] := 
  Flatten[Reverse /@ Partition[vec, 2]] /;
  VectorQ[vec, BinaryQ] && EvenQ[Length @ vec]

(**** </GottesmanFlip> ****)


(**** <Stabilizer> ****)

Stabilizer::usage = "Stabilzier[state] returns the stabilizer subgroup of the Pauli group that stabilizes state, which may be a column vecotr or expressed in terms of Ket[\[Ellipsis]] or Ket[<|\[Ellipsis]|>].\nStabilizer[state, {s1,s2,\[Ellipsis]}] assumes that state belongs to the Hilbert space associated with qubits {s1,s2,\[Ellipsis]}.\nStabilizer[graph] returns the stabilizer subgroup of the Pauli group that stabilizes the graph state associated with graph.\nStabilizer[graph, vtx] returns the operator associated with vertex vtx (the so-called correlation operator on vtx) that stabilizes the graph state associated with graph."

Stabilizer::notss = "`` is not a stabilizer state."

Stabilizer[state:(_?VectorQ|_?SquareMatrixQ)] := With[
  { mm = getStabilizer[state] },
  If[ FailureQ[mm], 
    Message[Stabilizer::notss, state];
    Return @ List @ One[Length @ state]
  ];
  Map[ThePauli, Keys @ mm] * Values[mm]
] /; IntegerPowerQ[2, Length @ state]


Stabilizer[expr_] := Module[
  { mm = getStabilizer[Matrix @ expr] },
  If[ FailureQ[mm],
    Message[Stabilizer::notss, expr];
    mm = FirstCase[expr, _Pauli | _Ket, Ket[{}], Infinity];
    Return @ List @ Pauli @ Table[0, Length @ mm]
  ];
  Map[Pauli, Keys @ mm] * Values[mm]
] /; Not @ FreeQ[expr, _Pauli | Ket[_List]]


Stabilizer[expr_] := Stabilizer[expr, Qubits @ expr]

Stabilizer[expr_, ss:{__?QubitQ}] := With[
  { mm = getStabilizer @ Matrix[expr, ss] },
  If[FailureQ[mm], Message[Stabilizer::notss, expr]; Return @ {1}];
  Elaborate[ (Multiply @@@ FlavorThread[ss, Keys @ mm]) * Values[mm] ]
]


getStabilizer[vec_?VectorQ] :=
  getStabilizer @ Dyad[vec, vec]

getStabilizer[rho_?SquareMatrixQ] := Module[
  { tsr },
  tsr = PauliCoefficients[rho];
  If[Not[theSSQ @ Values @ tsr], Return @ $Failed];
  Sign /@ tsr
]


Stabilizer[g_Graph] := Stabilizer @ GraphState[g]

Stabilizer[g_Graph, ss:{__?QubitQ}] :=
  Stabilizer[GraphState[g, FlavorCap @ ss], FlavorCap @ ss]

Stabilizer[g_Graph, vtx_?QubitQ] := Module[
  { new = If[FlavorCapQ[vtx], Drop[vtx, -1], vtx],
    adj },
  adj = AdjacencyList[g, new|new[$]];
  vtx[1] ** Apply[Multiply, Through[adj[3]]]
]

(**** </Stabilizer> ****)


(**** <StabilizerGenerators> ****)

StabilizerGenerators::usage = "StabilizerGenerators[{g1, g2, \[Ellipsis]}] returns a list of independent generators of stabilizer subgroup {g1, g2, \[Ellipsis]} of the Pauli group."

StabilizerGenerators[grp_List] := Module[
  { ss = Qubits[grp],
    gg, cc
  },
  gg = GottesmanVector[#, ss]& /@ grp;
  gg = Orthogonalize[gg, Mod[Dot[#1, #2], 2]&];
  gg = DeleteCases[gg, {0..}];
  gg = FromGottesmanVector[#, ss]& /@ gg;
  cc = FirstCase[Coefficient[grp, #], Except[0]] & /@ gg;
  cc * gg
]

(**** </StabilizerGenerators> ****)


(**** <UpdateStabilizerGenerators> ****)

UpdateStabilizerGenerators::usage = "UpdateStabilizerGenerators[{g1, g2, \[Ellipsis]}, msr] returns a new list of stabilizer generators corresponding to the post-measurement state with outcome 1 (out of 1 and -1) upon the measurement of msr on the state stabilized by generators {g1, g2, \[Ellipsis]}.\nBoth generators gk and measurement operator (a Pauli string) msr are specified by full Gottesman vectors."

UpdateStabilizerGenerators[gnr_?MatrixQ, msr_?VectorQ] := Module[
  { alt = Most[msr],
    chk, new },
  chk = Map[GottesmanInner[alt, #]&, Most /@ gnr];
  chk = PositionIndex[chk];
  If[MissingQ[chk @ 1], Return @ gnr];
  new = ReplacePart[gnr, First[chk @ 1] -> msr];
  If[Length[chk @ 1] == 1, Return @ new];
  alt = gnr[[First @ chk @ 1]];
  ReplaceAt[new, v_ :> GottesmanTimes[alt, v], List /@ Rest[chk @ 1]]
]

(**** </UpdateStabilizerGenerators> ****)


(**** <GottesmanTimes> ****)

GottesmanTimes::usage = "GottesmanTimes[a, b] returns Gottesman vector c such that P(c) = P(a) ** P(b), where P(v) is the Pauli string corresponding to Gottesman vector v."

SetAttributes[GottesmanTimes, {Flat, OneIdentity}]

(* for reduced Gottesman vectors *)
GottesmanTimes[a_?VectorQ, b_?VectorQ] :=
  Mod[a + b, 2] /; ArrayQ[{a, b}, 2, BinaryQ] && EvenQ[Length @ a]

(* for full Gottesman vectors *)
GottesmanTimes[a_?VectorQ, b_?VectorQ] := Module[
  { aa = Partition[a, 2],
    bb = Partition[b, 2],
    cc, ff },
  cc = Mod[aa + bb, 2];
  ff = Map[FromDigits[#, 2]&, Transpose @ {aa, bb, cc}, {2}];
  ff = Total[Signature /@ ff];
  Append[Flatten[cc], Power[I, ff] * Last[a] * Last[b]]
] /; ArrayQ[{a, b}, 2] && OddQ[Length @ a]

(* for conjugation transformation, C[mat] ** P[vec] ** Dagger[C[mat]]  *)
GottesmanTimes[vec_?VectorQ, mat_?MatrixQ] := Module[
  { pos = PositionIndex[Normal @ Most @ vec],
    new, sig },
  If[MissingQ[pos @ 1], Return @ vec];
  new = mat[[pos @ 1]];
  new = Fold[GottesmanTimes, Normal @ new];
  (* NOTE: The following line is surprisingly slow; hence, the above line instead. *)
  (* new = GottesmanTimes @@ new; *)
  sig = Last[vec] * Power[I, Count[Partition[vec, 2], {1, 1}]];
  ReplaceAt[new, v_ :> v * sig, -1]
]

(**** </GottesmanTimes> ****)


(**** <StabilizerState> ****)

StabilizerStateQ::usage = "StabilizerStateQ[state] returns True if state is a (pure or mixed) stabilizer state, a state that can be stabilized by a non-trivial subgroup of the Pauli group; and False otherwise. The state may be a column vector, square matrix, or expressed in terms of Ket[\[Ellipsis]], Ket[<|\[Ellipsis]|>], Pauli[{\[Ellipsis]}], or (labelled) qubit operators."

StabilizerStateQ::notqbt = "`` is not a state vector for qubits."

StabilizerStateQ[any:(_?VectorQ|_?SquareMatrixQ)] := (
  Message[StabilizerStateQ::notqbt, any];
  False
) /; Not @ IntegerPowerQ[2, Length @ any]

StabilizerStateQ[vec_?VectorQ] :=
  StabilizerStateQ @ Dyad[vec, vec]

StabilizerStateQ[mat_?SquareMatrixQ] :=
  theSSQ[Values @ PauliCoefficients @ mat]

theSSQ[val_?VectorQ] := TrueQ @ And[
  NoneTrue[val, MatchQ[#, _Complex]&],
  Equal @@ Abs[val]
]


StabilizerStateQ[expr_] := StabilizerStateQ[Matrix @ expr]

StabilizerStateQ[expr_, ss:{__?QubitQ}] := StabilizerStateQ[Matrix @ expr]


StabilizerStateCount::usage = "StabilizerStateCount[n] returns the number of (pure) stabilizer states on an n-qubit system.\nStabilizerStateCount[{s1,s2,\[Ellipsis],sn}] is equivalent to StabilizerStateCount[n] for qubits s1, s2, \[Ellipsis], sn."
(* See: Aaronson and Gottesman (2004). *)

StabilizerStateCount[n_Integer] :=
  Power[2, n] * Product[Power[2, k] + 1, {k, n}]

StabilizerStateCount[ss:{___?QubitQ}] :=
  StabilizerStateCount[Length @ ss]

(**** </StabilizerState> ****)


(**** <GottesmanGroup> ****)

GottesmanGroup::usage = "GottesmanGroup is an alias for BinarySymplecticGroup."

GottesmanGroupOrder::usage = "GottesmanGroupOrder is an alias for BinarySymplecticGroupOrder."

GottesmanGroupElements::usage = "GottesmanGroupElements is an alias for BinarySymplecticGroupElements."

(**** </GottesmanGroup> ****)


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

BinarySymplecticGroupElements[ss:{__?QubitQ}, kk:(_Integer|{__Integer})] :=
  getSpElement[Length @ ss, kk]

BinarySymplecticGroupElements[n_Integer?Positive, kk:(_Integer|{__Integer})] :=
  getSpElement[n, kk]

BinarySymplecticGroupElements[n_, kk:{__Integer}] :=
  (Message[BinarySymplecticGroup::degree, n]; {})

(**** </BinarySymplecticGroup> ****)


(**** <Koenig-Smolin Algorihm for BinarySymplecticGroup> ****)

getSpElement::usage = "getSpElement[n, k] returns the k'th symplectic matrix in BinarySymplecticGroup[n]."

SetAttributes[getSpElement, Listable];

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

FindGottesmanShears[x_?VectorQ, y_?VectorQ] := Zero[{2, Length @ x}] /; x == y

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

(** Full vs reduced Gottesman matrix 
  - A reduced Gottesman matrix is a 2n x 2n matrix.
  - A full Gottesman matrix has an extra row of 2n parity bits.
  *)

(**** <GottesmanMatrixQ> ****)

GottesmanMatrixQ::usage = "GottesmanMatrixQ[mat] returns True if matrix mat is a (reduced) Gottesman matrix, which is symplectic with respect to the Gottesman inner prodcut."

GottesmanMatrixQ[mat_?SquareMatrixQ] := Module[
  { n = Length[mat],
    x },
  x = CircleTimes[One[n/2], ThePauli[1]];
  ArrayZeroQ[Mod[mat . x . Transpose[mat], 2] - x]
] /; MatrixQ[mat, BinaryQ] && EvenQ[Length @ mat]

GottesmanMatrixQ[_] = False

(**** </GottesmanMatrixQ> ****)


(**** <GottesmanMatrix> ****)

GottesmanMatrix::usage = "GottesmanMatrix[mat] returns the binary symplectic matrix corresponding to the Clifford operator represented with matrix representation mat.\nGottesmanMatrix[op, {s$1,s$2,$$}] returns the binary symplectic matrix corresponding to Clifford operator op."

GottesmanMatrix::dim = "`` has wrong dimensions and is not a valid matrix representation of a Clifford operator."

GottesmanMatrix[mat_?MatrixQ] := Module[
  { n = Log[2, First @ Dimensions @ mat],
    xz },
  If[ Not @ IntegerQ[n],
    Message[GottesmanMatrix::dim, MatrixForm @ mat];
    Return[{{}}]
  ];
  xz = ThePauli /@ Riffle[
    NestList[RotateRight, PadRight[{1}, n], n-1],
    NestList[RotateRight, PadRight[{3}, n], n-1]
  ];
  GottesmanVector /@ Supermap[mat] /@ xz
]


GottesmanMatrix[expr:Except[_?MatrixQ]] := GottesmanMatrix[Matrix @ expr]

GottesmanMatrix[expr_, ss:{__?QubitQ}] := GottesmanMatrix @ Matrix[expr, ss]

GottesmanMatrix[expr_, S_?QubitQ] := GottesmanMatrix @ Matrix[expr, S @ {$}]

(**** </GottesmanMatrix> ****)


(**** <FullGottesmanMatrix> ****)

FullGottesmanMatrix::usage = "FullGottesmanMatrix[spec] is similar to GottesmanMatrix, but returns a full Gottesman matrix, i.e., a GottesmanMatrix with an additional row of sign entries at the end."

FullGottesmanMatrix::dim = GottesmanMatrix::dim

FullGottesmanMatrix[mat_?SquareMatrixQ] := Module[
  { n = Log[2, Length @ mat],
    xz },
  If[ Not @ IntegerQ[n],
    Message[FullGottesmanMatrix::dim, MatrixForm @ mat];
    Return[{{}}]
  ];
  xz = ThePauli /@ Riffle[
    NestList[RotateRight, PadRight[{1}, n], n-1],
    NestList[RotateRight, PadRight[{3}, n], n-1]
  ];
  FullGottesmanVector /@ Supermap[mat] /@ xz
] /; MatrixQ[mat, NumericQ]


FullGottesmanMatrix[expr:Except[_?MatrixQ]] := FullGottesmanMatrix[Matrix @ expr]

FullGottesmanMatrix[expr_, ss:{__?QubitQ}] := FullGottesmanMatrix @ Matrix[expr, ss]

FullGottesmanMatrix[expr_, S_?QubitQ] := FullGottesmanMatrix @ Matrix[expr, S @ {$}]

(**** </FullGottesmanMatrix> ****)


(**** <FromGottesmanMatrix> ****)

FromGottesmanMatrix::usage = "FromGottesmanMatrix[mat, {s$1,s$2,$$}] returns the Clifford operator corresponding to Gottesman matrix mat."

(* from reduced Gottesman matrix *)
FromGottesmanMatrix[gm_?GottesmanMatrixQ] := 
  Apply[Dot, Matrix[Flatten @ vdBergFactor @ gm, Length[gm]/2]]

(* from full Gottesman matrix *)
FromGottesmanMatrix[gm_?MatrixQ] := Module[
  { mat = FromGottesmanMatrix[Transpose @ Most @ Transpose @ gm],
    fac },
  fac = Last[Transpose @ gm] * Last[Transpose @ FullGottesmanMatrix @ mat];
  mat . FromGottesmanVector[GottesmanFlip @ ParityBoole @ fac]
] /; GottesmanMatrixQ[Most @ Transpose @ gm]


FromGottesmanMatrix[gm_?MatrixQ, ss:{__?QubitQ}] :=
  Elaborate @ ExpressionFor[FromGottesmanMatrix @ gm, ss]

FromGottesmanMatrix[gm_?MatrixQ, Pauli|_Integer] :=
  Elaborate @ ExpressionFor[FromGottesmanMatrix @ gm]
(* NOTE: _integer is for CliffordGroupElements *)

(**** </FromGottesmanMatrix> ****)


GottesmanInverse::usage = "GottesmanInverse[mat] returns the inverse of binary symplectic matrix mat (with respect to the Gottesman inner product)."

GottesmanInverse[mat_] := Module[
  { n = Length[mat] / 2,
    JX },
  JX = CircleTimes[One[n], ThePauli[1]];
  Mod[JX . Transpose[mat] . JX, 2]
]


RandomGottesmanMatrix::usage = "RandomGottesmanMatrix[n] randomly generates a 2n\[Times]2n Gottesman matrix."

RandomGottesmanMatrix[n_Integer] :=
  GottesmanGroupElements[n, RandomInteger[{1, GottesmanGroupOrder @ n}]]

RandomGottesmanMatrix[ss:{__?QubitQ}] :=
  RandomGottesmanMatrix[Length @ ss]


RandomFullGottesmanMatrix::usage = "RandomFullGottesmanMatrix[n] randomly generates a 2n\[Times](2n+1) full Gottesman matrix."

RandomFullGottesmanMatrix[n_Integer] :=
  Transpose @ Append[RandomGottesmanMatrix @ n, RandomChoice[{1, -1}, 2n]]

RandomFullGottesmanMatrix[ss:{__?QubitQ}] :=
  RandomFullGottesmanMatrix[Length @ ss]


(**** <GottesmanSolve> ****)

GottesmanSolve::usage = "GottesmanSolve[mat, vec] returns a solution x to a system of binary linear equations mat\[CenterDot]x==vec, where mat is a matrix consisting of rows of Gottesman vectors and vec is a vector."

GottesmanSolve::incmp = "Matrix `` and vector `` are incompatible to form a system of linear equations mat\[CenterDot]x==vec."

GottesmanSolve::odd = "`` is not a valid matrix consisting of rows of Gottesman vectors."

GottesmanSolve[mat_?MatrixQ, vec_?VectorQ] := (
  Message[GottesmanSolve::incmp, mat, vec];
  Return @ Normal @ Zero[Last @ Dimensions @ mat]
) /; Length[mat] != Length[vec]

GottesmanSolve[mat_?MatrixQ, vec_?VectorQ] := (
  Message[GottesmanSolve::odd, mat, vec];
  Return @ Normal @ Zero[Last @ Dimensions @ mat]
) /; OddQ[Last @ Dimensions @ mat]

GottesmanSolve[mat_?MatrixQ, vec_?VectorQ] :=
  LinearSolve[mat, vec, Modulus -> 2]

(**** </GottesmanSolve> ***)


(**** <GottesmanStandard> ****)

GottesmanStandard::usage = "GottesmanStandard[mat] converts mat consisting of rows of Gottesman vectors into the standard form and returns {xmat, zmat, perm}, a list of the X- and Z-part of the resulting matrix in the standard form and perm specifying the permutation of columns."

GottesmanStandard::odd = "`` has an odd number of columns and is not a matrix consisting of rows of valid Gottesman vectors. A column of zeros is padded."

GottesmanStandard::incmp =  "Incompatible dimenions in matrix `` and vector ``.";

GottesmanStandard[mat_?MatrixQ] := (
  Message[GottesmanStandard::odd, mat];
  GottesmanStandard @ ArrayPad[mat, {{0, 0}, {0, 1}}]
 ) /; OddQ[Last @ Dimensions @ mat]

GottesmanStandard[mat_?MatrixQ] := Module[
  {xx, zz, vv, cc},
  {xx, zz, vv, cc} = GottesmanStandard[mat, Zero[{Length @ mat, 1}]];
  {xx, zz, cc}
]

GottesmanStandard[mat_?MatrixQ, vec_?VectorQ] := (
  Message[GottesmanStandard::incmp, mat, vec];
  GottesmanStandard[mat, Zero[Length @ mat]]
 ) /; Length[mat] != Length[vec]

GottesmanStandard[mat_?MatrixQ, vec_?VectorQ] := Module[
  {xx, zz, vv, cc},
  {xx, zz, vv, cc} = GottesmanStandard[mat, Transpose @ {vec}];
  {xx, zz, Flatten @ vv, cc}
]

GottesmanStandard[mat_?MatrixQ, off_?MatrixQ] := (
  Message[GottesmanStandard::incmp, mat, off];
  GottesmanStandard[mat, Zero[{Length @ mat, 1}]]
) /; Length[mat] != Length[off]

GottesmanStandard[mat_?MatrixQ, off_?MatrixQ] := Module[
  { vv = off,
    xx, zz, rx, rz,
    cx, cz, new, m, n },
  {xx, zz} = GottesmanSplit[mat];
  {m, n} = Dimensions[xx];

  (* Gaussian elimitation of the X-part *)

  new = RowReduce[ArrayFlatten @ {{xx, zz, vv}}, Modulus->2];
  xx = new[[;;, ;;n]];
  zz = new[[;;, n+1;;2n]];
  vv = new[[;;, 2n+1;;]];
  
  rx = MatrixRank[xx, Modulus->2];
  cx = columnPivoting[xx, 0, Range @ rx];
  
  xx = Transpose @ Permute[Transpose @ xx, cx];
  zz = Transpose @ Permute[Transpose @ zz, cx];
  
  If[rx == m, Return @ {xx, zz, vv, cx}];

  (* Gaussian elimitation of the Z-part *)

  new = RotateLeft[#, n+rx]& /@ ArrayFlatten @ {{xx, zz, vv}};
  new = Join[ new[[;;rx]], RowReduce[new[[rx+1;;]], Modulus->2] ];
  new = RotateRight[#, n+rx]& /@ new;
  xx = new[[;;, ;;n]];
  zz = new[[;;, n+1;;2n]];
  vv = new[[;;, 2n+1;;]];

  rz = MatrixRank[zz[[rx+1;;, rx+1;;]], Modulus->2];
  cz = columnPivoting[zz, rx, Range @ rz];
    
  xx = Transpose @ Permute[Transpose @ xx, cz];
  zz = Transpose @ Permute[Transpose @ zz, cz];
  
  Return @ {xx, zz, vv, PermutationProduct[cx, cz]}
]


columnPivoting::usage = "columnPivoting[mat] performs the partial pivoting of columns of matrix mat which is assumed to be in the reduced row echelon form."

columnPivoting::echelon = "Matrix `` is not in the reduced row echelon form."

columnPivoting[mat_?MatrixQ, off_Integer, kk:{__Integer}] :=
  PermutationProduct @@ Map[columnPivoting[mat, off, #]&, kk]

columnPivoting[mat_?MatrixQ, off_Integer, k_Integer] := Module[
  { pos = FirstPosition[mat[[off+k, off+1;;]], 1],
    cyc = Cycles @ {{}} },
  If[MissingQ[pos], Return @ cyc, pos = First @ pos];

  Which[
    pos < k, Message[columnPivoting::echelon, mat]; Return @ cyc,
    pos == k, Return @ cyc
   ];
  
  Cycles @ {{off + k, off + pos}}
]

(**** </GottesmanStandard> ****)


(**** <CliffordFactor> ****)

CliffordFactor::usage = "CliffordFactor[op] returns a list of generators of the Clifford group that combine to yield Clifford operator op.\nCliffordFactor[mat,{s1,s2,\[Ellipsis]}] decomposes the Clifford operator corresponding to Gottesman matrix mat."
(* NOTE: Since v3.5.11, CliffordFactor is based on the method in van den Berg (2021) through the vdBergFactor function. Previously, it was based on Gottesman's theorem, implemented through the GottesmanFactor function.  *)

Options[CliffordFactor] = {"Strict" -> False}

CliffordFactor[mat_?MatrixQ, ss:{___?QubitQ}, OptionsPattern[]] :=
  If[ OptionValue["Strict"],
    CliffordFactor[Transpose @ SparseArray @ Append[Transpose @ mat, Table[1, Length @ mat]], ss],
    PauliMutate[vdBergFactor @ mat, ss]
  ] /; GottesmanMatrixQ[mat]

CliffordFactor[mat_?MatrixQ, ss:{___?QubitQ}, ___?OptionQ] := Module[
  { gg = vdBergFactor[Transpose @ Most @ Transpose @ mat],
    ff = Last @ Transpose @ mat,
    mm },
  mm = Dot @@ Matrix[Flatten @ gg, Length @ ss];
  ff *= Last @ Transpose @ FullGottesmanMatrix[mm];
  Append[
    PauliMutate[gg, ss],
    FromGottesmanVector[GottesmanFlip @ ParityBoole @ ff, ss]
  ]
] /; GottesmanMatrixQ[Most @ Transpose @ mat]


CliffordFactor[op:Except[_?MatrixQ]] := Module[
  { ss = Qubits @ op,
    mat },
  mat = GottesmanMatrix[op, ss];
  CliffordFactor[mat, ss]
]

(**** </CliffordFactor> ****)


(**** <vdBergFactor> ****)

vdBergFactor::usage = "vdBergFactor[mat] returns a list of elementary Clifford operators that generates the Clifford unitary operator corresponding to Gottesman matrix mat.\nThis code is the base of CliffordFactor and FromGottesmanMatrix."
(* SEE: van den Berg (2021) *)
(* NOTE: Since v3.5.11, CliffordFactor and FromGottesmanMatrix are based on vdBergFactor, which replaces GottesmanFactor. Compared with GottesmanFactor, vdBergFactor is faster and the generated set of gates are completely elementary. Moreover, it is easier to trace the change of signs along the transformation of Pauli strings. *)

vdBergFactor[mat_?MatrixQ] := Switch[ Normal @ mat,
  {{0, 1}, {1, 0}}, {Pauli[{6}]},
  {{1, 1}, {0, 1}}, {Pauli[{7}]},
  {{0, 1}, {1, 1}}, {Pauli[{7}], Pauli[{6}]},
  {{1, 0}, {1, 1}}, {Pauli[{6}], Pauli[{7}], Pauli[{6}]},
  {{1, 1}, {1, 0}}, {Pauli[{6}], Pauli[{7}]},
  _, {Pauli[{0}]}
] /; Length[mat] == 2

vdBergFactor[mat_?MatrixQ] := Module[
  { n = Length[mat] / 2,
    new = mat,
    ops = {},
    hdm, hh, gg },
  hh = Pauli @ PadRight[{6}, n];
  hdm = theGttsMatrix[hh];
  (* the 1st row *)
  gg = nullPartZ[new[[1]]];
  AppendTo[ops, gg];
  new = Mod[new . theGttsMatrix[gg], 2];
  gg = nullPartX[new[[1]]];
  ops = Join[ops, gg];
  new = Mod[new . theGttsMatrix[gg, n], 2];
  (* exchange the X and Z bits of the first qubit *)
  AppendTo[ops, hh];
  new = new . hdm;
  (* the 2nd row *)
  gg = nullPartZ[new[[2]]];
  AppendTo[ops, gg];
  new = Mod[new . theGttsMatrix[gg], 2];
  gg = nullPartX[new[[2]]];
  ops = Join[ops, gg];
  new = Mod[new . theGttsMatrix[gg, n], 2];
  (* exchange back the X and Z bits of the first qubit *)
  AppendTo[ops, hh];
  new = new . hdm;
  (* go to the next block *)
  Join[ 
    ops, 
    vdBergFactor @ new[[3;;, 3;;]] /. {
      CNOT[i_, j_] :> CNOT[i+1, j+1],
      SWAP[i_, j_] :> SWAP[i+1, j+1],
      Pauli[v_] :> Pauli[PadLeft[v, n]]
    }
  ] /. Pauli[{0..}] -> Nothing
] /; Length[mat] > 2


nullPartZ::usage = "nullPartZ[vec] returns a list of elementary single-qubit Clifford gates that get every entry of the Z-part of Gottesman vector vec to be zero."

nullPartZ[vec_?VectorQ] := Pauli @ Replace[
  Partition[Normal @ vec, 2],
  { {0, 1} -> 6,
    {1, 1} -> 7,
    {_, _} -> 0
  },
  1
]


nullPartX::usage = "nullPartX[vec] returns a list of elementary two-qubit Clifford gates that get all but the first entry of the X-part of Gottesman vector vec to be zero."

nullPartX[vec_?VectorQ] := buildCX @ Flatten @ Position[Normal @ vec[[1;; ;;2]], 1]


buildCX::usage = "buildCX[{k1, k2, ...}] is the behind-the-scene workhorse for nullPartX.\nGiven the list of qubits {k1, k2, ...} that have non-zero X-entries of the Gottesman vector of concern, it returns a list of CNOT gates that get all but one entry to be zero, if necessary, including an additional element of SWAP gate to get the remaining entry to be assigned with the first qubit."

buildCX[pp:{_, __}] := With[
  { qq = Partition[pp, 2] },
  Join[CNOT @@@ qq, buildCX @ Complement[pp, Last @ Transpose @ qq]]
]

buildCX[{k_}] = List @ If[k == 1, Nothing, SWAP[1, k]]


theGttsMatrix::usage = "theGttsMatrix[spec] returns the Gottesman matrix of the elementary Clifford gate spec among the Identity, Hadamard, quadrant-phase, CNOT, and SWAP gates."

theGttsMatrix @ Pauli[mm_?VectorQ] := CirclePlus @@ Map[theGttsMatrix, mm]

theGttsMatrix[ops_List, n_Integer] := Dot @@ Map[theGttsMatrix[#, n]&, ops]


(* for Idenity, Hadarmard or Quadrant *)
theGttsMatrix[0] := ThePauli[0]

theGttsMatrix[6] := ThePauli[1]

theGttsMatrix[7] := SparseArray @ {{1, 1}, {0, 1}}


(* for CNOT *)
theGttsMatrix[CNOT[i_, j_], n_Integer] := One[2n] + SparseArray[
  { {2i-1, 2j-1} -> 1,
    {2j, 2i} -> 1
  },
  {2n, 2n}
]

(* for SWAP *)
theGttsMatrix[SWAP[i_, j_], n_Integer] := CircleTimes[
  PermutationMatrix[Cycles @ {{i, j}}, n],
  ThePauli[0]
]

(**** </vdBergFactor> ****)


(**** <GottesmanFactor> ****)

GottesmanFactor::usage = "GottesmanFactor[op] returns a list of generators of the Clifford group that combine to yield Clifford operator op.\nGottesmanFactor[mat,{s1,s2,\[Ellipsis]}] decomposes the Clifford operator corresponding to Gottesman matrix mat."
(* SEE ALSO: Gottesman (1998), QuantumWorkbook (2022, Section 6.3.4). *)
(* NOTE: Before v3.5.11, CliffordFactor was based on GottesmanFactor. Compared with vdBergFactor, GottesmanFactor provides a more compact set of gates, but the gates are of a bit higher level. *)

GottesmanFactor::badmat = "`` is not a valid binary symplectic matrix."

GottesmanFactor[op_] := Module[
  { ss = Qubits @ op,
    mat },
  mat = GottesmanMatrix[op, ss];
  GottesmanFactor[mat, ss]
]

GottesmanFactor[mat_?GottesmanMatrixQ, ss:{_?QubitQ}] :=
  { FromGottesmanMatrix[mat, ss] }

GottesmanFactor[mat_?MatrixQ, ss:{_?QubitQ, __?QubitQ}] := Module[
  { n = Length @ ss,
    kk, qq, rr,
    ff, hh, aa, bb, vv,
    opf, oph, opa, opb, opv, cyc, new },

  ff = Transpose[Partition[#, 2]& /@ Take[mat, 2]];
  kk = FirstPosition[GottesmanInner @@@ ff, 1];
  
  If[ MissingQ[kk], 
    Message[GottesmanFactor::badmat, MatrixForm @ mat];
    Return @ {1}
  ];

  If[ (kk = First[kk]) != 1,
    cyc = CircleTimes[
      PermutationMatrix[Cycles @ {{1, kk}}, n],
      One[2]
     ];
    new = Mod[mat . cyc, 2];
    opf = SWAP @@ Part[ss, {1, kk}];
    Return @ Join[{opf}, GottesmanFactor[new, ss]]
  ];

  {qq, rr} = TakeDrop[ss, 1];
  
  ff = First @ ff;
  ff = Mod[GottesmanInverse[ff] . ThePauli[1], 2];

  opf = Dagger @ FromGottesmanMatrix[ff, qq];

  new = CirclePlus[ff, One[2*(n-1)]];
  new = Mod[mat . new, 2];

  aa = FromGottesmanVector[new[[2, 3;;]], rr];
  bb = FromGottesmanVector[new[[1, 3;;]], rr];
  aa = GottesmanMatrix[opa = ControlledGate[qq, aa], ss];
  bb = GottesmanMatrix[opb = ControlledGate[qq, bb], ss];
  hh = GottesmanMatrix[oph = First[qq][6], ss];

  vv = Mod[new . aa . hh . bb, 2];
  vv = vv[[3;;, 3;;]];

  simplifyGate @ Join[{opf, opa, oph, opb}, GottesmanFactor[vv, rr]]
]


simplifyGate::usage = "simplifyGate[expr] translates expr to a simpler elementary gate."

SetAttributes[simplifyGate, Listable]

simplifyGate[1] = Nothing

simplifyGate[any_] = any

simplifyGate @ ControlledGate[cc_, T_[j___, 1]] := CNOT[cc, T[j, $]]

simplifyGate @ ControlledGate[cc_, T_[j___, 3]] :=
  CZ[Keys @ cc, T[j, $]] /; ContainsOnly[Values[cc], {1}]

simplifyGate[S_[j___, 1]/Sqrt[2] + S_[j___, 3]/Sqrt[2]] := S[j, 6]

simplifyGate[(S_[j___, 1] + S_[j___, 3])/Sqrt[2]] := S[j, 6]

(**** </GottesmanFactor> ****)


(**** <PauliMutate> ****)

PauliMutate::usage = "PauliMutate ..."

PauliMutate[op_Pauli, ss:{__?QubitQ}] := Module[
  { new = FlavorThread[ss, First @ op] /. _?QubitQ[___, 0] -> Nothing },
  If[ Length[new] == 0, 1, new]
]


PauliMutate[op_CNOT, ss:{__?QubitQ}] = op (* fallback *)

PauliMutate[CNOT[c_Integer, t_Integer], ss:{__?QubitQ}] := With[
  { qq = FlavorCap[ss] },
  CNOT[qq[[c]], qq[[t]]]
]

PauliMutate[op_SWAP, ss:{__?QubitQ}] = op (* fallback *)

PauliMutate[SWAP[c_Integer, t_Integer], ss:{__?QubitQ}] := With[
  { qq = FlavorCap[ss] },
  SWAP[qq[[c]], qq[[t]]]
]

PauliMutate[expr_, ss:{__?QubitQ}] := ReplaceAll[
  expr,
  { op_Pauli :> PauliMutate[op, ss],
    op_CNOT :> PauliMutate[op, ss],
    op_SWAP :> PauliMutate[op, ss]
  }
]

(**** </PauliMutate> ****)


End[]

EndPackage[]
