(* stabilizer formalism *)
BeginPackage["Q3`"]

{ GottesmanVector, FromGottesmanVector,
  GottesmanTest, GottesmanInner, GottesmanBasis,
  GottesmanSplit, GottesmanMerge };

{ GottesmanMatrix, FromGottesmanMatrix, GottesmanInverse,
  GottesmanMatrixQ };

{ GottesmanStandard, GottesmanSolve };

{ CliffordDecompose = CliffordFactor };

{ Stabilizer, StabilizerGenerators };

{ StabilizerStateQ, StabilizerStateCount };

{ GottesmanGroup = BinarySymplecticGroup,
  GottesmanGroupElements = BinarySymplecticGroupElements };

Begin["`Private`"]

(**** <PauliGroup> ****)

FullPauliGroup::usage = "FullPauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators, on n qubits.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup::usage = "PauliGroup[n] represents the Pauli group, the of group of tensor products of the Pauli operators up to global phase factors, on n qubits. It is a factor group FullPauliGroup[n]/{Exp[\[ImaginaryI] m\[Pi]/2]:m=0,1,2,3}.\nPauliGroup[{s1, s2, ...}] represents the Pauli group on the labelled qubits {s1, s2, \[Ellipsis]}."

PauliGroup::todo = "Not supported yet."

FullPauliGroup[S_?QubitQ] := FullPauliGroup @ {S}

FullPauliGroup[ss:{__?QubitQ}] := FullPauliGroup[FlavorNone @ ss] /;
  Not[FlavorNoneQ @ {ss}]

PauliGroup[S_?QubitQ] := PauliGroup @ {S}

PauliGroup[ss:{__?QubitQ}] := PauliGroup[FlavorNone @ ss] /;
  Not[FlavorNoneQ @ {ss}]


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


(**** <PauliMatrixQ> ****)

PauliMatrixQ::usage = "PauliMatrixQ[mat] returns True if matrix mat is an element of the full Pauli group, and False otherwise."

(* NOTE: The previous method based on PauliDecompose is slow for a large
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
] /; IntegerQ @ Log[2, Length @ mat] /; Length[mat] > 2

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

FullCliffordGroup[ss:{__?QubitQ}] := FullCliffordGroup[FlavorNone @ ss] /;
  Not[FlavorNoneQ @ {ss}]

CliffordGroup[S_?QubitQ] := CliffordGroup @ {S}

CliffordGroup[ss:{__?QubitQ}] := CliffordGroup[FlavorNone @ ss] /;
  Not[FlavorNoneQ @ {ss}]


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


(**** <GottesmanVector> ****)

GottesmanVector::usage = "GottesmanVector[mat] returns the Gottesman vector for the Pauli operator with matrix representation mat.\nGottesmann[op] returns the vector in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\) corresponding to the coset represented by the Pauli operator op on n (unlabeled) qubits.\nGottesmann[op, {S1,S2,...,Sn}] returns the vector in \!\(\*SubsuperscriptBox[\[DoubleStruckCapitalZ],\"2\",\"2n\"]\) corresponding to the coset represented by the Pauli operator op on the (labeled) qubits {S1, S2, ..., Sn}."

GottesmanVector[mat_?MatrixQ] :=
  GottesmanVector[Elaborate @ ExpressionFor @ mat]

GottesmanVector[op_Pauli] := Flatten @ ReplaceAll[
  List @@ op,
  { 0 -> {0, 0},
    1 -> {1, 0},
    2 -> {1, 1},
    3 -> {0, 1} }
 ]

GottesmanVector[_?CommutativeQ op_] := GottesmanVector[op]

GottesmanVector[_?CommutativeQ, ss:{__?QubitQ}] :=
  GottesmanVector[Pauli @ ConstantArray[0, Length @ ss]]

GottesmanVector[_?CommutativeQ op_, ss:{__?QubitQ}] :=
  GottesmanVector[op, ss]

GottesmanVector[op_?QubitQ, ss:{__?QubitQ}] := With[
  { qq = FlavorNone[ss] },
  GottesmanVector @ Pauli[
    qq /. {FlavorMute[op] -> FlavorLast[op]} /. Thread[qq -> 0]
   ]
 ]

HoldPattern @
  GottesmanVector[Multiply[op__?QubitQ], ss:{__?QubitQ}] := With[
    { qq = FlavorNone[ss] },
    GottesmanVector @ Pauli[
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

FromGottesmanVector[vec:{(0|1)..}] := Pauli @ ReplaceAll[
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
 ) /; OddQ[Length@vec]

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

(**** </GottesmanVector> ****)


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
] /; IntegerQ @ Log[2, Length @ state]


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
  tsr = PauliDecompose[rho];
  If[Not[theSSQ @ Values @ tsr], Return @ $Failed];
  Sign /@ tsr
]


Stabilizer[g_Graph] := Stabilizer @ GraphState[g]

Stabilizer[g_Graph, ss:{__?QubitQ}] :=
  Stabilizer[GraphState[g, FlavorNone @ ss], FlavorNone @ ss]

Stabilizer[g_Graph, vtx_?QubitQ] := Module[
  { new = If[FlavorNoneQ[vtx], Drop[vtx, -1], vtx],
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


(**** <StabilizerState> ****)

StabilizerStateQ::usage = "StabilizerStateQ[state] returns True if state is a (pure or mixed) stabilizer state, a state that can be stabilized by a non-trivial subgroup of the Pauli group; and False otherwise. The state may be a column vector, square matrix, or expressed in terms of Ket[\[Ellipsis]], Ket[<|\[Ellipsis]|>], Pauli[{\[Ellipsis]}], or (labelled) qubit operators."

StabilizerStateQ::notqbt = "`` is not a state vector for qubits."

StabilizerStateQ[any:(_?VectorQ|_?SquareMatrixQ)] := (
  Message[StabilizerStateQ::notqbt, any];
  False
) /; Not @ IntegerQ @ Log[2, Length @ any]

StabilizerStateQ[vec_?VectorQ] :=
  StabilizerStateQ @ Dyad[vec, vec]

StabilizerStateQ[mat_?SquareMatrixQ] :=
  theSSQ[Values @ PauliDecompose @ mat]

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

BinarySymplecticGroupElements[ss:{__?QubitQ}, kk:{__Integer}] :=
  getSpElement[Length @ ss, kk]

BinarySymplecticGroupElements[n_Integer?Positive, kk:{__Integer}] :=
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


(**** <GottesmanMatrix> ****)

GottesmanMatrixQ::usage = "GottesmanMatrixQ[mat] returns True if 2n\[Times]2n matrix mat is symplectic with respect to the Gottesman inner product."

GottesmanMatrixQ[mat_?MatrixQ] := False /;
  OddQ @ Length[mat]

GottesmanMatrixQ[mat_?MatrixQ] := Module[
  { n = Length[mat] / 2,
    Jx },
  Jx = CircleTimes[One[n], ThePauli[1]];
  TrueQ[Mod[mat . Jx . Transpose[mat], 2] == Jx]
 ]


GottesmanMatrix::usage = "GottesmanMatrix[mat] returns the binary symplectic matrix corresponding to the Clifford operator represented with matrix representation mat.\nGottesmanMatrix[op, {s$1,s$2,$$}] returns the binary symplectic matrix corresponding to Clifford operator op."

GottesmanMatrix::dim = "`` has wrong dimensions and is not a valid matrix representation of a Clifford operator."

GottesmanMatrix[op_, S_?QubitQ] := GottesmanMatrix[op, {FlavorNone @ S}]

GottesmanMatrix[op_, ss:{__?QubitQ}] := Module[
  { n = Length @ ss,
    xz },
  xz = Flatten @ Through[ss @ {1, 3}];
  GottesmanVector[#, ss]& /@ Elaborate[Supermap[op] /@ xz]
 ]
(* NOTE: Often, GottesmanMatrix[Matrix[op, ss]] is faster. But there are cases
   where this form is faster, and hence we keep this form. *)

GottesmanMatrix[op_] := Module[
  { n, xz },
  n  = FirstCase[{op}, Pauli[k_] :> Length[k], Missing[], Infinity];
  xz = Pauli /@ Riffle[
    NestList[RotateRight, PadRight[{1}, n], n-1],
    NestList[RotateRight, PadRight[{3}, n], n-1]
   ];
  GottesmanVector /@ Elaborate[Supermap[op] /@ xz]
 ] /; Not @ FreeQ[op, _Pauli]
(* NOTE: Often, GottesmanMatrix[Matrix[op]] is faster. But there are cases
   where this form is faster, and hence we keep this form. *)

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


FromGottesmanMatrix::usage = "FromGottesmanMatrix[mat, {s$1,s$2,$$}] returns the Clifford operator corresponding to binary symplectic matrix mat."

FromGottesmanMatrix::spmat = "`` is not a valid binary symplectic matrix."

FromGottesmanMatrix[mat_?MatrixQ, ss:{_?QubitQ, __?QubitQ}] := Module[
  { n = Length @ ss,
    kk, qq, rr,
    ff, hh, aa, bb, vv,
    opf, oph, opa, opb, opv, cyc, new },

  ff = Transpose[Partition[#, 2]& /@ Take[mat, 2]];
  kk = FirstPosition[GottesmanInner @@@ ff, 1];
  
  If[ MissingQ[kk],
    Message[FromGottesmanMatrix::spmat, MatrixForm @ mat];
    Return[1],
    kk = First[kk]
   ];

  If[ kk != 1,
    cyc = CircleTimes[
      PermutationMatrix[Cycles @ {{1, kk}}, n],
      One[2]
     ];
    new = Mod[mat . cyc, 2];
    opf = Swap @@ Part[ss, {1, kk}];
    Return @ Elaborate[opf ** FromGottesmanMatrix[new, ss]]
   ];

  {qq, rr} = TakeDrop[ss, 1];
  
  ff = First @ ff;
  ff = Mod[GottesmanInverse[ff] . ThePauli[1], 2];
  
  opf = FromGottesmanMatrix[ff, qq];

  new = CirclePlus[ff, One[2*(n-1)]];
  new = Mod[mat . new, 2];

  aa = FromGottesmanVector[new[[2, 3;;]], rr];
  bb = FromGottesmanVector[new[[1, 3;;]], rr];
  aa = GottesmanMatrix[opa = ControlledGate[qq, aa], ss];
  bb = GottesmanMatrix[opb = ControlledGate[qq, bb], ss];
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
  ss = S[Range[Length[mat]/2], $];
  op = FromGottesmanMatrix[mat, ss];
  ExpressionFor @ Matrix[op, ss]
 ]


GottesmanInverse::usage = "GottesmanInverse[mat] returns the inverse of binary symplectic matrix mat (with respect to the Gottesman inner product)."

GottesmanInverse[mat_] := Module[
  { n = Length[mat] / 2,
    JX },
  JX = CircleTimes[One[n], ThePauli[1]];
  Mod[JX . Transpose[mat] . JX, 2]
 ]
  
(**** </GottesmanMatrix> ****)


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

CliffordDecompose::usage = "CliffordDecompose is an alias of CliffordFactor."

CliffordFactor::usage = "CliffordFactor[op] returns a list of generators of the Clifford group that combine to yield Clifford operator op.\nCliffordFactor[mat,{s1,s2,\[Ellipsis]}] decomposes the Clifford operator corresponding to Gottesman matrix mat."

CliffordFactor::badmat = "`` is not a valid binary symplectic matrix."

CliffordFactor[op_] := Module[
  { ss = Qubits @ op,
    mat },
  mat = GottesmanMatrix[op, ss];
  CliffordFactor[mat, ss]
 ]

CliffordFactor[mat_?GottesmanMatrixQ, ss:{_?QubitQ}] :=
  { FromGottesmanMatrix[mat, ss] }

CliffordFactor[mat_?MatrixQ, ss:{_?QubitQ, __?QubitQ}] := Module[
  { n = Length @ ss,
    kk, qq, rr,
    ff, hh, aa, bb, vv,
    opf, oph, opa, opb, opv, cyc, new },

  ff = Transpose[Partition[#, 2]& /@ Take[mat, 2]];
  kk = FirstPosition[GottesmanInner @@@ ff, 1];
  
  If[ MissingQ[kk], 
    Message[CliffordFactor::badmat, MatrixForm @ mat];
    Return @ {1}
   ];

  If[ (kk = First[kk]) != 1,
    cyc = CircleTimes[
      PermutationMatrix[Cycles @ {{1, kk}}, n],
      One[2]
     ];
    new = Mod[mat . cyc, 2];
    opf = Swap @@ Part[ss, {1, kk}];
    Return @ Join[{opf}, CliffordFactor[new, ss]]
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

  simplifyGate @ Join[{opf, opa, oph, opb}, CliffordFactor[vv, rr]]
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

(**** </CliffordFactor> ****)


End[]

EndPackage[]
