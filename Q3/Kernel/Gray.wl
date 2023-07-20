(* -*- mode:math -*- *)
(* To simulate the universal quantum computation based on the Gray code. *)

BeginPackage["Q3`"]

`Gray`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.65 $"][[2]], " (",
  StringSplit["$Date: 2023-07-20 09:38:58+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ GrayCodeBasis, GrayTransform, TheGrayTransform };

{ GrayControlledGate, GrayControlledW,
  FromTwoLevelU, TwoLevelU, TwoLevelDecomposition };

(**** renamed ****)

{ GrayTwoLevelU };


Begin["`Private`"]

GraySubsets::usage = "GraySubsets[set] constructs a binary-reflected Gray code on set, that is, returns the list of all subsets of set each of which differs from its predecessor by only one element."

(* NOTE: The code has just been copied from Combinatorica package. *)

GraySubsets[n_Integer?Positive] := GraySubsets @ Range[n]

GraySubsets[{}] := { {} }

GraySubsets[ls_List] := Block[
  { $RecursionLimit = Infinity,
    ss }, 
  ss = GraySubsets @ Take[ls, 1-Length[ls]];
  Join[ss,  Map[Prepend[#, First @ ls]&, Reverse @ ss]]
 ]


(**** <GrayTransform> ****)

GrayCodeBasis::usage = "GrayCodeBasis[{s1,s2,\[Ellipsis]}] returns the computational basis of qubits or spins s1, s2, \[Ellipsis] arranged in the Gray code (i.e., reflected binary code) sequence.\nGrayCodeBasis[n] returns the computational basis of n (unlabelled) qubits arranged in the Gray code."

GrayCodeBasis[n_Integer] := Basis[n] . TheGrayTransform[n]

GrayCodeBasis[ss:{__?QubitQ}] := Basis[ss] . TheGrayTransform[Length @ ss]

GrayCodeBasis[ss:{__?SpinQ}] := 
  Basis[ss] . TheGrayTransform[Length @ ss] /;
  AllTrue[Spin[ss], # == 1/2&]


GrayTransform::usage = "GrayTransform[{s1,s2,\[Ellipsis]}] represents the unitary transformation from the computational basis of qubits or spins s1, s2, \[Ellipsis] to the Gray code basis.\nGrayTransform[n] is for n unlabelled qubits."

GrayTransform[ss:{__?QubitQ}] := GrayTransform[FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]


GrayTransform /:
Matrix @ GrayTransform[ss:{__?QubitQ}] := TheGrayTransform[Length @ ss]

GrayTransform /:
Matrix @ GrayTransform[n_Integer] := TheGrayTransform[n]


GrayTransform /:
Elaborate[op_GrayTransform] = op (* fallback *)

GrayTransform /:
Elaborate @ GrayTransform[ss:{__?QubitQ}] :=
  Elaborate @ ExpressionFor[TheGrayTransform[Length @ ss], ss]

GrayTransform /:
Elaborate @ GrayTransform[n_Integer] := TheGrayTransform[n]
  Elaborate @ ExpressionFor[TheGrayTransform[n]]


GrayTransform /:
Multiply[pre___, GrayTransform[ss:{__?QubitQ}], Ket[aa_Association]] :=
  Ket[ss -> BinaryToGray[Lookup[aa, ss]]]

GrayTransform /:
Multiply[pre___, op:GrayTransform[{__?QubitQ}], post___] :=
  Multiply[pre, Elaborate @ op, post]

GrayTransform /:
Multiply[pre___, GrayTransform[n_Integer], Ket[bb__?BinaryQ]] :=
  Ket @@ BinaryToGray[{bb}]


TheGrayTransform::usage = "TheGrayTransform[n] returns the matrix transforming the computational basis of n qubits to the Gray code basis."

TheGrayTransform[n_] := Module[
  {gg, mm},
  gg = Map[FromDigits[#, 2] &, BinaryToGray /@ Tuples[{0, 1}, n]];
  mm = PadRight[{1}, Power[2, n]];
  Transpose[RotateRight[mm, #]& /@ gg]
 ]

(**** </GrayTransform> ****)


GrayControlledGate::usage = "GrayControlledGate[qq, expr] decomposes the n-bit controlled expr into elementary gates, where qq is the list of control qubits and expr is supposed to be a unitary operator."

(* See Barenco et al. (1995) and Vartiainen et al. (2004). *)

GrayControlledGate[q_?QubitQ, expr_] := GrayControlledGate[{q}, expr]

GrayControlledGate[{q_?QubitQ}, expr_] := ControlledGate[{q}, expr]

GrayControlledGate[qq:{_?QubitQ, __?QubitQ}, expr_] := Module[
  { mm = Matrix[expr],
    nn = Power[2, Length[qq]-1], 
    op, rr, cc, dd, vv, ll, cV, cn },

  mm = MatrixPower[mm, 1/nn];
  op = ExpressionFor[mm, Qubits @ expr];

  rr = Reverse /@ GraySubsets[ReverseSort @ FlavorNone @ qq];
  rr = Rest[rr];

  nq = Length @ qq;
  cc = Last /@ rr;
  vv = Riffle[ ConstantArray[op, nn], Dagger @ op ];
  ll = Riffle[
    ConstantArray["Label" -> "V", nn], 
    "Label" -> Superscript["V", "\[Dagger]"]
   ];
  cV = ControlledGate @@@ Transpose[{cc, vv, ll}];

  dd = Flatten @ Successive[MutualComplement, Most /@ rr];
  cn = CNOT @@@ Transpose[{dd, Rest @ cc}];

  FunctionExpand @ Riffle[cV, cn]
 ]

MutualComplement[a_, b_] := Union[Complement[a, b], Complement[b, a]]


GrayControlledW::usage = "GrayControlledW[qq, expr] decomposes the n-bit controlled expr into elementary gates, expr is supposed to be a unitary operator.\nThis version is merely for heuristic purposes. Use GrayControlledGate instead."

GrayControlledW[q_?QubitQ, expr_] := ControlledGate[{q}, expr]

GrayControlledW[{q_?QubitQ}, expr_] := ControlledGate[{q}, expr]

GrayControlledW[qq:{__?QubitQ}, expr_] := Module[
  { mm = Matrix[expr],
    tt = Qubits[expr],
    rr = Reverse /@ GraySubsets[ReverseSort @ FlavorNone @ qq],
    ss, op, n, V },
  ss = Map[Length, rr];
  ss = -Power[-1, ss];
  
  n = Length @ qq;
  V = FunctionExpand @ MatrixPower[mm, Power[2, 1-n]];
  op = ExpressionFor[V, tt];

  Flatten @ MapThread[grayCtrl[#1, op, #2]&, {rr, ss}]
 ]


grayCtrl[qq_, op_,  1] := grayCtrl[qq, op, "V"]

grayCtrl[qq_, op_, -1] :=
  grayCtrl[qq, Dagger @ op, Superscript["V","\[Dagger]"]]


grayCtrl[{ }, op_, lbl_] := {}

grayCtrl[{q_?QubitQ}, op_, lbl_] := ControlledGate[{q}, op, "Label"->lbl]

grayCtrl[{aa__?QubitQ, b_?QubitQ}, op_, lbl_] := With[
  { cn = Map[CNOT[#, b]&, {aa}] },
  Flatten @ { cn, ControlledGate[{b}, op, "Label"->lbl], cn }
 ]


(**** <BinaryToGray> ****)

BinaryToGray::usage = "BinaryToGray[bits] converts the binary number bits to a bit-reflected Gray code (BRGC)."

(* https://en.wikipedia.org/wiki/Gray_code *)
BinaryToGray[bits_?VectorQ] := Mod[bits + ShiftRight[bits], 2]

GrayToBinary::usage = "GrayToBinary[gray] converts the bit-reflected Gray code gray to a binary number."

(* https://en.wikipedia.org/wiki/Gray_code *)
GrayToBinary[gg:{0..}] := gg

(* https://en.wikipedia.org/wiki/Gray_code *)
GrayToBinary[gray_?VectorQ] := Module[
  { i, k, mask },
  k = Length[gray] - First[FirstPosition[gray, 1]];
  mask = Total @ Table[ShiftRight[gray, i], {i, 1, k}];
  Mod[gray + mask, 2]
 ]


GrayToInteger::usage = "GrayToInteger[gray] converts the Gray code gray to a decimal number."

GrayToInteger[gray_?VectorQ] := FromDigits[GrayToBinary @ gray, 2]


IntegerToGray::usage = "IntegerToGray[n] gives the Gray code (i.e., reflected binary code) corresponding to the sequence of binary digits of the integer n.\nIntegerToGray[n, len] pads the list on the left with zeros to give a list of length len."

IntegerToGray[n_Integer] := BinaryToGray @ IntegerDigits[n, 2]

IntegerToGray[nn:{___Integer}] := BinaryToGray /@ IntegerDigits[nn, 2]

IntegerToGray[n_Integer, len_Integer] :=
  BinaryToGray @ IntegerDigits[n, 2, len]

IntegerToGray[nn:{___Integer}, len_Integer] :=
  BinaryToGray /@ IntegerDigits[nn, 2, len]

(**** </BinaryToGray> ****)


(**** <GraySequence> ****)

GraySequence::usage = "GraySequence[{x, y}, n] returns the list of n-bit Gray codes connecting the integers x and y.\nGraySequence[{x, y}] calculates n automatically.\nGraySequence[n] returns the list of all n-bit Gray codes.\nEach Gray code is given in binary digits."

GraySequence[{x_Integer, y_Integer}, n_Integer?Positive] := Module[
  {kk = IntegerDigits[BitXor[x, y], 2, n]},
  kk = BitSet[0, n - Flatten @ Position[kk, 1]];
  FoldList[BitXor, x, kk]
 ]

GraySequence[{x_Integer, y_Integer}] :=
  GraySequence[{x, y}, Max @ Ceiling @ Log[2, {x, y} + 1]]


GraySequence[1] = {0, 1}

GraySequence[n_Integer] := Join[
  GraySequence[n-1],
  BitSet[Reverse @ GraySequence[n-1], n-1]
 ] /; n > 1

(**** </GraySequence> ****)


(**** <FromTwoLevelU> *****)

FromTwoLevelU::usage = "FromTwoLevelU[mat, {x, y}, {q1, q2, ...}] returns a list containing multi-control NOT gates and one controlled-unitary gate that compose the two-level unitary operation specified by mat."

FromTwoLevelU[ TwoLevelU[mat_?MatrixQ, {x_, y_}, L_], qq:{__?QubitQ} ] :=
  FromTwoLevelU[mat, {x, y}, FlavorNone @ qq] /;
  L == Power[2, Length @ qq]

FromTwoLevelU[mat_?MatrixQ, {x_Integer, y_Integer}, qq:{__?QubitQ}] :=
  Module[
    { gray = GraySequence[{x, y} - 1, Length @ qq],
      mask, expr },
    mask = Successive[grayCNOT[{#1,#2}, qq]&, Most @ gray];
    expr = grayCtrlU[Take[gray, -2], mat, qq];
    Join[mask, {expr}, Reverse @ mask]
   ] /; OrderedQ @ {x, y}


grayCNOT::usage = "grayCNOT[{x, y}, {s1, s2, \[Ellipsis]}] construct the CNOT gate corresponding to transposition Cycles[{{x,y}}], where integers x and y are assumed to be in the Gray code; they are different in only one bit."

grayCNOT[pair:{_Integer, _Integer}, ss:{__?QubitQ}] := Module[
  { n = Length @ ss,
    cc, tt, vv},
  cc = IntegerDigits[BitXor @@ pair, 2, n];
  tt = Part[ss, Flatten @ Position[cc, 1]];
  cc = Flatten @ Position[cc, 0];
  vv = Part[IntegerDigits[First @ pair, 2, n], cc];
  cc = Part[ss, cc];
  CNOT[cc -> vv, tt]
 ]

grayCNOT[kk:{_Integer, _Integer, __Integer}, ss:{__?QubitQ}] := With[
  { mask = Successive[grayCNOT[{#1, #2}, ss]&, Most @ kk] },
  Join[mask, List @ grayCNOT[Take[kk, -2], ss], Reverse @ mask]
 ]


grayCtrlU::usage = "grayCtrlU[{x, y}, mat, {s1, s2, \[Ellipsis]}] construct the controlled-unitary gate corresponding to the two-level unitary matrix mat with rows and columns x and y. Here, x and y are supposed to be the Gray code."

grayCtrlU[pair:{_Integer, _Integer}, mat_, ss:{__?QubitQ}] := Module[
  { n = Length @ ss,
    cc, tt, vv, op },
  cc = IntegerDigits[BitXor @@ pair, 2, n];

  tt = FlavorNone @ Part[ss, Flatten @ Position[cc, 1]];
  op = Elaborate @ ExpressionFor[mat, tt];
  If[ Not @ OrderedQ @ pair,
    op = With[{X = First[tt][1]}, X ** op ** X]
   ];
    
  cc = Flatten @ Position[cc, 0];
  vv = Part[IntegerDigits[First @ pair, 2, n], cc];
  cc = Part[ss, cc];
  ControlledGate[cc -> vv, op, "Label"->"U"]
 ]


GrayTwoLevelU::usage = "GrayTwoLevelU has been renamed FromTwoLevelU."

GrayTwoLevelU[args___] := (
  Message[Q3General::renamed, "GrayTwoLevelU", "FromTwoLevelU"];
  FromTwoLevelU[args]
 )

(**** </FromTwoLevelU> *****)


TwoLevelU::usage = "TwoLevelU[mat, {i, j}, n] represents a two-level unitary matrix, that is, the 2 x 2 unitary matrix mat operating on the ith and jth rows and columns of an n x n matrix.\nMatrix[TwoLevelU[mat, {i, j}, n]] returns the full n x n matrix.\nSee also FromTwoLevelU, which decomposes TwoLevelU[...] into CNOT gates and one controlled-U gate."

Format[op_TwoLevelU] := Interpretation[MatrixForm @ Matrix @ Chop @ op, op]

TwoLevelU /:
HoldPattern @ Matrix @ TwoLevelU[mat_?MatrixQ, {x_, y_}, n_] := Module[
  { new = One[n],
    val = Flatten @ mat,
    idx = Tuples[{x, y}, 2] },
  ReplacePart[new, Thread[idx -> val]]
 ]


TwoLevelDecomposition::usage = "TwoLevelDecomposition[mat] returns a list of two-level unitary matrices U1, U2, ... in terms of TwoLevelU, where Dot[U1, U2, ...] is formally equivalent to mat."

TwoLevelDecomposition[mat_?MatrixQ] := twoLevelDCMP[mat, 1]

twoLevelDCMP[mat_?MatrixQ, k_Integer] := Module[
  { mm = Rest @ mat,
    UU, vv },
  {vv, UU} = twoLevelDCMP[First @ mat, k] /. {Identity -> Nothing};
  If[k == Length[First @ mat], Return @ UU];
  If[mm == {}, Return @ UU];
  mm = Dot[ mm, Sequence @@ Reverse[Topple /@ Matrix /@ UU] ];
  Join[twoLevelDCMP[mm, k+1], UU]
 ]

twoLevelDCMP[vec_?VectorQ, k_Integer] := Module[
  { new, UU, U },
  {new, UU} = twoLevelDCMP[vec, k+1];
  {new, U}  = twoLevelDCMP[new, {k}];
  {new, Prepend[UU, U]}
 ] /; 1 <= k < Length[vec]-1

twoLevelDCMP[vec_?VectorQ, k_Integer] := Module[
  {new, U},
  {new, U} = twoLevelDCMP[vec, {k}];
  {new, {U}}
 ] /; k >= Length[vec]-1

twoLevelDCMP[vec_?VectorQ, {k_Integer}] := Module[
  { new = Take[vec, {k, k+1}],
    nrm, U },
  If[Chop @ Norm[new-{1,0}] == 0, Return @ {vec, Identity}];

  nrm = Norm[new];
  If[Chop[nrm] == 0, Return @ {vec, Identity}];
  
  U = {
    new,
    {-1, 1} Reverse[Conjugate @ new]
   } / nrm;
  new = ReplacePart[vec, {k -> nrm, k+1 -> 0}];
  {new, TwoLevelU[U, {k, k+1}, Length @ vec]}
 ] /; 1 <= k < Length[vec]

twoLevelDCMP[vec_?VectorQ, {k_Integer}] := With[
  { z = Last @ vec },
  { ReplacePart[vec, k -> Abs @ z],
    TwoLevelU[DiagonalMatrix @ {1, z/Abs[z]}, {k-1, k}, k] }
 ] /; k == Length[vec]


End[]

EndPackage[]
