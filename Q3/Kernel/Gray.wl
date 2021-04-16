(* -*- mode:math -*- *)
(* Mathematica package to simulate the universal quantum computation based on
   the Gray code. *)

BeginPackage[ "Q3`Gray`",
  { "Q3`Abel`",
    "Q3`Cauchy`",
    "Q3`Pauli`",
    "Q3`Quisso`"
   }
 ]

`Information`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.31 $"][[2]], " (",
  StringSplit["$Date: 2021-04-16 11:40:04+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

Q3`Q3Clear[];

{ BinaryToGray, GrayToBinary };

{ GrayCode, GrayCodeSubsets };

{ GrayControlledU, GrayControlledW };

{ GrayTwoLevelU, TwoLevelU, TwoLevelDecomposition };


Begin["`Private`"]

$symbs = Unprotect[]


GrayCodeSubsets::usage = "GrayCodeSubsets[set] constructs a binary-reflected Gray code on set, that is, returns the list of all subsets of set each of which differs from its predecessor by only one element."

(* NOTE: The code has just been copied from Combinatorica package. *)

GrayCodeSubsets[n_Integer?Positive] := GrayCodeSubsets[Range[n]]

GrayCodeSubsets[ { } ] := { {} }

GrayCodeSubsets[l_List] := Block[
  { $RecursionLimit = Infinity,
    s }, 
  s = GrayCodeSubsets[Take[l, 1-Length[l]]];
  Join[s,  Map[Prepend[#, First[l]]&, Reverse[s]]]
 ]


GrayControlledU::usage = "GrayControlledU[qq, expr] decomposes the n-bit controlled expr into elementary gates, where qq is the list of control qubits and expr is supposed to be a unitary operator."

(* See Barenco et al. PRB (1995). *)

GrayControlledU[q_?QubitQ, expr_] := GrayControlledU[{q}, expr]

GrayControlledU[{q_?QubitQ}, expr_] := ControlledU[{q}, expr]

GrayControlledU[qq:{_?QubitQ, __?QubitQ}, expr_] := Module[
  { mm = Matrix[expr],
    nn = Power[2, Length[qq]-1], 
    op, rr, cc, dd, vv, ll, cV, cn },

  mm = MatrixPower[mm, 1/nn];
  op = QuissoExpression[mm, Qubits @ expr];

  rr = Reverse /@ GrayCodeSubsets[ReverseSort @ FlavorNone @ qq];
  rr = Rest[rr];

  nq = Length @ qq;
  cc = Last /@ rr;
  vv = Riffle[ ConstantArray[op, nn], Dagger @ op ];
  ll = Riffle[
    ConstantArray["Label" -> "V", nn], 
    "Label" -> Superscript["V", "\[Dagger]"]
   ];
  cV = ControlledU @@@ Transpose[{cc, vv, ll}];

  dd = Flatten @ Successive[MutualComplement, Most /@ rr];
  cn = CNOT @@@ Transpose[{dd, Rest @ cc}];

  FunctionExpand @ Riffle[cV, cn]
 ]

MutualComplement[a_, b_] := Union[Complement[a, b], Complement[b, a]]


GrayControlledW::usage = "GrayControlledW[qq, expr] decomposes the n-bit controlled expr into elementary gates, expr is supposed to be a unitary operator.\nThis version is merely for heuristic purposes. Use GrayControlledU instead."

GrayControlledW[q_?QubitQ, expr_] := ControlledU[{q}, expr]

GrayControlledW[{q_?QubitQ}, expr_] := ControlledU[{q}, expr]

GrayControlledW[qq:{__?QubitQ}, expr_] := Module[
  { mm = Matrix[expr],
    tt = Qubits[expr],
    rr = Reverse /@ GrayCodeSubsets[ReverseSort @ FlavorNone @ qq],
    ss, op, n, V },
  ss = Map[Length, rr];
  ss = -Power[-1, ss];
  
  n = Length @ qq;
  V = FunctionExpand @ MatrixPower[mm, Power[2, 1-n]];
  op = QuissoExpression[V, tt];

  Print["op = ", op];

  Flatten @ MapThread[grayCtrl[#1, op, #2]&, {rr, ss}]
 ]


grayCtrl[qq_, op_,  1] := grayCtrl[qq, op, "V"]

grayCtrl[qq_, op_, -1] :=
  grayCtrl[qq, Dagger @ op, Superscript["V","\[Dagger]"]]


grayCtrl[{ }, op_, lbl_] := {}

grayCtrl[{q_?QubitQ}, op_, lbl_] := ControlledU[{q}, op, "Label"->lbl]

grayCtrl[{aa__?QubitQ, b_?QubitQ}, op_, lbl_] := With[
  { cn = Map[CNOT[#, b]&, {aa}] },
  Flatten @ { cn, ControlledU[{b}, op, "Label"->lbl], cn }
 ]


BinaryToGray::usage = "BinaryToGray[bits] converts the binary number bits to a bit-reflected Gray code (BRGC)."

(* https://en.wikipedia.org/wiki/Gray_code *)
BinaryToGray[bits_List] := Mod[bits + ShiftRight[bits], 2]

GrayToBinary::usage = "GrayToBinary[gray] converts the bit-reflected Gray code gray to a binary number."

(* https://en.wikipedia.org/wiki/Gray_code *)
GrayToBinary[gg : {0 ..}] := gg

(* https://en.wikipedia.org/wiki/Gray_code *)
GrayToBinary[gray_List] := Module[
  { j = First @ FirstPosition[gray, 1],
    mask },
  mask = Total @ Table[ShiftRight[gray, n], {n, 1, Length[gray] - j}];
  Mod[gray + mask, 2]
 ]


GrayCode::usage = "GrayCode[n, x_, y_] returns the list of n-bit Gray codes connecting the integers x and y.\nEach Gray code is given in binary digits.\nGrayCode[n] returns the list of all n-bit Gray codes.\nGrayCode[n] is equivalent to GrayCode[n, 0, 2^n-1]."

GrayCode[n_Integer, x_, y_] := Module[
  { a = FromDigits[GrayToBinary[IntegerDigits[x, 2, n]], 2],
    b = FromDigits[GrayToBinary[IntegerDigits[y, 2, n]], 2] },
  If[ a > b,
    Reverse[ BinaryToGray /@ IntegerDigits[Range[b, a], 2, n] ],
    BinaryToGray /@ IntegerDigits[Range[a, b], 2, n]
   ]
 ]

GrayCode[1] = {{0}, {1}}

GrayCode[n_Integer] := Join[
  Map[Prepend[#, 0]&, GrayCode[n - 1]],
  Map[Prepend[#, 1]&, Reverse @ GrayCode[n - 1]]
 ] /; n > 1


GrayTwoLevelU::usage = "GrayTwoLevelU[mat, {x, y}, {q1, q2, ...}] returns a list of CNOT gates and one controlled-U gate that compose the two-level unitary operation specified by mat."

GrayTwoLevelU[ TwoLevelU[mat_?MatrixQ, {x_, y_}, L_], qq:{__?QubitQ} ] :=
  GrayTwoLevelU[mat, {x, y}, FlavorNone @ qq] /;
  L == Power[2, Length @ qq]

GrayTwoLevelU[mat_?MatrixQ, {x_Integer, y_Integer}, qq:{__?QubitQ}] :=
  Module[
    { gray = GrayCode[Length @ qq, x-1, y-1],
      mask, expr },
    mask = Catenate @ Successive[grayCNOT[#1, #2, qq]&, Most @ gray];
    expr = grayCtrlU[gray[[-2]], gray[[-1]], mat, qq];
    Join[mask, expr, Reverse @ mask]
   ] /; OrderedQ @ {x, y}

grayCNOT[g1_, g2_, qq_] := Module[
  { xx = g1 + g2,
    cc = Mod[g1 + g2, 2] },
  xx = Pick[qq, xx, 0];
  xx = Through[xx[1]];
  cc = GroupBy[Transpose @ {cc, qq}, First, Last @* Transpose];
  {xx, CNOT[cc[0], cc[1]], xx} /. {} -> Nothing
 ]

grayCtrlU[g1_, g2_, mat_, qq_] := Module[
  { xx = g1 + g2,
    cc = Mod[g1 + g2, 2],
    op },
  xx = Pick[qq, xx, 0];
  xx = Through[xx[1]];
  cc = GroupBy[Transpose @ {cc, qq}, First, Last @* Transpose];
  op = QuissoExpression[mat, cc[1]];
  If[ Not @ OrderedQ @ {g1, g2},
    With[
      { tt = First @ cc[1] },
      op = Multiply[tt[1], op, tt[1]]
     ]
   ];
  {xx, ControlledU[cc[0], op, "Label"->"U"], xx} /. {} -> Nothing
 ]


TwoLevelU::usage = "TwoLevelU[mat, {i, j}, n] represents a two-level unitary matrix, that is, the 2 x 2 unitary matrix mat operating on the ith and jth rows and columns of an n x n matrix.\nMatrix[TwoLevelU[mat, {i, j}, n]] returns the full n x n matrix.\nSee also GrayTwoLevelU, which decomposes TwoLevelU[...] into CNOT gates and one controlled-U gate."

TwoLevelU /:
HoldPattern @ Matrix @ TwoLevelU[mat_?MatrixQ, {x_, y_}, n_] := Module[
  { new = One[n],
    val = Flatten @ mat,
    idx = Tuples[{x, y}, 2] },
  ReplacePart[new, Thread[idx -> val]]
 ]


TwoLevelDecomposition::usage = "TwoLevelDecomposition[mat] returns a list of two-level unitary matrices U1, U2, ... in terms of TwoLevelU, where Dot[U1, U2, ...] is formally equivalent to mat."

TwoLevelDecomposition[mat_?MatrixQ] := twoLevelDCMP[mat, 1]

twoLevelDCMP[mat_?MatrixQ, j_Integer] := Module[
  { mm = Rest @ mat,
    UU, vv },
  {vv, UU} = twoLevelDCMP[First @ mat, j];
  If[ j == Length[First @ mat], Return @ UU ];
  If[ mm == {}, Return @ UU ];
  mm = Dot[ mm, Sequence @@ Reverse[ Topple /@ Matrix /@ UU ] ];
  Join[ twoLevelDCMP[mm, j+1], UU ]
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
    L = Length[vec],
    U },
  U = {
    new,
    {-1, 1} Reverse[Conjugate @ new]
   } / Norm[new];
  
  new = ReplacePart[vec, {k -> Norm[new], k+1 -> 0}];
  { new, TwoLevelU[U, {k, k+1}, L] }
 ] /; 1 <= k < Length[vec]

twoLevelDCMP[vec_?VectorQ, {k_Integer}] := With[
  { z = Last @ vec },
  { ReplacePart[vec, k -> Abs @ z],
    TwoLevelU[DiagonalMatrix @ {1, z/Abs[z]}, {k-1, k}, k] }
 ] /; k == Length[vec]


Protect[ Evaluate @ $symbs ]

End[]


Q3`Q3Protect[]


EndPackage[]
