(* -*- mode:math -*- *)
(* To simulate the universal quantum computation based on the Gray code. *)
BeginPackage["Q3`"]

`Gray`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.90 $"][[2]], " (",
  StringSplit["$Date: 2023-08-06 09:20:27+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ GrayBasis, GrayTransform, TheGrayTransform, GrayCycles };

{ GrayGivensFactor };

{ GrayControlledGate };


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

GrayBasis::usage = "GrayBasis[{s1,s2,\[Ellipsis]}] returns the computational basis of qubits or spins s1, s2, \[Ellipsis] arranged in the Gray code (i.e., reflected binary code) sequence.\nGrayBasis[n] returns the computational basis of n (unlabelled) qubits arranged in the Gray code."

GrayBasis[n_Integer] := Basis[n] . TheGrayTransform[n]

GrayBasis[ss:{__?QubitQ}] := Basis[ss] . TheGrayTransform[Length @ ss]

GrayBasis[ss:{__?SpinQ}] := 
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
Elaborate @ GrayTransform[n_Integer] :=
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

TheGrayTransform[n_Integer] := Module[
  {gg, mm},
  gg = BitReflect[Range[Power[2, n]]-1];
  mm = PadRight[{1}, Power[2, n]];
  Transpose[RotateRight[mm, #]& /@ gg]
 ]


GrayCycles::usage = "GrayCycles[n] returns the cycles representation of the Gray transform."

GrayCycles[n_Integer] := InversePermutation @
  PermutationCycles[1 + BitReflect[Range[Power[2, n]] - 1]]

(**** </GrayTransform> ****)


(**** <GrayControlledGate> ****)

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

(**** </GrayControlledGate> ****)


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

SetAttributes[IntegerToGray, Listable]

IntegerToGray[n_Integer] := IntegerDigits[BitReflect[n], 2]

IntegerToGray[n_Integer, len_Integer] :=
  IntegerDigits[BitReflect[n], 2, len]


BitReflect::usage = "BitReflect[n] returns an integer the binary digits of which are the Gray code (reflected binary code) of integer n."

BitReflect[n_] := BitXor[n, BitShiftRight[n]]

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



(**** <GivensRotation> *****)

GivensRotation::usage = "GivensRotation[mat, {i, j}, n] represents the Givens foration in the plane spanned by the two coordinate axes i and j in an n-dimensional space.\nGivensRotation[mat, {i, j}, {s1, s2, \[Ellipsis]}] represents the Givens rotatation operator acting on qubits s1, s2, \[Ellipsis]."

GivensRotation::two = "The first argument of GivensRotation must be a 2\[Times]2 matrix."

GivensRotation::range = "Either or both of `` is out of [1, ``]."

AddElaborationPatterns[ _GivensRotation ]

GivensRotation /:
NonCommutativeQ[ GivensRotation[___] ] = True

GivensRotation /:
MultiplyGenus @ GivensRotation[___] := "Singleton"

GivensRotation /:
MultiplyKind @ GivensRotation[_?MatrixQ, _, {__?QubitQ}] = Qubit


GivensRotation /:
MakeBoxes[op:GivensRotation[mat_?MatrixQ, ij:{_, _}, n_Integer], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    GivensRotation, op, None,
    { BoxForm`SummaryItem @ {"Dimensions: ", {n, n}},
      BoxForm`SummaryItem @ {"Affected columns and rows: ", ij} },
    { BoxForm`SummaryItem @ {"Matrix: ", mat} },
    fmt, "Interpretable" -> Automatic ]

GivensRotation /:
MakeBoxes[op:GivensRotation[mat_?MatrixQ, ij:{_, _}, ss:{__?QubitQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    GivensRotation, op, None,
    { BoxForm`SummaryItem @ {"Acting on: ", ss},
      BoxForm`SummaryItem @ {"Affected columns and rows: ", ij} },
    { BoxForm`SummaryItem @ {"Matrix: ", mat} },
    fmt, "Interpretable" -> Automatic ]


GivensRotation[mat_?MatrixQ, rest___] := (
  Message[GivensRotation::two, mat];
  GivensRotation[One[2], rest]
 ) /; Dimensions[mat] != {2, 2}

GivensRotation[mat_?MatrixQ, ij:{_Integer, _Integer}, n_Integer] := (
  Message[GivensRotation::range, ij, n];
  GivensRotation[mat, {1, 2}, n]
 ) /; Not[And @@ Thread[1 <= ij <= n]]


GivensRotation[mat_?MatrixQ, ij_, ss:{__?QubitQ}] :=
  GivensRotation[mat, ij, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]


GivensRotation /:
Dagger[op_GivensRotation] = op (* fallback *)

GivensRotation /:
Dagger @ GivensRotation[mat_?MatrixQ, rest__] :=
  GivensRotation[Topple @ mat, rest]


GivensRotation /:
Elaborate[op:GivensRotation[_, _, ss:{__?QubitQ}, ___]] :=
  Elaborate @ ExpressionFor[Matrix[op], ss]


GivensRotation /:
ExpressionFor[
  GivensRotation[mat_?MatrixQ, ij:{_Integer, _Integer}, n_Integer],
  ss:{__?QubitQ} ] := GivensRotation[mat, ij, ss]


GivensRotation /:
MatrixForm[op:GivensRotation[_?MatrixQ, {_, _}, n_Integer]] :=
  MatrixForm @ Matrix @ op

GivensRotation /:
Matrix @ GivensRotation[mat_?MatrixQ, {x_Integer, y_Integer}, n_Integer] :=
  Module[
    { new = One[n],
      val = Flatten @ mat,
      idx = Tuples[{x, y}, 2] },
    ReplacePart[new, Thread[idx -> val]]
   ]

GivensRotation /:
Matrix @ GivensRotation[mat_?MatrixQ, ij_, ss:{__?QubitQ}] :=
  Matrix[GivensRotation[mat, ij, ss], ss]

GivensRotation /:
Matrix[GivensRotation[mat_?MatrixQ, ij_, ss:{__?QubitQ}], rest__] :=
  SparseArray @ Matrix[
    ExpressionFor[Matrix @ GivensRotation[mat, ij, Power[2, Length @ ss]], ss],
    rest
   ]

(**** </GivensRotation> *****)


(**** <GivensRotation/:Expand> *****)

GivensRotation /:
Expand @
  GivensRotation[mat_?MatrixQ, ij:{_Integer, _Integer}, ss:{__?QubitQ}] :=
  Module[
    { gray = GraySequence[ij-1, Length @ ss],
      mask, expr },
    mask = Successive[grayCNOT[{#1, #2}, ss]&, Most @ gray];
    expr = grayCtrlU[Take[gray, -2], mat, ss];
    QuantumCircuit @@ Join[mask, {expr}, Reverse @ mask]
   ] /; OrderedQ[ij]


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

(**** </GivensRotation/:Expand> *****)


(**** <GivensFactor> ****)

GivensFactor::usage = "GivensFactor[mat] returns a list of Givens matrices that compose the unitary matrix mat.\nGivensFactor[op]
returns a list of controlled-unitary and single-qubit gates that compose the unitary operator op.\nGivensFactor[mat,{Subscript[s, 1],Subscript[s, 2],\[Ellipsis]}] regards the matrix mat as the matrix representation of a unitary operator acting on qubits Subscript[s, 1],Subscript[s, 2],\[Ellipsis]."

GivensFactor::dim = "The dimensions of matrix `` are not compatible with qubits ``."

GivensFactor[mat_?SquareMatrixQ, ss:{__?QubitQ}] :=
  GivensFactor[mat, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]

GivensFactor[mat_?SquareMatrixQ, ss:{__?QubitQ}] := (
  Message[GivensFactor::dim, mat, ss];
  { ActOn[1, ss] }
 ) /; Length[mat] != Power[2, Length @ ss]


GivensFactor[mat_?SquareMatrixQ, ss:{__?QubitQ}] := With[
  { gg = GivensFactor[mat] },
  Flatten @ Join[ {First @ gg}, Map[ExpressionFor[#, ss]&, Rest @ gg] ]
 ]

GivensFactor[mat_?SquareMatrixQ] := Module[
  { len = Length @ mat,
    det, new, pos },
  det = Conjugate[Power[Det @ mat, 1/len]];
  pos = Flatten[Table[{i, j}, {i, len-1}, {j, Reverse @ Range[i+1, len]}], 1];
  Dagger @ Reverse @ Append[
    FoldPairList[theGivens, det * mat, pos] /. {Identity -> Nothing},
    det
   ]
 ]

GivensFactor[op_] := With[
  { ss = Qubits @ op },
  GivensFactor[Matrix[op, ss], ss]
 ]


theGivens::usage = "theGivens[...] represents each step of the Givens decomposition procedure in the Gray code basis, nullifying the jth column element of the ith row of mat using the (j-1)th column element."

theGivens[mat_?MatrixQ, {i_Integer, j_Integer}] :=
  Module[
    { vec = Normalize @ mat[[i, {j-1, j}]],
      new, two },
    If[ Or[Chop[vec] == {1, 0}, Chop[Norm @ vec] == 0],
      Return @ {Identity, mat}
     ];
    new = Transpose @ {Conjugate @ vec, {-1, 1} * Reverse[vec]};
    (* In order to properly handle the determinant,
       it must be {-1,1}; not {1,-1}. *)
    two = GivensRotation[new, {j-1, j}, Length @ mat];
    (* Basis change to the Gray code basis. *)
    new = Matrix[two];
    {two, mat.new}
   ]

(**** </GivensFactor> ****)


(**** <GrayGivensFactor> ****)

(* See: Vartiainen et al. (2004). *)

GrayGivensFactor::usage = "GrayGivensFactor[op]
returns a list of controlled-unitary and single-qubit gates that compose the unitary operator op.\nGrayGivensFactor[mat,{Subscript[s, 1],Subscript[s, 2],\[Ellipsis]}] regards the matrix mat as the matrix representation of a unitary operator acting on qubits Subscript[s, 1],Subscript[s, 2],\[Ellipsis]."

GrayGivensFactor::dim = "The dimensions of matrix `` are not compatible with qubits ``."

GrayGivensFactor[mat_?SquareMatrixQ, ss:{__?QubitQ}] :=
  GrayGivensFactor[mat, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]

GrayGivensFactor[mat_?SquareMatrixQ, ss:{__?QubitQ}] := (
  Message[GrayGivensFactor::dim, mat, ss];
  { ActOn[1, ss] }
 ) /; Length[mat] != Power[2, Length @ ss]

GrayGivensFactor[mat_?SquareMatrixQ, ss:{__?QubitQ}] := Module[
  { len = Length[mat],
    gry = GrayCycles[Length @ ss],
    det, new, pos },
  det = Conjugate[Power[Det @ mat, 1/len]];
  pos = Flatten[Table[{i, j}, {i, len-1}, {j, Reverse @ Range[i+1, len]}], 1];
  (* Basis change to the Gray code basis. *)
  new = det * Transpose @ Permute[Transpose @ Permute[mat, gry], gry];
  Dagger @ Reverse @ Append[
    FoldPairList[grayGivens[gry, ss], new, pos],
    If[Rationalize[det] == 1, Nothing, det]
   ]
 ]

GrayGivensFactor[op_] := With[
  { ss = Qubits @ op },
  GrayGivensFactor[Matrix[op, ss], ss]
 ]


grayGivens::usage = "grayGivens[...][...] represents each step of the Givens decomposition procedure in the Gray code basis, nullifying the jth column element of the ith row of mat using the (j-1)th column element."

grayGivens[gry_Cycles, ss:{__?QubitQ}][mat_?MatrixQ, {i_Integer, j_Integer}] :=
  Module[
    { vec = Normalize @ mat[[i, {j-1, j}]],
      ctr = grayTakens[{i, j}, ss],
      new, cop },
    If[Or[Chop[vec] == {1, 0}, Chop[Norm@vec] == 0], Return @ {1, mat}];
    new = Transpose @ {Conjugate @ vec, {-1, 1} * Reverse[vec]};
    (* In order to properly handle the determinant,
       it must be {-1,1}; not {1,-1}. *)
    If[Not @ ctr["Ordered"], new = Reverse[Reverse /@ new]];
    cop = ControlledGate[
      ctr["Control"], 
      Elaborate @ ExpressionFor[new, ctr["Target"]]
     ];
    (* Basis change to the Gray code basis. *)
    new = Transpose @ Permute[Transpose @ Permute[Matrix[cop, ss], gry], gry];
    {cop, mat.new}
   ]


grayTakens::usage = "Finds the minimal set of control qubits when nullifying the jth column element of the ith row using the (j-1)th column element."

grayTakens[{i_Integer, j_Integer}, ss:{__?QubitQ}] := Module[
  { n = Length[ss],
    kk, jj, p, ff, cc, an },
  kk = IntegerToGray[j-2, n];
  jj = IntegerToGray[j-1, n];
  cc = findControls[{i, j}, Range @ n];
  p = First @ FirstPosition[Mod[kk + jj, 2], 1];
  cc = Join[cc, Range[p+1, n]];
  Association[
    "Control" -> Thread[ss[[cc]] -> kk[[cc]]],
    "Target" -> ss[[p]],
    "Ordered" -> OrderedQ @ {kk[[p]], jj[[p]]}
   ]
 ]


findControls::usage = "The workhorce of grayTakens."

findControls[{i_Integer, j_Integer}, ss_List] := Join[ {},
  findControls[{i, j}, Rest @ ss]
 ] /; j <= Power[2, Length[ss]-1]

findControls[{i_Integer, j_Integer}, ss_List] := Join[ {First @ ss},
  findControls[{i, j} - Power[2, Length[ss]-1], Rest @ ss]
 ] /; i > Power[2, Length[ss]-1]

findControls[{i_Integer, j_Integer}, ss_List] := Module[
  { n = Length @ ss,
    kk, jj, p },
  kk = IntegerToGray[j-2, n];
  jj = IntegerToGray[j-1, n];
  p = First @ FirstPosition[Mod[kk + jj, 2], 1];
  ff = Range[p-1];
  If[i >= Power[2, n-p] + 1,
    Part[ss, FirstPosition[kk[[ff]], 1]],
    {}
   ]
 ]

(**** </GrayGivensFactor> ****)


End[]

EndPackage[]
