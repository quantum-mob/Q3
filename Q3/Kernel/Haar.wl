(* -*- mode:math -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ UnitaryTwirling,
  UnitaryTwirling };
{ WeingartenFunction };

Begin["`Private`"]

(**** <UnitaryTwirling> ****)

UnitaryTwirling::usage = "UnitaryTwirling[{n, d}] returns a supermap corresponding to the twirling operation over the Haar measure of the unitary group."

UnitaryTwirling::big = "The numbers n (= ``) and/or d (= ``) are too large. Use UnitaryTwirling[{{\[Ellipsis]}, {\[Ellipsis]}, {\[Ellipsis]}, {\[Ellipsis]}}, {n, d}] instead."

UnitaryTwirling[{n_Integer, d_Integer}] := Module[
  { elm, gmt, cls, mat, wgt },
  elm = GroupElements[SymmetricGroup @ n];
  mat = Map[TheWeylPermutation[{n, d}], elm];
  mat = SparseArray @ Outer[KroneckerProduct, mat, mat, 1];
  (* NOTE: Matrices are all real. *)

  cls = YoungClasses[n];
  cls = KeyMap[WeingartenFunction[#, d]&, cls];
  cls = Flatten @ KeyValueMap[Thread[#2 -> #1] &, cls];
  
  gmt = theInvMultiplicationTable[n];
  wgt = SparseArray[gmt /. cls];
  mat = Total @ Flatten[mat * wgt, 1];
  Supermap @ SparseArray @ ArrayReshape[mat, ConstantArray[Power[d, n], 4]]
] /; If[ 
  (n<4) || (n==4 && d<6) || (n==5 && d<3), True,
  Message[UnitaryTwirling::big, n, d]; False
]

theInvMultiplicationTable::usage = "theInvMultiplicationTable[n] returns the matrix of elements Inverse[g_i]g_j."

theInvMultiplicationTable[n_Integer] := Module[
  { gmt = GroupMultiplicationTable[SymmetricGroup @ n],
    inv },
  inv = Position[gmt, 1];
  inv = SparseArray[Thread[inv -> 1], {1, 1}*n!];
  Transpose[gmt . inv]
]

(**** </UnitaryTwirling> ****)


(**** <UnitaryTwirling> ****)

UnitaryTwirling::usage = UnitaryTwirling::usage <> "\nUnitaryTwirling[{i, k, j, l}, {n, d}] returns the C(i,k;j,l) element of the Choi matrix representing the twirling operation."

UnitaryTwirling[
  idx:{_Integer, _Integer, _Integer, _Integer}, 
  {n_Integer, d_Integer}
] := theUnitaryTwirling[IntegerDigits[idx-1, d, n]+1, {n, d}]

UnitaryTwirling[
  idx:{{__Integer}, {__Integer}, {__Integer}, {__Integer}}, 
  {n_Integer, d_Integer}
] := Module[
  { nn = Power[d, n],
    pp, cm },
  pp = Transpose @ Tuples[idx];
  pp = Union[Transpose @ pp, Transpose @ pp[[{3, 4, 1, 2}]]];
  pp = Select[pp, OrderedQ[Partition[#, 2]]&];
  cm = Map[theUnitaryTwirling[#, {n, d}]&, IntegerDigits[pp-1, d, n] + 1];
  cm = SparseArray[Thread[pp -> cm], {nn, nn, nn, nn}];
  cm += Transpose[cm, {3, 4, 1, 2}]
]

theUnitaryTwirling[{ii_, kk_, jj_, ll_}, {n_Integer, d_Integer}] :=
  0 /; Not @ And[
    YoungContent[ii, d] == YoungContent[jj, d],
    YoungContent[kk, d] == YoungContent[ll, d]
  ]

theUnitaryTwirling[{ii_, kk_, jj_, ll_}, {n_Integer, d_Integer}] :=
  Module[
    { type = YoungContent[kk, d] },
    Factorial[d-1] * Whole[Factorial @ type] / Factorial[n + d -1]
  ] /; Apply[Equal, ii]

theUnitaryTwirling[{ii_, kk_, jj_, ll_}, {n_Integer, d_Integer}] :=
  Module[
    { gg = YoungSubgroup[YoungContent @ ii],
      hh = YoungSubgroup[YoungContent @ kk],
      cc },
    gg = FindPermutation[jj, ii] ** GroupElements[gg];
    hh = FindPermutation[ll, kk] ** GroupElements[hh];
    cc = Outer[Multiply, InversePermutation /@ gg, hh];
    cc = Map[WeingartenFunction[#, {n, d}]&, cc, {2}];
    Total[Flatten @ cc]
  ]

(**** </UnitaryTwirling> ****)


(**** <WeingartenFunction> ****)

WeingartenFunction::usage = "WeingartenFunction[prm, {n, d}] returns the value at permutation prm of the Weingarten function for the symmetric group S(n) and the unitary group U(d).\nWeingartenFunction[type, d] assumes that the permutation belongs to the conjugacy class of cycle decomposition type in the symmmetric group S(n).\nSee Colllins and Śniady (2006)."

WeingartenFunction::len = "The length of permutation vector `` is different from the specified value ``."

WeingartenFunction[n_Integer?Positive, d_Integer?Positive] :=
  AssociationMap[WeingartenFunction[#, d]&, Reverse @ YoungShapes @ n]

WeingartenFunction[class_YoungShape, d_Integer?Positive] := Module[
  { n = YoungDegree[class],
    shp, chr, dimS, dimU },
  shp = YoungShapes[n, d];
  chr = Map[YoungCharacters[#, class]&, shp];
  dimS = Map[YoungTableauCount, shp];
  dimU = Map[WeylTableauCount[#, d]&, shp];
  Total[chr * dimS^2 / dimU] / (n!)^2
]


(* for heuristic purposes *)

WeingartenFunction[prm_List?PermutationListQ, d_Integer?Positive] :=
  WeingartenFunction[CycleDecompositionType @ prm, d]

WeingartenFunction[prm_List?PermutationListQ, {n_Integer, d_Integer?Positive}] :=
  WeingartenFunction[CycleDecompositionType @ prm, d] /;
  If[ Length[prm] == n, True,
    Message[WeingartenFunction::len, prm, n]; False
  ]

WeingartenFunction[cyc_Cycles, {n_Integer, d_Integer?Positive}] :=
  WeingartenFunction[CycleDecompositionType[cyc, n], d]

(**** </WeingartenFunction> ****)

End[]

EndPackage[]
