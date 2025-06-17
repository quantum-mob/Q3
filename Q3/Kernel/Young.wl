(* ::Package:: *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ YoungDiagram, FerrersDiagram };
{ YoungShape, YoungShapes, YoungShapeQ };
{ YoungByte, YoungByteQ };
{ YoungContent, YoungContents };
{ YoungDegree };

{ YoungTranspose, YoungTrim };

{ YoungTableau, YoungTableauQ, YoungTableaux, YoungTableauCount,
  YoungForm };

{ YoungVector, YoungVectorQ };

{ LegacyYoungTableaux };

{ WeylTableaux, WeylTableauCount, WeylTableauQ };

{ GelfandPattern, GelfandPatternQ };
{ GelfandYoungPatterns, GelfandYoungPatternQ };

{ YoungElements, YoungGenerators, YoungSubgroup };

{ GroupCentralizerSize, YoungCentralizerSize,
  GroupClassSize, YoungClassSize,
  GroupClasses, YoungClasses, YoungClassCount,
  GroupCharacters, YoungCharacters };

{ KostkaNumber };
{ InterlaceGraph };

{ Transpositions, PermutationTranspositions,
  InversionVector };

{ YoungDistance };

{ CycleDecompositionType };
{ PermutationForm };

{ PermutationBasis };

{ DominatesQ, Dominates, DominatedBy };

{ YoungPileUp, YoungBratteliDiagram };

{ SpechtBasis, YoungInvariantBasis };

{ RSKMap, TwoLineArray, RowInsertion,
  YoungTableauProduct };

{ TheWeylPermutation };

{ RimHookGraph };

Begin["`Private`"]

(**** <PermutationForm > ***)

PermutationForm::usage = "PermutationForm[cyc] displays permutation cycles cyc in terms of \[Pi].\nPermutationForm[perm] displays perm specified in the permutation list representation in the two-list form."

PermutationForm[Cycles[{}]] := Subscript[\[Pi], 0]

PermutationForm[Cycles[pp_List]] :=
  Row @ Map[Subscript[\[Pi], Row @ #]&, pp]

PermutationForm[{}] = {}

PermutationForm[prm_List?PermutationListQ] := DisplayForm @ RowBox @ {
  "(",
  Grid @ {Range[Length @ prm], prm},
  ")"
}

PermutationForm[expr_Association] := PermutationForm /@ expr

PermutationForm[expr_] := ReplaceAll[ expr,
  { pp:$PermutationSpec :> PermutationForm[pp],
    tt_Transpositions :> PermutationForm[tt] }
]

(**** </PermutationForm > ***)


YoungDiagram::usage = "YoungDiagram[shape] displays shape in a Young diagram.\nYoungDiagram[yt] displays the Young diagram hosting Young tableau yt.\nA Young diagram is a finite collection of boxes, or cells, arranged in left-justified rows, with the row lengths in non-increasing order. Listing the number of boxes in each row gives a partition \[Lambda] of a non-negative integer n, the total number of boxes of the diagram. The Young diagram is said to be of shape \[Lambda], and it carries the same information as that partition.\nA Young diagram is also called a Ferrers diagram, particularly when represented using dots."

YoungDiagram[sh_YoungShape] = sh

YoungDiagram[shape:{___Integer}] :=
  Grid @ Map[Table[Item[" ", Frame->True], #]&, shape]

YoungDiagram[yt:{{___Integer}..}] := YoungDiagram[Length /@ yt]

YoungDiagram[yt_YoungTableau] := YoungShape[yt]


FerrersDiagram::usage = "FerrersDiagram[shape] displays shape in a Ferrers diagram.\nYoungDiagram[yt] displays the Ferrers diagram hosting Young tableau yt.\nA Young diagram is a finite collection of boxes, or cells, arranged in left-justified rows, with the row lengths in non-increasing order. Listing the number of boxes in each row gives a partition \[Lambda] of a non-negative integer n, the total number of boxes of the diagram. The Young diagram is said to be of shape \[Lambda], and it carries the same information as that partition.\nA Young diagram is also called a Ferrers diagram, particularly when represented using dots."

FerrersDiagram[YoungShape[data_List]] := FerrersDiagram[data]

FerrersDiagram[shape:{___Integer}] :=
  Grid @ Map[Table["\[FilledCircle]", #]&, shape]

FerrersDiagram[yt:{{___Integer}..}] := FerrersDiagram[YoungShape @ yt]

FerrersDiagram[yt_YoungTableau] := FerrersDiagram[YoungShape @ yt]


(**** <YoungDegree> ****)

YoungDegree::usage = "YoungDegree[obj] returns the degree of the symmetric group concerning the obj."

YoungDegree[shape_YoungShape] := Total @@ shape

YoungDegree[gp_GelfandPattern] := YoungDegree[YoungShape @ gp]

YoungDegree[tbl_YoungTableau] := YoungDegree[YoungShape @ tbl]

YoungDegree[gp_List?GelfandPatternQ] := YoungDegree[GelfandPattern @ gp]

YoungDegree[tb_List?anyYoungTableauQ] := YoungDegree[YoungTableau @ tb]

(**** </YoungDegree> ****)


(**** <YoungShape> ****)

YoungShape::usage = "YoungShape[{n1,n2,\[Ellipsis],nk}] represents a Young shape.\nYoungShape[tb] returns the shape, i.e., the integer partition of Young tableau tb."

SetAttributes[YoungShape, NHoldAll]

Format[ys:YoungShape[data:{___Integer}]] :=
  Interpretation[YoungDiagram @ data, ys]

YoungShape[GelfandPattern[gp_]] := YoungShape[YoungTrim @ First @ gp]

YoungShape[YoungTableau[tb_]] := YoungShape[Length /@ tb]

YoungShape[gp_List?GelfandPatternQ] := 
  YoungShape[GelfandPattern @ gp] /; gp != {}

YoungShape[tb_List?anyYoungTableauQ] := 
  YoungShape[YoungTableau @ tb] /; tb != {}
(* NOTE: anyYoungTableauQ[{}] gives True. *)

(**** </YoungShape> ****)


YoungShapeQ::usage="YoungShapeQ[shape] returns True if and only if shape is an integer partition, arranged in non-increasing order.\nA Young shape defines a Young diagram."

YoungShapeQ[YoungShape[data_List]] := YoungShapeQ[data]

YoungShapeQ[_] = False

YoungShapeQ[pp:{__Integer?NonNegative}] := Apply[GreaterEqual, pp]
(* NOTE: Must allow 0 since some functions uses 0 in shape specification. *)


(**** <YoungShapes> ****)

YoungShapes::usage = "YoungShapes[n] returns the list of all possible Young shapes for integer n.\nYoungShapes[n, d] returns the list of Young shapes at most d rows.\nYoungShapes[n, spec] with the same spec for IntegerPartitions[n, spec] is allowed.\nYoungShapes[content] returns a list of Young shapes that dominates ReverseSort[content]."

YoungShapes[n_Integer, spec___] := YoungShape /@ IntegerPartitions[n, spec]

YoungShapes[content:{__Integer}] := Select[
  YoungShapes[Total @ content, Length @ content],
  Dominates[ReverseSort @ content]
]

(**** </YoungShapes> ****)


(**** <YoungTrim> ****)

YoungTrim::usage="YoungTrim[shape] trims trailing zeros from shape.\nYoungTrim[tbl] trims trailing {}s from Young tableau tbl."

YoungTrim[YoungTableau[data_]] := YoungTableau[YoungTrim @ data]

YoungTrim[{any___List, {}...}] := {any}


YoungTrim[YoungShape[data_]] := YoungShape[YoungTrim @ data]

YoungTrim[{any___, 0...}] := {any}

(**** </YoungTrim> ****)


YoungTranspose::usage = "YoungTranspose[shape] reflects a partition 'shape' along the main diagonal.\nTransposeTableau[tb] reflects a standard Young tableau 'tb' along the main diagonal, creating a different tableau."

YoungTranspose[YoungShape[data_]] := YoungShape @ YoungTranspose[data]

YoungTranspose[shape:{__Integer}] :=
 Table[LengthWhile[shape, # >= k &], {k, First @ shape}]


YoungTranspose[YoungTableau[data_]] := YoungTableau[YoungTranspose @ data]

YoungTranspose[tb:{{___Integer}..}] := With[
  { new = YoungTranspose[Length /@ tb] },
  Table[tb[[j, i]], {i, Length @ new}, {j, new[[i]]}]
]
(* NOTE: tb does not need to be a semi-standard Young tableau. Any Young-like
   tableau is allowed. This is useful in Schur transform. *)


(**** <YoungByte> ****)

YoungByte::usage = "YoungByte[{b1,b2,\[Ellipsis]}] is a binary representation of an integer partition of n:=b1+b2+\[Ellipsis] with (b1, b2, \[Ellipsis] \[Element] {0, 1}."

(* Returns the degree of the symmetric group. *)
YoungByte /:
YoungDegree[yb_YoungByte] := YoungDegree[YoungShape @ yb]

(* Returns the binary representation of a Young shape. *)
YoungByte @ YoungShape[partition_] := YoungByte @ Fold[
  Join[#1, Append[ConstantArray[1, #2], 0]]&, 
  {},
  Subtractions[Reverse @ YoungTrim @ partition]
]

(* Converts back a binary representation to the normal form. *)
YoungByte /:
YoungShape[yb_YoungByte] := Module[
  { byte = First[YoungTrim @ yb] },
  byte = SequenceReplace[byte, {a:(Except[0]...), 0} -> {a}];
  YoungShape @ Reverse @ Accumulate @ Map[Total, byte]
]

(* Removes leading 0s and trailing 1s in the binary representation. *)
YoungByte /:
YoungTrim @ YoungByte[{0..., Shortest[any___], 1...}] := 
  YoungByte @ {any}

YoungByte /:
YoungTranspose @ YoungByte[byte_] :=
  YoungByte @ Reverse @ ReplaceAll[byte, {0 -> 1, 1 -> 0}]

(**** </YoungByte> ****)


(**** <YoungTableauQ> ****)

YoungTableauQ::usage = "YoungTableauQ[tb] yields True if tb represents a standard Young tableau and False otherwise."

YoungTableauQ[{}] = True

YoungTableauQ[tb_?anyYoungTableauQ] := TrueQ[
  And @@ Join[
    List[DuplicateFreeQ @ Flatten @ tb],
    Less @@@ tb,
    Less @@@ YoungTranspose[tb]
  ]
]

YoungTableauQ[_] = False


anyYoungTableauQ::usage = "anyYoungTableauQ[tb] yields True if tb represents a Young tableau (not necessarily semi-standard) and False otherwise."

anyYoungTableauQ[{}] = True

anyYoungTableauQ[tb:{{___Integer}..}] := Apply[GreaterEqual, Length /@ tb]
(* NOTE: It must be ___Integer (not __Integer) so as to allow trailing {}s;
   see YoungTrim. *)

anyYoungTableauQ[_] = False

(**** </YoungTableauQ> ****)


(**** <YoungTableau> ****)

YoungTableau::usage = "YoungTableau[data] represents a Young tableau.\nYoungTableau[gp] converts Gelfand pattern gp to Young tableau."

SetAttributes[YoungTableau, NHoldAll]

Format[tbl:YoungTableau[data:{{___}..}]] :=
  Interpretation[YoungForm @ data, tbl]

YoungTableau /:
Equal[YoungTableau[a_], YoungTableau[b_]] := Equal[a, b]

(**** </YoungTableau> ****)


(**** <YoungForm> ****)

YoungForm::usage = "YoungForm[tb] displays Young tableau tb in the conventional form."

YoungForm::notyt = "`` is not a Young tableau."

YoungForm[yt_YoungTableau] = yt

YoungForm[tb:{{___}..}] :=
  Grid @ Map[Item[#, Frame->True]&, tb, {2}]

YoungForm[data_] := (
  Message[YoungForm::notyt, data];
  data
)

(**** </YoungForm> ****)


(**** <YoungVector> ****)

YoungVector::usage = "YoungVector[{r1,r2,r3,\[Ellipsis],rn}] encodes a standard Young tableau of degree n such that the cell numbered k appears in the rkth row. Always r1 = 1, and it may be omitted as sometimes adopted for convention. It also refers to a path in the Bratteli diagram for the canonical tower of subgroups of the symmetric group."
(* Kawano & Sekigawa (2016) *)

Format[YoungVector[pp:{___Integer?Positive}]] := 
 Interpretation[MatrixForm @ {pp}, YoungVector @ pp]

YoungVector @ YoungTableau[data_] := Module[
  { vec = Flatten @ MapIndexed[#1 -> First[#2] &, data, {2}] },
  YoungVector[Values @ KeySort @ vec]
]

YoungVector /:
YoungTableau @ YoungVector[pp:{___Integer}] :=
 YoungTableau[Values @ KeySort @ PositionIndex @ pp]

YoungVector /:
YoungShape @ YoungVector[pp_] := 
  YoungShape[Values @ KeySort @ Counts @ pp]

YoungVector /:
YoungDegree[YoungVector[pp_]] := Length[pp]


YoungVectorQ::usage = "YoungVectorQ[{r1,r2,\[Ellipsis],rn}] returns True if the list represents a valid Young vector."

YoungVectorQ[pp:{___Integer?Positive}] := And[
  OrderedQ[Reverse @ KeySort @ Counts @ pp],
  Sequence @@ Thread[pp <= Range[Length @ pp]]
]

YoungVectorQ[_] = False

(**** </YoungVector> ****)


(**** <YoungTableauCount> ****)

YoungTableauCount::usage = "YoungTableauCount[shape] uses the hook length formula to count the number of standard Young tableaux of 'shape'.\nYoungTableauCount[n] gives the total number of standard Young tableaux for all partitions of integer 'n'.\nBorrowed from NumberOfTableaux in Combinatorica package."

YoungTableauCount[pp_List?YoungShapeQ] :=
  YoungTableauCount[YoungShape[pp]]

YoungTableauCount[YoungShape[pp_]] := Module[
  { qq = YoungTranspose[pp],
    j, k },
  Factorial[Total @ pp] /
    Product[
      pp[[j]] + qq[[k]] - j - k + 1,
      {j, Length[pp]},
      {k, pp[[j]]}
    ]
]

YoungTableauCount[n_Integer] :=
  Total @ Map[YoungTableauCount, YoungShapes @ n]

(**** <YoungTableauCount> ****)


(**** <theKetFormat> ****)
(* for YoungRegularBasis, etc. *)

theKetFormatQ[_Cycles] = True

theKetFormat[cyc_Cycles] := PermutationForm[cyc]

(**** </theKetFormat> ****)


(**** <YoungSubgroup> ****)

YoungSubgroup::usage = "YoungSubgroup[content] returns the Young subgroup with content of the symmetric group of degree n:=Total[content]."

YoungSubgroup[shape_YoungShape] :=
  YoungSubgroup[First @ shape]

YoungSubgroup[content:{__Integer}] :=
  PermutationGroup[YoungGenerators @ content]

(**** </YoungSubgroup> ****)


(**** <YoungGenerators> ****)

YoungGenerators::usage = "YoungGenerators[content] returns a generating set of the Young subgroup with content of the symmetric group of degree n:=Total[content].\nYoungGenerators[n] is an alias of GroupGenerators[SymmetricGroup[n]]."

YoungGenerators::negative = "Negative value is not allowed as a part of content."

YoungGenerators[n_Integer] :=
  GroupGenerators[SymmetricGroup @ n]

YoungGenerators[shape_YoungShape] :=
  YoungGenerators[First @ shape]

YoungGenerators[content:{__Integer?NonNegative}] := Module[
  { gg },
  gg = Select[TakeList[Range[Total @ content], content], Length[#] > 1 &];
  gg = Function[set, Union @ {Cycles @ {Take[set, 2]}, Cycles @ {set}}] /@ gg;
  Flatten[gg]
] /; If[
  AllTrue[content, NonNegative], True,
  Message[YoungGenerators::negative, content]; False
]

(**** </YoungSubgroup> ****)


(**** <YoungElements> ****)

YoungElements::usage = "YoungElements[content] returns a list of elements in the Young subgroup with content of the symmetric group of degree n:=Total[content].\nYoungElements[n] and YoungElements[n, {k1, k2, \[Ellipsis]}] are aliases of GroupElements[SymmetricGroup[n]] and GroupElements[SymmetricGroup[n], {k1, k2, \[Ellipsis]}], respectively."

YoungElements::negative = "Negative value is not allowed as a part of content."

YoungElements[n_Integer] :=
  GroupElements[SymmetricGroup @ n]

YoungElements[n_Integer, kk:{___Integer}] :=
  GroupElements[SymmetricGroup @ n, kk]

YoungElements[shape_YoungShape] :=
  YoungElements[First @ shape]

YoungElements[content:{__Integer?NonNegative}] := 
  GroupElements[YoungSubgroup @ content]

YoungElements[content:{__Integer?NonNegative}, kk:{___Integer}] :=
  GroupElements[YoungSubgroup @ content, kk]

(**** </YoungSubgroup> ****)


(**** <GroupCharacters> ****)

GroupCharacters::usage = "GroupCharacters[group] returns the table of characters of the irreducible representations of 'group'. The characters of each irreducible representation is stored in a row vector.\nGroupCharacters[group, irr] gives a list of the characters of the irreducible representation 'irr'.\nGroupCharacters[group, irr, class] returns the character of the irreducible representation 'irr' of 'group' evaluated at the conjugacy class 'class'.\nFor a symmetric group, both irreducible representation and class are specified by integer partitions."

GroupCharacters[SymmetricGroup[n_Integer]] :=
  YoungCharacters[n] /; n > 0

GroupCharacters[SymmetricGroup[n_Integer], irr_List?YoungShapeQ] :=
  YoungCharacters[irr] /; Total[First @ irr] == n

GroupCharacters[SymmetricGroup[n_Integer], irr_YoungShape, class_YoungShape] :=
  YoungCharacters[irr, class] /;
  Total[First @ irr] == Total[First @ class] == n


GroupCharacters[grp:{_String, _Integer}] :=
  FiniteGroupData[grp, "CharacterTable"]

(**** </GroupCharacters> ****)


(**** <YoungCharacters> ****)

YoungCharacters::usage = "YoungCharacters[n] returns the character table of the symmetric group of degree n.\nYoungCharacters[irr] returns a list of characters of conjugacy classes in irreducible representation 'irr'.\nYoungCharacters[irr, class] returns the character of 'class' in irreducible representation 'irr'."

YoungCharacters[n_Integer] := With[
  { shapes = YoungShapes[n] },
  Outer[YoungCharacters, shapes, Reverse @ shapes]
]
(* NOTE: The rows of the character table is arranged as YoungShapes[n]. 
  The columns are arranged as Reverse[YoungShapes[n]]. *)

YoungCharacters[irrep_YoungShape] := Map[
  YoungCharacters[irrep, #]&,
  Reverse[YoungShapes @ YoungDegree @ irrep]
]
(* NOTE: The rows of the character table is arranged as YoungShapes[n]. 
  The columns are arranged as Reverse[YoungShapes[n]]. *)

YoungCharacters[irrep_YoungShape, YoungShape[type_]] :=  
  yngMurnaghanNakayama[YoungByte @ irrep, type]


yngMurnaghanNakayama::usage = "yngMurnaghanNakayama[binaryShape, type] returns the character of the conjugacy class of 'type' in the irreducible representation of 'binaryShape' of the symmetric group, using the MNinner algorithm from Bernstein (2004) based on the Murnaghan-Nakayama rule."

yngMurnaghanNakayama[binaryShape_YoungByte, {}] = 1

yngMurnaghanNakayama[binaryShape_YoungByte, type_List] := 
  0 /; Length[First @ binaryShape] < First[type]

yngMurnaghanNakayama[binaryShape_YoungByte, type_List] := Module[
  { shp = First[binaryShape],
    len = First[type],
    chr = 0,
    sgn },
  sgn = IntegerParity @ Count[Take[shp, len-1], 0];
  Do[
    If[ shp[[i]] != shp[[i+len-1]], sgn = -sgn ];
    If[ shp[[{i, i+len}]] == {1, 0},
      shp[[{i, i+len}]] = shp[[{i+len, i}]];
      chr += sgn * yngMurnaghanNakayama[YoungByte @ shp, Rest @ type];
      shp[[{i, i+len}]] = shp[[{i+len, i}]];
    ],
    {i, Length[shp] - len}
  ];
  chr
]

(**** </YoungCharacters> ****)


(**** <RimHookGraph> ****)

RimHookGraph::usage = "RimHookGraph[irrep, class] returns a graph of Young shapes connected by revmoving a rim hook. Both irreducible representation irrep and conjugacy class are specified in YoungShape.\nThis function is just to heuristically illustrate the Murnaghan-Nakayama rule for computing the characters of the symmetric group."

RimHookGraph[shape_YoungShape, type_YoungShape, opts:OptionsPattern[Graph]] := 
  Module[
    { edges = yngRimHookEdges[YoungByte @ shape, First @ type] },
    Graph[ Union @ edges, opts,
      VertexLabels -> "Name",
      EdgeLabels -> "EdgeTag",
      GraphLayout -> "LayeredDigraphEmbedding",
      ImageSize -> Medium
    ]
  ]

(* NOTE: This yngRimHookEdges may be combined with yngMurnaghanNakayama. But I keep them as they are because yngRimHookEdges is just for heuristic purposes and yngMurnaghanNakayama is for efficient calculation of characters. *)
yngRimHookEdges[YoungByte @ {}, _] = {}

yngRimHookEdges[binaryShape_YoungByte, {}] = { 
  DirectedEdge[YoungShape @ binaryShape, 1, 1] 
}

yngRimHookEdges[binaryShape_YoungByte, type_List] := { 
  DirectedEdge[YoungShape @ binaryShape, 0, 1] 
} /; Length[First @ binaryShape] < First[type]

yngRimHookEdges[byte_YoungByte, type_List] := Module[
  { bin = First[byte],
    len = First[type],
    edg = {},
    sgn, new },
  sgn = IntegerParity @ Count[Take[bin, len-1], 0];
  Do[
    If[ bin[[i]] != bin[[i+len-1]], sgn = -sgn ];
    If[ bin[[{i, i+len}]] == {1, 0},
      new = bin;
      new[[{i, i+len}]] = bin[[{i+len, i}]];
      new = YoungTrim[YoungByte @ new];
      edg = Join[ edg,
        { DirectedEdge[YoungShape @ byte, YoungShape @ new, sgn] },
        yngRimHookEdges[new, Rest @ type]
      ]
    ],
    {i, Length[bin] - len}
  ];
  If[ edg == {},
    {DirectedEdge[YoungShape @ byte, 0, 1]},
    Flatten[edg]
  ]
]

(**** </RimHookGraph> ****)


(**** <GroupClasses> ****)

GroupClasses::usage = "GroupClasses[group] returns the list of conjugacy classes of group."

GroupClasses[SymmetricGroup[n_Integer]] :=
  YoungClasses[n] /; n > 0

GroupClasses[SymmetricGroup[n_Integer], irr:(_YoungShape|_List?YoungShapeQ)] :=
  YoungClasses[irr] /; Total[irr] == n

(**** </GroupClasses> ****)


YoungClassCount::usage = "YoungClassCount[n] returns the number of conjugacy classes of the symmetric group of degree n."

YoungClassCount[n_Integer] := PartitionsP[n]


(**** <YoungClasses> ****)

YoungClasses::usage = "YoungClasses[n] returns an association of conjugacy classes of the symmetric group of degree n.\nEach key of the returned association refers to the 'cycle decomposition type' of permutations in the class.\nConjugacy classes in the symmetric group of degree n are uniquely determined by the cycle decomposition type of permutations. Hence, like irreducible representations, conjugacy classes in the symmetric group are in one-to-one correspondence to partitions of n."

YoungClasses[n_Integer] := With[
  { elm = GroupElements[SymmetricGroup @ n] },
  KeyMap[    
    YoungShape,
    KeySort[
      ReplaceAll[
        GroupBy[elm, theCycleDecompositionType[n]], 
        Thread[elm -> Range[Length @ elm]]
      ], 
      LexicographicOrder
    ]
  ]
]
(* NOTE: The keys are arranged so that they correspond to the columns of FiniteGroupData[{"SymmetricGroup", n}, "CharacterTable"]. The order is the same as Reverse[YoungShapes[n]] but not as ReverseSort[YoungShapes[n]]. *)

(**** </YoungClasses> ****)


(**** <CycleDecompositionType> ****)

CycleDecompositionType::usage = "CycleDecompositionType[prm, n] returns the cycle decomposition type of permutation prm of n elements.\nCycleDecompositionType[n] is an operator form of CycleDecompositionType to be applied to permutations.\nA cycle decomposition of a permutation is an expression of the permutation as a product of disjoint cycles, where each cycle represents a cyclic rearrangement of elements. This decomposition is unique up to the order of the cycles and cyclic rotations within each cycle. The cycle decomposition type of a permutation is a list of the lengths of the cycles in its cycle decomposition. By convention, a cycle decomposition type is arranged in decreasing order, and is a partition of n."

CycleDecompositionType[n_Integer][any_] :=
  CycleDecompositionType[any, n]

CycleDecompositionType[prm_List?PermutationListQ] :=
  CycleDecompositionType[PermutationCycles @ prm, Length @ prm]

CycleDecompositionType[cyc_Cycles, n_Integer] :=
  YoungShape @ theCycleDecompositionType[n] @ cyc

(* NOTE: This version without the YoungShape wrapper is required for YoungClasses. *)
theCycleDecompositionType[n_Integer][Cycles[spec_]] := With[
  { body = ReverseSort[Length /@ spec] },
  Join[body, Table[1, n-Total[body]]]
]

(**** </CycleDecompositionType> ****)


GroupClassSize::usage = "GroupGlassSize[group, class] returns the number of elements in the conjugacy class 'class'."

GroupClassSize[SymmetricGroup[n_Integer], class_List?YoungShapeQ] :=
  YoungClassSize[class] /; n > 0

GroupClassSize[group_, g_] :=
  GroupOrder[group] / GroupCentralizerSize[group, g]


(**** <YoungClassSize> ****)

YoungClassSize::usage="YoungClassSize[class] returns the number of elements in the conjugacy class 'class' in SymmetricGroup[n].\nThe conjugacy class is specified by a partition of integer 'n'.\nThe inverse of YoungClassSize[class] = GroupOrder[SymmetricGroup[n]] / YoungCentralizerSize[class]; see, e.g., Sagan, The Symmetric Group (Springer, 2001) Section 1.1."

YoungClassSize[n_Integer] :=
  Factorial[n] / YoungCentralizerSize[n]

YoungClassSize[class_YoungShape] :=
  Factorial[YoungDegree @ class] / YoungCentralizerSize[class]

YoungClassSize[class_List?YoungShapeQ] :=
  YoungClassSize[YoungShape @ class]

(**** </YoungClassSize> ****)


GroupCentralizerSize::usage = "GroupCentralizerSize[group, g] returns the number of elements in the conjugacy class containing the element 'g' of the group 'group'."

GroupCentralizerSize[SymmetricGroup[n_Integer], class_List?YoungShapeQ] :=
  YoungCentralizerSize[class] /; n > 0

GroupCentralizerSize[group_, g_] :=
  GroupOrder @ GroupCentralizer[group, g]


(**** <YoungCentralizerSize> ****)

YoungCentralizerSize::usage = "YoungCentralizerSize[class] returns the size of the centralizer of an element in conjugacy class, which is specified by the corresponding Young shape.\nNot that YoungCentralizerSize[class] = GroupOrder[SymmetricGroup[n]] / YoungClassSize[class]."

YoungCentralizerSize[n_Integer] :=
  Map[YoungCentralizerSize, Reverse @ YoungShapes @ n]

YoungCentralizerSize[class_List?YoungShapeQ] :=
  YoungCentralizerSize[YoungShape @ class]

YoungCentralizerSize[YoungShape[class_List]] :=
  Whole[Factorial @ Counts @ class] * Whole[YoungTrim @ class];

(**** </YoungCentralizerSize> ****)


(**** <KostkaNumber> ****)

KostkaNumber::usage = "KostkaNumber[shape, content] returns the Kostka nunber, i.e., the number of Weyl tableaux of shape and content.\nKostkaNumber[n] returns a matrix of Kostka numbers of degree n."

KostkaNumber[n_Integer?Positive] := With[
  { shp = YoungShapes[n] },
  Outer[KostkaNumber, shp, shp]
]
(* TODO: There is a room for improvement here. *)

KostkaNumber[shape_List?YoungShapeQ, any_] :=
  KostkaNumber[YoungShape @ shape, any]

KostkaNumber[any_, content_List] :=
  KostkaNumber[any, YoungShape @ YoungTrim @ ReverseSort @ content]

KostkaNumber[All, content_YoungShape] :=
  Map[KostkaNumber[#, content]&, YoungShapes @ YoungDegree @ content]

KostkaNumber[shape_YoungShape, All] :=
  Map[KostkaNumber[shape, #]&, YoungShapes @ YoungDegree @ shape]


KostkaNumber[shape_YoungShape, shape_YoungShape] = 1

KostkaNumber[shape_YoungShape, YoungShape@{}] = 0

KostkaNumber[shape_YoungShape, content_YoungShape] := 0 /;
  YoungDegree[shape] != YoungDegree[content]

KostkaNumber[shape_YoungShape, content_YoungShape] := 0 /;
  Not @ DominatesQ[First @ shape, First @ content]

(* Pieri rule *)
KostkaNumber[shape_YoungShape, content_YoungShape] := Module[
  { new = yngInterlaces[shape],
    rst = Rest /@ content },
  Total @ Map[KostkaNumber[#, rst]&, new]
]


yngInterlaces::usage = "yngInterlaces[shape] returns a list of Young shapes obtained from removing zero or one cells from each column of shape."
(* Section 3.2.1 in Bacon et al. (2017a) *)

yngInterlaces[YoungShape[shape_]] := Module[
  { del = Subtractions[Reverse @ shape] },
  del = Reverse /@ Tuples[Range[0, #] & /@ del];
  Map[YoungTrim @ YoungShape[shape - #] &, del]
]

(**** </KostkaNumber> ****)


(**** <InterlaceGraph> ****)

InterlaceGraph::usage = "InterlaceGraph[shape, d] returns a graph of Young shapes obtained from removing zero or one cells in each column of shape and consecutively. Illustrates the Gelfand-Zetlin basis of the unitary group U(d)."
(* Section 3.2.1 in Bacon et al. (2017a) *)

InterlaceGraph[shape_YoungShape, d_Integer, opts:OptionsPattern[Graph]] :=
  Module[
    { edges = yngInterlaceEdges[shape, d] },
    Graph[ edges, opts,
      (* GraphLayout -> "LayeredEmbedding", *)
      VertexLabels -> "Name",
      ImageSize -> Medium
    ]
  ]

yngInterlaceEdges[shape_YoungShape, 0] = {}

yngInterlaceEdges[shape_YoungShape, d_Integer] := Module[
  { new },
  new = Select[yngInterlaces @ shape, 0 < Length[First @ #] < d &];
  Union @ Join[
    Thread @ DirectedEdge[shape, new],
    Flatten @ Map[yngInterlaceEdges[#, d-1]&, new]
  ]
]

(**** </InterlaceGraph> ****)


(**** <YoungTableaux> ****)

YoungTableaux::usage = "YoungTableaux[shape] constructs all standard Young tableaux of 'shape'.\nYoungTableaux[n] constructs all standard Young tableaux of rank n."

Options[YoungTableaux] = {"LexicographicOrder" -> False}

YoungTableaux[shape:{___Integer}, opts___?OptionQ] :=
  YoungTableaux[YoungShape @ shape, opts]

YoungTableaux[shape_YoungShape, OptionsPattern[]] := With[
  { result = YoungTableau /@ GelfandYoungPatterns[shape] },
  If[OptionValue["LexicographicOrder"], Reverse @ result, result, result]
]
(* NOTE: Since v3.0, based on GelfandYoungPatterns.
   Now, the resulting list is not in lexicographic order and consistent with
   SchurBasis. *)

YoungTableaux[n_Integer?Positive, opts___?OptionQ] :=
  Catenate @ Map[YoungTableaux[#, opts]&, IntegerPartitions @ n]

(**** </YoungTableaux> ****)


(**** <LegacyYoungTableaux> ****)

LegacyYoungTableaux::usage = "LegacyYoungTableaux[shape] constructs all standard Young tableaux of 'shape' specified by an integer partition using the method in the legacy Combinatorica package.\nLegacyYoungTableaux[n] constructs all standard Young tableaux of rank n."

LegacyYoungTableaux[sh:{___Integer}] :=
  LegacyYoungTableaux[YoungShape @ sh]

LegacyYoungTableaux[s_YoungShape] :=
  NestList[nextYoungTableau, lastYoungTableau[s], YoungTableauCount[s]-1]

LegacyYoungTableaux[n_Integer?Positive] :=
  Catenate @ Map[LegacyYoungTableaux, YoungShapes @ n]

(* NOTE: This is the FIRST Young tableau for LegacyYoungTableaux, which adopts a different lexicographic oder. See the Details section of GelfandOrder. *)
lastYoungTableau::usage = "lastYoungTableau[p] constructs the last standard Young tableau of shape p."

lastYoungTableau[data_List?YoungShapeQ] :=
  lastYoungTableau[YoungShape @ data]

lastYoungTableau[shape_YoungShape] :=
  YoungTranspose @ firstYoungTableau @ YoungTranspose[shape]

(* NOTE: This is the LAST Young tableau for LegacyYoungTableaux, which adopts a different lexicographic order. See the Details section of GelfandOrder. *)
firstYoungTableau::usage = "firstYoungTableau[p] constructs the first Young tableau of shape p."

firstYoungTableau[data_List?YoungShapeQ] :=
  firstYoungTableau[YoungShape @ data]

firstYoungTableau[YoungShape[shape_]] :=
  YoungTableau @ TakeList[Range @ Total @ shape, shape]


nextYoungTableau::usage = "nextYoungTableau[tb] gives the standard Young tableau of the same shape as tb, following tb in the COLUMN-WISE lexicographic order."

nextYoungTableau[data_List?YoungShapeQ] :=
  nextYoungTableau[YoungShape @ data]

(* NOTE: LegacyYoungTableaux adopts the lexicographic odering. See the Details section of GelfandOrder. *)
nextYoungTableau[YoungTableau[tb_]] := Module[
  { yy, shp, row, val, new },

  yy = Values @ KeySort @ Flatten @ MapIndexed[(#1->First[#2])&, tb, {2}];
  If[LessEqual @@ yy, Return @ lastYoungTableau @ YoungShape[tb]];

  val = 1 + Length[First @ Split[yy, LessEqual]];
  row = First @ FirstPosition[tb, val];
  
  shp = Length /@ DeleteCases[tb, k_/;k>val, {2}];
  row = First @ Last @ Position[shp, shp[[row+1]]];
  shp[[row]]--;

  new = First @ lastYoungTableau[YoungShape @ shp];
  If[ Length[new] < row,
    new = Append[new, {val}],
    new[[row]] = Append[new[[row]], val]
  ];

  new = Flatten @ MapIndexed[(#2->#1)&, new, {2}];
  YoungTableau @ ReplacePart[tb, new]
]

(**** </LegacyYoungTableaux> ****)


TheWeylPermutation::usage = "TheWeylPermutation[prm, {n, d}] returns the matrix representation of permutation prm on V\[CircleTimes]\[Ellipsis]\[CircleTimes]V.\nTheWeylPermutation[{n, d}] is an operator form of TheWeylPermutation to be applied to permutations.\nTheWeylPermutation may be regarded as a generalization of PermutationMatrix."

TheWeylPermutation[{n_Integer, d_Integer}][prm_] :=
  TheWeylPermutation[prm, {n, d}]

TheWeylPermutation[prm:(_Cycles|_?PermutationListQ), {n_Integer, d_Integer}] :=
  Module[
    { kk = Range[n],
      pp, tt, id },
    id = One[Power[d, n]];
    id = Tensorize[id, ConstantArray[d, 2*n]];
    pp = Permute[2*kk, prm];
    tt = Transpose[id, Riffle[2*kk-1, pp]];
    TensorFlatten[tt]
  ]


(**** <Permutation> ****)

Permutation::usage = "Permutation[cyc,{s1,s2,\[Ellipsis]}] represents the permutation operator acting on species {s1,s2,\[Ellipsis]}."

Permutation::cyc = "`` does not represent a valid permutation in disjoint cyclic form. See PermutationCyclesQ."

AddElaborationPatterns[_Permutation]

Format[op:Permutation[cyc_Cycles, ss:{__?SpeciesQ}]] :=
  Interpretation[Permutation[PermutationForm @ cyc, ss], op]


Permutation[prm_?PermutationListQ, ss:{__?SpeciesQ}] :=
  Permutation[PermutationCycles @ prm, FlavorCap @ ss]


Permutation[Cycles[{}], qq:{__?SpeciesQ}] := 1

Permutation[cyc_Cycles, ss:{__?SpeciesQ}] :=
  Permutation[cyc, FlavorCap @ ss] /;
  Not[FlavorCapQ @ ss]


Permutation /: Dagger[op_Permutation] = Conjugate[op] (* fallback *)

Permutation /:
Dagger @ Permutation[cyc_, ss:{__?SpeciesQ}] :=
  Permutation[InversePermutation[cyc], ss]


Permutation /: Elaborate[op_Permutation] = op (* fallback *)

Permutation /:
Elaborate @ Permutation[cyc_?PermutationCyclesQ, ss:{__?SpeciesQ}] :=
  With[
    { bs = Basis @ ss },
    Elaborate @ Total @ Map[Dyad[KetPermute[#, cyc, ss], #, ss]&, bs]
  ]
(* NOTE: Here, _?PermutationCyclesQ cannot be replaced by
   $PermutationSpec because of HoldPattern. *)


Permutation /:
Matrix[Permutation[prm_Cycles, ss:{__?SpeciesQ}]] := 
  TheWeylPermutation[prm, {Length @ ss, Dimension @ First @ ss}]

Permutation /:
Matrix[
  op:Permutation[_Cycles, ss:{__?SpeciesQ}],
  rr:{__?SpeciesQ}
] := MatrixEmbed[Matrix @ op, ss, rr]

Permutation /: (* fallback *)
Matrix[op_Permutation, rest___] := op * Matrix[1, rest]


Permutation /:
Multiply[ pre___,
  ops:Repeated[Permutation[_, qq:{__?SpeciesQ}], {2, Infinity}],
  post___ ] := Multiply[ pre,
    Permutation[PermutationProduct @@ Reverse[First /@ {ops}], qq],
    post ]


Permutation /:
Multiply[ pre___,
  Permutation[spec_, qq:{__?SpeciesQ}], v_Ket,
  post___ ] :=
  Multiply[pre, KetPermute[v, spec, qq], post]

Permutation /:
Multiply[ pre___,
  v_Bra, Permutation[spec_, qq:{__?SpeciesQ}],
  post___ ] :=
  Multiply[pre, Dagger @ KetPermute[Dagger @ v, spec, qq], post]

Permutation /:
Multiply[ pre___,
  Permutation[spec_, qq:{__?SpeciesQ}],
  Dyad[a_Association, b_Association],
  post___ ] := Multiply[ pre,
    Dyad[
      Join[a, AssociationThread[Keys[a] -> Permute[Lookup[a, qq], spec]]],
      b ],
    post ] /; ContainsAll[Keys @ a, FlavorCap @ qq]

Permutation /:
Multiply[ pre___,
  Dyad[a_Association, b_Association],
  Permutation[spec_, qq:{__?SpeciesQ}],
  post___ ] := Multiply[ pre,
    Dyad[ a,
      Join[b, AssociationThread[Keys[b] -> Permute[Lookup[b, qq], spec]]] ],
    post ] /; ContainsAll[Keys @ b, FlavorCap @ qq]

(**** </Permutation> ****)


(**** <Cycles> ****)

HoldPattern @ NonCommutativeQ[ _Cycles ] = True

(***
  Group multiplication of the symmetric group. 
  ***)

HoldPattern @
  Multiply[pre___, op_Cycles, more__Cycles, post___] :=
  Multiply[pre, PermutationProduct @@ Reverse[{op, more}], post]
  
(*** 
  Young's normal representation.
  See also YoungNormalRepresentation. 
  ***)

HoldPattern @
  Multiply[pre___, op_Cycles, Ket[ytx:{__YoungTableau}], post___] :=
  Multiply[pre, KetPermute[Ket[ytx], op], post]
(* NOTE: Notice '__' in ytx, with op acting on all SYTs in ytx. *)
  
HoldPattern @ Multiply[ pre___,
  CircleTimes[ops__Cycles], Ket[ytx:{__YoungTableau}], post___ ] :=
  Multiply[ pre,
    CircleTimes @@ MapThread[KetPermute, {Ket /@ List /@ ytx, {ops}}],
    post ]

(***
  The left regular reprepsentation of the symmetric group. 
  See also YoungLeftRepresentation.
  ***)

HoldPattern @
  Multiply[pre___, op_Cycles, Ket[cc:{__Cycles}], post___] :=
  Multiply[pre, Ket @ Multiply[op, cc], post]
(* NOTE: Notice '__' in cc, with op acting on all Cycles in cc. *)
  
HoldPattern @ Multiply[ pre___,
  CircleTimes[ops__Cycles], Ket[cc:{__Cycles}], post___ ] :=
  Multiply[pre, Ket @ Multiply[{ops}, cc], post]
  
(**** </Cycles> ****)


(**** <KetPermute> ****)

KetPermute::usage = "KetPermute[vec, perm] returns a new state vector where each Ket[\[Ellipsis]] in state vector vec is replaced by a new one with the logical values permuted according to permutation perm.\nKetPermute[vec, perm, {q1, q2, \[Ellipsis]}] returns a new state vector permuting the values of the particles q1, q2, \[Ellipsis] in each Ket[<|\[Ellipsis]|>] in state vector vec according to permutation perm.\nThe parameter perm may be a group such as SymmetricGroup, PermutationGroup, AlternatingGroup, or a list of Cycles, where a list of state vectors are returned after applying all elements of the group or list."

$PermutationSpec = Alternatives[_?PermutationListQ, _?PermutationCyclesQ]

$PermutationGroups = Alternatives @@ Blank /@ {
  SymmetricGroup, AlternatingGroup, PermutationGroup, CyclicGroup
}

anyPermutationSpecQ[spec:$PermutationSpec] := True

anyPermutationSpecQ[spec:{$PermutationSpec ..}] := True

anyPermutationSpecQ[spec:$PermutationGroups] := True

anyPermutationSpecQ[_] = False


(* special case *)

KetPermute[expr_, {}] := expr

KetPermute[expr_, Cycles[{}]] := expr

KetPermute[expr_, {}, {__?SpeciesQ}] := expr

KetPermute[expr_, Cycles[{}], {__?SpeciesQ}] := expr


(* For Specht basis and Young's normal representation *)
(* See Sagan (2001, Section 2.7 and Exercise 2.11) and Krovi (2019). *)
(* NOTE: Young's normal representation should be distinguished from
   Young's natural or seminormal representation. *)

KetPermute[Ket[{yt_YoungTableau}], Cycles @ {{x_, y_}}] := Module[
  { xx = FirstPosition[First @ yt, x],
    yy = FirstPosition[First @ yt, y],
    dd, tt },
  Which[
    First[xx] == First[yy], Ket[{yt}],
    Last[xx] == Last[yy], -Ket[{yt}],
    True,
    dd = 1 / YoungDistance[yt, {x, y}];
    tt = ReplaceAll[yt, {x -> y, y -> x}];
    Ket[{yt}] * dd + Ket[{tt}] * Sqrt[1-dd^2]
  ]
] /; x+1 == y


KetPermute[v:Ket[{_YoungTableau}], cyc_Cycles] :=
  KetPermute[v, PermutationList @ cyc]

KetPermute[Ket[{yt_YoungTableau}], prm_List?PermutationListQ] := Module[
  { cc = adjacentTranspositions[prm] },
  cc = Map[Cycles[{{#, #+1}}]&, cc];
  Garner @ Fold[KetPermute, Ket @ {yt}, cc]
]

KetPermute[Ket[yy:{_YoungTableau, __YoungTableau}], cc_] :=
  CircleTimes @@ Map[KetPermute[#, cc]&, Ket /@ List /@ yy]

(* for Pauli Kets *)

KetPermute[Ket[ss_List], spec:$PermutationSpec] :=
  Ket @ Permute[ss, spec]

KetPermute[Ket[ss_List], group:$PermutationGroups] :=
  Ket /@ Permute[ss, group]


(* for labelled Kets *)

KetPermute[v:Ket[_Association], spec:$PermutationSpec, ss:{__?SpeciesQ}] :=
  With[
    { vv = Permute[v @ ss, spec] },
    Ket[v, ss -> vv]
  ]

KetPermute[v:Ket[_Association], spec:{$PermutationSpec..}, ss:{__?SpeciesQ}] :=
  Module[
    { vv = v[ss] },
    vv = Map[Permute[vv, #]&, spec];
    Map[ Ket[v, ss -> #]&, vv ]
  ]

KetPermute[v:Ket[_Association], group:$PermutationGroups, ss:{__?SpeciesQ}] :=
  With[
    { vv = Permute[v @ ss, group] },
    Map[ Ket[v, ss -> #]&, vv ]
  ]


(* multiple permutations *)

KetPermute[v_Ket, spec:{$PermutationSpec..}] :=
  Map[KetPermute[v, #]&, spec]

KetPermute[v:Ket[_Association], spec:{$PermutationSpec..}, ss:{__?SpeciesQ}] :=
  Map[KetPermute[v, #, ss]&, spec]


(* general expressions *)

KetPermute[expr_, spec_?anyPermutationSpecQ] :=
  ReplaceAll[expr, v_Ket :> KetPermute[v, spec]] /;
  Not @ FreeQ[expr, _Ket]

KetPermute[expr_, spec_?anyPermutationSpecQ, ss:{__?SpeciesQ}] :=
  ReplaceAll[expr, v:Ket[_Association] :> KetPermute[v, spec, ss]]

(**** </KetPermute> ****)


(**** <KetSymmetrize> ****)

KetSymmetrize::usage = "KetSymmetrize[expr, {s1, s2, \[Ellipsis]}, tbl] symmetrizes every kets appearing in expr according to polytabloid specified by standard Young tableau tbl."
(* TODO: YoungSymmetrizer *)

KetSymmetrize[bs_List, ss:{__?SpeciesQ}, tbl_List?YoungTableauQ] :=
  KetSymmetrize[bs, ss, YoungTableau @ tbl]

KetSymmetrize[bs_List, ss:{__?SpeciesQ}, YoungTableau[tbl_]] := Module[
  { ts = YoungTranspose[tbl],
    qq, bb },
  qq = TakeList[ss[[Flatten @ ts]], Length /@ ts];
  bb = Fold[Union @* KetSort, bs, qq];
  DeleteCases[
    Garner @ Union @ Map[KetSymmetrize[#, ss, tbl]&, bb],
    0
  ]
] /; NoneTrue[bs, FreeQ[#, Ket[_Association]]&]

KetSymmetrize[expr_] := With[
  { ss = Agents[expr] },
  KetSymmetrize[expr, ss, {Range[Length @ ss]}]
 ] /; Not @ FreeQ[expr, Ket[_Association]]

KetSymmetrize[expr_, {}, ___] := expr /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSymmetrize[expr_, ss:{__?SpeciesQ}] :=
  KetSymmetrize[expr, ss, 1] /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSymmetrize[expr_, ss:{__?SpeciesQ}, 1] :=
  KetSymmetrize[expr, ss, YoungTableau @ {Range @ Length @ ss}] /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSymmetrize[expr_, ss:{__?SpeciesQ}, -1] :=
  KetSymmetrize[expr, ss, YoungTableau @ Transpose @ {Range @ Length @ ss}] /;
  Not @ FreeQ[expr, Ket[_Association]]


KetSymmetrize[expr_, ss:{__?SpeciesQ}, tbl_List?YoungTableauQ] :=
  KetSymmetrize[expr, ss, YoungTableau @ tbl]

KetSymmetrize[expr_, ss:{__?SpeciesQ}, YoungTableau[tbl_]] := Module[
  { ts = YoungTranspose[tbl],
    qq = ss[[Flatten @ tbl]],
    aa, bb, cc, new },
  aa = Flatten /@ Tuples[Permutations /@ tbl];
  bb = Tuples[Permutations /@ ts];
  cc = yngSignatureTo[ts, #] & /@ bb;
  bb = Flatten /@ YoungTranspose /@ bb;
  expr /. {
    v:Ket[_Association] :> 
      Dot[Ket[ss -> Permute[v[qq], #]]& /@ bb, cc]
  } /. {
    w:Ket[_Association] :> 
      Total[Ket[ss -> Permute[w[qq], #]]& /@ aa]
  }
] /; Not @ FreeQ[expr, Ket[_Association]]


yngSignatureTo::usage = "yngSignatureTo[a, b] compares the rows of (not necessarily stadnard) Young Tableaux a and b, and returns the products of the signatures. Useful to construct polytabloid."

yngSignatureTo[a_, b_] := Whole @ MapThread[SignatureTo, {a, b}]


KetSymmetrize[expr_] := KetSymmetrize[expr, 1]

KetSymmetrize[v_Ket, 1] := Total @ Permutations[v];

KetSymmetrize[expr_, 1] := expr /. {v_Ket :> KetSymmetrize[v, 1]}


KetSymmetrize[v_Ket, -1] := Module[
  { n = Length @ v,
    vv = Sort @ v,
    ff },
  vv = Permute[vv, SymmetricGroup[n]];
  ff = Signature /@ vv;
  ff . vv
]

KetSymmetrize[expr_, -1] :=
  ReplaceAll[ expr, v_Ket :> KetSymmetrize[v, -1] ]


(* Young symmetrizer *)
KetSymmetrize[expr_, tbl_List?YoungTableauQ] :=
  KetSymmetrize[expr, YoungTableau @ tbl]

(* Young symmetrizer *)
KetSymmetrize[expr_, YoungTableau[tbl_]] := Module[
  { tt = Flatten[tbl],
    ts = YoungTranspose[tbl],
    aa, bb, cc, new },
  aa = Flatten /@ Tuples[Permutations /@ tbl];
  bb = Tuples[Permutations /@ ts];
  cc = yngSignatureTo[ts, #] & /@ bb;
  bb = Flatten /@ YoungTranspose /@ bb;
  expr /. {
    v_Ket :> Dot[Permute[v[[tt]], #]& /@ bb, cc]
  } /. {
    w_Ket :> Total[Permute[w[[tt]], #]& /@ aa]
  }
]

(**** </KetSymmetrize> ****)


(**** <InversionVector> ****)

InversionVector::usage = "InversionVector[perm] returns the inversion vector corresponding to permutation perm.\nThe number of elements greater than i to the left of i in a permutation gives the ith element of the inversion vector (Skiena 1990, p. 27).\nTotal[InversionVector[perm]] equals the number of inversions in permtuation perm as well as the length of perm (i.e., the smallest number of adjacent transpositions combining to perm).\nSee also Combinatorica`ToInversionVector."

InversionVector[cyc_Cycles] := InversionVector[PermutationList @ cyc]

InversionVector[{}] = {0}

InversionVector[p_?PermutationListQ] := Module[
  { new = Take[p, #]& /@ InversePermutation[p] },
  Most @ MapThread[
    Function[{x, y}, Count[x, _?(# > y &)]], {new, Range[Length @ p]}]
] /; (Length[p] > 0)


inversionCount::usage = "inversionCount[prm] returns the number of inversions in a permutation prm; substitute for the corresponding combinatorica function.\nSee also InversionVector."

inversionCount[pi_?PermutationListQ] := Sum[
  If[Part[pi, i] > Part[pi, j], 1, 0],
  {j, Length[pi]},
  {i, j-1}
]

(**** </InversionVector> ****)


(**** <Transpositions> ****)

Transpositions::usage = "Transpositions[{k1,k2,\[Ellipsis]}] represents a sequence of adjacent transpositions (k1,k1+1) (k2,k2+1) \[Ellipsis]."

SetAttributes[Transpositions, NHoldAll]

Transpositions /:
PermutationForm[Transpositions[{}]] :=
  Subscript["\[Tau]", 0]

Transpositions /:
PermutationForm[Transpositions[kk:{__Integer}]] :=
  Row @ Map[Subscript["\[Tau]", Row @ {#, #+1}]&, kk]

Transpositions[cyc_Cycles] :=
  Transpositions[adjacentTranspositions @ cyc]

Transpositions /:
PermutationCycles[Transpositions[kk:{___Integer}]] :=
  Apply[PermutationProduct, Cycles[{{#, #+1}}]& /@ kk]

Transpositions /:
PermutationList[trs:Transpositions[{___Integer}]] :=
  PermutationList[PermutationCycles @ trs]

Transpositions /:
PermutationProduct[trs_Transpositions, any_] :=
  PermutationProduct[PermutationCycles @ trs, any]

Transpositions /:
PermutationProduct[any_, trs_Transpositions] :=
  PermutationProduct[any, PermutationCycles @ trs]

(**** </Transpositions> ****)


(**** <PermutationTranspositions> ****)

PermutationTranspositions::usage = "PermutationTranspositions[perm] returns a list of adjacent transpositions that combine to the permtuation perm.\nNote that permutations are multiplied right to left like right operators, not like functions."

PermutationTranspositions[{}] = Transpositions[{}]

PermutationTranspositions[prm_List?PermutationListQ]:= 
  Transpositions[adjacentTranspositions @ prm]

PermutationTranspositions[cyc_Cycles] :=
  PermutationTranspositions[PermutationList @ cyc]


adjacentTranspositions::usage="adjacentTranspositions[prm] decomposes permutation prm into a product of transpositions of immediate neighbors. An entry k in the returned list denotes ransposition (k,k+1)."

adjacentTranspositions[cyc_Cycles] :=
  adjacentTranspositions[PermutationList @ cyc]

adjacentTranspositions[prm_List?PermutationListQ] := Module[
  { idx = 1,
    trs = {},
    new = prm },
  While[ idx < Length[new],
    If[ new[[idx]] < new[[idx+1]],
      idx++,
      trs = Append[trs, idx];
      new = Permute[new, Cycles @ {{idx, idx+1}}];
      If[idx>1, idx--, idx++]
     ]
   ];
  Return[trs]
]

(**** </PermutationTranspositions> ****)


(**** <YoungDistance> ****)

YoungDistance::usage = "YoungDistance[yt, {x, y}] returns the Manhattan distance between boxes corresponding to letters x and y in standard Young tableau yt.\nNote that unlike usual 'distances', it may be negative.\nIt is also known as the axial distance (Sagan, 2001) or Manhattan distance (Krovi, 2019).\nIt is used in the construction of Young's normal, seminormal and natural representations of the symmetric group."

YoungDistance[data_List?YoungTableauQ, rest___] := 
  YoungDistance[YoungTableau[data],rest]

YoungDistance[YoungTableau[data_List], {x_Integer, y_Integer}] :=
  Module[
    { xx = FirstPosition[data, x],
      yy = FirstPosition[data, y] },
    Apply[Subtract, xx - yy]
  ]

YoungDistance[syt_YoungTableau] := With[
  {n = YoungDegree[syt]},
  Table[YoungDistance[syt, {k, k+1}], {k, n-1}]
]

(**** </YoungDistance> ****)


(**** <YoungBratteliDiagram> ****)

YoungBratteliDiagram::usage = "YoungBratteliDiagram[n] constructs the Bratteli diagram corresponding to the canonical tower of subgrups of the symmetric group of degree n."

YoungBratteliDiagram[n_Integer, opts:OptionsPattern[Graph]] := Module[
  { grf = NestList[yngBrattelli, YoungShape[{1}], n-1],
    vtx },
  grf = Graph[Flatten @ Rest @ grf];
  Graph[ grf, opts,
    GraphLayout -> "LayeredEmbedding",
    VertexLabels -> "Name",
    VertexLabelStyle -> Medium,
    ImageSize -> Medium
  ]
]

yngBrattelli[shape_YoungShape] := 
  Map[DirectedEdge[shape, #]&, YoungPileUp @ shape]

yngBrattelli[edges:{__DirectedEdge}] := 
  Flatten @ Map[yngBrattelli, Union[Last /@ edges]]

(**** </YoungBratteliDiagram> ****)


(**** <YoungPileUp> ****)

YoungPileUp::usage = "YoungPileUp[gyp] returns a list of Gelfand-Young patterns resulting from adding a new cell numbered n+1 to the Gelfand-Young pattern 'gyp' of degree n.\nYoungPileUp[gyp, d] returns a list in which the standard Young tableau corresponding to each Gelfand-Young pattern has at most d rows."

YoungPileUp::rows = "The standard Young tableau corresponding to Gelfand-Young pattern `` already has more than `` rows."

(* Young shapes *)

YoungPileUp[YoungShape[{}], ___] := { YoungShape @ {1} }

YoungPileUp[YoungShape[data_]] := 
  YoungPileUp[YoungShape @ data, Length[data] + 1]

YoungPileUp[YoungShape[data_], d_Integer] := Module[
  { new = Append[YoungTrim @ data, 0] },
  new = Table[
    ReplacePart[new, k -> new[[k]]+1],
    {k, Min @ {d, Length @ new}}
  ];
  YoungShape /@ YoungTrim /@ Select[new, YoungShapeQ]
]

(* Young tableaux *)

YoungPileUp[YoungTableau[{}], ___] := { YoungTableau[{{1}}] }

YoungPileUp[syt_YoungTableau] :=
 YoungPileUp[syt, Length[First @ syt] + 1]

YoungPileUp[syt_YoungTableau, d_Integer] := Module[
  { n = YoungDegree[syt] + 1,
    new = Append[First @ syt, {}] },
  new = Table[
    ReplacePart[new, k -> Append[new[[k]], n]],
    {k, Min @ {d, Length @ new}}
  ];
  new = Select[new, YoungTableauQ];
  YoungTableau /@ YoungTrim /@ new
]


(* Gelfand-Young patterns *)

YoungPileUp[GelfandPattern[{}], ___] := { GelfandPattern[{{1}}] }

YoungPileUp[gy_GelfandPattern] :=
  YoungPileUp[gy, YoungDegree[gy]+1]

YoungPileUp[GelfandPattern[gyp_], d_Integer] := Module[
  { deg = Length[gyp] + 1,
    new },
  new = PadRight[First @ gyp, deg];
  new = Table[
    ReplacePart[new, k -> new[[k]]+1],
    {k, Min @ {d, deg}}
  ];
  GelfandPattern /@ Map[Prepend[gyp, #]&, Select[new, YoungShapeQ]]
] /; If[
  LengthWhile[First @ gyp, Positive] <= d, True,
  Message[YoungPileUp::rows, GelfandPattern @ gyp, d]; False
]

(**** </YoungPileUp> ****)


(**** <YoungInvariantBasis> ****)

YoungInvariantBasis::usage = "YoungInvariantBasis[{v1,v2,\[Ellipsis]}] returns the list of all vectors that are invariant under the symmetric group in the space spanned by computational basis {v1,v2,\[Ellipsis]}."

YoungInvariantBasis[bs:{Ket[{__YoungTableau}]..}] := Module[
  { n = YoungDegree @ FirstCase[bs, _YoungTableau, YoungTableau @ {{}}, Infinity],
    op },
  (* so-called the twirling operator *)
  op = Total[GroupElements @ SymmetricGroup @ n];
  op /= GroupOrder[SymmetricGroup @ n];
  DeleteCases[Union @ KetCanonical[op ** bs, False], 0]
]

(**** </YoungInvariantBasis> ****)


(**** <SpechtBasis> ****)

SpechtBasis::usage = "SpechtBasis[n] or SpechtBasis[SymmetricGroup[n]] constructs the bases of the Specht modules of the symmetric group of degree n.\nSpechtBasis[shape] returns the basis of the Specht module corresponding to Young shape shape." 

SpechtBasis[shape_YoungShape] := Ket /@ List /@ YoungTableaux[shape]
(* NOTE: Since v3.0, YoungTableaux is now based on GelfandYoungPatterns and
   is already consistent with SpechtBasis. *)

SpechtBasis[SymmetricGroup[n_Integer]] := SpechtBasis[n]

SpechtBasis[n_Integer] := With[
  { pp = YoungShapes[n] },
  AssociationThread[pp -> SpechtBasis /@ pp]
]

(**** </SpechtBasis> ****)


(**** <PermutationBasis> ****)

PermutationBasis::usage = "PermutationBasis[{m1,m2,\[Ellipsis],md}, {s1,s2,\[Ellipsis],sn}] returns the basis of the permutation module consisting of n-tuples of d letters (or levels) with content (or type) {m1,m2,\[Ellipsis],md} for the symmetric group associated with set {s1,s2,\[Ellipsis],sn} of d-level species.\nPermutationBasis[{s1,s2,\[Ellipsis],sn}] returns an association of the bases of all possible permutation modules for the symmetric group associated with set {s1,s2,\[Ellipsis],sn} of d-level species."

PermutationBasis::dim = "The dimensions of species in `` are not the same."

PermutationBasis::len = "The dimension of species `` is not the same as the length of content ``."

PermutationBasis::num = "The number of particles in `` is not the same as that in content ``."

PermutationBasis[n_Integer, d_Integer] := 
  AssociationMap[PermutationBasis, OrderedPartitions[n, d]]

PermutationBasis[content:{__Integer?NonNegative}] :=
  Ket /@ Permutations[ContentVector[content]-1]


PermutationBasis[ss:{__?SpeciesQ}] :=
  PermutationBasis[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

PermutationBasis[ss:{__?SpeciesQ}] := Module[
  { occ },
  occ = OrderedPartitions[Length @ ss, Dimension @ First @ ss];
  AssociationMap[PermutationBasis[#, ss]&, occ]
] /; If[ 
  Apply[Equal, Dimension @ ss], True,
  Message[PermutationBasis::dim, ss]; False
]

PermutationBasis[content:{__Integer?NonNegative}, ss:{__?SpeciesQ}] := Module[
  { tpl },
  tpl = Permutations[ContentVector[content]-1];
  Return[Ket[ss -> #]& /@ tpl]
] /; 
If[ Apply[Equal, Dimension @ ss],
  If[ Dimension[First @ ss] == Length[content],
    If[ Total[content] == Length[ss],
      True,
      Message[PermutationBasis::num, ss, content]; False  
    ],
    Message[PermutationBasis::len, ss, content]; False
  ],
  Message[PermutationBasis::dim, ss]; False
]

(**** </PermutationBasis> ****)


(**** <DominatesQ> ****)

DominatesQ::usage = "DominatesQ[a,b] returns True if list a dominates list b and False otherwise."

DominatesQ[a_?ListQ, b_?ListQ] := Module[
  { n = Max[Length @ a, Length @ b],
    aa, bb },
  aa = Accumulate @ PadRight[a, n];
  bb = Accumulate @ PadRight[b, n];
  AllTrue[GreaterEqual @@@ Transpose @ {aa, bb}, TrueQ]
]

(* shortcut *)
DominatesQ[a_YoungShape, b_] := DominatesQ[First @ a, b]

(* shortcut *)
DominatesQ[a_, b_YoungShape] := DominatesQ[a, First @ b]

DominatesQ[_, _] = False


Dominates::usage = "Dominates[b] is an operator form that yields a\[RightTriangleEqual]b when applied to an expression a."

Dominates[b_?ListQ][a_] := DominatesQ[a, b]

(* shortcut *)
Dominates[a_YoungShape] := Dominates[First @ a]


DominatedBy::usage = "DominatedBy[a] is an operator form that yields b\[LeftTriangleEqual]a when applied to an expression b."

DominatedBy[a_?ListQ][b_] := DominatesQ[a, b]

(* shortcut *)
DominatedBy[a_YoungShape] := DominatedBy[First @ a]

(**** </DominatesQ> ****)


(**** <TwoLineArray> ****)

TwoLineArray::usage = "TwoLineArray[mat] converts matrix mat with non-negative entries to the corresponding two-line array (generalized permutation).\nTwoLineArray[{a1,a2,\[Ellipsis],an}, {b1,b2,\[Ellipsis],bn}] returns a matrix with non-negative entries that corresponds to the two-line array {{a1,a2,\[Ellipsis],an}}, {b1,b2,\[Ellipsis],bn}}.\nTwoLineArray[{b1,b2,\[Ellipsis],bn}] is equivalent to TwoLineArray[{1,2,\[Ellipsis],n}, {b1,b2,\[Ellipsis],bn}]."

TwoLineArray[mat_?MatrixQ] := Module[
  { ww },
  ww = MapIndexed[Table[#2, #1]&, mat, {2}];
  ww = Catenate @ Flatten[ww, 1];
  Transpose[ww]
] /; MatrixQ[mat, (NumberQ[#] && IntegerQ[#] && NonNegative[#] &)]

TwoLineArray[a : {__Integer}, b : {__Integer}] :=
  SparseArray[Normal @ Counts @ Transpose @ {a, b}]

TwoLineArray[b : {__Integer}] :=
  TwoLineArray[Range @ Length @ b, b]

(**** <TwoLineArray> ****)


(**** <RSKMap> ****)

RSKMap::usage = "RSKMap[{{a1, a2, ...}, {b1, b2, ...}}] returns {p, q}, where p is a standard Young tableau and b is semi-standard Young tableau, corresponding to the generalized permutation specified by words {a1, a2, ...} and {b2, b2, ...} according to the RSK algorithm."
(** See Fulton (1997). **)

RSKMap[mat_?MatrixQ] := 
  Apply[RSKMap, TwoLineArray @ mat]


RSKMap[kk:{__Integer}] := RSKMap[Range[Length @ kk], kk]

RSKMap[aa:{__Integer}, bb:{__Integer}] :=
    Fold[RowInsertion, YoungTableau /@ {{}, {}}, Transpose @ {aa, bb}]

(**** </RSKMap> ****)


(**** <RowInsertion> ****)

RowInsertion::usage = "RowInsertion[wt, a] returns new Weyl tableau with integer a added to Weyl tableau wt by the row insertion process.\nRowInsertion[wt, {a1,a2,\[Ellipsis],an}] successively add integers a1, a2, \[Ellipsis], an."
(** Insertion to single Weyl tableau **)
(** See Fulton (1997). **)

RowInsertion[wt_YoungTableau, aa:{___Integer}] :=
  Fold[RowInsertion, wt, aa]


RowInsertion[YoungTableau[{}], a_Integer] :=
  YoungTableau[{{a}}]

RowInsertion[wt_YoungTableau, a_Integer] :=
  YoungTableau @ yngRowInsertion[First @ wt, a]


yngRowInsertion[data:{{___Integer} ..}, a_] := Module[
  {row, b},
  {row, b} = yngRowInsertion[First @ data, a];
  Which[
    b == 0,
    Join[{row}, Rest @ data],
    Length[data] == 1,
    Join[{row}, {{b}}],
    True,
    Join[{row}, yngRowInsertion[Rest @ data, b]]
  ]
]

yngRowInsertion[row:{___Integer}, a_Integer] := Module[
  { k = LengthWhile[row, # <= a &] },
  If[ k == Length[row],
    {Append[row, a], 0},
    {ReplacePart[row, k+1 -> a], row[[k+1]]}
  ]
]


RowInsertion::usage = RowInsertion::usage <>"\nRowInsertion[{p, q}, {a, b}] returns new pair of Weyl tableaux with integers a and b added, where a is the ordering index and b is the content index.\nRowInsertion[{p, q}, {{a1,a2,\[Ellipsis],an}, {b1,b2,\[Ellipsis],bn}}] successively add integer pairs {a1, b1}, {a2, b2}, \[Ellipsis], {an, bn}.\nNote that p is the recording tableau and q is the insertion tableau."
(** Insertion to a pair of Weyl tableaux **)
(** See Fulton (1997). **)

RowInsertion[
  {p_YoungTableau, q_YoungTableau},
  {Automatic, b:{___Integer}}
] := RowInsertion[{p, q}, {Range @ Length @ b, b}]

RowInsertion[
  {p_YoungTableau, q_YoungTableau},
  {a:{___Integer}, b:{___Integer}}
] := Fold[RowInsertion, {p, q}, Transpose @ {a, b}]

RowInsertion[{YoungTableau[{}], YoungTableau[{}]}, {a_Integer, b_Integer}] :=
  { YoungTableau @ {{a}}, YoungTableau @ {{b}} }

RowInsertion[{p_YoungTableau, q_YoungTableau}, {a_Integer, b_Integer}] :=
  YoungTableau /@ yngRowInsertion[{First @ p, First @ q}, {a, b}]


yngRowInsertion[{p:{__List}, q:{__List}}, {a_, b_}] := Module[
  {row, new},
  {row, new} = yngRowInsertion[First /@ {p, q}, {a, b}];
  Which[
    new == {0, 0},
    Catenate /@ Transpose @ {List /@ row, Rest /@ {p, q}},
    Length[p] == 1,
    Transpose @ {row, List /@ new},
    True,
    Catenate /@ Transpose @ {
      List /@ row, 
      yngRowInsertion[Rest /@ {p, q}, new]
    }
  ]
]

yngRowInsertion[{p:{___Integer}, q:{___Integer}}, {a_, b_}] := Module[
  { k = LengthWhile[q, # <= b &] },
  If[ k == Length[q],
    { {Append[p, a], Append[q, b]}, {0, 0} },
    { {p, ReplacePart[q, k+1 -> b]}, {a, q[[k+1]]} }
  ]
]

(**** </RowInsertion> ****)


(**** <YoungTableauProduct> ****)

YoungTableauProduct::usage = "YoungTableauProduct[a, b, \[Ellipsis]] returns the composition a\[CenterDot]b\[CenterDot]\[Ellipsis] of Weyl tableaux a, b, \[Ellipsis]."
(* See Fulton (1997). *)

SetAttributes[YoungTableauProduct, {Flat, OneIdentity, Listable}]

YoungTableauProduct[a_] := a

YoungTableauProduct[a_YoungTableau, b_YoungTableau] :=
  RowInsertion[a, Flatten[Reverse @ First @ b]]

(**** </YoungTableauProduct> ****)

End[]

EndPackage[]
