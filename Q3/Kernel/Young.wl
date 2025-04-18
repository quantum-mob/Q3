(* ::Package:: *)

(* N.B. Some functions have been borrowed from the legacy Combinatorica
   package and from Bernd Guenther's IrrCharSymGrp.m v2.0 (posted on the
   Wolfram Community). *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ YoungDiagram, FerrersDiagram,
  YoungShape, YoungShapes, YoungShapeQ,
  YoungDegree };

{ YoungTranspose, YoungTrim };

{ YoungTableau };

{ YoungTableauQ, YoungTableaux, YoungTableauCount, YoungForm, 
  YoungTranspose };

{ LegacyYoungTableaux };

{ ToYoungTableau, ToGelfandPattern,
  GelfandContents };

{ GelfandYoungPatterns, GelfandYoungPatternQ };

{ GroupClassSize, SymmetricGroupClassSize,
  GroupCentralizerSize, SymmetricGroupCentralizerSize,
  GroupCharacters, SymmetricGroupCharacters,
  GroupClasses, SymmetricGroupClasses,
  CompoundYoungCharacters,
  YoungCharacterInner,
  KostkaMatrix };

{ GroupRegularRepresentation };

{ InversionVector, AdjacentTranspositions };

{ YoungDistance };

{ Transposition };

{ PermutationForm };

{ PermutationBasis };

{ DominatesQ, Dominates, DominatedBy };

{ YoungShapePile, BratteliDiagram };

{ SpechtBasis, YoungInvariantBasis };


Begin["`Private`"]

PermutationForm::usage = "PermutationForm[cyc] displays permutation cycles cyc in terms of \[Pi].\nPermutationForm[perm] displays perm specified in the permutation list representation in the two-list form."

PermutationForm[Cycles[{}]] := Subscript[\[Pi], 0]

PermutationForm[Cycles[pp_List]] :=
  Row @ Map[Subscript[\[Pi], Row @ #]&, pp]

PermutationForm[{}] = {}

PermutationForm[prm_?PermutationListQ] := DisplayForm @ RowBox @ {
  "(",
  Grid @ {Range[Length @ prm], prm},
  ")"
}

PermutationForm[expr_Association] := PermutationForm /@ expr

PermutationForm[expr_] := ReplaceAll[ expr,
  { pp:$PermutationSpec :> PermutationForm[pp] }
]


Transposition::usage = "Transposition[{i, j}] returns Cycles[{{i, j}}], representing the transposition of elements i and j. It is a shortcut to Cycles[{{i, j}}].\nTransposition[n] is equivalent to Transposition[{n, n+1}]."

Transposition[{}] := Cycles[{}]

Transposition[pair:{_Integer, _Integer}] := Cycles @ {pair}

Transposition[x_Integer, y_Integer] := Transposition @ {x, y}

Transposition[k_Integer] := Transposition @ {k, k+1}


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

YoungDegree[tbl_YoungTableau] := YoungDegree[YoungShape @ tbl]

(**** </YoungDegree> ****)


(**** <YoungShape> ****)

YoungShapeQ::usage="YoungShapeQ[shape] returns True if and only if shape is an integer partition, arranged in non-increasing order.\nA Young shape defines a Young diagram."

YoungShapeQ[YoungShape[data_List]] := YoungShapeQ[data]

YoungShapeQ[_] = False

YoungShapeQ[pp:{__Integer?NonNegative}] := Apply[GreaterEqual, pp]
(* NOTE: Must allow 0 since some functions uses 0 in shape specification. *)


YoungShape::usage = "YoungShape[tb] returns the shape, i.e., the integer partition of Young tableau tb."

Format[ys:YoungShape[data:{___}]] :=
  Interpretation[YoungDiagram @ data, ys]

YoungShape[YoungTableau[tb_]] := YoungShape[tb]

YoungShape[tb:{__List}] := YoungShape[Length /@ tb]


YoungShapes::usage = "YoungShapes[n] returns the list of all possible Young shapes for integer n.\nYoungShapes[n, d] returns the list of Young shapes at most d rows.\nYoungShapes[spec] with the same spec for IntegerPartitions[spec] is allowed."

YoungShapes[spec__] := YoungShape /@ IntegerPartitions[spec]

(**** </YoungShape> ****)


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


YoungTableauCount::usage = "YoungTableauCount[shape] uses the hook length formula to count the number of standard Young tableaux of 'shape'.\nYoungTableauCount[n] gives the total number of standard Young tableaux for all partitions of integer 'n'.\nBorrowed from NumberOfTableaux in Combinatorica package."

YoungTableauCount[YoungShape[pp_]] := YoungTableauCount[pp]

YoungTableauCount[pp_?YoungShapeQ] := Module[
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
  Total @ Map[YoungTableauCount, IntegerPartitions @ n]


(**** <GroupRegularRepresentation> ****)

GroupRegularRepresentation::usage = "GroupRegularRepresentation[grp, elm] returns the matrix of group element elm in the left regular representation of group grp."

GroupRegularRepresentation::elm = "`2` is not an element of group `1`."

GroupRegularRepresentation[grp_, elm_] :=
  Transpose @ Thread @ UnitVector[
    GroupOrder @ grp,
    Part[
      Transpose @ GroupMultiplicationTable[grp], 
      GroupElementPosition[grp, elm]
     ]
  ] /; GroupElementQ[grp, elm]

GroupRegularRepresentation[grp_, elm_] := (
  Message[GroupRegularRepresentation::elm, grp, elm];
  One[GroupOrder @ grp]
)

(* For the regular representation of the symmetric group *)
theKetFormatQ[_Cycles] = True

theKetFormat[cyc_Cycles] := PermutationForm[cyc]

(**** </GroupRegularRepresentation> ****)


(**** <GroupCharacters> ****)

GroupCharacters::usage = "GroupCharacters[group] returns the table of characters of the irreducible representations of 'group'. The characters of each irreducible representation is stored in a row vector.\nGroupCharacters[group, irr] gives a list of the characters of the irreducible representation 'irr'.\nGroupCharacters[group, irr, class] returns the character of the irreducible representation 'irr' of 'group' evaluated at the conjugacy class 'class'.\nFor a symmetric group, both irreducible representation and class are specified by integer partitions."

GroupCharacters[SymmetricGroup[n_Integer]] :=
  SymmetricGroupCharacters[n] /; n > 0

GroupCharacters[SymmetricGroup[n_Integer], irr_?YoungShapeQ] :=
  SymmetricGroupCharacters[irr] /; Total[irr] == n

GroupCharacters[SymmetricGroup[n_Integer],
  irr_?YoungShapeQ, class_?YoungShapeQ] :=
  SymmetricGroupCharacters[irr, class] /;
  Total[irr] == Total[class] == n


SymmetricGroupCharacters::uasge = "SymmetricGroupCharacters[n] returns the table of characters of SymmetricGroup[n].\nSymmetricGroupCharacters[irr] returns a list of characters of the irreducible representation 'irr'.\nSymmetricGroupCharacters[irr, class] returns the character of the irreducible representation 'irr' evaluated at the conjugacy class 'class'.\nBoth 'irr' and 'class' are specified by partitions of integer 'n'."

SymmetricGroupCharacters[n_Integer] := Module[
  { pp = IntegerPartitions[n],
    wght, vecs },
  wght = SymmetricGroupCentralizerSize /@ pp;
  vecs = CompoundYoungCharacters /@ pp;
  Orthogonalize[vecs, ((#1/wght) . #2)&, Method -> "GramSchmidt"]
 ]

SymmetricGroupCharacters[irr_?YoungShapeQ] :=
  characterSymmetricGroup[irr, #]& /@ IntegerPartitions[Total @ irr]  
  
SymmetricGroupCharacters[irr_?YoungShapeQ, class_?YoungShapeQ] :=
  characterSymmetricGroup[irr, class]


characterSymmetricGroup[{}, {}] := 1; 

characterSymmetricGroup[shape_?YoungShapeQ, class_?YoungShapeQ] :=
  YoungTableauCount[shape] /; And[
    Total[shape] == Total[class],
    Length[class] >= 1,
    First[class] == 1
   ]

characterSymmetricGroup[shape_?YoungShapeQ, class_?YoungShapeQ] :=
  With[
    { classmax = First[class],
      class0 = Rest[class],
      mu = YoungTranspose[shape],
      nu = Append[shape,0] },
    Sum[
      If[shape[[j]]+mu[[i]]+1-j-i != classmax,
        0,
        If[EvenQ[classmax+i-shape[[j]]], -1, 1] * 
          characterSymmetricGroup[
            Select[
              Table[
                If[k<j||nu[[k]]<i, nu[[k]], Max[nu[[k+1]],i]-1],
                {k, Length[shape]}
               ],
              (#>0)&
             ],
            class0
           ]
       ],
      {j, 1, Length[shape]},
      {i, 1, shape[[j]]}
     ]
  ] /; And[
    Total[shape] == Total[class],
    Length[class] >= 1,
    First[class] > 1
  ]

(**** </GroupCharacters> ****)


(**** <GroupClasses> ****)

GroupClasses::usage = "GroupClasses[group] returns the list of conjugacy classes of group."

GroupClasses[SymmetricGroup[n_Integer]] :=
  SymmetricGroupClasses[n] /; n > 0

GroupClasses[SymmetricGroup[n_Integer], irr_?YoungShapeQ] :=
  SymmetricGroupClasses[irr] /; Total[irr] == n


SymmetricGroupClasses::uasge = "SymmetricGroupClasses[n] returns an association of conjugacy classes of the symmetric group of degree n.\nEach key of the returned association refers to the 'cycle decomposition type' of the permutations in the class, which in turn uniquelty corresponds to a partition of integer n."

SymmetricGroupClasses[n_Integer] := With[
  { elm = GroupElements[SymmetricGroup @ n] },
  KeyMap[
    YoungShape,
    KeySort[
      GroupBy[elm, theIrreducibleLabel[n]], 
      LexicographicOrder
    ]
  ]
]

theIrreducibleLabel[n_Integer][Cycles[spec_List]] := With[
  { body = ReverseSort[Length /@ spec] },
  Join[body, Table[1, n-Total[body]]]
]

(**** </GroupClasses> ****)


GroupClassSize::usage = "GroupGlassSize[group, class] returns the number of elements in the conjugacy class 'class'."

GroupClassSize[SymmetricGroup[n_Integer], class_?YoungShapeQ] :=
  SymmetricGroupClassSize[class] /; n > 0

GroupClassSize[group_, g_] :=
  GroupOrder[group] / GroupCentralizerSize[group, g]


SymmetricGroupClassSize::usage="SymmetricGroupClassSize[class] returns the number of elements in the conjugacy class 'class' in SymmetricGroup[n].\nThe conjugacy class is specified by a partition of integer 'n'.\nThe inverse of SymmetricGroupClassSize[class] = GroupOrder[SymmetricGroup[n]] / SymmetricGroupCentralizerSize[class]; see, e.g., Sagan, The Symmetric Group (Springer, 2001) Section 1.1."

SymmetricGroupClassSize[shape_YoungShape] :=
  SymmetricGroupClassSize[First @ shape]

SymmetricGroupClassSize[class_?YoungShapeQ] :=
  GroupOrder[SymmetricGroup @ Total @ class] /
  SymmetricGroupCentralizerSize[class]


GroupCentralizerSize::usage = "GroupCentralizerSize[group, g] returns the number of elements in the conjugacy class containing the element 'g' of the group 'group'."

GroupCentralizerSize[SymmetricGroup[n_Integer], class_?YoungShapeQ] :=
  SymmetricGroupCentralizerSize[class] /; n > 0

GroupCentralizerSize[group_, g_] :=
  GroupOrder @ GroupCentralizer[group, g]


SymmetricGroupCentralizerSize::usage = "SymmetricGroupCentralizerSize[class] returns the size of the centralizer class of an element of cycle type class.\nThe inverse of SymmetricGroupCentralizerSize[class] coincides, up to a factor of the group order, with the size of the conjugacy class; that is, SymmetricGroupCentralizerSize[class] = GroupOrder[SymmetricGroup[n]] / (the size of the class class)."

SymmetricGroupCentralizerSize[class_?YoungShapeQ] :=
  Apply[Times, Factorial /@ Counts[class]] * Apply[Times, class];


CompoundYoungCharacters::usage = "CompoundYoungCharacters[shape] returns the composite Young character corresponding to partition shape."

CompoundYoungCharacters[pp_?YoungShapeQ] := Module[
  { chrVect = Table[0, PartitionsP[Total @ pp]],
    supPartitionTupel = Partition[pp,1],
    hashPositionTupel = Prime[pp],
    r, columnIdx },

  With[
    { hashPosList = SparseArray[
        Flatten @ MapIndexed[
          {Times @@ Prime[#1] -> First[#2]}&,
          IntegerPartitions[Total[pp]]
         ]
       ]
     },

    While[ True,
      columnIdx = Part[hashPosList, Whole @ hashPositionTupel];
      chrVect[[columnIdx]] += Whole @ Apply[
        Multinomial,
        Map[
          Part[#, 2]&,
          SplitBy[Sort @ Flatten[Tally /@ supPartitionTupel, 1], First],
          {2}
         ],
        2
       ];

      r = Length[supPartitionTupel];
      While[(r>0) && (First[supPartitionTupel[[r]]]==1), r--];
      If[r<=0, Break[]];
      
      supPartitionTupel = Join[
        Take[supPartitionTupel,r-1],
        {nextPartition[supPartitionTupel[[r]]]},
        Partition[Drop[pp,r],1]
       ];
      hashPositionTupel = Join[
        Take[hashPositionTupel, r-1],
        {Whole @ Prime[supPartitionTupel[[r]]]},
        Prime @ Drop[pp,r]
       ]
     ]
   ];
  
  chrVect
 ]


nextPartition[pp_?YoungShapeQ] := Module[
  { i = First @ Last @ Position[pp, x_/;x>1],
    k = Length[pp],
    j, qr },
  j = Part[pp, i];
  qr = QuotientRemainder[j+k-i, j-1];
  Join[
    Take[pp, i-1],
    ConstantArray[j-1, Part[qr, 1]],
    If[Part[qr, 2] >= 1, {Part[qr, 2]}, {}]
   ]
 ] /; AnyTrue[pp, #>1&]

nextPartition[pp_?YoungShapeQ] := {Total @ pp} /; AllTrue[pp, #==1&]
(* Convention: at the last partition, we cycle back to the first one. *)


KostkaMatrix::usage = "KostkaMatrix[n] returns the matrix of Kostka numbers of rank n."

KostkaMatrix[n_Integer] := Dot[
  SymmetricGroupCharacters[n],
  DiagonalMatrix[1 / (SymmetricGroupCentralizerSize /@ IntegerPartitions[n])],
  Transpose[CompoundYoungCharacters /@ IntegerPartitions[n]]
 ] /; n > 0


YoungCharacterInner::usage = "YoungCharacterInner[f, g, n] returns the scalar product of the class vectors f and g for a symmetric group of rank n."

YoungCharacterInner[f_List, g_List, n_Integer] := Total[
  f * g / (SymmetricGroupCentralizerSize /@ IntegerPartitions[n])
 ] /; And[
   n > 0,
   Length[f]==PartitionsP[n],
   Length[g]==PartitionsP[n]
  ]


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


(**** <YoungForm> ****)

YoungTableau::usage = "YoungPattern[data] represents a Young tableau specified by data."

Format[tbl:YoungTableau[data:{{___}..}]] :=
  Interpretation[YoungForm @ data, tbl]

YoungTableau /:
Equal[YoungTableau[a_], YoungTableau[b_]] := Equal[a, b]


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
  NestList[nextYoungTableau, firstYoungTableau[s], YoungTableauCount[s]-1]

LegacyYoungTableaux[n_Integer?Positive] :=
  Catenate @ Map[LegacyYoungTableaux, YoungShapes @ n]


firstYoungTableau::usage = "firstYoungTableau[p] constructs the first standard Young tableau with shape described by partition p."

firstYoungTableau[shape_YoungShape] :=
  YoungTranspose @ lastYoungTableau @ YoungTranspose[shape]


lastYoungTableau::usage = "lastYoungTableau[p] constructs the last Young tableau with shape described by partition p."

lastYoungTableau[YoungShape[shape_]] :=
  YoungTableau @ TakeList[Range @ Total @ shape, shape]


nextYoungTableau::usage = "nextYoungTableau[tb] gives the standard Young tableau of the same shape as tb, following tb in lexicographic order."

(* NOTE 2021-10-27: It seems that the standard Young tableaux are ordered
   according to the "last letter sequence". See Pauncz (1995a, Section 3.2). *)

nextYoungTableau[YoungTableau[tb_]] := Module[
  { yy, shp, row, val, new },

  yy = Values @ KeySort @ Flatten @ MapIndexed[(#1->First[#2])&, tb, {2}];
  If[LessEqual @@ yy, Return @ firstYoungTableau @ YoungShape[tb]];

  val = 1 + Length[First @ Split[yy, LessEqual]];
  row = First @ FirstPosition[tb, val];
  
  shp = Length /@ DeleteCases[tb, k_/;k>val, {2}];
  row = First @ Last @ Position[shp, shp[[row+1]]];
  shp[[row]]--;

  new = First @ firstYoungTableau[YoungShape @ shp];
  If[ Length[new] < row,
    new = Append[new, {val}],
    new[[row]] = Append[new[[row]], val]
   ];

  new = Flatten @ MapIndexed[(#2->#1)&, new, {2}];
  YoungTableau @ ReplacePart[tb, new]
 ]

(**** </LegacyYoungTableaux> ****)


(**** <Permutation> ****)

Permutation::usage = "Permutation[cyc,{s1,s2,\[Ellipsis]}] represents the permutation operator acting on species {s1,s2,\[Ellipsis]}."

Permutation::cyc = "`` does not represent a valid permutation in disjoint cyclic form. See PermutationCyclesQ."

AddElaborationPatterns[_Permutation]

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
Matrix[
  op:Permutation[_?PermutationCyclesQ, {__?SpeciesQ}],
  rest___ ] := Matrix[Elaborate @ op, rest]

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

HoldPattern @
  Multiply[pre___, op_Cycles, more__Cycles, post___] :=
  Multiply[pre, PermutationProduct @@ Reverse[{op, more}], post]
  
HoldPattern @
  Multiply[pre___, op_Cycles, Ket[ytx:{__YoungTableau}], post___] :=
  Multiply[pre, KetPermute[Ket[ytx], op], post]
(* NOTE: Notice '__' in ytx, with op acting on all SYTs in ytx. *)
  
HoldPattern @ Multiply[ pre___,
  CircleTimes[ops__Cycles], Ket[ytx:{__?YoungTableauQ}], post___ ] :=
  Multiply[ pre,
    CircleTimes @@ MapThread[KetPermute, {Ket /@ List /@ ytx, {ops}}],
    post ]
  
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
(* NOTE: that Young's normal representation should be distinguished from
   Young's natural or seminormal representation. *)

KetPermute[Ket[{yt_YoungTableau}], Cycles @ {{x_, y_}}] := Module[
  { xx = FirstPosition[First @ yt, x],
    yy = FirstPosition[First @ yt, y],
    dd, tt },
  Which[
    First[xx] == First[yy], Ket[{yt}],
    Last[xx] == Last[yy], -Ket[{yt}],
    True,
    dd = 1 / YoungDistance[{x, y}, yt];
    tt = ReplaceAll[yt, {x -> y, y -> x}];
    Ket[{yt}] * dd + Ket[{tt}] * Sqrt[1-dd^2]
   ]
 ] /; x+1 == y


KetPermute[Ket[{yt_YoungTableau}], cc_Cycles] :=
  Garner @ Fold[KetPermute, Ket @ {yt}, AdjacentTranspositions @ cc]

KetPermute[Ket[{yt_YoungTableau}], perm_?PermutationListQ] :=
  Garner @ Fold[KetPermute, Ket @ {yt}, AdjacentTranspositions @ perm]

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


(**** KetSymmetrize ****)

KetSymmetrize::usage = "KetSymmetrize[expr, {s1, s2, \[Ellipsis]}, tbl] symmetrizes every kets appearing in expr according to polytabloid specified by standard Young tableau tbl.\n"

KetSymmetrize[bs_List, ss:{__?SpeciesQ}, tbl_YoungTableau] :=
  KetSymmetrize[bs, ss, First @ tbl]

KetSymmetrize[bs_List, ss:{__?SpeciesQ}, tbl_?YoungTableauQ] := Module[
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
  KetSymmetrize[expr, ss, {Range[Length @ ss]}] /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSymmetrize[expr_, ss:{__?SpeciesQ}, 1] :=
  KetSymmetrize[expr, ss, {Range[Length @ ss]}] /;
  Not @ FreeQ[expr, Ket[_Association]]

KetSymmetrize[expr_, ss:{__?SpeciesQ}, -1] :=
  KetSymmetrize[expr, ss, Transpose @ {Range[Length @ ss]}] /;
  Not @ FreeQ[expr, Ket[_Association]]


KetSymmetrize[expr_, ss:{__?SpeciesQ}, tbl_YoungTableau] :=
  KetSymmetrize[expr, ss, First @ tbl]

KetSymmetrize[expr_, ss:{__?SpeciesQ}, tbl_?YoungTableauQ] := Module[
  { qq = ss[[Flatten @ tbl]],
    aa, bb, cc, new },
  aa = Flatten /@ Tuples[Permutations /@ tbl];
  new = YoungTranspose[tbl];
  bb = Tuples[Permutations /@ new];
  cc = yngSignatureTo[new, #] & /@ bb;
  bb = Flatten /@ YoungTranspose /@ bb;
  expr /. {
    v:Ket[_Association] :> 
      Dot[Ket[ss -> Permute[v[qq], #]]& /@ bb, cc]
  } /. {
     w:Ket[_Association] :> 
       Total[Ket[ss -> Permute[w[qq], #]]& /@ aa]
  }
] /; Not @ FreeQ[expr, Ket[_Association]]


yngSignatureTo::usage = "yngSignatureTo[a,b] compares the rows of (not necessarily stadnard) Young Tableaux a and b. Useful to construct polytabloid."

yngSignatureTo[a_?anyTableauQ, b_?anyTableauQ] := 
 Whole @ MapThread[SignatureTo, {a, b}]

anyTableauQ::uage = "anyTableauQ[tb] returns True if tb is a legitimate (not necessarily standard) Young tableau."

anyTableauQ[tb : {__List}] := And[
  Apply[GreaterEqual, Length /@ tb], 
  Apply[GreaterEqual, Length /@ YoungTranspose[tb]]
]


(* total symmetrization for Pauli Kets *)

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


KetSymmetrize[expr_, tbl_?YoungTableauQ] := Module[
  { tt = Flatten[tbl],
    aa, bb, cc, new },
  aa = Flatten /@ Tuples[Permutations /@ tbl];
  new = YoungTranspose[tbl];
  bb = Tuples[Permutations /@ new];
  cc = yngSignatureTo[new, #] & /@ bb;
  bb = Flatten /@ YoungTranspose /@ bb;
  expr /. {
    v_Ket :> Dot[Permute[v[[tt]], #]& /@ bb, cc]
  } /. {
    w_Ket :> Total[Permute[w[[tt]], #]& /@ aa]
  }
]

(**** </KetSymmetrize> ****)


InversionVector::usage = "InversionVector[perm] returns the inversion vector corresponding to permutation perm.\nThe number of elements greater than i to the left of i in a permutation gives the ith element of the inversion vector (Skiena 1990, p. 27).\nTotal[InversionVector[perm]] equals to the number of inversions in permtuation perm as well as to the length of perm (i.e., the smallest number of adjacent transpositions combining to perm).\nSee also Combinatorica`ToInversionVector."

InversionVector[cyc_Cycles] := InversionVector[PermutationList @ cyc]

InversionVector[{}] = {0}

InversionVector[p_?PermutationListQ] := Module[
  { new = Take[p, #]& /@ InversePermutation[p] },
  Most @ MapThread[
    Function[{x, y}, Count[x, _?(# > y &)]], {new, Range[Length @ p]}]
] /; (Length[p] > 0)


(**** <AdjacentTranspositions> ****)

AdjacentTranspositions::usage = "AdjacentTranspositions[perm] returns a list of adjacent transpositions that combine to the permtuation perm.\nNote that permutations are multiplied right to left like right operators, not like functions."

AdjacentTranspositions[prm_?PermutationListQ]:= 
  Map[Transposition, intoTranspositions @ prm]

AdjacentTranspositions[{}] = {}

AdjacentTranspositions[cyc_Cycles] :=
  AdjacentTranspositions[PermutationList @ cyc]


intoTranspositions::usage="intoTranspositions[perm] represents perm as product of transpositions of immediate neighbors. An entry value of k in the returned list denotes the transposition (k,k+1)."

intoTranspositions[cyc_Cycles] :=
  intoTranspositions[PermutationList @ cyc]

intoTranspositions[prm_?PermutationListQ] := Module[
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

fromTranspositions::usage = "fromTranspositions[trs] is the inverse operation of intoTranspositions.\nGiven here just for heuristic reasons."

fromTranspositions[ntr_List] :=
  Apply[PermutationProduct, Cycles[{{#,#+1}}]& /@ ntr]

(**** </AdjacentTranspositions> ****)


(**** <YoungDistance> ****)

YoungDistance::usage = "YoungDistance[{x, y}, yt] returns the Manhattan distance between boxes corresponding to letters x and y in standard Young tableau yt.\nNote that unlike usual 'distances', it may be negative.\nIt is also known as the axial distance (Sagan, 2001) or Manhattan distance (Krovi, 2019).\nIt is used in the construction of Young's seminormal representation of the symmetric group."

YoungDistance[{x_Integer, y_Integer}, yt_YoungTableau] :=
  YoungDistance[{x, y}, First @ yt]

YoungDistance[{x_Integer, y_Integer}, data_?YoungTableauQ] := Module[
  { xx = FirstPosition[data, x],
    yy = FirstPosition[data, y] },
  Dot[yy - xx, {-1, 1}]
]

(**** </YoungDistance> ****)


(**** <BratteliDiagram> ****)

BratteliDiagram::usage = "BratteliDiagram[n] constructs the Bratteli diagram for the symmetric group of degree n."

BratteliDiagram[n_Integer, opts : OptionsPattern[Graph]] := Module[
  { grf = Graph @ Flatten @ Rest @ NestList[brattelli, {1}, n-1],
    vtx },
  vtx = VertexList[grf];
  vtx = Map[Rule[#, YoungDiagram @ #]&, vtx];
  Graph[ grf, opts,
    GraphLayout -> "LayeredEmbedding",
    VertexLabels -> vtx,
    VertexLabelStyle -> Large ]
]

brattelli[shape_?YoungShapeQ] := 
  Map[UndirectedEdge[shape, #] &, YoungShapePile[shape]]

brattelli[edges : {__UndirectedEdge}] := 
  Flatten @ Map[brattelli, Union[Last /@ edges]]


YoungShapePile::usage = "YoungShapePile[shape] returns the list of new Young shapes resulting from adding a box to shape."

YoungShapePile[shape_?YoungShapeQ] := Module[
  { new = Append[YoungTrim[shape], 0],
    k },
  new = Table[
    ReplacePart[new, k -> new[[k]]+1],
    {k, 1, Length[new]}
  ];
  YoungTrim /@ Select[new, YoungShapeQ]
]

(**** </BratteliDiagram> ****)


(**** <YoungInvariantBasis> ****)

YoungInvariantBasis::usage = "YoungInvariantBasis[{v1,v2,\[Ellipsis]}] returns the list of all vectors that are invariant under the symmetric group in the space spanned by computational basis {v1,v2,\[Ellipsis]}."

YoungInvariantBasis[bs:{Ket[{__YoungTableau}]..}] := Module[
  { n = YoungDegree @ FirstCase[bs, _YoungTableau, YoungTableau @ {{}}, Infinity],
    op },
  (* so-called the twirling operator *)
  op = Total @ GroupElements @ SymmetricGroup[n];
  op /= GroupOrder[SymmetricGroup @ n];
  DeleteCases[Union @ KetCanonical[op ** bs, False], 0]
]

(**** </YoungInvariantBasis> ****)


(**** <SpechtBasis> ****)

SpechtBasis::usage = "SpechtBasis[n] or SpechtBasis[SymmetricGroup[n]] constructs the bases of the Specht modules of the symmetric group of degree n.\nSpechtBasis[shape] returns the basis of the Specht module corresponding to Young shape shape." 

SpechtBasis[shape_YoungShape] := Ket /@ List /@ YoungTableaux[shape]
(* NOTE: Since v3.0, YoungTableaux is now based on GelfandYoungPatterns and
   is already consistent with SchurBasis. *)
(* Ket /@ ToYoungTableau /@ GelfandYoungPatterns[shape] *)
(* OBSOLETE NOTE: To be consistent with the Schur basis,
   we use the above method instead of the following:
   SpechtBasis[shape_?YoungShapeQ] := Ket /@ YoungTableaux[shape]
   *)

SpechtBasis[SymmetricGroup[n_Integer]] := SpechtBasis[n]

SpechtBasis[n_Integer] := With[
  { pp = YoungShapes[n] },
  AssociationThread[pp -> SpechtBasis /@ pp]
 ]

(* For the Specht module *)
theKetFormatQ[_?YoungTableauQ] = True

theKetFormat[tbl_?YoungTableauQ] := {YoungForm[tbl]}
(* NOTE: Do not use test anyYoungTableauQ since it also passes Gelfand
   patterns. *)

(**** </SpechtBasis> ****)


(**** <PermutationBasis> ****)

PermutationBasis::usage = "PermutationBasis[{m1,m2,\[Ellipsis],md}, {s1,s2,\[Ellipsis],sn}] returns the basis of the permutation module consisting of n-tuples of d letters (or levels) with content (or type) {m1,m2,\[Ellipsis],md} for the symmetric group associated with set {s1,s2,\[Ellipsis],sn} of d-level species.\nPermutationBasis[{s1,s2,\[Ellipsis],sn}] returns an association of the bases of all possible permutation modules for the symmetric group associated with set {s1,s2,\[Ellipsis],sn} of d-level species."

PermutationBasis::baddim = "The dimensions of species in `` are not equal to each other."

PermutationBasis[ss:{__?SpeciesQ}] := 
  PermutationBasis[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

PermutationBasis[ss:{__?SpeciesQ}] := Module[
  { dim = Dimension[ss],
    shp, occ },
  If[ Apply[Equal, dim],
    dim = First @ dim,
    Message[PermutationBasis::baddim, ss];
    Return[$Failed]
   ];
  shp = PadRight[#, dim]& /@ IntegerPartitions[Length @ ss, dim];
  occ = Flatten[Permutations /@ shp, 1];
  AssociationMap[PermutationBasis[#, ss]&, occ]
 ]

PermutationBasis[type:{__Integer?NonNegative}, ss:{__?SpeciesQ}] :=
  Module[
    { dim = Dimension[ss],
      occ, tpl},
    If[ Apply[Equal, dim],
      dim = First @ dim,
      Message[PermutationBasis::baddim, ss];
      Return[$Failed]
     ];
    occ = PadRight[type, dim];
    tpl = Permutations @ Flatten @ MapThread[Table, {Range[dim]-1, occ}];
    Return[Ket[ss -> #]& /@ tpl]
   ] /; Total[type] == Length[ss]


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

DominatesQ[_, _] = False


Dominates::usage = "Dominates[b] is an operator form that yields a\[RightTriangleEqual]b when applied to an expression a."

Dominates[b_?ListQ][a_?ListQ] := DominatesQ[a, b]


DominatedBy::usage = "DominatedBy[a] is an operator form that yields b\[LeftTriangleEqual]a when applied to an expression b."

DominatedBy[a_?ListQ][b_?ListQ] := DominatesQ[a, b]

(**** </DominatesQ> ****)


End[]

EndPackage[]
