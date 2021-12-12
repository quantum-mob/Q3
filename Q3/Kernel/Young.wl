(* -*- mode: Mathematica -*- *)

(* N.B. Some functions have been borrowed from the legacy Combinatorica
   package and from Bernd Buenther's IrrCharSymGrp.m v2.0 (posted on the
   Wolfram Community). *)

BeginPackage["Q3`"];

`Young`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.59 $"][[2]], " (",
  StringSplit["$Date: 2021-12-11 10:38:33+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ YoungDiagram, FerrersDiagram,
  YoungShape, YoungShapeQ };

{ YoungTranspose, YoungTrim };

{ YoungTableauQ, YoungTableaux, CountYoungTableaux, YoungForm, 
  NextYoungTableau, LastYoungTableau, FirstYoungTableau,
  YoungTranspose };

{ GroupClassSize, SymmetricGroupClassSize,
  GroupCentralizerSize, SymmetricGroupCentralizerSize,
  GroupCharacters, SymmetricGroupCharacters,
  CharacterScalarProduct,
  CompoundYoungCharacters, KostkaMatrix };

{ KetPermute, KetSymmetrize };
{ PermutationMatrix };


Begin["`Private`"]

YoungDiagram::usage = "YoungDiagram[shape] displays shape in a Young diagram.\nA Young diagram is a finite collection of boxes, or cells, arranged in left-justified rows, with the row lengths in non-increasing order. Listing the number of boxes in each row gives a partition \[Lambda] of a non-negative integer n, the total number of boxes of the diagram. The Young diagram is said to be of shape \[Lambda], and it carries the same information as that partition.\nA Young diagram is also called a Ferrers diagram, particularly when represented using dots."

YoungDiagram[shape_?YoungShapeQ] :=
  YoungForm @ Map[Table[" ", #]&, YoungTrim @ shape]

FerrersDiagram[shape_?YoungShapeQ] :=
  Grid @ Map[Table["\[FilledCircle]", #]&, shape]


YoungShapeQ::usage="YoungShapeQ[shape] returns True if and only if shape is an integer partition, arranged in non-increasing order.\nA Young shape defines a Young diagram."

YoungShapeQ[_] = False

YoungShapeQ[pp:{__Integer?NonNegative}] := Apply[GreaterEqual, pp]
(* NOTE: Must allow 0 since some functions uses 0 in shape specification. *)


YoungTrim::usage="YoungTrim[shape] trims trailing zeros from shape."

YoungTrim[{kk__, Longest[0...]}] := {kk} /; 
  YoungShapeQ[{kk}]

YoungTrim[{rows__List, Longest[{}...]}] := {rows} /;
  anyYoungTableauQ[{rows}]


YoungTranspose::usage = "YoungTranspose[shape] reflects a partition 'shape' along the main diagonal.\nTransposeTableau[tb] reflects a standard Young tableau 'tb' along the main diagonal, creating a different tableau."

YoungTranspose[shape_?YoungShapeQ] := Module[
  { y },
  Table[
    First @ Last @ Position[shape, x_/;x>=y],
    {y, First @ shape}
   ]
 ]

YoungTranspose[tb_?anyYoungTableauQ] := Module[
  { new = YoungTranspose[Length /@ tb],
    i, j },
  Table[Part[tb, j, i], {i, Length[new]}, {j, Part[new,i]}]
 ]
(* NOTE: tb does not need to be a semi-standard Young tableau. Any Young-like
   tableau is allowed. This is useful in Schur transform. *)


YoungShape::usage = "YoungShape[tb] returns the shape, i.e., the integer partition of Young tableau tb."

YoungShape[tb_?anyYoungTableauQ] := Length /@ tb


CountYoungTableaux::usage = "CountYoungTableaux[shape] uses the hook length formula to count the number of standard Young tableaux of 'shape'.\nCountYoungTableaux[n] gives the total number of standard Young tableaux for all partitions of integer 'n'.\nBorrowed from NumberOfTableaux in Combinatorica package."

CountYoungTableaux[pp_?YoungShapeQ] := Module[
  { qq = YoungTranspose[pp],
    j, k },
  Factorial[Total @ pp] /
    Product[
      pp[[j]] + qq[[k]] - j - k + 1,
      {j, Length[pp]},
      {k, pp[[j]]}
     ]
 ]

CountYoungTableaux[n_Integer] :=
  Total @ Map[CountYoungTableaux, IntegerPartitions @ n]


nextPartition[pp_?YoungShapeQ] := Module[
  { i = First @ Last @ Position[pp, x_/;x>1],
    k = Length[pp],
    j, qr},
  j = Part[pp, i];
  qr = QuotientRemainder[j+k-i, j-1];
  Join[
    Take[pp, i-1],
    ConstantArray[j-1, Part[qr, 1]],
    If[Part[qr, 2] >= 1, {Part[qr, 2]}, {}]
   ]
 ] /; AnyTrue[pp, #>1&]

nextPartition[pp_?YoungShapeQ] := {Total @ pp} /; AllTrue[pp, #==1&]
(* Convention: at the last partition we cycle back to the first one. *)


permInversions[pi_?PermutationListQ]:=Sum[If[Part[pi,i]>Part[pi,j],1,0],{j,Length[pi]},{i,j-1}]; (* The number of inversions in a permutation; substitute for the corresponding combinatorica function. *)


GroupCharacters::usage = "GroupCharaters[group] returns the table of characters of the irreducible representations of 'group'. The characters of each irreducible representation is stored in a row vector.\nGroupCharacters[group, irr] gives a list of the characters of the irreducible representation 'irr'.\nGroupCharacters[group, irr, class] returns the character of the irreducible representation 'irr' of 'group' evaluated at the conjugacy class 'class'.\nFor a symmetric group, both irreducible representation and class are specified by integer partitions."

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
  CountYoungTableaux[shape] /; And[
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


GroupClassSize::usage = "GroupGlassSize[group, class] returns the number of elements in the conjugacy class 'class'."

GroupClassSize[SymmetricGroup[n_Integer], class_?YoungShapeQ] :=
  SymmetricGroupClassSize[class] /; n > 0

GroupClassSize[group_, g_] :=
  GroupOrder[group] / GroupCentralizerSize[group, g]


SymmetricGroupClassSize::usage="SymmetricGroupClassSize[class] returns the number of elements in the conjugacy class 'class' in SymmetricGroup[n].\nThe conjugacy class is specified by a partition of integer 'n'.\nThe inverse of SymmetricGroupClassSize[class] = GroupOrder[SymmetricGroup[n]] / SymmetricGroupCentralizerSize[class]; see, e.g., Sagan, The Symmetric Group (Springer, 2001) Section 1.1."

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
      columnIdx = Part[hashPosList, Times @@ hashPositionTupel];
      chrVect[[columnIdx]] += Times @@ Apply[
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
        {Times @@ Prime[supPartitionTupel[[r]]]},
        Prime @ Drop[pp,r]
       ]
     ]
   ];
  
  chrVect
 ]


KostkaMatrix::usage = "KostkaMatrix[n] returns the matrix of Kostka numbers of rank n."

KostkaMatrix[n_Integer] := Dot[
  SymmetricGroupCharacters[n],
  DiagonalMatrix[1 / (SymmetricGroupCentralizerSize /@ IntegerPartitions[n])],
  Transpose[CompoundYoungCharacters /@ IntegerPartitions[n]]
 ] /; n > 0


CharacterScalarProduct::usage = "CharacterScalarProduct[f, g, n] returns the scalar product of the class vectors f and g for a symmetric group of rank n."

CharacterScalarProduct[f_List, g_List, n_Integer] := Total[
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

anyYoungTableauQ::usage = "anyYoungTableauQ[tb] yields True if tb represents a Young tableau and False otherwise."

anyYoungTableauQ[tb:{__List}] := Apply[GreaterEqual, Length /@ tb]


YoungForm::usage = "YoungForm[tb] displays Young tableau tb in the conventional form."

YoungForm::notyt = "Data `` is not a Young tableau."

YoungForm[tb_?anyYoungTableauQ] :=
  Grid @ Map[Item[#, Frame->True]&, tb, {2}]

YoungForm[data_] := (
  Message[YoungForm::notyt, data];
  data
 )


YoungTableaux::usage = "YoungTableaux[shape] constructs all standard Young tableaux of 'shape' specified by an integer partition.\nYoungTableaux[n] constructs all standard Young tableaux of rank 'n'."

YoungTableaux[s_?YoungShapeQ] :=
  NestList[NextYoungTableau, FirstYoungTableau[s], CountYoungTableaux[s]-1]

YoungTableaux[n_Integer?Positive] :=
  Catenate @ Map[YoungTableaux, IntegerPartitions @ n]


FirstYoungTableau::usage = "FirstYoungTableau[p] constructs the first standard Young tableau with shape described by partition p."

FirstYoungTableau[shape_?YoungShapeQ] :=
  YoungTranspose @ LastYoungTableau @ YoungTranspose[shape]

LastYoungTableau::usage = "LastYoungTableau[p] constructs the last Young tableau with shape described by partition p."

LastYoungTableau[shape_?YoungShapeQ] :=
  FoldPairList[TakeDrop, Range[Total @ shape], shape]


NextYoungTableau::usage = "NextYoungTableau[tb] gives the standard Young tableau of the same shape as tb, following tb in lexicographic order."

(* NOTE 2021-10-27: It seems that the standard Young tableaux are ordered
   according the "last letter sequence". See Pauncz (1995a, Section 3.2). *)

NextYoungTableau[tb_?YoungTableauQ] := Module[
  { yy, shp, row, val, new },

  yy = Values @ KeySort @ Flatten @ MapIndexed[(#1->First[#2])&, tb, {2}];
  If[LessEqual @@ yy, Return @ FirstYoungTableau[Length /@ tb]];

  val = 1 + Length[First @ Split[yy, LessEqual]];
  row = First @ FirstPosition[tb, val];
  
  shp = Length /@ DeleteCases[tb, k_/;k>val, {2}];
  row = First @ Last @ Position[shp, shp[[row+1]]];
  shp[[row]]--;
  
  new = FirstYoungTableau[shp];
  If[ Length[new] < row,
    new = Append[new, {val}],
    new[[row]] = Append[new[[row]], val]
   ];

  new = Flatten @ MapIndexed[(#2->#1)&, new, {2}];
  ReplacePart[tb, new]
 ]


(**** <KetPermute> ****)

KetPermute::usage = "KetPermute[v, {q1, q2, ...}, cycles] returns a new Ket permuting the values of the particles q1, q2, ... in Ket v."

(* for Pauli Kets *)

KetPermute[Ket[ss__], perm:(_Cycles|_?PermutationListQ)] :=
  Ket @@ Permute[{ss}, perm]

KetPermute[Ket[ss__],
  group:(_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := Ket @@@ Permute[{ss}, group]

KetPermute[expr_,
  spec:(_Cycles|_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := expr /. { v_Ket :> KetPermute[v, spec] }

KetPermute[expr_, pp:{__Cycles}] :=
  Map[ KetPermute[expr, #]&, pp ]


(* for general Kets *)

KetPermute[v:Ket[_Association],
  qq:{__?SpeciesQ}, perm:(_Cycles|_?PermutationListQ)] := Module[
    { vv = v[qq] },
    vv = Permute[vv, perm];
    Ket[v, qq -> vv]
   ]

KetPermute[v:Ket[_Association], qq:{__},
  group:(_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := Module[
   { vv = v[qq] },
   vv = Permute[vv, group];
   Map[ Ket[v, qq -> #]&, vv ]
  ]

KetPermute[expr_, qq:{__},
  spec:(_Cycles|_SymmetricGroup|_AlternatingGroup|_PermutationGroup)
 ] := expr /. { v:Ket[_Association] :> KetPermute[v, qq, spec] }

KetPermute[expr_, qq:{__}, pp:{__Cycles}] :=
  Map[ KetPermute[expr, qq, #]&, pp ]

(* operator form *)
KetPermute[qq:{__}, spec_][v_] := KetPermute[v, qq, spec]

(**** </KetPermute> ****)


(**** KetSymmetrize ****)

KetSymmetrize::usage = "KetSymmetrize[expr, {s1, s2, \[Ellipsis]}, tbl] symmetrizes every kets appearing in expr according to polytabloid specified by standard Young tableau tbl.\n"

KetSymmetrize[bs_List, ss:{__?SpeciesQ}, tbl_?YoungTableauQ] := Module[
  { ts = YoungTranspose[tbl],
    qq, bb },
  qq = FoldPairList[TakeDrop, ss[[Flatten @ ts]], Length /@ ts];
  bb = Fold[Union @* KetSort, bs, qq];
  DeleteCases[
    Garner @ Union @ Map[KetSymmetrize[#, ss, tbl]&, bb],
    0
   ]
 ] /; NoneTrue[bs, FreeQ[#, Ket[_Association]]&]

KetSymmetrize[expr_] := With[
  { ss = NonCommutativeSpecies[expr] },
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
 Times @@ MapThread[SignatureTo, {a, b}]

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


PermutationMatrix::usage = "PermutationMatrix[perm, n] returns the n x n matrix representation of the permutation perm.\nPermutationMatrix[perm] first tries to find the proper dimension of the matrix from perm and returns the permutation matrix."

PermutationMatrix[perm_?PermutationCyclesQ] :=
  PermutationMatrix[ perm, Max @ Cases[perm, _Integer, Infinity] ]

PermutationMatrix[perm_?PermutationCyclesQ, n_Integer] := 
  Permute[ IdentityMatrix[n], perm ]


End[]

EndPackage[]
