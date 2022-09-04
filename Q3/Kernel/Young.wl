(* -*- mode: Mathematica -*- *)

(* N.B. Some functions have been borrowed from the legacy Combinatorica
   package and from Bernd Buenther's IrrCharSymGrp.m v2.0 (posted on the
   Wolfram Community). *)

BeginPackage["Q3`"];

`Young`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.109 $"][[2]], " (",
  StringSplit["$Date: 2022-09-04 10:32:19+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ YoungDiagram, FerrersDiagram,
  YoungShape, YoungShapeQ };

{ YoungTranspose, YoungTrim };

{ YoungTableauQ, YoungTableaux, YoungTableauCount, YoungForm, 
  NextYoungTableau, LastYoungTableau, FirstYoungTableau,
  YoungTranspose };

{ GroupClassSize, SymmetricGroupClassSize,
  GroupCentralizerSize, SymmetricGroupCentralizerSize,
  GroupCharacters, SymmetricGroupCharacters,
  CharacterScalarProduct,
  CompoundYoungCharacters, KostkaMatrix };

{ InversionVector, AdjacentTranspositions };

{ YoungDistance };

(**** Obsolete ****)

{ CountYoungTableaux }; (* renamed *)


Begin["`Private`"]

Format[ Ket[tbs__?anyYoungTableauQ] ] := Ket @@ Map[YoungForm, {tbs}]


YoungDiagram::usage = "YoungDiagram[shape] displays shape in a Young diagram.\nYoungDiagram[yt] displays the Young diagram hosting Young tableau yt.\nA Young diagram is a finite collection of boxes, or cells, arranged in left-justified rows, with the row lengths in non-increasing order. Listing the number of boxes in each row gives a partition \[Lambda] of a non-negative integer n, the total number of boxes of the diagram. The Young diagram is said to be of shape \[Lambda], and it carries the same information as that partition.\nA Young diagram is also called a Ferrers diagram, particularly when represented using dots."

YoungDiagram[shape_?YoungShapeQ] :=
  YoungForm @ Map[Table[" ", #]&, YoungTrim @ shape]

YoungDiagram[yt_?anyYoungTableauQ] := YoungDiagram[YoungShape @ yt]


FerrersDiagram::usage = "FerrersDiagram[shape] displays shape in a Ferrers diagram.\nYoungDiagram[yt] displays the Ferrers diagram hosting Young tableau yt.\nA Young diagram is a finite collection of boxes, or cells, arranged in left-justified rows, with the row lengths in non-increasing order. Listing the number of boxes in each row gives a partition \[Lambda] of a non-negative integer n, the total number of boxes of the diagram. The Young diagram is said to be of shape \[Lambda], and it carries the same information as that partition.\nA Young diagram is also called a Ferrers diagram, particularly when represented using dots."

FerrersDiagram[shape_?YoungShapeQ] :=
  Grid @ Map[Table["\[FilledCircle]", #]&, shape]

FerrersDiagram[yt_?anyYoungTableauQ] := FerrersDiagram[YoungShape @ yt]


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


YoungTableauCount::usage = "YoungTableauCount[shape] uses the hook length formula to count the number of standard Young tableaux of 'shape'.\nYoungTableauCount[n] gives the total number of standard Young tableaux for all partitions of integer 'n'.\nBorrowed from NumberOfTableaux in Combinatorica package."

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


CountYoungTableaux[args__] := (
  Message[Q3General::renamed, "CountYoungTableaux", "YoungTableauCount"];
  YoungTableauCount[args]
 )


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

anyYoungTableauQ::usage = "anyYoungTableauQ[tb] yields True if tb represents a Young tableau (not necessarily semi-standard) and False otherwise."

anyYoungTableauQ[tb:{__List}] := Apply[GreaterEqual, Length /@ tb]


YoungForm::usage = "YoungForm[tb] displays Young tableau tb in the conventional form."

YoungForm::notyt = "Data `` is not of the Young-tableau form."

YoungForm[tb_?anyYoungTableauQ] :=
  Grid @ Map[Item[#, Frame->True]&, tb, {2}]

YoungForm[data_] := (
  Message[YoungForm::notyt, data];
  data
 )


YoungTableaux::usage = "YoungTableaux[shape] constructs all standard Young tableaux of 'shape' specified by an integer partition.\nYoungTableaux[n] constructs all standard Young tableaux of rank 'n'."

YoungTableaux[s_?YoungShapeQ] :=
  NestList[NextYoungTableau, FirstYoungTableau[s], YoungTableauCount[s]-1]

YoungTableaux[n_Integer?Positive] :=
  Catenate @ Map[YoungTableaux, IntegerPartitions @ n]


FirstYoungTableau::usage = "FirstYoungTableau[p] constructs the first standard Young tableau with shape described by partition p."

FirstYoungTableau[shape_?YoungShapeQ] :=
  YoungTranspose @ LastYoungTableau @ YoungTranspose[shape]


LastYoungTableau::usage = "LastYoungTableau[p] constructs the last Young tableau with shape described by partition p."

LastYoungTableau[shape_?YoungShapeQ] :=
  TakeList[Range @ Total @ shape, shape]


NextYoungTableau::usage = "NextYoungTableau[tb] gives the standard Young tableau of the same shape as tb, following tb in lexicographic order."

(* NOTE 2021-10-27: It seems that the standard Young tableaux are ordered
   according to the "last letter sequence". See Pauncz (1995a, Section 3.2). *)

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


(**** <Permutation> ****)

Permutation::usage = "Permutation[cyc,{s1,s2,\[Ellipsis]}] represents the permutation operator acting on species {s1,s2,\[Ellipsis]}."

Permutation::cyc = "`` does not represent a valid permutation in disjoint cyclic form. See PermutationCyclesQ."

AddElaborationPatterns[_Permutation]

Permutation[Cycles[{}], qq:{__?SpeciesQ}] := 1

Permutation[cyc_, ss:{__?SpeciesQ}] :=
  Permutation[cyc, FlavorNone @ ss] /;
  Not @ FlavorNoneQ[ss]

Permutation /:
HoldPattern @ Dagger @ Permutation[cyc_, ss:{__?SpeciesQ}] :=
  Permutation[InversePermutation[cyc], ss]

Permutation /:
HoldPattern @ Elaborate @
  Permutation[cyc:(_Cycles|_?PermutationListQ), ss:{__?SpeciesQ}] :=
  Module[
    { bs = Basis @ ss },
    If[ Not @ PermutationCyclesQ[cyc],
      Message[Permutation::cyc, cyc];
      Return[1]
     ];
    Elaborate @ Total @ Map[Dyad[KetPermute[#, cyc, ss], #, ss]&, bs]
   ]

Permutation /:
HoldPattern @ Matrix[op_Permutation, rest___] := Matrix[Elaborate[op], rest]


Permutation /:
HoldPattern @ Multiply[pre___,
  ops:Repeated[Permutation[_, qq:{__?SpeciesQ}], {2, Infinity}],
  post___] :=
  Multiply[pre,
    Permutation[PermutationProduct @@ Reverse[First /@ {ops}], qq],
    post]


Permutation /:
HoldPattern @ Multiply[pre___,
  Permutation[spec_, qq:{__?SpeciesQ}], v_Ket,
  post___] :=
  Multiply[pre, KetPermute[v, spec, qq], post]

Permutation /:
HoldPattern @ Multiply[pre___,
  v_Bra, Permutation[spec_, qq:{__?SpeciesQ}],
  post___] :=
  Multiply[pre, Dagger @ KetPermute[Dagger @ v, spec, qq], post]

Permutation /:
HoldPattern @ Multiply[
  pre___,
  Permutation[spec_, qq:{__?SpeciesQ}],
  Dyad[a_Association, b_Association, c_List],
  post___
 ] := Multiply[
   pre,
   Dyad[ KetPermute[Ket[a], spec, qq], Ket[b], c ],
   post
  ] /; ContainsAll[c, FlavorNone @ qq]

Permutation /:
HoldPattern @ Multiply[
  pre___,
  Dyad[a_Association, b_Association, c_List],
  Permutation[spec_, qq:{__?SpeciesQ}],
  post___
 ] := Multiply[
   pre,
   Dyad[ Ket[a], KetPermute[Ket[b], spec, qq], c ],
   post
  ] /; ContainsAll[c, FlavorNone @ qq]


(* NOTE *)

(* This method is significantly slower than the above methods.
   It also overwrites the previous code pieces, so do not include it. *)

(*
Permutation /:
HoldPattern @ Multiply[pre___,
  op:Permutation[_, {__?SpeciesQ}],
  post___] :=
  Multiply[pre, Elaborate @ op, post]
 *)

(**** </Permutation> ****)


(**** <PermutationMatrix> ****)

(* PermutationMatrix is now included in Mathematica since v13.1. *)

If[ $VersionNumber < 13.1,
  PermutationMatrix::usage = "PermutationMatrix[perm, n] returns the n x n matrix representation of the permutation perm.\nPermutationMatrix[perm] first tries to find the proper dimension of the matrix from perm and returns the permutation matrix.";

  PermutationMatrix[perm_?PermutationCyclesQ] :=
    PermutationMatrix[ perm, Max @ Cases[perm, _Integer, Infinity] ];

  PermutationMatrix[perm_?PermutationCyclesQ, n_Integer] := 
    Transpose @ Permute[ IdentityMatrix[n], perm ];
 ]

(**** </PermutationMatrix> ****)


(**** <KetPermute> ****)

KetPermute::usage = "KetPermute[vec, perm] returns a new state vector where each Ket[\[Ellipsis]] in state vector vec is replaced by a new one with the logical values permuted according to permutation perm.\nKetPermute[vec, {q1, q2, ...}, perm] returns a new state vector permuting the values of the particles q1, q2, ... in each Ket[<|\[Ellipsis]|>] in state vector vec according to permutation perm.\nPermutation perm may be a group such as SymmetricGroup, PermutationGroup, AlternatingGroup, or a list of Cycles, where a list of state vectors are returned after applying all elements of the group or list."

$PermutationSpec = Alternatives[_?PermutationListQ, _Cycles]

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


(* for Specht basis states *)
(* See also Krovi (2019). *)

KetPermute[Ket[yt_?YoungTableauQ], Cycles @ {{x_, y_}}] := Module[
  { xx = FirstPosition[yt, x],
    yy = FirstPosition[yt, y],
    dd, tt },
  Which[
    First[xx] == First[yy], Ket[yt],
    Last[xx] == Last[yy], -Ket[yt],
    True,
    dd = 1 / YoungDistance[x, y, yt];
    tt = ReplaceAll[yt, {x -> y, y -> x}];
    Ket[yt] * dd + Ket[tt] * Sqrt[1-dd^2]
   ]
 ] /; x+1 == y


KetPermute[Ket[yt_?YoungTableauQ], cc_Cycles] :=
  Garner @ Fold[KetPermute, Ket[yt], AdjacentTranspositions @ cc]

KetPermute[Ket[yt_?YoungTableauQ], perm_?PermutationListQ] :=
  Garner @ Fold[KetPermute, Ket[yt], AdjacentTranspositions @ perm]


(* for Pauli Kets *)

KetPermute[Ket[ss__], spec:$PermutationSpec] :=
  Ket @@ Permute[{ss}, spec]

KetPermute[Ket[ss__], group:$PermutationGroups] :=
  Ket @@@ Permute[{ss}, group]


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


(* backward compatibility *)

KetPermute[expr_, qq:{__?SpeciesQ}, spec_] := (
  Message[Q3General::changed, KetPermute, "The list of species must come last."];
  KetPermute[expr, spec, qq]
 )

(**** </KetPermute> ****)


(**** KetSymmetrize ****)

KetSymmetrize::usage = "KetSymmetrize[expr, {s1, s2, \[Ellipsis]}, tbl] symmetrizes every kets appearing in expr according to polytabloid specified by standard Young tableau tbl.\n"

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


InversionVector::usage = "InversionVector[perm] returns the inversion vector corresponding to permutation perm.\nThe number of elements greater than i to the left of  i in a permutation gives the ith element of the inversion vector (Skiena 1990, p. 27).\nTotal[InversionVector[perm]] equals to the number of inversions in permtuation perm as well as to the length of perm (i.e., the smallest number of adjacent transpositions combining to perm).\nSee also Combinatorica`ToInversionVector."

InversionVector[cyc_Cycles] := InversionVector[PermutationList @ cyc]

InversionVector[p_?PermutationListQ] := Module[
  {new = Take[p, #] & /@ InversePermutation[p]},
  Most@MapThread[
    Function[{x, y}, Count[x, _?(# > y &)]], {new, Range[Length@p]}]
 ] /; (Length[p] > 0)


(**** <AdjacentTranspositions> ****)

AdjacentTranspositions::usage = "AdjacentTranspositions[perm] returns a list of adjacent transpositions that combine to the permtuation perm."

(* TODO: Requires some optimization. *)

AdjacentTranspositions[prm_?PermutationListQ] := 
  AdjacentTranspositions @ PermutationCycles[prm]

AdjacentTranspositions[Cycles[pp:{__List}]] := Module[
  { qq = ChainBy[#, List]& /@ pp },
  qq = Sort /@ Flatten[Reverse /@ qq, 1];
  Cycles /@ List /@ Catenate[theAdjacent /@ qq]
 ]

theAdjacent[{x_Integer, y_Integer}] := With[
  {cc = ChainBy[Range[x, y], List]},
  Join[cc, Reverse @ Most @ cc]
 ] /; x < y

(**** </AdjacentTranspositions> ****)


YoungDistance::usage = "YoungDistance[x, y, yt] returns the Manhattan distance between boxes corresponding to letters x and y.\nNote that unlike the built-in ManhattanDistance function, it may be negative."

YoungDistance[x_Integer, y_Integer, yt_?YoungTableauQ] := Module[
  { xx = FirstPosition[yt, x],
    yy = FirstPosition[yt, y] },
  Dot[yy - xx, {-1, 1}]
 ]


End[]

EndPackage[]
