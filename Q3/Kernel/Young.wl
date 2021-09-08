(* ::Package:: *)

(* Originally from: *)
(* :Author: Bernd Guenther *)
(* :Package Version: 2.0 *)
(* :Mathematica Version: 12.0 *)
(* :History: 2.0 Eliminated dependency on Combinatorica package. *)
   
BeginPackage["Q3`"];

`Young`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.5 $"][[2]], " (",
  StringSplit["$Date: 2021-09-08 18:21:01+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ YoungTableaux, YoungTableauQ, CountYoungTableaux,
  NextYoungTableau, LastYoungTableau, FirstYoungTableau,
  YoungTranspose, IntegerPartitionQ };

{ GroupClassSize, GroupCentralizerSize,
  SymmetricGroupCentralizerSize,
  GroupCharacters, SymmetricGroupCharacters,
  KostkaMatrix, CharacterScalarProduct };

{ KetPermute, KetSymmetrize };
{ PermutationMatrix };

{ CoxeterTest, NTranspDecomp,
  YoungsNaturalReprValue, YoungsNaturalRepresentation,
  YoungsSeminormalReprValue, YoungsSeminormalRepresentation,
  InvariantYMetric,
  YnrCharacterTest,
  CompoundYoungChar,
  NormSquareOfTableau, WeakLeftBruhatGraph };


Begin["`Private`"]

NTranspDecomp::usage="NTranspDecomp[pi_?PermutationListQ] represents pi as product of transpositions of immediate neighbors. An entry value of k in the returned list denotes the transposition (k,k+1).\[IndentingNewLine]Attention: Permutations are multiplied right to left like right operators, not like functions!"


ExpandNTrDecom::usage="ExpandNTrDecom[ntr_List] is the inverse operation of NTranspDecomp."


InvariantYMetric::usage="InvariantYMetric[\[Lambda]_?IntegerPartitionQ] is the scalar product invariant under Young's natural presentation corresponding to the integer partition \[Lambda]."


CoxeterTest::usage="CoxeterTest[ynr_] applied to the matrices of Young's natural representation checks whether these matrices satisfy Coxeter's relations, as they must. So unless you tamper with the definitions this function should always return TRUE."


YnrCharacterTest::usage="YnrCharacterTest[ynr_,\[Lambda]_] applied to the matrices of Young's natural representation corresponding to the integer partition \[Lambda] computes the character and compares it to the relevant entry in the character table. So unless you tamper with the definitions this function should always return TRUE. A complete test would be for instance: \[IndentingNewLine]testPartition=RandomPartition[5];\[IndentingNewLine]testYnr=YoungsNaturalRepresentation[testPartition];\[IndentingNewLine]CoxeterTest[testYnr]&&YnrCharacterTest[testYnr,testPartition]"


WeakLeftBruhatGraph::usage="WeakLeftBruhatGraph[\[Lambda]_?IntegerPartitionQ] Construct weak left Bruhat graph of standard tableaux.
Start with rowwise ordered tableau (observe that it is smallest with respect to weak left Bruhat ordering) and then do breadth first algorithm.
Output is a record with two components; first is the list of stanard tableaux.
Second is the list of weighted edges, where weight i means that the transposition (i,i+1) the first connected tableau to the second. The edges are given as three component record with the first two components denoting the indices of the connected tableaux and the third record the weight."


Seminormal2Natural::usage="Seminormal2natural[\[Lambda]_?IntegerPartitionQ] The transformation matrix turning the seminormal presentation into the natural presentation. Each row vector is the expansion of a natural basis vector in terms of the seminormal basis vectors."


NormSquareOfTableau::usage="NormSquareOfTableau[myTableau_] computes the norm squares of the seminormal basis vectors."


YoungsNaturalRepresentation::usage="YoungsNaturalRepresentation[\[Lambda]_?IntegerPartitionQ] computes the matrices of Young's natural representation of the symmetric group corresponding to the integer partition \[Lambda] by transforming the seminormal representation. The function returns the images of the transpositions of immediate neighbors, listed in order of the transposed elements. The matrices are supposed to operate from the right on row vectors."


YoungsSeminormalRepresentation::usage="YoungsSeminormalRepresentation[\[Lambda]_?IntegerPartitionQ] computes the matrices of Young's seminormal representation of the symmetric group corresponding to the integer partition \[Lambda]. The function returns the images of the transpositions of immediate neighbors, listed in order of the transposed elements. The matrices are supposed to operate from the right on row vectors."


YoungsNaturalReprValue::usage="YoungsNaturalReprValue[\[Lambda]_?IntegerPartitionQ,pi_?PermutationListQ] is the matrix assigned to permutation \[Pi] by Young's natural representation corresponding to partition \[Lambda]."


YoungsSeminormalReprValue::usage="YoungsSeminormalReprValue[\[Lambda]_?IntegerPartitionQ,pi_?PermutationListQ] is the matrix assigned to permutation \[Pi] by Young's seminormal representation corresponding to partition \[Lambda]."



IntegerPartitionQ::usage="IntegerPartitionQ[\[Lambda]] is true if and only if \[Lambda] is an integer partition, arranged in decreasing order."

IntegerPartitionQ[_] = False

IntegerPartitionQ[pp:{__Integer?NonNegative}] := Apply[GreaterEqual, pp]
(* NOTE: Must allow 0 since some functions uses 0 in shape specification. *)


YoungTranspose::usage = "YoungTranspose[shape] reflects a partition 'shape' along the main diagonal.\nTransposeTableau[tb] reflects a standard Young tableau 'tb' along the main diagonal, creating a different tableau."

YoungTranspose[shape_?IntegerPartitionQ] := Module[
  { y },
  Table[
    First @ Last @ Position[shape, x_/;x>=y],
    {y, First @ shape}
   ]
 ]

YoungTranspose[tb:{{__Integer?Positive}..}] := Module[
  { new = YoungTranspose[Length /@ tb],
    i, j },
  Table[Part[tb, j, i], {i, Length[new]}, {j, Part[new,i]}]
 ] /; IntegerPartitionQ[Length /@ tb]
(* NOTE: Cannot use tb_?YoungTableauQ since YoungTableauQ itself calls
   YoungTranspose. It would cause $RecursionsLimit::reclim2 error. *)


CountYoungTableaux::usage = "CountYoungTableaux[shape] uses the hook length formula to count the number of standard Young tableaux of 'shape'.\nCountYoungTableaux[n] gives the total number of standard Young tableaux for all partitions of integer 'n'.\nBorrowed from NumberOfTableaux in Combinatorica package."

CountYoungTableaux[pp_?IntegerPartitionQ] := Module[
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


nextPartition[pp_?IntegerPartitionQ] := Module[
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

nextPartition[pp_?IntegerPartitionQ] := {Total @ pp} /; AllTrue[pp, #==1&]
(* Convention: at the last partition we cycle back to the first one. *)


permInversions[pi_?PermutationListQ]:=Sum[If[Part[pi,i]>Part[pi,j],1,0],{j,Length[pi]},{i,j-1}]; (* The number of inversions in a permutation; substitute for the corresponding combinatorica function. *)


GroupCharacters::usage = "GroupCharaters[group] returns the table of characters of the irreducible representations of 'group'. The characters of each irreducible representation is stored in a row vector.\nGroupCharacters[group, irr] gives a list of the characters of the irreducible representation 'irr'.\nGroupCharacters[group, irr, class] returns the character of the irreducible representation 'irr' of 'group' evaluated at the conjugacy class 'class'.\nFor a symmetric group, both irreducible representation and class are specified by integer partitions."

GroupCharacters[SymmetricGroup[n_Integer]] :=
  SymmetricGroupCharacters[n] /; n > 0

GroupCharacters[SymmetricGroup[n_Integer], irr_?IntegerPartitionQ] :=
  SymmetricGroupCharacters[irr] /; Total[irr] == n

GroupCharacters[SymmetricGroup[n_Integer],
  irr_?IntegerPartitionQ, class_?IntegerPartitionQ] :=
  SymmetricGroupCharacters[irr, class] /;
  Total[irr] == Total[class] == n


SymmetricGroupCharacters::uasge = "SymmetricGroupCharacters[n] returns the table of characters of SymmetricGroup[n].\nSymmetricGroupCharacters[irr] returns a list of characters of the irreducible representation 'irr'.\nSymmetricGroupCharacters[irr, class] returns the character of the irreducible representation 'irr' evaluated at the conjugacy class 'class'.\nBoth 'irr' and 'class' are specified by partitions of integer 'n'."


SymmetricGroupCharacters[n_Integer] := With[
  { weights=SymmetricGroupCentralizerSize/@IntegerPartitions[n],
    rDimension=PartitionsP[n] },
  Module[
    { resTbl=CompoundYoungChar/@ IntegerPartitions[n],
      denomVector,kostkaNumbers },
    For[ k=2, k<=rDimension, k++,
      denomVector = resTbl[[k]]/weights;
      kostkaNumbers = (Dot[denomVector,#])&/@Take[resTbl,k-1];
      resTbl[[k]] -= Dot[kostkaNumbers, Take[resTbl,k-1]];
     ];
    resTbl
   ]
 ] /; n>0

SymmetricGroupCharacters[irr_?IntegerPartitionQ] :=
  characterSymmetricGroup[irr, #]& /@ IntegerPartitions[Total @ irr]  
  
SymmetricGroupCharacters[irr_?IntegerPartitionQ, class_?IntegerPartitionQ] :=
  characterSymmetricGroup[irr, class]


characterSymmetricGroup[{}, {}] := 1; 

characterSymmetricGroup[
  \[Lambda]_?IntegerPartitionQ, \[Rho]_?IntegerPartitionQ] :=
  CountYoungTableaux[\[Lambda]] /;
  Total[\[Lambda]] == Total[\[Rho]] &&
  Length[\[Rho]] >= 1 &&
  First[\[Rho]] == 1;


characterSymmetricGroup[
  \[Lambda]_?IntegerPartitionQ, \[Rho]_?IntegerPartitionQ] := With[
    { \[Rho]max=First[\[Rho]],\[Rho]0=Drop[\[Rho],1],
      \[Mu]=YoungTranspose[\[Lambda]],
      \[Nu]=Append[\[Lambda],0] },
    Sum[
      If[\[Lambda][[j]]+\[Mu][[i]] +1-j-i!=\[Rho]max,
        0,
        If[EvenQ[\[Rho]max+i-\[Lambda][[j]]], -1, 1] * 
          characterSymmetricGroup[
            Select[
              Table[
                If[k<j||\[Nu][[k]]<i, \[Nu][[k]], Max[\[Nu][[k+1]],i]-1],
                {k, Length[\[Lambda]]}
               ],
              (#>0)&
             ],
            \[Rho]0
           ]
       ],
      {j, 1, Length[\[Lambda]]},
      {i, 1, \[Lambda][[j]]}
     ]
   ] /;
  Total[\[Lambda]] == Total[\[Rho]] &&
  Length[\[Rho]] >= 1 &&
  First[\[Rho]] > 1;


GroupClassSize::usage = "GroupGlassSize[group, class] returns the number of elements in the conjugacy class 'class'."

GroupClassSize[SymmetricGroup[n_Integer], class_?IntegerPartitionQ] :=
  SymmetricGroupClassSize[class] /; n > 0

GroupClassSize[group_, g_] :=
  GroupOrder[group] / GroupCentralizerSize[group, g]


SymmetricGroupClassSize::usage="SymmetricGroupClassSize[class] returns the number of elements in the conjugacy class 'class' in SymmetricGroup[n].\nThe conjugacy class is specified by a partition of integer 'n'.\nThe inverse of SymmetricGroupClassSize[class] = GroupOrder[SymmetricGroup[n]] / SymmetricGroupCentralizerSize[class]; see, e.g., Sagan, The Symmetric Group (Springer, 2001) Section 1.1."

SymmetricGroupClassSize[class_?IntegerPartitionQ] :=
  GroupOrder[SymmetricGroup @ Total @ class] /
  SymmetricGroupCentralizerSize[class]


GroupCentralizerSize::usage = "GroupCentralizerSize[group, g] returns the number of elements in the conjugacy class containing the element 'g' of the group 'group'."

GroupCentralizerSize[SymmetricGroup[n_Integer], class_?IntegerPartitionQ] :=
  SymmetricGroupCentralizerSize[class] /; n > 0

GroupCentralizerSize[group_, g_] :=
  GroupOrder @ GroupCentralizer[group, g]


SymmetricGroupCentralizerSize::usage="SymmetricGroupCentralizerSize[\[Rho]_?IntegerPartitionQ] returns the size of the centralizer class of an element of cycle type \[Rho].\nThe inverse of SymmetricGroupCentralizerSize[\[Rho]] coincides, up to a factor fo the group order, with the size of the conjugacy class; that is, SymmetricGroupCentralizerSize[\[Rho]] = GroupOrder[SymmetricGroup[n]] / (the size of the class \[Rho])."

SymmetricGroupCentralizerSize[\[Rho]_?IntegerPartitionQ] := Apply[
  Times,
  Factorial /@ Counts[\[Rho]]
 ] * Apply[Times, \[Rho]];


CompoundYoungChar::usage="CompoundYoungChar[\[Lambda]_?IntegerPartitionQ] returns the composite Young character corresponding to the partition \[Lambda]."

CompoundYoungChar[pp_?IntegerPartitionQ] := Module[
  { chrVect=Table[0,{PartitionsP[Total[pp]]}],
    supPartitionTupel=Partition[pp,1],
    hashPositionTupel=Prime[pp],
    r,columnIdx },

  With[
    { hashPosList = SparseArray[
        Flatten @ MapIndexed[
          {Times @@ Prime[#1] -> First[#2]}&,
          IntegerPartitions[Total[pp]]
         ]
       ]
     },

    While[True,
      columnIdx=Part[hashPosList,Times@@hashPositionTupel];
      chrVect[[columnIdx]] += Times @@ Apply[
        Multinomial,
        Map[
          (Part[#,2])&,
          SplitBy[Sort[Flatten[Tally/@supPartitionTupel,1]],First],{2}
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
        Take[hashPositionTupel,r-1],
        {Times@@Prime[supPartitionTupel[[r]]]},Prime[Drop[pp,r]]
       ]
     ]
   ];
  chrVect
 ]


KostkaMatrix::usage="KostkaMatrix[n_Integer] returns the matrix of Kostka numbers of rank n."

KostkaMatrix[n_Integer] := Dot[
  SymmetricGroupCharacters[n],
  DiagonalMatrix[(1/SymmetricGroupCentralizerSize[#])& /@ IntegerPartitions[n]],
  Transpose[CompoundYoungChar /@ IntegerPartitions[n]]
 ] /; n > 0


CharacterScalarProduct::usage="CharacterScalarProduct[f_List,g_List,groupRank_Integer] returns the scalar product of the class vectors f and g."

CharacterScalarProduct[f_List,g_List,groupRank_Integer] := Dot[
  f*g,
  1 / (SymmetricGroupCentralizerSize /@ IntegerPartitions[groupRank])
 ] /;
  (groupRank>0) &&
  (Length[f]==PartitionsP[groupRank]) &&
  (Length[g]==PartitionsP[groupRank])


NTranspDecomp[pi_?PermutationListQ]:=
Module[{idx=1,transList={},pi2=pi},While[idx<Length[pi2],
If[pi2[[idx]]<pi2[[idx+1]],idx++,
transList=Append[transList,idx];
pi2=System`Permute[pi2,System`Cycles[{{idx,idx+1}}]];
If[idx>1,idx--,idx++]]];transList];


ExpandNTrDecom[ntr_List]:=PermutationList[Apply[PermutationProduct,System`Cycles[{{#,#+1}}]&/@ntr]];


CoxeterTest[ynr_]:=And[Apply[And,(#.#==IdentityMatrix[Length[ynr[[1]]]])&/@ynr],
And@@Table[ynr[[r]].ynr[[r+1]].ynr[[r]]==ynr[[r+1]].ynr[[r]].ynr[[r+1]],{r,Length[ynr]-1}],
And@@Flatten[Table[ynr[[r]].ynr[[s]]==ynr[[s]].ynr[[r]],
{r,Length[ynr]-2},{s,r+2,Length[ynr]}]]];


cTypeRepresentative[\[Lambda]_?IntegerPartitionQ]:=
Flatten[Apply[Range,Transpose[{Prepend[Drop[#,-1]+1,1],#-1}],{1}]]&[Accumulate[\[Lambda]]];


YnrCharacterTest[ynr_,\[Lambda]_]:=(
  Append[
    Tr /@ Apply[
      Dot,
      Extract[ynr,#]& /@ Partition[#,1]& /@ cTypeRepresentative /@
        Drop[IntegerPartitions[Total[\[Lambda]]],-1], {1}
     ],
    Length[ynr[[1]]]
   ] == Part[
     SymmetricGroupCharacters @ Total[\[Lambda]],
     Part[Position[IntegerPartitions[Total[\[Lambda]]],\[Lambda]], 1, 1]
    ]
 );


InvariantYMetric[\[Lambda]_?IntegerPartitionQ]:=
With[{wlbg1=WeakLeftBruhatGraph[\[Lambda]],
transform=Seminormal2Natural[\[Lambda]]},
Times@@Factorial/@YoungTranspose[\[Lambda]]transform.DiagonalMatrix[NormSquareOfTableau/@First/@wlbg1].Transpose[transform]];


predPermutations1[invPList_,curPos_,sourcePos_]:=MapIndexed[{System`Permute[invPList,First[#1]],{curPos,sourcePos,Last[#1]}}&,{System`Cycles[{{#,#+1}}],#}&/@Flatten[Position[Differences[invPList],x_/;x<0]]];


predPermutations2[invPListList_,curPos_,sourcePos_]:=
MapIndexed[{First[Part[#1,1]],Function[x,ReplacePart[x,1->Part[x,1]+First[#2]]]/@Part[#1,2]}& ,
Transpose/@Gather[
Join@@MapIndexed[predPermutations1[#1,curPos,sourcePos+First[#2]]&,
First/@invPListList],
(Part[#1,1]==Part[#2,1])&]];


rowWiseInvPList[\[Lambda]_?IntegerPartitionQ]:=
PermutationList[System`InversePermutation[PermutationCycles[Join@@YoungTranspose[(Range@@#)&/@Drop[FoldList[{1+Last[#1],#2+Last[#1]}&,{0,0},\[Lambda]],1]]]],Total[\[Lambda]]];


WeakLeftBruhatGraph[\[Lambda]_?IntegerPartitionQ]:=
With[{x=rowWiseInvPList[\[Lambda]],n=Total[\[Lambda]],
shape=Drop[FoldList[{1+Last[#1],#2+Last[#1]}&,{0,0},YoungTranspose[\[Lambda]]],1]},
Function[v,{YoungTranspose[Function[w,Take[PermutationList[System`InversePermutation[PermutationCycles[Part[v,1]]],n],w]]/@shape],
Part[v,2]}]/@
Flatten[Nest[Append[#,predPermutations2[
Last[#],Length[Flatten[#,1]],Length[Flatten[#,1]]-Length[Last[#]]]]&,
{{{x,{}}}},permInversions[x]],1]];


youngAuxiliary[\[Lambda]_,modus_]:=
(* modus=1: only transform; modus=2: natural presentation; modus=3: seminormal presentation *)
With[{wlbg1=WeakLeftBruhatGraph[\[Lambda]]},
Module[{wlbgAdjacencyLists,contentVectors,spanningTree,transform,tnorm,tinv,semimatrix},
(* The following expression computes the adjacency lists of the weak left Bruhat graph;an entrySubscript[a, ij]may have four different meanings,depending on the following cases:i) IfSubscript[a, ij]=ithen j and j+1 are contained in the same row of tableau i.ii) IfSubscript[a, ij]=-ithen j and j+1 are contained in the same column of tableau i.iii) IfSubscript[a, ij]\[NotEqual]\[PlusMinus]ibutSubscript[a, ij]<0then i and i+1 appear inverted in tableau i and application of the admissible transposition (j,j+1) turns tableau i into tableauSubscript[a, ij],thus removing an inversion.iv) IfSubscript[a, ij]\[NotEqual]\[PlusMinus]ibutSubscript[a, ij]>0then i and i+1 appear in correct order in tableau i and application of the admissible transposition (j,j+1) turns tableau i into tableauSubscript[a, ij],thus adding an inversion. *)
wlbgAdjacencyLists=Normal[SparseArray[
(({Part[#,1],Part[#,3]}->Part[#,2])&/@ Flatten[Part[#,2]&/@wlbg1,1])
~Join~
(({Part[#,2],Part[#,3]}->-Part[#,1])&/@ Flatten[Part[#,2]&/@wlbg1,1])
~Join~
Flatten[MapIndexed[Function[{v,w},Function[u,{First[w],u}->First[w]]/@v],Function[v,Last/@Select[Transpose[{Flatten[Function[u,Append[u,0]]/@(Differences/@v)],Flatten[v]}],Function[u,First[u]==1]]]/@(First/@wlbg1)]]
~Join~
Flatten[MapIndexed[Function[{v,w},Function[u,{First[w],u}->-First[w]]/@v],Function[v,Last/@Select[Transpose[{Flatten[Function[u,Append[u,0]]/@(Differences/@v)],Flatten[v]}],Function[u,First[u]==1]]]/@(YoungTranspose[#]&/@(First/@wlbg1))]],{Length[wlbg1],Total[\[Lambda]]-1}]
];
contentVectors=Function[u,Normal[SparseArray[Flatten[MapIndexed[Function[{v1,v2},{v1->Last[v2]-First[v2]}],First[u],{2}]],{Total[\[Lambda]]}]]]/@wlbg1;
If[modus!=3,
	spanningTree=If[Length[wlbg1]==1,{},First/@MapIndexed[Drop[#1/.(Rule[{a_},b_]):>{First[#2],a,b},-1]&,ArrayRules/@SparseArray[Flatten[Function[v,Function[u,{Part[u,2],Part[u,1]}->Part[u,3]]/@Last[v]]/@Drop[wlbg1,1]],{Length[wlbg1]-1,Length[wlbg1]}]]];
	transform=SparseArray[{Length[wlbg1],Length[wlbg1]}->1,{Length[wlbg1],Length[wlbg1]}];
	Module[{k,r,s,x},For[i=Length[spanningTree],i>0,i--,
	(* e_i = s_r e_k is the base vector to be constructed. *)
	k=Part[spanningTree,i,2];
	r=Part[spanningTree,i,3];
	For[j=k,j<=Length[wlbg1],j++,
	(* v_j is a Young vector appearing in e_k with coefficient x. *)
	x=Part[transform,k,j];
	If[x==0,Continue[]];
	s=Part[wlbgAdjacencyLists,j,r];
	Switch[s,
	(* row inversion *) j,Part[transform,i,j]+=x,
	(* column inversion *) -j,Part[transform,i,j]-=x,
	(* removing an inversion *) x_/;x<0,Part[transform,i,j]+=x/(Part[contentVectors,j,r+1]-Part[contentVectors,j,r]);
	Part[transform,i,-s]+= x (1-1/(Part[contentVectors,j,r+1]-Part[contentVectors,j,r])^2),
	(* admissibly adding an inversion *)_,Part[transform,i,s]+=x;
	Part[transform,i,j]+=x/(Part[contentVectors,j,r+1]-Part[contentVectors,j,r]);
	]]]];
	tnorm=Normal[transform]];
If[modus==1,Return[tnorm]];
semimatrix=Normal[SparseArray[Flatten[Module[{s},Table[s=Part[wlbgAdjacencyLists,k,r];
Switch[s,
(* row inversion *) k,{{r,k,k}->1},
(* column inversion *) -k,{{r,k,k}->-1},
(* removing an inversion *) x_/;x<0,
{{r,k,k}->1/(Part[contentVectors,k,r+1]-Part[contentVectors,k,r]),
{r,k,-s}->1-1/(Part[contentVectors,k,r+1]-Part[contentVectors,k,r])^2},
(* admissibly adding an inversion *)_,
{{r,k,k}->1/(Part[contentVectors,k,r+1]-Part[contentVectors,k,r]),
{r,k,s}->1}],
{r,Total[\[Lambda]]-1},{k,Length[wlbg1]}]]],
{Total[\[Lambda]]-1,Length[wlbg1],Length[wlbg1]}]];
If[modus==3,Return[semimatrix]];
tinv=Inverse[tnorm];
tnorm.#.tinv&/@ semimatrix
]];


Seminormal2Natural[\[Lambda]_?IntegerPartitionQ]:=youngAuxiliary[\[Lambda],1]/; Total[\[Lambda]]>1


YoungsNaturalRepresentation[\[Lambda]_?IntegerPartitionQ]:=youngAuxiliary[\[Lambda],2]/; Total[\[Lambda]]>1


YoungsSeminormalRepresentation[\[Lambda]_?IntegerPartitionQ]:=youngAuxiliary[\[Lambda],3]/; Total[\[Lambda]]>1


NormSquareOfTableau[myTableau_] := With[
  {trshape=YoungTranspose[Length/@myTableau]},
  Product[
    If[((i2>i1)\[Or](j2>j1))\[And](Part[myTableau,i1,j1]>Part[myTableau,i2,j2]),
1-1/(i1-j1-i2+j2)^2,1],
  {j1,1,Length[trshape]},{i1,1,Part[trshape,j1]},
  {j2,j1,Length[trshape]},{i2,1,Part[trshape,j2]}]
 ]


YoungsNaturalReprValue[pp_?IntegerPartitionQ,pi_?PermutationListQ]:=If[pi==Range[Total[pp]],IdentityMatrix[CountYoungTableaux[pp]],Dot@@Extract[YoungsNaturalRepresentation[pp],Partition[NTranspDecomp[pi],1]]]/;Total[pp]==Length[pi];


YoungsSeminormalReprValue[pp_?IntegerPartitionQ,pi_?PermutationListQ] := If[
  pi==Range[Total[pp]],
  IdentityMatrix[CountYoungTableaux[pp]],
  Dot @@ Extract[
    YoungsSeminormalRepresentation[pp],
    Partition[NTranspDecomp[pi], 1]
   ]
 ] /; Total[pp]==Length[pi];



(*
 * Borrowed from Combinatorica`
 *)

YoungTableaux::usage = "YoungTableaux[shape] constructs all standard Young tableaux of 'shape' specified by an integer partitio.\nYoungTableaux[n] constructs all standard Young tableaux of rank 'n'."

YoungTableaux[s_?IntegerPartitionQ] :=
  NestList[NextYoungTableau, FirstYoungTableau[s], CountYoungTableaux[s]-1]

YoungTableaux[n_Integer?Positive] :=
  Catenate @ Map[YoungTableaux, IntegerPartitions @ n]


YoungTableauQ::usage = "YoungTableauQ[t] yields True if and only if t represents a standard Young tableau."

YoungTableauQ[{}] = True

YoungTableauQ[tb:{__List}] := And [
  Apply[And, LessEqual @@@ tb],
  Apply[And, LessEqual @@@ YoungTranspose[tb]],
  Apply[GreaterEqual, Length /@ tb],
  Apply[GreaterEqual, Length /@ YoungTranspose[tb]]
 ]


FirstYoungTableau::usage = "FirstYoungTableau[p] constructs the first standard Young tableau with shape described by partition p."

FirstYoungTableau[s_?IntegerPartitionQ] :=
  YoungTranspose @ LastYoungTableau @ YoungTranspose[s]

LastYoungTableau::usage = "LastYoungTableau[p] constructs the last Young tableau with shape described by partition p."

LastYoungTableau[s_?IntegerPartitionQ] :=
  FoldPairList[TakeDrop, Range[Total @ s], s]


NextYoungTableau::usage = "NextYoungTableau[tb] gives the standard Young tableau of the same shape as tb, following tb in lexicographic order."

NextYoungTableau[tb_?YoungTableauQ] := Module[
  { yy, shp, row, val, i, new },

  yy = RowsInTableau[tb];
  If[LessEqual @@ yy, Return @ FirstYoungTableau[Length /@ tb]];

  val = First @ FirstPosition[
    FoldPairList[{#1 <= #2, #2}&, First @ yy, Rest @ yy],
    False
   ];
  val++;
  
  shp = Length /@ DeleteCases[tb, k_/;k>val, {2}];
  row = First @ Last @ Position[ shp,
    shp[[First @ FirstPosition[tb, val] + 1]]
   ];
  shp[[row]]--;
  new = FirstYoungTableau[shp];
  If[ Length[new] < row,
    new = Append[new, {val}],
    new[[row]] = Append[new[[row]], val]
   ];
  Join[
    Table[
      Join[new[[i]], Select[tb[[i]], (#>val)&]],
      {i, Length @ new}
     ],
    Table[tb[[i]], {i, Length[new]+1, Length @ tb}]
   ]
 ]


RowsInTableau::usage = "RowsInTableau[tb] returns a list of rows where each integer appear in the standard Young tableau 'tb'."

RowsInTableau[tb_] := Module[
  { nn = Range[Length @ Flatten @ tb] },
  Map[First[FirstPosition[tb, #]]&, nn]
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
  { qq = ss[[Flatten@tbl]],
    aa, bb, cc, new },
  aa = Flatten /@ Tuples[Permutations /@ tbl];
  new = YoungTranspose[tbl];
  bb = Tuples[Permutations /@ new];
  cc = yngSignatureTo[new, #] & /@ bb;
  bb = Flatten /@ YoungTranspose /@ bb;
  expr /. {
    v : Ket[_Association] :> 
      Dot[Ket[ss -> Permute[v[qq], #]]& /@ bb, cc]
   } /. {
     w : Ket[_Association] :> 
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

KetSymmetrize[expr_, 1] := expr /. {v_Ket :> KetSymmetize[v, 1]}


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
