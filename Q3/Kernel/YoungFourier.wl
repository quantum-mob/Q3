(* ::Package:: *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ YoungOGS, YoungOGSn,
  FromYoungOGS };

{ YoungDualOGS, YoungDualOGSn,
  FromYoungDualOGS };

{ KawanoSekigawaMatrix,
  AdaptedYoungFourier };

{ YoungFourierMatrix, YoungFourier };
{ YoungFourierBasis, YoungRegularBasis };
{ YoungLeftRepresentation,
  YoungRightRepresentation,
  YoungNormalRepresentation,
  YoungSeminormalRepresentation,
  YoungSeminormalMetric };

{ LegacyNormalRepresentation };

{ YoungBruhatGraph };

{ LeftRegularRepresentation,
  RightRegularRepresentation };

{ YoungClebschGordan,
  YoungClebschGordanTransform,
  HarrowClebschGordanTransform };

Begin["`Private`"]

(**** <YoungOGS> ****)
(* See also Kawano16a and Shwartz19a *)

YoungOGS::usage = "YoungOGS[perm, n] returns the standard ordered generating system (OGS) canonical form of the symmetric group of degree n."

SyntaxInformation[YoungOGS] = {
  "ArgumentsPattern" -> {_, _}
 }

YoungOGS[prm_Cycles, n_Integer] :=
  theYoungOGS @ PermutationList[prm, n]

YoungOGS[prm_?PermutationListQ, n_Integer] := 
  theYoungOGS @ PermutationList[prm, n]

YoungOGS[elm:{(_Cycles|_List?PermutationListQ)...}, n_Integer] :=
  Map[YoungOGS[#, n]&, elm]


theYoungOGS[prm_List] := 
  If[OrderedQ @ prm, {0}, {1}] /; Length[prm] == 2

theYoungOGS[prm_List] := Module[
  { n = Length[prm],
    new = prm,
    pow, pos },
  pos = First @ FirstPosition[new, n];
  pow = Mod[pos - n, n];
  If[ pow > 0,
    gnr = RotateLeft[Range @ n]; (* Cycles[{{1,2,...,k}}] *)
    new = PermutationProduct[PermutationPower[gnr, pow], new];
    pow = Mod[-pow, n]
  ];
  Append[theYoungOGS[Most @ new], pow] /; n > 2
]


YoungOGSn::usage = "YoungOGSn[prm, n] converts to an integer the standard OGS canonical form corresponding to permutation prm for the symmetric group of degree n."

SyntaxInformation[YoungOGSn] = {
  "ArgumentsPattern" -> {_, _}
 }

YoungOGSn[spec_, n_Integer] := Module[
  { ogs = YoungOGS[spec, n],
    fac },
  fac = Range[2, n];
  Dot[ogs, n! / fac!]
]


FromYoungOGS::usage = "FromYoungOGS[ogs] returns the permtuation corresponding to the standard OGS canonical form ogs."

FromYoungOGS[ogs_List] := Module[
  { n = 1 + Length[ogs],
    gg, pp },
  gg = Table[Cycles @ {Range[k]}, {k, 2, n}];
  pp = Thread @ PermutationPower[gg, ogs];
  Apply[PermutationProduct, Reverse @ pp]
]

(**** </YoungOGS> ****)


(**** <YoungDualOGS> ****)
(* See also Kawano16a and Shwartz19a *)

YoungDualOGS::usage = "YoungDualOGS[perm, n] returns the dual-standard ordered generating system (OGS) canonical form of the symmetric group of degree n."

SyntaxInformation[YoungDualOGS] = {
  "ArgumentsPattern" -> {_, _}
 }

YoungDualOGS[prm_Cycles, n_Integer] :=
  theYoungDualOGS @ PermutationList[prm, n]

YoungDualOGS[prm_?PermutationListQ, n_Integer] := 
  theYoungDualOGS @ PermutationList[prm, n]


theYoungDualOGS[prm_List] := 
  If[OrderedQ @ prm, {0}, {1}] /; Length[prm] == 2

theYoungDualOGS[prm_List] := Module[
  { n = Length[prm],
    new = prm,
    pow },
  pow = Mod[n - new[[n]], n];
  If[ pow > 0,
    gnr = RotateLeft[Range @ n]; (* Cycles[{{1,2,...,k}}] *)
    new = PermutationProduct[new, PermutationPower[gnr, pow]];
    pow = Mod[-pow, n]
  ];
  Append[theYoungDualOGS[Most @ new], pow] /; n > 2
]


YoungDualOGSn::usage = "YoungDualOGSn[prm] converts to an integer the dual-standard OGS canonical form corresponding to permutation prm."

SyntaxInformation[YoungDualOGSn] = {
  "ArgumentsPattern" -> {_, _}
 }

YoungDualOGSn[spec_, n_Integer] := Module[
  { ogs = YoungDualOGS[spec, n],
    fac },
  fac = Range[2, n];
  Dot[ogs, n! / fac!]
]


FromYoungDualOGS::usage = "FromYoungDualOGS[ogs] returns the permtuation corresponding to the dual-standard OGS canonical form ogs."

FromYoungDualOGS[ogs_List] := Module[
  { n = 1 + Length[ogs],
    gg, pp },
  gg = Table[Cycles @ {Range[k]}, {k, 2, n}];
  pp = Thread @ PermutationPower[gg, ogs];
  Apply[PermutationProduct, pp]
]

(**** </YoungDualOGS> ****)


(**** <KawanoSekigawaMatrix> ****)

KawanoSekigawaMatrix::usage = "YoungFourieMatrix[n] returns the matrix describing the basis change from the Young-Fourier basis to the subgroup-adapted Young-Fourier basis."

KawanoSekigawaMatrix::invalid = "Invalid FourierParameters ``. {\"Right\", \"Right\"} is assumed."

Options[KawanoSekigawaMatrix] = {
  FourierParameters -> {"Right", "Right"}
}

KawanoSekigawaMatrix[n_Integer, OptionsPattern[]] := Module[
  { prm = OptionValue[FourierParameters],
    yng = Map[YoungTableaux, YoungShapes @ n],
    new = YoungTableaux[n-1] },
  prm = doForceList[prm, 2];
  (* Young-Fourier basis *)
  yng = Map[Tuples[#,2]&, yng];
  yng = Flatten[yng, 1];
  (* Subgroup-adapted Young-Fourier basis *)
  new = Flatten @ Map[YoungPileUp, new];
  new = Map[Thread @ {#, YoungTableaux @ YoungShape @ #} &, new];
  new = Flatten[new, 1];
  PermutationMatrix[
    PermutationList[FindPermutation[yng, new], Length @ yng],
    TargetStructure -> "SparseArray"
  ]
]

(**** </KawanoSekigawaMatrix> ****)


(**** <YoungFourierMatrix> ****)

YoungFourierMatrix::usage = "YoungFourieMatrix[n] returns the matrix describing the Fourier transform over the symmetric group of degree n."

YoungFourierMatrix[n_Integer, OptionsPattern[YoungFourier]] := Module[
  { prm = OptionValue[FourierParameters],
    shp = YoungShapes[n],
    elm = GroupElements[SymmetricGroup @ n],
    rep, dim },
  prm = doForceList[prm, 2];
  dim = Map[YoungTableauCount, shp];
  rep = Map[YoungNormalRepresentation, shp];
  rep = Outer[Construct, rep, elm] * Sqrt[dim/Length[elm]];
  rep = Switch[ prm,
    {"Right", "Right"}, rep,
    {"Left", "Right"}, Map[ConjugateTranspose, rep, {2}],
    {"Right", "Left"}, Map[Transpose, rep, {2}],
    {"Left", "Left"}, Conjugate[rep],
    _, Message[YoungFourier::invalid, prm]
  ];
  Map[Flatten, Transpose @ rep]
]

(**** </YoungFourierMatrix> ****)


(**** <YoungFourierBasis> ****)

YoungFourierBasis::usage = "YoungFourierBasis[n] returns the Young-Fourier basis of degree n, i.e., the Fourier transform over the symmetric group of degree n of the canonical basis of the left regular representation of the same group."

YoungFourierBasis[n_Integer, opts:OptionsPattern[YoungFourier]] := Module[
  { mat = YoungFourierMatrix[n, opts],
    key, val },
  key = Ket /@ Flatten[
    Map[Tuples[YoungTableaux @ #, 2]&, YoungShapes @ n],
    1 
  ];
  val = Ket /@ List /@ GroupElements[SymmetricGroup @ n];
  AssociationThread[key -> val . mat]
]

(**** </YoungFourierBasis> ****)


(**** <YoungFourier> ****)

YoungFourier::usage = "YoungFourier[n] represents the Fourier transform over the symmetric group of degree n.\nYoungFourier[n][Ket[{g}]] returns the Fourier transform of Ket[{g}] over the symmetric group.\nYoungFourier[Ket[{y1,y2}]] returns the inverse Fourier transform of Ket[{y1,y2}] over the symmetric group."

YoungFourier::invalid = "Invalid FourierParameters `` for the Young-Fourier transform. {\"Right\", \"Right\"} is assumed."

Options[YoungFourier] = {
  FourierParameters -> {"Right", "Right"}
}

YoungFourier[n_Integer, rest___][expr_Plus] := 
  Garner @ Map[YoungFourier[n, rest], expr]

YoungFourier[n_Integer, rest___][z_?CommutativeQ expr_] :=
  z * YoungFourier[n, rest][expr]


YoungFourier /:
Multiply[
  pre___,
  op:YoungFourier[_Integer, ___],
  in:( Ket[{_Cycles}] | Ket[{ya_YoungTableau, yb_YoungTableau}] )
  post___ 
] := Multiply[pre, op[in], post]

YoungFourier[n_Integer, opts:OptionsPattern[]][
  Ket @ {cyc_Cycles}
] := Module[
  { trs = YoungFourierMatrix[n, opts],
    fbs = YoungShapes[n],
    pos = GroupElementPosition[SymmetricGroup @ n, cyc] },
  fbs = Map[Tuples[YoungTableaux @ #, 2]&, fbs];
  fbs = Flatten @ Map[Ket, fbs, {2}];
  fbs . trs[[pos]]
]

YoungFourier[n_Integer, opts:OptionsPattern[]][
  Ket @ {ya_YoungTableau, yb_YoungTableau}
] := Module[
  { trs = Transpose @ YoungFourierMatrix[n, opts],
    fbs = YoungShapes[n],
    cbs = GroupElements[SymmetricGroup @ n],
    pos },
  cbs = Ket /@ List /@ cbs;
  fbs = Map[Tuples[YoungTableaux @ #, 2]&, fbs];
  fbs = Flatten[fbs, 1];
  pos = First @ FirstPosition[fbs, {ya, yb}];
  cbs . trs[[pos]]
]

(**** </YoungFourier> ****)


(**** <YoungBruhatGraph> ****)

YoungBruhatGraph::usage = "YoungBruhatGraph[shape] constructs a weak left Bruhat graph of standard tableaux, starting with the row-wise ordered tableau (observe that it is smallest with respect to weak left Bruhat ordering). The edges are weighted, where weight i means that the transposition (i,i+1) induces the transition."

YoungBruhatGraph[data_List?YoungShapeQ]:=
  YoungBruhatGraph[YoungShape @ data]

YoungBruhatGraph[shape_YoungShape, opts:OptionsPattern[Graph]]:= Module[
  { init, data },
  init = tableauToPermutation[firstYoungTableau @ shape];
  data = Flatten @ Rest @ NestList[findBruhatEdges, init, inversionCount @ init];
  data = Map[tableauFromPermutation[#, shape]&, data];
  Graph[data, opts,
    (* GraphLayout -> "LayeredEmbedding", *)
    ImageSize -> Medium,
    VertexLabels -> "Name",
    EdgeLabels -> "EdgeTag"
  ]
]

findBruhatEdges[prm:{___Integer}] := Module[
  { trs },
  trs = First /@ SequencePosition[prm, {a_, b_} /; Not[OrderedQ @ {a, b}]];
  trs = Map[{Cycles @ {{#, # + 1}}, #} &, trs]; 
  Map[UndirectedEdge[prm, Permute[prm, First @ #], Last @ #] &, trs]
]

findBruhatEdges[edges:{___UndirectedEdge}] := Module[
  {nodes},
  nodes = Union @ Map[Part[#, 2] &, edges];
  Flatten @ Map[findBruhatEdges, nodes]
]


tableauFromPermutation::usage = "tableauFromPermutation[prm, shape] maps permutation list prm back to standard Young tableau."

tableauFromPermutation[prm_List?PermutationListQ, shape_YoungShape] := 
  YoungTranspose @ YoungTableau @ TakeList[
    InversePermutation @ prm,
    First @ YoungTranspose @ shape
  ]

tableauFromPermutation[UndirectedEdge[src_,dst_, tag_], shape_YoungShape] := 
  UndirectedEdge[
    tableauFromPermutation[src, shape],
    tableauFromPermutation[dst, shape],
    tag
  ]


tableauToPermutation::usage = "tableauToPermutation[yt] maps standard Young tableau to a permutation list. The resulting permutation list is easier to find and apply adjacent transpositions."

tableauToPermutation[data_List?YoungTableauQ] :=
  tableauToPermutation[YoungTableau @ data]

tableauToPermutation[yt_YoungTableau] :=
  InversePermutation[Catenate @ First @ YoungTranspose @ yt]

(**** <YoungBruhatGraph> ****)


(**** <LegacyNormalRepresentation> ****)

LegacyNormalRepresentation::usage = "LegacyNormalRepresentation[shape] represents the homomorphism from the symmetric group to the matrix representation.\nSee also SpechtBasis."

LegacyNormalRepresentation[shape_YoungShape][op_Cycles] :=
  LegacyNormalRepresentation[shape, op]

LegacyNormalRepresentation[shape_YoungShape, op_Cycles] := Module[
  { bs = Ket /@ List /@ YoungTableaux[shape] },
  MatrixIn[op, bs]
]

(**** </LegacyNormalRepresentation> ****)


(**** <YoungNormalRepresentation> ****)

YoungNormalRepresentation::usage = "YoungNormalRepresentation[shape] refers to Young's normal representation of the symmetric group corresponding to integer partition shape.\nYoungNormalRepresentation[shape][prm] returns the matrix of permutation prm in Young's normal representation.\nSee also SpechtBasis."

YoungNormalRepresentation[shape_YoungShape] :=
  YoungNormalRepresentation[
    shape, 
    theYoungNormalRep[shape, YoungBruhatGraph @ shape]
  ]

YoungNormalRepresentation /:
MatrixForm[YoungNormalRepresentation[shape_YoungShape, data_?ArrayQ]] :=
  Map[MatrixForm, data]

YoungNormalRepresentation /:
Normal[YoungNormalRepresentation[shape_YoungShape, data_?ArrayQ]] := data


YoungNormalRepresentation[shape_YoungShape, data_?ArrayQ][
  Transpositions[{}]
] := One[YoungTableauCount @ shape]

YoungNormalRepresentation[shape_YoungShape, data_?ArrayQ][
  Transpositions[trs_]
] := SimplifyThrough[ Dot @@ Extract[data, List /@ Reverse @ trs] ]


YoungNormalRepresentation[shape_YoungShape, data_?ArrayQ][
  prm:(_Cycles | _List?PermutationListQ)
] := YoungNormalRepresentation[shape, data][PermutationTranspositions @ prm]


theYoungNormalRep::usage = "theYoungNormalRep[graph] constructs the Young's normal representation using the weak leaft Bruhat graph."

theYoungNormalRep[shape_YoungShape, data_Graph] := Module[
  { n = YoungDegree[shape],
    tableaux = YoungTableaux[shape],
    distances, adjacency, rules },
  rules = Normal @ Map[First, PositionIndex @ tableaux];
  adjacency = RotateRight /@ ReplaceAll[List @@@ EdgeList @ data, rules];
  distances = Map[YoungDistance, tableaux];

  rules = Flatten @ Map[
    Function[
      {k, i, j},
      { {k, i, i} -> 1/Part[distances,i,k],
        {k, i, j} -> Sqrt[1 - 1/Part[distances,i,k]^2],
        {k, j, i} -> Sqrt[1 - 1/Part[distances,i,k]^2],
        {k, j, j} -> -1/Part[distances,i,k]
      }
    ] @@ # &,
    adjacency
  ];
  rules = Association @ Join[
    Flatten @ Table[
      {k, i, i} -> 1/Part[distances,i,k],
      {k, n-1},
      {i, Length @ tableaux}
    ],
    rules
  ];
  SparseArray[Normal @ rules, {n-1, Length @ tableaux, Length @ tableaux}]
]

(**** </YoungNormalRepresentation> ****)


(**** <YoungSeminormalRepresentation> ****)

YoungSeminormalRepresentation::usage = "YoungSeminormalRepresentation[shape] refers to Young's seminormal representation of the symmetric group corresponding to the integer partition shape.\n YoungSeminormalRepresentation[shape][prm] returns the matrix of permutation prm in Young's seminormal representation."

YoungSeminormalRepresentation[shape_YoungShape] :=
  YoungSeminormalRepresentation[
    shape, 
    theYoungSeminormalRep[shape, YoungBruhatGraph @ shape]
  ]

YoungSeminormalRepresentation /:
MatrixForm[YoungSeminormalRepresentation[shape_YoungShape, data_?ArrayQ]] :=
  Map[MatrixForm, data]

YoungSeminormalRepresentation /:
Normal[YoungSeminormalRepresentation[shape_YoungShape, data_?ArrayQ]] := data


YoungSeminormalRepresentation[shape_YoungShape, data_?ArrayQ][
  Transpositions[{}]
] := One[YoungTableauCount @ shape]

YoungSeminormalRepresentation[shape_YoungShape, data_?ArrayQ][
  Transpositions[trs_]
] := SimplifyThrough[ Dot @@ Extract[data, List /@ Reverse @ trs] ]


YoungSeminormalRepresentation[shape_YoungShape, data_?ArrayQ][
  prm:(_Cycles | _List?PermutationListQ)
] := YoungSeminormalRepresentation[shape, data][PermutationTranspositions @ prm]


theYoungSeminormalRep::usage = "theYoungSeminormalRep[data, n] constructs the Young's seminormal representation using the weak leaft Bruhat graph specified by data."

theYoungSeminormalRep[shape_YoungShape, data_Graph] := Module[
  { n = YoungDegree[shape],
    tableaux = YoungTableaux[shape],
    distances, adjacency, rules },
  rules = Normal @ Map[First, PositionIndex @ tableaux];
  adjacency = RotateRight /@ ReplaceAll[List @@@ EdgeList @ data, rules];
  distances = Map[YoungDistance, tableaux];

  rules = Flatten @ Map[
    Function[
      {k, i, j},
      Which[
        i < j,
        { {k, i, j} -> 1 - 1/Part[distances,i,k]^2,
          {k, j, i} -> 1
        },
        i > j, 
        { {k, i, j} -> 1,
          {k, j, i} -> 1 - 1/Part[distances,j,k]^2
        },
        True, Nothing
      ]
    ] @@ # &,
    adjacency
  ];
  rules = Join[
    Flatten @ Table[
      {k, i, i} -> 1/Part[distances,i,k],
      {k, n-1},
      {i, Length @ tableaux}
    ],
    rules
  ];
  SparseArray[rules, {n-1, Length @ tableaux, Length @ tableaux}]
]

(**** </YoungSeminormalRepresentation> ****)


(**** <YoungSeminormalMetric> ****)

YoungSeminormalMetric::usage = "YoungSeminormalMetric[syt] returns the norm square of the seminormal basis vector corresponding to standard Young tableau syt.\nYoungSeminormalMetric[shape] returns a list of the norm squares of the seminormal basis vectors belonging to shape.\nNote that Young's seminormal representation is not orthogonal in the canonical Hermitian product. However, it is orthogonal with respect to a diagonal scalar prodcut given by YoungSeminormalMetric."

YoungSeminormalMetric[data_List?YoungShapeQ] :=
  YoungSeminormalMetric[YoungShape @ data]

YoungSeminormalMetric[shape_YoungShape] :=
  Map[YoungSeminormalMetric, YoungTableaux @ shape]


YoungSeminormalMetric[data_List?YoungTableauQ] :=
  YoungSeminormalMetric[YoungTableau @ data]

YoungSeminormalMetric[YoungTableau[data_]] := With[
  { trshape = YoungTranspose[Length /@ data] },
  Product[
    If[
      And[
        Or[i2>i1, j2>j1],
        Part[data,i1,j1] > Part[data,i2,j2]
      ],
      1-1/(i1-j1-i2+j2)^2,
      1
    ],
    {j1, 1, Length[trshape]},
    {i1, 1, Part[trshape,j1]},
    {j2, j1, Length[trshape]},
    {i2, 1, Part[trshape,j2]}
  ]
]

(**** </YoungSeminormalMetric> ****)


(**** <YoungRegularBasis> ****)

YoungRegularBasis::usage = "YoungRegularBasis[n] returns the Young regular basis of degree n, i.e., the canonical basis of the left regular representation of the symmetric group of degree n."

YoungRegularBasis[n_Integer] := Module[
  { mat = YoungFourierMatrix[n],
    key, val },
  key = Ket /@ List /@ GroupElements[SymmetricGroup @ n];
  val = Ket /@ Flatten[
    Map[Tuples[YoungTableaux @ #, 2]&, YoungShapes @ n],
    1 ];
  AssociationThread[key -> val . Topple[mat]]
]

(**** </YoungRegularBasis> ****)


(**** <YoungLeftRepresentation> ****)

YoungLeftRepresentation::usage = "YoungLeftRepresentation[n] represents the left regular representation of the symmetric group of degree n."

YoungLeftRepresentation[n_Integer] :=
  YoungLeftRepresentation[SymmetricGroup @ n]

YoungLeftRepresentation[grp_SymmetricGroup][cyc_Cycles] := 
  LeftRegularRepresentation[grp][cyc]

(**** </YoungLeftRepresentation> ****)


(**** <YoungRightRepresentation> ****)

YoungRightRepresentation::usage = "YoungRightRepresentation[n] represents the left regular representation of the symmetric group of degree n."

YoungRightRepresentation[n_Integer] :=
  YoungRightRepresentation[SymmetricGroup @ n]

YoungRightRepresentation[grp_SymmetricGroup][cyc_Cycles] := 
  RightRegularRepresentation[grp][cyc]

(**** </YoungRightRepresentation> ****)


(**** <LeftRegularRepresentation> ****)

LeftRegularRepresentation::usage = "LeftRegularRepresentation[group, g] returns the left regular representation of element g of group.\n LeftRegularRepresentation[group, {g1,g2,\[Ellipsis],gn}] returns the list of the left regular representations of elements g1, g2, \[Ellipsis], gn."

LeftRegularRepresentation::gmt = "Group `` is not supported."

LeftRegularRepresentation[grp_][elm_] :=
  LeftRegularRepresentation[grp, elm]

LeftRegularRepresentation[grp_, All] := Module[
  { gmt = GroupMultiplicationTable[grp] },
  If[ Not[MatrixQ @ gmt],
    Message[LeftRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  Transpose /@ PermutationMatrix /@ Transpose[gmt]
]

LeftRegularRepresentation[grp_, elm_] := Module[
  { gmt = GroupMultiplicationTable[grp],
    k },
  If[ MatrixQ[gmt],
    gmt = Transpose[gmt], (* due to Mathematica's convention *)
    Message[LeftRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  k = GroupElementPosition[grp, elm];
  If[ ListQ[k], (* NOT ListQ[elm] *)
    Map[Transpose[PermutationMatrix[#, TargetStructure -> "Sparse"]]&, gmt[[k]]],
    Transpose @ PermutationMatrix[gmt[[k]], TargetStructure -> "Sparse"]
  ]
]
(* NOTE: For SymmetricGroup, elm may be specified by a permutation list (see PermutationList); hence, NOT ListQ[elm] instead of ListQ[k]. *)

LeftRegularRepresentation[grp:{_String, _Integer}, All] :=
  LeftRegularRepresentation[grp, FiniteGroupData[grp, "Elements"]]

LeftRegularRepresentation[grp:{_String, _Integer}, kk_] := Module[
  { gmt = FiniteGroupData[grp, "MultiplicationTable"] },
  If[ MatrixQ[gmt],
    gmt = Transpose[gmt], (* due to Mathematica's convention *)
    Message[LeftRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  If[ ListQ[kk],
    Map[Transpose[PermutationMatrix[#, TargetStructure -> "Sparse"]]&, gmt[[kk]]],
    Transpose @ PermutationMatrix[gmt[[kk]], TargetStructure -> "Sparse"]
  ]
]

(**** </LeftRegularRepresentation> ****)


(**** <RightRegularRepresentation> ****)

RightRegularRepresentation::usage = "RightRegularRepresentation[group, g] returns the right regular representation of element g of group.\n RightRegularRepresentation[group, {g1,g2,\[Ellipsis],gn}] returns the list of the right regular representations of elements g1, g2, \[Ellipsis], gn."

RightRegularRepresentation::gmt = "Group `` is not supported."

RightRegularRepresentation[grp_][elm_] :=
  RightRegularRepresentation[grp, elm]

RightRegularRepresentation[grp_, All] := Module[
  { gmt = GroupMultiplicationTable[grp] },
  If[ Not[MatrixQ @ gmt],
    Message[RightRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  Map[PermutationMatrix, gmt]
]

RightRegularRepresentation[grp_, elm_] := Module[
  { gmt = GroupMultiplicationTable[grp],
    k },
  If[ Not[MatrixQ @ gmt],
    Message[RightRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  k = GroupElementPosition[grp, elm];
  If[ ListQ[k], (* NOT ListQ[elm} *)
    Map[PermutationMatrix[#, TargetStructure -> "Sparse"]&, gmt[[k]]],
    PermutationMatrix[gmt[[k]], TargetStructure -> "Sparse"]
  ]
]
(* NOTE: For SymmetricGroup, elm may be specified by a permutation list (see PermutationList); hence, NOT ListQ[elm] instead of ListQ[k]. *)

RightRegularRepresentation[grp:{_String, _Integer}, All] :=
  RightRegularRepresentation[grp, FiniteGroupData[grp, "Elements"]]

RightRegularRepresentation[grp:{_String, _Integer}, kk_] := Module[
  { gmt = FiniteGroupData[grp, "MultiplicationTable"] },
  If[ Not[MatrixQ @ gmt],
    Message[RightRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  If[ ListQ[kk],
    Map[PermutationMatrix[#, TargetStructure -> "Sparse"]&, gmt[[kk]]],
    PermutationMatrix[gmt[[kk]], TargetStructure -> "Sparse"]
  ]
]

(**** </LeftRegularRepresentation> ****)


(**** <YoungClebschGordanTransform> ****)

YoungClebschGordanTransform::usage = "YoungClebschGordanTransform[vec] returns the Clebsch-Gordan transformation of vector vec associated with the symmetric group."

YoungClebschGordanTransform::mn = "`` and `` have different ranks."

YoungClebschGordanTransform[z_?CommutativeQ expr_] :=
  Garner[z * YoungClebschGordanTransform[expr]]

YoungClebschGordanTransform[expr_Plus] :=
  Garner @ Map[YoungClebschGordanTransform, expr]

YoungClebschGordanTransform[Ket[a_?YoungTableauQ, b_?YoungTableauQ]] :=
  Module[
    { m = Total @ YoungShape[a],
      n = Total @ YoungShape[b],
      op },
    If[ m != n,
      Message[YoungClebschGordanTransform::mn, a, b];
      Return[0]
    ];
    op = Total[GroupElements @ SymmetricGroup @ n] /
      GroupOrder[SymmetricGroup @ n];
    Total @ Map[
      ( Sqrt[YoungTableauCount @ YoungShape @ #] *
          OSlash[Ket[#], op ** Ket[#, a, b]] )&,
      YoungTableaux[n]
    ]
  ]

(**** </YoungClebschGordanTransform> ****)


(**** <HarrowClebschGordanTransform> ****)

HarrowClebschGordanTransform::usage = "HarrowClebschGordanTransform[vec] returns the Clebsch-Gordan transformation of vector vec associated with the symmetric group.\nIt is equivalent to YoungClebschGordanTransform, but is based on the method suggested by Harrow (PhD Thesis, 2005)."

HarrowClebschGordanTransform[z_?CommutativeQ expr_] :=
  Garner[z * HarrowClebschGordanTransform[expr]]

HarrowClebschGordanTransform[expr_Plus] :=
  Garner @ Map[HarrowClebschGordanTransform, expr]

HarrowClebschGordanTransform[Ket[a_?YoungTableauQ, b_?YoungTableauQ]] := 
  Module[
    { shp = YoungShape[a],
      vec, out },
    vec = CircleTimes[Ket[a], Total[Ket[#, #] & /@ YoungTableaux[shp]], 
      Ket[b]];
    vec /= Sqrt[YoungTableauCount @ shp];
    vec = iQFTG @ ControlledGamma @ QFTG[vec];
    out = Cases[vec, Ket[p_, q_, rr__] -> Ket[q], Infinity];
    out = Collect[
      ReplaceAll[vec, Ket[p_, q_, rr__] -> Ket[q]*Ket[p, rr]],
      out, Garner] /. {Times -> OSlash}
  ]


QFTG[z_?CommutativeQ expr_] := Garner[z * QFTG[expr]]

QFTG[expr_Plus] := Garner@Map[QFTG, expr]

QFTG[Ket[a_, b_, c_, d_]] := CircleTimes[
  Ket[b, a] /. Normal[YoungFourierBasis@Total@YoungShape@a],
  Ket[c, d]
 ]


iQFTG[z_?CommutativeQ expr_] := Garner[z * iQFTG[expr]]

iQFTG[expr_Plus] := Garner@Map[iQFTG, expr]

iQFTG[Ket[a_, b_, c_]] := CircleTimes[
  Ket[a] /. Normal[YoungRegularBasis@Total@YoungShape@b],
  Ket[b, c]
]


ControlledGamma[z_?CommutativeQ expr_] :=  Garner[z * ControlledGamma[expr]]

ControlledGamma[expr_Plus] := Garner @ Map[ControlledGamma, expr]

ControlledGamma[Ket[a_, b_, c_]] :=
  CircleTimes[Ket[a, b], InversePermutation[a] ** Ket[c]]

(**** </HarrowClebschGordanTransform> ****)

End[]

EndPackage[]
