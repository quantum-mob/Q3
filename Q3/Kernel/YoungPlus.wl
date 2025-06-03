(* ::Package:: *)
(* N.B.: This package contains some symbols from Bernd Guenther's
   IrrCharSymGrp.m v2.0 (posted on the Wolfram Community).  *)

Get["QuantumMob`Q3`"]

BeginPackage["QuantumMob`Q3`", {"System`"}]

ClearAll @@ Evaluate @ Unprotect[
  CoxeterTest,
  YoungNaturalRepresentation,
  YoungNaturalMetric,
  LegacySeminormalRepresentation,
  LegacyBruhatGraph,
  Seminormal2Natural,
  YoungCharacterTest
];

{
  CoxeterTest,
  YoungNaturalRepresentation,
  YoungNaturalMetric,
  LegacySeminormalRepresentation,
  LegacyBruhatGraph,
  Seminormal2Natural,
  YoungCharacterTest
};

Begin["`Private`"]

CoxeterTest::usage = "CoxeterTest[rep] returns True if all matices in Young's representation rep satisfy Coxeter's relations, as they must.\nSo unless you tamper with the definitions, this function should always return True."

CoxeterTest[ynr_?ArrayQ] := And[
  Apply[And, (#.#==IdentityMatrix[Length[ynr[[1]]]])& /@ ynr],
  And @@ Table[
    ynr[[r]].ynr[[r+1]].ynr[[r]]==ynr[[r+1]].ynr[[r]].ynr[[r+1]],
    {r, Length[ynr]-1}
  ],
  And @@ Flatten @ Table[
    ynr[[r]].ynr[[s]]==ynr[[s]].ynr[[r]],
    {r, Length[ynr]-2}, {s,r+2,Length[ynr]}
  ]
]


Seminormal2Natural::usage = "Seminormal2natural[\[Lambda]] The transformation matrix turning the seminormal presentation into the natural presentation. Each row vector is the expansion of a natural basis vector in terms of the seminormal basis vectors."

Seminormal2Natural[pp_?YoungShapeQ]:=
  youngAuxiliary[pp, 1] /; Total[pp]>1


(*** <YoungNaturalRepresentation> ****)

YoungNaturalRepresentation::usage = "YoungNaturalRepresentation[shape] returns full object YoungNaturalRepresentation[shape, array] representing Young's natural representation of the symmetric group, where array is a list of matrices of the adjacent transpositions.\nThe matrices in array are supposed to operate from the right on row vectors.\nYoungNaturalRepresentation[shape, array][prm] returns the matrix representation of permutation prm in Young's natural representation associated with partition shape."

YoungNaturalRepresentation[data_List?YoungShapeQ]:=
  YoungNaturalRepresentation[YoungShape @ data]

YoungNaturalRepresentation[shape_YoungShape]:=
  YoungNaturalRepresentation[shape, SparseArray @ youngAuxiliary[shape, 2]] /; 
  YoungDegree[shape]>1


YoungNaturalRepresentation[shape_YoungShape, data_?ArrayQ][
  Transpositions[{}]
] := One[YoungTableauCount @ shape]

YoungNaturalRepresentation[shape_YoungShape, data_?ArrayQ][
  Transpositions[trs_]
] := SimplifyThrough[ Dot @@ Extract[data, List /@ trs] ]


YoungNaturalRepresentation[shape_YoungShape, data_?ArrayQ][
  prm:(_Cycles | _List?PermutationListQ)
] := YoungNaturalRepresentation[shape, data][PermutationTranspositions @ prm]


YoungNaturalRepresentation /:
MatrixForm[YoungNaturalRepresentation[shape_YoungShape, data_?ArrayQ]] :=
  Map[MatrixForm, data]

YoungNaturalRepresentation /:
Normal[YoungNaturalRepresentation[shape_YoungShape, data_?ArrayQ]] := data


(*** </YoungNaturalRepresentation> ****)


YoungCharacterTest::usage = "YoungCharacterTest[rep] computes the character vector in Young's representation rep and compares it to the relevant entry in the character table, where rep is YoungNaturalRepresentation, YoungSeminormalRepresentation, or YoungNormalRepresentation.\nUnless you tamper with the definitions, this function should always return True."

YoungCharacterTest[rep_, shape_List?YoungShapeQ] :=
  YoungCharacterTest[rep, YoungShape @ shape]

YoungCharacterTest[rep_] := Module[
  { shape = First[rep],
    types = Reverse[YoungShapes @ YoungDegree @ First @ rep],
    chr, new },
  new = Tr /@ rep /@ YoungClassRepresentative /@ types;
  chr = LegacyYoungCharacters[shape];
  new == chr
]

YoungClassRepresentative::usage = "YoungClassRepresentative[type] returns a representative of the conjugacy class of type in the symmetric group. The type is specified by an integer partition, and the result is given in Transpositions."

YoungClassRepresentative[type_List?YoungShapeQ] :=
  YoungClassRepresentative[YoungShape @ type]

YoungClassRepresentative[YoungShape[type_]] := Module[
  { new = Accumulate @ type,
    trs },
  trs = Range @@@ Transpose @ {
    Prepend[Most[new] + 1, 1], 
    new - 1
  };
  Transpositions[Flatten @ trs]
]


YoungNaturalMetric::usage = "YoungNaturalMetric[shape] is the scalar product invariant under Young's natural presentation corresponding to the integer partition shape."

YoungNaturalMetric[shape_List?YoungShapeQ] :=
  YoungNaturalMetric[YoungShape @ shape]

YoungNaturalMetric[YoungShape[shape_]] := With[
  { graphData = compatibleBruhatGraph @ LegacyBruhatGraph[shape],
    transform = Seminormal2Natural[shape] },
  Whole[Factorial /@ YoungTranspose[shape]] *
  Dot[
    transform,
    DiagonalMatrix[YoungSeminormalMetric /@ First /@ graphData],
    Transpose[transform]
  ]
]


(* mode=1: only transform;
   mode=2: natural presentation;
   mode=3: seminormal presentation *)
youngAuxiliary[shape_YoungShape, mode_] :=
  youngAuxiliary[First @ shape, mode]

youngAuxiliary[shape_List?YoungShapeQ, mode_] := Module[
  { n = Total[shape],
    graphData = compatibleBruhatGraph @ LegacyBruhatGraph[shape] },

  (* The following expression computes the adjacency lists of the weak left
     Bruhat graph; an entry Subscript[a, ij] may have four different
     meanings, depending on the following cases: 
     (i) If Subscript[a, ij]=i, then j and j+1 are contained in the same row of tableau i. 
     (ii) If Subscript[a, ij]=-i, then j and j+1 are contained in the same column of tableau i. 
     (iii) If Subscript[a, ij]\[NotEqual]\[PlusMinus]i but Subscript[a, ij]<0, then i and i+1 appear inverted in tableau i and application of the admissible transposition (j,j+1) turns tableau i
     into tableau Subscript[a, ij], thus removing an inversion. 
     (iv) If Subscript[a, ij]\[NotEqual]\[PlusMinus]i but Subscript[a, ij]>0, then i and i+1 appear in correct order in tableau i and application of the
     admissible transposition (j,j+1) turns tableau i into
     tableau Subscript[a, ij], thus adding an inversion. *)

  Module[
    { adjacency,
      contents, spanningTree, transform, tnorm, tinv, semimatrix },

    adjacency = Normal @ SparseArray[
      Join[
        ({Part[#,1],Part[#,3]}->Part[#,2])& /@ Flatten[Part[#,2]& /@ graphData, 1],
        ({Part[#,2],Part[#,3]}->-Part[#,1])& /@ Flatten[Part[#,2]& /@ graphData, 1],
        Flatten @ MapIndexed[ 
          Function[{v, w}, Function[u, {First[w], u} -> First[w]] /@ v],
          Function[
            v,
            Last /@ Select[
              Transpose @ {
                Flatten[Function[u, Append[u, 0]] /@ (Differences /@ v)],
                Flatten[v]
              },
              Function[u, First[u]==1]
            ]
          ] /@ (First /@ graphData)
        ],
        Flatten @ MapIndexed[
          Function[{v, w}, Function[u, {First[w], u} -> -First[w]] /@ v],
          Function[
              v,
              Last /@ 
              Select[
                Transpose @ { 
                  Flatten[Function[u, Append[u, 0]] /@ (Differences /@ v)], 
                  Flatten[v] 
                },
                Function[u, First[u]==1]
              ]
          ] /@
          (YoungTranspose[#]&) /@ 
          (First /@ graphData)
        ]
      ],
      {Length[graphData], n-1} 
    ];

    contents = Function[ u,
      Normal @ SparseArray[
        Flatten @ MapIndexed[
          Function[{v1,v2},{v1->Last[v2]-First[v2]}],
          First[u],
          {2}
        ],
        {n}
      ]
    ] /@ graphData;
    If[mode!=3,
      spanningTree = If[ Length[graphData]==1, {},
        First /@ MapIndexed[
          Drop[#1/.(Rule[{a_},b_]):>{First[#2],a,b},-1]&,
          ArrayRules /@ SparseArray[
            Flatten[Function[v,Function[u,{Part[u,2],Part[u,1]}->Part[u,3]]/@Last[v]] /@ Drop[graphData,1]],
            {Length[graphData]-1, Length[graphData]}
          ]
        ]
      ];
      transform = SparseArray[
        {Length[graphData], Length[graphData]} -> 1,
        {Length[graphData], Length[graphData]}
      ];
      Module[
        { k,r,s,x},
        For[ i=Length[spanningTree],i>0,i--,
          (* e_i = s_r e_k is the base vector to be constructed. *)
          k=Part[spanningTree,i,2];
          r=Part[spanningTree,i,3];
          For[j=k,j<=Length[graphData],j++,
            (* v_j is a Young vector appearing in e_k with coefficient x. *)
            x=Part[transform,k,j];
            If[x==0,Continue[]];
            s=Part[adjacency,j,r];
            Switch[s,
              j, Part[transform,i,j]+=x, (* row inversion *) 
              -j, Part[transform,i,j]-=x, (* column inversion *) 
              x_/;x<0, Part[transform,i,j] += x /
                (Part[contents,j,r+1]-Part[contents,j,r]);
              Part[transform,i,-s] += x * (1 -
                  1/(Part[contents,j,r+1]-Part[contents,j,r])^2),
              (* removing an inversion *) 
              _, Part[transform,i,s]+=x;
              Part[transform,i,j] += x /
                (Part[contents,j,r+1] - Part[contents,j,r]);
              (* admissibly adding an inversion *)
             ]
           ]
         ]
       ];
      tnorm=Normal[transform]
    ];
    If[mode==1, Return[tnorm]];
    semimatrix = Normal @ SparseArray[
      Flatten @ Module[
        {s},
        Table[
          s = Part[adjacency, k, r];
          Switch[ s,
            k, {{r,k,k}->1}, (* row inversion *) 
            -k, {{r,k,k}->-1}, (* column inversion *)
            x_/;x<0, (* removing an inversion *)
            { {r,k,k}->1/(Part[contents,k,r+1]-Part[contents,k,r]),
              {r,k,-s}->1-1/(Part[contents,k,r+1]-Part[contents,k,r])^2 },
            _, (* admissibly adding an inversion *)
            { {r,k,k}->1/(Part[contents,k,r+1]-Part[contents,k,r]),
              {r,k,s}->1 }
          ],
          {r, n-1},
          {k, Length[graphData]}
        ]
      ],
      {n-1, Length[graphData], Length[graphData]}
    ];
    If[mode==3, Return[semimatrix]];
    tinv=Inverse[tnorm];
    (tnorm.#.tinv&) /@ semimatrix
  ]
]

compatibleBruhatGraph::usage = "compatibleBruhatGraph[data] coverts the new format of LegacyBruhatGraph to the old format for backward compatibility."

compatibleBruhatGraph[graphData_Association] :=
  KeyValueMap[
    Function[{key, val}, {key, val}], 
    graphData
  ] /. YoungTableau -> Identity;


LegacyBruhatGraph::usage="LegacyBruhatGraph[shape] constructs weak left Bruhat graph of standard tableaux. Start with row-wise ordered tableau (observe that it is smallest with respect to weak left Bruhat ordering) and then do breadth first algorithm. Output is a record with two components: The first is the list of standard tableaux. The second is the list of weighted edges, where weight i means that the transposition (i,i+1) the first connected tableau to the second. The edges are given as three component record with the first two components denoting the indices of the connected tableaux and the third record the weight."

LegacyBruhatGraph[data_List?YoungShapeQ]:=
  LegacyBruhatGraph[YoungShape @ data]

LegacyBruhatGraph[shape_YoungShape]:= Module[
  { k = 0,
    init = tableauToPermutation[firstYoungTableau @ shape],
    data },
  data = NestList[
    ( k += Length[#];
      updateConnectedTableaux[#, k, k-Length[#]] 
    )&,
    Association[init -> {}],
    inversionCount[init]
  ];
  data = Merge[data, Catenate];
  AssociationMap[
    Function[v, tableauFromPermutation[First @ v, shape] -> Last[v]],
    data
  ]
]


findConnectedTableaux::usage = "findConnectedTableaux[prm, curPos, srcPos] finds standard Young tableaux resulting from the present standard Young tableau prm (given in the form of permutation list; see tableauToPermutation). The result is a list of pairs {newPrm, {curPos, srcPos, weight}}."

findConnectedTableaux[prm_List?PermutationListQ, curPos_, sourcePos_] := Module[
  { trs },
  trs = Flatten @ Position[Differences[prm], x_/;x<0];
  trs = Map[{Cycles @ {{#, #+1}}, #}&, trs];
  Map[
    Rule[Permute[prm, First @ #], {curPos, sourcePos, Last @ #}]&,
    trs
  ]
]


updateConnectedTableaux::usage = "updateConnectedTableaux[data, curPos, srcPos] finds standard Young tableaux connected from those in data. "

updateConnectedTableaux[data_, curPos_, sourcePos_] := Module[
  { new, out },
  new = Join @@ MapIndexed[
    findConnectedTableaux[#1, curPos, sourcePos+First[#2]]&,
    Keys @ data
  ];
  new = GroupBy[new, First, Values];
  out = MapIndexed[
    Map[Function[x, ReplacePart[x, 1->Part[x,1]+First[#2]]], #1]&, 
    Values @ new
  ];
  AssociationThread[Keys @ new, out]
]


LegacySeminormalRepresentation::usage = "LegacySeminormalRepresentation[pp] computes the matrices of Young's seminormal representation of the symmetric group corresponding to the integer partition pp. The function returns the images of the transpositions of immediate neighbors, listed in order of the transposed elements. The matrices are supposed to operate from the right on row vectors.\nLegacySeminormalRepresentation[shape, prm] returns the matrix assigned to permutation prm by Young's seminormal representation corresponding to partition shape."
(* NOTE: There are two important differences between LegacySeminormalRepresentation and YoungSeminormalRepresentaion: 
  1. In LegacySeminormalRepresentation, matrices are supposed to operate from the right on row vectors.
  2. The order of Specht basis vectors are different. *)

LegacySeminormalRepresentation[data_List?YoungShapeQ]:=
  LegacySeminormalRepresentation[YoungShape @ data]

LegacySeminormalRepresentation[shape_YoungShape]:=
  legacyYoungSeminormalRep[LegacyBruhatGraph @ shape, YoungDegree @ shape]

LegacySeminormalRepresentation[data_List?YoungShapeQ, any_] :=
  LegacySeminormalRepresentation[YoungShape @ data, any]

LegacySeminormalRepresentation[shape_YoungShape, cyc_Cycles] :=
  LegacySeminormalRepresentation[
    shape, 
    PermutationList[cyc, YoungDegree @ shape]
  ]

LegacySeminormalRepresentation[shape_YoungShape, prm_?PermutationListQ] :=
  If[ prm == Range[YoungDegree @ shape],
    IdentityMatrix[YoungTableauCount @ shape],
    Dot @@ Extract[
      LegacySeminormalRepresentation[shape],
      Partition[adjacentTranspositions[prm], 1]
    ]
  ] /; YoungDegree[shape]==Length[prm];


legacyYoungSeminormalRep::usage = "legacyYoungSeminormalRep[data, n] constructs the Young's seminormal representation using the weak leaft Bruhat graph specified by data.\nA copy of youngAuxiliary particularly for Young's seminormal representation."

(****
  The following expression computes the adjacency lists of the weak left
  Bruhat graph; an entry Subscript[a, ij] may have three different
  meanings, depending on the following cases:
  (i) If Subscript[a, ij] == 0, then nothing special.
  (ii) If Subscript[a, ij]<0, then j and j+1 appear inverted in tableau i and application of the admissible transposition (j,j+1) turns tableau i into tableau -Subscript[a, ij], thus removing an inversion. 
  (iii) If Subscript[a, ij]>0, then j and j+1 appear in correct order in tableau i and application of the admissible transposition (j,j+1) turns tableau i into tableau Subscript[a, ij], thus adding an inversion. *)

legacyYoungSeminormalRep[data_, n_Integer] := Module[
  { tables = Keys[data], 
    codes = Flatten[Values @ data, 1], 
    adjacency, distances },

  adjacency = Normal @ SparseArray[
    Join[
      ({Part[#,1], Part[#,3]} -> +Part[#,2])& /@ codes,
      ({Part[#,2], Part[#,3]} -> -Part[#,1])& /@ codes
    ],
    {Length[data], n-1}
  ];
  
  distances = YoungDistance /@ tables;
  
  SparseArray[
    Flatten @ Module[
      {s},
      Table[
        s = Part[adjacency, k, r];
        { {r, k, k} -> 1/Part[distances,k,r],
          Which[
            s < 0, (* removing an inversion *)
            {r, k, -s} -> 1 - 1/Part[distances,k,r]^2,
            s > 0, (* admissibly adding an inversion *)
            {r, k, s} -> 1,
            True, Nothing
          ] 
        },
        {r, n-1},
        {k, Length[data]}
      ]
    ],
    {n-1, Length @ data, Length @ data}
  ]
]


sameRowTranspositions::usage = "sameRowTranspositions[syt] returns a list of elements k such that k and k+1 appear on the same row in standar Young tableau syt."

sameRowTranspositions[data_?YoungShapeQ] :=
  sameRowTranspositions[YoungTableau @ data]

sameRowTranspositions[YoungTableau[data_]] := Module[
  { del },
  del = Transpose @ {
    Flatten[data],
    Flatten[(Append[#, 0]&) /@ Differences /@ data]
  };
  First /@ Select[del, Last[#]==1&]
]

End[]

EndPackage[]


(**** post-processing ****)

BeginPackage["QuantumMob`Q3`"]

Begin["`Private`"]

SetAttributes[Evaluate @ Names["`*"], ReadProtected];

End[]

SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

(* Users are allowed to change variables. *)
Unprotect["`$*"];

(* Too dangerous to allow users to change these. *)
Protect[$GarnerPatterns, $ElaborationPatterns];

EndPackage[]
