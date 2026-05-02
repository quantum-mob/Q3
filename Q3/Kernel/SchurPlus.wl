(* -*- mode: Mathematica -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ DualSchurBasis };

{ GelfandClasses, GelfandClass };

Begin["`Private`"]

(**** <DualSchurBasis> ****)
DualSchurBasis::usage = "DualSchurBasis[n, d] returns an association of Schur basis of n qudits of dimension d, based on the dual Schur transform algorithm.\nDualSchurBasis[type] returns the Schur basis of the permutation module associated with type.\nDualSchurBasis[shape, d] returns the Schur basis of ... . \nDualSchurBasis[shape, content] returns the Schur basis of ... ."

DualSchurBasis::incmp = "Shape `` must dominate the shape of content ``."

DualSchurBasis[ss:{__?SpeciesQ}] :=
  DualSchurBasis[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

DualSchurBasis[ss:{__?SpeciesQ}] := Module[
  { cbs = Basis[ss], 
    sbs },
  sbs = DualSchurBasis[Length @ ss, Dimension @ First @ ss];
  Map[Dot[#, cbs]&, sbs]
]

DualSchurBasis[n_Integer, d_Integer] := Module[
  { ss = YoungShapes[n, d],
    tt, bs },
  tt = PadRight[First /@ ss, {Length @ ss, d}];
  tt = Catenate[Permutations /@ tt];
  bs = Outer[DualSchurBasis, ss, tt, 1];
  Join @@ Flatten[bs]
]


DualSchurBasis[shape_YoungShape, d_Integer] := Module[
  { contents = YoungContents[shape, d] },
  Join @@ Map[DualSchurBasis[shape, #]&, contents]
]

DualSchurBasis[content:{__Integer}] := Module[
  { shapes = YoungShapes[content] },
  Join @@ Map[DualSchurBasis[#, content]&, shapes]
]


DualSchurBasis[shape_YoungShape, content:{__Integer}] := Module[
  { dim = Length[content],
    sub = YoungElements[content],
    rep, pbs, trv, prj, mat, tag, pos },

  {tag, pos} = DualSchurBasisNames[shape, content];

  (* irreducible represenations *)
  rep = YoungNormalRepresentation[shape];

  (* permutation/transversal basis *)
  pbs = Permutations[ContentVector @ content];

  (* transversal elements *)
  trv = Map[FindPermutation, pbs];
  trv = Map[rep, trv];

  (* projections *)
  prj = YoungProjector[rep][content];
  prj = prj[[All, pos]];

  (* NOTE: Somehow, Dot returns the result in a dense array. *)
  mat = SparseArray @ Dot[trv, prj];
  mat = Transpose[Conjugate[mat], {3, 1, 2}];
  mat = SimplifyThrough @ Map[Normalize, mat, {2}];

  (* permutation/transversal basis in the computational basis *)
  pbs = 1 + Map[FromDigits[#, dim]&, pbs - 1];
  pbs = One[ Power[dim, YoungDegree @ shape] ][[pbs]];

  AssociationThread[tag -> SparseArray /@ Flatten[mat . pbs, 1]]
] /; If[ DominatesQ[First @ shape, ReverseSort @ content], True,
  Message[DualSchurBasis::incmp, shape, content]; False
]

DualSchurBasis[shape_YoungShape, content:{__Integer}] := Association[]
(**** </DualSchurBasis> ****)


DualSchurBasisNames::usage = "DualSchurBasisNames[shape, content] returns {names, poslist}, where names is a list of labels referring to the irreducible basis vectors and poslist is the list of positions of standard Young tableaux that properly combines with content to generate a Weyl tableau."

DualSchurBasisNames[shape_YoungShape, content:{___Integer}] := Module[
  { yy = YoungTableaux[shape],
    ss = ContentVector[content], 
    ww },
  ww = yy /. Thread[Range @ Total @ content -> ss];
  ww = First /@ KeySelect[PositionIndex @ ww, WeylTableauQ];
  { Tuples @ {yy, Keys @ ww}, Values @ ww }
] /; YoungDegree[shape] == Total[content]


(**** <GelfandClasses> ****)
GelfandClasses::usage = "GelfandClasses[shape, content] returns an association grouping the standard Young tableaux of the specified shape into Gelfand-Tsetlin classes with respect to the given content.\nThe keys of the returned association are semistandard Young tableaux of the specified shape and content, each labeling one Gelfand-Tsetlin class. The values are lists of standard Young tableaux belonging to the corresponding class.\nThe number of classes equals the Kostka number K(shape, content), and only admissible classes (whose keys are valid semistandard tableaux) are included.";

GelfandClasses[shape_YoungShape, content:{___Integer}] := Module[
   { yy = YoungTableaux[shape],
     ss = ContentVector[content],
     ww },
   ww = yy /. Thread[Range[Total @ content] -> ss];
   ww = Map[If[WeylTableauQ[#], #, None]&, ww];
   ww = Merge[Thread[ww -> yy], Identity];
   Join[KeyDrop[ww, None], KeyTake[ww, None]]
] /; YoungDegree[shape] == Total[content]
(**** </GelfandClasses> ****)


(**** <GelfandClass> ****)
GelfandClass::usage = "GelfandClass[weyl, content] returns the standard Young tableaux in the Gelfand-Tsetlin class labeled by the Weyl tableau weyl with the given content.\nThe resulting standard Young tableaux form a basis spanning the Gelfand-Tsetlin subspace of the irreducible representation that is labeled by the Weyl tableau weyl with the given content.\nThis subspace is one-dimensional after applying the Young subgroup projector and is preserved by the chain of subgroups associated with content.";

GelfandClass[ssyt_List?WeylTableauQ, any_] :=
  GelfandClass[YoungTableau @ ssyt, any]

GelfandClass[weyl_YoungTableau, d_Integer] :=
  GelfandClass[weyl, YoungContent[weyl, d]]

GelfandClass[YoungTableau[weyl_List], mu:{___Integer}] := Module[
  { nn = Prepend[Accumulate[mu], 0], 
    strips, buildTableau },
  strips = Table[
    Module[
      {rowBoxes},
      rowBoxes = Association @@ Table[
        Module[{cols = Flatten[Position[weyl[[i]], k]]},
          If[cols === {}, Nothing, i -> cols]
        ],
        {i, Length[weyl]}
      ];
      stripFillings[rowBoxes, nn[[k]]]
    ],
    {k, Length @ mu}
  ];
  buildTableau[fillings_] := Module[
    {syt, rules},
    syt = Map[ConstantArray[0, #] &,  Length /@ weyl];
    rules = Join @@ fillings;
    Do[syt[[r[[1, 1]], r[[1, 2]]]] = r[[2]], {r, rules}];
    YoungTableau[syt]
  ];
  buildTableau /@ Tuples[strips]
]

(** Standard fillings of a single horizontal strip -- 
    rowBoxes: an association <| rowIndex -> {colIdx_1, colIdx_2, ...} |> listing the columns of boxes in this strip, by row.
    offset: the value N_{k-1}:=\mu_1+\mu_2+...+\mu_{k-1}, so entries are filled as offset + 1, ..., offset + m. **)

stripFillings[rowBoxes_Association, offset_Integer] := Module[
  { rows = Keys[rowBoxes], 
    sizes, m, shuffles },
  sizes = Length /@ Values[rowBoxes];
  m = Total[sizes];
  (* Enumerate ordered set partitions of {1,...,m} with block sizes 'sizes' *)
  shuffles = Permutations[Flatten[MapIndexed[ConstantArray[#2[[1]], #1] &, sizes]]];
  shuffles = DeleteDuplicates[shuffles];
  (* Each shuffle assigns a row-index to each of the m positions;
     for shuffle s, position j (with value offset+j) goes to the next
     unfilled column in row s[[j]]. *)
  Function[
    {shuffle},
    Module[
      { cursor = ConstantArray[1, Length[rows]], 
        filling = {}, 
        rowIdx },
      Do[
        rowIdx = shuffle[[j]];
        AppendTo[ filling,
          {rows[[rowIdx]], rowBoxes[rows[[rowIdx]]][[cursor[[rowIdx]]]]} -> offset + j
        ];
        cursor[[rowIdx]] += 1,
        {j, m}
      ];
      filling
    ]
  ] /@ shuffles
]
(**** </GelfandClass> ****)


End[]

EndPackage[]
