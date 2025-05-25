(* -*- mode: Mathematica -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ GelfandPattern, GelfandPatternQ, GelfandPatterns, 
  GelfandOrder, GelfandForm };

{ GelfandYoungPatternQ, GelfandYoungPatterns };

{ WeylTableauQ, WeylTableaux, WeylTableauCount };

{ ClebschGordanX, ReducedWigner };

{ PartialHook };

{ SchurBasisQ, SchurBasis, SchurLabelPile, GelfandYoungPile };

Begin["`Private`"]

(**** <YoungType> ****)

YoungType::usage = "YoungType[tb] returns the type (or content or weight) of Weyl tableau tb; i.e., a list of multiplicities of numbers (or letters) appearing in the tableau."
(* Definition 2.9.1 in Sagan (2001) *)

YoungType::exss = "The second argument is not necessary and ignored."

YoungType::lett = "The number of letters (levels) must be given as the second argument."

YoungType[GelfandPattern[data_]] := With[
  { nn = Append[Total /@ data, 0] },
  Differences[Reverse @ nn]
]

YoungType[GelfandPattern[data_], d_Integer] :=
  PadRight[YoungType[any], d]

YoungType[YoungTableau[data_]] :=
  YoungType[YoungTableau @ data, Max @ data]

YoungType[YoungTableau[data_], d_Integer] := Values @ Join[
  AssociationThread[Range[d] -> 0],
  KeySelect[Counts[Flatten @ data], #<=d&]
]

(* flexibility *)
YoungType[data_?GelfandPatternQ, rest___] := 
  YoungType[GelfandPattern @ data, rest]

(* flexibility *)
YoungType[data_?WeylTableauQ, rest___] := 
  YoungType[YoungTableau @ data, rest]

(**** </Youngtype> ****)


(**** <YoungTypes> ****)

YoungTypes::usage = "YoungTypes[n, d] returns a list of types of degree n for d letters.\n YoungTypes[shape, d] returns a list of types ReverseSort of which are dominated by shape."

YoungTypes[n_Integer, d_Integer] := Module[
  { types = IntegerPartitions[n, d] },
  types = PadRight[types, {Length @ types, d}];
  Catenate @ Map[Permutations, types]
]

YoungTypes[shape_YoungShape, d_Integer] := Module[
  { types },
  types = Select[
    IntegerPartitions[YoungDegree @ shape, d], 
    DominatedBy[shape]
  ];
  types = PadRight[types, {Length @ types, d}];
  Catenate @ Map[Permutations, types]
]

(**** </YoungTypes> ****)


(**** <GelfandPattern> ****)

GelfandPattern::usage = "GelfandPattern[data] represents a Gelfand pattern specified by data.\nGelfandPattern[yt, d] converts Young tableau yt with entries of d letters to Gelfand pattern."
(* See Louck (2008). *)

GelfandPattern::ill = "Target dimension `` is smaller than the largest letter `` in the Weyl tableau."

SetAttributes[GelfandPattern, NHoldAll]

Format[gp:GelfandPattern[data:{{___}..}]] :=
  Interpretation[GelfandForm @ data, gp]

GelfandPattern /:
Equal[GelfandPattern[a_], GelfandPattern[b_]] := Equal[a, b]

GelfandPattern /:
YoungShape[GelfandPattern[data:{__List}]] :=
  YoungShape @ YoungTrim[First @ data]

(* Conversion: See Louck (2008). *)
GelfandPattern /:
YoungTableau[GelfandPattern[data_]] := Module[
  { dim = Length @ data,
    dff },
  dff = Differences /@ Transpose @ Reverse @ PadRight[data, {dim+1, dim}];
  YoungTableau @ YoungTrim[
    Flatten /@ MapIndexed[Table[Last @ #2, #1]&, dff, {2}] 
  ]
]

(* Conversion: See Louck (2008). *)
GelfandPattern[YoungTableau[data_], d_Integer] := Module[
  { kk = Reverse[Range @ d],
    mm },
  mm = FoldList[DeleteCases[#1, #2, {2}]&, data, Most @ kk];
  mm = Map[Length, mm, {2}];
  GelfandPattern @ MapThread[PadRight, {mm, kk}]
] /; If[
  d >= Max[data], True,
  Message[GelfandPattern::ill, d, Max @ data];
  False
]


theKetFormatQ[_GelfandPattern] = True

theKetFormat[gp_GelfandPattern] := YoungTableau[gp]

(**** </GelfandPattern> ****)


(**** <GelfandForm> ****)

GelfandForm::usage = "GelfandForm[tb] displays Gelfand pattern tb in the upper-left triangluar form."

GelfandForm::notgp = "Data `` is not of the Gelfand-pattern form."

GelfandForm[gp_GelfandPattern] = gp

GelfandForm[tb:{{___}..}] :=
  DisplayForm @ RowBox @ { "(", Grid[tb, Spacings -> {0.5, 0}], ")" }

GelfandForm[data_] := (
  Message[GelfandForm::notgp, data];
  data
)

(**** </GelfandForm> ****)


(**** <GelfandOrder> ****)

GelfandOrder::usage = "GelfandOrder[a, b] returns 1 if the Young tableaux corresponding to Gelfand patterns a and b are in the standard lexicographic order for Young tableaux."

(* NOTE: The lexicographic order of Young tableaux is different from the
   lexicographic order for normal lists. *)

GelfandOrder[a_?GelfandPatternQ, b_?GelfandPatternQ] := 
  Order[Rest @ a, Rest @ b] /; First[a] == First[b]

GelfandOrder[a_?GelfandPatternQ, b_?GelfandPatternQ] :=
  -Order[First @ a, First @ b]

(**** </GelfandOrder> ****)


(**** <GelfandPatternQ> ****)

GelfandYoungPatternQ::usage = "GelfandYoungPatternQ[tb] returns True if tb is a valid Gelfand-Young pattern and False otherwise.\nA Gelfand pattern is called a Gelfand-Young pattern if it corresponds to a standard Young tableau."

GelfandYoungPatternQ[gp_GelfandPattern] :=
  GelfandYoungPatternQ[First @ gp]

GelfandYoungPatternQ[gp_List?GelfandPatternQ] :=
  ContainsOnly[Differences[Total /@ gp], {-1}]

GelfandYoungPatternQ[_] = False

(**** </GelfandPatternQ> ****)


(**** <GelfandPatterns> ****)

GelfandPatterns::usage = "GelfandPatterns[shape, d] constructs all possible Gelfand patterns for shape with d letters.\nGelfandPattern[n, d] returns all Gelfand patterns of order n with d letters.\nGelfandPatterns[shape, type] returns a list of Gelfand patterns of shape and type."

SyntaxInformation[GelfandPatterns] = {"ArgumentsPattern" -> {_, _}}

GelfandPatterns[shape:(_YoungShape | _List?YoungShapeQ)] := (
  CheckArguments[GelfandPatterns[shape], 2];
  GelfandPatterns[shape, Length @ shape]
)

GelfandPatterns[n_Integer, d_Integer] :=
  Catenate @ Map[GelfandPatterns[#, d]&, YoungShapes[n, d]]

GelfandPatterns[data_List?YoungShapeQ, d_Integer] :=
  GelfandPatterns[YoungShape @ data, d]

GelfandPatterns[YoungShape[data_List], d_Integer] :=
  Map[GelfandPattern, theGelfandPatterns @ PadRight[data, d]]


theGelfandPatterns[{k_Integer}] := {{{k}}}

theGelfandPatterns[p:{_Integer, __Integer}] := Module[
  { qq },
  qq = Tuples @ Successive[Range[#1, #2, -1]&, p];
  qq = Catenate[theGelfandPatterns /@ qq];
  Map[Prepend[#, p]&, qq]
]


GelfandPatterns::incmp = "The degree of `` is different from the sum of type ``."

GelfandPatterns[data_List?YoungShapeQ, type:{__Integer}] :=
  GelfandPatterns[YoungShape @ data, type]

GelfandPatterns[YoungShape[data_List], type:{__Integer}] := Map[
  GelfandPattern, 
  theGelfandPatterns[PadRight[data, Length @ type], Accumulate @ type]
] /; If[ 
  Total[data] == Total[type], True,
  Message[GelfandPatterns::incmp, YoungShape[data], type]; False
]

theGelfandPatterns[{k_Integer}, {a_Integer}] :=
  If[k == a, {{{k}}}, {}]

theGelfandPatterns[pp:{_Integer, __Integer}, aa:{__Integer}] := Module[
  { qq },
  qq = Tuples @ Successive[Range[#1, #2, -1]&, pp];
  qq = Select[qq, Total[#] == aa[[-2]]&];
  qq = Catenate[theGelfandPatterns[#, Most @ aa]& /@ qq];
  Map[Prepend[#, pp]&, qq]
]

(**** </GelfandPatterns> ****)


(**** <GelfandPatternQ> ****)

GelfandPatternQ::usage = "GelfandPatternQ[tb] returns True if tb represents a valid Gelfand pattern."

GelfandPatternQ[GelfandPattern[data_List]] := GelfandPatternQ[data]

(* betweenness condition *)
GelfandPatternQ[data_?anyGelfandPatternQ] := 
  Apply[And, GreaterEqual @@@ Successive[Riffle, data]]

GelfandPatternQ[] = False


(* quick check *)
anyGelfandPatternQ[data:{{__Integer}..}] :=
  Equal[Length /@ data, Reverse @ Range @ Length @ data]

anyGelfandPatternQ[_] = False

(**** </GelfandPatternQ> ****)


(**** <GelfandYoungPatterns> ****)

GelfandYoungPatterns::usage = "GelfandYoungPatterns[shape] gives a list of all Gelfand-Young patterns of shape.\nGelfandYoungPatterns[n] returns the list of all Standrd Young Tableaux of roder n.\nA Gelfand pattern is called a Gelfand-Young pattern if it corresponds to a standard Young tableau."

GelfandYoungPatterns[n_Integer] :=
  Catenate @ Map[GelfandYoungPatterns, YoungShapes @ n]

GelfandYoungPatterns[data_List?YoungShapeQ] :=
  GelfandYoungPatterns[YoungShape @ data]

GelfandYoungPatterns[YoungShape @ {}] := { GelfandPattern[{{}}] }

GelfandYoungPatterns[YoungShape[p_]] :=
  GelfandPattern /@ theGelfandYoung @ PadRight[p, Total @ p]


theGelfandYoung[{1}] = {{{1}}}

theGelfandYoung[p:{___Integer}] := Module[
  { qq },
  qq = Tuples @ Successive[Range[#1, Max[#1-1, #2], -1]&, p];
  qq = Select[qq, Length[#] == Total[#]&];
  qq = Catenate[theGelfandYoung /@ qq];
  Map[Prepend[#, p]&, qq]
]

(**** </GelfandYoungPatterns> ****)


WeylTableauQ::usage = "WeylTableauQ[tb] yields True if tb represents a Weyl tableau (i.e., a semi-standard Young tableau) and False otherwise.\nSee also YoungTableauQ."

WeylTableauQ[YoungTableau[data_List]] := WeylTableauQ[data]

WeylTableauQ[{}] = True

WeylTableauQ[tb_?anyYoungTableauQ] := TrueQ[
  And @@ Join[
    LessEqual @@@ tb,
    Less @@@ YoungTranspose[tb]
  ]
]

WeylTableauQ[_] = False


(**** <WeylTableaux> ****)

WeylTableaux::usage = "WeylTableaux[shape, d] returns a list of all possible Weyl tableaux (semi-standard Young tableaux) of shape with entries of d letters.\nWeylTableax[n, d] returns the list of all Weyl tableaux of order n with entries of d letters.\nWeylTableaux[shape, type] returns a list of Weyl tableaux of type."

SyntaxInformation[WeylTableaux] = {"ArgumentsPattern" -> {_, _}}

WeylTableaux[shape_?YoungShapeQ] := (
  CheckArguments[WeylTableaux[shape], 2];
  WeylTableaux[shape, Max @ shape]
)

WeylTableaux[n_Integer, d_Integer] :=
  Catenate @ Map[WeylTableaux[#, d]&, YoungShapes[n, d]]

WeylTableaux[shape:(_YoungShape|_List?YoungShapeQ), d_Integer] :=
  YoungTableau /@ GelfandPatterns[shape, d]

WeylTableaux[shape:(_YoungShape|_List?YoungShapeQ), type:{__Integer}] :=
  YoungTableau /@ GelfandPatterns[shape, type]

(**** </WeylTableaux> ****)


(**** <WeylTableauCount> ****)

WeylTableauCount::usage = "WeylTableauCount[shape, d] returns the number of Weyl tableaux of d letters consistent with shape."

WeylTableauCount[n_Integer, d_Integer] :=
  Total @ Map[WeylTableauCount[#, d]&, YoungShapes[n, d]]

WeylTableauCount[data_List?YoungShapeQ, d_Integer] := 
  WeylTableauCount[YoungShape @ data, d]

WeylTableauCount[YoungShape[data_List], d_Integer] := With[
  { pp = PadRight[data, d] },
  Product[pp[[i]] - pp[[j]] + j - i, {i, 1, d}, {j, i + 1, d}] /
   Product[j - i, {i, 1, d}, {j, i + 1, d}]
]
(* cf. ChoiceCount *)

(**** </WeylTableauCount> ****)


(**** <PartialHook> ****)

PartialHook::usage = "PartialHook[gz] returns a matrix with elements of the partial hooks of Gelfand pattern gz."
(* See Biedenharn68a. *)

PartialHook[gz_List?GelfandPatternQ] :=
  PartialHook[GelfandPattern @ gz]

PartialHook[GelfandPattern[data_]] := With[
  { d = Length[data] },
  Reverse @ PadRight[data, {d, d}] + Array[(#1-#2)&, {d, d}]
]

(**** </PartialHook> ****)


(**** <ReducedWigner> ****)
(* See Bacon07a *)

ReducedWigner::usage = "ReducedWigner[n, {a, i}, {b, j}] returns the reduced Wigner coefficient of fundamental tensor operators of the U(n) group."

ReducedWigner[d_Integer,
  {a_?YoungShapeQ, j_Integer},
  {b_?YoungShapeQ, k_Integer}] := Module[
    {aa, bb, ff, x1, x2, y1, y2},
    
    aa = PadRight[a, d] + d - Range[d];
    bb = PadRight[b, d-1] + (d-1) - Range[d-1];

    If[ k == 0,
      x1 = Whole[aa[[j]] - bb];
      y1 = Whole @ Delete[aa[[j]] - aa, j];
      x2 = y2 = 1;
      ff = newSign[d-j],
      (* Else *)
      x1 = Whole @ Delete[aa[[j]] - bb, k];
      x2 = Whole @ Delete[bb[[k]] - aa + 1, j];
      y1 = Whole @ Delete[aa[[j]] - aa, j];
      y2 = Whole @ Delete[bb[[k]] - bb + 1, k];
      ff = newSign[k-j]
    ];

    ff * Sqrt[(x1 * x2) / (y1 * y2)]
  ] /; And[
    Length[YoungTrim @ a] <= d, 
    Length[YoungTrim @ b] < d
  ]

newSign[0] = 1;
newSign[x_] := Sign[x]

(**** </ReducedWigner> ****)


(**** <ClebschGordanX> ****)
(* See Louck70a and Louck08a. *)

CleschGordanX::usage = "ClebschGordanX[in, s, out] or ClebschGordanX[{in, s}, out] returns the extended Clebsch-Gordan coefficient of Gelfand basis state Ket[out] in terms of tensor product of Gelfand state Ket[in] and Ket[s]. Parameters out and in are specified by Gelfand patterns."

ClebschGordanX[{in_GelfandPattern, s_Integer}, out_GelfandPattern] :=
  ClebschGordanX[in, s, out]

ClebschGordanX[GelfandPattern[in_], s_Integer, GelfandPattern[out_]] :=
  If[s == 1 && out-in == {{1}}, 1, 0] /;
  1 == Length[out] == Length[in]

ClebschGordanX[GelfandPattern[in_], s_Integer, GelfandPattern[out_]] :=
  Module[
    { n = Length @ out,
      dd, ch, j },
    dd =  out - in;

    ch = DeleteCases[dd, 0, {2}];
    If[ ch != PadRight[{{1}}, n, {{}}], Return[0] ];

    j = First @ FirstPosition[dd[[1]], 1];
    ReducedWigner[n, {in[[1]], j}, {in[[2]], 0}]
  ] /; s == Length[out] == Length[in] > 1

ClebschGordanX[GelfandPattern[in_], s_Integer, GelfandPattern[out_]] :=
  Module[
    { n = Length @ out,
      dd, ch, j, k },
    dd =  Take[out, 2] - Take[in, 2];

    ch = DeleteCases[dd, 0, {2}];
    If[ ch != {{1}, {1}}, Return[0] ];

    j = First @ FirstPosition[dd[[1]], 1];
    k = First @ FirstPosition[dd[[2]], 1];
    ReducedWigner[n, {in[[1]], j}, {in[[2]], k}] * ClebschGordanX[
      GelfandPattern @ Rest @ in, s,
      GelfandPattern @ Rest @ out ]
  ] /; s < Length[out] == Length[in]

(**** </ClebschGordanX> ****)


SchurBasisQ::usage = "SchurBasisQ[obj] returns True obj is a Schur basis."

SchurBasisQ[
  bs:Association[({_GelfandPattern, _GelfandPattern} -> _)..]
] := AllTrue[Map[Apply[Length], Transpose @ Keys[bs], {2}], Apply[Equal]]

SchurBasisQ[_] = False


(**** <SchurBasis> ****)

SchurBasis::usage = "SchurBasis[n, d] constructs the Schur basis for a system of n particles with d-dimensional Hilbert space.\nSchurBasis[{q1, q2, \[Ellipsis], qn}] is equivalent to SchurBasis[d, n] with d = Dimension[q1] = Dimension[q2] = \[Ellipsis] = Dimension[qn] but the states are expressed in terms of labelled species {q1, q2, \[Ellipsis]}."

SchurBasis::dimen = "Non-identical dimensions ``. All the dimensions of the Hilbert spaces associated with the systems should be the same."

SchurBasis[d_Integer][n_Integer] := SchurBasis[n, d]

SchurBasis[1, d_Integer] := AssociationThread @ Rule[
  Tuples @ {GelfandPatterns[{1}, 1], GelfandPatterns[{1}, d]},
  Basis @ {d}
]

SchurBasis[n_Integer, d_Integer] :=
  Nest[SchurBasis[#, d]&, SchurBasis[1, d], n-1]


SchurBasis[{S_?SpeciesQ}] := AssociationThread @ Rule[
  Tuples @ {GelfandPatterns[{1}, 1], GelfandPatterns[{1}, Dimension @ S]},
  Basis[S]
]

SchurBasis[{a_?SpeciesQ, rest__?SpeciesQ}] :=
  Fold[SchurBasis, SchurBasis @ {a}, FlavorCap @ {rest}]
  

SchurBasis[S_?SpeciesQ] := SchurBasis[S[$]] /; Not[FlavorCapQ @ S]

SchurBasis[spec_][bs_?SchurBasisQ] := SchurBasis[bs, spec]

SchurBasis[bs_?SchurBasisQ, spec:(_Integer|_?SpeciesQ)] := KeySort[
  Join @@ With[
    { node = Basis @ {spec} },
    KeyValueMap[nextSchurBasis[#1, #2, node]&, regroupSchurBasis @ bs]
  ],
  -Order[#1, #2]&
]
(* NOTE: The sorted keys are not in lexicographic order;
   see also GelfandOrder. *)

nextSchurBasis[yt_GelfandPattern, bs_Association, node_List] := Module[
  { d = Length @ node,
    src, dst, mat, tsr },
  src = Tuples @ {Keys[bs], Range[d]};
  dst = SchurLabelPile[yt, d];
  mat = SparseArray @ Outer[ClebschGordanX, src, Last @ Transpose @ dst, 1];

  tsr = Flatten @ Outer[CircleTimes, Values[bs], node, 1];
  AssociationThread[dst -> Garner[tsr . mat]]
]
          
regroupSchurBasis[bs_Association] := Merge[
  KeyValueMap[(First[#1] -> Rule[Last[#1], #2])&, bs],
  Association
]

(**** </SchurBasis> ****)


(**** <SchurLabelPile> ****)

SchurLabelPile::usage = "SchurLabelPile[gy, d] returns a list of pairs {yt, wt} of Gelfand patterns that are allowed to arise when one adds a node of d letters to the existing representation specified by Gelfand-Young pattern gy. Each of the resulting pairs refers uniquely to an element of the Schur basis for U(d) and S(n) where n = YoungDegree[gy] + 1."

SchurLabelPile[d_Integer][gy_GelfandPattern] :=
  SchurLabelPile[gy, d]
          
SchurLabelPile[gy_GelfandPattern, d_Integer] := 
  Join @@ Map[
    Tuples[{List @ #, GelfandPatterns[YoungShape @ #, d]}]&,
    GelfandYoungPile[gy, d]
  ]
(* TODO (2025-05-24): This can be implemented in a more efficient way by using the braching rule of Gelfand-Zetlin basis in Section 3.2.1 of Bacon07a. *)

(**** </SchurLabelPile> ****)


(**** <GelfandYoungPile> ****)

GelfandYoungPile::usage = "GelfandYoungPile[gy, d] generates a list of new Gelfand-Young patterns that may arise when one adds a node of d-dimensional Hilbert space to the existing irreducible space associated with Gelfand-Young pattern gy."

GelfandYoungPile[d_Integer][gy_GelfandPattern] :=
  GelfandYoungPile[gy, d]  

GelfandYoungPile[GelfandPattern[gy_], d_Integer] := Module[
  { L = Length[gy] + 1,
    new },
  new = PadRight[First @ gy, L];
  new = Table[new + UnitVector[L, j], {j, 1, Min @ {d, L}}];
  GelfandPattern /@ Map[Prepend[gy, #]&, Select[new, YoungShapeQ]]
]

GelfandYoungPile[yt_YoungTableau, d_Integer] := With[
  { n = YoungDegree[yt] },
  GelfandYoungPile[GelfandPattern[yt, n], d]
]

(**** </GelfandYoungPile> ****)

End[]

EndPackage[]
