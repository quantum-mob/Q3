(* -*- mode: Mathematica -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ GelfandPattern };

{ GelfandPatterns, GelfandPatternQ, GelfandForm, GelfandOrder };

{ ToYoungTableau, ToGelfandPattern,
  GelfandContents };

{ GelfandYoungPatterns, GelfandYoungPatternQ };

{ WeylTableaux, WeylTableauCount, WeylTableauQ };

{ WeylType, WeylContents };

{ RSKMap };

{ ClebschGordanX, ReducedWigner };

{ PartialHook };

{ SchurBasisQ, SchurBasis, NextSchurLabels, GelfandAttach };

Begin["`Private`"]

WeylType::usage = "WeylType[tb] returns the content of Weyl tableau tb.\nThe content of a Weyl tableau is the inversely sorted list of multiplicities of numbers (or letters) appearing in the tableau.\nSimilar to WeylContents."

WeylType[yt_YoungTableau] := WeylType[First @ yt]

WeylType[data_?WeylTableauQ] := ReverseSort @ Values @ Counts[Flatten @ data]


WeylContents::usage = "WeylContents[tb, n] returns an association of the occupation numbers of the levels in the state described by the Weyl tableau tb.\nWeylContents[tb, n, f] maps the resulting keys by function f.\nEssentially the same as WeylType."

WeylContents[tb_?WeylTableauQ, n_Integer] := Join[
  AssociationThread[Range[n] -> 0],
  Counts[Flatten @ tb]
 ]

WeylContents[tb_?WeylTableauQ, n_Integer, func_] :=
  KeyMap[func, WeylContents[tb, n]]


(**** <GelfandPatterns> ****)

GelfandPatterns::usage = "GelfandPatterns[shape, d] constructs all possible Gelfand patterns for shape with d letters.\nGelfandPattern[n, d] returns all Gelfand patterns of order n with d letters."

SyntaxInformation[GelfandPatterns] = {"ArgumentsPattern" -> {_, _}}

GelfandPatterns[shape_?YoungShapeQ] := (
  CheckArguments[GelfandPatterns[shape], 2];
  GelfandPatterns[shape, Length @ shape]
 )

GelfandPatterns[n_Integer, d_Integer] :=
  Catenate @ Map[GelfandPatterns[#, d]&, IntegerPartitions @ n]

GelfandPatterns[YoungShape[data_List], d_Integer] :=
  GelfandPatterns[data, d]

GelfandPatterns[p:{___Integer}, d_Integer] :=
  Map[GelfandPattern, theGelfandPatterns @ PadRight[p, d]]


theGelfandPatterns[{k_Integer}] := {{{k}}}

theGelfandPatterns[p:{_Integer, __Integer}] := Module[
  { qq },
  qq = Tuples @ Successive[Range[#1, #2, -1]&, p];
  qq = Catenate[theGelfandPatterns /@ qq];
  Map[Prepend[#, p]&, qq]
 ]

(**** </GelfandPatterns> ****)


(**** <GelfandPatternQ> ****)

GelfandPatternQ::usage = "GelfandPatternQ[tb] returns True if tb represents a valid Gelfand pattern."

GelfandPatternQ[GelfandPattern[data_List]] := GelfandPatternQ[data]

GelfandPatternQ[tb:{__List}] := Module[
  { n = Length @ tb,
    new },
  new = Table[tb[[i-j+1, j]], {i, 1, n}, {j, 1, i}];
  TrueQ[
    And @@ Join[
      GreaterEqual @@@ YoungTranspose[tb],
      GreaterEqual @@@ new
     ]
   ]
 ]

anyGelfandPatternQ[tb:{{__Integer}..}] :=
  Equal[YoungShape @ tb, Reverse @ Range @ Length @ tb]

anyGelfandPatternQ[_] = False

(**** </GelfandPatternQ> ****)


(**** <GelfandForm> ****)

GelfandPattern::usage = "GelfandPattern[data] represents a Gelfand pattern specified by data."

Format[gp:GelfandPattern[data:{{___}..}]] :=
  Interpretation[GelfandForm @ data, gp]

YoungShape[GelfandPattern[data:{__List}]] :=
  YoungShape @ YoungTrim[First @ data]


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


(**** <GelfandYoungPatterns> ****)

GelfandYoungPatternQ::usage = "GelfandYoungPatternQ[tb] returns True if tb is a valid Gelfand-Young pattern and False otherwise.\nA Gelfand pattern is called a Gelfand-Young pattern if it corresponds to a standard Young tableau."

GelfandYoungPatternQ[gp_?GelfandPatternQ] :=
  ContainsOnly[Differences[Total /@ gp], {-1}]

GelfandYoungPatternQ[_] = False


GelfandYoungPatterns::usage = "GelfandYoungPatterns[shape] gives a list of all Gelfand-Young patterns of shape.\nGelfandYoungPatterns[n] returns the list of all Standrd Young Tableaux of roder n.\nA Gelfand pattern is called a Gelfand-Young pattern if it corresponds to a standard Young tableau.\nThe resulting list must equal Reverse @ Map[ToGelfandPattern[n], YoungTableaux[shape]], where n = Total[shape]."

GelfandYoungPatterns[n_Integer] :=
  Catenate @ Map[GelfandYoungPatterns, IntegerPartitions @ n]

GelfandYoungPatterns[YoungShape[data_List]] :=
  GelfandYoungPatterns[data]

GelfandYoungPatterns[{}] := { GelfandPattern[{{}}] }

GelfandYoungPatterns[p:{__Integer}] :=
  GelfandPattern /@ theGelfandYoung @ PadRight[p, Total @ p]

theGelfandYoung[{1}] = {{{1}}}

theGelfandYoung[p_?YoungShapeQ] := Module[
  { qq },
  qq = Tuples @ Successive[Range[#1, Max[#1-1, #2], -1]&, p];
  qq = Select[qq, Length[#] == Total[#]&];
  qq = Catenate[theGelfandYoung /@ qq];
  Map[Prepend[#, p]&, qq]
 ]

(* Method 2: This is much slower than the above.
   Currently (Young.wl,v1.94), YoungTableaux is based on the method borrowed
   from the legacy Combinatorica package. *)

oldGelfandYoungPatterns[shape_?YoungShapeQ] := With[
  { n = Total @ shape },
  Reverse @ Map[ToGelfandPattern[#, n]&, YoungTableaux @ shape]
 ]

(**** </GelfandYoungPatterns> ****)


(**** <WeylTableaux> ****)

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


WeylTableaux::usage = "WeylTableaux[shape, d] returns a list of all possible Weyl tableaux (semi-standard Young tableaux) of shape with entries of d letters.\nWeylTableax[n, d] returns the list of all Weyl tableaux of order n with entries of d letters."

SyntaxInformation[WeylTableaux] = {"ArgumentsPattern" -> {_, _}}

WeylTableaux[shape_?YoungShapeQ] := (
  CheckArguments[WeylTableaux[shape], 2];
  WeylTableaux[shape, Max @ shape]
 )

WeylTableaux[n_Integer, d_Integer] :=
  Catenate @ Map[WeylTableaux[#, d]&, IntegerPartitions @ n]

WeylTableaux[shape_?YoungShapeQ, d_Integer] :=
  ToYoungTableau /@ GelfandPatterns[shape, d]


WeylTableauCount::usage = "WeylTableauCount[shape, d] returns the number of Weyl tableaux of d letters consistent with shape."

WeylTableauCount[n_Integer, d_Integer] :=
  Total @ Map[WeylTableauCount[#, d]&, YoungShapes[n, d]]

WeylTableauCount[shape_YoungShape, d_Integer] :=
  WeylTableauCount[First @ shape, d]

WeylTableauCount[shape_List?YoungShapeQ, d_Integer] := With[
  { pp = PadRight[shape, d] },
  Product[pp[[i]] - pp[[j]] + j - i, {i, 1, d}, {j, i + 1, d}] /
   Product[j - i, {i, 1, d}, {j, i + 1, d}]
]
(* cf. ChoiceCount *)

(**** </WeylTableaux> ****)


(**** <ToYoungTableau> ****)

ToYoungTableau::usage = "ToYoungTableau[gz] converts Gelfand pattern gz to the corresponding semi-standard Young tableau."
(* See Krovi119a. *)

ToYoungTableau::notgp = "Data `` is not a valid Gelfand pattern."

ToYoungTableau[GelfandPattern[data_List]] :=
  YoungTableau[ToYoungTableau @ data]

ToYoungTableau[gp:{{___Integer}..}] := Module[
  { n = Length @ gp,
    dd },
  dd = Differences /@ Transpose @ Reverse @ PadRight[gp, {n+1, n}];
  YoungTrim[ Flatten /@ Table[Table[k, dd[[j, k]]], {j, n}, {k, n}] ]
 ]

ToYoungTableau[gp_] := (
  Message[ToYoungTableau::notgp, gp];
  gp
 )


YoungTableau @ GelfandPattern[data_] :=
  YoungTableau[ToYoungTableau @ data]

(**** </ToYoungTableau> ****)


(**** <GelfandContents> ****)

GelfandContents::usage = "GelfandContents[gp] returns an association of the occupation numbers of the levels in the state described by the Gelfand pattern gp.\nGelfandContents[gp, f] maps the resulting keys by function f."

GelfandContents[gp_?GelfandPatternQ] := With[
  { kk = Range @ Length @ gp,
    nn = Append[Total /@ gp, 0] },
  AssociationThread[kk -> Differences[Reverse @ nn]]
 ]

GelfandContents[gp_?GelfandPatternQ, func_] :=
  KeyMap[func, GelfandContents @ gp]

(**** </GelfandContents> ****)


(**** <ToGelfandPattern> ****)

ToGelfandPattern::usage = "ToGelfandPattern[tbl, n] converts a semi-standard Young tableau tbl to the corresponding Gelfand pattern of n letters.\nToGelfandPattern[n] represents an operation form."

ToGelfandPattern::notwt = "`` is not a valid Weyl tableau."

ToGelfandPattern[n_Integer][tb_?WeylTableauQ] := ToGelfandPattern[tb, n]

ToGelfandPattern[{}, 1] := { {0} }

ToGelfandPattern[tb_?WeylTableauQ, 1] := { Length /@ tb }

ToGelfandPattern[tb_YoungTableau, n_Integer] :=
  GelfandPattern @ ToGelfandPattern[First @ tb, n]

ToGelfandPattern[tb_List?WeylTableauQ, n_Integer] := Prepend[
  ToGelfandPattern[YoungTrim @ DeleteCases[tb, n, {2}], n-1],
  PadRight[Length /@ tb, n]
]

ToGelfandPattern[tb_, _Integer] := (
  Message[ToGelfandPattern::notwt, tb];
  { {0} }
)

ToGelfandPattern[tb_?WeylTableauQ] := (
  CheckArguments[ToGelfandPattern[tb], 2];
  ToGelfandPattern[tb, Max @ tb]
)

(**** </ToGelfandPattern> ****)


(**** <RSKMap> ****)

RSKMap::usage = "RSKMap[{{a1, a2, ...}, {b1, b2, ...}}] returns {p, q}, where p is a standard Young tableau and b is semi-standard Young tableau, corresponding to the generalized permutation specified by words {a1, a2, ...} and {b2, b2, ...} according to the RSK algorithm."

RSKMap[kk:{__Integer}] := RSKMap @ {Range[Length @ kk], kk}

RSKMap[{aa:{__Integer}, bb:{__Integer}}] :=
  Fold[rsk, {{}, {}}, Transpose @ {aa, bb}]


rsk[{{}, {}}, {a_Integer, b_Integer}] := {{{a}}, {{b}}}

rsk[{p_?YoungTableauQ, q_?WeylTableauQ}, {a_Integer, b_Integer}] :=
  Module[
    { pp, qq, aa, bb, ppp, qqq },
    {pp, qq, aa, bb} = rowInsert[First @ p, First @ q, a, b];
    If[ bb == 0,
      Return @ {Prepend[Rest @ p, pp], Prepend[Rest @ q, qq]}
     ];
    {ppp, qqq} = rsk[{Rest @ p, Rest @ q}, {aa, bb}];
    { Prepend[ppp, pp], Prepend[qqq, qq] }
   ]


rowInsert[{}, {}, a_Integer, b_Integer] := {{a}, {b}, 0, 0}

rowInsert[p:{__Integer}, q:{__Integer}, a_Integer, b_Integer] :=
  {Append[p, a], Append[q, b], 0, 0} /;
  AllTrue[q, (#<=b)&]

rowInsert[p:{__Integer}, q:{__Integer}, a_Integer, b_Integer] := Module[
  {j},
  j = First @ FirstPosition[Thread[q > b], True];
  {p, ReplacePart[q, j -> b], a, q[[j]]}
 ]

(**** </RSKMap> ****)


(**** <PartialHook> ****)

PartialHook::usage = "PartialHook[gz] returns a matrix with elements given by the partial hooks of Gelfand pattern gz."
(* See Biedenharn68a. *)

PartialHook[gz_] := With[
  { n = Length @ gz },
  Reverse @ PadRight[gz, {n, n}] + Array[(#1-#2)&, {n, n}]
 ]

GZtoMatrix::usage = "GZtoMatrix[gz] converts GZ pattern to a conventional matrix."

GZtoMatrix[gz_] := With[
  { n = Length @ gz },
  Reverse @ PadRight[gz, {n, n}]
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
      x1 = Aggregate[aa[[j]] - bb];
      y1 = Aggregate @ Delete[aa[[j]] - aa, j];
      x2 = y2 = 1;
      ff = newSign[d-j],
      (* Else *)
      x1 = Aggregate @ Delete[aa[[j]] - bb, k];
      x2 = Aggregate @ Delete[bb[[k]] - aa + 1, j];
      y1 = Aggregate @ Delete[aa[[j]] - aa, j];
      y2 = Aggregate @ Delete[bb[[k]] - bb + 1, k];
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


(**** <SchurBasis> ****)

SchurBasisQ::usage = "SchurBasisQ[obj] returns True obj is a Schur basis."

SchurBasisQ[
  bs:Association[({_GelfandPattern, _GelfandPattern} -> _)..]
 ] := AllTrue[Map[Apply[Length], Transpose @ Keys[bs], {2}], Apply[Equal]]

SchurBasisQ[_] = False


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
  dst = NextSchurLabels[yt, d];
  mat = SparseArray @ Outer[ClebschGordanX, src, Last @ Transpose @ dst, 1];

  tsr = Flatten @ Outer[CircleTimes, Values[bs], node, 1];
  AssociationThread[dst -> Garner[tsr . mat]]
 ]
          
regroupSchurBasis[bs_Association] := Merge[
  KeyValueMap[(First[#1] -> Rule[Last[#1], #2])&, bs],
  Association
 ]


NextSchurLabels::usage = "NextSchurLabels[gy, n] returns a list of pairs {yt, wt} of Gelfand patterns that are allowed to arise when one adds a node of n letters to the existing representation specified by Gelfand pattern gy. Each of the resulting pairs refers uniquely an element of the Schur basis for U(n) and S(N) where N = Length[gy] + 1."

NextSchurLabels[d_Integer][gy_GelfandPattern] :=
  NextSchurLabels[gy, d]
          
NextSchurLabels[gy_GelfandPattern, d_Integer] := 
  Join @@ Map[
    Tuples[{List @ #, GelfandPatterns[YoungShape @ #, d]}]&,
    GelfandAttach[gy, d]
   ]

GelfandAttach::usage = "GelfandAttach[gy, d] generates a list of new Gelfand-Young patterns that may arise when one adds a node of d-dimensional Hilbert space to the existing irreducible space associated with Gelfand-Young pattern gy."

GelfandAttach[d_Integer][gy_GelfandPattern] :=
  GelfandAttach[gy, d]  

GelfandAttach[GelfandPattern[gy_], d_Integer] := Module[
  { L = Length[gy] + 1,
    new },
  new = PadRight[First @ gy, L];
  new = Table[new + UnitVector[L, j], {j, 1, Min @ {d, L}}];
  GelfandPattern /@ Map[Prepend[gy, #]&, Select[new, YoungShapeQ]]
 ]

(* For the Schur basis *)
theKetFormatQ[_?GelfandPatternQ] = True

theKetFormat[gp_?GelfandPatternQ] := YoungForm[ToYoungTableau @ gp]
(* NOTE: Standard Young tableaux and Gelfand patterns can be distinguished. *)

(**** </SchurBasis> ****)

End[]

EndPackage[]
