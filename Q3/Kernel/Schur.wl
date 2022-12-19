(* -*- mode: Mathematica -*- *)

BeginPackage["Q3`"];

`Schur`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.120 $"][[2]], " (",
  StringSplit["$Date: 2022-12-19 11:48:19+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ GelfandPatterns, GelfandPatternQ, GelfandForm };

{ ToYoungTableau, ToGelfandPattern,
  GelfandContents };

{ GelfandYoungPatterns, GelfandYoungPatternQ };

{ WeylTableaux, WeylTableauCount, WeylTableauQ };

{ WeylType, WeylContents };

{ RSKMap };

{ ClebschGordanX, ReducedWigner };

{ PartialHook };

{ SchurBasisQ, SchurBasis, NextSchurLabels, NextGelfandYoungPatterns };

(**** Obsoletes ****)

{ CountWeylTableaux }; (* renamed *)

Begin["`Private`"]

WeylType::usage = "WeylType[tb] returns the content of Weyl tableau tb.\nThe content of a Weyl tableau is the inversely sorted list of multiplicities of numbers (or letters) appearing in the tableau.\nSimilar to WeylContents."

WeylType[tb_?WeylTableauQ] := ReverseSort @ Values @ Counts[Flatten @ tb]


WeylContents::usage = "WeylContents[tb, n] returns an association of the occupation numbers of the levels in the state described by the Weyl tableau tb.\nWeylContents[tb, n, f] maps the resulting keys by function f.\nEssentially the same as WeylType."

WeylContents[tb_?WeylTableauQ, n_Integer] := Join[
  AssociationThread[Range[n] -> 0],
  Counts[Flatten @ tb]
 ]

WeylContents[tb_?WeylTableauQ, n_Integer, func_] :=
  KeyMap[func, WeylContents[tb, n]]

(**** <GelfandPatterns> ****)

GelfandPatterns::usage = "GelfandPatterns[shape] constructs all possible Gelfand patterns consistent with shape.\nGelfandPatterns[shape, n] constructs all possible Gelfand patterns for shape and with n letters."

GelfandPatterns[p_?YoungShapeQ, d_Integer] :=
  GelfandPatterns @ PadRight[p, d]

GelfandPatterns[{k_Integer}] := {{{k}}}

GelfandPatterns[p_?YoungShapeQ] := Module[
  { qq },
  qq = Tuples @ Successive[Range[#1, #2, -1]&, p];
  qq = Catenate[GelfandPatterns /@ qq];
  Map[Prepend[#, p]&, qq]
 ]

(**** </GelfandPatterns> ****)


(**** <GelfandPatternQ> ****)

GelfandPatternQ::usage = "GelfandPatternQ[tb] returns True if tb represents a valid Gelfand pattern."

GelfandPatternQ[tb_?anyGelfandPatternQ] := Module[
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

GelfandForm::usage = "GelfandForm[tb] displays Gelfand pattern tb in the upper-left triangluar form."

GelfandForm::notgp = "Data `` is not of the Gelfand-pattern form."

GelfandForm[tb_?anyGelfandPatternQ] := DisplayForm @ RowBox @ {
  "(", Grid[tb, Spacings -> {0.5, 0}], ")"
 }

GelfandForm[data_] := (
  Message[GelfandForm::notgp, data];
  data
 )

(**** </GelfandForm> ****)


(**** <GelfandYoungPatterns> ****)

GelfandYoungPatternQ::usage = "GelfandYoungPatternQ[tb] returns True if tb is a valid Gelfand-Young pattern and False otherwise.\nA Gelfand pattern is called a Gelfand-Young pattern if it corresponds to a standard Young tableau."

GelfandYoungPatternQ[gp_?GelfandPatternQ] :=
  ContainsOnly[Differences[Total /@ gp], {-1}]

GelfandYoungPatternQ[_] = False


GelfandYoungPatterns::usage = "GelfandYoungPatterns[shape] gives a list of all Gelfand-Young patterns of shape.\nA Gelfand pattern is called a Gelfand-Young pattern if it corresponds to a standard Young tableau.\nThe resulting list must equal Reverse @ Map[ToGelfandPattern[n], YoungTableaux[shape]], where n = Total[shape]."

GelfandYoungPatterns[{}] := {{{}}}

GelfandYoungPatterns[p_?YoungShapeQ] :=
  theGelfandYoung @ PadRight[p, Total @ p]

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

WeylTableauQ[{}] = True

WeylTableauQ[tb_?anyYoungTableauQ] := TrueQ[
  And @@ Join[
    LessEqual @@@ tb,
    Less @@@ YoungTranspose[tb]
   ]
 ]

WeylTableauQ[_] = False


WeylTableaux::usage = "WeylTableaux[shape, n] returns a list of all possible Weyl tableaux (semi-standard Young tableaux) of shape with entries of n letters."

WeylTableaux[shape_?YoungShapeQ, d_Integer] :=
  ToYoungTableau /@ GelfandPatterns[shape, d]

SyntaxInformation[WeylTableaux] = {"ArgumentsPattern" -> {_, _}}

WeylTableaux[shape_?YoungShapeQ] := (
  CheckArguments[WeylTableaux[shape], 2];
  WeylTableaux[shape, Max @ shape]
 )


WeylTableauCount::usage = "WeylTableauCount[shape, d] returns the number of Weyl tableaux of d letters consistent with shape."

WeylTableauCount[shape_?YoungShapeQ, d_Integer] := Module[
  { pp = PadRight[shape, d],
    mm, vv },
  vv = Times @@
    (Flatten @ Table[pp[[i]] - pp[[j]] + j - i, {i, 1, d}, {j, i+1, d}]);
  mm = Times @@
    (Flatten @ Table[j - i, {i, 1, d}, {j, i+1, d}]);
  vv / mm
 ]

CountWeylTableaux[args__] := (
  Message[Q3General::renamed, "CountWeylTableaux", "WeylTableauCount"];
  WeylTableauCount[args]
 )

(**** </WeylTableaux> ****)


(**** <ToYoungTableau> ****)

ToYoungTableau::usage = "ToYoungTableau[gz] converts Gelfand pattern gz to the corresponding semi-standard Young tableau."
(* See Krovi119a. *)

ToYoungTableau::notgp = "Data `` is not a valid Gelfand pattern."

ToYoungTableau[tb_?GelfandPatternQ] := Module[
  { n = Length @ tb,
    mm, dd },
  mm = Transpose @ Reverse @ PadRight[tb, {n+1, n}];
  dd = Differences /@ mm;
  YoungTrim[ Flatten /@ Table[Table[k, dd[[j, k]]], {j, n}, {k, n}] ]
 ]

ToYoungTableau[tb_] := (
  Message[ToYoungTableau::notgp, tb];
  tb
 )

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

ToGelfandPattern[tb_?WeylTableauQ, n_Integer] := Prepend[
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
      x1 = Times @@ (aa[[j]] - bb);
      y1 = Times @@ Delete[aa[[j]] - aa, j];
      x2 = y2 = 1;
      ff = newSign[d-j],
      (* Else *)
      x1 = Times @@ Delete[aa[[j]] - bb, k];
      x2 = Times @@ Delete[bb[[k]] - aa + 1, j];
      y1 = Times @@ Delete[aa[[j]] - aa, j];
      y2 = Times @@ Delete[bb[[k]] - bb + 1, k];
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

ClebschGordanX[{in_?GelfandPatternQ, s_Integer}, out_?GelfandPatternQ] :=
  ClebschGordanX[in, s, out]

ClebschGordanX[in_?GelfandPatternQ, s_Integer, out_?GelfandPatternQ] :=
  If[ s == 1 && out-in == {{1}}, 1, 0 ] /;
  1 == Length[out] == Length[in]

ClebschGordanX[in_?GelfandPatternQ, s_Integer, out_?GelfandPatternQ] :=
  Module[
    { n = Length @ out,
      dd, ch, j },
    dd =  out - in;

    ch = DeleteCases[dd, 0, {2}];
    If[ ch != PadRight[{{1}}, n, {{}}], Return[0] ];

    j = First @ FirstPosition[dd[[1]], 1];
    ReducedWigner[n, {in[[1]], j}, {in[[2]], 0}]
   ] /; s == Length[out] == Length[in]

ClebschGordanX[in_?GelfandPatternQ, s_Integer, out_?GelfandPatternQ] :=
  Module[
    { n = Length @ out,
      dd, ch, j, k },
    dd =  Take[out, 2] - Take[in, 2];

    ch = DeleteCases[dd, 0, {2}];
    If[ ch != {{1}, {1}}, Return[0] ];

    j = First @ FirstPosition[dd[[1]], 1];
    k = First @ FirstPosition[dd[[2]], 1];
    ReducedWigner[n, {in[[1]], j}, {in[[2]], k}] *
      ClebschGordanX[Rest @ in, s, Rest @ out]
   ] /; s < Length[out] == Length[in]

(**** </ClebschGordanX> ****)


(**** <SchurBasis> ****)

SchurBasisQ::usage = "SchurBasisQ[obj] returns True obj is a Schur basis."

HoldPattern @ SchurBasisQ[
  bs:Association[({_?GelfandPatternQ, _?GelfandPatternQ} -> _)..]
 ] := AllTrue[Map[Length, Transpose @ Keys[bs], {2}], Apply[Equal]]

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
    Fold[SchurBasis, SchurBasis @ {a}, FlavorNone @ {rest}]
  

SchurBasis[S_?SpeciesQ] := SchurBasis[S[None]] /;
  FlavorLast[S] =!= None

SchurBasis[spec_][bs_?SchurBasisQ] := SchurBasis[bs, spec]

SchurBasis[bs_?SchurBasisQ, spec:(_Integer|_?SpeciesQ)] := With[
  { node = Basis @ {spec} },
  Join @@ KeyValueMap[nextSchurBasis[#1, #2, node]&, regroupSchurBasis @ bs]
 ]
  
nextSchurBasis[yt_?GelfandPatternQ, bs_Association, node_List] := Module[
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

NextSchurLabels[d_Integer][gy_?GelfandPatternQ] :=
  NextSchurLabels[gy, d]
          
NextSchurLabels[gy_?GelfandPatternQ, d_Integer] := 
  Join @@ Map[
    Tuples[{List @ #, GelfandPatterns[First @ #, d]}]&,
    NextGelfandYoungPatterns[gy, d]
   ]

NextGelfandYoungPatterns::usage = "NextGelfandYoungPatterns[gy, d] generates a list of new Gelfand-Young patterns that may arise when one adds a node of d-dimensional Hilbert space to the existing irreducible space associated with Gelfand-Young pattern gy."

NextGelfandYoungPatterns[d_Integer][gy_?GelfandPatternQ] :=
  NextGelfandYoungPatterns[gy, d]  

NextGelfandYoungPatterns[gy_?GelfandPatternQ, d_Integer] := Module[
  { L = Length[gy] + 1,
    new },
  new = PadRight[First @ gy, L];
  new = Table[new + UnitVector[L, j], {j, 1, Min @ {d, L}}];
  Map[Prepend[gy, #]&, Select[new, YoungShapeQ]]
 ]

(**** </SchurBasis> ****)

End[]

EndPackage[]
