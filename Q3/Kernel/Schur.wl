(* -*- mode: Mathematica -*- *)

BeginPackage["Q3`"];

`Schur`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.58 $"][[2]], " (",
  StringSplit["$Date: 2021-12-08 00:41:39+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ RSKMap };

{ GelfandPatterns, GelfandPatternQ, GelfandPatternForm,
  ToYoungTableau, ToGelfandPattern };

{ WeylTableaux, CountWeylTableaux, WeylTableauQ };

{ ClebschGordanX, ReducedWigner };

{ PartialHook, GZtoMatrix };

{ SchurBasisQ, SchurBasis, NextSchurBasis, NextIrreducibleLabels };

{ DualSchurBasis, RelabelSchurBasis };


Begin["`Private`"]

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

GelfandPatternQ::usage = "GelfandPatternQ[tb] returns True if tb represents a Gelfand pattern."

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

anyGelfandPatternQ[tb_] :=
  Equal[YoungShape @ tb, Reverse @ Range @ Length @ tb]

(**** </GelfandPatternQ> ****)


(**** <GelfandPatternForm> ****)

GelfandPatternForm::usage = "GelfandPatternForm[tb] displays Gelfand pattern tb in the upper-left triangluar form."

GelfandPatternForm::notyt = "Data `` is not of Gelfand-pattern form."

(* This is the conventional form. *)
(*
GelfandPatternForm[tb_?anyGelfandPatternQ] := DisplayForm @ RowBox @ {
  "(",
  Grid[
    MapIndexed[ArrayPad[#1, #2-1, Null]&, Map[Riffle[#, Null]&, tb]],
    Spacings -> {0, 0.5}
   ],
  ")"
 }
 *)

GelfandPatternForm[tb_?anyGelfandPatternQ] := DisplayForm @ RowBox @ {
  "(", Grid[tb, Spacings -> {0.5, 0}], ")"
 }

GelfandPatternForm[data_] := (
  Message[GelfandPatternForm::notyt, data];
  data
 )

(**** </GelfandPatternForm> ****)


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


WeylTableaux::usage = "WeylTableaux[shape, n] returns a list of all possible Weyl tableaux (semi-standard Young tableaux) of shape with entries of n letters.\nWeylTableaux[shape] is equivalent to WeylTableaux[shape, Length @ shape]."

WeylTableaux[shape_?YoungShapeQ, d_Integer] :=
  WeylTableaux @ PadRight[shape, d]

WeylTableaux[shape_?YoungShapeQ] :=
  ToYoungTableau /@ GelfandPatterns[shape]


CountWeylTableaux::usage = "CountWeylTableaux[shape, d] returns the number of Weyl tableaux of d letters consistent with shape."

CountWeylTableaux[shape_?YoungShapeQ, d_Integer] := Module[
  { pp = PadRight[shape, d],
    mm, vv },
  vv = Times @@
    (Flatten @ Table[pp[[i]] - pp[[j]] + j - i, {i, 1, d}, {j, i+1, d}]);
  mm = Times @@
    (Flatten @ Table[j - i, {i, 1, d}, {j, i+1, d}]);
  vv / mm
 ]

(**** </WeylTableaux> ****)


ToYoungTableau::usage = "ToYoungTableau[gz] converts Gelfand pattern gz to the corresponding semi-standard Young tableau."
(* See Krovi119a. *)

ToYoungTableau[tb_?GelfandPatternQ] := Module[
  { n = Length @ tb,
    mm, dd },
  mm = Transpose @ Reverse @ PadRight[tb, {n+1, n}];
  dd = Differences /@ mm;
  YoungTrim[ Flatten /@ Table[Table[k, dd[[j, k]]], {j, n}, {k, n}] ]
 ]


ToGelfandPattern::usage = "ToGelfandPattern[tbl, n] converts a semi-standard Young tableau tbl to the corresponding Gelfand pattern of n letters."

ToGelfandPattern::onearg = "ToGelfandPattern requires two arguments. `` is assumed for the second argument."

ToGelfandPattern[{}, 1] := { {0} }

ToGelfandPattern[tb_?WeylTableauQ, 1] := { Length /@ tb }

ToGelfandPattern[tb_?WeylTableauQ, n_Integer] := Prepend[
    ToGelfandPattern[YoungTrim @ DeleteCases[tb, n, {2}], n-1],
    PadRight[Length /@ tb, n]
   ]

ToGelfandPattern[tb_?WeylTableauQ] := With[
  { n = Max[tb] },
  Message[ToGelfandPattern::onearg, n];
  ToGelfandPattern[tb, n]
 ]

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


SchurBasisQ::usage = "SchurBasis[obj] returns True obj is an Schur basis."

HoldPattern @ SchurBasisQ[bs:Association[(_?GelfandPatternQ -> _List)..]] :=
  Module[
    { kk = Keys @ bs },
    If[ Equal @@ Map[Length, kk], True, False, False ]
   ]

SchurBasisQ[_] = False


(**** <SchurBasis> ****)

SchurBasis::usage = "SchurBasis[d, n] constructs the Schur basis for a system of n particles with d-dimensional Hilbert space.\nSchurBasis[{q1, q2, \[Ellipsis], qn}] is equivalent to SchurBasis[d, n] with d = Dimension[q1] = Dimension[q2] = \[Ellipsis] = Dimension[qn] but the states are expressed in terms of labelled species."

SchurBasis::dimen = "Non-identical dimensions ``. All the dimensions of the Hilbert spaces associated with the systems should be the same."
  
SchurBasis[d_Integer, n_Integer] := Nest[
  NextSchurBasis[#, d]&,
  Association[{{1}} -> Map[Ket, Range @ d]],
  n-1
 ]

SchurBasis[qq:{__?QubitQ}] := Module[
  { n = Length @ qq,
    bs },
  bs = SchurBasis[2, n];
  Association[ Normal[bs] /. { Ket[ss__] :> Ket[qq -> {ss}-1] } ]
 ]

SchurBasis[qq:{__?QuditQ}] := Module[
  { n = Length @ qq,
    d = Dimension @ qq,
    bs },
  If[ Equal @@ d, d = First[d],
    Message[SchurBasis::dimen, d];
    Return[{}]
   ];
  bs = SchurBasis[d, n];
  Association[ Normal[bs] /. { Ket[ss__] :> Ket[qq -> {ss}-1] } ]
 ]
  

NextSchurBasis::usage = "NextSchurBasis[bs, n] constructs an irreducible basis for the enlarged system with one more node of n letters by using the Bacon-Chuang-Harrow algorithm."

NextSchurBasis[bs_?SchurBasisQ, d_Integer] :=
  Join @@ KeyValueMap[NextSchurBasis[#1, #2, d]&, bs]

NextSchurBasis[tb_?GelfandPatternQ, bs_List, d_Integer] := Module[
  { tsr, dst, mat, new },
  tsr = GelfandPatterns[First @ tb, d];
  tsr = Tuples @ {tsr, Range[d]};
  
  dst = NextIrreducibleLabels[tb, d];
  mat = matSchurTransform[#, tsr]& /@ dst;
  
  tsr = CircleTimes @@@ Tuples[{bs, Ket /@ Range[d]}];
  
  new = Garner @ Map[(tsr.#)&, mat];
  AssociationThread[dst -> new]
 ]

matSchurTransform[dst_?GelfandPatternQ, tsr_List] := Module[
  { d = Length[First @ First @ tsr],
    lbl },
  lbl = GelfandPatterns[First @ dst, d];
  Outer[ClebschGordanX, tsr, lbl, 1]
 ]

NextIrreducibleLabels::usage = "NextIrreducibleLabels[tb, n] returns new Gelfand patterns when one adds a node of n letters to the existing representation specified by Gelfand pattern tb. Each of the resulting Gelfand patterns refers uniquely to an irreducible representation of both U(n) and S(N), where N = Length[tb] + 1."

NextIrreducibleLabels[tb_?GelfandPatternQ, d_Integer] := Module[
  { L = Length[tb] + 1,
    new },
  new = PadRight[First @ tb, L];
  new = Table[new + UnitVector[L, j], {j, 1, Min @ {d, L}}];
  Map[Prepend[tb, #]&, Select[new, YoungShapeQ]]
 ]

(**** </SchurBasis> ****)


(**** <DualSchurBasis> ****)

DualSchurBasis::usage = "DualSchurBasis[d, n] constructs the dual Schur basis for a system of n particles with d-dimensional Hilbert space."

DualSchurBasis[args__] := RelabelSchurBasis @ SchurBasis[args]

DualSchurBasis[d_Integer, n_Integer] :=
  RelabelSchurBasis[SchurBasis[d, n], d]

DualSchurBasis[qq:{__?QubitQ}] := 
  RelabelSchurBasis[SchurBasis @ qq, 2]

DualSchurBasis[qq:{__?QuditQ}] :=
  RelabelSchurBasis[SchurBasis @ qq, Dimension @ First @ qq]


RelabelSchurBasis::usage = "RelabelSchurBasis[bs, d] regroups the elements in Schur basis bs so that irreducible bases are labelled by Weyl tableaux (i.e, semi-standard Young tableaux), or more precisely, the Gelfand patterns corresponding to them."

RelabelSchurBasis[bs_?SchurBasisQ, d_Integer] :=
  Merge[KeyValueMap[RelabelSchurBasis[d], bs], Union]

RelabelSchurBasis[d_Integer][gz_?GelfandPatternQ, bs_List] := Module[
  { new },
  new = GelfandPatterns[First @ gz, d];
  Association @ MapThread[Rule, {new, bs}]
 ]

(**** </DualSchurBasis> ****)


End[]

EndPackage[]
