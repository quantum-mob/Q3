(* -*- mode: Mathematica -*- *)

BeginPackage["Q3`"];

`Schur`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.37 $"][[2]], " (",
  StringSplit["$Date: 2021-12-02 20:56:34+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ RSKMap };

{ GelfandZetlinPatterns, WeylTableaux, GelfandZetlinQ,
  ToYoungTableau, ToGelfandZetlin };

{ ClebschGordanX, ReducedWigner };

{ PartialHook, GZtoMatrix };

{ SchurBasisQ, SchurBasis, NextSchurBasis, NextIrreducibleLabels };


Begin["`Private`"]

(**** <GelfandZetlinPatterns> ****)

GelfandZetlinPatterns::usage = "GelfandZetlinPatterns[shape] constructs all possible Gelfand-Zetlin patterns consistent with shape.\nGelfandZetlinPatterns[shape, n] constructs all possible Gelfand-Zetlin patterns for shape and with n letters."

GelfandZetlinPatterns[p_?IntegerPartitionQ, d_Integer] :=
  GelfandZetlinPatterns @ PadRight[p, d]

GelfandZetlinPatterns[{k_Integer}] := {{{k}}}

GelfandZetlinPatterns[p_?IntegerPartitionQ] := Module[
  { qq },
  qq = Tuples[Successive[Range[#1, #2, -1]&, p]];
  qq = Catenate[GelfandZetlinPatterns /@ qq];
  Map[Prepend[#, p]&, qq]
 ]

WeylTableaux::usage = "WeylTableaux[shape, n] returns all Weyl tableau (semi-standard Young tableaux) of shape with n letters.\nWeylTableaux[shape] is equivalent to WeylTableaux[shape, Length @ shape]."

WeylTableaux[shape_?IntegerPartitionQ, n_Integer] :=
  WeylTableaux[PadRight[shape, n]]

WeylTableaux[shape_?IntegerPartitionQ] :=
  ToYoungTableau /@ GelfandZetlinPatterns[shape]

(**** </GelfandZetlinPatterns> ****)


(**** <GelfandZetlinQ> ****)

GelfandZetlinQ::usage = "GelfandZetlinQ[tbl] returns True if tbl represents a Gelfand-Zetlin pattern."

GelfandZetlinQ[tb_] := Module[
  { n = Length @ tb,
    new },
  If[ Not @ Equal[YoungShape @ tb, Reverse @ Range @ n],
    Return[False]
   ];
  new = Table[tb[[i-j+1, j]], {i, 1, n}, {j, 1, i}];
  And @@ Join[
    GreaterEqual @@@ YoungTranspose[tb],
    GreaterEqual @@@ new
   ] 
 ]

(**** </GelfandZetlinQ> ****)


ToYoungTableau::usage = "ToYoungTableau[gz] converts Gelfand-Zetlin pattern gz to the corresponding semi-standard Young tableau."
(* See Krovi119a. *)

ToYoungTableau[tb_?GelfandZetlinQ] := Module[
  { n = Length @ tb,
    mm, dd },
  mm = Transpose @ Reverse @ PadRight[tb, {n+1, n}];
  dd = Differences /@ mm;
  DeleteCases[ Flatten /@ Table[Table[k, dd[[j, k]]], {j, n}, {k, n}], {} ]
 ]


ToGelfandZetlin::usage = "ToGelfandZetlin[tbl, n] converts a semi-standard Young tableau tbl to the corresponding Gelfand-Zetlin pattern of n letters."

ToGelfandZetlin[{}, 1] := { {0} }

ToGelfandZetlin[tbl_?YoungTableauQ, 1] := { Length /@ tbl }

ToGelfandZetlin[tbl_?YoungTableauQ, n_Integer] := Prepend[
    ToGelfandZetlin[DeleteCases[DeleteCases[tbl, n, {2}], {}], n-1],
    PadRight[Length /@ tbl, n]
   ]


(**** <RSKMap> ****)

RSKMap::usage = "RSKMap[{{a1, a2, ...}, {b1, b2, ...}}] returns {p, q}, where p is a standard Young tableau and b is semi-standard Young tableau, corresponding to the generalized permutation specified by words {a1, a2, ...} and {b2, b2, ...} according to the RSK algorithm."

RSKMap[kk:{__Integer}] := RSKMap @ {Range[Length @ kk], kk}

RSKMap[{aa:{__Integer}, bb:{__Integer}}] :=
  Fold[rsk, {{}, {}}, Transpose @ {aa, bb}]


rsk[{{}, {}}, {a_Integer, b_Integer}] := {{{a}}, {{b}}}

rsk[{p_?YoungTableauQ, q_?YoungTableauQ}, {a_Integer, b_Integer}] :=
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


GZtoMatrix::usage = "GZtoMatrix[gz] converts GZ pattern to a conventional matrix."

GZtoMatrix[gz_] := With[
  { n = Length @ gz },
  Transpose @ Reverse @ PadRight[gz, {n, n}]
 ]

PartialHook::usage = "PartialHook[gz] returns a matrix with elements given by the partial hooks of Gelfand-Zetlin pattern gz."
(* See Biedenharn68a. *)

PartialHook[gz_] := With[
  { n = Length @ gz },
  GZtoMatrix[gz] + Array[(#2-#1)&, {n, n}]
 ]


(**** <ReducedWigner> ****)
(* See Bacon07a *)

ReducedWigner::usage = "ReducedWigner[n, {a, i}, {b, j}] returns the reduced Wigner coefficient of fundamental tensor operators of the U(n) group."

ReducedWigner[d_Integer,
  {a_?IntegerPartitionQ, j_Integer},
  {b_?IntegerPartitionQ, k_Integer}] := Module[
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
     Length[IntegerPartitionTrim @ a] <= d, 
     Length[IntegerPartitionTrim @ b] < d
    ]

newSign[0] = 1;
newSign[x_] := Sign[x]

(**** </ReducedWigner> ****)


(**** <ClebschGordanX> ****)

CleschGordanX::usage = "ClebschGordanX[in, s, out] or ClebschGordanX[{in, s}, out] returns the extended Clebsch-Gordan coefficient of Gelfand-Zetlin basis state Ket[out] in terms of tensor product of Gelfand-Zetlin state Ket[in] and Ket[s]. Parameters out and in are specified by Gelfand-Zetlin patterns."

ClebschGordanX[{in_?GelfandZetlinQ, s_Integer}, out_?GelfandZetlinQ] :=
  ClebschGordanX[in, s, out]

ClebschGordanX[in_?GelfandZetlinQ, s_Integer, out_?GelfandZetlinQ] :=
  If[ s == 1 && out-in == {{1}}, 1, 0 ] /;
  1 == Length[out] == Length[in]

ClebschGordanX[in_?GelfandZetlinQ, s_Integer, out_?GelfandZetlinQ] :=
  Module[
    { n = Length @ out,
      dd, ch, j },
    dd =  out - in;

    ch = DeleteCases[dd, 0, {2}];
    If[ ch != PadRight[{{1}}, n, {{}}], Return[0] ];

    j = First @ FirstPosition[dd[[1]], 1];
    ReducedWigner[n, {in[[1]], j}, {in[[2]], 0}]
   ] /; s == Length[out] == Length[in]

ClebschGordanX[in_?GelfandZetlinQ, s_Integer, out_?GelfandZetlinQ] :=
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

HoldPattern @ SchurBasisQ[bs:Association[(_?GelfandZetlinQ -> _List)..]] :=
  Module[
    { kk = Keys @ bs },
    If[ Equal @@ Map[Length, kk], True, False, False ]
   ]

SchurBasisQ[_] = False


(**** <SchurBasis> ****)

SchurBasis::usage = "SchurBasis[d, n] constructs the Schur basis for a system of n particles with d-dimensional Hilbert space."

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

NextSchurBasis[tb_?GelfandZetlinQ, bs_List, d_Integer] := Module[
  { tsr, dst, mat, new },
  tsr = GelfandZetlinPatterns[First @ tb, d];
  tsr = Tuples @ {tsr, Range[d]};
  
  dst = NextIrreducibleLabels[tb, d];
  mat = matSchurTransform[#, tsr]& /@ dst;
  
  tsr = CircleTimes @@@ Tuples[{bs, Ket /@ Range[d]}];
  
  new = Garner @ Map[(tsr.#)&, mat];
  AssociationThread[dst -> new]
 ]

matSchurTransform[dst_?GelfandZetlinQ, tsr_List] := Module[
  { d = Length[First @ First @ tsr],
    lbl },
  lbl = GelfandZetlinPatterns[First @ dst, d];
  Outer[ClebschGordanX, tsr, lbl, 1]
 ]

NextIrreducibleLabels::usage = "NextIrreducibleLabels[tb, n] returns new Gelfand-Zetlin patterns when one adds a node of n letters to the existing representation specified by Gelfand-Zetlin pattern tb. Each of the resulting Gelfand-Zetlin patterns refers uniquely to an irreducible representation of both U(n) and S(N), where N = Length[tb] + 1."

NextIrreducibleLabels[tb_?GelfandZetlinQ, d_Integer] := Module[
  { L = Length[tb] + 1,
    new },
  new = PadRight[First @ tb, L];
  new = Table[new + UnitVector[L, j], {j, 1, Min @ {d, L}}];
  Map[Prepend[tb, #]&, Select[new, IntegerPartitionQ]]
 ]

(**** </SchurBasis> ****)


End[]

EndPackage[]
