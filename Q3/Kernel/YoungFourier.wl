(* ::Package:: *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ YoungOGS, YoungOGSn,
  FromYoungOGS };

{ YoungDualOGS, YoungDualOGSn,
  FromYoungDualOGS };

{ YoungFourierMatrix, YoungFourier };
{ YoungFourierBasis, YoungRegularBasis };
{ YoungNormalRepresentation,
  YoungRegularRepresentation };

{ LeftRegularRepresentation,
  RightRegularRepresentation };

{ YoungClebschGordanTransform,
  YoungClebschGordan };
{ HarrowClebschGordanTransform };

Begin["`Private`"]

(**** <YoungOGS> ****)
(* See also Kawano16a and Shwartz19a *)

YoungOGS::usage = "YoungOGS[perm] returns the standard ordered generating system (OGS) canonical form of the symmetric group."

YoungOGS[Cycles[{}]] = {0}

YoungOGS[prm_Cycles] :=
  theYoungOGS @ PermutationList[prm]

YoungOGS[prm_Cycles, n_Integer] :=
  theYoungOGS @ PermutationList[prm, n]

YoungOGS[prm_?PermutationListQ] :=
  theYoungOGS[prm]

YoungOGS[prm_?PermutationListQ, n_Integer] := 
  theYoungOGS @ PermutationList[prm, n]


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


YoungOGSn::usage = "YoungOGSn[prm] converts to an integer the standard OGS canonical form corresponding to permutation prm."

YoungOGSn[args__] := Module[
  { ogs = YoungOGS[args],
    fac, n },
  n = 1 + Length[ogs];
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

YoungDualOGS::usage = "YoungDualOGS[perm] returns the dual-standard ordered generating system (OGS) canonical form of the symmetric group."

YoungDualOGS[Cycles[{}]] = {0}

YoungDualOGS[prm_Cycles] :=
  theYoungDualOGS @ PermutationList[prm]

YoungDualOGS[prm_Cycles, n_Integer] :=
  theYoungDualOGS @ PermutationList[prm, n]

YoungDualOGS[prm_?PermutationListQ] :=
  theYoungDualOGS[prm]

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

YoungDualOGSn[args__] := Module[
  { ogs = YoungDualOGS[args],
    fac, n },
  n = 1 + Length[ogs];
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


YoungFourierMatrix::usage = "YoungFourieMatrix[n] returns the matrix describing the Fourier transform over the symmetric group of degree n."

YoungFourierMatrix[n_Integer] := Module[
  { shp = YoungShapes[n],
    elm = GroupElements[SymmetricGroup @ n] },
  Map[ Flatten,
    Outer[
      (Sqrt[YoungTableauCount[#2]] *
          Topple[YoungNormalRepresentation[#2, #1]])&,
      elm, shp, 1 ] / Sqrt[Length @ elm]
  ]
]


(**** <YoungFourierBasis> ****)

YoungFourierBasis::usage = "YoungFourierBasis[n] returns the Young-Fourier basis of degree n, i.e., the Fourier transform over the symmetric group of degree n of the canonical basis of the left regular representation of the same group."

YoungFourierBasis[n_Integer] := Module[
  { mat = YoungFourierMatrix[n],
    key, val },
  key = Ket /@ Flatten[
    Map[Tuples[YoungTableaux @ #, 2]&, YoungShapes @ n],
    1 ];
  val = Ket /@ List /@ GroupElements[SymmetricGroup @ n];
  AssociationThread[key -> val . mat]
]

(**** </YoungFourierBasis> ****)


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


(**** <YoungNormalRepresentation> ****)

YoungNormalRepresentation::usage = "YoungNormalRepresentation[shape] represents the homomorphism from the symmetric group to the matrix representation.\nSee also SpechtBasis."

YoungNormalRepresentation[shape_YoungShape][op_Cycles] :=
  YoungNormalRepresentation[shape, op]

YoungNormalRepresentation[shape_YoungShape, op_Cycles] := Module[
  { bs = Ket /@ List /@ YoungTableaux[shape] },
  MatrixIn[op, bs]
]

(**** </YoungNormalRepresentation> ****)


(**** <YoungRegularRepresentation> ****)

YoungRegularRepresentation::usage = "YoungRegularRepresentation[n] represents the left regular representation of the symmetric group of degree n."

YoungRegularRepresentation[n_Integer] :=
  YoungRegularRepresentation[SymmetricGroup @ n]

YoungRegularRepresentation[grp_SymmetricGroup][cyc_Cycles] := 
  LeftRegularRepresentation[grp][cyc]

(**** </YoungRegularRepresentation> ****)


(**** <LeftRegularRepresentation> ****)

LeftRegularRepresentation::usage = "LeftRegularRepresentation[group, g] returns the left regular representation of element g of group.\n LeftRegularRepresentation[group, {g1,g2,\[Ellipsis],gn}] returns the list of the left regular representations of elements g1, g2, \[Ellipsis], gn."

LeftRegularRepresentation::gmt = "Group `` is not supported."

LeftRegularRepresentation[grp_][elm_] :=
  LeftRegularRepresentation[grp, elm]

LeftRegularRepresentation[grp_, elm_] := Module[
  { gmt = GroupMultiplicationTable[grp],
    k },
  If[ MatrixQ[gmt],
    gmt = Transpose[gmt], (* due to Mathematica's convention *)
    Message[LeftRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  k = GroupElementPosition[grp, elm];
  If[ ListQ[elm],
    Map[Transpose[PermutationMatrix[#, TargetStructure -> "Sparse"]]&, gmt[[k]]],
    Transpose @ PermutationMatrix[gmt[[k]], TargetStructure -> "Sparse"]
  ]
]

(**** </LeftRegularRepresentation> ****)


(**** <RightRegularRepresentation> ****)

RightRegularRepresentation::usage = "RightRegularRepresentation[group, g] returns the right regular representation of element g of group.\n RightRegularRepresentation[group, {g1,g2,\[Ellipsis],gn}] returns the list of the right regular representations of elements g1, g2, \[Ellipsis], gn."

RightRegularRepresentation::gmt = "Group `` is not supported."

RightRegularRepresentation[grp_][elm_] :=
  RightRegularRepresentation[grp, elm]

RightRegularRepresentation[grp_, elm_] := Module[
  { gmt = GroupMultiplicationTable[grp],
    k },
  If[ Not[MatrixQ @ gmt],
    Message[RightRegularRepresentation::gmt, grp];
    Return[$Failed]
  ];
  k = GroupElementPosition[grp, elm];
  If[ ListQ[elm],
    Map[PermutationMatrix[#, TargetStructure -> "Sparse"]&, gmt[[k]]],
    PermutationMatrix[gmt[[k]], TargetStructure -> "Sparse"]
  ]
]

(**** </LeftRegularRepresentation> ****)


(**** <YoungFourier> ****)

YoungFourier::usage = "YoungFourier[n] represents the Fourier transform over the symmetric group of degree n.\nYoungFourier[n][Ket[op]] returns the Fourier transform of Ket[op] over the symmetric group.\nYoungFourier[Ket[{y1,y2}]] returns the Fourier transform of Ket[{y1,y2}] over the symmetric group."

YoungFourier[n_Integer][expr_Plus] := Garner @ Map[YoungFourier[n], expr]

YoungFourier[n_Integer][z_?CommutativeQ expr_] :=
  z * YoungFourier[n][expr]

YoungFourier /:
Multiply[pre___, op:YoungFourier[_Integer], v:Ket[{_Cycles}], post___] :=
  Multiply[pre, op[v], post]

YoungFourier[n_Integer][Ket[{op_Cycles}]] := With[
  { shp = YoungShapes[n] },
  Garner[
    Total @ Map[theYoungFourier[#, op]&, shp] /
      Sqrt[GroupOrder @ SymmetricGroup @ n]
  ]
]

theYoungFourier[shape_YoungShape, op_Cycles] :=
  Sqrt[YoungTableauCount @ shape] *
  Map[Ket, Tuples[YoungTableaux[shape], 2]] .
  Flatten[Transpose @ YoungNormalRepresentation[shape, op]]


YoungFourier /:
Multiply[ pre___,
  op:YoungFourier[_Integer],
  v:Ket[{_?YoungTableauQ, _?YoungTableauQ}], post___ ] :=
  Multiply[pre, op[v], post]

(* Here, n is not necessary but kept for consistency. *)
YoungFourier[n_Integer][Ket[{ya_YoungTableau, yb_YoungTableau}]] :=
  Module[
    { ops = GroupElements @ SymmetricGroup[n],
      shp = YoungShape[ya],
      mat, pos, tbl },
    tbl = YoungTableaux[shp];
    pos = {First @ FirstPosition[tbl, yb], First @ FirstPosition[tbl, ya]};
    mat = YoungNormalRepresentation[shp] /@ ops;
    mat = Map[Part[#, Sequence @@ pos]&, mat];
    Garner[
      Map[Ket @* List, ops] . mat *
        Sqrt[YoungTableauCount @ shp] /
        Sqrt[GroupOrder @ SymmetricGroup @ n]
    ]
  ]

(**** </YoungFourier> ****)


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
