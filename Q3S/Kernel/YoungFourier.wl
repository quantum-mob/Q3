(* ::Package:: *)

BeginPackage["QuantumMob`Q3S`", {"System`"}]

{ YoungFourierMatrix, YoungFourier };
{ YoungFourierBasis, YoungRegularBasis };
{ YoungNormalRepresentation };

{ YoungClebschGordanTransform,
  YoungClebschGordan };
{ HarrowClebschGordanTransform };

Begin["`Private`"]

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

YoungNormalRepresentation::usage = "YoungNormalRepresentation[shape] represents the homomorphism from the group to the matrix representation.\nSee also SpechtBasis."

YoungNormalRepresentation[shape_YoungShape][op_Cycles] :=
  YoungNormalRepresentation[shape, op]

YoungNormalRepresentation[shape_YoungShape, op_Cycles] := Module[
  { bs = Ket /@ List /@ YoungTableaux[shape] },
  MatrixIn[op, bs]
 ]

(**** </YoungNormalRepresentation> ****)


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
