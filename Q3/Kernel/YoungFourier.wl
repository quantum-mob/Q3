(* -*- mode:math -*- *)
BeginPackage["Q3`"];

`YoungFourier`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.14 $"][[2]], " (",
  StringSplit["$Date: 2023-03-25 17:03:30+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];


{ YoungFourierMatrix, YoungFourier };
{ YoungFourierBasis, YoungRegularBasis };
{ YoungNormalRepresentation };

Begin["`Private`"]

YoungRegularBasis::usage = "YoungRegularBasis[n] returns the Young regular basis of degree n, i.e., the canonical basis of the left regular representation of the symmetric group of degree n."

YoungRegularBasis[n_Integer] := Ket /@ GroupElements[SymmetricGroup @ n]


YoungFourierMatrix::usage = "YoungFourieMatrix[n] returns the matrix describing the Fourier transform over the symmetric group of degree n."

YoungFourierMatrix[n_Integer] := Module[
  { shp = IntegerPartitions[n],
    elm = GroupElements[SymmetricGroup @ n] },
  Map[ Flatten,
    Outer[
      (Sqrt[YoungTableauCount[#2]] *
          Topple[YoungNormalRepresentation[#2, #1]])&,
      elm, shp, 1 ] / Sqrt[Length @ elm]
   ]
 ]


YoungFourierBasis::usage = "YoungFourierBasis[n] returns the Young-Fourier basis of degree n, i.e., the Fourier transform over the symmetric group of degree n of the canonical basis of the left regular representation of the same group."

YoungFourierBasis[n_Integer] := Module[
  { mat = YoungFourierMatrix[n],
    key },
  key = Flatten[
    Map[Tuples[YoungTableaux @ #, 2]&, IntegerPartitions @ n],
    1 ];
  AssociationThread[key -> YoungRegularBasis[n] . mat]
 ]


YoungNormalRepresentation::usage = "YoungNormalRepresentation[shape] represents the homomorphism from the group to the matrix representation.\nSee also SpechtBasis."

YoungNormalRepresentation[shape_?YoungShapeQ][op_Cycles] :=
  YoungNormalRepresentation[shape, op]

YoungNormalRepresentation[shape_?YoungShapeQ, op_Cycles] := Module[
  { bs = Ket /@ YoungTableaux[shape] },
  MatrixIn[op, bs]
 ]


(**** <YoungFourier> ****)

YoungFourier::usage = "YoungFourier[n] represents the Fourier transform over the symmetric group of degree n.\nYoungFourier[n][Ket[op]] returns the Fourier transform of Ket[op] over the symmetric group.\nYoungFourier[Ket[{y1,y2}]] returns the Fourier transform of Ket[{y1,y2}] over the symmetric group."

YoungFourier[n_Integer][expr_Plus] := Garner @ Map[YoungFourier[n], expr]

YoungFourier[n_Integer][z_?CommutativeQ expr_] :=
  z * YoungFourier[n][expr]

YoungFourier /:
Multiply[pre___, op:YoungFourier[_Integer], v:Ket[_Cycles], post___] :=
  Multiply[pre, op[v], post]

YoungFourier[n_Integer][Ket[op_Cycles]] := With[
  { shp = IntegerPartitions[n] },
  Garner[
    Total @ Map[theYoungFourier[#, op]&, shp] /
      Sqrt[GroupOrder @ SymmetricGroup @ n]
   ]
 ]

theYoungFourier[shape_?YoungShapeQ, op_Cycles] :=
  Sqrt[YoungTableauCount @ shape] *
  Map[Ket, Tuples[YoungTableaux[shape], 2]] .
  Flatten[Transpose @ YoungNormalRepresentation[shape, op]]


YoungFourier /:
Multiply[ pre___,
  op:YoungFourier[_Integer],
  v:Ket[{_?YoungTableauQ, _?YoungTableauQ}], post___ ] :=
  Multiply[pre, op[v], post]

(* Here, n is not necessary but kept for consistency. *)
YoungFourier[n_Integer][Ket[{ya_?YoungTableauQ, yb_?YoungTableauQ}]] :=
  Module[
    { ops = GroupElements @ SymmetricGroup[n],
      shp = YoungShape[ya],
      mat, pos, tbl },
    tbl = YoungTableaux[shp];
    pos = {First @ FirstPosition[tbl, yb], First @ FirstPosition[tbl, ya]};
    mat = YoungNormalRepresentation[shp] /@ ops;
    mat = Map[Part[#, Sequence @@ pos]&, mat];
    Garner[
      Map[Ket, ops] . mat *
        Sqrt[YoungTableauCount @ shp] /
        Sqrt[GroupOrder @ SymmetricGroup @ n]
     ]
   ]


Format[vec:Ket[{_?YoungTableauQ, _?YoungTableauQ}..]] :=
  Map[YoungForm, vec, {2}]

(**** </YoungFourier> ****)


End[]

EndPackage[]
