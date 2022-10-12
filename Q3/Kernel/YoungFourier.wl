(* -*- mode:math -*- *)
BeginPackage["Q3`"];

`YoungFourier`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.10 $"][[2]], " (",
  StringSplit["$Date: 2022-10-12 04:37:25+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];


{ YoungFourierBasis, YoungRegularBasis };
{ YoungNormalRepresentation };

Begin["`Private`"]


YoungRegularBasis::usage = "YoungRegularBasis[n] returns the Young regular basis of degree n, i.e., the canonical basis of the left regular representation of the symmetric group of degree n."

YoungRegularBasis[n_Integer] := Ket /@ GroupElements[SymmetricGroup @ n]


YoungFourierBasis::usage = "YoungFourierBasis[n] returns the Young-Fourier basis of degree n, i.e., the Fourier transform over the symmetric group of degree n of the canonical basis of the left regular representation of the same group.\nYoungFourierBasis[shp] returns the Young-Fourier basis in the sector designated by partition shp."

YoungFourierBasis[n_Integer] := Module[
  { shp = IntegerPartitions[n] },
  AssociationThread[shp -> Map[YoungFourierBasis, shp]]
 ]

YoungFourierBasis[shape_?YoungShapeQ] := Module[
  { dim = YoungTableauCount[shape],
    ops = GroupElements @ SymmetricGroup[Total @ shape],
    mat },
  mat = YoungNormalRepresentation[shape] /@ ops;
  mat = Dot[Ket /@ ops, Topple /@ mat] * Sqrt[dim] / Sqrt[Length @ ops] //
    Garner;
  AssociationThread[ Tuples[YoungTableaux[shape], {2}] -> Flatten @ mat ]
 ]


YoungNormalRepresentation::usage = "YoungNormalRepresentation[shape] represents the homomorphism from the group to the matrix representation.\nSee also SpechtBasis."

YoungNormalRepresentation[shape_?YoungShapeQ][op_Cycles] :=
  YoungNormalRepresentation[shape, op]

YoungNormalRepresentation[shape_?YoungShapeQ, op_Cycles] := Module[
  { bs = Ket /@ YoungTableaux[shape] },
  MatrixIn[op, bs]
 ]

End[]

EndPackage[]
