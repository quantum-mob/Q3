(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2022-09-12 09:21:04+09 $ *)
(* $Revision: 1.6 $ *)

BeginPackage["YoungFourier`", {"Q3`"}]

Unprotect["`*"];
ClearAll["`*"];


{ YoungFourierBasis };
{ YoungNormalRepresentation };

{ toYoungForm };

Begin["`Private`"]


YoungFourierBasis::usage = "YoungFourierBasis[n] ... ."

YoungFourierBasis[n_Integer] := Module[
  { shp = IntegerPartitions[n] },
  AssociationThread[shp -> Map[YoungFourierBasis, shp]]
 ]

YoungFourierBasis[shape_?YoungShapeQ] := Module[
  { dim = YoungTableauCount[shape],
    ops = GroupElements @ SymmetricGroup[Total @ shape],
    mat },
  mat = YoungNormalRepresentation[shape] /@ ops;
  mat = Dot[Ket /@ ops, Topple @ mat] * Sqrt[dim] / Sqrt[Length @ ops] //
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



(*
 * Tools
 *)

toYoungForm[shape_?YoungShapeQ] := YoungDiagram[shape]

toYoungForm[yy : {_?YoungTableauQ, _?YoungTableauQ}] := YoungForm /@ yy

toYoungForm[aa : Association[(_?YoungShapeQ -> _Association) ..]] := 
  KeyMap[YoungDiagram] @ Map[toYoungForm] @ aa

toYoungForm[aa : Association[({__?YoungTableauQ} -> _) ..]] := 
  KeyMap[Map @ YoungForm] @ aa


End[]

SetAttributes[Evaluate @ Protect["`*"], ReadProtected];

EndPackage[]
