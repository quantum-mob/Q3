(* -*- mode:math -*- *)

BeginPackage["Q3`"]

`QML`$Version = StringJoin[
  "Q3/", $Input, " v",
  StringSplit["$Revision: 1.2 $"][[2]], " (",
  StringSplit["$Date: 2023-07-16 23:20:14+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ BasisEmbedding };

{ AmplitudeEmbedding,
  AmplitudeEmbeddingGate };

Begin["`Private`"]

(**** <BasisEmbedding> ****)

BasisEmbedding::usage = "BasisEmbedding[data, {s1,s2,\[Ellipsis]}] returns computational basis states encoding data."

BasisEmbedding[vv:{__?BinaryQ}, ss:{__?QubitQ}] := 
  Ket[ss -> PadRight[vv, Length @ ss]]

BasisEmbedding[ss:{__?QubitQ}][vv:{__?BinaryQ}] := 
  BasisEmbedding[vv, ss]

(**** </BasisEmbedding> ****)


(**** <AmplitudeEmbedding> ****)

(* SEE: Schuld and Pertruccione (2018), Mottonen et al. (2005) *)

AmplitudeEmbedding::usage = "AmplitudeEmbedding[data, {s1,s2,\[Ellipsis]}] returns a quantum state the amplitudes of which encode data on qubits s1, s2, \[Ellipsis]."

AmplitudeEmbedding[in_?VectorQ, ss:{__?QubitQ}] :=
  Basis[ss] . PadRight[in, Power[2, Length @ ss]]


AmplitudeEmbeddingGate::usage = "AmplitudeEmbedding[data, {s1,s2,\[Ellipsis]}] represents the gate that implement the amplitude embedding of data into a quantum state."

AmplitudeEmbeddingGate::negative = "Some elements of `` is not real non-negative."

(*
AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := (
  Message[AmplitudeEmbeddingGate::negative, in];
  AmplitudeEmbeddingGate[Re @ in, ss]
 ) /; Not @ AllTrue[in, NonNegative]
 *)

AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  AmplitudeEmbeddingGate[in, FlavorNone @ ss] /;
  Not[FlavorNone @ ss]


AmplitudeEmbeddingGate /:
Matrix[AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}], rest___] :=
  Dot @@ Matrix[{ExpandAll @ AmplitudeEmbeddingGate[in, ss]}, rest]


AmplitudeEmbeddingGate /:
Elaborate @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  Elaborate @ ExpressionFor[Matrix[AmplitudeEmbeddingGate[in, ss], ss], ss]


AmplitudeEmbeddingGate /:
ExpandAll @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  Apply[Sequence, Expand /@ {Expand @ AmplitudeEmbeddingGate[in, ss]}]


AmplitudeEmbeddingGate /:
Expand @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := Module[
  { yy = theAmplitudeEmbeddingY[in, Length @ ss],
    op, cc },
  cc = Table[Drop[ss, -k], {k, Length @ ss}];
  yy = MapIndexed[Rotation[#1, ss[[-First @ #2]][2]]&, yy, {2}];
  Sequence @@ Reverse @ Flatten @
    MapThread[UniformlyControlledGate, {cc, yy}]
 ] /; AllTrue[in, NonNegative]

AmplitudeEmbeddingGate /:
Expand @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := Module[
  { yy = theAmplitudeEmbeddingY[in, Length @ ss],
    zz = theAmplitudeEmbeddingZ[in, Length @ ss],
    op, cc },
  cc = Table[Drop[ss, -k], {k, Length @ ss}];
  yy = MapIndexed[Rotation[#1, ss[[-First @ #2]][2]]&, yy, {2}];
  zz = MapIndexed[Rotation[#1, ss[[-First @ #2]][3]]&, zz, {2}];
  Sequence @@ Reverse @ Flatten @ {
    MapThread[UniformlyControlledGate, {cc, zz}],
    MapThread[UniformlyControlledGate, {cc, yy}]
   }
 ]

theAmplitudeEmbeddingY[in_?VectorQ, n_Integer] := Module[
  { dd, nn, ph },
  dd = PadRight[in, Power[2, n]];
  dd = Table[Partition[dd, Power[2, k]], {k, n}];
  nn = Map[Drop[#, Length[#]/2]&, dd, {2}];
  dd = Map[Norm, dd, {2}];
  nn = Map[Norm, nn, {2}];
  2 * ArcSin @ PseudoDivide[nn, dd]
 ]

theAmplitudeEmbeddingZ[in_?VectorQ, n_Integer] := Module[
  { dd, nn, ph },
  dd = Arg @ PadRight[in, Power[2, n]];
  dd = Map[Total, Table[Partition[dd, Power[2, k-1]], {k, n}], {2}];
  dd = Partition[#, 2]& /@ dd;
  -Map[Apply[Subtract], dd, {2}] / Power[2, Range[n]-1]
 ]


AmplitudeEmbeddingGate /:
Multiply[ pre___,
  op:AmplitudeEmbeddingGate[_?VectorQ, {__?QubitQ}, ___?OptionQ],
  in_Ket ] := With[
    { gg = {ExpandAll @ op} },
    Multiply[pre, Fold[Multiply[#2, #1]&, in, gg]]
   ]

Multiply[ pre___,
  op:AmplitudeEmbeddingGate[{__?QubitQ}, _, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
(* NOTE: DO NOT put "AmplitudeEmbeddingGate /:". Otherwise, the above rule with
   AmplitudeEmbeddingGate[...]**Ket[] is overridden. *)


AmplitudeEmbeddingGate /:
ParseGate[
  op:AmplitudeEmbeddingGate[_?VectorQ, {__?QubitQ}, opts___?OptionQ],
  more___?OptionQ ] :=
  Sequence @@ Map[ParseGate[#, opts, more]&, {Expand @ op}]


(**** </AmplitudeEmbedding> ****)


End[]

EndPackage[]
