(* -*- mode:math -*- *)

BeginPackage["Q3`"]

`QML`$Version = StringJoin[
  "Q3/", $Input, " v",
  StringSplit["$Revision: 1.8 $"][[2]], " (",
  StringSplit["$Date: 2023-07-22 21:28:17+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ BasisEmbedding,
  BasisEmbeddingGate };

{ AmplitudeEmbedding,
  AmplitudeEmbeddingGate };

Begin["`Private`"]

(**** <BasisEmbedding> ****)

BasisEmbedding::usage = "BasisEmbedding[data, {s1,s2,\[Ellipsis]}] returns computational basis states encoding data."

BasisEmbedding[vv:{__?BinaryQ}, ss:{__?QubitQ}] := 
  Ket[ss -> PadRight[vv, Length @ ss]]

BasisEmbedding[ss:{__?QubitQ}][vv:{__?BinaryQ}] := 
  BasisEmbedding[vv, ss]


BasisEmbeddingGate::usage = "BasisEmbeddingGate[data, {s1,s2,\[Ellipsis]}] represents the gate sequence implementing the basis embedding of data."

BasisEmbeddingGate::len = "The lengths of `` and `` must be the same."

BasisEmbeddingGate[vv:{__?BinaryQ}, ss:{__?QubitQ}] :=
  BasisEmbeddingGate[vv, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]

BasisEmbeddingGate[vv:{__?BinaryQ}, ss:{__?QubitQ}] := (
  Message[BasisEmbeddingGate::len, vv, ss];
  BasisEmbeddingGate[PadRight[vv, Length @ ss], ss]
 ) /; Length[vv] != Length[ss]

BasisEmbeddingGate[vv:{__?BinaryQ}, ss:{__?QubitQ}] :=
  Multiply @@ MapThrough[ss, vv]
    
(**** </BasisEmbedding> ****)


(**** <AmplitudeEmbedding> ****)

(* SEE: Schuld and Pertruccione (2018), Mottonen et al. (2005) *)

AmplitudeEmbedding::usage = "AmplitudeEmbedding[data, {s1,s2,\[Ellipsis]}] returns a quantum state the amplitudes of which encode data on qubits s1, s2, \[Ellipsis]."

AmplitudeEmbedding[in_?VectorQ, ss:{__?QubitQ}] :=
  Basis[ss] . PadRight[in, Power[2, Length @ ss]]


AmplitudeEmbeddingGate::usage = "AmplitudeEmbedding[data, {s1,s2,\[Ellipsis]}] represents the gate that implement the amplitude embedding of data into a quantum state."

AmplitudeEmbeddingGate::negative = "Some elements of `` is not real non-negative."

AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  AmplitudeEmbeddingGate[in, FlavorNone @ ss] /;
  Not[FlavorNoneQ @ ss]


AmplitudeEmbeddingGate /:
Matrix[AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}], rest___] :=
  Dot @@ Matrix[{ExpandAll @ AmplitudeEmbeddingGate[in, ss]}, rest]


AmplitudeEmbeddingGate /:
Elaborate @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  Elaborate @ ExpressionFor[Matrix[AmplitudeEmbeddingGate[in, ss], ss], ss]


AmplitudeEmbeddingGate /:
ExpandAll @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  Apply[QuantumCircuit, Expand @ Expand @ AmplitudeEmbeddingGate[in, ss]]


AmplitudeEmbeddingGate /:
Expand @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := Module[
  { yy = theAmplitudeEmbeddingY[in, Length @ ss],
    op, cc },
  cc = Table[Drop[ss, -k], {k, Length @ ss}];
  QuantumCircuit @@ Reverse @ Flatten @ MapThread[
    UniformlyControlledRotation,
    { cc, yy, Through[Reverse[ss][2]] }
   ]
 ] /; AllTrue[in, NonNegative]

AmplitudeEmbeddingGate /:
Expand @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := Module[
  { yy = theAmplitudeEmbeddingY[in, Length @ ss],
    zz = theAmplitudeEmbeddingZ[in, Length @ ss],
    op, cc },
  cc = Table[Drop[ss, -k], {k, Length @ ss}];
  QuantumCircuit @@ Reverse @ Flatten @ {
    MapThread[UniformlyControlledRotation, {cc, zz, Through[Reverse[ss][3]]}],
    MapThread[UniformlyControlledRotation, {cc, yy, Through[Reverse[ss][2]]}]
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
  AmplitudeEmbeddingGate[_?VectorQ, ss:{__?QubitQ}, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ss, "TargetShape" -> "CircleDot", opts, more]


(**** </AmplitudeEmbedding> ****)


End[]

EndPackage[]
