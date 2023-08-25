(* -*- mode: math; -*- *)

BeginPackage["Q3`"]

`QuantumCircuit`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 3.53 $"][[2]], " (",
  StringSplit["$Date: 2023-08-24 16:28:11+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ QuantumCircuit,
  QuantumCircuitIn,
  QuantumCircuitOut,
  QuantumCircuitTrim };

{ ParseGate, Gate, Mark };

{ ParsePort, Port };

Begin["`Private`"]

QuantumCircuit::usage = "QuantumCircuit[a, b, ...] represents the quantum circuit model consisting of the gate operations a, b, ..., and it is displayed the circuit in a graphical form.\nExpressionFor[ QuantumCircuit[...] ] takes the non-commutative product of the elements in the quantum circuit; namely, converts the quantum circuit to a operator or vector expression.\nMatrix[ QuantumCircuit[...] ] returns the matrix representation of the quantum circuit model."

QuantumCircuit::noqubit = "No Qubit found in the expression ``. Use KetRegulate to specify the Qubits explicitly."

QuantumCircuit::nofunc = "Unknown function \"``\" to draw the gate. \"Rectangle\" is assumed."

QuantumCircuit::ket = "`` is not a proper ket of the form Ket[<|...|>] or ProductState[<|...|>]."

QuantumCircuit::elm = "`` is not a quantum circuit element."


QuantumCircuitIn::usage = "QuantumCircuitIn is a holder for input expression in QuantumCircuit.\nSee also QuantumCircuitOut."

QuantumCircuitOut::usage = "QuantumCircuitOut is a holder for expected output expressions in QuantumCircuit. Note that the output expressions are just expected output and may be different from the actual output. They are used only for output label and ignored by ExpressionFor and Elaborate.\nSee also QuantumCircuitIn."

SetAttributes[{QuantumCircuit, QuantumCircuitOut, QuantumCircuitIn}, Flat]

AddElaborationPatterns[_QuantumCircuit]

Options[QuantumCircuit] = {
  "UnitLength" -> 36, (* 72 is a good choice for presentation *)
  "Visible" -> None,
  "Invisible" -> None,
  "PortSize" -> 0.65
 }

$CircuitSize = 1

$CircuitUnit = 1

$GateSize := 0.8 $CircuitUnit

$DotSize := 0.09 $CircuitUnit

$InOutOffset := 0.1 $CircuitUnit

$BraceWidth := 0.125 $CircuitUnit


Format[ qc:QuantumCircuit[__, opts___?OptionQ] ] :=
  Interpretation[Graphics @ qc, qc]


QuantumCircuit /:
Qubits @ QuantumCircuit[gg__, opts_?OptionsQ] := Union[
  Qubits @ {gg},
  FlavorNone @ q3AssureList @ OptionValue[QuantumCircuit, opts, "Visible"]
 ]

QuantumCircuit /:
Measurements[qc:QuantumCircuit[__, ___?OptionQ]] :=
  Measurements[QuantumCircuitTrim @ qc]

QuantumCircuit /:
Expand @ QuantumCircuit[gg__, opts___?OptionQ] :=
  QuantumCircuit[Sequence @@ Map[Expand, {gg}], opts]

QuantumCircuit /:
ExpandAll @ QuantumCircuit[gg__, opts___?OptionQ] :=
  QuantumCircuit[Sequence @@ Map[ExpandAll, {gg}], opts]

QuantumCircuit /:
GateFactor @ QuantumCircuit[gg__, opts___?OptionQ] :=
  QuantumCircuit[Sequence @@ Map[GateFactor, {gg}], opts]


(**** <Multiply> ****)

QuantumCircuit /:
NonCommutativeQ[_QuantumCircuit] = True

QuantumCircuit /:
MultiplyKind[_QuantumCircuit] = Qubit

QuantumCircuit /:
MultiplyGenus[_QuantumCircuit] := "Singleton"


QuantumCircuit /:
Dagger @ QuantumCircuit[gg__, opts___?OptionQ] :=
  QuantumCircuit[Sequence @@ Map[Dagger, Reverse @ {gg}], opts]


QuantumCircuit /:
Multiply[pre___, QuantumCircuit[elm__], post___] :=
  Multiply[pre, Elaborate @ QuantumCircuit[Reverse @ {post}, elm]]
(* NOTE: {elm} may include Measurement. *)

QuantumCircuit /:
Multiply[pre___, Longest[cc__QuantumCircuit], post___] :=
  Multiply[pre, Elaborate @ Apply[QuantumCircuit, Reverse @ {cc}], post]

(**** </Multiply> ****)


(**** <Elaborate> ****)

QuantumCircuit /:
ExpressionFor[ qc_QuantumCircuit ] := Elaborate[ qc ]

QuantumCircuit /:
Elaborate @ QuantumCircuit[gg__, ___?OptionQ] := Module[
  { expr = Flatten @ QuantumCircuitTrim @ {gg} },
  Garner[ qvCircuitOperate @@ expr ]
 ]
(* NOTE: This makes the evaluation much faster, especially, when the initial
   state is specified in the circuit. *)


qvCircuitOperate[] = 1

qvCircuitOperate[pre__, op_Measurement, post___] := 
  qvCircuitOperate[op @ qvCircuitOperate[pre], post] /;
  Not @ FreeQ[Elaborate @ {pre}, Ket[_Association]]

qvCircuitOperate[op_Measurement, post___] :=
  Multiply[qvCircuitOperate[post], op]

qvCircuitOperate[op:Except[_Measurement]..] :=
  Elaborate @ Fold[ Garner[Multiply[#2, #1]]&, 1, {op} ]
(* NOtE: This is another method:
   Fold[ Garner[Multiply[#2, #1]]&, 1,  Elaborate @ {op} ]
   However, this cannot take the advantange of op ** Ket[...]. *)

qvCircuitOperate[gg__] := MeasurementFunction[{gg}]

(**** </Elaborate> ****)


(**** <Matrix> ****)

QuantumCircuit /:
Matrix[qc_QuantumCircuit] := Matrix[qc, Qubits @ qc]

QuantumCircuit /:
Matrix[qc:QuantumCircuit[gg__, ___?OptionQ], ss:{___?QubitQ}] := Module[
  { ff },
  ff = SplitBy[
    Flatten @ QuantumCircuitTrim @ {gg},
    MatchQ[_Measurement]
   ];
  Apply[qcMatrix, MapApply[Dot, Reverse /@ Matrix[ff, ss]]]
 ]

qcMatrix[v_?VectorQ] = v

qcMatrix[m_?MatrixQ] = m

qcMatrix[m_Measurement] = m

qcMatrix[v_?VectorQ, msr_Measurement, rest___] :=
  qcMatrix[msr @ v, rest]

qcMatrix[v_?VectorQ, mat_?MatrixQ, rest___] :=
  qcMatrix[mat.v, rest]

qcMatrix[gg__] := MeasurementFunction[{gg}]

(**** </Matrix> ****)


(**** <QuantumCircuitTrim> ****)

QuantumCircuitTrim::usage = "QuantumCircuitTrim[expr] removes visualization options and Graphics Directives that are not evaluable expressions. Useful to convert QuantumCircuit to an evaluation-ready expression."

SetAttributes[ QuantumCircuitTrim, Listable ];

QuantumCircuitTrim[ HoldPattern @ QuantumCircuit[gg__, ___?OptionQ] ] :=
  Flatten @ QuantumCircuitTrim @ {gg}

QuantumCircuitTrim[ QuantumCircuitIn[a__] ] :=
    Multiply @@ QuantumCircuitTrim[ {a} ]
(* NOTE: Useful to apply Matrix directly to QuantumCircuit.  *)

QuantumCircuitTrim[ _QuantumCircuitOut ] = Nothing

QuantumCircuitTrim[ _?OptionQ ] = Nothing

QuantumCircuitTrim[ g_?ComplexQ ] = g (* NOT _?CommutativeQ *)

QuantumCircuitTrim[ g_ ] := Nothing /;
  FreeQ[g, _?QubitQ | _Dyad | _Ket | _ProductState]

QuantumCircuitTrim[ HoldPattern @ Projector[v_, qq_, ___?OptionQ] ] :=
  Dyad[v, v, qq]

QuantumCircuitTrim[ v:ProductState[_Association, ___] ] := Expand[v]

QuantumCircuitTrim[ v:Ket[_Association] ] = v

QuantumCircuitTrim[ op_QFT ] := op

QuantumCircuitTrim[ Gate[expr_, ___?OptionQ] ] := expr

QuantumCircuitTrim[ op_Symbol[expr__, ___?OptionQ] ] := op[expr]

QuantumCircuitTrim[ g_ ] := g

(**** </QuantumCircuitTrim> ****)


(**** <User Interface for QuantumCircuit> ****)

(* NOTE: QuantumCircuit has attribute Flat. *)

QuantumCircuit[rest:Except[_?qcKetQ].., Longest[vv__?qcKetQ]] :=
  QuantumCircuit[rest, QuantumCircuitOut[vv]]

QuantumCircuit[Longest[vv__?qcKetQ]] :=
  QuantumCircuit @ QuantumCircuitIn[vv]

QuantumCircuit[Longest[opts__?OptionQ], rest:Except[_?OptionQ]..] :=
  QuantumCircuit[rest, opts]

QuantumCircuit[a_QuantumCircuitOut, bb__QuantumCircuitOut] :=
  QuantumCircuit @ QuantumCircuitOut[a, bb]

QuantumCircuit[a_QuantumCircuitIn, bb__QuantumCircuitIn] :=
  QuantumCircuit @ QuantumCircuitIn[a, bb]

QuantumCircuit[rest__, in_QuantumCircuitIn] :=
  QuantumCircuit[in, rest]

QuantumCircuit[out_QuantumCircuitOut, rest:Except[_?OptionQ|_QuantumCircuitOut]..] :=
  QuantumCircuit[rest, out]

qcKetQ[expr_] := And[
  FreeQ[expr, _QuantumCircuitIn | _QuantumCircuitOut | _Projector],
  Not @ FreeQ[expr, _Ket | _ProductState]
 ]

(* See also GraphState[] *)
QuantumCircuit[g_Graph] := Module[
  { qubits = VertexList[g],
    links  = EdgeList[g] },
  links = links /. { UndirectedEdge -> CZ, DirectedEdge -> CZ };
  QuantumCircuit[Through[qubits[6]], Sequence @@ links]
  /; AllTrue[ qubits, QubitQ ]
 ]

(**** <User Interface for QuantumCircuit> ****)


(*
 * Graphical display of circuit
 *)

QuantumCircuit /:
HoldPattern @
  Graphics[ QuantumCircuit[gg__, opts___?OptionQ], more___?OptionQ ] :=
  Module[
    { ss = Qubits @ {gg},
      cc = ParseGate @ {gg},
      vv, ww, xx, yy, in, out, unit, port, nodes, marks, lines },

    {vv, ww, unit, port} =
      {"Visible", "Invisible", "UnitLength", "PortSize"} /.
      Flatten[{opts}] /. Options[QuantumCircuit];
    (* NOTE: Here, Flatten is required since OptionQ[{}] returns True and in
       such a case, {...} /. {} /. {...} returns {{...}} instead of {...}. *)

    port = q3AssureList[port, 2];

    vv = FlavorNone @ Flatten @ q3AssureList @ vv;
    ww = FlavorNone @ Flatten @ q3AssureList @ ww;
    ss = Union @ Flatten @ {ss, vv, ww};

    If[cc == {}, cc = {"Spacer"}];
    (* There can be only input elements. *)
    
    xx  = 1 + Accumulate[Prepend[Map[qcDepth, cc], 0]];
    xx *= $CircuitUnit;
    $CircuitSize = Last[xx];
    
    yy = Range[Length @ ss] $CircuitUnit;
    yy = AssociationThread[ss, -yy];

    nodes = qcNodes[cc, Most @ xx, yy];
    lines = qcLines[cc, xx, KeyDrop[yy, ww]];

    marks = qcMark @ Cases[{gg}, _Mark, Infinity];

    in = FirstCase[ {gg}, QuantumCircuitIn[kk___] :> {kk} ];
    in = qCircuitInput[in, xx, yy];

    out = FirstCase[ {gg}, QuantumCircuitOut[kk___] :> {kk} ];
    out = qCircuitOutput[out, xx, yy];

    Graphics[ Join[lines, in, nodes, marks, out],
      Sequence @@ FilterRules[{opts}, Options @ Graphics],
      more,
      PlotRange -> {Full, MinMax[yy] + {-1, 1}*$CircuitUnit/2},
      ImagePadding -> { unit*port, {1, 1} },
      ImageSize -> unit * ($CircuitSize + Total[port])
     ]
   ]


qcDepth::usage = "qcDepth[expr] returns the depth of quantum circuit element expr."

qcDepth[qc_QuantumCircuit] := Total @ Map[qcDepth, List @@ qc]

qcDepth[gg_List] := Max @ Map[qcDepth, gg]

qcDepth[any_] := Boole @ Not @ FreeQ[any, _?QubitQ | "Separator" | "Spacer" ]


(**** <ParseGate> *****)

Gate::usage = "Gate[{s1,s2,\[Ellipsis]}, opts] represents a low-level quantum circuit element operating on qubits {s1,s2,\[Ellipsis]}.\nGate[{c1,c2,\[Ellipsis]}\[RightArrow]{v1,v2,\[Ellipsis]}, {t1,t2,\[Ellipsis]}, opts] represents a low-level quantum circuit element operating on target qubits {t1,t2,\[Ellipsis]} conditioned on control qubits {c1,c2,\[Ellipsis]} having values {v1,v2,\[Ellipsis]}."

Options[Gate] = {
  "LinkShape" -> "Default",
  "LinkLabel" -> None,
  "TargetShape" -> "Rectangle",
  "ControlShape" -> "Dot",
  "Label" -> None,
  "LabelSize" -> 1, (* RELATIVE size *)
  "LabelStyle" -> {},
  (* A list of options to Style; e.g., "LabelStyle" -> {FontSland -> Plain} *)
  "LabelAngle" -> 0,
  "LabelOffset" -> {0, 0}, (* See Text for details. *)
  N -> False (* only for QFT *)
 }

Gate[ss:{__?QubitQ}, opts:OptionsPattern[]] :=
  Gate[FlavorNone @ ss, opts] /; Not[FlavorNoneQ @ ss]

Gate[cc:{__?QubitQ}, tt:{__?QubitQ}, opts:OptionsPattern[]] :=
  Gate[Thread[cc -> 1], tt, opts]

Gate[Rule[cc:{__?QubitQ}, v_], tt:{__?QubitQ}, opts:OptionsPattern[]] :=
  Gate[Thread[cc -> v], tt, opts]

Gate[cc:{Rule[_?QubitQ, _]..}, tt:{__?QubitQ}, opts:OptionsPattern[]] :=
  Gate[FlavorNone @ cc, FlavorNone @ tt, opts] /;
  Not @ FlavorNoneQ @ Join[Keys @ cc, tt]

ParseGate::usage = "ParseGate[expr, opts] is a low-level function to preprocess quantum circuit element expr."

ParseGate::unknown = "Unknown quantum circuit element ``."

(* NOTE: NEVER set Listable attribute for ParseGate. *)
ParseGate[{gg__, opts___?OptionQ}] := Map[ParseGate[#, opts]&, {gg}]

ParseGate[gg_List, opts___?OptionQ] := Map[ParseGate[#, opts]&, gg]


(* These elements are handled separately. *)
ParseGate[_QuantumCircuitIn|_QuantumCircuitOut|_Mark, opts___?OptionQ] = Nothing


ParseGate[qc_QuantumCircuit] := Map[ParseGate, qc]
  

ParseGate[Gate[some__], more___?OptionQ] := Gate[some, more]

ParseGate[op_?QubitQ, opts___?OptionQ] :=
  Gate[ Qubits @ op, opts, "Label" -> HoldForm[thePauliForm @ op] ]
(* NOTE: HoldForm is required here because later qcNodes uses ReleaseHold. *)

(* NOTE: This case should never occur. *)
(*
ParseGate[ HoldPattern @ Dagger[S_?QubitQ], opts___?OptionQ ] :=
  Gate[ Qubits @ S, opts, "Label" -> HoldForm @ thePauliForm[Dagger @ S] ]
 *)

ParseGate[HoldPattern @ Multiply[ss__?QubitQ], opts___?OptionQ] :=
  Map[ParseGate[#, opts]&, Reverse @ {ss}]

ParseGate[Measurement[ss:{__?PauliQ}], opts___?OptionQ] :=
  Map[ParseGate[Measurement[#], opts]&, ss]

ParseGate[Measurement[S_?QubitQ], opts___?OptionQ] := Gate[
  {FlavorMute @ S},
  "TargetShape" -> "Measurement", opts,
  "Label" -> measurementLabel[S]
 ]

ParseGate[
  HoldPattern @ Measurement[Multiply[ss__?QubitQ]], opts___?OptionQ ] :=
  Gate[ FlavorMute @ {ss},
    "TargetShape" -> "Measurement", opts,
    "Label" -> measurementLabel @ {ss} ]

ParseGate[
  HoldPattern @ Projector[v_, qq_, opts___?OptionQ], more___?OptionQ ] :=
  Gate[ qq, "TargetShape" -> "Projector", "Label" -> None, opts, more ]

ParseGate[
  op:Phase[_, _?QubitQ, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ Qubits @ op, opts, more, "Label" -> HoldForm @ thePauliForm[op] ]


ParseGate[
  op:Rotation[_, {_, _, _}, G_?QubitQ, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[Qubits @ G, opts, more, "Label" -> gateLabel @ op]

ParseGate[
  op:EulerRotation[{_,_,_}, G_?QubitQ, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[{G}, opts, more, "Label" -> gateLabel @ op]


ParseGate[
  ControlledGate[rr:{__Rule}, S_?QubitQ, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ rr, Qubits @ S, opts, more,
    "Label" -> {None, gateLabel[S]} ]

ParseGate[
  ControlledGate[
    cc:{Rule[_?QubitQ, _?BinaryQ]..},
    op:(Phase|Rotation|EulerRotation)[__, opts___?OptionQ],
    more___?OptionQ ],
  rest___?OptionQ ] :=
  Gate[ cc, Qubits @ op, opts, more, rest,
    "Label" -> {None, gateLabel[op]} ]

ParseGate[
  ControlledGate[
    cc:{Rule[_?QubitQ, _?BinaryQ]..},
    HoldPattern @ Multiply[ss__?QubitQ],
    opts___?OptionQ ],
  more___?OptionQ ] := Sequence @@ Map[
    ParseGate[ControlledGate[cc, #], opts, more]&,
    Reverse @ {ss}
   ]

ParseGate[
  ControlledGate[ cc:{Rule[_?QubitQ, _]..}, expr_, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ cc, Qubits[expr], opts, more ] /;
  Not @ FreeQ[expr, _Dyad|_?QubitQ]


ParseGate[ CNOT[cc:{Rule[_?QubitQ, _]..}, tt:{__?QubitQ}], opts___?OptionQ ] :=
  Gate[cc, tt, "TargetShape" -> "CirclePlus"]


ParseGate[ Toffoli[a_?QubitQ, b__?QubitQ, c_?QubitQ], opts___?OptionQ ] :=
  Gate[Thread[{a, b} -> {1, 1}], {c}, "TargetShape" -> "CirclePlus"]


ParseGate[ CZ[c_?QubitQ, t_?QubitQ], ___?OptionQ ] :=
  Gate[{c}, {t}, "ControlShape" -> "Dot", "TargetShape" -> "Dot"]

ParseGate[ Swap[c_?QubitQ, t_?QubitQ], opts___?OptionQ ] :=
  Gate[ {c}, {t},
    "ControlShape" -> "Cross",
    "TargetShape" -> "Cross"
   ]


ParseGate[ InteractionXY[phi_, {a_?QubitQ, b_?QubitQ}], ___?OptionQ ] :=
  Gate[ {a}, {b},
    "ControlShape" -> "Cross",
    "TargetShape" -> "Cross",
    "LinkShape" -> "Wiggly"
   ]

ParseGate[ InteractionZZ[phi_, {a_?QubitQ, b_?QubitQ}], ___?OptionQ ] :=
  Gate[ {a}, {b},
    "ControlShape" -> "Dot",
    "TargetShape" -> "Dot",
    "LinkShape" -> "Wiggly" ]


ParseGate[
  UnitaryInteraction[{0, 0, phi_}, ss:{__?QubitQ}, opts___?OptionQ], ___ ] :=
  Gate[ Most @ ss, {Last @ ss}, opts,
    "ControlShape" -> "Dot",
    "TargetShape" -> "Dot",
    "LinkShape" -> "Wiggly" ]

ParseGate[
  HoldPattern @ UnitaryInteraction[_?VectorQ | _?MatrixQ, ss:{__?QubitQ},
    opts___?OptionQ], ___] :=
  Gate[ Most @ ss, {Last @ ss}, opts,
    "ControlShape" -> "Cross",
    "TargetShape" -> "Cross",
    "LinkShape" -> "Wiggly" ]


ParseGate[ Fredkin[a_?QubitQ, {b_?QubitQ, c_?QubitQ}], opts___?OptionQ ] :=
  Gate[ {a}, {b, c},
    "ControlShape" -> "Dot",
    "TargetShape" -> "Cross"
   ]

ParseGate[
  Deutsch[ph_, {a_?QubitQ, b_?QubitQ, c_?QubitQ}, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ {a, b}, {c}, opts, more, "Label" -> "D" ]


ParseGate[
  Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := ParseGate @ Oracle[f, cc, tt, opts, more]

ParseGate @ Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  Gate[ cc, tt, opts,
    "ControlShape" -> "Oval",
    "TargetShape" -> "CirclePlus",
    "Label" -> "f(x)",
    "LabelSize" -> 0.9 ]


ParseGate[
  ControlledPower[cc:{__?QubitQ}, op_, opts___?OptionQ],
  more__?OptionQ
 ] := ParseGate @ ControlledPower[cc, op, opts, more]

ParseGate @ ControlledPower[cc:{__?QubitQ}, op_, opts___?OptionQ] :=
  Gate[ cc, Qubits[op],
    "Label" -> gateLabel[ControlledPower[cc, op, opts]],
    opts,
    "ControlShape" -> "Oval",
    "TargetShape" -> "Rectangle"
   ]


ParseGate[
  UniformlyControlledRotation[
    cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ cc, {S}, opts, more,
    "ControlShape" -> "MixedDot",
    "Label" -> {None, gateLabel @ Rotation[0, vv, S]}
   ]


ParseGate[
  UniformlyControlledGate[cc:{__?QubitQ}, tt_List, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ cc, Qubits @ tt, more, opts,
    "ControlShape" -> "MixedDot",
    "Label" -> {None, "U"}
   ]


ParseGate[
  ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := ParseGate @ ModMultiply[n, cc, tt, more, opts]

ParseGate @
  ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  Gate[ cc, tt,
    "ControlShape" -> "Oval",
    "TargetShape" -> "Rectangle", opts,
    "Label" -> {"x", StringForm["x\[ThinSpace]y % ``", n]},
    "LabelAngle" -> Pi/2 ]

ParseGate[
  ModMultiply[n_Integer, a_Integer, tt:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := ParseGate @ ModMultiply[n, a, tt, more, opts]

ParseGate @
  ModMultiply[n_Integer, a_Integer, tt:{__?QubitQ}, opts___?OptionQ] :=
  Gate[ tt,
    "TargetShape" -> "Rectangle", opts,
    "Label" -> StringForm["``\[ThinSpace]x % ``", a, n],
    "LabelAngle" -> Pi/2 ]


ParseGate[QFT[qq:{__?QubitQ}, opts___?OptionQ], more__?OptionQ] :=
  ParseGate @ QFT[qq, more, opts]

ParseGate[QFT[qq:{__?QubitQ}, opts___?OptionQ]] :=
  Gate[qq, opts, "Label" -> "QFT", "LabelAngle" -> Pi/2]

ParseGate[
  HoldPattern @ Dagger @ QFT[qq:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := ParseGate @ Dagger @ QFT[qq, opts, more]

ParseGate[HoldPattern @ Dagger @ QFT[qq:{__?QubitQ}, opts___?OptionQ]] :=
  Gate[qq, opts, "Label" -> SuperDagger["QFT"], "LabelAngle" -> Pi/2]


ParseGate[ expr:Except[_List|_?(FreeQ[#,_?QubitQ]&)], opts___?OptionQ ] :=
  Gate[ Qubits @ expr, opts ]

ParseGate[_?NumericQ, ___?OptionQ] = "Spacer"

ParseGate[gate:("Separator" | "Spacer"), ___?OptionQ] = gate


ParseGate[any_?StringQ, ___?OptionQ] := (
  Message[QuantumCircuit::elm, any];
  "Spacer"
 )

ParseGate[expr_, ___?OptionQ] := expr /; FreeQ[expr, _?QubitQ]
(* Graphics primitives and directivescorrespond to this case. *)

(**** </ParseGate> *****)


measurementLabel::usage = "measurementLabel[op] returns the default label of the measurement operator op (only Pauli operators allowed)."

measurementLabel[op_Multiply] := Map[measurementLabel, List @@ op]

measurementLabel[ss:{___?QubitQ}] := measurementLabel /@ ss

measurementLabel[S_?QubitQ] :=
  FlavorLast[S] /. {0 -> "I", 1 -> "X", 2 -> "Y", 3 -> None, _ -> "?"}


(**** <gateLabel> *****)

gateLabel::usage = "gateLabel[G] returns the label of circuit element G to be displayed in the circuit diagram."

SetAttributes[gateLabel, Listable];

(* Not used any longer. *)
gateLabel[_Symbol?QubitQ[___, -C[n_]]] :=
  With[{m = -n}, Style[HoldForm[-2 Pi / HoldForm[Power[2, m]]], Small]]
(* NOTE: HoldForm is required here because later qcNodes uses ReleaseHold. *)
  
(* Not used any longer. *)
gateLabel[_Symbol?QubitQ[___, C[n_]]] :=
  With[{m = -n}, Style[HoldForm[2 Pi / HoldForm[Power[2, m]]], Small]]
(* NOTE: HoldForm is required here because later qcNodes uses ReleaseHold. *)
  
(* Not used any longer. *)
gateLabel[S_?QubitQ] := thePauliForm[S]


gateLabel[ op_Phase ] := thePauliForm[op]


gateLabel @ Rotation[_, {any_, 0|0., 0|0.}, _?QubitQ, ___] :=
  Subscript["R", "x"] /; And[any != 0, any != 0.]

gateLabel @ Rotation[_, {0|0., any_, 0|0.}, _?QubitQ, ___] :=
  Subscript["R", "y"] /; And[any != 0, any != 0.]

gateLabel @ Rotation[_, {0|0., 0|0., any_}, _?QubitQ, ___] :=
  Subscript["R", "z"] /; And[any != 0, any != 0.]

gateLabel[ Rotation[_, {_, _, _}, _?QubitQ, ___] ] :=
  Subscript[ "R", Style["n", Bold] ]


gateLabel @ EulerRotation[{_, _, _}, S_?QubitQ, ___] :=
  Subscript["R", "E"]


gateLabel @ ControlledPower[_, _, OptionsPattern[]] := With[
  { lbl = OptionValue[ControlledPower, "Label"] },
  {First @ lbl, Superscript[Last @ lbl, First @ lbl]}
 ]

(**** </gateLabel> *****)


(**** <gateShape> ****)

gateShape::usage = "gateShape[name][x, y, args] renders the shape of the quantum circuit element named name."

gateShape["CirclePlus"][x_, yy_List, ___] :=
  gateShape["CirclePlus"] @@@ Thread @ {x, yy}

gateShape["CirclePlus"][x_, y_?NumericQ, ___] := {
  Circle[{x, y}, $GateSize / 3],
  Line @ {
    { {x-$GateSize/3,y}, {x+$GateSize/3,y} },
    { {x,y-$GateSize/3}, {x,y+$GateSize/3} }
   }
 }


gateShape["Cross"][x_, Rule[yy_List, _], ___] :=
  gateShape["Cross"][x, yy]

gateShape["Cross"][x_, yy_List, ___] :=
  gateShape["Cross"] @@@ Thread @ {x, yy}

gateShape["Cross"][x_, y_, ___] := List @ Line @ {
    { {x,y}+{-1,-1}*2*$DotSize, {x,y}+{+1,+1}*2*$DotSize },
    { {x,y}+{-1,+1}*2*$DotSize, {x,y}+{+1,-1}*2*$DotSize }
   }


gateShape["Measurement"][x_, {y_}, opts___?OptionQ] :=
  gateShape["Measurement"][x, y, opts]

gateShape["Measurement"][x_, yy:{_, __}, opts___?OptionQ] := Module[
  { tt = OptionValue[Gate, {opts}, "Label"],
    cc, mm, rest },
  rest = Normal @ KeyDrop[{opts}, "Label"];
  
  mm = MapThread[
    gateShape["Measurement"][x, #1, "Label" -> #2, opts]&,
    {yy, tt}
   ];

  cc = {
    Line @ Thread @ {x-$DotSize/2, yy},
    Line @ Thread @ {x+$DotSize/2, yy}
   };

  {cc, mm}
 ]

gateShape["Measurement"][x_, y_, opts___?OptionQ] := Module[
  {pane, text, arc, needle},

  pane = gateShape["Rectangle"][x, y];
  text = measurementText[{x, y}, opts];
  
  arc = Circle[ {x, y - 0.25 $GateSize}, .5 $GateSize, {1,5} Pi/6 ];
  needle = Line[{ {x, y - 0.25 $GateSize}, {x,y} + .3{1,1}$GateSize }];
  
  {pane, text, arc, needle}
 ]


gateShape["Projector"][x_, yy_List, ___] := Module[
  { y1 = Min @ yy,
    y2 = Max @ yy,
    pane, symb },
  pane = Polygon[{
      {x, y2} + $GateSize {+1,+1}/2,
      {x, y2} + $GateSize {-1,+1}/2,
      {x, y1} + $GateSize {-1,-1}/2,
      {x, y1} + $GateSize {+1,-1}/2 }];
  symb = Polygon[{
      {x, y2} + $GateSize {+1,+1}/2,
      {x, y1} + $GateSize {-1,-1}/2,
      {x, y2} + $GateSize {-1,+1}/2,
      {x, y1} + $GateSize {+1,-1}/2 }];
  { {EdgeForm[], White, pane},
    {EdgeForm[Black], White, symb} }
 ]


gateShape["Dot"][x_, yy_List, ___] :=
  gateShape["Dot"][x, yy -> Table[1, Length @ yy]]
(* NOTE: This form may occur on TARGET (NOT control) qubits such as for CZ. *)

gateShape["Dot"][x_, rr:Rule[_List, _List], ___] :=
  gateShape["Dot"] @@@ Thread @ {x, Thread @ rr}

gateShape["Dot"][x_, y_?NumericQ -> 1, ___] :=
  Disk[{x, y}, $DotSize]

gateShape["Dot"][x_, y_?NumericQ -> 0, ___] :=
  {EdgeForm[Black], White, Disk[{x, y}, $DotSize]}


gateShape["MixedDot"][x_, rr:Rule[_List, _List], ___] :=
  gateShape["MixedDot"] @@@ Thread @ {x, Thread @ rr}

gateShape["MixedDot"][x_, y_?NumericQ -> _, ___] :=
  { EdgeForm[Black],
    White, Disk[{x, y}, $DotSize, {1, 5}*Pi/4],
    Black, Disk[{x, y}, $DotSize, {-3, 1}*Pi/4] }


gateShape["CircleDot"][x_, yy_List, ___] := {
  Line[Thread @ {x, yy}],
  gateShape["CircleDot"] @@@ Thread @ {x, yy}
 }

gateShape["CircleDot"][x_, y_, ___] :=
  { EdgeForm[Black],
    White, Disk[{x, y}, 2*$DotSize],
    Black, Disk[{x, y}, 0.75*$DotSize] }


gateShape["Rectangle"][x_, yy_List, opts___?OptionQ] := Module[
  { y1 = Min @ yy,
    y2 = Max @ yy,
    pane, line, text },
  text = gateText[{x, Mean @ {y1, y2}}, opts];
  pane = Rectangle[
    {x, y1} - 0.5{1,1}$GateSize,
    {x, y2} + 0.5{1,1}$GateSize ];
  line = Line @ {
    {x, y1} + {-1, -1}*$GateSize/2,
    {x, y1} + {+1, -1}*$GateSize/2,
    {x, y2} + {+1, +1}*$GateSize/2,
    {x, y2} + {-1, +1}*$GateSize/2,
    {x, y1} + {-1, -1}*$GateSize/2
   };
  {{EdgeForm[], White, pane}, line, text}
 ]

gateShape["Rectangle"][ x_, y_?NumericQ, opts___?OptionQ ] :=
  gateShape["Rectangle"][x, {y}, opts]


gateShape["Oval"][ x_, y_?NumericQ, opts___?OptionQ ] := Module[
  { pane, text},
  text = gateText[{x, y}, opts];
  pane = Disk[{x, y}, $GateSize/2];
  { {EdgeForm[Black], White, pane}, text }
 ]

gateShape["Oval"][ x_, Rule[yy_List, _], opts___?OptionQ ] := Module[
  { x1 = x - $GateSize/2,
    x2 = x + $GateSize/2,
    y1 = Min @ yy,
    y2 = Max @ yy,
    y0, y3, ff, pane, text},
  
  text = gateText[{x, Mean @ {y1, y2}}, opts];

  ff = 0.657;
  y0 = y1 - $GateSize ff;
  y3 = y2 + $GateSize ff;
  pane = FilledCurve @ {
    BezierCurve @ {{x2, y2}, {x2, y3}, {x1, y3}, {x1, y2}}, 
    Line @ {{x1, y2}, {x1, y1}}, 
    BezierCurve @ {{x1, y0}, {x2, y0}, {x2, y1}}
   };
  { {EdgeForm[Black], White, pane}, text }
 ]

(**** </gateShape> ****)


(**** <linkShape> ****)

linkShape["Default"][x_, yy_List, ___?OptionQ] :=
  Line[Thread @ {x, yy}]

linkShape["Wiggly"][x_, yy_List, opts___?OptionQ] := {
  Successive[
    gateText[(#1+#2)/2, opts, "LabelOffset" -> {-2, 0}]&,
    Thread @ {x, yy}
   ],
  theWiggly[Thread @ {x, yy}]
 }


theWiggly::usage = "theWiggly[a, b] returns a list of points wiggling around the straight line connecting the two points a and b."

theWiggly[args__] := BezierCurve @ theSawtooth[args]


theSawtooth::usage = "theSawtooth[a, b, n, scale] returns a list of points corresponding to the sawtooth shape around the straight line connecting the two points a and b."

theSawtooth[pp:{{_, _}..}] := Successive[theSawtooth, pp]

theSawtooth[a:{_, _}, b:{_, _}] :=
  theSawtooth[a, b, Round[Norm[a-b]*4/$CircuitUnit], 1.5]

theSawtooth[a:{_, _}, b:{_, _}, n_Integer, scale_] := Module[
  { pp = Subdivide[a, b, n] },
  Prepend[
    Catenate @ Successive[
      { (#2+#1)/2 + scale*Reverse[{1, -1} * (#2-#1)],
        (#2+#1)/2 - scale*Reverse[{1, -1} * (#2-#1)],
        #2 }&,
      pp ],
    a ]
 ]

(**** </linkShape> ****)


gateText[{x_, y_}, opts___?OptionQ] := Module[
  { label = OptionValue[Gate, {opts}, "Label"],
    angle = OptionValue[Gate, {opts}, "LabelAngle"],
    offset = OptionValue[Gate, {opts}, "LabelOffset"],
    factor = OptionValue[Gate, {opts}, "LabelSize"] },
  If[label == None, Return @ Nothing];
  If[angle != 0, label = Rotate[label, angle]];
  Text[
    Style[ label,
      Sequence @@ q3AssureList @ OptionValue[Gate, {opts}, "LabelStyle"],
      FontSlant -> Italic,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitSize) factor] ],
    {x, y},
    offset
    (* Notice the y-offset:
       Before v12.2, y-offset=0 shifted a bit upward.
       It seems different in v12.2. *)
   ]
 ]

measurementText[{x_, y_}, opts___?OptionQ] := Module[
  { label = OptionValue[Gate, {opts}, "Label"],
    factor = OptionValue[Gate, {opts}, "LabelSize"] },
  If[label == None, Return @ Nothing];
  Text[
    Style[ label,
      Sequence @@ q3AssureList @ OptionValue[Gate, {opts}, "LabelStyle"],
      FontSlant -> Italic,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitSize) factor] ],
    {x + 0.65 $GateSize, y},
    {-1, -1}
   ]
 ]


qcNodes::usage = "qcNodes[ ... ] takes circuit elements and construct them as nodes of the circuit diagram by assigning horizontal and vertical coordinates to them."

qcNodes[gg_List, xx_List, yy_Association] :=
  ReleaseHold @ Thread @ Hold[qcDrawGate][gg, xx, yy]


qcDrawGate::usage = "Renders the gates."

qcDrawGate[gg_List, x_, yy_Association] := Map[qcDrawGate[#, x, yy]&, gg]

qcDrawGate[
  Gate[cc:{Rule[_?QubitQ, _]..}, tt:{__?QubitQ}, opts:OptionsPattern[]],
  x_, yy_Association ] := Module[
    { yc = Lookup[yy, Keys @ cc],
      yt = Lookup[yy, tt],
      label = OptionValue[Gate, {opts}, "Label"],
      control = gateShape @ OptionValue[Gate, {opts}, "ControlShape"],
      target = gateShape @ OptionValue[Gate, {opts}, "TargetShape"],
      link = linkShape @ OptionValue[Gate, {opts}, "LinkShape"],
      dots, legs, pane },

    If[Not @ ListQ[label], label = {label, label}];
    
    dots = control[x, yc -> Values[cc], "Label" -> First[label], opts];
    pane = target[x, yt, "Label" -> Last[label], opts];
    legs = link[x, Lookup[yy, Join[Keys @ cc, tt]], opts];
    
    Join[{legs}, dots, pane]
   ]


qcDrawGate[Gate[tt:{__?QubitQ}, opts___?OptionQ], x_, yy_Association] :=
  Module[
    { yt = Lookup[yy, tt],
      target = gateShape @ OptionValue[Gate, {opts}, "TargetShape"] },
    target[x, yt, opts]
   ]


qcDrawGate[qc_QuantumCircuit, x_, yy_Association] := With[
  { xx = Range[x, qcDepth[qc] + x - 1] },
  ReleaseHold @ Thread[Hold[qcDrawGate][List @@ qc, xx, yy]]
 ]


qcDrawGate["Spacer", _, _Association] = Nothing

qcDrawGate["Separator", x_, yy_Association] := Module[
  { xy = Tuples[{{x}, MinMax @ yy }] },
  { Dotted,
    Line @ {
      {0,-$CircuitUnit/2} + First @ xy,
      {0,+$CircuitUnit/2} + Last @ xy }
   }
 ]

qcDrawGate[g_, x_, yy_Association] := g


qcLines::usage = "qcLines[gg, x, y] finds when Measurement occurs in the QuantumCircuit and renders the qubit line after Measurement in dashes."

qcLines[ gg_List, xx_List, yy_Association ] := Module[
  { mm, zz, dashed, plain },
  mm = Map[
    Cases[ {#}, Gate[{S_?QubitQ},
        "TargetShape" -> "Measurement", ___?OptionQ] -> S, Infinity ]&,
    gg
   ];
  mm = Flatten[ Thread /@ Thread[mm -> Mos[xx]] ];
  mm = KeySort @ KeyTake[Association @ mm, Keys @ yy];
  
  zz = Lookup[yy, Keys @ mm];
  dashed = Line @ Transpose @ {
    Thread[ {Values @ mm, zz} ],
    Thread[ {Last @ xx, zz} ] };

  plain = Association @ Thread[ Keys[yy] -> Last[xx] ];
  plain = Join[ plain, mm ];
  plain = Line @ Transpose @ {
    Thread[{0, Values @ yy}],
    Transpose @ {Values @ plain, Values @ yy} };

  {{Dashed, dashed}, plain}
 ]


qCircuitOutput::usage = "It draws the output states behind the scene."

qCircuitOutput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitOutput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{Last[xx] + $InOutOffset, #}&, yy],
    ff = List @ ParsePort @ gg },
  Map[qcDrawPort[#, xy]&, ff]
 ]


qCircuitInput::usage = "It draws the input states behind the scene."

qCircuitInput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitInput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{-$InOutOffset, #}&, yy],
    ff },

  ff = Join[gg, {"Pivot" -> {1, 0}, "Type" -> -1} ];
  ff = List @ ParsePort @ ff;

  Map[qcDrawPort[#, xy]&, ff]
 ]


(**** <ParsePort> ****)

Port::usage = "Port[{s1,s2,\[Ellipsis]}, opts] represents a low-level quantum circuit element operating on qubits {s1,s2,\[Ellipsis]}.\nGate[{c1,c2,\[Ellipsis]}\[RightArrow]{v1,v2,\[Ellipsis]}, {t1,t2,\[Ellipsis]}, opts] represents a low-level quantum circuit element operating on target qubits {t1,t2,\[Ellipsis]} conditioned on control qubits {c1,c2,\[Ellipsis]} having values {v1,v2,\[Ellipsis]}."

Gate[cc:{__?QubitQ}, tt:{__?QubitQ}, opts:OptionsPattern[]] :=
  Gate[cc -> Table[1, Length @ cc], tt, opts]


ParseGate::usage = "ParseGate[expr, opts] is a low-level function to preprocess quantum circuit element expr."

ParsePort::usage = "ParsePorts preprocesses various input and output forms of QuantumCircuit."

Options[Port] = {
  "Label" -> Automatic,
  "LabelSize" -> 1, (* RELATIVE *)
  "LabelStyle" -> {},
  (* A list of options to Style; e.g., "LabelStyle" -> {FontSland -> Plain} *)
  "LabelAngle" -> 0,
  "Pivot" -> {-1, 0},
  "Type"  -> 1 (* 1: input, -1: output *)
 }

ParsePort[v:Ket[_Association], opts___?OptionQ] := Port[v, opts]

ParsePort[v:Ket[Except[_Association]], ___] :=
  (Message[QuantumCircuit::ket, v]; Nothing)
(* NOTE: Somehow v_Ket does not work properly. *)

ParsePort[v:ProductState[_Association, ___?OptionQ], more___?OptionQ] :=
  Port[v, more]

ParsePort[v:ProductState[Except[_Association]], ___] :=
  (Message[QuantumCircuit::ket, v]; Nothing)
(* NOTE: Somehow v_ProductState does not work properly. *)

ParsePort[expr:Except[_List], opts___?OptionQ] :=
  Port[expr, opts] /; Not @ FreeQ[expr, _Ket]

ParsePort[a_List, opts___?OptionQ] := ParsePort @@ Join[a, {opts}]

ParsePort[g_, opts___?OptionQ] := g /; FreeQ[g, _Ket | _ProductState]

ParsePort[a_, b__, opts___?OptionQ] := Map[ParsePort[#, opts]&, {a, b}]

(**** </ParsePort> ****)


qcDrawPort::usage = "qcDrawPort renders the input/output ports."

qcDrawPort[ gg_List, xy_Association ] := Map[qcDrawPort[#, xy]&, gg]

qcDrawPort[ Port[ Ket[v_], opts___?OptionQ ], xy_Association ] := Module[
  { vv = Ket /@ v,
    tt, label, pivot },
  { label, pivot } = {"Label", "Pivot"} /. {opts} /. Options[Port];

  If[label === None, Return @ {}];
  
  tt = If[ label === Automatic,
    vv,
    If[ Not @ ListQ @ label, label = {label} ];
    AssociationThread[ Keys[v] -> PadRight[label, Length[v], label] ]
   ];
  tt = Association @ KeyValueMap[
    Switch[ #2,
      None, Nothing,
      Automatic, #1 -> Ket[Lookup[v, #1]],
      _, #1 -> #2 ]&,
    tt ];
  
  Values @ MapThread[
    qcPortText[#1, #2, pivot, opts]&,
    KeyIntersection @ {tt, xy}
   ]
 ]

qcDrawPort[
  Port[ ProductState[v_Association, opts___], more___?OptionQ ],
  xy_Association
 ] := Module[
   { label, pivot, tt },
   { label, pivot } = {"Label", "Pivot"} /. {opts, more} /.
     Options[Port];

   tt = If [ label === Automatic,
     Map[ Simplify @ Dot[{Ket[0], Ket[1]}, #]&, v ],
     If[ Not @ ListQ @ label, label = {label} ];
     AssociationThread[ Keys[v] -> PadRight[label, Length[v], label] ]
    ];
  tt = Association @ KeyValueMap[
    Switch[ #2,
      None, Nothing,
      Automatic, #1 -> {Ket[0], Ket[1]} . Lookup[v, #1],
      _, #1 -> #2 ]&,
    tt ];
     
   Values @ MapThread[
     qcPortText[#1, #2, pivot, opts, more]&,
     KeyIntersection @ {tt, xy}
    ]
  ]

qcDrawPort[ Port[ expr_, opts___?OptionQ ], xy_Association ] := (
  Message[QuantumCircuit::noqubit, expr];
  Return @ {};
 ) /; Qubits[expr] == {}

qcDrawPort[ Port[ expr_, opts___?OptionQ ], xy_Association ] := Module[
  { qq = Qubits @ expr,
    label, pivot, dir, brace, text, zz },

  { label, pivot, dir } = { "Label", "Pivot", "Type" } /.
    {opts} /. Options[Port];

  If[label === None, Return @ {}];
  
  text = If[label === Automatic, SimpleForm[expr, qq], label];
  
  zz = Transpose[ MinMax /@ Transpose @ Lookup[xy, qq] ];

  If[ Length[qq] > 1,
    brace = qcPortBrace[dir, zz];
    zz = Mean @ zz + ($InOutOffset + $BraceWidth) {dir, 0};
    { brace, qcPortText[text, zz, pivot, opts] },
    qcPortText[text, Mean @ zz, pivot, opts]
   ]
 ]

qcDrawPort[ g_, xy_Association ] := g


qcPortText[text_, pt:{_, _}, pivot:{_, _}, opts___?OptionQ] := Module[
  { label = text,
    angle = OptionValue[Port, {opts}, "LabelAngle"],
    factor = OptionValue[Port, {opts}, "LabelSize"] },
  If[angle != 0, label = Rotate[label, angle]];
  Text[
    Style[
      label,
      Sequence @@ q3AssureList @ OptionValue[Port, {opts}, "LabelStyle"],
      FontWeight -> "Light",
      FontSize -> Scaled[(0.4 $GateSize / $CircuitSize) factor]
     ],
    pt, pivot
   ]
 ]

qcPortBrace[-1, { a:{_, _}, b:{_, _} } ] :=
  LeftBrace[a, b, "Width" -> $BraceWidth]

qcPortBrace[+1, { a:{_, _}, b:{_, _} } ] :=
  RightBrace[a, b, "Width" -> $BraceWidth]


(**** <Mark> ****)

SetAttributes[qcMark, Listable];

Mark::usage = "Mark[text, {x, y}] is similar to Text[text, {x, -y}] but the coordinates {x, -y} are scaled by unit scale of QuantumCircuit and is supposed to be used only inside QuantumCircuit."

qcMark @ Mark[text_, {x_, y_}, opts___?OptionQ] :=
  qcMark @ Mark[text, {x, y}, {0, 0}, opts]

qcMark @ Mark[text_, {x_, y_}, {a_, b_}, opts___?OptionQ] := Module[
  { label = text,
    angle = OptionValue[Gate, {opts}, "LabelAngle"],
    factor = OptionValue[Gate, {opts}, "LabelSize"] },
  If[angle != 0, label = Rotate[label, angle]];
  Text[
    Style[ label,
      Sequence @@ q3AssureList @ OptionValue[Gate, {opts}, "LabelStyle"],
      FontSlant -> Plain,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitSize) factor] ],
    {x, -y} * $CircuitUnit,
    {a, b}
   ]
 ]

(**** </Mark> ****)


(**** <GateFactor> ****)

GateFactor::usage = "GateFactor[gate] factorizes a high-level gate GATE into an efficient sequence of elementary gates."

GateFactor[expr_] = expr

(**** </GateFactor> ****)


End[]

EndPackage[]
