(* -*- mode: math; -*- *)
BeginPackage["Q3`"]

{ QuantumCircuit,
  QuantumCircuitTrim };

{ ParseGate, Gate, Mark };

{ ParsePort, Port };
{ PortIn, PortOut };


Begin["`Private`"]

QuantumCircuit::usage = "QuantumCircuit[a, b, ...] represents the quantum circuit model consisting of the gate operations a, b, ..., and it is displayed the circuit in a graphical form.\nExpressionFor[ QuantumCircuit[...] ] takes the non-commutative product of the elements in the quantum circuit; namely, converts the quantum circuit to a operator or vector expression.\nMatrix[ QuantumCircuit[...] ] returns the matrix representation of the quantum circuit model."

QuantumCircuit::noqubit = "No Qubit found in the expression ``. Use KetRegulate to specify the Qubits explicitly."

QuantumCircuit::nofunc = "Unknown function \"``\" to draw the gate. \"Rectangle\" is assumed."

QuantumCircuit::ket = "`` is not a proper ket of the form Ket[<|...|>] or ProductState[<|...|>]."

QuantumCircuit::elm = "`` is not a quantum circuit element."


PortIn::usage = "PortIn is a holder for input expression in QuantumCircuit.\nSee also PortOut."

PortOut::usage = "PortOut is a holder for expected output expressions in QuantumCircuit. Note that the output expressions are just expected output and may be different from the actual output. They are used only for output label and ignored by ExpressionFor and Elaborate.\nSee also PortIn."


(**** <User Interface> ****)

SetAttributes[{QuantumCircuit, PortOut, PortIn}, Flat]

QuantumCircuit[rest:Except[_?qcKetQ].., Longest[vv__?qcKetQ]] :=
  QuantumCircuit[rest, PortOut[vv]]

QuantumCircuit[Longest[vv__?qcKetQ]] :=
  QuantumCircuit @ PortIn[vv]

QuantumCircuit[Longest[opts__?OptionQ], rest:Except[_?OptionQ]..] :=
  QuantumCircuit[rest, opts]

QuantumCircuit[a_PortOut, bb__PortOut] :=
  QuantumCircuit @ PortOut[a, bb]

QuantumCircuit[a_PortIn, bb__PortIn] :=
  QuantumCircuit @ PortIn[a, bb]

QuantumCircuit[rest__, in_PortIn] :=
  QuantumCircuit[in, rest]

QuantumCircuit[out_PortOut, rest:Except[_?OptionQ|_PortOut]..] :=
  QuantumCircuit[rest, out]


qcKetQ[_PortIn | _PortOut | _Projector] = False

qcKetQ[expr_] := Not @ FreeQ[expr, _Ket | _ProductState | _State]


(* See also GraphState[] *)
QuantumCircuit[pre___, g_Graph, post___] := Module[
  { qubits = VertexList[g],
    links  = EdgeList[g] },
  links = links /. { UndirectedEdge -> CZ, DirectedEdge -> CZ };
  QuantumCircuit[pre, Through[qubits[6]], Sequence @@ links, post]
  /; AllTrue[qubits, QubitQ]
]

(**** </User Interface> ****)


(**** <Utility Tools> ****)

QuantumCircuit /:
Qubits @ QuantumCircuit[gg__, opts___?OptionQ] := Union[
  Qubits@{gg},
  FlavorNone @ doAssureList["Visible" /. {opts} /. Options[QuantumCircuit]]
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

(**** </Utility Tools> ****)


(**** <Multiply> ****)

QuantumCircuit /:
NonCommutativeQ[_QuantumCircuit] = True

QuantumCircuit /:
MultiplyKind[_QuantumCircuit] = Qubit


QuantumCircuit /:
Dagger @ QuantumCircuit[gg__, opts___?OptionQ] :=
  QuantumCircuit[Sequence @@ Map[Dagger, Reverse@{gg}], opts]


QuantumCircuit /:
Multiply[pre___, QuantumCircuit[elm__], post___] :=
  Multiply[pre, Elaborate @ QuantumCircuit[Reverse@{post}, elm]]
(* NOTE: {elm} may include Measurement. *)

QuantumCircuit /:
Multiply[pre___, Longest[cc__QuantumCircuit], post___] :=
  Multiply[pre, Elaborate @ Apply[QuantumCircuit, Reverse@{cc}], post]

(**** </Multiply> ****)


(**** <Elaborate> ****)

AddElaborationPatterns[_QuantumCircuit]

QuantumCircuit /:
ExpressionFor[ qc_QuantumCircuit ] := Elaborate[ qc ]

QuantumCircuit /:
Elaborate @ QuantumCircuit[gg__, ___?OptionQ] := Module[
  { expr = Flatten @ QuantumCircuitTrim @ {gg} },
  Garner[ QCAct @@ expr ]
]
(* NOTE: This makes the evaluation much faster, especially, when the initial
   state is specified in the circuit. *)

QCAct::usage = "QCAct[elm1, elm2, \[Ellipsis]] is a version of Multiply for QuantumCircuit elements elm1, elm2, \[Ellipsis]."

QCAct[] = 1

QCAct[any_] := Elaborate[any]

QCAct[pre__, op_Measurement, post___] := 
  QCAct[op @ QCAct[pre], post] /;
  Not @ FreeQ[{pre}, _Ket|_State]

QCAct[op_Measurement, post___] :=
  Multiply[QCAct[post], op]

QCAct[op:Except[_Measurement]..] :=
  Elaborate @ Fold[ Garner[Multiply[#2, #1]]&, 1, {op} ]
(* NOtE: One can use Elaborate@{op} as follows:
   Fold[ Garner[Multiply[#2, #1]]&, 1,  Elaborate@{op} ]
   However, this cannot take the advantange of op ** Ket[...]. *)

QCAct[gg__] := MeasurementFunction[{gg}]

(**** </Elaborate> ****)


(**** <Matrix> ****)

QuantumCircuit /:
Matrix[qc_QuantumCircuit] := Matrix[qc, Qubits @ qc]

QuantumCircuit /:
Matrix[qc:QuantumCircuit[gg__, ___?OptionQ], ss:{___?QubitQ}] := Module[
  { ff },
  ff = SplitBy[
    Flatten @ QuantumCircuitTrim@{gg},
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

SetAttributes[QuantumCircuitTrim, Listable];

QuantumCircuitTrim[ HoldPattern @ QuantumCircuit[gg__, ___?OptionQ] ] :=
  Flatten @ QuantumCircuitTrim @ {gg}

QuantumCircuitTrim[ PortIn[a__] ] :=
    Multiply @@ QuantumCircuitTrim[ {a} ]
(* NOTE: Useful to apply Matrix directly to QuantumCircuit.  *)

QuantumCircuitTrim[ _PortOut ] = Nothing

QuantumCircuitTrim[ _?OptionQ ] = Nothing

QuantumCircuitTrim[ g_?ComplexQ ] = g (* NOT _?CommutativeQ *)

QuantumCircuitTrim[ g_ ] := Nothing /;
  FreeQ[g, _?QubitQ | _Dyad | _Ket | _ProductState]

QuantumCircuitTrim[ HoldPattern @ Projector[v_, qq_, ___?OptionQ] ] :=
  Dyad[v, v, qq]

QuantumCircuitTrim[ v:ProductState[_Association, ___] ] := Expand[v]

QuantumCircuitTrim[ v:Ket[_Association] ] = v

QuantumCircuitTrim[ ActOn[op_, __] ] = op

QuantumCircuitTrim[ Gate[expr_, ___?OptionQ] ] = expr

QuantumCircuitTrim[ op_Symbol[expr__, ___?OptionQ] ] := op[expr]

QuantumCircuitTrim[ g_ ] := g

(**** </QuantumCircuitTrim> ****)


(**** <Graphics> ****)

$CircuitDepth = 1 (* dynamically change *)

$CircuitUnit = 1

$GateSize := 0.80 * $CircuitUnit

$PortSize := 0.65 * $CircuitUnit * {1, 1} (* subject to modification *)

$DotSize := 0.09 * $CircuitUnit

$PortGap := 0.20 * $CircuitUnit

$BraceWidth := 0.4 * $CircuitUnit

Options[QuantumCircuit] = {
  "UnitLength" -> 36, (* 72 is a good choice for presentation *)
  "Visible" -> None,
  "Invisible" -> None,
  "PortSize" -> 0.65
}

Format[ qc:QuantumCircuit[__, opts___?OptionQ] ] :=
  Interpretation[Graphics @ qc, qc]

QuantumCircuit /:
HoldPattern @
  Graphics[ QuantumCircuit[gg__, opts___?OptionQ], more___?OptionQ ] :=
  Module[
    { ss = Qubits@{gg},
      cc = ParseGate@{gg},
      vv, ww, xx, yy, in, out, unit, nodes, marks, lines },

    {vv, ww, unit, $PortSize} =
      {"Visible", "Invisible", "UnitLength", "PortSize"} /.
      Flatten[{opts}] /. Options[QuantumCircuit];
    (* NOTE: Here, Flatten is required since OptionQ[{}] returns True and in
       such a case, {...} /. {} /. {...} returns {{...}} instead of {...}. *)

    $PortSize = doAssureList[$PortSize, 2] * $CircuitUnit;

    vv = FlavorNone @ Flatten @ doAssureList @ vv;
    ww = FlavorNone @ Flatten @ doAssureList @ ww;
    ss = Union @ Flatten@{ss, vv, ww};

    cc = DeleteCases[cc, {}]; (* E.g., Measurement[{}] *)
    If[cc == {}, cc = {"Spacer"}]; (* E.g., only input elements *)
    
    xx  = 1 + Accumulate[Prepend[Map[qcDepth, cc], 0]];
    xx *= $CircuitUnit;
    $CircuitDepth = Last[xx];
    
    yy = Range[Length @ ss] * $CircuitUnit;
    yy = AssociationThread[ss, -yy];

    nodes = qcNodes[cc, Most @ xx, yy];
    lines = qcLines[cc, xx, KeyDrop[yy, ww]];

    marks = qcMark @ Cases[{gg}, _Mark, Infinity];

    in = FirstCase[ {gg}, PortIn[kk___] :> {kk} ];
    in = qCircuitInput[in, xx, yy];

    out = FirstCase[ {gg}, PortOut[kk___] :> {kk} ];
    out = qCircuitOutput[out, xx, yy];

    Graphics[ Join[lines, in, nodes, marks, out],
      FilterRules[{opts}, Options @ Graphics],
      more,
      PlotRange -> { {0, Max @ xx}, MinMax[yy] + 0.5*$CircuitUnit*{-1, 1} },
      ImagePadding -> unit * { $PortSize, 0.2*$CircuitUnit*{1, 1} },
      ImageSize -> unit * ( $CircuitDepth + Total[$PortSize] )
    ]
  ]


qcDepth::usage = "qcDepth[expr] returns the depth of quantum circuit element expr."

qcDepth[qc_QuantumCircuit] := Total @ Map[qcDepth, List @@ qc]

qcDepth[gg_List] := Max @ Map[qcDepth, gg]

qcDepth[any_] := Boole @ Not @ FreeQ[any, _?QubitQ | "Separator" | "Spacer" ]

(**** </Graphics> ****)


(**** <Gate> *****)

Gate::usage = "Gate[{s1,s2,\[Ellipsis]}, opts] represents a low-level quantum circuit element operating on qubits {s1,s2,\[Ellipsis]}.\nGate[{c1,c2,\[Ellipsis]}\[RightArrow]{v1,v2,\[Ellipsis]}, {t1,t2,\[Ellipsis]}, opts] represents a low-level quantum circuit element operating on target qubits {t1,t2,\[Ellipsis]} conditioned on control qubits {c1,c2,\[Ellipsis]} having values {v1,v2,\[Ellipsis]}."

Options[Gate] = {
  "LinkShape" -> "Default",
  "LinkLabel" -> None,
  "LinkLabelSize" -> 1, (* RELATIVE size *)
  "LinkLabelStyle" -> {}, (* Example: "LabelStyle" -> {FontSland -> Plain} *)
  "LinkLabelAngle" -> 0,
  "LinkLabelAlignment" -> {-0.25, 0}, (* See PanedText for details. *)
  "ControlShape" -> "Dot",
  "ControlLabel" -> None,
  "ControlLabelSize" -> 1, (* RELATIVE size *)
  "ControlLabelStyle" -> {}, (* Example: "LabelStyle" -> {FontSland -> Plain} *)
  "ControlLabelAngle" -> 0,
  "ControlLabelAlignment" -> {0, 0}, (* See PanedText for details. *)
  "Shape" -> "Rectangle", (* for controlled gates, this is intended fro the target qubits. *)
  "Label" -> None,
  "LabelSize" -> 1, (* RELATIVE size *)
  "LabelStyle" -> {}, (* Example: "LabelStyle" -> {FontSland -> Plain} *)
  "LabelAngle" -> 0,
  "LabelAlignment" -> {0, 0} (* See PanedText for details. *)
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

(**** </Gate> *****)


(**** <Port> ****)

Port::usage = "Port[expr] is a low-level object representing an input port which is fed value expr or an output port producing value expr in a quantum circuit."

Options[Port] = {
  "Label" -> Automatic,
  "LabelSize" -> 1, (* RELATIVE *)
  "LabelAngle" -> 0,
  "LabelStyle" -> {}, (* Example: "LabelStyle" -> {FontSland -> Plain} *)
  "LabelAlignment" -> {-1, 0}, (* Usually, {11, 0} for input, and {-1, 0} for output  *)
  "Type"  -> 1 (* -1: input, 1: output *)
}

(**** </Port> ****)


(**** <ParsePort> ****)

ParsePort::usage = "ParsePorts preprocesses various input and output forms of QuantumCircuit."

ParsePort[g_, opts___?OptionQ] := 
  g /; FreeQ[g, _Ket | _ProductState | _State]


ParsePort[ {gg:Except[_?OptionQ].., opts___?OptionQ}, more___?OptionQ ] := 
  Map[ParsePort[#, more, opts]&, {gg}]


ParsePort[v:Ket[_Association], opts___?OptionQ] := 
  Port[v, opts]

ParsePort[v:Ket[Except[_Association]], ___] :=
  (Message[QuantumCircuit::ket, v]; Nothing)
(* NOTE: Somehow v_Ket does not work properly. *)


ParsePort[v:ProductState[_Association, opts___?OptionQ], more___?OptionQ] :=
  Port[v, more, opts]

ParsePort[v:ProductState[Except[_Association], ___], ___] :=
  (Message[QuantumCircuit::ket, v]; Nothing)
(* NOTE: Somehow v_ProductState does not work properly. *)


(* fallback *)

(* NOTE: This is dangerous because Plus and Times can happen. *)
(* 
ParsePort[vv_Symbol[any__, opts___?OptionQ], more__?OptionQ] :=
  ParsePort[ vv[any, more, opts] ]
 *)

ParsePort[expr:Except[_List], opts___?OptionQ] :=
  Port[expr, FilterRules[{opts}, Options @ Port]] /;
    Not @ FreeQ[expr, _Ket|_State]

(**** </ParsePort> ****)


(**** <ParseGate> *****)

ParseGate::usage = "ParseGate[expr, opts] is a low-level function to preprocess quantum circuit element expr."

ParseGate::unknown = "Unknown quantum circuit element ``."

ParseGate[ {gg:Except[_?OptionQ].., opts___?OptionQ}, more___?OptionQ ] := 
  Map[ParseGate[#, more, opts]&, {gg}]


ParseGate[qc_QuantumCircuit] := Map[ParseGate, qc]

(* These elements are handled separately. *)
ParseGate[_PortIn|_PortOut|_Mark, opts___?OptionQ] = Nothing


ParseGate[_?NumericQ, ___?OptionQ] = "Spacer"

ParseGate[gate:("Separator" | "Spacer"), ___?OptionQ] = gate

ParseGate[any_?StringQ, ___?OptionQ] := (
  Message[QuantumCircuit::elm, any];
  "Spacer"
)

ParseGate[expr_, ___?OptionQ] := expr /; FreeQ[expr, _?QubitQ]
(* Graphics primitives and directivescorrespond to this case. *)


(* Single-qubit gates *)  

ParseGate[op_?QubitQ, opts___?OptionQ] :=
  Gate[ Qubits @ op, opts, "Label" -> HoldForm[thePauliForm @ op] ]
(* NOTE: HoldForm is required here because later qcNodes uses ReleaseHold.
   Recall that thePauliForm uses HoldForm. *)


ParseGate[
  HoldPattern @ Multiply[ss__?QubitQ], 
  opts___?OptionQ
] :=
  Map[ParseGate[#, opts]&, Reverse@{ss}]


ParseGate[Measurement[ss:{___?PauliQ}, opts___?OptionQ], more___?OptionQ] :=
  Map[ParseGate[Measurement[#], more, opts]&, ss]

ParseGate[Measurement[S_?QubitQ, opts___?OptionQ], more___?OptionQ] := 
  Gate[ {FlavorMute @ S},
    "Shape" -> "Measurement", more, opts,
    "Label" -> measurementLabel[S]
  ]

HoldPattern @ ParseGate[
  Measurement[Multiply[ss__?QubitQ], opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ FlavorMute @ {ss},
    "Shape" -> "Measurement", more, opts,
    "Label" -> measurementLabel@{ss}
  ]

HoldPattern @ ParseGate[Projector[v_, qq_, ___?OptionQ], ___?OptionQ] :=
  Gate[qq, "Shape" -> "Projector", "Label" -> None]


ParseGate[ op:Phase[_, _?QubitQ, opts___?OptionQ], more___?OptionQ ] :=
  Gate[ Qubits @ op, more, opts, "Label" -> HoldForm @ thePauliForm[op] ]

ParseGate[ op:Rotation[_, {_, _, _}, G_?QubitQ, opts___?OptionQ], more___?OptionQ ] :=
  Gate[Qubits @ G, more, opts, "Label" -> gateLabel @ op]

ParseGate[ op:EulerRotation[{_, _, _}, G_?QubitQ, opts___?OptionQ], more___?OptionQ ] :=
  Gate[{G}, more, opts, "Label" -> gateLabel @ op]


(* Multi-qubit gates *)

ParseGate[
  ControlledGate[rr:{__Rule}, S_?QubitQ, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ rr, Qubits @ S, more, opts,
    "Label" -> thePauliForm[S]
  ]

ParseGate[
  ControlledGate[
    cc:{Rule[_?QubitQ, _?BinaryQ]..},
    op:(_Phase|_Rotation|_EulerRotation),
    opts___?OptionQ
  ],
  more___?OptionQ 
] :=
  Gate[ cc, Qubits @ op, 
    more, opts, Options[op],
    "Label" -> gateLabel[op]
  ]

ParseGate[
  ControlledGate[cc:{Rule[_?QubitQ, _]..}, expr_, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[cc, Qubits @ expr, more, opts] /;
  Not @ FreeQ[expr, _Dyad|_?QubitQ]


ParseGate[CNOT[cc:{Rule[_?QubitQ, _]..}, tt:{__?QubitQ}, ___?OptionQ], ___?OptionQ] :=
  Gate[cc, tt, "Shape" -> "CirclePlus"]


ParseGate[Toffoli[a_?QubitQ, b__?QubitQ, c_?QubitQ, ___?OptionQ], ___?OptionQ] :=
  Gate[ Thread[{a, b} -> {1, 1}], {c},
    "Shape" -> "CirclePlus" 
  ]


ParseGate[CZ[ss:{__?QubitQ}, ___?OptionQ], ___?OptionQ] :=
  Gate[ Most @ ss, {Last @ ss},
    "ControlShape" -> "Dot",
    "Shape" -> "Dot" 
  ]

ParseGate[Swap[c_?QubitQ, t_?QubitQ, ___?OptionQ], ___?OptionQ] :=
  Gate[ {c}, {t},
    "ControlShape" -> "Cross",
    "Shape" -> "Cross"
  ]


ParseGate[iSwap[c_?QubitQ, t_?QubitQ, ___?OptionQ], ___?OptionQ] :=
  Gate[ {c}, {t},
    "ControlShape" -> "CircleCross",
    "Shape" -> "CircleCross"
  ]


ParseGate[
  UnitaryInteraction[{0, 0, phi_}, ss:{__?QubitQ}, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ Most @ ss, {Last @ ss}, more, opts,
    "Shape" -> "Dot",
    "ControlShape" -> "Dot",
    "LinkShape" -> "Wiggly"
  ]

HoldPattern @ ParseGate[ 
  UnitaryInteraction[_?VectorQ|_?MatrixQ, ss:{__?QubitQ}, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ Most @ ss, {Last @ ss}, more, opts,
    "Shape" -> "Dot",
    "ControlShape" -> "Dot",
    "LinkShape" -> "Wiggly"
  ]


ParseGate[
  Fredkin[a_?QubitQ, {b_?QubitQ, c_?QubitQ}, ___?OptionQ],
  ___?OptionQ
] :=
  Gate[ {a}, {b, c},
    "ControlShape" -> "Dot",
    "Shape" -> "Cross"
  ]

ParseGate[
  Deutsch[ph_, {a_?QubitQ, b_?QubitQ, c_?QubitQ}, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ {a, b}, {c}, more, opts, "Label" -> "D" ]


ParseGate[ 
  Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ cc, tt, more, opts,
    "ControlShape" -> "Oval",
    "ControlLabel" -> "f(x)",
    "ControlLabelSize" -> 0.9,
    "Shape" -> "CirclePlus"
  ]


ParseGate[ 
  elm:ControlledPower[cc:{__?QubitQ}, op_, opts___?OptionQ], 
  more___?OptionQ
] := 
  Module[
    { new },
    new = FilterRules[
      { more, opts, Options @ op,
        "ControlShape" -> "Oval",
        "ControlLabel" -> "x",
        "Label" -> gateLabel[op]
      },
      Options @ Gate
    ];
    Gate[ cc, Qubits @ op,
      "Label" -> mySuperscript[
        OptionValue[Gate, new, "Label"], 
        OptionValue[Gate, new, "ControlLabel"]
      ], 
      new ]
  ]


ParseGate[
  UniformlyControlledRotation[
    cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ cc, {S}, opts,
    "ControlShape" -> "MixedDot",
    "Label" -> gateLabel @ Rotation[0, vv, S]
  ]


ParseGate[
  UniformlyControlledGate[cc:{__?QubitQ}, tt_List, opts___?OptionQ],
  more___?OptionQ
] :=
  Gate[ cc, Qubits @ tt, more, opts,
    "ControlShape" -> "MixedDot",
    "Label" -> "U"
  ]


ParseGate[
  ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ], 
  more___?OptionQ
] :=
  Gate[ cc, tt, more, opts,
    "ControlShape" -> "Oval",
    "ControlLabel" -> "x",
    "Shape" -> "Rectangle",
    "Label" -> StringForm["x\[ThinSpace]y % ``", n],
    "LabelAngle" -> -Pi/2 ]

ParseGate @
  ModMultiply[n_Integer, a_Integer, tt:{__?QubitQ}, opts___?OptionQ] :=
  Gate[ tt,
    "Shape" -> "Rectangle", opts,
    "Label" -> StringForm["``\[ThinSpace]x % ``", a, n],
    "LabelAngle" -> -Pi/2 ]


ParseGate[op:QFT[_, qq:{__?QubitQ}, _, opts___?OptionQ], more___?OptionQ] := 
  Gate[ qq, 
    FilterRules[{more, opts}, Options @ Gate],
    "Label" -> gateLabel[op],
    "LabelAngle" -> Pi/2
  ]


ParseGate[op:QBR[qq:{__?QubitQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[ qq, 
    FilterRules[{more, opts}, Options @ Gate],
    "Label" -> "QBR",
    "LabelAngle" -> Pi/2
  ]

ParseGate[op:QCR[qq:{__?QubitQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[ qq, 
    FilterRules[{more, opts}, Options @ Gate],
    "Label" -> "QCR",
    "LabelAngle" -> Pi/2
  ]

ParseGate[Gate[args__, opts___?OptionQ], more___?OptionQ] := 
  Gate[args, more, opts]

(* fallback *)

(* NOTE: This is dangerous because Plus and Times can happen. *)
(* 
ParseGate[op_Symbol[any__, opts___?OptionQ], more__?OptionQ] :=
  ParseGate @ op[any, more, opts]
 *)

ParseGate[expr:Except[_List], opts___?OptionQ] :=
  Gate[Qubits @ expr, FilterRules[{opts, Options @ expr}, Options @ Gate]]

(**** </ParseGate> *****)


(**** <measurementLabel> *****)

measurementLabel::usage = "measurementLabel[op] returns the default label of the measurement operator op (only Pauli operators allowed)."

measurementLabel[op_Multiply] := Map[measurementLabel, List @@ op]

measurementLabel[ss:{___?QubitQ}] := measurementLabel /@ ss

measurementLabel[S_?QubitQ] :=
  FlavorLast[S] /. {0 -> "I", 1 -> "X", 2 -> "Y", 3 -> None, _ -> "?"}

(**** </measurementLabel> *****)


(**** <gateLabel> *****)

gateLabel::usage = "gateLabel[G] returns the label of circuit element G to be displayed in the circuit diagram."

SetAttributes[gateLabel, Listable];


gateLabel[ S_?QubitQ ] := thePauliForm[S]


gateLabel[ op_Phase ] := thePauliForm[op]


gateLabel @ Rotation[_, {any_, 0|0., 0|0.}, _?QubitQ, ___] :=
  Subscript["R", "x"] /; And[any != 0, any != 0.]

gateLabel @ Rotation[_, {0|0., any_, 0|0.}, _?QubitQ, ___] :=
  Subscript["R", "y"] /; And[any != 0, any != 0.]

gateLabel @ Rotation[_, {0|0., 0|0., any_}, _?QubitQ, ___] :=
  Subscript["R", "z"] /; And[any != 0, any != 0.]

gateLabel[ Rotation[_, {_, _, _}, _?QubitQ, ___] ] :=
  Subscript[ "R", Style["n", Bold] ]


gateLabel @ EulerRotation[{_, _, _}, _?QubitQ, ___?OptionQ] :=
  Subscript["R", "E"]


gateLabel @ QFT[type_, _List, _?BooleanQ, ___] :=
  Switch[ type,
    -1, SuperDagger["QFT"],
    +1, "QFT",
    _, "DFT"
  ]

gateLabel[expr_] := "U"

(**** </gateLabel> *****)


(**** <gateShape> ****)

gateShape::usage = "gateShape[name][x, y, args] renders the shape of the quantum circuit element named name."

gateShape["CirclePlus"][x_, yy_List, ___] :=
  gateShape["CirclePlus"] @@@ Thread@{x, yy}

gateShape["CirclePlus"][x_, y_?NumericQ, ___] := {
  Circle[{x, y}, $GateSize / 3],
  Line@{
    { {x-$GateSize/3,y}, {x+$GateSize/3,y} },
    { {x,y-$GateSize/3}, {x,y+$GateSize/3} }
   }
 }


gateShape["CircleCross"][x_, Rule[yy_List, _], ___] :=
  gateShape["CircleCross"][x, yy]

gateShape["CircleCross"][x_, yy_List, ___] :=
  gateShape["CircleCross"] @@@ Thread@{x, yy}

gateShape["CircleCross"][x_, y_?NumericQ, ___] := {
  {EdgeForm[Black], White, Disk[{x, y}, $GateSize / 3]},
  Line@{
    { {x,y}+{-1,-1}*2*$DotSize, {x,y}+{+1,+1}*2*$DotSize },
    { {x,y}+{-1,+1}*2*$DotSize, {x,y}+{+1,-1}*2*$DotSize }
   }
 }


gateShape["Cross"][x_, Rule[yy_List, _], ___] :=
  gateShape["Cross"][x, yy]

gateShape["Cross"][x_, yy_List, ___] :=
  gateShape["Cross"] @@@ Thread@{x, yy}

gateShape["Cross"][x_, y_, ___] := List @ Line@{
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
    Line @ Thread@{x-$DotSize/2, yy},
    Line @ Thread@{x+$DotSize/2, yy}
   };

  {cc, mm}
 ]

gateShape["Measurement"][x_, y_, opts___?OptionQ] := Module[
  {pane, text, arc, needle},

  pane = gateShape["Rectangle"][x, y];
  text = theMeasurementLabel[{x, y}, opts];
  
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
    {EdgeForm[Opacity[1]], White, symb} }
 ]


gateShape["Dot"][x_, yy_List, ___] :=
  gateShape["Dot"][x, yy -> Table[1, Length @ yy]]
(* NOTE: This form may occur on TARGET (NOT control) qubits such as for CZ. *)

gateShape["Dot"][x_, rr:Rule[_List, _List], ___] :=
  gateShape["Dot"] @@@ Thread @ {x, Thread @ rr}

gateShape["Dot"][x_, y_?NumericQ -> 1, ___] :=
  Disk[{x, y}, $DotSize]

gateShape["Dot"][x_, y_?NumericQ -> 0, ___] :=
  {EdgeForm[Opacity[1]], White, Disk[{x, y}, $DotSize]}


gateShape["MixedDot"][x_, rr:Rule[_List, _List], ___] :=
  gateShape["MixedDot"] @@@ Thread @ {x, Thread @ rr}

gateShape["MixedDot"][x_, y_?NumericQ -> _, ___] :=
  { EdgeForm[Opacity[1]],
    White, Disk[{x, y}, $DotSize, {1, 5}*Pi/4],
    Black, Disk[{x, y}, $DotSize, {-3, 1}*Pi/4]
  }


gateShape["CircleDot"][x_, yy_List, ___] := {
  Line[Thread@{x, yy}],
  gateShape["CircleDot"] @@@ Thread@{x, yy}
 }

gateShape["CircleDot"][x_, y_, ___] :=
  { EdgeForm[Opacity[1]],
    White, Disk[{x, y}, 2.00*$DotSize],
    Black, Disk[{x, y}, 0.75*$DotSize]
  }


gateShape["Rectangle"][x_, yy_List, opts___?OptionQ] := Module[
  { y1 = Min @ yy,
    y2 = Max @ yy,
    pane, line, text },
  text = theGateLabel[{x, Mean @ {y1, y2}}, opts];
  pane = Rectangle[
    {x, y1} - 0.5*{1,1}*$GateSize,
    {x, y2} + 0.5*{1,1}*$GateSize ];
  {{EdgeForm[Opacity[1]], White, pane}, text}
 ]

gateShape["Rectangle"][ x_, y_?NumericQ, opts___?OptionQ ] :=
  gateShape["Rectangle"][x, {y}, opts]


gateShape["Oval"][ x_, y_?NumericQ, opts___?OptionQ ] := Module[
  { pane, text},
  text = theGateLabel[{x, y}, opts];
  pane = Disk[{x, y}, $GateSize/2];
  { {EdgeForm[Opacity[1]], White, pane}, text }
 ]

gateShape["Oval"][ x_, Rule[yy_List, _], opts___?OptionQ ] := Module[
  { x1 = x - $GateSize/2,
    x2 = x + $GateSize/2,
    y1 = Min @ yy,
    y2 = Max @ yy,
    y0, y3, pane, text},
  
  text = theGateLabel[{x, Mean@{y1, y2}}, opts];

  y0 = y1 - $GateSize/2;
  y3 = y2 + $GateSize/2;
  pane = Rectangle[{x1, y0}, {x2, y3}, RoundingRadius -> $GateSize/2];
  { {EdgeForm[Opacity[1]], White, pane}, text }
]

(**** </gateShape> ****)


(**** <linkShape> ****)

linkShape["Default"][x_, yy_List, ___?OptionQ] :=
  Line[Thread @ {x, yy}]

linkShape["Wiggly"][x_, yy_List, opts___?OptionQ] := {
  Successive[
    theLinkLabel[(#1+#2)/2, opts, "LabelAlignment" -> {-2, 0}]&,
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


(**** <theGateLabel> ****)

theGateLabel::usage = "theGateLabel[{x, y}] renders the gate label at position {x, y}."

theGateLabel[{x_, y_}, opts___?OptionQ] := Module[
  { new = FilterRules[Flatten @ {opts}, Options @ Gate],
    sty, txt },
  txt = OptionValue[Gate, new, "Label"];
  If[txt === None, Return @ Nothing];

  fit = OptionValue[Gate, new, "LabelSize"];
  sty = OptionValue[Gate, new, "LabelStyle"];
  new = KeyReplace[
    Join[new, Options @ Gate],
    { "LabelAngle" -> "Angle",
      "LabelAlignment" -> "Alignment" }
  ];

  PanedText[ txt,
    FilterRules[new, Options @ PanedText],
    "PaneSize" -> $CircuitUnit * {1, 1},
    "PanePosition" -> {x, y},
    "Style" -> Join[ doAssureList @ sty,
      { FontSlant -> Italic,
        FontWeight -> "Light",
        FontSize   -> Scaled[0.5 * fit * $GateSize / $CircuitDepth] }
    ]
  ]
]

(**** </theGateLabel> ****)


(**** <theLinkLabel> ****)

theLinkLabel::usage = "theLinkLabel[{x, y}] renders the link label at position {x, y}."

theLinkLabel[{x_, y_}, opts___?OptionQ] := Module[
  { new = FilterRules[Flatten @ {opts}, Options @ Gate],
    sty, txt },
  txt = OptionValue[Gate, new, "LinkLabel"];
  If[txt === None, Return @ Nothing];

  fit = OptionValue[Gate, new, "LinkLabelSize"];
  sty = OptionValue[Gate, new, "LinkLabelStyle"];
  new = KeyReplace[
    Join[new, Options @ Gate],
    { "LinkLabelAngle" -> "Angle",
      "LinkLabelAlignment" -> "Alignment" }
  ];

  PanedText[ txt,
    FilterRules[new, Options @ PanedText],
    "PaneSize" -> $CircuitUnit * {1, 1},
    "PanePosition" -> {x, y},
    "PaneAlignment" -> {-1, 0},
    "Style" -> Join[ doAssureList @ sty,
      { FontSlant -> Italic,
        FontWeight -> "Light",
        FontSize   -> Scaled[0.5 * fit * $GateSize / $CircuitDepth] }
    ]
  ]
]

(**** </theLinkLabel> ****)


(**** <theMeasurementLabel> ****)

theMeasurementLabel[{x_, y_}, opts___?OptionQ] := Module[
  { label = OptionValue[Gate, {opts}, "Label"],
    factor = OptionValue[Gate, {opts}, "LabelSize"] },
  If[label == None, Return @ Nothing];
  Text[
    Style[ label,
      doAssureList @ OptionValue[Gate, {opts}, "LabelStyle"],
      FontSlant -> Italic,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitDepth) factor] ],
    {x + 0.65 $GateSize, y},
    {-1, -1}
  ]
]

(**** </theMeasurementLabel> ****)


qcNodes::usage = "qcNodes[ ... ] takes circuit elements and construct them as nodes of the circuit diagram by assigning horizontal and vertical coordinates to them."

qcNodes[gg_List, xx_List, yy_Association] :=
  ReleaseHold @ Thread @ Hold[qcDrawGate][gg, xx, yy]


(**** <qcDrawGate> ****)

qcDrawGate::usage = "Renders the gates."

qcDrawGate[gg_List, x_, yy_Association] := Map[qcDrawGate[#, x, yy]&, gg]

qcDrawGate[
  Gate[cc:{Rule[_?QubitQ, _]..}, tt:{__?QubitQ}, opts___?OptionQ],
  x_, yy_Association
] := 
  Module[
    { yc = Lookup[yy, Keys @ cc],
      yt = Lookup[yy, tt],
      new = FilterRules[Flatten @ {opts}, Options @ Gate],
      alt, label, control, target, link, dots, legs, pane },
    control = gateShape @ OptionValue[Gate, new, "ControlShape"];
    target = gateShape @ OptionValue[Gate, new, "Shape"];
    link = linkShape @ OptionValue[Gate, new, "LinkShape"];
    
    pane = target[x, yt, new];
    
    alt = Reverse @ Normal @ KeyReplace[
      KeyDrop[Reverse @ new, {"Label", "LabelSize", "LabelStyle", "LabelAngle", "LabelAlignment"}],
      { "ControlLabel" -> "Label",
        "ControlLabelSize" -> "LabelSize",
        "ControlLabelStyle" -> "LabelStyle",
        "ControlLabelAngle" -> "LabelAngle",
        "ControlLabelAlignment" -> "LabelAlignment" }
    ];
    dots = control[ x, yc -> Values[cc], alt];

    legs = link[x, Join[yc, yt], new];
    
    Join[{legs}, dots, pane]
  ]


qcDrawGate[Gate[tt:{__?QubitQ}, opts___?OptionQ], x_, yy_Association] :=
  Module[
    { yt = Lookup[yy, tt],
      new = FilterRules[Flatten@{opts}, Options @ Gate] },
    target = gateShape @ OptionValue[Gate, new, "Shape"];
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
    Line@{
      {0,-$CircuitUnit/2} + First @ xy,
      {0,+$CircuitUnit/2} + Last @ xy }
   }
 ]

qcDrawGate[g_, x_, yy_Association] := g

(**** </qcDrawGate> ****)


qcLines::usage = "qcLines[gg, x, y] finds when Measurement occurs in the QuantumCircuit and renders the qubit line after Measurement in dashes."

qcLines[ gg_List, xx_List, yy_Association ] := Module[
  { mm, zz, dashed, plain },
  mm = Map[
    Cases[ {#}, Gate[{S_?QubitQ},
        "Shape" -> "Measurement", ___?OptionQ] -> S, Infinity ]&,
    gg
   ];
  mm = Flatten[ Thread /@ Thread[mm -> Most[xx]] ];
  mm = KeySort @ KeyTake[Association @ mm, Keys @ yy];
  
  zz = Lookup[yy, Keys @ mm];
  dashed = Line @ Transpose@{
    Thread[ {Values @ mm, zz} ],
    Thread[ {Last @ xx, zz} ] };

  plain = Association @ Thread[ Keys[yy] -> Last[xx] ];
  plain = Join[ plain, mm ];
  plain = Line @ Transpose@{
    Thread[{0, Values @ yy}],
    Transpose@{Values @ plain, Values @ yy} };

  {{Dashed, dashed}, plain}
 ]


qCircuitOutput::usage = "It draws the output states behind the scene."

qCircuitOutput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitOutput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{Last[xx] + $PortGap, #}&, yy],
    ff },
  ff = List @ ParsePort @ Join[gg, {"LabelAlignment" -> {-1, 0}, "Type" -> +1}];
  Map[qcDrawPort[#, xy]&, ff]
]


qCircuitInput::usage = "It draws the input states behind the scene."

qCircuitInput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitInput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{-$PortGap, #}&, yy],
    ff },
  ff = List @ ParsePort @ Join[gg, {"LabelAlignment" -> {1, 0}, "Type" -> -1}];
  Map[qcDrawPort[#, xy]&, ff]
]


(**** <qcDrawPort> ****)

qcDrawPort::usage = "qcDrawPort renders the input/output ports."

qcDrawPort[gg_List, xy_Association] := Map[qcDrawPort[#, xy]&, gg]

qcDrawPort[ Port[Ket[v_], opts___?OptionQ], xy_Association ] := Module[
  { new = FilterRules[Flatten@{opts}, Options @ Port],
    txt, tt, label },
  txt = OptionValue[Port, new, "Label"];
  If[txt === None, Return@{}];

  If[ txt === Automatic,
    txt = Ket /@ List /@ v,
    txt = AssociationThread[Keys[v] -> doForceList[txt, Length @ v] ]
  ];

  txt = Association @ KeyValueMap[
    Switch[ #2,
      None, Nothing,
      Automatic, #1 -> Ket[Lookup[v, #1]],
      _, #1 -> #2 ]&,
    txt ];
  
  Values @ MapThread[
    thePortLabel[#1, #2, new]&,
    KeyIntersection@{txt, xy}
  ]
]

qcDrawPort[
  Port[ProductState[v_Association, opts___], more___?OptionQ],
  xy_Association
] := 
  Module[
    { new = FilterRules[Flatten@{more, opts}, Options @ Port],
      txt },
    txt = OptionValue[Port, new, "Label"];
    If[txt === None, Return@{}];

    If[ txt === Automatic,
      txt = Map[ Simplify @ Dot[Ket /@ {{0}, {1}}, #]&, v ],
      txt = AssociationThread[ Keys[v] -> doForceList[txt, Length @ v] ]
    ];

    txt = Association @ KeyValueMap[
      Switch[ #2,
        None, Nothing,
        Automatic, #1 -> {Ket@{0}, Ket@{1}} . Lookup[v, #1],
      _, #1 -> #2 ]&,
      txt
    ];
     
    Values @ MapThread[
      thePortLabel[#1, #2, new]&,
      KeyIntersection@{txt, xy}
    ]
  ]

qcDrawPort[ Port[expr_, ___], _Association ] := (
  Message[QuantumCircuit::noqubit, expr];
  Return@{};
) /; Qubits[expr] == {}

qcDrawPort[ Port[expr_, opts___?OptionQ], xy_Association ] := Module[
  { qq = Qubits @ expr,
    new = FilterRules[Flatten@{opts, Options @ expr}, Options @ Port],
    txt, dir, brace, pos },

  txt = OptionValue[Port, new, "Label"];
  dir = OptionValue[Port, new, "Type"];

  If[txt === None, Return@{}];
  
  If[txt === Automatic, txt = SimpleForm[expr, qq], txt];
  
  pos = Transpose[ MinMax /@ Transpose @ Lookup[xy, qq] ];

  If[ Length[qq] > 1,
    brace = thePortBrace[dir, pos];
    pos = Mean[pos] + ($PortGap + $BraceWidth)*{dir, 0};
    { brace, thePortLabel[txt, pos, new] },
    thePortLabel[txt, Mean @ pos, new]
  ]
]

qcDrawPort[g_, _Association] := g

(**** </qcDrawPort> ****)


(**** <thePortLabel> ****)

thePortLabel::usage = "thePortLabel[expr, {x, y}, {offsetx, offsety}] renders the port label expr at position {x, y} with port-pane alignment {offsetx, offsety}."

thePortLabel[text_, pos:{_, _}, opts___?OptionQ] := Module[
  { new = FilterRules[Flatten@{opts}, Options @ Port],
    fit, pvt },
  fit = OptionValue[Port, new, "LabelSize"];
  pvt = OptionValue[Port, new, "Type"];
  
  new = KeyReplace[ 
    Join[new, Options @ Port],
    { "LabelStyle" -> "Style",
      "LabelAngle" -> "Angle",
      "LabelAlignment" -> "Alignment" }
  ];
  PanedText[ text,
    FilterRules[new, Options @ PanedText],
    (* "Paned" -> True, *)
    "PaneSize" -> {Switch[pvt, -1, First @ $PortSize, 1, Last @ $PortSize], $CircuitUnit},
    "PanePosition" -> pos,
    "PaneAlignment" -> {-pvt, 0},
    "Style" -> {
      FontWeight -> "Light",
      FontSize -> Scaled[0.4 * fit * $GateSize / $CircuitDepth] 
    }
  ]
]

(**** </thePortLabel> ****)


(**** <thePortBrace> ****)

thePortBrace[-1, { a:{_, _}, b:{_, _} } ] :=
  LeftBrace[a, b, "Width" -> $BraceWidth]

thePortBrace[+1, { a:{_, _}, b:{_, _} } ] :=
  RightBrace[a, b, "Width" -> $BraceWidth]

(**** </thePortBrace> ****)


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
      doAssureList @ OptionValue[Gate, {opts}, "LabelStyle"],
      FontSlant -> Plain,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitDepth) factor] ],
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
