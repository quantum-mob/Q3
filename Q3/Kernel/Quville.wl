(* -*- mode: math; -*- *)

BeginPackage["Q3`"]

`Quville`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.40 $"][[2]], " (",
  StringSplit["$Date: 2022-08-14 16:44:05+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ QuantumCircuit, QuissoIn, QuissoOut,
  QuantumCircuitTrim };

(* Obsolete Symbols *)

{ QuissoCircuit }; (* Obsolete *)

Begin["`Private`"]

QuissoCircuit::usage = "QuissoCircuit has been renamed QuantumCircuit."

QuissoCircuit[args___] := (
  Message[Q3General::renamed, "QuissoCircuit", "QuantumCircuit"];
  QuantumCircuit[args]
 )


QuantumCircuit::usage = "QuantumCircuit[a, b, ...] represents the quantum circuit model consisting of the gate operations a, b, ..., and it is displayed the circuit in a graphical form.\nExpressionFor[ QuantumCircuit[...] ] takes the non-commutative product of the elements in the quantum circuit; namely, converts the quantum circuit to a Quisso expression.\nMatrix[ QuantumCircuit[...] ] returns the matrix representation of the quantum circuit model."

QuantumCircuit::noqubit = "No Qubit found in the expression ``. Use LogicalForm to specify the Qubits explicitly."

QuantumCircuit::nofunc = "Unknown function \"``\" to draw the gate. \"Rectangle\" is assumed."

QuissoIn::usage = "QuissoIn is a holder for input expression in QuantumCircuit.\nSee also QuissoOut."

QuissoOut::usage = "QuissoOut is a holder for expected output expressions in QuantumCircuit. Note that the output expressions are just expected output and may be different from the actual output. They are used only for output label and ignored by ExpressionFor and Elaborate.\nSee also QuissoIn."

SetAttributes[{QuantumCircuit, QuissoOut, QuissoIn}, Flat]

AddElaborationPatterns[_QuantumCircuit]

Options[QuantumCircuit] = {
  "TargetFunction" -> "Rectangle",
  "ControlFunction" -> "Dot",
  "UnitLength" -> 36,
  "PortSize" -> 0.65,
  "LabelSize" -> 1, 
  "Label" -> Automatic,
  "Visible" -> {},
  "Invisible" -> {}
 }

$CircuitSize = 1

$CircuitUnit = 1

$GateSize := 0.8 $CircuitUnit

$DotSize := 0.09 $CircuitUnit

$InOutOffset := 0.1 $CircuitUnit

$BraceWidth := 0.125 $CircuitUnit


Format[ qc:QuantumCircuit[__, opts___?OptionQ] ] := Graphics[qc]


(**** </Multiply, ExpressionFor and Matrix on QuantumCircuit> ****)

QuantumCircuit /:
NonCommutativeQ[ QuantumCircuit[__] ] = True

QuantumCircuit /:
Kind[ QuantumCircuit[__] ] = NonCommutative

QuantumCircuit /:
MultiplyGenus[ QuantumCircuit[__] ] := "QuantumCircuit"

HoldPattern @ Multiply[
  Longest[pre___],
  QuantumCircuit[elm__], Longest[v__Ket],
  post___] := Multiply[pre, Elaborate @ QuantumCircuit[v, elm], post]
  
HoldPattern @ Multiply[pre___, Longest[qc__QuantumCircuit], post___] :=
  Multiply[pre, Multiply @@ Map[Elaborate, {qc}], post]


QuantumCircuit /:
ExpressionFor[ qc_QuantumCircuit ] := Elaborate[ qc ]

QuantumCircuit /:
HoldPattern @ Elaborate[ QuantumCircuit[gg__, ___?OptionQ] ] := Module[
  { expr = Flatten @ QuantumCircuitTrim @ {gg} },
  Garner[ qCircuitOperate @@ expr ]
 ]
(* NOTE: This makes the evaluation much faster, especially, when the initial
   state is specified in the circuit. *)

QuantumCircuit /:
HoldPattern @ Qubits[ QuantumCircuit[gg__, opts___?OptionQ] ] := Union[
  Qubits @ {gg},
  FlavorNone @ Flatten[
    {"Visible"} /. {opts} /. Options[QuantumCircuit]
   ]
 ]

QuantumCircuit /:
HoldPattern @ Matrix[ qc:QuantumCircuit[gg__, ___?OptionQ] ] := Module[
  { expr = Flatten @ QuantumCircuitTrim @ {gg} },
  qCircuitMatrix[ Sequence @@ expr, Qubits @ qc ]
 ]


qCircuitOperate::usage = "Converts gates to operators ..."

qCircuitOperate[] = 1

qCircuitOperate[pre__, op_Measurement, post___] := 
  qCircuitOperate[op @ qCircuitOperate[pre], post] /;
  Not @ FreeQ[Elaborate @ {pre}, Ket[_Association]]

qCircuitOperate[op_Measurement, post___] :=
  Multiply[qCircuitOperate[post], op]

qCircuitOperate[ op:Except[_Measurement].. ] :=
  Fold[ Garner @ Multiply[#2, #1]&, 1, Elaborate @ {op} ]


qCircuitMatrix::usage = "Based on Matrix[] ..."

qCircuitMatrix[qq:{__?QubitQ}] := Matrix[1, qq]

qCircuitMatrix[pre___, Measurement[op_], post___,  qq:{__?QubitQ}] :=
  Module[
    { mat = Matrix[op, qq] },
    mat = Measurement[mat] @ qCircuitMatrix[pre, qq];
    qCircuitMatrix[post, qq] . mat
   ]

qCircuitMatrix[op:Except[_Measurement].., qq:{__?QubitQ}] := Module[
  { new },
  new = Map[Matrix[#, qq]&] @ Elaborate @ Reverse @ {op};
  Dot @@ new
 ]

(**** </Multiply, ExpressionFor and Matrix on QuantumCircuit> ****)


(**** <QuantumCircuitTrim> ****)

QuantumCircuitTrim::usage = "QuantumCircuitTrim[expr] removes visualization options and Graphics Directives that are not evaluable expressions. Useful to convert QuantumCircuit to an evaluation-ready expression."

SetAttributes[ QuantumCircuitTrim, Listable ];

QuantumCircuitTrim[ HoldPattern @ QuantumCircuit[gg__] ] :=
  Flatten @ QuantumCircuitTrim @ {gg}

QuantumCircuitTrim[ QuissoIn[a__] ]  := Multiply @@ QuantumCircuitTrim[ {a} ]
(* NOTE: Useful to apply Matrix directly to QuantumCircuit.  *)

QuantumCircuitTrim[ _QuissoOut ] = Nothing

QuantumCircuitTrim[ _?OptionQ ] = Nothing

QuantumCircuitTrim[ g_?ComplexQ ] = g (* NOT _?CommutativeQ *)

QuantumCircuitTrim[ g_ ] := Nothing /;
  FreeQ[g, _?QubitQ | _Ket | _ProductState]

QuantumCircuitTrim[ HoldPattern @ Projector[v_, qq_, ___?OptionQ] ] :=
  Dyad[v, v, qq]

QuantumCircuitTrim[ v:ProductState[_Association, ___] ] := Expand[v]

QuantumCircuitTrim[ op_QFT ] := op

QuantumCircuitTrim[ Gate[expr_, ___?OptionQ] ] := expr

QuantumCircuitTrim[ op_Symbol[expr__, ___?OptionQ] ] := op[expr]

QuantumCircuitTrim[ g_ ] := g

(**** </QuantumCircuitTrim> ****)


(**** <User Interface for QuantumCircuit> ****)

(* NOTE: QuantumCircuit has attribute Flat. *)

QuantumCircuit[rest:Except[_?qcKetQ].., Longest[vv__?qcKetQ]] :=
  QuantumCircuit[rest, QuissoOut[vv]]

QuantumCircuit[Longest[vv__?qcKetQ]] :=
  QuantumCircuit @ QuissoIn[vv]

QuantumCircuit[Longest[opts__?OptionQ], rest:Except[_?OptionQ]..] :=
  QuantumCircuit[rest, opts]

QuantumCircuit[a_QuissoOut, bb__QuissoOut] :=
  QuantumCircuit @ QuissoOut[a, bb]

QuantumCircuit[a_QuissoIn, bb__QuissoIn] :=
  QuantumCircuit @ QuissoIn[a, bb]

QuantumCircuit[rest__, in_QuissoIn] :=
  QuantumCircuit[in, rest]

QuantumCircuit[out_QuissoOut, rest:Except[_?OptionQ|_QuissoOut]..] :=
  QuantumCircuit[rest, out]

qcKetQ[expr_] := And[
  FreeQ[expr, _QuissoIn | _QuissoOut | _Projector],
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
      cc = qCircuitGate @ {gg},
      vv, ww, xx, yy, nodes, lines, in, out, unit },

    {vv, ww, unit, port} = {
      {"Visible"}, {"Invisible"},
      "UnitLength", "PortSize"
     } /. {opts} /. Options[QuantumCircuit];

    If[ ListQ[port], Null, port = {port, port} ];

    vv = FlavorNone @ Flatten @ vv;
    ww = FlavorNone @ Flatten @ ww;
    ss = Union @ Flatten @ {ss, vv, ww};

    If[ cc == {}, cc = {"Spacer"} ];
    (* There can be only input elements. *)
    
    xx  = Accumulate @ Boole[ qGateQ /@ cc ];
    xx *= $CircuitUnit;
    $CircuitSize = $CircuitUnit + Max[xx];
    
    yy = Range[ Length @ ss ] $CircuitUnit;
    yy = AssociationThread[ss, -yy];
    
    nodes = qCircuitNodes[ cc, xx, yy ];
    lines = qCircuitLines[ cc, xx, KeyDrop[yy, ww] ];
    
    in = FirstCase[ {gg}, QuissoIn[kk___] :> {kk} ];
    in = qCircuitInput[in, xx, yy];

    out = FirstCase[ {gg}, QuissoOut[kk___] :> {kk} ];
    out = qCircuitOutput[out, xx, yy];

    Graphics[ Join[lines, in, nodes, out],
      Sequence @@ FilterRules[{opts}, Options @ Graphics],
      more,
      PlotRange -> {Full, MinMax[yy] + {-1, 1}*$CircuitUnit/2},
      ImagePadding -> { unit*port, {1, 1} },
      ImageSize -> unit * ($CircuitSize + Total[port])
     ]
   ]

qGateQ::usage = "qGateQ[expr] is True if expr is an expression of operators."

qGateQ[expr_] := Not @ FreeQ[expr, _?QubitQ | "Separator" | "Spacer" ]
(* Recall that FreeQ[ Ket[<|...|>], _?QubitQ] = True . *)


qCircuitGate::usage = "qCircuitGate[expr, opts] preprocesses various circuit elements."

qCircuitGate::unknown = "Unknown quantum circuit element ``."

(* NOTE: DO NOT set Listable attribute for qCircuitGate. *)

Options[qCircuitGate] = {
  "TargetFunction"  -> "Rectangle",
  "ControlFunction" -> "Dot",
  "LabelSize" -> 1, (* RELATIVE size *)
  "Label" -> None
 }


qCircuitGate[{gg__, opts___?OptionQ}] :=
  Map[qCircuitGate[#, opts]&, {gg}]

qCircuitGate[gg_List, opts___?OptionQ] :=
  Map[qCircuitGate[#, opts]&, gg]


qCircuitGate[ _QuissoIn | _QuissoOut, opts___?OptionQ ] = Nothing
  

qCircuitGate[ S_Symbol?QubitQ[j___, k_Integer?Negative], opts___?OptionQ ] :=
  Gate[
    {S[j,None]}, opts,
    "Label" -> qGateLabel[S[j,k]],
    "LabelSize" -> 0.5
   ]

qCircuitGate[ S_?QubitQ, opts___?OptionQ ] :=
  Gate[ Qubits @ S, opts, "Label" -> qGateLabel[S] ]

qCircuitGate[ HoldPattern @ Dagger[S_?QubitQ], opts___?OptionQ ] :=
  Gate[ Qubits @ S, opts, "Label" -> Superscript[qGateLabel[S],"\[Dagger]"] ]

qCircuitGate[ HoldPattern @ Multiply[ss__?QubitQ], opts___?OptionQ ] :=
  Map[ qCircuitGate[#, opts]&, {ss} ]

qCircuitGate[ Measurement[ss:{__?fPauliOpQ}], opts___?OptionQ ] :=
  Map[ qCircuitGate[Measurement[#], opts]&, ss ]

qCircuitGate[ Measurement[S_?QubitQ], opts___?OptionQ ] :=
  Gate[
    {FlavorMute @ S},
    "TargetFunction" -> "Measurement",
    opts,
    "Label" -> qMeasurementLabel[S]
   ]

qCircuitGate[
  HoldPattern @ Measurement[Multiply[ss__?QubitQ]], opts___?OptionQ ] :=
  Gate[
    FlavorMute @ {ss},
    "TargetFunction" -> "Measurement",
    opts,
    "Label" -> qMeasurementLabel @ {ss}
   ]

qCircuitGate[
  HoldPattern @ Projector[v_, qq_, opts___?OptionQ], more___?OptionQ ] :=
  Gate[ qq, "TargetFunction" -> "Projector", "Label" -> None, opts, more ]

qCircuitGate[
  Phase[ ang_, G_?QubitQ, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ Qubits @ G, opts, more, "Label" -> qGateLabel[ Phase[ang, G] ] ]

qCircuitGate[
  Rotation[ ang_, G_?QubitQ, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ Qubits @ G, opts, more, "Label" -> qGateLabel[ Rotation[ang, G] ] ]

qCircuitGate[
  EulerRotation[ ang:{_,_,_}, G_?QubitQ, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ {G}, opts, more, "Label" -> qGateLabel[ EulerRotation[ang, G] ] ]


qCircuitGate[
  ControlledU[ cc:{__?QubitQ}, S_?QubitQ, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ cc, Qubits @ S, opts, more, "Label" -> qGateLabel[S] ]

qCircuitGate[
  ControlledU[
    cc:{__?QubitQ},
    op:(Phase|Rotation|EulerRotation)[j__, opts___?OptionQ],
    more___?OptionQ ],
  rest___?OptionQ ] :=
  Gate[ cc, Qubits @ op, opts, more, rest, "Label" -> qGateLabel[op] ]

qCircuitGate[
  ControlledU[
    cc:{__?QubitQ},
    HoldPattern @ Multiply[ss__?QubitQ],
    opts___?OptionQ ],
  more___?OptionQ ] :=
  Sequence @@ Map[qCircuitGate[ControlledU[cc, #], opts, more]&, {ss}]

qCircuitGate[
  ControlledU[ cc:{__?QubitQ}, expr_, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ cc, Qubits[expr], opts, more ] /; Not @ FreeQ[expr, _?QubitQ]


qCircuitGate[ CNOT[cc:{__?QubitQ}, tt:{__?QubitQ}], opts___?OptionQ ] :=
  Gate[ cc, tt, "TargetFunction" -> "CirclePlus" ]

qCircuitGate[ Toffoli[a_?QubitQ, b__?QubitQ, c_?QubitQ], opts___?OptionQ ] :=
  Gate[ {a, b}, {c}, "TargetFunction" -> "CirclePlus" ]


qCircuitGate[ CZ[cc:{__?QubitQ}, tt:{__?QubitQ}], opts___?OptionQ ] :=
  Sequence @@ Map[qcgCZ[cc, #, opts]&, tt]

qcgCZ[ cc:{__?QubitQ}, t_?QubitQ, opts___?OptionQ ] :=
  Gate[ cc, {t}, "ControlFunction" -> "Dot", "TargetFunction" -> "Dot" ]


qCircuitGate[ SWAP[c_?QubitQ, t_?QubitQ], opts___?OptionQ ] :=
  Gate[ {c}, {t},
    "ControlFunction" -> "Cross",
    "TargetFunction" -> "Cross"
   ]

qCircuitGate[ Fredkin[a_?QubitQ, b_?QubitQ, c_?QubitQ], opts___?OptionQ ] :=
  Gate[ {a}, {b, c},
    "ControlFunction" -> "Dot",
    "TargetFunction" -> "Cross"
   ]

qCircuitGate[
  Deutsch[ph_, {a_?QubitQ, b_?QubitQ, c_?QubitQ}, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ {a, b}, {c}, opts, more, "Label" -> "D" ]


qCircuitGate[
  Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := qCircuitGate @ Oracle[f, cc, tt, opts, more]

qCircuitGate @ Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  Gate[ cc, tt, opts,
    "ControlFunction" -> "Oval",
    "TargetFunction" -> "CirclePlus",
    "Label" -> "f" ]


qCircuitGate[
  QFT[qq:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := qCircuitGate @ QFT[qq, opts, more]

qCircuitGate[ QFT[qq:{__?QubitQ}, opts___?OptionQ] ] :=
  Module[
    { more = Join[{opts}, Options @ QFT],
      lbl, ang },
    { lbl, ang } = {"Label", "LabelRotation"} /. more;
    Gate[qq, "Label" -> Rotate[lbl, ang], Sequence @@ more]
   ]

qCircuitGate[
  HoldPattern @
    Dagger @ QFT[qq:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := qCircuitGate @ Dagger @ QFT[qq, opts, more]

qCircuitGate[
  HoldPattern @
    Dagger @ QFT[qq:{__?QubitQ}, opts___?OptionQ]
 ] := Module[
   { more = Join[{opts}, Options @ QFT],
     lbl, ang },
   { lbl, ang } = {"Label", "LabelRotation"} /. more;
   Gate[qq, "Label" -> Rotate[SuperDagger[lbl], ang], Sequence @@ more]
  ]


qCircuitGate[ expr:Except[_List|_?(FreeQ[#,_?QubitQ]&)], opts___?OptionQ ] :=
  Gate[ Qubits @ expr, opts ]

qCircuitGate[ z_?NumericQ, ___?OptionQ ] := "Spacer"

qCircuitGate[ gate:("Separator" | "Spacer"), ___?OptionQ ] := gate


qCircuitGate[ expr_, ___?OptionQ ] := expr /; FreeQ[expr, _?QubitQ]
(* Graphics primitives corresponds to this case. *)


qMeasurementLabel::usage = "qMeasurementLabel[op] returns the default label of the measurement operator op (only Pauli operators allowed)."

qMeasurementLabel[op_Multiply] := Map[qMeasurementLabel, List @@ op]

qMeasurementLabel[ss:{___?QubitQ}] := qMeasurementLabel /@ ss

qMeasurementLabel[S_?QubitQ] :=
  FlavorLast[S] /. {0 -> "I", 1 -> "X", 2 -> "Y", 3 -> None, _ -> "?"}


qGateLabel::usage = "qGateLabel[G] returns the label of the circuit element to be displayed in the circuit diagram."

SetAttributes[qGateLabel, Listable];

qGateLabel[ _Symbol?QubitQ[___, n_Integer?Negative] ] :=
  DisplayForm @ FractionBox[Row @ {2, Pi}, SuperscriptBox[2, -n]] 

qGateLabel[ S_?QubitQ ] := Last[S] /. {
  0 -> "I",
  1 -> "X", 2 -> "Y", 3 -> "Z",
  6 -> "H", 7 -> "S", 8 -> "T" }

qGateLabel[ gate_Phase ] := "\[Phi]"

qGateLabel[ Rotation[_, S_?QubitQ, ___] ] :=
  Subscript[ "U", FlavorLast[S] /. {1->"x", 2->"y", 3->"z"} ]

qGateLabel[ EulerRotation[{_, _, _}, S_?QubitQ, ___] ] := Subscript["U", "E"]


qDrawGateCirclePlus[ x_, yy_List, ___ ] :=
  qDrawGateCirclePlus @@@ Thread @ {x, yy}

qDrawGateCirclePlus[ x_, y_?NumericQ, ___ ] := Module[
  { circ, crss },
  circ = Circle[ {x, y}, $GateSize / 3 ];
  crss = Line[ {
      { {x-$GateSize/3,y}, {x+$GateSize/3,y} },
      { {x,y-$GateSize/3}, {x,y+$GateSize/3} }
     } ];
  { circ, crss }
 ]


qDrawGateCross[x_, yy_List, ___] := qDrawGateCross @@@ Thread @ {x, yy}

qDrawGateCross[x_, y_, ___] := List @ Line[{
    { {x,y}+{-1,-1}$DotSize, {x,y}+{+1,+1}$DotSize },
    { {x,y}+{-1,+1}$DotSize, {x,y}+{+1,-1}$DotSize }
   }]


qDrawGateMeasurement[ x_, {y_}, opts___?OptionQ ] :=
  qDrawGateMeasurement[x, y, opts]

qDrawGateMeasurement[ x_, yy:{_, __}, opts___?OptionQ ] := Module[
  { cc, mm, tt, rest },

  tt = "Label" /. {opts} /. Options[qCircuitGate];
  rest = Normal @ KeyDrop[{opts}, "Label"];
  mm = MapThread[
    qDrawGateMeasurement[x, #1, "Label" -> #2, opts]&,
    {yy, tt}
   ];

  cc = {
    Line @ Thread @ {x-$DotSize/2, yy},
    Line @ Thread @ {x+$DotSize/2, yy}
   };

  { cc, mm }
 ]

qDrawGateMeasurement[ x_, y_, opts___?OptionQ ] := Module[
  { pane, text, arc, needle },

  pane = qDrawGateRectangle[x, y];
  text = qMeasurementText[x, y, opts];
  
  arc = Circle[ {x, y - 0.25 $GateSize}, .5 $GateSize, {1,5} Pi/6 ];
  needle = Line[{ {x, y - 0.25 $GateSize}, {x,y} + .3{1,1}$GateSize }];
  
  { pane, text, arc, needle }
 ]


qDrawGateProjector[ x_, yy_List, ___ ] := Module[
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


qDrawGateDot[ x_, yy_List, ___ ] := qDrawGateDot @@@ Thread @ {x, yy}

qDrawGateDot[ x_, y_?NumericQ, ___ ] := Disk[ {x, y}, $DotSize ]

qDrawGateRectangle[ x_, yy_List, opts___?OptionQ ] := Module[
  { y1 = Min @ yy,
    y2 = Max @ yy,
    pane, line, text },
  text = qGateText[x, Mean @ {y1, y2}, opts];
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

qDrawGateRectangle[ x_, y_?NumericQ, opts___?OptionQ ] :=
  qDrawGateRectangle[x, {y}, opts]


qDrawGateOval[ x_, y_?NumericQ, opts___?OptionQ ] := Module[
  { pane, text},
  text = qGateText[x, y, opts];
  pane = Disk[{x, y}, $GateSize/2];
  { {EdgeForm[Black], White, pane}, text }
 ]

qDrawGateOval[ x_, yy_List, opts___?OptionQ ] := Module[
  { x1 = x - $GateSize/2,
    x2 = x + $GateSize/2,
    y1 = Min @ yy,
    y2 = Max @ yy,
    y0, y3, ff, pane, text},
  
  text = qGateText[x, Mean @ {y1, y2}, opts];

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


qGateText[ x_, y_, opts___?OptionQ ] := Module[
  { label, factor },
  { label, factor } = { "Label", "LabelSize" } /.
    {opts} /. Options[qCircuitGate];
  If[ label == None, Return @ Nothing ];
  Text[
    Style[ label, Italic,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitSize) factor] ],
    {x, y},
    {0, 0}
    (* Notice the y-offset:
       Before v12.2, y-offset=0 shifted a bit upward.
       It seems different in v12.2. *)
   ]
 ]

qMeasurementText[ x_, y_, opts___?OptionQ ] := Module[
  { label, factor },
  { label, factor } = { "Label", "LabelSize" } /.
    {opts} /. Options[qCircuitGate];
  If[ label == None, Return @ Nothing ];
  Text[
    Style[ label, Italic,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitSize) factor] ],
    {x + 0.65 $GateSize, y},
    {-1, -1}
   ]
 ]


SetAttributes[qDrawGateSymbol, Listable]

qDrawGateSymbol[name_?StringQ] :=
  Symbol["Q3`Private`" <> "qDrawGate" <> name] /;
  MemberQ[
    { "Dot", "CirclePlus", "Projector", "Measurement",
      "Rectangle", "Oval", "Cross" },
    name
   ]

qDrawGateSymbol[name_?StringQ] := (
  Message[QuantumCircuit::nofunc, name];
  qDrawGateSymbol["Rectangle"]
 )


qCircuitNodes::usage = "qCircuitNodes[ ... ] takes circuit elements and construct them as nodes of the circuit diagram by assigning horizontal and vertical coordinates to them."

qCircuitNodes[ gg_List, xx_List, yy_Association ] := Module[
  { ff, F },
  
  ff = Thread[ F[ gg, xx, yy ] ];
  ff = ff /. { F -> qDrawGate };

  Return[ff];
 ]

qDrawGate::uage = "Renders the gates."

qDrawGate[ gg_List, x_, yy_Association ] := Map[ qDrawGate[#, x, yy]&, gg ]

qDrawGate[
  Gate[cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ],
  x_, yy_Association
 ] := Module[
   { yc = Lookup[yy, cc],
     yt = Lookup[yy, tt],
     control, target, dots, link, pane },

   { control, target } = qDrawGateSymbol[
     { "ControlFunction", "TargetFunction" } /. {opts} /.
       Options[qCircuitGate]
    ];
   
   link = Line @ Join[ Thread @ {x, yc}, Thread @ {x, yt} ];
   
   dots = control[x, yc, opts];
   pane = target[x, yt, opts];
   
   Join[{link}, dots, pane]
  ]


qDrawGate[ Gate[tt:{__?QubitQ}, opts___?OptionQ], x_, yy_Association ] :=
  Module[
    { yt = Lookup[yy, tt],
      target },
    
    target = qDrawGateSymbol[
      "TargetFunction" /. {opts} /. Options[qCircuitGate]
     ];

    target[x, yt, opts]
   ]


qDrawGate[ "Spacer", _, _Association ] = Nothing

qDrawGate[ "Separator", x_, yy_Association ] := Module[
  { xy = Tuples[{{x}, MinMax @ yy }] },
  { Dotted,
    Line @ {
      {0,-$CircuitUnit/2} + First @ xy,
      {0,+$CircuitUnit/2} + Last @ xy }
   }
 ]

qDrawGate[ g_, x_, yy_Association ] := g


qCircuitLines::usage = "qCircuitLines[gg, x, y] finds when Measurement occurs in the QuantumCircuit and renders the qubit line after Measurement in dashes."

qCircuitLines[ gg_List, xx_List, yy_Association ] := Module[
  { mm, zz, dashed, plain },
  mm = Map[
    Cases[{#}, Gate[{S_?QubitQ}, "TargetFunction" -> "Measurement", ___?OptionQ] -> S, Infinity]&,
    gg
   ];
  mm = Flatten[ Thread /@ Thread[mm -> xx] ];
  mm = KeySort @ KeyTake[Association @ mm, Keys @ yy];
  
  zz = Lookup[yy, Keys @ mm];
  dashed = Line @ Transpose @ {
    Thread[ {Values @ mm, zz} ],
    Thread[ {1+Max[xx], zz} ] };

  plain = Association @ Thread[ Keys[yy] -> 1+Max[xx] ];
  plain = Join[ plain, mm ];
  plain = Line @ Transpose @ {
    Thread[{0, Values @ yy}],
    Transpose @ {Values @ plain, Values @ yy} };

  {{Dashed, dashed}, plain}
 ]


qCircuitOutput::usage = "It draws the output states behind the scene."

qCircuitOutput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitOutput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{$CircuitSize + $InOutOffset, #}&, yy],
    ff = List @ qCircuitPort @ gg },
  Map[qDrawPort[#, xy]&, ff]
 ]


qCircuitInput::usage = "It draws the input states behind the scene."

qCircuitInput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitInput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{-$InOutOffset, #}&, yy],
    ff },
  
  ff = Join[gg, {"Pivot" -> {1, 0}, "Type" -> -1} ];
  ff = List @ qCircuitPort @ ff;

  Map[qDrawPort[#, xy]&, ff]
 ]


qCircuitPort::usage = "qCircuitPorts preprocesses various input and output forms of QuantumCircuit."

Options[ qCircuitPort ] = {
  "Label" -> Automatic,
  "LabelSize" -> 1, (* RELATIVE *)
  "Pivot" -> {-1, 0},
  "Type"  -> 1 (* 1: input, -1: output *)
 }

qCircuitPort[ v_Ket, opts___?OptionQ ] := Port[v, opts]

qCircuitPort[ v_ProductState, opts___?OptionQ ] := Port[v, opts]

qCircuitPort[ expr:Except[_List], opts___?OptionQ ] :=
  Port[expr, opts] /; Not @ FreeQ[expr, _Ket]

qCircuitPort[ a_List, opts___?OptionQ ] := qCircuitPort @@ Join[a, {opts}]

qCircuitPort[ g_, opts___?OptionQ ] := g /; FreeQ[g, _Ket | _ProductState]

qCircuitPort[ a_, b__, opts___?OptionQ ] :=
  Map[ qCircuitPort[#, opts]&, {a, b} ]


qDrawPort::usage = "qDrawPort renders the input/output ports."

qDrawPort[ gg_List, xy_Association ] := Map[ qDrawPort[#, xy]&, gg ]

qDrawPort[ Port[ Ket[v_], opts___?OptionQ ], xy_Association ] := Module[
  { vv = Ket /@ v,
    tt, label, pivot },
  { label, pivot } = {"Label", "Pivot"} /. {opts} /. Options[qCircuitPort];

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
    qPortText[#1, #2, pivot, opts]&,
    KeyIntersection @ {tt, xy}
   ]
 ]

qDrawPort[
  Port[ ProductState[v_Association, opts___], more___?OptionQ ],
  xy_Association
 ] := Module[
   { label, pivot, tt },
   { label, pivot } = {"Label", "Pivot"} /. {opts, more} /.
     Options[qCircuitPort];

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
     qPortText[#1, #2, pivot, opts, more]&,
     KeyIntersection @ {tt, xy}
    ]
  ]

qDrawPort[ Port[ expr_, opts___?OptionQ ], xy_Association ] := (
  Message[QuantumCircuit::noqubit, expr];
  Return @ {};
 ) /; Qubits[expr] == {}

qDrawPort[ Port[ expr_, opts___?OptionQ ], xy_Association ] := Module[
  { qq = Qubits @ expr,
    label, pivot, dir, brace, text, zz },

  { label, pivot, dir } = { "Label", "Pivot", "Type" } /.
    {opts} /. Options[qCircuitPort];

  If[ label === None, Return @ {} ];
  
  text = If[label === Automatic, SimpleForm[expr, qq], label];
  
  zz = Transpose[ MinMax /@ Transpose @ Lookup[xy, qq] ];

  If[ Length[qq] > 1,
    brace = qPortBrace[dir, zz];
    zz = Mean @ zz + ($InOutOffset + $BraceWidth) {dir, 0};
    { brace, qPortText[text, zz, pivot, opts] },
    qPortText[text, Mean @ zz, pivot, opts]
   ]
 ]

qDrawPort[ g_, xy_Association ] := g


qPortText[text_, pt:{_, _}, pivot:{_, _}, opts___?OptionQ] := Module[
  { factor },
  factor = "LabelSize" /. {opts} /. Options[qCircuitPort];
  Text[
    Style[
      text,
      FontWeight -> "Light",
      FontSize -> Scaled[(0.4 $GateSize / $CircuitSize) factor]
     ],
    pt, pivot
   ]
 ]

qPortBrace[-1, { a:{_, _}, b:{_, _} } ] :=
  LeftBrace[a, b, "Width" -> $BraceWidth]

qPortBrace[+1, { a:{_, _}, b:{_, _} } ] :=
  RightBrace[a, b, "Width" -> $BraceWidth]

End[]

EndPackage[]
