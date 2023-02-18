(* -*- mode: math; -*- *)

BeginPackage["Q3`"]

`Quville`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 2.13 $"][[2]], " (",
  StringSplit["$Date: 2023-02-18 18:33:57+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ QuantumCircuit,
  QuantumCircuitIn,
  QuantumCircuitOut,
  QuantumCircuitTrim };

(* Obsolete Symbols *)

Begin["`Private`"]

QuantumCircuit::usage = "QuantumCircuit[a, b, ...] represents the quantum circuit model consisting of the gate operations a, b, ..., and it is displayed the circuit in a graphical form.\nExpressionFor[ QuantumCircuit[...] ] takes the non-commutative product of the elements in the quantum circuit; namely, converts the quantum circuit to a operator or vector expression.\nMatrix[ QuantumCircuit[...] ] returns the matrix representation of the quantum circuit model."

QuantumCircuit::noqubit = "No Qubit found in the expression ``. Use LogicalForm to specify the Qubits explicitly."

QuantumCircuit::nofunc = "Unknown function \"``\" to draw the gate. \"Rectangle\" is assumed."

QuantumCircuit::ket = "`` is not a proper ket of the form Ket[<|...|>] or ProductState[<|...|>]."

QuantumCircuitIn::usage = "QuantumCircuitIn is a holder for input expression in QuantumCircuit.\nSee also QuantumCircuitOut."

QuantumCircuitOut::usage = "QuantumCircuitOut is a holder for expected output expressions in QuantumCircuit. Note that the output expressions are just expected output and may be different from the actual output. They are used only for output label and ignored by ExpressionFor and Elaborate.\nSee also QuantumCircuitIn."

SetAttributes[{QuantumCircuit, QuantumCircuitOut, QuantumCircuitIn}, Flat]

AddElaborationPatterns[_QuantumCircuit]

Options[QuantumCircuit] = {
  "TargetFunction" -> "Rectangle",
  "ControlFunction" -> "Dot",
  "UnitLength" -> 36, (* 72 is a good choice for presentation *)
  "PortSize" -> 0.65,
  "LabelSize" -> 1, (* RELATIVE size *)
  "Label" -> None,
  "Visible" -> {},
  "Invisible" -> {}
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
Qubits @ QuantumCircuit[gg__, ___?OptionQ] := Union[
  Qubits @ {gg},
  FlavorNone @ OptionValue[QuantumCircuit, "Visible"]
 ]

QuantumCircuit /:
Measurements[qc:QuantumCircuit[__, ___?OptionQ]] :=
  Measurements[QuantumCircuitTrim @ qc]


(**** <Multiply> ****)

QuantumCircuit /:
NonCommutativeQ[ QuantumCircuit[__] ] = True

QuantumCircuit /:
Kind[ QuantumCircuit[__] ] = NonCommutative

QuantumCircuit /:
MultiplyGenus[ QuantumCircuit[__] ] := "QuantumCircuit"


QuantumCircuit /:
Multiply[pre___, QuantumCircuit[elm__], post___] :=
  Multiply[pre, Elaborate @ QuantumCircuit[Reverse @ {post}, elm]]
(* NOTE: {elm} may include Measurement. *)

QuantumCircuit /:
Multiply[pre___, Longest[cc__QuantumCircuit], post___] :=
  Multiply[pre, Elaborate @ Apply[QuantumCircuit, Reverse @ {cc}], post]

(**** </Multiply> ****)


(**** <ExpressionFor> ****)

QuantumCircuit /:
ExpressionFor[ qc_QuantumCircuit ] := Elaborate[ qc ]

QuantumCircuit /:
Elaborate @ QuantumCircuit[gg__, ___?OptionQ] := Module[
  { expr = Flatten @ QuantumCircuitTrim @ {gg} },
  Garner[ qCircuitOperate @@ expr ]
 ]
(* NOTE: This makes the evaluation much faster, especially, when the initial
   state is specified in the circuit. *)


qCircuitOperate[] = 1

qCircuitOperate[pre__, op_Measurement, post___] := 
  qCircuitOperate[op @ qCircuitOperate[pre], post] /;
  Not @ FreeQ[Elaborate @ {pre}, Ket[_Association]]

qCircuitOperate[op_Measurement, post___] :=
  Multiply[qCircuitOperate[post], op]

qCircuitOperate[op:Except[_Measurement]..] :=
  Elaborate @ Fold[ Garner[Multiply[#2, #1]]&, 1,  {op} ]
(* NOtE: This is another method:
   Fold[ Garner[Multiply[#2, #1]]&, 1,  Elaborate @ {op} ]
   However, this cannot take the advantange of op ** Ket[...]. *)

qCircuitOperate[gg__] := MeasurementFunction[{gg}]

(**** </ExpressionFor> ****)



(**** <Matrix> ****)

QuantumCircuit /:
Matrix[ qc:QuantumCircuit[gg__, ___?OptionQ] ] := Module[
  { ff },
  ff = SplitBy[
    Flatten @ QuantumCircuitTrim @ {gg},
    MatchQ[_Measurement]
   ];
  Apply[qCircuitMatrix, MapApply[Dot, Reverse /@ Matrix[ff, Qubits @ qc]]]
 ]

qCircuitMatrix[v_?VectorQ] = v

qCircuitMatrix[m_?MatrixQ] = m

qCircuitMatrix[m_Measurement] = m

qCircuitMatrix[v_?VectorQ, M_Measurement, rest___] :=
  qCircuitMatrix[M[v], rest]

qCircuitMatrix[v_?VectorQ, m_?MatrixQ, rest___] :=
  qCircuitMatrix[m.v, rest]

qCircuitMatrix[gg__] := MeasurementFunction[{gg}]

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
  FreeQ[g, _?QubitQ | _Ket | _ProductState]

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
      cc = qcGate @ {gg},
      vv, ww, xx, yy, nodes, lines, in, out, unit },

    {vv, ww, unit, port} = {
      {"Visible"}, {"Invisible"},
      "UnitLength", "PortSize"
     } /. {opts} /. Options[QuantumCircuit];

    If[ ListQ[port], Null, port = {port, port} ];

    vv = FlavorNone @ Flatten @ vv;
    ww = FlavorNone @ Flatten @ ww;
    ss = Union @ Flatten @ {ss, vv, ww};

    If[cc == {}, cc = {"Spacer"}];
    (* There can be only input elements. *)
    
    xx  = Accumulate @ Boole[ quvGateQ /@ cc ];
    xx *= $CircuitUnit;
    $CircuitSize = $CircuitUnit + Max[xx];
    
    yy = Range[ Length @ ss ] $CircuitUnit;
    yy = AssociationThread[ss, -yy];
    
    nodes = qcNodes[ cc, xx, yy ];
    lines = qcLines[ cc, xx, KeyDrop[yy, ww] ];

    in = FirstCase[ {gg}, QuantumCircuitIn[kk___] :> {kk} ];
    in = qCircuitInput[in, xx, yy];

    out = FirstCase[ {gg}, QuantumCircuitOut[kk___] :> {kk} ];
    out = qCircuitOutput[out, xx, yy];

    Graphics[ Join[lines, in, nodes, out],
      Sequence @@ FilterRules[{opts}, Options @ Graphics],
      more,
      PlotRange -> {Full, MinMax[yy] + {-1, 1}*$CircuitUnit/2},
      ImagePadding -> { unit*port, {1, 1} },
      ImageSize -> unit * ($CircuitSize + Total[port])
     ]
   ]

quvGateQ::usage = "quvGateQ[expr] is True if expr is an expression of operators."

quvGateQ[expr_] := Not @ FreeQ[expr, _?QubitQ | "Separator" | "Spacer" ]
(* Recall that FreeQ[ Ket[<|...|>], _?QubitQ] = True . *)


qcGate::usage = "qcGate[expr, opts] preprocesses various circuit elements."

qcGate::unknown = "Unknown quantum circuit element ``."

(* NOTE: DO NOT set Listable attribute for qcGate. *)

qcGate[{gg__, opts___?OptionQ}] :=
  Map[qcGate[#, opts]&, {gg}]

qcGate[gg_List, opts___?OptionQ] :=
  Map[qcGate[#, opts]&, gg]


qcGate[ _QuantumCircuitIn | _QuantumCircuitOut, opts___?OptionQ ] = Nothing
  

qcGate[ op_?QubitQ, opts___?OptionQ ] :=
  Gate[ Qubits @ op, opts, "Label" -> HoldForm[thePauliForm @ op] ]
(* NOTE: HoldForm is required here because later qcNodes uses HoldRelease. *)

(* NOTE: This case should not occur. *)
(*
qcGate[ HoldPattern @ Dagger[S_?QubitQ], opts___?OptionQ ] :=
  Gate[ Qubits @ S, opts, "Label" -> HoldForm @ thePauliForm[Dagger @ S] ]
 *)

qcGate[ HoldPattern @ Multiply[ss__?QubitQ], opts___?OptionQ ] :=
  Map[ qcGate[#, opts]&, {ss} ]

qcGate[ Measurement[ss:{__?PauliQ}], opts___?OptionQ ] :=
  Map[ qcGate[Measurement[#], opts]&, ss ]

qcGate[ Measurement[S_?QubitQ], opts___?OptionQ ] :=
  Gate[
    {FlavorMute @ S},
    "TargetFunction" -> "Measurement",
    opts,
    "Label" -> measurementLabel[S]
   ]

qcGate[
  HoldPattern @ Measurement[Multiply[ss__?QubitQ]], opts___?OptionQ ] :=
  Gate[
    FlavorMute @ {ss},
    "TargetFunction" -> "Measurement",
    opts,
    "Label" -> measurementLabel @ {ss}
   ]

qcGate[
  HoldPattern @ Projector[v_, qq_, opts___?OptionQ], more___?OptionQ ] :=
  Gate[ qq, "TargetFunction" -> "Projector", "Label" -> None, opts, more ]

qcGate[
  op:Phase[_, _?QubitQ, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ Qubits @ op, opts, more, "Label" -> HoldForm @ thePauliForm[op] ]

qcGate[
  Rotation[ang_, G_?QubitQ, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ Qubits @ G, opts, more, "Label" -> gateLabel @ Rotation[ang, G] ]

qcGate[
  EulerRotation[ ang:{_,_,_}, G_?QubitQ, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ {G}, opts, more, "Label" -> gateLabel[ EulerRotation[ang, G] ] ]


qcGate[
  ControlledGate[ rr_Rule, S_?QubitQ, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ rr, Qubits @ S, opts, more,
    "Label" -> {None, gateLabel[S]} ]

qcGate[
  ControlledGate[
    Rule[cc:{__?QubitQ}, vv:{__?BinaryQ}],
    op:(Phase|Rotation|EulerRotation)[__, opts___?OptionQ],
    more___?OptionQ ],
  rest___?OptionQ ] :=
  Gate[ cc -> vv, Qubits @ op, opts, more, rest,
    "Label" -> {None, gateLabel[op]} ]

qcGate[
  ControlledGate[
    Rule[cc:{__?QubitQ}, vv:{__?BinaryQ}],
    HoldPattern @ Multiply[ss__?QubitQ],
    opts___?OptionQ ],
  more___?OptionQ ] :=
  Sequence @@ Map[qcGate[ControlledGate[cc->vv, #], opts, more]&, {ss}]

qcGate[
  ControlledGate[ Rule[cc:{__?QubitQ}, vv_], expr_, opts___?OptionQ ],
  more___?OptionQ ] :=
  Gate[ cc->vv, Qubits[expr], opts, more ] /;
  Not @ FreeQ[expr, _Dyad|_?QubitQ]


qcGate[ CNOT[Rule[cc:{__?QubitQ}, vv_], tt:{__?QubitQ}], opts___?OptionQ ] :=
  Gate[ cc -> vv, tt, "TargetFunction" -> "CirclePlus" ]


qcGate[ Toffoli[a_?QubitQ, b__?QubitQ, c_?QubitQ], opts___?OptionQ ] :=
  Gate[ {a, b} -> {1, 1}, {c}, "TargetFunction" -> "CirclePlus" ]


qcGate[ CZ[cc:{__?QubitQ}, tt:{__?QubitQ}], ___?OptionQ ] :=
  Sequence @@ Map[
    Gate[cc, {#}, "ControlFunction" -> "Dot", "TargetFunction" -> "Dot"]&,
    tt
   ]


qcGate[ SWAP[c_?QubitQ, t_?QubitQ], opts___?OptionQ ] :=
  Gate[ {c}, {t},
    "ControlFunction" -> "Cross",
    "TargetFunction" -> "Cross"
   ]

qcGate[ Fredkin[a_?QubitQ, b_?QubitQ, c_?QubitQ], opts___?OptionQ ] :=
  Gate[ {a}, {b, c},
    "ControlFunction" -> "Dot",
    "TargetFunction" -> "Cross"
   ]

qcGate[
  Deutsch[ph_, {a_?QubitQ, b_?QubitQ, c_?QubitQ}, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ {a, b}, {c}, opts, more, "Label" -> "D" ]


qcGate[
  Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := qcGate @ Oracle[f, cc, tt, opts, more]

qcGate @ Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  Gate[ cc, tt, opts,
    "ControlFunction" -> "Oval",
    "TargetFunction" -> "CirclePlus",
    "Label" -> "f" ]


qcGate[
  ControlledExp[cc:{__?QubitQ}, op_, opts___?OptionQ],
  more__?OptionQ
 ] := qcGate @ ControlledExp[cc, op, opts, more]

qcGate @ ControlledExp[cc:{__?QubitQ}, op_, opts___?OptionQ] :=
  Gate[ cc, Qubits[op],
    "Label" -> gateLabel[ControlledExp[cc, op, opts]],
    opts,
    "ControlFunction" -> "Oval",
    "TargetFunction" -> "Rectangle"
   ]


qcGate[
  QFT[qq:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := qcGate @ QFT[qq, opts, more]

qcGate[ QFT[qq:{__?QubitQ}, opts___?OptionQ] ] :=
  Module[
    { more = Join[{opts}, Options @ QFT],
      lbl, ang },
    { lbl, ang } = {"Label", "LabelRotation"} /. more;
    Gate[qq, "Label" -> Rotate[lbl, ang], Sequence @@ more]
   ]

qcGate[
  HoldPattern @ Dagger @ QFT[qq:{__?QubitQ}, opts___?OptionQ],
  more__?OptionQ
 ] := qcGate @ Dagger @ QFT[qq, opts, more]

qcGate[
  HoldPattern @ Dagger @ QFT[qq:{__?QubitQ}, opts___?OptionQ]
 ] := Module[
   { more = Join[{opts}, Options @ QFT],
     lbl, ang },
   { lbl, ang } = {"Label", "LabelRotation"} /. more;
   Gate[qq, "Label" -> Rotate[SuperDagger[lbl], ang], Sequence @@ more]
  ]


qcGate[ expr:Except[_List|_?(FreeQ[#,_?QubitQ]&)], opts___?OptionQ ] :=
  Gate[ Qubits @ expr, opts ]

qcGate[ z_?NumericQ, ___?OptionQ ] := "Spacer"

qcGate[ gate:("Separator" | "Spacer"), ___?OptionQ ] := gate


qcGate[ expr_, ___?OptionQ ] := expr /; FreeQ[expr, _?QubitQ]
(* Graphics primitives corresponds to this case. *)


measurementLabel::usage = "measurementLabel[op] returns the default label of the measurement operator op (only Pauli operators allowed)."

measurementLabel[op_Multiply] := Map[measurementLabel, List @@ op]

measurementLabel[ss:{___?QubitQ}] := measurementLabel /@ ss

measurementLabel[S_?QubitQ] :=
  FlavorLast[S] /. {0 -> "I", 1 -> "X", 2 -> "Y", 3 -> None, _ -> "?"}


gateLabel::usage = "gateLabel[G] returns the label of circuit element G to be displayed in the circuit diagram."

SetAttributes[gateLabel, Listable];

(* Not used any longer. *)
gateLabel[_Symbol?QubitQ[___, -C[n_]]] :=
  With[{m = -n}, Style[HoldForm[-2 Pi / HoldForm[Power[2, m]]], Small]]
(* NOTE: HoldForm is required here because later qcNodes uses HoldRelease. *)
  
(* Not used any longer. *)
gateLabel[_Symbol?QubitQ[___, C[n_]]] :=
  With[{m = -n}, Style[HoldForm[2 Pi / HoldForm[Power[2, m]]], Small]]
(* NOTE: HoldForm is required here because later qcNodes uses HoldRelease. *)
  
(* Not used any longer. *)
gateLabel[S_?QubitQ] := thePauliForm[S]


gateLabel[ op_Phase ] := thePauliForm[op]

gateLabel[ Rotation[_, S_?QubitQ, ___] ] :=
  Subscript[ "U", FlavorLast[S] /. {1->"x", 2->"y", 3->"z"} ]

gateLabel[ EulerRotation[{_, _, _}, S_?QubitQ, ___] ] := Subscript["U", "E"]

gateLabel[ ControlledExp[_, _, OptionsPattern[]] ] := With[
  { lbl = OptionValue[ControlledExp, "Label"] },
  {First @ lbl, Superscript[Last @ lbl, First @ lbl]}
 ]


gateShape["CirclePlus"][x_, yy_List, ___] :=
  gateShape["CirclePlus"] @@@ Thread @ {x, yy}

gateShape["CirclePlus"][x_, y_?NumericQ, ___] := Module[
  { circ, crss },
  circ = Circle[ {x, y}, $GateSize / 3 ];
  crss = Line[ {
      { {x-$GateSize/3,y}, {x+$GateSize/3,y} },
      { {x,y-$GateSize/3}, {x,y+$GateSize/3} }
     } ];
  { circ, crss }
 ]


gateShape["Cross"][x_, Rule[yy_List, _], ___] :=
  gateShape["Cross"][x, yy]

gateShape["Cross"][x_, yy_List, ___] :=
  gateShape["Cross"] @@@ Thread @ {x, yy}

gateShape["Cross"][x_, y_, ___] := List @ Line @ {
    { {x,y}+{-1,-1}$DotSize, {x,y}+{+1,+1}$DotSize },
    { {x,y}+{-1,+1}$DotSize, {x,y}+{+1,-1}$DotSize }
   }


gateShape["Measurement"][x_, {y_}, opts___?OptionQ] :=
  gateShape["Measurement"][x, y, opts]

gateShape["Measurement"][x_, yy:{_, __}, opts___?OptionQ] := Module[
  {cc, mm, tt, rest},

  tt = "Label" /. {opts} /. Options[QuantumCircuit];
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
  text = qMeasurementText[x, y, opts];
  
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
(* NOTE: This form may occur on target qubits such as for CZ. *)

gateShape["Dot"][x_, Rule[yy_List, vv_List], ___] :=
  gateShape["Dot"] @@@ Thread @ {x, Thread[yy->vv]}

gateShape["Dot"][x_, y_?NumericQ -> 1, ___] := Disk[{x, y}, $DotSize]

gateShape["Dot"][x_, y_?NumericQ -> 0, ___] :=
  {EdgeForm[Black], White, Disk[{x, y}, $DotSize]}


gateShape["Rectangle"][x_, yy_List, opts___?OptionQ] := Module[
  { y1 = Min @ yy,
    y2 = Max @ yy,
    pane, line, text },
  text = gateText[x, Mean @ {y1, y2}, opts];
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
  text = gateText[x, y, opts];
  pane = Disk[{x, y}, $GateSize/2];
  { {EdgeForm[Black], White, pane}, text }
 ]

gateShape["Oval"][ x_, Rule[yy_List, _], opts___?OptionQ ] := Module[
  { x1 = x - $GateSize/2,
    x2 = x + $GateSize/2,
    y1 = Min @ yy,
    y2 = Max @ yy,
    y0, y3, ff, pane, text},
  
  text = gateText[x, Mean @ {y1, y2}, opts];

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


gateText[ x_, y_, opts___?OptionQ ] := Module[
  { label, factor },
  { label, factor } = { "Label", "LabelSize" } /.
    {opts} /. Options[QuantumCircuit];
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
    {opts} /. Options[QuantumCircuit];
  If[ label == None, Return @ Nothing ];
  Text[
    Style[ label, Italic,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.5 $GateSize / $CircuitSize) factor] ],
    {x + 0.65 $GateSize, y},
    {-1, -1}
   ]
 ]


qcNodes::usage = "qcNodes[ ... ] takes circuit elements and construct them as nodes of the circuit diagram by assigning horizontal and vertical coordinates to them."

qcNodes[ gg_List, xx_List, yy_Association ] :=
  ReleaseHold @ Thread @ Hold[drawGate][gg, xx, yy]


Gate::usage = "Gate[{c1,c2,...}, {t1,t2,...}, opts] represents a multi-control multi-target gate element in the quantum circuit."

Gate[cc:{__?QubitQ}, tt:{__?QubitQ}, opts:OptionsPattern[]] :=
  Gate[cc -> Table[1, Length @ cc], tt, opts]


drawGate::usage = "Renders the gates."

drawGate[gg_List, x_, yy_Association] := Map[drawGate[#, x, yy]&, gg]

drawGate[
  Gate[Rule[cc:{__?QubitQ}, vv_], tt:{__?QubitQ}, opts:OptionsPattern[]],
  x_, yy_Association ] := Module[
   { yc = Lookup[yy, cc],
     yt = Lookup[yy, tt],
     label = OptionValue[QuantumCircuit, {opts}, "Label"],
     control, target, dots, link, pane },

   If[Not @ ListQ[label], label = {label, label}];
   {control, target} = gateShape /@ {"ControlFunction", "TargetFunction"} /.
     {opts} /. Options[QuantumCircuit];
   
   link = Line @ Join[Thread @ {x, yc}, Thread @ {x, yt}];
   
   dots = control[x, yc -> vv, "Label" -> First[label], opts];
   pane = target[x, yt, "Label" -> Last[label], opts];
   
   Join[{link}, dots, pane]
  ]


drawGate[Gate[tt:{__?QubitQ}, opts___?OptionQ], x_, yy_Association] :=
  Module[
    { yt = Lookup[yy, tt],
      target },
    
    target = gateShape[
      "TargetFunction" /. {opts} /. Options[QuantumCircuit]
     ];

    target[x, yt, opts]
   ]


drawGate["Spacer", _, _Association] = Nothing

drawGate["Separator", x_, yy_Association] := Module[
  { xy = Tuples[{{x}, MinMax @ yy }] },
  { Dotted,
    Line @ {
      {0,-$CircuitUnit/2} + First @ xy,
      {0,+$CircuitUnit/2} + Last @ xy }
   }
 ]

drawGate[g_, x_, yy_Association] := g


qcLines::usage = "qcLines[gg, x, y] finds when Measurement occurs in the QuantumCircuit and renders the qubit line after Measurement in dashes."

qcLines[ gg_List, xx_List, yy_Association ] := Module[
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

qcCircuitPort[v:Ket[_Association], opts___?OptionQ] := Port[v, opts]

qCircuitPort[v:Ket[Except[_Association]], ___] :=
  (Message[QuantumCircuit::ket, v]; Nothing)
(* NOTE: Somehow v_Ket does not work properly. *)

qCircuitPort[v:ProductState[_Association, ___?OptionQ], more___?OptionQ] :=
  Port[v, more]

qCircuitPort[v:ProductState[Except[_Association]], ___] :=
  (Message[QuantumCircuit::ket, v]; Nothing)

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
