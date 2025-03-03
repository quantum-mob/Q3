(* -*- mode:math -*- *)
BeginPackage["QuantumMob`Q3S`", {"System`"}]

{ Customize, $Customizations };

{ $EmptyPlotMarkers };


Begin["`Private`"]

$Customizations::usage = "Custom options for various frequently used functions."

$Customizations = {
  (** Common **)
  (* PlotStyle -> Thick, *)
  (* AxesStyle -> Large, *)
  (* ImageSize -> Large, *)
  (** Graphics **)
  Axes -> False,
  Frame -> True,
  (* FrameStyle -> Large, *)
  GridLines -> Automatic,
  PlotRangePadding -> Scaled[0.025],
  (** Graphics3D **)
  Nothing
};


(**** <Customize> ****)

Customize::usage = "Customize[symb, options] sets the options for symb with the specified options and $Customizations."

Customize[ss:{__Symbol}, opts___?OptionQ] :=
  Scan[Customize[opts], ss]

Customize[symb_Symbol, opts___?OptionQ] := Module[
  { mint },
  mint = FilterRules[
    Normal @ Association @ Join[$Customizations, {opts}],
    Options[symb]
  ];
  SetOptions[symb, mint]
]

Customize[opts___?OptionQ][symb_Symbol] :=
  Customize[symb, opts]
  
(**** </Customize> ****)


(* Graphics *)

Customize[Graphics, Frame -> False, Axes -> False, GridLines -> None];

(* Graphics-related functions *)

Customize @ {
  Histogram,
  Plot, ParametricPlot, LogPlot, LogLinearPlot, LogLogPlot,
  ListPlot, ListLinePlot, ListLogPlot, ListLogLinearPlot, ListLogLogPlot,
  ReImPlot, AbsArgPlot
};

(* 2022-07-23 (v13.1): For some unknown reason, AxesStyle->Large causes a
   problem with ComplexListPlot. *)
Customize[ComplexListPlot, AxesStyle->{}];

(* Graphics3D-related functions *)

Customize[Graphics3D];

Customize[
  { Plot3D,
    ParametricPlot3D
   },
  Axes -> True
]


$EmptyPlotMarkers::usage = "$EmptyPlotMarkers gives a list of predefined empty markers."

$EmptyPlotMarkers = {
  "\[EmptyCircle]",
  "\[EmptyUpTriangle]",
  "\[EmptyDiamond]",
  "\[EmptySquare]",
  "\[EmptyDownTriangle]"
};


End[]

EndPackage[]
