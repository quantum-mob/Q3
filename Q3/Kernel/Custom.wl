(* -*- mode:math -*- *)

BeginPackage["Q3`Custom`"]

$Customizations::usage = "Custom options for various frequently used functions."

Customization::usage = "Customization[symb, options] sets the options for symb with the specified options and $Customizations."


Begin["`Private`"]

(***** <Customization> ****)

$Customizations = {
  (* Graphics *)
  Axes -> False,
  Frame -> True,
  FrameStyle -> Large,
  PlotRangePadding -> Scaled[0.025],
  PlotStyle -> Thick,
  GridLines -> Automatic,
  FrameStyle -> Large,
  (* Graphics3D *)
  PlotStyle -> Thick,
  (* Common *)
  AxesStyle -> Large,
  ImageSize -> Large
 };


Customization[ss:{__Symbol}, opts___?OptionQ] := Scan[
  Customization[#, opts]&,
  ss
 ]
  
Customization[symb_Symbol, opts___?OptionQ] := Module[
  { less = Normal @ KeyDrop[$Customizations, Keys @ {opts}],
    more },
  more = FilterRules[Join[{opts}, less], Options[symb]];
  SetOptions[symb, more]
 ]


(* Graphics *)

Customization[Graphics, Frame -> False, Axes -> False, GridLines -> None];

(* Graphics-related functions *)

Customization @ {
  Histogram,
  Plot, ParametricPlot, LogPlot, LogLinearPlot, LogLogPlot,
  ListPlot, ListLinePlot, ListLogPlot, ListLogLinearPlot, ListLogLogPlot
 };

(* Graphics3D-related functions *)

Customization[
  { Graphics3D,
    Plot3D,
    ParametricPlot3D
   },
  Axes -> True
 ]

(***** </Customization> ****)


End[]

EndPackage[]
