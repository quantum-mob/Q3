(* -*- mode:math -*- *)
(* Mahn-Soo Choi *)
(* $Date: 2022-07-23 00:53:51+09 $ *)
(* $Revision: 1.7 $ *)

BeginPackage["Q3`"]

$Customizations::usage = "Custom options for various frequently used functions."

Customize::usage = "Customize[symb, options] sets the options for symb with the specified options and $Customizations."


Begin["`Private`"]

$Customizations = {
  (* Graphics *)
  Axes -> False,
  Frame -> True,
  FrameStyle -> Large,
  GridLines -> Automatic,
  PlotRangePadding -> Scaled[0.025],
  (* Graphics3D *)
  (* Common *)
  PlotStyle -> Thick,
  AxesStyle -> Large,
  ImageSize -> Large
 };


Customize[ss:{__Symbol}, opts___?OptionQ] := Scan[
  Customize[#, opts]&,
  ss
 ]
  
Customize[symb_Symbol, opts___?OptionQ] := Module[
  { less = Normal @ KeyDrop[$Customizations, Keys @ {opts}],
    more },
  more = FilterRules[Join[{opts}, less], Options[symb]];
  SetOptions[symb, more]
 ]


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

End[]

EndPackage[]
