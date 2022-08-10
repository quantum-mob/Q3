(* -*- mode:math -*- *)

BeginPackage["Q3`"]

`Einstein`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.15 $"][[2]], " (",
  StringSplit["$Date: 2022-08-08 13:41:19+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

Begin["`Private`"]


(**** <fallbacks> ****)

MultiplyExp /:
HoldPattern @ Elaborate[ MultiplyExp[expr_] ] := MultiplyExp[expr]

(**** </fallbacks> ****)


End[]

EndPackage[]
