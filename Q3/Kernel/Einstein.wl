(* -*- mode:math -*- *)
BeginPackage["Q3`"]

`Einstein`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.16 $"][[2]], " (",
  StringSplit["$Date: 2023-04-27 12:55:51+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

Begin["`Private`"]

HoldPattern @ Multiply[ pre___,
  Ket[a_Association], Bra[b_Association], post___] :=
  Multiply[pre, Dyad[a, b], post]
(* EXPERIMENTAL since v5.66 *)
(* NOTE (v5.85): This must come at the final stage and is moved to here.
   Otherwise, for example, Dagger[a[1]] ** Ket[] ** Bra[] ** a[1]
   results in Dagger[a[1]] ** Dyad[<||>,<|a[1]->1|>]. *)


(**** <fallbacks> ****)

MultiplyExp /:
HoldPattern @ Elaborate[ MultiplyExp[expr_] ] := MultiplyExp[expr]

(**** </fallbacks> ****)

End[]

EndPackage[]
