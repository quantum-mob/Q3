(* -*- mode:math -*- *)

BeginPackage["Q3`"]

`Einstein`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.12 $"][[2]], " (",
  StringSplit["$Date: 2021-06-05 20:53:17+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ JordanWignerTransform }; (* Q3`Abel` *)


Begin["`Private`"]

JordanWignerTransform::usage = "JordanWignerTransform[]"

JordanWignerTransform[expr_, {} -> {}] := expr

JordanWignerTransform[expr_, qq:{__?QubitQ} -> ff:{__?FermionQ}] :=
  Garner @ Elaborate[ expr /. JordanWignerTransform[qq -> ff] ]

JordanWignerTransform[expr_, ff:{__?FermionQ} -> qq:{__?QubitQ}] :=
  Garner @ Elaborate[ expr /. JordanWignerTransform[ff -> qq] ]

JordanWignerTransform[{} -> {}] := {}

JordanWignerTransform[qq:{__?QubitQ} -> ff:{__?FermionQ}] := Module[
  { rr = Through[Construct[qq, 4]],
    xx = Through[Construct[qq, 1]],
    yy = Through[Construct[qq, 2]],
    zz = Through[Construct[qq, 3]],
    cc, pp, rules },
  pp = FoldList[Multiply, 1, Parity /@ Most[ff]];
  cc = pp ** ff;
  Join[
    Thread[Dagger[rr] -> Dagger[cc]],
    Thread[rr -> cc],
    Thread[xx -> Dagger[cc] + cc],
    Thread[yy -> I (Dagger[cc] - cc)],
    Thread[zz -> Map[Parity, ff]]
   ]
 ] /; Length[qq] == Length[ff]

JordanWignerTransform[ff:{__?FermionQ} -> qq:{__?QubitQ}] := Module[
  { rr = Through[Construct[qq, 4]],
    zz = Through[Construct[qq, 3]],
    cc, pp },
  pp = FoldList[Multiply, 1, Most @ zz];
  cc = Multiply @@@ Transpose @ {pp, rr};
  Thread[ff -> cc]
 ] /; Length[qq] == Length[ff]


(**** <fallbacks> ****)

MultiplyExp /:
HoldPattern @ Elaborate[ MultiplyExp[expr_] ] := MultiplyExp[expr]

(**** </fallbacks> ****)

End[]

EndPackage[]
