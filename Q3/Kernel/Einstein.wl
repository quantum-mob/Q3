(* -*- mode:math -*- *)

BeginPackage[ "Q3`Einstein`",
  { "Q3`Abel`",
    "Q3`Cauchy`",
    "Q3`Pauli`",
    "Q3`Quisso`",
    "Q3`Fock`",
    "Q3`Wigner`"
   }
 ]

`Information`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.7 $"][[2]], " (",
  StringSplit["$Date: 2021-04-16 11:40:04+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

Q3`Q3Clear[];

{ JordanWignerTransform };


Begin["`Private`"]

$symbs = Unprotect[ Multiply, MultiplyExp ]

JordanWignerTransform::usage = "JordanWignerTransform[]"

JordanWignerTransform[expr_, qq:{__?QubitQ} -> ff:{__?FermionQ}] :=
  Garner @ Elaborate[ expr /. JordanWignerTransform[qq -> ff] ]

JordanWignerTransform[expr_, ff:{__?FermionQ} -> qq:{__?QubitQ}] :=
  Garner @ Elaborate[ expr /. JordanWignerTransform[ff -> qq] ]

JordanWignerTransform[qq:{__?QubitQ} -> ff:{__?FermionQ}] := Module[
  { rr = Through[Construct[qq, 4]],
    zz = Through[Construct[qq, 3]],
    cc, pp, rules },
  pp = FoldList[Multiply, 1, Parity /@ Most[ff]];
  cc = Multiply @@@ Transpose @ {pp, ff};
  rules = Thread[rr -> cc];
  Join[ Dagger[rules], rules, Thread[zz -> Map[Parity, ff]] ]
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

Protect[ Evaluate @ $symbs ]

End[]


Q3`Q3Protect[]


EndPackage[]
