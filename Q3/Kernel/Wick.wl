BeginPackage["Q3`"]

{ WickState };

{ WickExpectation };

Begin["`Private`"]


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[expr, mat, ket] calculates the expectation value of operator expr with respect to WickState[mat, ket] efficiently based on the Wick theorem."

WickExpectation[_?AnyFermionQ, mat_?MatrixQ, vec_Ket] = 0

WickExpectation[z_?CommutativeQ, mat_?MatrixQ, vec_Ket] = z

WickExpectation[z_?CommutativeQ op_, mat_, vec_] := 
  z * WickExpectation[op, mat, vec]

WickExpectation[expr_Plus, mat_, vec_] := 
  WickExpectation[#, mat, vec]& /@ expr

HoldPattern @
WickExpectation[op:Multiply[__?AnyFermionQ], mat_?MatrixQ, Ket[vv_Association]] :=
  theWickFermi[List @@ op, mat, Ket @ vv]

(**** </WickExpectation> ****)


(**** <theWickFermi> ****)

theWickFermi::usage = "WickFermi[...] ... "

theWickFermi[aa:{__?AnyFermionQ}, mat_?MatrixQ, Ket[vv_Association]] :=
  Module[
    { rr = Thread[Keys[vv] -> Range[Length @ vv]],
      bb, cc, ff, nn, mm },
    cc = Keys[theKetTrim @ vv];
    cc = ReplaceAll[cc, rr];
    (* {pos, bare/dressed, sheer/dagger} *)
    bb = Switch[#, _Dagger, {Peel[#], 1, 1}, _, {#, 1, 0}]& /@ aa;
    bb = ReplaceAll[bb, rr];
    ff = Join[
      Thread[{Reverse @ cc, 0, 0}],
      bb,
      Thread[{cc, 0, 1}]
    ];
    nn = Length[ff];
    ff = Table[
      {i, j} -> theWickM[mat][ff[[i]], ff[[j]]],
      {i, nn},
      {j, i+1, nn}
    ];
    mm = SymmetrizedArray[Flatten[ff, 1], {nn, nn}, Antisymmetric[{1, 2}]];
    Pfaffian[Normal @ N @ mm]
  ]


theWickM::usage = "theWickM[mat][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input form: {pos, bare/dressed, sheer/dagger} *)
theWickM[mat_?MatrixQ][{_, _, 1}, {_, _, _}] = 0

theWickM[mat_?MatrixQ][{_, _, 0}, {_, _, 0}] = 0

theWickM[mat_?MatrixQ][{a_, 0, 0}, {a_, 0, 1}] = 1

theWickM[mat_?MatrixQ][{a_, 0, 0}, {b_, 0, 1}] = 0

theWickM[mat_?MatrixQ][{a_, 0, 0}, {b_, 1, 1}] := Conjugate[mat[[b, a]]]

theWickM[mat_?MatrixQ][{a_, 1, 0}, {b_, 0, 1}] := mat[[a, b]]

theWickM[mat_?MatrixQ][{a_, 1, 0}, {a_, 1, 1}] = 1

theWickM[mat_?MatrixQ][{a_, 1, 0}, {b_, 1, 1}] = 0

(**** </theWickFermi> ****)


End[]

EndPackage[]
