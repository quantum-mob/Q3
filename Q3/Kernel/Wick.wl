BeginPackage["Q3`"]

{ WickState };

{ WickExpectation };

Begin["`Private`"]


(**** <WickState> ****)

WickState::usage = "WickState[mat, <|c1->v1, c2->v2, \[Ellipsis], cn->vn|>] represents a many-body state occupying the dressed fermion modes dj related to the bare fermion modes ci by the unitary matrix mat."


WickState /:
MakeBoxes[vec:WickState[mat_?MatrixQ, aa_Association], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ {"Bare modes: ", Keys @ aa},
      BoxForm`SummaryItem @ {"Occupation: ", Values @ aa}
    },
    { BoxForm`SummaryItem @ { "Transformation: ", 
        MatrixForm[mat[[;;UpTo[8]]], mat[[;;UpTo[8]]]] } 
    },
    fmt, "Interpretable" -> Automatic ]

WickState[m_, Ket[a_Association]] := WickState[m, a]

(**** </WickState> ****)


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[expr, mat, assoc] calculates the expectation value of operator expr with respect to WickState[mat, assoc] efficiently based on the Wick theorem."

WickExpectation[c_, mat_, Ket[a_Association]] := WickExpectation[c, mat, a]

WickExpectation[_?AnyFermionQ, mat_?MatrixQ, _Association] = 0

WickExpectation[z_?CommutativeQ, mat_?MatrixQ, _Association] = z

WickExpectation[z_?CommutativeQ op_, mat_, vec_] :=
  z * WickExpectation[op, mat, vec]

WickExpectation[expr_Plus, mat_, vec_] := 
  WickExpectation[#, mat, vec]& /@ expr

HoldPattern @
WickExpectation[op:Multiply[__?AnyFermionQ], mat_?MatrixQ, vv_Association] :=
  theWickFermi[List @@ op, mat, vv]

(**** </WickExpectation> ****)


(**** <theWickFermi> ****)

theWickFermi::usage = "WickFermi[...] ... "

theWickFermi[aa:{__?AnyFermionQ}, mat_?MatrixQ, vv_Association] :=
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
