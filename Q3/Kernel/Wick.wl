BeginPackage["Q3`"]

{ WickState };

{ WickExpectation };

Begin["`Private`"]


(**** <WickState> ****)

WickState::usage = "WickState[mat, <|c1->v1, c2->v2, \[Ellipsis], cn->vn|>] represents a many-body state occupying the dressed fermion modes dj related to the bare fermion modes ci by the unitary matrix mat.\nWickState[{u, v}, <|c1->v1, c2->v2, \[Ellipsis], cn->vn|>] represents a many-body state with occupation v1, \[Ellipsis], vn of fermion modes c1, \[Ellipsis], cn that evolves in accordance with the 2l\[Times]2l unitary matrix which comprises blocks u, v, v* and u*."


WickState /:
MakeBoxes[vec:WickState[mat_?MatrixQ, aa_Association], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ {"Bare modes: ", Keys @ aa},
      BoxForm`SummaryItem @ {"Occupation: ", Values @ aa}
    },
    { BoxForm`SummaryItem @ { "Transformation: ",
        MatrixForm[mat[[;;UpTo[8], ;;UpTo[8]]]] }
    },
    fmt, "Interpretable" -> Automatic ]

WickState /:
MakeBoxes[vec:WickState[{uu_?MatrixQ, vv_?MatrixQ}, aa_Association], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, vec, None,
    { BoxForm`SummaryItem @ {"Bare modes: ", Keys @ aa},
      BoxForm`SummaryItem @ {"Occupation: ", Values @ aa}
    },
    { BoxForm`SummaryItem @ { "Transformation (U part): ",
        MatrixForm[uu[[;;UpTo[8], ;;UpTo[8]]]] },
      BoxForm`SummaryItem @ { "Transformation (V part): ",
        MatrixForm[vv[[;;UpTo[8], ;;UpTo[8]]]] }
    },
    fmt, "Interpretable" -> Automatic ]

WickState[any_, Ket[a_Association]] := WickState[any, a]

(**** </WickState> ****)


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[expr, mat, assoc] calculates the expectation value of a polynomial of fermion creation and annihilation operators with respect to WickState[mat, assoc] efficiently based on the Wick theorem.\nWickExpectation[expr, {u, v}, assoc] calculates the expectation value of a polynomial expr of fermionic creation and annihilation operators with respect to WickState[{u, v}, assoc] efficiently based on the Wick theorem."

WickExpectation[c_, any_, Ket[a_Association]] := WickExpectation[c, any, a]

WickExpectation[_?AnyFermionQ, mm:(_?MatrixQ|{_?MatrixQ, _?MatrixQ}), _Association] = 0

WickExpectation[z_?CommutativeQ, mm:(_?MatrixQ|{_?MatrixQ, _?MatrixQ}), _Association] = z

WickExpectation[z_?CommutativeQ op_, mat_, vec_] :=
  z * WickExpectation[op, mat, vec]

WickExpectation[expr_Plus, mat_, vec_] := 
  WickExpectation[#, mat, vec]& /@ expr

HoldPattern @
WickExpectation[op:Multiply[__?AnyFermionQ], mat:{_?MatrixQ, _?MatrixQ}, vv_Association] :=
  theWickNambu[List @@ op, mat, vv]

HoldPattern @
WickExpectation[op:Multiply[__?AnyFermionQ], mat_?MatrixQ, vv_Association] :=
  theWickFermi[List @@ op, mat, vv]

(**** </WickExpectation> ****)


(**** <theWickNambu> ****)

theWickNambu::usage = "WickNambu[...] ... "

theWickNambu[aa:{__?AnyFermionQ}, mat:{_?MatrixQ, _?MatrixQ}, vv_Association] :=
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
      {i, j} -> theNambuM[mat][ff[[i]], ff[[j]]],
      {i, nn},
      {j, i+1, nn}
    ];
    mm = SymmetrizedArray[Flatten[ff, 1], {nn, nn}, Antisymmetric[{1, 2}]];
    Pfaffian[mm]
  ]


theNambuM::usage = "theNambuM[{u, v}][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input form: {pos, bare/dressed, sheer/dagger} *)

theNambuM[{u_, v_}][{_, 0, 1}, {_, 0, _}] = 0

theNambuM[{u_, v_}][{_, 0, 0}, {_, 0, 0}] = 0

theNambuM[{u_, v_}][{a_, 0, 0}, {a_, 0, 1}] = 1

theNambuM[{u_, v_}][{a_, 0, 0}, {b_, 0, 1}] = 0


theNambuM[{u_, v_}][{a_, 0, 0}, {b_, 1, 0}] := Conjugate[v[[b, a]]]

theNambuM[{u_, v_}][{a_, 0, 0}, {b_, 1, 1}] := Conjugate[u[[b, a]]]

theNambuM[{u_, v_}][{a_, 0, 1}, {b_, 1, _}] = 0


theNambuM[{u_, v_}][{a_, 1, _}, {b_, 0, 0}] = 0

theNambuM[{u_, v_}][{a_, 1, 0}, {b_, 0, 1}] := u[[a, b]]

theNambuM[{u_, v_}][{a_, 1, 1}, {b_, 0, 1}] := v[[a, b]]


theNambuM[{u_, v_}][{a_, 1, 0}, {b_, 1, 0}] := Dot[u, Topple @ v][[a, b]]

theNambuM[{u_, v_}][{a_, 1, 0}, {b_, 1, 1}] := Dot[u, Topple @ u][[a, b]]

theNambuM[{u_, v_}][{a_, 1, 1}, {b_, 1, 0}] := Dot[v, Topple @ v][[a, b]]

theNambuM[{u_, v_}][{a_, 1, 1}, {b_, 1, 1}] := Dot[v, Topple @ u][[a, b]]

(**** </theWickNambu> ****)


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
      {i, j} -> theFermiM[mat][ff[[i]], ff[[j]]],
      {i, nn},
      {j, i+1, nn}
    ];
    mm = SymmetrizedArray[Flatten[ff, 1], {nn, nn}, Antisymmetric[{1, 2}]];
    Pfaffian[mm]
  ]


theFermiM::usage = "theFermiM[mat][{a, i, j}, {b, p, q}] calcualtes the elements of matrix M."

(* input form: {pos, bare/dressed, sheer/dagger} *)
theFermiM[mat_?MatrixQ][{_, _, 1}, {_, _, _}] = 0

theFermiM[mat_?MatrixQ][{_, _, 0}, {_, _, 0}] = 0

theFermiM[mat_?MatrixQ][{a_, 0, 0}, {a_, 0, 1}] = 1

theFermiM[mat_?MatrixQ][{a_, 0, 0}, {b_, 0, 1}] = 0

theFermiM[mat_?MatrixQ][{a_, 0, 0}, {b_, 1, 1}] := Conjugate[mat[[b, a]]]

theFermiM[mat_?MatrixQ][{a_, 1, 0}, {b_, 0, 1}] := mat[[a, b]]

theFermiM[mat_?MatrixQ][{a_, 1, 0}, {a_, 1, 1}] = 1

theFermiM[mat_?MatrixQ][{a_, 1, 0}, {b_, 1, 1}] = 0

(**** </theWickFermi> ****)


End[]

EndPackage[]
