BeginPackage["Q3`"]

{ WickLogarithmicNegativity, WickTimeReversalMoment };
{ WickEntanglementEntropy, WickMutualInformation };
{ QuantumLog }; (* mainly in vonNeumann.wl *)

{ WickMatrix, WickElements };

{ WickState, WickGaussian, WickUnitary };
{ WickOperator, WickOperatorFrom };
{ WickExpectation, WickGreenFunction };

{ WickDensityMatrix };

{ WickCircuit, WickRandomCircuit };
{ RandomWickState, RandomNambuState };

{ NambuState, NambuOperator, NambuUnitary, NambuGaussian,
  NambuHermitian, NambuGreen,  NambuMatrix }; 

Begin["`Private`"]

(**** <WickTimeReversalMoment> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)
WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."

WickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[WickTimeReversalMoment] = { "Epsilon" -> 1.25*^-5 } (* 1.0*^-8 is also a reasonable choice *)


WickTimeReversalMoment[alpha_, NambuGreen[{g_?MatrixQ, f_?MatrixQ}, ___], rest__] := 
  WickTimeReversalMoment[alpha, {g, f}, rest]

WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  WickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk, opts]

WickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, OptionsPattern[]] := Quiet[
  Module[
    { dd = Length[grn],
      gg, oo, id, xx, zz, uu, ww, pf1, pf2, dgn, off
    },
    oo = Zero[{dd, dd}];
    id = One[dd];
    xx = CircleTimes[ThePauli[1], id];
    zz = CircleTimes[ThePauli[3], id];

    (* \Gamma *)
    gg = tameMatrix[id - N[grn], OptionValue["Epsilon"]];
    (* NOTE: When there is a fermion mode that is unoccuppied with certainty, the coherent-state representation becomes unusual, and one needs to handle such cases separately. While this is possible, Q3 offers a ditry trick. *)
    (* NOTE: N[grn] is to avoid additional normalization (or even orthonormalization) of the eigenvectors of grn. *)
    gg = Normal @ NambuHermitian[{gg, -anm}];
  
    pf1 = Power[Pfaffian[Inverse[gg.xx]], 2];

    (* \Omega of the density operator \rho *)
    ww = Inverse[gg] - zz;

    uu = SparseArray[
      Flatten @ {
        Thread[Transpose@{kk, dd + kk} ->  I],
        Thread[Transpose@{dd + kk, kk} -> -I],
        Thread[Transpose@{kk, kk} -> 0],
        Thread[Transpose@{dd + kk, dd + kk} -> 0],
        {i_, i_} -> 1,
        {_, _} -> 0
      },
      {2*dd, 2*dd}
    ];
    (* \Omega of partial TR *)
    ww = Topple[uu] . ww . uu;

    dgn = CirclePlus[ww[[;;dd, ;;dd]], ww[[dd+1;;, dd+1;;]]];
    off = ArrayFlatten @ {
      {oo, ww[[;;dd, dd+1;;]]},
      {ww[[dd+1;;, ;;dd]], oo}
    };
    pf2 = Pfaffian[(off - zz).xx];
    Check[pf2 /= pf1, Message[WickTimeReversalMoment::infy]; pf2 = 0];

    (* effective \Omega of \Xi *)
    ww = Inverse[zz - off];
    ww = off + dgn . ww . dgn;
    pf2 *= Pfaffian[xx.(ww + zz)];

    (* effective \Gamma *)
    gg = Inverse[ww + zz];
    (* effective Green's function Gij *)
    gg = CircleTimes[ThePauli[10], id] - gg;

    (* Recall the particle-hole symmetry. *)
    gg = Take[Eigenvalues @ gg, dd];
    Total[Log[2, Power[gg, alpha] + Power[1-gg, alpha]]] + Log[2, Power[pf2, alpha]]
  ],
  Inverse::luc
  (* 2024-08-11: Inverse::luc is silenced; the warning message does not seem to be serious in most cases, but goes off too often. *)
]


tameMatrix::usage = "tameMatrix[mat, eps] tames a singular matrix mat with a small positive eps, and returns the resulting non-singular matrix."

(* NOtE: mat is supposed to be Hermitian. *)
tameMatrix[mat_?MatrixQ, eps_] := Module[
  {val, vec},
  {val, vec} = Eigensystem[mat];
  val = val /. {x_?(ZeroQ[#, eps] &) :> x + 1.25*eps};
  Transpose[vec] . DiagonalMatrix[val] . Conjugate[vec]
]

(**** </WickTimeReversalMoment> ****)


(**** <WickLogarithmicNegtivity> ****)

(* See also: Shapourian and Ryu (2017, 2019) *)
WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[{grn,anm}, {k1,k2,\[Ellipsis]}] returns the fermionic negativity over modes k1, k2, \[Ellipsis] of the fermionic Gaussian states characterized by the Green's function grn (in an L\[Times]L matrix for L fermion modes) and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickLogarithmicNegativity[grn, {k1,k2,\[Ellipsis]}] is equivalent to WickLogarithmicNegativity[{grn,0}, {k1,k2,\[Ellipsis]}]."

Options[WickLogarithmicNegativity] = Options[WickTimeReversalMoment]


WickLogarithmicNegativity[kk:{__Integer}][any_] :=
  WickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[WickLogarithmicNegativity, "Epsilon"]]

WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, grn, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts:OptionsPattern[]] :=
  WickTimeReversalMoment[1/2, {grn, anm}, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]

WickLogarithmicNegativity[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], rest__] :=
  WickLogarithmicNegativity[{gg, ff}, rest]

(* operator form *)
WickLogarithmicNegativity[dd:{__?FermionQ}][any_] :=
  WickLogarithmicNegativity[any, dd]

WickLogarithmicNegativity[ws_WickState, dd:{__?FermionQ}, opts:OptionsPattern[]] := Module[
  { gg = WickGreenFunction[ws],
    cc = Last[ws],
    kk },
  kk = dd /. Thread[cc -> Range[Length @ cc]];
  WickTimeReversalMoment[1/2, gg, kk, opts, "Epsilon" -> OptionValue["Epsilon"]]
]

(**** </WickLogarithmicNegtivity> ****)


AddElaborationPatterns[_WickState, _WickGaussian, _WickUnitary, _WickOperator];


(**** <WickState> ****)

WickState::usage = "WickState[enc, trs, mat, {c1, c2, \[Ellipsis], cm}] represents a many-body state of m fermionic modes c1, c2, \[Ellipsis], cm in a structed data form."

WickState::trs = "Inconsistent transformations ``; each transformation must be specified either {mat, mat} or mat form."

WickState::frm = "No fermion modes in ``."

WickState::null = "`` is the null state."

WickState /:
MakeBoxes[ws:WickState[ops:{___Rule}, cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", cc },
      BoxForm`SummaryItem @ { "Depth: ", Length @ ops }
    },
    { BoxForm`SummaryItem @ { "Operator flags: ", Keys @ ops },
      BoxForm`SummaryItem @ { "Operator transforms: ", ArrayShort @ Values @ ops }    
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* canonicalization *)

WickState[cc:{__?FermionQ}] := WickState[{}, cc] (* vacuum state *)

WickState[0, cc:{__?FermionQ}] := (* null state *)
  WickState[{Identity -> Table[0, Length @ cc]}, cc]

WickState[Ket[aa_Association]] := Module[
  { cc = Select[Keys @ aa, FermionQ],
    dd = Select[Keys @ theKetTrim @ aa, FermionQ] },
  WickState[theWickOperator[Dagger @ dd, cc], cc]
]

WickState[ops:{__Dagger?AnyFermionQ}, cc:{__?FermionQ}] :=
  WickState @ Ket[cc -> 0, Peel[ops] -> 1]

WickState[ops:{Rule[_, _?VectorQ]..}, cc:{___?FermionQ}] :=
  WickState[Thread[Map[Hood, Keys @ ops] -> Values[ops]], cc] /;
  AnyTrue[Keys @ ops, AnyFermionQ]


WickState /:
NormSquare[WickState[{}, cc:{___?FermionQ}]] = 1

WickState /:
NormSquare[WickState[ops:{__Rule}, cc:{__?FermionQ}]] := Quiet[
  Re @ Sqrt @ Det @ WickMatrix @ Join[theConjugateReverse @ ops, ops], 
  Det::luc
]

WickState /:
Norm[ws:WickState[{___Rule}, {__?FermionQ}]] := Sqrt[NormSquare @ ws]


WickState /:
Normalize[ws:WickState[{}, {__?FermionQ}], ___] = ws

WickState /:
Normalize[ws:WickState[ops:{___Rule}, cc:{___?FermionQ}]] := Module[
  { flg = Keys[ops],
    new },
  Quiet @ Check[
    new = Values[ops] * Power[Norm @ ws, -1/Length[ops]],
    flg = {Identity};
    new = Zero @ {1, Length @ cc}
  ];
  WickState[Thread[flg -> new], cc]
]


WickState /:
Expand[ws:WickState[ops:{___Rule}, cc:{___?FermionQ}]] :=
  State[Matrix[ws, cc], cc]


WickState /:
Elaborate[ws_WickState] = ws (* fallback *)

WickState /:
Elaborate[ws:WickState[{___Rule}, cc:{__?FermionQ}]] := Module[
  { ff = WickElements[ws] },
  KetChop[ Multiply @@ Append[ff, Ket[cc]] ]
]


WickState /:
Matrix[ws_WickState, rest___] := (
  Message[WickState::bad, ws];
  Matrix[Ket[], rest]
)

WickState /:
Matrix[ws:WickState[{___Rule}, cc:{__?FermionQ}]] := Matrix[ws, cc]

WickState /:
Matrix[ws:WickState[ops:{___Rule}, cc:{__?FermionQ}], ss:{__?SpeciesQ}] :=
  With[
    { ff = WickElements[ops, cc] },
    SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ff, ss]
    ]
  ]


WickState /:
NonCommutativeQ[_WickState] = True

WickState /:
MultiplyKind[_WickState] = Fermion

(**** </WickState> ****)


(**** <WickGaussian> ****)

WickGaussian::usage = "WickGaussian[{mat, inv}] represents a non-unitary operator of the Gaussian form that is specified by the pair {mat, inv} of mutually inverse matrices."

WickGaussian::num = "Matrix `` needs to be numeric."

WickGaussian /:
MakeBoxes[WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    WickGaussian, mat, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ mat }
    },
    { BoxForm`SummaryItem @ { "Transform: ", ArrayShort /@ {mat, inv} }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[{mat, inv}]

(* canonicalization *)
WickGaussian[mat_?MatrixQ, rest___] := WickGaussian[{mat, Inverse @ mat}, rest] /; 
  If[MatrixQ[mat, NumericQ], True, Message[WickGaussian::num, mat]; False]

WickGaussian[{mat_/;MatrixQ[mat, NumericQ], inv_/;MatrixQ[inv, NumericQ]}, ___][ws_WickState] := 
  Module[
    { new },
    new = MapApply[
      #1 -> Switch[#1, Dagger, mat . #2, Identity, #2 . inv, _, $Failed] &,
      First @ ws
    ];
    WickState[new, Last @ ws]
  ]

WickGaussian /:
MatrixForm[op : WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___]] :=
  MatrixForm @ mat

WickGaussian /: 
NonCommutativeQ[_WickGaussian] = True

WickGaussian /:
MultiplyKind[_WickGaussian] = Fermion

WickGaussian /:
Multiply[pre___, op_WickGaussian, ws_WickState] := Multiply[pre, op @ ws]

WickGaussian /:
Multiply[pre___, op_WickGaussian, fs_Ket] := Multiply[pre, op @ WickState @ fs]


WickGaussian /:
Matrix[op:WickGaussian[{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___]] := Matrix[op, cc]

WickGaussian /:
Matrix[WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, cc:{__?FermionQ}], ss:{__?SpeciesQ}] := Module[
  { ff = Select[ss, FermionQ],
    rr = Select[ss, Not @* FermionQ],
    mm, n },
  n = Length[ff];
  
  (* Jordan-Wigner transformation *)
  mm = Table[PadRight[Table[3, k-1], n], {k, n}] + 4 * One[n];
  mm = ThePauli /@ mm;
  
  ff = Thread[ff -> mm];
  rr = Thread[rr -> Map[One, Dimension @ rr]];
  
  (* Convert the Nambu spinor to a list of matrices *)
  mm = Values @ KeyTake[Join[ff, rr], cc];

  MatrixExp @ TensorContract[
    Transpose[Topple /@ mm, {3, 1, 2}] . MatrixLog[mat] . mm,
    {{2, 3}}
  ]
]

WickGaussian /: (* fallback *)
Matrix[wu_WickGaussian, rest___] := wu * Matrix[1, rest]

(**** </WickGaussian> ****)


(**** <WickUnitary> ****)

WickUnitary::usage = "WickUnitary[{u, v}] represents the unitary matrix ArrayFlatten[{{u, v}, Conjugate @ {v, u}}] in the Nambu space."

WickUnitary /:
MakeBoxes[op:WickUnitary[trs_?MatrixQ, rest___], fmt_] := Module[
    { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ trs }
    },
    { BoxForm`SummaryItem @ { "Transform: ", ArrayShort @ trs }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[trs]


WickUnitary[0, cc:{___?FermionQ}, rest___] := (* null operator *)
  WickUnitary[Zero[Length[cc]*{1, 1}], cc, rest]

WickUnitary[1, cc:{___?FermionQ}, rest___] := (* identity operator *)
  WickUnitary[One[Length @ cc], cc, rest]


WickUnitary /:
Times[z_?CommutativeQ, WickUnitary[uv_, rest___]] := WickUnitary[z * uv, rest]

WickUnitary /:
Plus[WickUnitary[a_, cc_, opts___?OptionQ], WickUnitary[b_, cc_, more___?OptionQ]] :=
  WickUnitary[a + b, cc, Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Plus[WickUnitary[a_, opts___?OptionQ], WickUnitary[b_, more___?OptionQ]] :=
  WickUnitary[a + b, Sequence @@ Flatten @ {opts, more}]


WickUnitary /:
Dot[WickUnitary[a_, cc_, opts___?OptionQ], WickUnitary[b_, cc_, more___?OptionQ]] :=
  WickUnitary[Dot[a, b], cc, Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Dot[WickUnitary[a_, opts___?OptionQ], WickUnitary[b_, more___?OptionQ]] :=
  WickUnitary[Dot[a, b], Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Dagger[WickUnitary[mat_?MatrixQ, rest___]] := WickUnitary[Topple @ mat, rest]


WickUnitary /:
Elaborate[wu:WickUnitary[_?MatrixQ, cc:{__?FermionQ}, ___]] :=
  ExpressionFor[Matrix @ wu, cc]

WickUnitary /: (* fallback *)
Elaborate[wu_WickUnitary] = wu


WickUnitary /:
Matrix[wu:WickUnitary[_?MatrixQ, cc:{__?FermionQ}, ___]] :=
  Matrix[wu, cc]

WickUnitary /:
Matrix[WickUnitary[trs_?MatrixQ, cc:{__?FermionQ}, ___], rest__] := 
  Matrix[Q3`WickGaussian[{trs, Topple @ trs}, cc], rest]

WickUnitary /: (* fallback *)
Matrix[wu_WickUnitary, rest___] := wu * Matrix[1, rest]


WickUnitary /:
MatrixForm[WickUnitary[trs_?MatrixQ, ___], rest___] := MatrixForm[trs, rest]

WickUnitary /:
ArrayShort[WickUnitary[trs_?MatrixQ, ___], rest___] := ArrayShort[trs, rest]


WickUnitary /: 
NonCommutativeQ[_WickUnitary] = True

WickUnitary /:
MultiplyKind[_WickUnitary] = Fermion

WickUnitary /:
Multiply[pre___, wu_WickUnitary, ws_WickState] := Multiply[pre, wu @ ws]

WickUnitary /:
Multiply[pre___, wu_WickUnitary, fs_Ket] := Multiply[pre, wu @ WickState @ fs]


WickUnitary[{}, ___][any_] = any

WickUnitary[mat_/;MatrixQ[mat, NumericQ], ___][ws_WickState] := Module[
  { new },
  new = MapApply[
    #1 -> Switch[#1, Dagger, mat . #2, Identity, #2 . Topple[mat], _, $Failed] &,
    First @ ws
  ];
  WickState[new, Last @ ws]
]

WickUnitary[spec__][fs_Ket] := WickUnitary[spec][WickState @ fs]


WickUnitary /:
ParseGate[WickUnitary[trs_, ff:{___?FermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[ff, more, opts, "Label" -> "U"]

(**** </WickUnitary> ****)


(**** <theConjugateReverse> ****)

theConjugateReverse::usage = "theConjugateReverse[{flag1 -> vec1, flag2 -> vec2, ...}] returns the reversed list of rules with the values complex conjugated and the flags interchanges (Idenity <-> Dagger).\ntheConjugateReverse[mat] returns the reverse of {Conjugate[B], Conjugate[A]} for matrix mat with block structure mat = {A, B}."

(* for normal models *)
theConjugateReverse[ops:{Rule[Identity|Dagger, _?VectorQ]...}] :=
  Reverse @ Thread @ Rule[
    ReplaceAll[Keys @ ops, {Identity -> Dagger, Dagger -> Identity}],
    Conjugate[Values @ ops]
  ]

(* for normal models *)
theConjugateReverse[{tag_?VectorQ, trs_?MatrixQ}] := {
  Reverse @ ReplaceAll[tag, {Identity -> Dagger, Dagger -> Identity}],
  Reverse @ Conjugate @ trs
}

(* for the BdG models *)
theConjugateReverse[ops_?MatrixQ] := With[
  { new = ArrayFlatten[Reverse /@ PartitionInto[ops, {1, 2}]] },
  Conjugate @ Reverse @ new
]

(**** </theConjugateReverse> ****)


(**** <WickElements> ****)

WickElements::usage = "WickElements[spec, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion operators corresponding to specification spec."

(* fot normal models *)

WickElements[ops:{___Rule}, cc:{__?FermionQ}] :=
  MapApply[#2 . #1[cc] &, ops]

WickElements[WickState[ops:{___Rule}, cc:{__?FermionQ}], ___] :=
  WickElements[ops, cc]

WickElements[WickOperator[ops:{___Rule}, ___?OptionQ], cc:{__?FermionQ}] :=
  WickElements[ops, cc]

WickElements[WickOperator[ops:{___Rule}, cc:{__?FermionQ}, ___], ___] :=
  WickElements[ops, cc]

(* for the BdG models *)

WickElements[ops_?MatrixQ, cc:{__?FermionQ}] :=
  ops . Join[cc, Dagger @ cc]

WickElements[NambuState[_?NambuMatrixQ, ops_?MatrixQ, cc:{__?FermionQ}], ___] :=
  WickElements[ops, cc]

WickElements[NambuOperator[trs_?MatrixQ, ___?OptionQ], cc:{__?FermionQ}] :=
  WickElements[trs, cc]

WickElements[NambuOperator[trs_?MatrixQ, cc:{__?FermionQ}], ___] :=
  WickElements[trs, cc]

(**** </WickElements> ****)


(**** <WickOperator> ****)

WickOperator::usage = "WickOperator[{c1,c2,...,ck}] represents an operator equivalent to c1**c2**...**ck, but is to be applied to a Wick state. on WickState ws.\nWickOperator[Measurement[c]] or WickOperator[Measurement[{c1, c2, \[Ellipsis]}]] is equivalent to Measurement[\[Ellipsis]].\nWickOperator[{u, v}] is equivalent to WickUnitary[{u, v}]."

WickOperator /:
MakeBoxes[op:WickOperator[trs:{___Rule}, rest___], fmt_] := Module[
  { cc = {rest} },
  cc = Which[ 
    Length[cc] == 0, "Unspecified",
    MatchQ[First @ cc, {__?FermionQ}], First[cc],
    True, "Unspecified"
  ];
  BoxForm`ArrangeSummaryBox[
    WickOperator, op, None,
    { BoxForm`SummaryItem @ { "Target: ", cc },
      BoxForm`SummaryItem @ { "Operators: ", Length @ trs }
    },
    { BoxForm`SummaryItem @ { "Flags: ", ArrayShort[Keys @ trs] },
      BoxForm`SummaryItem @ { "Transforms: ", ArrayShort[Values @ trs] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]


WickOperator[msr_Measurement] = msr

WickOperator[trs_WickUnitary] = trs

(* canonicalization *)

WickOperator[op_?AnyFermionQ, cc:{__?FermionQ}, rest___] :=
  WickOperator[{op}, cc, rest]

WickOperator[ops:{___?AnyFermionQ}, cc:{__?FermionQ}, rest___] :=
  WickOperator[theWickOperator[ops, cc], cc, rest]

WickOperator[rule_Rule, rest___] := WickOperator[{rule}, rest]

WickOperator[ops:{__Rule}] :=
  WickOperator @ Thread[Map[Hood, Keys @ ops] -> Values[ops]] /;
  AnyTrue[Keys @ ops, AnyFermionQ]


WickOperator[{}][any_] = any

WickOperator[ops:{Rule[_, _?VectorQ]..}, ___][in_WickState] :=
  WickState[Join[ops, First @ in], Last @ in]

WickOperator[ops:{__?AnyFermionQ}, ___][in_WickState] := WickState[
  Join[theWickOperator[ops, Last @ in], First @ in],
  Last @ in
]


WickOperator /:
Dagger @ WickOperator[ops:{__Rule}, rest___] :=
  WickOperator[theConjugateReverse @ ops, rest]


WickOperator /: 
NonCommutativeQ[_WickOperator] = True

WickOperator /:
MultiplyKind[_WickOperator] = Fermion

WickOperator /:
Multiply[pre___, opr_WickOperator, ws_WickState] := Multiply[pre, opr[ws]]

WickOperator /:
Multiply[pre___, opr_WickOperator, fs_Ket] := Multiply[pre, opr[WickState @ fs]]


WickOperator /:
Matrix[WickOperator[cc:{__?AnyFermionQ}, ___], rest___] :=
  Dot @@ Matrix[cc, rest]

WickOperator /: (* fallback *)
Matrix[op_WickOperator, rest___] := op * Matrix[1, rest]

WickOperator /:
Elaborate[op:WickOperator[trs:{___Rule}, cc:{__?FermionQ}, ___]] :=
  Apply[Multiply, WickElements[trs, cc]]

WickOperator /: (* fallback *)
Elaborate[op_WickOperator] = op 


WickOperator /:
VacuumExpectation[WickOperator[jmp:{___Rule}, ___]] :=
  Pfaffian @ WickMatrix[jmp]


WickOperator /:
ParseGate[WickOperator[op:{___?AnyFermionQ}, opts___?OptionQ], more___?OptionQ] :=
  Gate[Fermions @ op, more, opts]

(**** </WickOperator> ****)


(**** <WickOperatorFrom> ****)

(* NOTE: In principle, WickOperatorFrom may be integrated into WickOperator, but separating this feature keeps better the performance of WickOperator. *)

WickOperatorFrom::usage = "WickOperatorFrom[expr_, {c1, c2, \[Ellipsis]}] constructs WickOperator from linear combination (or a list of linear combinations) expr of fermion operators of fermion modes {c1, c2, \[Ellipsis]}."

WickOperatorFrom::mixed = "Mixed linear combination `` of creation and annihilation operators."

WickOperatorFrom::nlin = "`` is not a linear combination of the creation and annihilation operators of fermion modes ``."

WickOperatorFrom[cc : {__?FermionQ}][spec_] :=
  WickOperatorFrom[spec, cc]

WickOperatorFrom[expr_List, cc:{__?FermionQ}] :=
  WickOperator[theWickOperator[cc] /@ expr, cc]

WickOperatorFrom[expr_, cc:{__?FermionQ}] :=
  WickOperator[{theWickOperator[expr, cc]}, cc] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[WickOperatorFrom::nlin, expr, cc];
    False
  ]


theWickOperator::usage = "theWickOperator[expr, {c1, c2, \[Ellipsis]}] returns the coefficient list of expr in either creation or annihilation operators of fermion modes {c1, c2, \[Ellipsis]}. theWickOperator[expr, {c1, c2, \[Ellipsis], Dagger[c1], Dagger[c2], \[Ellipsis]}] returns the coefficients list of expr in {c1, c2, \[Ellipsis], Dagger[c1], Dagger[c2], \[Ellipsis]}."

theWickOperator[cc:{__?FermionQ}][any_] := theWickOperator[any, cc]

theWickOperator[expr_List, cc:{__?FermionQ}] := theWickOperator[cc] /@ expr

theWickOperator[expr_, cc:{__?FermionQ}] := Module[
  { aa = Coefficient[expr, cc],
    bb = Coefficient[expr, Dagger @ cc]},
  Which[
    ZeroQ @ Norm[aa, Infinity],
    Dagger -> bb,
    ZeroQ @ Norm[bb, Infinity],
    Identity -> aa,
    True, Message[WickOperator::mixed, expr]; Identity -> aa
  ]
]


theWickLinearQ::usage = "theWickLinearQ[expr, {c1, c2, \[Ellipsis]}] returns True if expr is a linear combination of the creation and annihilation operators of fermion modes {c1, c2, \[Ellipsis]}, and False otherwise."

theWickLinearQ[expr_List, cc : {__?FermionQ}] :=
  AllTrue[expr, theWickLinearQ[#, cc]&]

theWickLinearQ[expr_, cc : {__?FermionQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ Join[cc, Dagger @ cc], ___]
  ]
]

(**** </WickOperatorFrom> ****)


(**** <Measurement> ****)

Measurement /:
Multiply[pre___, msr:Measurement[_?FermionQ|{__?FermionQ}], ws_WickState] := 
  Multiply[pre, msr[ws]]

theMeasurement[ws:WickState[trs:{___Rule}, cc_], c_?FermionQ] := Module[
  { msr, dgr, mat, prb },
  msr = theWickOperator[{c, Dagger @ c}, cc];
  dgr = theConjugateReverse[trs];
  mat = WickMatrix @ Join[dgr, msr, trs];
  prb = Quiet[Re @ Sqrt @ Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= NormSquare[ws];
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[c] = 0;
    WickOperator[{c, Dagger @ c}, cc][ws],
    $MeasurementOut[c] = 1;
    WickOperator[{Dagger @ c, c}, cc][ws]
  ]
]

(**** </Measurement> ****)


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[ws] represents an expectation value with respect to the Wick state ws.\nWickState[ws][expr] returns the expectation value of expr, where expr may be WickOperator, NambuOperator, or non-commutative multinomial of fermion creation and annihilation operators."

(* linearity *)

WickExpectation[ws_][z_?CommutativeQ] = z * NormSquare[ws]
(* NOTE: The Wick state is assumed to be normalized. *)

WickExpectation[ws_][z_?CommutativeQ op_] :=
  z * WickExpectation[ws][op]

WickExpectation[ws_][expr_Plus] := 
  WickExpectation[ws] /@ expr


WickExpectation[ws_WickState][HoldPattern @ Multiply[ops__?AnyFermionQ]] :=
  WickExpectation[ws] @ WickOperatorFrom[{ops}, Last @ ws]

WickExpectation[ws:WickState[bb_, cc_]][WickOperator[ops:{___Rule}, ___]] := Module[
  { aa = theConjugateReverse[bb],
    mat },
  mat = WickMatrix @ Join[aa, ops, bb];
  Pfaffian[mat] (* NOTE: The Wick state is assumed to be normalized. *)
]

(**** </WickExpectation> ****)


(**** <WickGreenFunction> ****)

WickGreenFunction::usage = "WickGreenFunction[ws] returns the pair {G, F} of normal Green's function G and anomalous Green's function F with respect to Wick state ws.\nWickGreenFunction[ws, {d1, d2, \[Ellipsis]}] calculates the Green's functionns over given fermion modes {d1, d2, \[Ellipsis]} out of all fermion modes in ws."

WickGreenFunction::null = "The null state is encountered: ``."

WickGreenFunction[ws_WickState] :=
  WickGreenFunction[ws, Last @ ws]

WickGreenFunction[ws:WickState[qq_, cc_], dd:{___?FermionQ}] := Module[
  { pp = theConjugateReverse[qq],
    aa, bb, gg, wm, n },
  bb = Lookup[First /@ PositionIndex[cc], dd];
  bb = One[Length @ cc][[bb]];
  aa = Thread[Identity -> bb];
  bb = Thread[Dagger -> bb];

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = WickMatrix[pp];
  wm[[1, 3]] = WickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = WickMatrix[qq];

  n = Length[dd];
  gg = Zero[{n, n}];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[i]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[i]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[i]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, n}
  ];
  Table[
    wm[[1, 2]] = WickMatrix[pp, {aa[[i]], bb[[j]]}];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[{aa[[i]], bb[[j]]}];
    wm[[2, 3]] = WickMatrix[{aa[[i]], bb[[j]]}, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];
  Return[gg] (* NOTE: The Wick state is assumed to be normalized. *)
]

(**** </WickGreenFunction> ****)


(**** <WickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickEntanglementEntropy::usage = "WickEntanglementEntropy[ws, {d1, d2, \[Ellipsis]}] returns the entanglement entropy in the Wick state ws between the subsystem {d1, d2, \[Ellipsis]} \[Subset] {c1, c2, \[Ellipsis], cn} and the rest of the total system {c1,c2,\[Ellipsis],cn} of fermion modes.\nWickEntanglementEntropy[{gg, ff}, {k1, k2, \[Ellipsis]}] or WickEntanglementEntropy[NambuGreen[{gg, ff}], {k1, k2, \[Ellipsis]}] calculates the entanglement entropy from the matrices gg and ff of normal and anomalous Green's functions, respectively. The index list {k1, k2, \[Ellipsis]} specifies the subsystem {ck1,ck2,\[Ellipsis]}\[Subset]{c1,c2,\[Ellipsis],cn}."

WickEntanglementEntropy[dd:{__?FermionQ}][any_] :=
  WickEntanglementEntropy[any, dd]

WickEntanglementEntropy[ws_WickState, dd:{__?FermionQ}] :=
  WickEntanglementEntropy[WickGreenFunction[ws, dd], Range[Length @ dd]]


WickEntanglementEntropy[kk:{__Integer}][ay_] :=
  WickEntanglementEntropy[ay, kk]

WickEntanglementEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___], kk:{__Integer}] :=
  WickEntanglementEntropy[First @ grn, kk]

WickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  theWickEntropy @ Normal @ NambuGreen[{gg, ff}] / 2
]

WickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  theWickEntropy @ grn[[kk, kk]]


theWickEntropy::usage = "theWickEntropy[grn] returns the entropy of the fermionic Gaussian state characterized by the matrix grn of Green's function."

theWickEntropy[grn_?MatrixQ] :=
  QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn]

(**** </WickEntanglementEntropy> ****)


(**** <WickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickMutualInformation::usage = "WickMutualInformation[ws, {d1, d2, \[Ellipsis]}] returns the mutual information in Wick state ws between the subsystem {d1, d2, \[Ellipsis]} \[Subset] {c1, c2, \[Ellipsis], cn} and the rest of the total system {c1,c2,\[Ellipsis],cn} of fermion modes.\nWickMutualInformation[{gg, ff}, {k1, k2, \[Ellipsis]}] or WickMutualInformation[NambuGreen[{gg, ff}] {k1, k2, \[Ellipsis]}] calculates the mutual information from the matrices gg and ff of normal and anomalous Green's functions, respectively. The index list {k1, k2, \[Ellipsis]} specifies the subsystem {ck1,ck2,\[Ellipsis]}\[Subset]{c1,c2,\[Ellipsis],cn}."

WickMutualInformation[dd:{__?FermionQ}][any_] :=
  WickMutualInformation[any, dd]

WickMutualInformation[ws_WickState, dd:{__?FermionQ}] := 
  WickMutualInformation[
    WickGreenFunction[ws], 
    Lookup[First /@ PositionIndex[Last @ ws], dd]
  ]


WickMutualInformation[kk:{__Integer}][spec_] :=
  WickMutualInformation[spec, kk]

WickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] := With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  ( theWickEntropy[Normal @ NambuGreen @ {gg[[kk, kk]], ff[[kk, kk]]}] +
    theWickEntropy[Normal @ NambuGreen @ {gg[[ll, ll]], ff[[ll, ll]]}] -
    theWickEntropy[Normal @ NambuGreen @ {gg, ff}]
  ) / 2
]

WickMutualInformation[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], kk:{__Integer}] :=
  WickMutualInformation[{gg, ff}, kk]

WickMutualInformation[grn_?MatrixQ, kk:{__Integer}] :=
  WickMutualInformation[NambuMatrix @ {grn, 0}, kk]

(**** </WickMutualInformation> ****)


(**** <WickMatrix> ****)

WickMatrix::usage= "WickMatrix[spec] constructs the so-called Wick matrix, an anti-symmetric matrix with elements of Wick contractions between two fermion operators."

WickMatrix::dim = "The second dimension of the `` matrix cannot be odd; something is fatally wrong."

(* backward compatibility *)
WickMatrix[ass:{Rule[Identity|Dagger, _?VectorQ]...}] :=
  WickMatrix[{Keys @ ass, SparseArray @ Values @ ass}]

(* for the normal models *)
WickMatrix[{tag_?VectorQ, trs_?MatrixQ}] := Module[
  { kk, ii, jj, ij, rr },
  kk = PositionIndex[tag];
  ii = kk[Identity];
  jj = kk[Dagger];
  If[ MissingQ[ii] || MissingQ[jj],
    Return @ Zero @ {Length @ tag, Length @ tag}
  ];
  rr = trs[[ii]] . Transpose[ trs[[jj]] ];
  ij = Tuples @ {ii, jj};
  kk = First[#] < Last[#]& /@ ij;
  ij = Pick[ij, kk];
  rr = Pick[Flatten @ rr, kk];
  rr = Join[
    Thread[ij -> rr],
    Thread[Reverse /@ ij -> -rr]
  ];
  SparseArray[rr, Length[tag]*{1, 1}]
]
(* NOTE: This method makes use of the built-in function Dot, and is faster than other methods using MapApply, etc., on selected elements of ij. *)

(* backward compatibility *)
WickMatrix[aa:{___Rule}, bb:{___Rule}] :=WickMatrix[
  {Keys @ aa, SparseArray @ Values @ aa},
  {Keys @ bb, SparseArray @ Values @ bb}
]

(* for the normal models *)
WickMatrix[{atag_?VectorQ, atrs_?MatrixQ}, {btag_?VectorQ, btrs_?MatrixQ}] :=
Module[
  { kk, ii, jj, ij, rr },
  ii = Lookup[PositionIndex @ atag, Identity];
  jj = Lookup[PositionIndex @ btag, Dagger];
  If[ MissigQ[ii] || MissingQ[jj], 
    Return @ Zero @ {Length @ atag, Length @ btag}
  ];
  rr = atrs[[ii]] . Transpose[ btrs[[jj]] ];
  rr = Thread[ Tuples[{ii, jj}] -> Flatten[rr] ];
  SparseArray[rr, {Length @ atag, Length @ btag}]
]


(* for the BdG models *)
WickMatrix[jmp_?MatrixQ] := Module[
  { m = Length[jmp],
    aa, bb, mat },
  {aa, bb} = First @ PartitionInto[jmp, {1, 2}];
  mat = aa . Transpose[bb];
  Table[mat[[i,i]] = 0, {i, m}];
  Table[
    mat[[j, i]] = -mat[[i, j]],
    {i, m},
    {j, i+1, m}
  ];
  Return[mat]
]

(* for the BdG models *)
WickMatrix[ma_?MatrixQ, mb_?MatrixQ] := Module[
  { aa, bb },
  aa = First @ First @ PartitionInto[ma, {1, 2}];
  bb = Last  @ First @ PartitionInto[mb, {1, 2}];
  aa . Transpose[bb]
]

(**** </WickMatrix> ****)


(**** <WickCircuit> ****)

WickCircuit::usage = "WickCircuit[{g1, g2, \[Ellipsis]}, {c1, c2, \[Ellipsis]}] represents a quantum circuit consisting of Wick gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes c1, c2, \[Ellipsis]."

WickCircuit /:
MakeBoxes[wc:WickCircuit[gg_List, cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", cc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", Short @ gg }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickCircuit /:
  Graphics[wc_WickCircuit, opts___?OptionQ] :=
  Graphics[QuantumCircuit @@ First[wc], opts]

WickCircuit /:
  Show[wc_WickCircuit, opts___?OptionQ] :=
  Graphics[QuantumCircuit @@ First[wc], opts]

(**** </WickCircuit> ****)


(**** <WickRandomCircuit> ****)

WickRandomCircuit::usage = "WickRandomCircuit[{c1, c2, \[Ellipsis]}, in, ugate, p, dep] simulates a random quantum circuit on fermion modes {c1, c2, \[Ellipsis]} starting from initial state IN, where layers of Gaussian unitary gate ugate alternate with layers of measurements on fermion modes selected randomly with probability p to form an overall depth dep."

WickRandomCircuit::save = "The result could not be saved."

Options[WickRandomCircuit] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "WRC"
}

WickRandomCircuit[
  cc:{__?FermionQ},
  in:(_WickState | _NambuState),
  uu:(_WickUnitary | _NambuUnitary),
  p_?NumericQ,
  t_Integer, 
  OptionsPattern[]
] := 
Module[
  { k = 0,
    progress = 0,
    data, qc, n, m },
  PrintTemporary @ ProgressIndicator @ Dynamic[progress];

  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    (* quantum circuit with randomly selected measurements *)
    qc = Riffle[ Table[uu, t], Measurement /@ RandomPick[cc, p, t] ];
    { Table[
        progress = ++k / (n*m);
        Normalize /@ FoldList[Construct[#2, #1]&, N[in], qc],
        m 
      ],
      WickCircuit[qc, cc]
    },
    n
  ];

  (* save data *)
  If[ OptionValue["SaveData"], 
    PrintTemporary["Saving the data (", ByteCount[data], " bytes) ..."]; 
    file = OptionValue["Filename"];
    If[ file === Automatic,
      file = FileNameJoin @ {
        Directory[],
        ToString[Unique @ OptionValue @ "Prefix"]
      };
      file = StringJoin[file, ".mx"]
    ];
    If[OptionValue["Overwrite"] && FileExistsQ[file], DeleteFile @ file];
    Check[
      Export[file, data];
      Echo[file, "Saved to"],
      Message[WickRandomCircuit::save]
    ]
  ];
  Return[data]
]

(**** </WickRandomCircuit> ****)


RandomWickState::usage = "RandomWickState[k, {c1, c2, \[Ellipsis]}] randomly generates a depth k Wick state with half filling on fermion modes {c1, c2, \[Ellipsis]}."

RandomWickState[cc:{__?FermionQ}] :=
  RandomWickState[RandomChoice @ Range[2,10,2], cc]

RandomWickState[k_Integer?Positive, cc:{__?FermionQ}] := Module[
  { ff, mm, in },
  ff = {Identity, Dagger};
  ff = PadRight[ff, k, ff];
  ff = Permute[ff, RandomPermutation[k]];
  mm = Table[RandomVector[Length @ cc], k];
  in = WickState[Dagger@cc[[;; ;;2]], cc];
  Normalize[ WickOperator[Thread[ff -> mm], cc][in] ]
]


(**** <WickDensityOpeator> ****)

WickDensityMatrix::usage = "WickDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function grn, assuming that grn is associated with a fermionic Gaussian state.\nWickDensityMatrix[ws] returns the density matrix corresponding to Wick state ws."

WickDensityMatrix::num = "Only numerical matrices are allowed."

WickDensityMatrix[grn_?MatrixQ] := Module[
  { n = Length[grn],
    cc, gg, uu, id },  
  (* Jordan-Wigner transformation *)
  cc = SparseArray[
    { {i_, i_} -> 4,
      {i_, j_} /; i > j -> 3,
      {_, _} -> 0 },
    {n, n}
  ];
  cc = ThePauli /@ Normal[cc]; (* bare modes *)

  id = One @ Power[2, n];

  {gg, uu} = Eigensystem[N @ grn];
  (* NOTE: N[...] is to avoid additional normaliztaion of uu and sorting. *)
  cc = Conjugate[uu] . cc; (* dressed modes *)
  cc = MapThread[Dot, {Topple /@ cc, cc}];
  cc = MapThread[#1*id + (1-2*#1)*#2&, {gg, cc}];
  Dot @@ cc
] /; If[ MatrixQ[grn, NumericQ], True,
  Message[WickDensityMatrix::num];
  False
]

WickDensityMatrix[ws_WickState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
]

(**** </WickDensityOpeator> ****)

End[]

EndPackage[]
