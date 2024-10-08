BeginPackage["Q3`"]

{ WickLogarithmicNegativity, WickTimeReversalMoment };
{ WickEntropy, WickEntanglementEntropy, WickMutualInformation };

{ FermiMeasurement };

{ WickMatrix, WickElements };

{ WickState, WickGaussian, WickUnitary };
{ WickOperator, WickOperatorFrom };
{ WickExpectation, WickGreenFunction };

{ WickDensityMatrix };

{ WickCircuit, RandomWickCircuit, RandomWickCircuitSimulate };

{ NoisyWickSimulate };
{ WickDampingOperator };

{ RandomWickState, RandomNambuState };
{ RandomWickOperator };

{ NambuState, NambuOperator, NambuUnitary, NambuGaussian,
  NambuHermitian, NambuGreen,  NambuMatrix, NambuMatrixQ }; 
{ QuantumLog }; (* mainly in vonNeumann.wl *)

Begin["`Private`"]

(**** <WickTimeReversalMoment> ****)

WickTimeReversalMoment::usage = "WickTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nWickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to WickTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

WickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[WickTimeReversalMoment] = { "Epsilon" -> 1.25*^-5 } (* 1.0*^-8 is also a reasonable choice *)


WickTimeReversalMoment[alpha_, NambuGreen[{g_?MatrixQ, f_?MatrixQ}, ___], rest__] := 
  WickTimeReversalMoment[alpha, {g, f}, rest]

WickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  WickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk, opts]

WickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts___?OptionQ] := 
  Quiet[theTimeReversalMoment[alpha, {grn, anm}, kk, opts], Inverse::luc]
(* 2024-08-11: Inverse::luc is silenced; the warning message does not seem to be serious in most cases, but goes off too often. *)

(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)
theTimeReversalMoment[
  alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer},
  OptionsPattern[WickTimeReversalMoment]
] := Module[
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
  Check[pf2 /= pf1, Message[WickTimeReversalMoment::infy, pf2/pf1]; pf2 = 0];

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

WickLogarithmicNegativity::usage = "WickLogarithmicNegativity[grn, {k1, k2, \[Ellipsis]}] returns the logarithmic entanglement negativity between the subsystem consisting of fermion modes {k1, k2,\[Ellipsis]}\[Subset]{1,2,\[Ellipsis],n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickLogarithmicNegativity[NambuGreen[{grn, anm}], {k1, k2,\[Ellipsis]}] or WickLogarithmicNegativity[{grn, anm}, {k1, k2,\[Ellipsis]}] returns the logarithmic negativity in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickLogarithmicNegativity[state, {k1, k2, \[Ellipsis]}] is equivalent to WickLogarithmicNegativity[WickGreenFunction[state], {k1, k2,\[Ellipsis]}] for state = WickState or NambuState."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

Options[WickLogarithmicNegativity] = Options[WickTimeReversalMoment]

(* canonical form for normal models *)
(* SEE ALSO: Shpurian and Ryu (2019b) and  Alba and Carollo (2023) *)
WickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___?OptionQ] := Module[
  { n = Length[grn],
    ll, gg, gp, gm, cx, id },
  ll = Supplement[Range @ n, kk];
  id = One[{n, n}];
  gg = 2*Transpose[grn] - id;
  gp = ArrayFlatten @ {
    { -gg[[kk, kk]], +I*gg[[kk, ll]] },
    { +I*gg[[ll, kk]], +gg[[ll, ll]] }
  };
  gm = ArrayFlatten @ {
    { -gg[[kk, kk]], -I*gg[[kk, ll]] },
    { -I*gg[[ll, kk]], +gg[[ll, ll]] }
  };
  cx = (id - Inverse[id + gp.gm].(gp + gm)) / 2;
  cx = Eigenvalues[cx];
  gg = Eigenvalues[id - Transpose[grn]];
  Total[Log[2, Sqrt[cx] + Sqrt[1-cx]]] + Total[Log[2, gg^2 + (1-gg)^2]]/2
]


(* operator form *)
WickLogarithmicNegativity[kk:{__Integer}][any_] :=
  WickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[WickLogarithmicNegativity, "Epsilon"]]

(* shortcut *)
WickLogarithmicNegativity[ws_WickState, kk:{__Integer}, ___] :=
  WickLogarithmicNegativity[WickGreenFunction @ ws, kk]

(**** </WickLogarithmicNegtivity> ****)


AddElaborationPatterns[_WickState, _WickGaussian, _WickUnitary, _WickOperator];


(**** <WickState> ****)

WickState::usage = "WickState[spec] represents a many-body state of non-interacting fermion modes."

WickState::trs = "Inconsistent transformations ``; each transformation must be specified either {mat, mat} or mat form."

WickState::mat = "Wick state `` is defined for `` fermion modes while `` includes `` fermion modes."

WickState::frm = "No fermion modes in ``."

WickState::null = "`` is the null state."

SetAttributes[WickState, NHoldAll]

WickState /:
MakeBoxes[ws:WickState[{flag_?VectorQ, trs_?MatrixQ}, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", Length @ Transpose @ trs },
      BoxForm`SummaryItem @ { "Depth: ", Length @ flag }
    },
    { BoxForm`SummaryItem @ { "Operator flags: ", ArrayShort @ flag },
      BoxForm`SummaryItem @ { "Operator transforms: ", ArrayShort @ trs }   
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickState /: (* vacuum state times a constant *)
MakeBoxes[ws:WickState[{z_?NumericQ, n_Integer}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Type: ", Switch[z, 0, Null, _, Vacuum] }
    },
    { BoxForm`SummaryItem @ { "Norm: ", Abs[z] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* vacuum state *)
(* WickState[{0, n}]: the null state  *)
(* WickState[{1, n}]: the vacuum state  *)
(* WickState[{z, n}]: the vacuum state times the overall constant z *)
WickState[n_Integer] := WickState[{1, n}] (* vacuum state *)

(* initialization *)
WickState[vv_/;VectorQ[vv, BinaryQ], n_Integer] := Module[
  { ww = PadRight[vv, n, vv],
    kk },
  kk = Flatten @ Position[ww, 1];
  If[ kk == {},
    WickState[{1, n}],
    WickState @ {
      ConstantArray[1, Length @ kk],
      One[n][[kk]]
    }
  ]
]

(* initialization *)
WickState[vv_/;VectorQ[vv, BinaryQ]] :=
  WickState[vv, Length @ vv]

(* initialization *)
WickState[Rule[n_Integer, vv_/;VectorQ[vv, BinaryQ]], ___] := 
  WickState[vv, n]

(* initialization *)
(* backward compatibility *)
WickState[Rule[cc:{__?FermionQ}, vv_/;VectorQ[vv, BinaryQ]], ___] := 
  WickState[vv, Length @ cc]

(* initialization *)
WickState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  WickState[Lookup[aa, cc], Length @ cc]
]


WickState /:
NormSquare[WickState[jmp:{_?VectorQ, _?MatrixQ}]] := With[
  { mat = WickMatrix @ WickJoin[WickConjugateReverse @ jmp, jmp] },
  If[ Length[mat] > MatrixRank[mat], 0,
    Quiet[Re @ Sqrt @ Det @ mat, Det::luc]
  ]
] 


WickState /:
NormSquare[WickState[{z_?NumericQ, n_Integer}]] :=
  AbsSquare[z]


WickState /:
Norm[ws_WickState] := Sqrt[NormSquare @ ws]


WickState /: (* vacuum state *)
Normalize[WickState[{z_?NumericQ, n_Integer}], ___] =
  WickState[{1, n}]

WickState /:
Normalize[ws:WickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  { tag = flag,
    new },
  Quiet @ Check[
    new = trs * Power[Norm @ ws, -1/Length[flag]],
    tag = 1;
    new = FermionCount[ws]
  ];
  WickState[{tag, new}]
]

(* NOTE: Just for tests. Equivalent to the above. *)
NormalizeQR[WickState[flag_?VectorQ, trs_?MatrixQ]] := Module[
  {qq, rr},
  {qq, rr} = QRDecomposition[Transpose @ trs];
  WickState[{flag, Conjugate @ qq}]
] /; ContainsOnly[flag, {1}]


WickState /: (* vacuum state *)
Times[z_?NumericQ, WickState[{x_?NumericQ, n_Integer}]] :=
  WickState[z x, n]

WickState /:
Times[z_?NumericQ, WickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  { new },
  new = trs * Power[z, 1/Length[flag]];
  WickState[{flag, new}]
]
(* NOTE: z must be real. *)
(* TODO: Extend it for complex z. *)


WickState /:
ExpressionFor[ws_WickState, cc:{__?FermionQ}] := Module[
  { ff = WickElements[ws, cc] },
  KetChop[ Multiply @@ Append[ff, Ket[cc]] ]
]

WickState /:
Matrix[ws:WickState[{flag_?VectorQ, trs_?MatrixQ}, ___], ss:{__?SpeciesQ}] :=
  With[
    { ff = WickElements[ws, Fermions @ ss] },
    SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ff, ss]
    ]
  ] /; If[ FermionCount[ws] === Length[Fermions @ ss], True,
      Message[WickState::mat, ws, FermionCount[ws], ss, Length @ Fermions @ ss]; False
    ]

WickState /:
Matrix[ws:WickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  { n = Last[Dimensions @ trs],
    c },
  Let[Fermion, c];
  Matrix[ws, c @ Range @ n]
]


WickState /:
NonCommutativeQ[_WickState] = True

WickState /:
MultiplyKind[_WickState] = Fermion

(**** </WickState> ****)


(**** <FermionCount> ****)

FermionCount::usage = "FermionCount[obj] returns the number of fermion modes that object obj is defined for."

FermionCount[WickState[{_?NumericQ, n_Integer}, ___]] = n

FermionCount[WickState[{_?VectorQ, trs_?MatrixQ}, ___]] := Last[Dimensions @ trs]

FermionCount[NambuState[{u_?MatrixQ, _?MatrixQ}, ___]] := Length[u]

FermionCount[WickOperator[{_?VectorQ, trs_?MatrixQ}, ___]] := Last[Dimensions @ trs]

FermionCount[FermiMeasurement[k_Integer, ___?OptionQ]] = k

FermionCount[FermiMeasurement[kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[FermiMeasurement[{}, ___?OptionQ]] = 0

FermionCount[WickGaussian[{_?MatrixQ, _?MatrixQ}, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[WickGaussian[{mat_?MatrixQ, _?MatrixQ}, ___]] := Length[mat]

FermionCount[WickUnitary[_?MatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[WickUnitary[mat_?MatrixQ, ___]] := Length[mat]

FermionCount[NambuUnitary[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuUnitary[uv_?NambuMatrixQ, ___]] := Length[First @ uv]

FermionCount[NambuHermitian[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuHermitian[ham_?NambuMatrixQ, ___]] := Length[First @ ham]

FermionCount[NambuGreen[_?NambuMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NambuGreen[grn_?NambuMatrixQ, ___]] := Length[First @ grn]

FermionCount[WickCircuit[gg_List, ___?OptionQ]] := Max[FermionCount /@ gg]

(**** </FermionCount> ****)


WickJoin::usage = "WickJoin[{flag1, mat1}, {flag2, mat2}, \[Ellipsis]] combines pairs of flag and matrix to an overall pair {flag and matrix}."

WickJoin[any_] = any

WickJoin[a:{_?VectorQ, _?MatrixQ}, b:{_?VectorQ, _?MatrixQ}..] :=
  Join @@@ Transpose[{a, b}]

WickJoin[ops__WickOperator] :=
  WickOperator @ Apply[WickJoin, First /@ {ops}]


WickSplit::usage = "WickSplit returns splits {flags, vectors} into individual pairs of flag and vector."

WickSplit[data : {_?VectorQ, _?MatrixQ}] := 
  Map[List, Transpose@data, {2}]

WickSplit[WickOperator[data : {_?VectorQ, _?MatrixQ}]] :=
  WickOperator /@ WickSplit[data]

WickSplit[ops : {__WickOperator}] :=
  WickSplit[WickJoin @@ ops]


(**** <RandomWickState> ****)

RandomWickState::usage = "RandomWickState[k, n] randomly generates a depth k Wick state with half filling on n fermion modes.\nRandomWickState[n] chooses depth k randomly from {2, 4, \[Ellipsis], n}."

RandomWickState[cc:{__?FermionQ}] :=
  RandomWickState[Length @ cc]

RandomWickState[n_Integer] :=
  RandomWickState[RandomChoice @ Range[2, n, 2], n]

RandomWickState[k_Integer?Positive, n_Integer] := Module[
  { in, ff, mm },
  in = WickState[{1, 0}, n];
  ff = PadRight[{0, 1}, k, {0, 1}];
  ff = Permute[ff, RandomPermutation @ k];
  mm = RandomMatrix[{k, n}];
  Normalize[WickOperator[{ff, mm}] @ in]
]

(**** </RandomWickState> ****)


(**** <WickGaussian> ****)

WickGaussian::usage = "WickGaussian[{mat, inv}] represents a non-unitary operator of the Gaussian form that is specified by the pair {mat, inv} of mutually inverse matrices.\nWickGaussian[mat] is automatically converted to WickGaussian[{mat, inv}], where inv is the inverse of matrix mat."

WickGaussian::num = "Matrix `` needs to be numeric."

SetAttributes[WickGaussian, NHoldRest]

WickGaussian /:
MakeBoxes[WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, rest___], fmt_] := Module[
  { kk = {rest} },
  kk = Which[
    Length[kk] == 0, All,
    MatchQ[First @ kk, {__Integer}], First[kk],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    WickGaussian, mat, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ kk },
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


WickGaussian[{mat_/;MatrixQ[mat, NumericQ], inv_/;MatrixQ[inv, NumericQ]}, ___][
  ws:WickState[{_?NumericQ, n_Integer}] (* vacuum state *)   
] = ws

WickGaussian[{mat_/;MatrixQ[mat, NumericQ], inv_/;MatrixQ[inv, NumericQ]}, ___?OptionQ][
  WickState[{flag_?VectorQ, trs_?MatrixQ}]
] := 
  Module[
    { kk = PositionIndex[flag],
      mm = trs},
    If[Not[MissingQ @ kk @ 0], mm[[kk @ 0]] = mm[[kk @ 0]] . inv];
    If[Not[MissingQ @ kk @ 1], mm[[kk @ 1]] = mm[[kk @ 1]] . Transpose[mat]];
    WickState[{flag, mm}]
  ]


WickGaussian /:
MatrixForm[op : WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___]] :=
  MatrixForm /@ {mat, inv}

WickGaussian /:
ArrayShort[op : WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___]] :=
  ArrayShort /@ {mat, inv}

WickGaussian /: 
NonCommutativeQ[_WickGaussian] = True

WickGaussian /:
MultiplyKind[_WickGaussian] = Fermion

WickGaussian /:
Multiply[pre___, op_WickGaussian, ws_WickState] := Multiply[pre, op @ ws]

WickGaussian /:
Multiply[pre___, op_WickGaussian, fs_Ket] := Multiply[pre, op @ WickState @ fs]

(* 
WickGaussian /:
Matrix[op:WickGaussian[{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___]] := Matrix[op, cc]
 *)
WickGaussian /:
Matrix[WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___?OptionQ], ss:{__?SpeciesQ}] := Module[
  { ff = Select[ss, FermionQ],
    rr = Select[ss, Not @* FermionQ],
    mm, nf },
  nf = Length[ff];
  
  (* Jordan-Wigner transformation *)
  mm = Table[PadRight[Table[3, k-1], nf], {k, nf}] + 4*One[nf];
  mm = ThePauli /@ mm;

  MatrixExp @ TensorContract[
    Transpose[Topple /@ mm, {3, 1, 2}] . MatrixLog[mat] . mm,
    {{2, 3}}
  ]
]

WickGaussian /: (* fallback *)
Matrix[wu_WickGaussian, rest___] := wu * Matrix[1, rest]

(**** </WickGaussian> ****)


(**** <WickUnitary> ****)

WickUnitary::usage = "WickUnitary[u] represents the Gaussian-type unitary operator that transforms n fermion modes according to n\[Times]n unitary matrix u.\nWickUnitary[1, n] is equivalent to WickUnitary[I], where I is the n\[Times]n identity matrix."

SetAttributes[WickUnitary, NHoldRest]

WickUnitary /:
MakeBoxes[op:WickUnitary[trs_?MatrixQ, rest___], fmt_] := Module[
    { kk = {rest} },
  kk = Which[ 
    Length[cc] == 0, All,
    MatchQ[First @ kk, {__Integer}], First[kk],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    WickUnitary, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ kk },
      BoxForm`SummaryItem @ { "Dimensions: ", Dimensions @ trs }
    },
    { BoxForm`SummaryItem @ { "Transform: ", ArrayShort @ trs }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; ArrayQ[trs]


(* null operator *)
WickUnitary[{0, n_Integer}, rest___] :=
  WickUnitary[Zero[n*{1, 1}], rest]

(* identity operator *)
WickUnitary[{1, n_Integer}, rest___] :=
  WickUnitary[One[n], rest]


WickUnitary /:
Times[z_?CommutativeQ, WickUnitary[uu_, rest___]] := WickUnitary[z * uu, rest]

WickUnitary /:
Plus[WickUnitary[a_, kk_, opts___?OptionQ], WickUnitary[b_, kk_, more___?OptionQ]] :=
  WickUnitary[a + b, kk, Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Plus[WickUnitary[a_, opts___?OptionQ], WickUnitary[b_, more___?OptionQ]] :=
  WickUnitary[a + b, Sequence @@ Flatten @ {opts, more}]


WickUnitary /:
Dot[WickUnitary[a_, kk_, opts___?OptionQ], WickUnitary[b_, kk_, more___?OptionQ]] :=
  WickUnitary[Dot[a, b], kk, Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Dot[WickUnitary[a_, opts___?OptionQ], WickUnitary[b_, more___?OptionQ]] :=
  WickUnitary[Dot[a, b], Sequence @@ Flatten @ {opts, more}]

WickUnitary /:
Dagger[WickUnitary[mat_?MatrixQ, rest___]] := WickUnitary[Topple @ mat, rest]


WickUnitary /:
ExpressionFor[wu:WickUnitary[_?MatrixQ, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ wu, cc]

WickUnitary /: (* fallback *)
ExpressionFor[wu_WickUnitary, ___] = wu


WickUnitary /:
Matrix[WickUnitary[trs_?MatrixQ, ___?OptionQ], cc:{__?FermionQ}] := 
  Matrix[WickGaussian @ {trs, Topple @ trs}, cc]

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

WickUnitary[mat_/;MatrixQ[mat, NumericQ], ___][
  ws:WickState[_?NumericQ, n_Integer] (* vacuum state *)   
] = ws

WickUnitary[mat_/;MatrixQ[mat, NumericQ], ___][
  WickState[{flag_?VectorQ, trs_?MatrixQ}]
] := Module[
  { kk = PositionIndex[flag],
    mm = trs },
  If[Not[MissingQ @ kk @ 0], mm[[kk @ 0]] = mm[[kk @ 0]] . Topple[mat]];
  If[Not[MissingQ @ kk @ 1], mm[[kk @ 1]] = mm[[kk @ 1]] . Transpose[mat]];
  WickState[{flag, mm}]
]

WickUnitary[spec__][fs_Ket] := WickUnitary[spec][WickState @ fs]

(**** </WickUnitary> ****)


(**** <WickConjugateReverse> ****)

WickConjugateReverse::usage = "WickConjugateReverse[mat] reverses the order of the rows and takes the complex conjugate of the elements of matrix mat.\nWickConjugateReverse[flags] interchanges each flag (0 <-> 1) and reverses the order of the entries of list flags.\nWickConjugateReverse[{flags, mat}] returns the pair {newFlags, newMat}."

WickConjugateReverse[trs_?MatrixQ] :=
  Reverse @ Conjugate @ trs

WickConjugateReverse[tag_?VectorQ] :=
  Reverse @ Mod[1 + tag, 2]

WickConjugateReverse[{tag_?VectorQ, trs_?MatrixQ}] := {
  WickConjugateReverse[tag],
  WickConjugateReverse[trs]
}

(**** </WickConjugateReverse> ****)


(**** <WickElements> ****)

WickElements::usage = "WickElements[spec, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion operators corresponding to specification spec."

WickElements::incmp = "Transformation matrix `` is intended for `` fermion modes while `` includes `` fermion modes."


WickElements[{flag_?VectorQ, trs_?MatrixQ}, cc:{__?FermionQ}] := Module[
  { kk = PositionIndex[flag],
    new = trs },
  If[Not[MissingQ @ kk @ 0], new[[kk @ 0]] = Dot[trs[[kk @ 0]], cc]];
  If[Not[MissingQ @ kk @ 1], new[[kk @ 1]] = Dot[trs[[kk @ 1]], Dagger @ cc]];
  new
] /; If[ Last[Dimensions @ trs] === Length[cc], True,
    Message[WickElements::incmp, trs, Last[Dimensions @ trs], cc, Length @ cc]; False
  ]

WickElements[WickState[{flag_?VectorQ, trs_?MatrixQ}], cc:{__?FermionQ}] :=
  WickElements[{flag, trs}, cc]

WickElements[WickState[{_?NumericQ, _Integer}], ___] = {}

WickElements[WickOperator[ops:{_?VectorQ, _?MatrixQ}, ___?OptionQ], cc:{__?FermionQ}] :=
  WickElements[ops, cc]

(**** </WickElements> ****)


(**** <WickOperator> ****)

WickOperator::usage = "WickOperator[{{flag1, flag2, \[Ellipsis]}, {cff1, cff2, \[Ellipsis]}}] represents a product of linear combinations of fermion annihilation (Subscript[flag, i]=0) or creation (Subscript[flag, i]=1) operators with coefficients Subscript[cff, i]={Subscript[z, i1],Subscript[z, i2],\[Ellipsis]}.\nWickOperator[{flag, cff}] is a shortcut for a single linear combination, and is automatically converted into the canonical form WickOperator[{{flag}, {cff}}].\nWickOperator[{{k1, f1}, {k2, f2}, \[Ellipsis]}, n] returns a WickOperator object representing a product of simple creation (Subscript[f, i]=1) or annihilation (Subscript[f, i]=0) operators of the Subscript[k, i]th fermion mode among overall n fermion modes."

WickOperator::flag = "`` is not a proper list of binary-coded flags."

SetAttributes[WickOperator, NHoldAll]

WickOperator /:
MakeBoxes[op:WickOperator[{flag_?VectorQ, trs_?MatrixQ}, rest___], fmt_] := Module[
  { kk = {rest} },
  kk = Which[ 
    Length[kk] == 0, All,
    MatchQ[First @ kk, {__Integer}], First[kk],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    WickOperator, op, None,
    { BoxForm`SummaryItem @ { "Target: ", ArrayShort @ kk },
      BoxForm`SummaryItem @ { "Operators: ", Length @ trs }
    },
    { BoxForm`SummaryItem @ { "Flags: ", ArrayShort @ flag },
      BoxForm`SummaryItem @ { "Transforms: ", ArrayShort @ trs }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]


(* canonicalziation *)
WickOperator[{flag:(0|1), cff_?VectorQ}, rest___] :=
  WickOperator[{{flag}, {cff}}]

(* shortcut *)
WickOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  {kk, flag},
  {kk, flag} = Transpose[spec];
  WickOperator[{flag, One[n][[kk]]}, opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[WickOperator::flag, flag]; False 
  ]
]

(* shortcut *)
WickOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  WickOperator[{spec}, n]


WickOperator[{}][any_] = any

WickOperator[jmp:{_?VectorQ, _?MatrixQ}, ___][WickState[trs:{_?VectorQ, _?MatrixQ}]] :=
  WickState @ WickJoin[jmp, trs]

WickOperator[jmp:{_?VectorQ, _?MatrixQ}, ___][WickState[{z_?NumericQ, n_Integer}]] :=
  z * WickState[jmp] /; Last[Dimensions @ Last @ jmp] == n


WickOperator /:
Dagger @ WickOperator[ops:{_?VectorQ, _?MatrixQ}, rest___] :=
  WickOperator[WickConjugateReverse @ ops, rest]


WickOperator /: 
NonCommutativeQ[_WickOperator] = True

WickOperator /:
MultiplyKind[_WickOperator] = Fermion

WickOperator /:
Multiply[pre___, aa_WickOperator, bb__WickOperator, post___] :=
  Multiply[pre, WickOperator[Join @@ Transpose[First /@ {aa, bb}]], post]

WickOperator /:
Multiply[pre___, op_WickOperator, ws_WickState] := Multiply[pre, op[ws]]

WickOperator /:
Multiply[pre___, op_WickOperator, fs_Ket] := Multiply[pre, op[WickState @ fs]]


WickOperator /:
Matrix[WickOperator[{flag_?VectorQ, trs_?MatrixQ}, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Dot @@ Matrix[WickElements[{flag, trs}, cc], ss]
]

WickOperator /:
Matrix[op:WickOperator[{flag_?VectorQ, trs_?MatrixQ}, ___]] := Module[
  { n = Last[Dimensions @ trs],
    c },
  Let[Fermion, c];
  Matrix[op, c @ Range @ n]
]

WickOperator /: (* fallback *)
Matrix[op_WickOperator, rest___] := op * Matrix[1, rest]

WickOperator /:
ExpressionFor[WickOperator[trs:{_?VectorQ, _?MatrixQ}, ___], cc:{__?FermionQ}] :=
  Apply[Multiply, WickElements[trs, cc]]

WickOperator /: (* fallback *)
ExpressionFor[op_WickOperator, __] = op 


WickOperator /:
VacuumExpectation[WickOperator[jmp:{_?VectorQ, _?MatrixQ}, ___]] :=
  Pfaffian @ WickMatrix[jmp]

(**** </WickOperator> ****)


RandomWickOperator::usage = "RandomWickOperator[k, n] randomly generates a depth k Wick operator for n fermion modes.\nRandomWickOperator[n] selects k randomly from {2, 4, \[Ellipsis], n}."

(* backward compatibility *)
RandomWickOperator[cc:{__?FermionQ}] :=
  RandomWickOperator[Length @ cc]

RandomWickOperator[n_Integer] :=
  RandomWickOperator[RandomChoice @ Range[2, n, 2], n]

RandomWickOperator[k_Integer?Positive, n_Integer] := Module[
  { ff, mm },
  ff = RandomChoice[{{0, 1}, {1, 0}}];
  ff = PadRight[ff, k, ff];
  ff = Permute[ff, RandomPermutation @ k];
  mm = RandomMatrix[{k, n}];
  WickOperator[{ff, mm}]
]


(**** <WickOperatorFrom> ****)

(* NOTE: In principle, WickOperatorFrom may be integrated into WickOperator, but separating this feature keeps better the performance of WickOperator. *)

WickOperatorFrom::usage = "WickOperatorFrom[expr_, {c1, c2, \[Ellipsis]}] constructs a WickOperator object from linear combination (or a list of linear combinations) expr of fermion operators of fermion modes {c1, c2, \[Ellipsis]}."

WickOperatorFrom::mixed = "Mixed linear combination `` of creation and annihilation operators."

WickOperatorFrom::nlin = "`` is not a linear combination of the creation and annihilation operators of fermion modes ``."

WickOperatorFrom[cc:{__?FermionQ}][spec_] :=
  WickOperatorFrom[spec, cc]

WickOperatorFrom[expr_, cc:{__?FermionQ}] :=
  WickOperator[theWickOperator[expr, cc]] /;
  If[ theWickLinearQ[expr, cc], True,
    Message[WickOperatorFrom::nlin, expr, cc];
    False
  ]


theWickOperator::usage = "theWickOperator[expr, {c1, c2, \[Ellipsis]}] returns the coefficient list of expr in either creation or annihilation operators of fermion modes {c1, c2, \[Ellipsis]}. theWickOperator[expr, {c1, c2, \[Ellipsis], Dagger[c1], Dagger[c2], \[Ellipsis]}] returns the coefficients list of expr in {c1, c2, \[Ellipsis], Dagger[c1], Dagger[c2], \[Ellipsis]}."

theWickOperator[cc:{__?FermionQ}][any_] := theWickOperator[any, cc]

theWickOperator[expr_List, cc:{__?FermionQ}] :=
  WickJoin @@ Map[theWickOperator[cc], expr]

theWickOperator[expr_, cc:{__?FermionQ}] := Module[
  { aa = Coefficient[expr, cc],
    bb = Coefficient[expr, Dagger @ cc]},
  Which[
    ZeroQ @ Norm[aa, Infinity],
    {{1}, {bb}},
    ZeroQ @ Norm[bb, Infinity],
    {{0}, {aa}},
    True, Message[WickOperator::mixed, expr]; {{0}, {aa}}
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


(**** <FermiMeasurement> ****)

FermiMeasurement::usage = "FermiMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nFermiMeasurement[{k1, k2, \[Ellipsis]}] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nFermiMeasurement[spec][ws] simulates the measurement on Wick state ws, and returns the post-measurement state."

SetAttributes[FermiMeasurement, NHoldAll]

FermiMeasurement[k_Integer][ws:WickState[{_?NumericQ, n_Integer}]] := (
  $MeasurementOut[k] = 0;
  WickState[{1, n}]
)

FermiMeasurement[k_Integer][ws:WickState[trs:{_?VectorQ, _?MatrixQ}]] := Module[
  { n = FermionCount[ws],
    nrm = NormSquare[ws],
    msr, dgr, mat, prb },
  msr = First @ WickOperator[{{k, 0}, {k, 1}}, n]; (* c ** Dagger[c] *)
  dgr = WickConjugateReverse[trs];
  mat = WickMatrix @ WickJoin[dgr, msr, trs];
  prb = Quiet[Re @ Sqrt @ Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= nrm;
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[k] = 0;
    WickOperator[{{k, 0}, {k, 1}}, n][ws] / Sqrt[prb*nrm],
    $MeasurementOut[k] = 1;
    WickOperator[{{k, 1}, {k, 0}}, n][ws] / Sqrt[(1-prb)*nrm]
  ]
]

FermiMeasurement[kk:{___Integer}][ws:(_WickState|_NambuState)] :=
  Fold[FermiMeasurement[#2][#1]&, ws, kk]


FermiMeasurement /:
Multiply[pre___, msr_FermiMeasurement, ws_WickState] := 
  Multiply[pre, msr @ ws]

FermiMeasurement /:
Readout[FermiMeasurement[k_]] := Readout[k]

(**** </FermiMeasurement> ****)


(**** <WickExpectation> ****)

WickExpectation::usage = "WickExpectation[ws] represents an expectation value with respect to the Wick or Nambu state ws.\nWickState[ws][expr] returns the expectation value of expr, where expr may be either WickOperator or NambuOperator consistent with ws."

WickExpectation[WickState[bb:{_?VectorQ, _?MatrixQ}]] @
  WickOperator[ops:{_?VectorQ, _?MatrixQ}, ___] := Module[
    { aa = WickConjugateReverse[bb],
      mat },
    mat = WickMatrix @ WickJoin[aa, ops, bb];
    Pfaffian[mat] (* NOTE: The Wick state is assumed to be normalized. *)
  ]

WickExpectation[WickState[{z_?NumericQ, n_Integer}]][op_WickOperator] :=
  AbsSquare[z] * VacuumExpectation[op]

(**** </WickExpectation> ****)


(**** <WickGreenFunction> ****)

WickGreenFunction::usage = "WickGreenFunction[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to WickState ws.\nWickGreenFunction[ns, {k1, k2, \[Ellipsis]}] returns NambuGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NambuState ns.\nWickGreenFunction[in] is equivalent to WickGreenFunction[in, Range[n]], where n is the number of fermion modes for which input Wick or Nambu state in is defined for.\nWickGreenFunction[data] or WickGreenFunction[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Wick or BdG states.\nWickGreenFunction[{k1, k2, \[Ellipsis]}] represents an operator form of WickGreenFunction to be applied to Wick or Nambu state."

WickGreenFunction::null = "The null state is encountered: ``."

(* operator form *)
WickGreenFunction[kk:{___Integer}][in:(_WickState|_NambuState)] :=
  WickGreenFunction[in, kk]

(* shortcut *)
WickGreenFunction[ws_WickState] :=
  WickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for normal models *)
WickGreenFunction[ws:WickState[qq:{_?VectorQ, _?MatrixQ}], kk:{___Integer}] := Module[
  { nc = FermionCount[ws],
    pp = WickConjugateReverse[qq],
    aa, bb, ab, gg, wm },
  bb = One[nc][[kk]];
  aa = Map[List, Transpose @ {ConstantArray[0, Length @ kk], bb}, {2}];
  bb = Map[List, Transpose @ {ConstantArray[1, Length @ kk], bb}, {2}];

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = WickMatrix[pp];
  wm[[1, 3]] = WickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = WickMatrix[qq];

  nc = Length[kk];
  gg = Zero[{nc, nc}];
  Table[
    ab = WickJoin[aa[[i]], bb[[i]]];
    wm[[1, 2]] = WickMatrix[pp, ab];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[ab];
    wm[[2, 3]] = WickMatrix[ab, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, i]] = Quiet[Re @ Sqrt @ Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, nc}
  ];
  Table[
    ab = WickJoin[aa[[i]], bb[[j]]];
    wm[[1, 2]] = WickMatrix[pp, ab];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = WickMatrix[ab];
    wm[[2, 3]] = WickMatrix[ab, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i, j]] = Pfaffian @ ArrayFlatten @ N @ wm;
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, nc},
    {j, i+1, nc}
  ];
  Return[gg] (* NOTE: The Wick state is assumed to be normalized. *)
]

(* vacuum state *)
WickGreenFunction[WickState[{z_?NumericQ, n_Integer}], kk:{___Integer}] :=
  One[Length @ kk]


(* for large data *)
WickGreenFunction[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = N @ Aggregate @ Dimensions[data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; WickGreenFunction[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _WickState | _NambuState]&]

(**** </WickGreenFunction> ****)


WickGreenFunctionQR::usage = "WickGreenFunctionQR[ws, {k1, k2, \[Ellipsis]}] returns ..."

WickGreenFunctionQR::dag = "Only 1 (corresponding to a creator) is allowed in a list of binary-coded flags."
(* NOTE: Just for tests. Equivalent to the above. *)

WickGreenFunctionQR[ws_WickState] :=
  WickGreenFunctionQR[ws, Range @ FermionCount @ ws]

WickGreenFunctionQR[WickState[{flag_?VectorQ, trs_?MatrixQ}], kk:{___Integer}] := Module[
  { cor = Transpose[trs],
    grn },
  grn = cor . Topple[cor];
  grn = One[Dimensions @ grn] - grn;
  grn[[kk, kk]]
] /; If[ ContainsOnly[flag, {1}], True,
    Message[WickGreenFunction::qr]; False
  ]


(**** <WickEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickEntropy::usage = "WickEntropy[grn] returns the von Neumann entropy of a fermionic Gaussian state characterized by the matrix grn of single-particle Green's functions. WickEntropy[NambuGreen[{grn, anm}]] or WickEntropy[{grn, anm}] considers a fermionic Gaussian state characterized by matrices grn and anm of normal and anomalous Green's functions."

(* canonical form for normal models *)
WickEntropy[grn_?MatrixQ] :=
  QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn]

(* canonicalization for BdG models *)
WickEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___]] :=
  theWickEntropy[Normal @ grn] / 2

(* canonicalization for BdG models *)
WickEntropy[grn:{_?MatrixQ, _?MatrixQ}] :=
  WickEntropy[NambuGreen @ grn]


(* shortcut *)
WickEntropy[in:(_WickState|_NambuState)] = 0

(**** </WickEntropy> ****)


(**** <WickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickEntanglementEntropy::usage = "WickEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickEntanglementEntropy[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or WickEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] is equivalent to WickEntanglementEntropy[WickGreenFunction[state, {k1, k2, \[Ellipsis]}], {k1, k2, \[Ellipsis]}] for Wick or BdG state.\nWickEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of WickEntanglementEtropy to be applied to Green's functions, Wick or Nambu state."

(* canonical form for normal models *)
WickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  WickEntropy @ grn[[kk, kk]]

(* canonical form for BdG models *)
WickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  WickEntropy @ Normal @ NambuGreen[{gg, ff}] / 2
]

(* canonicalization for BdG models *)
WickEntanglementEntropy[grn:NambuGreen[{_?MatrixQ, _?MatrixQ}, ___], kk:{__Integer}] :=
  WickEntanglementEntropy[First @ grn, kk]


(* operator form *)
WickEntanglementEntropy[kk:{__Integer}][any_] :=
  WickEntanglementEntropy[any, kk]

(* shortcut *)
WickEntanglementEntropy[in:(_WickState|_NambuState), kk:{__Integer}] :=
  WickEntanglementEntropy[WickGreenFunction[in, kk], kk]

(**** </WickEntanglementEntropy> ****)


(**** <WickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
WickMutualInformation::usage = "WickMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Wick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nWickMutualInformation[NambuGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or WickMutualInformation[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nWickMutualInformation[state, {k1, k2, \[Ellipsis]}] is equivalent to WickMutualInformation[WickGreenFunction[state], {k1, k2, \[Ellipsis]}] for Wick or BdG state.\nWickMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of WickEntanglementEtropy to be applied to Green's functions, Wick or Nambu state."

(* canonical form for normal models *)
WickMutualInformation[gg_?MatrixQ, kk:{__Integer}] :=With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  WickEntropy[ gg[[kk, kk]] ] + WickEntropy[ gg[[ll, ll]] ] - WickEntropy[ gg ]
]

(* canonical form for BdG models *)
WickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] := With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  ( WickEntropy[Normal @ NambuGreen @ {gg[[kk, kk]], ff[[kk, kk]]}] +
    WickEntropy[Normal @ NambuGreen @ {gg[[ll, ll]], ff[[ll, ll]]}] -
    WickEntropy[Normal @ NambuGreen @ {gg, ff}]
  ) / 2
]

(* canonicalization for BdG models *)
WickMutualInformation[NambuGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], kk:{__Integer}] :=
  WickMutualInformation[{gg, ff}, kk]

(* operator form *)
WickMutualInformation[kk:{__Integer}][any_] :=
  WickMutualInformation[any, kk]

(* shortcut for normal models *)
WickMutualInformation[in:(_WickState|_NambuState), kk:{__Integer}] := 
  WickMutualInformation[WickGreenFunction @ in, kk]

(**** </WickMutualInformation> ****)


(**** <WickMatrix> ****)

WickMatrix::usage= "WickMatrix[spec] constructs the so-called Wick matrix, an anti-symmetric matrix with elements of Wick contractions between two fermion operators."

WickMatrix::dim = "The second dimension of the `` matrix cannot be odd; something is fatally wrong."

(* for the normal models *)
WickMatrix[{tag_?VectorQ, trs_?MatrixQ}] := Module[
  { kk, ij, rr },
  kk = PositionIndex[tag];
  If[ MissingQ[kk @ 0] || MissingQ[kk @ 1],
    Return @ Zero @ {Length @ tag, Length @ tag}
  ];
  rr = trs[[kk @ 0]] . Transpose[ trs[[kk @ 1]] ];
  ij = Tuples @ {kk @ 0, kk @ 1};
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

(* for the normal models *)
WickMatrix[{atag_?VectorQ, atrs_?MatrixQ}, {btag_?VectorQ, btrs_?MatrixQ}] :=
Module[
  { kk, ii, jj, ij, rr },
  ii = Lookup[PositionIndex @ atag, 0];
  jj = Lookup[PositionIndex @ btag, 1];
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

WickCircuit::usage = "WickCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit consisting of Wick gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes."

WickCircuit /:
MakeBoxes[wc:WickCircuit[gg_List, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", FermionCount @ wc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", Short @ gg }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickCircuit /: 
NonCommutativeQ[_WickCircuit] = True

WickCircuit /:
MultiplyKind[_WickCircuit] = Fermion

WickCircuit /:
Multiply[pre___, wc_WickCircuit, in:(_WickState|_NambuState)] :=
  Multiply[pre, wc @ in]

WickCircuit[gg_List, ___][in:(_WickState|_NambuState)] :=
  Fold[#2[#1]&, in, gg]


WickCircuit /:
Show[wc_WickCircuit, rest___] := Graphics[wc, rest]

WickCircuit /:
Graphics[wc:WickCircuit[gg_List], more___?OptionQ] := Module[
  { c },
  Let[Fermion, c];
  Graphics[wc, c, more]
]

WickCircuit /:
Graphics[wc:WickCircuit[gg_List, opts___?OptionQ], c_Symbol?FermionQ, more___?OptionQ] := Module[
  { n = FermionCount[wc],
    cc, qc },
  cc = c[Range @ n];
  qc = gg /. {
    WickCircuit[{}] -> "Spacer",
    WickCircuit -> Identity,
    WickState[__] :> Ket[ss],
    WickUnitary[_?MatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    WickUnitary[_?MatrixQ, any___?OptionQ] :> Gate[cc, any],
    WickUnitary[_?MatrixQ, _, any___?OptionQ] :> Gate[cc, any],
    NambuUnitary[_?NambuMatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    NambuUnitary[_?NambuMatrixQ, any___?OptionQ] :> Gate[cc, any],
    NambuUnitary[_?NambuMatrixQ, _, any___?OptionQ] :> Gate[cc, any],
    FermiMeasurement[{}, ___] -> "Spacer",
    FermiMeasurement[k_Integer, any___?OptionQ] :> Gate[c @ {k}, any, "Shape" -> "Measurement"],
    FermiMeasurement[kk:{_Integer}, any___?OptionQ] :> Gate[c[kk], any, "Shape" -> "Measurement"],
    FermiMeasurement[kk:{_, __Integer}, any___?OptionQ] :> 
      Map[Gate[{c[#]}, any, "Shape" -> "Measurement"]&, kk]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]

(**** </WickCircuit> ****)


(**** <RandomWickCircuit> ****)

RandomWickCircuit::usage = "RandomWickCircuit[{uni, p}, dep] generate a random quantum circuit on non-interacting fermion modes, where layers of unitary gate uni (either WickUnitary[\[Ellipsis]] or NambuUnitary[\[Ellipsis]]) alternate with layers of measurements (FermiMeasurement[\[Ellipsis]]) on fermion modes selected randomly with probability p to form an overall depth dep.\nRandomWickCircuit[{ham, pdf, p}, k] unitary layers of random unitary gate uni=Exp[-I ham \[Tau]] with single-particle Hamiltonian ham (either n\[Times]n Hermitian matrix or NambuHermitian[\[Ellipsis]]) and the random evolution time \[Tau] distributed according to the probability distribution function pdf.\nRandomWickCircuit[{ham, p}, dep] assumes that the evolution time is uniformly distributed over the interval [0,2\[Pi] n/max], where max is the maximum of the absolute values of the entries of ham.\nRandomWickCircuit[ham, dep] generates a circuit for n fermion modes where each unitary layer corresponds to time evolution U=exp[-I ham \[Tau]] with the evolution time \[Tau] distributed by P(\[Tau])\[Proportional]exp[-n \[Tau]] and each measurement layer measures a fermion mode with probability p=1/n."

RandomWickCircuit[{uu:(_WickUnitary | _NambuUnitary), p_?NumericQ}, k_Integer] :=
  Module[
    { mm },
    mm = RandomPick[Range @ FermionCount @ uu, p, k];
    WickCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[FermiMeasurement, mm]
    ]
  ]

(* arbitrary distribution of evolution time *)
RandomWickCircuit[{ham:(_?MatrixQ|_NambuHermitian), pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = If[MatrixQ @ ham, Length @ ham, FermionCount @ ham],
      ab, tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = randomUnitaryLayer[ham, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[FermiMeasurement, mm];
    WickCircuit @ Riffle[uu, mm]
  ]

(* uniform distribution of evolution time *)
RandomWickCircuit[{ham:(_?MatrixQ|_NambuHermitian), p_?NumericQ}, k_Integer] :=
  Module[
    { n = If[MatrixQ @ ham, Length @ ham, FermionCount @ ham],
      max, pdf },
    max = Max @ Abs @ If[MatrixQ @ ham, ham, First @ ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    RandomWickCircuit[{ham, pdf, p}, k]
  ]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
RandomWickCircuit[ham:(_?MatrixQ|_NambuHermitian), k_Integer] :=
  Module[
    { n = If[MatrixQ @ ham, Length @ ham, FermionCount @ ham] },
    RandomWickCircuit[{ham, ExponentialDistribution[n], 1./n}, k]
  ]


randomUnitaryLayer[ham_?MatrixQ, tt_?VectorQ] :=
  Map[WickUnitary[MatrixExp[-I*ham*#]]&, tt]

randomUnitaryLayer[ham_NambuHermitian, tt_?VectorQ] := With[
  { mat = Normal[ham] },
  Map[NambuUnitary[MatrixExp[-I*mat*#]]&, tt]
]

(**** </RandomWickCircuit> ****)


(**** <RandomWickCircuitSimulate> ****)

RandomWickCircuitSimulate::usage = "RandomWickCircuitSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomWickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

RandomWickCircuitSimulate::save = "The result could not be saved."

Options[RandomWickCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RWC"
}

$RandomWickCircuitPatterns = Alternatives[
  {_WickUnitary, _?NumericQ}, 
  {_NambuUnitary, _?NumericQ},
  {_?MatrixQ, _, _?NumericQ},
  {_?MatrixQ, _?NumericQ},
  {_NambuHermitian, _, _?NumericQ},
  {_NambuHermitian, _?NumericQ},
  _?MatrixQ,
  _NambuHermitian
];

RandomWickCircuitSimulate[
  in:(_WickState | _NambuState),
  spec:$RandomWickCircuitPatterns,
  t_Integer, 
  opts:OptionsPattern[{RandomWickCircuit, RandomWickCircuitSimulate}]
] := 
Module[
  { k = 0,
    progress = 0,
    data, qc, n, m },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];

  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    qc = RandomWickCircuit[spec, t];
    { Table[
        progress = ++k / (n*m);
        FoldList[Construct[#2, #1]&, in, N @ First @ qc],
        (* NOTE: No explicit normalization here because both the unitary and measurement layers produce NORMALIZED states. *)
        m 
      ],
      qc
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
      Message[RandomWickCircuitSimulate::save]
    ]
  ];
  Return[data]
]

(**** </RandomWickCircuitSimulate> ****)


(**** <WickDensityMatrix> ****)

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

(**** </WickDensityMatrix> ****)


(**** <WickDampingOperator> ****)

WickDampingOperator::usage = "WickDampingOperator[jmp] returns a pair {mat, const} of the quadratic kernel mat and remaining constant term const of the effective damping operator in the normal ordering that corresponds to the list jmp of quantum jump operators."

WickDampingOperator::jmp = "Invalid form of quantum jump operators ``."

WickDampingOperator[jmp_WickOperator] :=
  WickDampingOperator[First @ jmp]

WickDampingOperator[jmp:{__WickOperator}] :=
  WickDampingOperator[WickJoin @@ jmp]

WickDampingOperator[{flag_?VectorQ, trs_?MatrixQ}] := Module[
  { kk = PositionIndex[flag],
    aa, bb },
  kk = Join[<|0 -> {}, 1 -> {}|>, kk];
  aa = Topple[trs[[kk @ 0]]] . trs[[kk @ 0]];
  bb = Topple[trs[[kk @ 1]]] . trs[[kk @ 1]];
  If[ MatrixQ[bb],
    {aa - Transpose[bb], Tr[bb]} / 2,
    {aa, 0} / 2
  ]
]

(**** </WickDampingOperator> ****)


(**** <NoisyWickSimulate> ****)

NoisyWickSimulate::usage = "NoisyWickSimulate[ham, jmp, in, {n, dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian matrix ham and the list jmp of quantum jump operators. The simulation starts from the initial WickState in at time 0 and goes n time steps by interval dt."

NoisyWickSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

NoisyWickSimulate::null = "The null state is encountered."

NoisyWickSimulate::save = "The result could not be saved."

Options[NoisyWickSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NWS"
}

NoisyWickSimulate[ ham_, jmp:(_WickOperator|{__WickOperator}),
  in_WickState, {nT_Integer, dt_},
  OptionsPattern[]
] :=
  Module[
    { n = OptionValue["Samples"],
      k = 0,
      progress = 0,
      aa, bb, dmp, fac, non },
    
    {dmp, fac} = WickDampingOperator[jmp];
    fac = Exp[-dt*fac];
    non = ham - I*dmp;
    non = WickGaussian @ {MatrixExp[-I*dt*non], MatrixExp[+I*dt*non]};

    PrintTemporary[ProgressIndicator @ Dynamic @ progress];
    data = Table[
      progress = ++k / n;
      altNoisyWickSimulate[N @ {non, fac}, WickSplit @ jmp, in, {nT, dt}],
      n
    ];
    
    (* save data *)
    If[ OptionValue["SaveData"],
      Module[
        { file, result },
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
        result = Export[file, data];
        If[ FailureQ[result],
          Echo[file, "Data saved to"],
          Echo[file, "Error saving data to"]
        ]
      ]
    ];
    Return[data]
  ] /; If[ MatrixQ[ham, NumericQ], True,
    Message[NoisyWickSimulate::ham, ham];
    False
  ]

altNoisyWickSimulate[{non_WickGaussian, fac_}, jmp:{__WickOperator}, in_WickState, {nT_Integer, dt_}] :=
  Module[
    { n = FermionCount[non],
      res = {in},
      new = in,
      prb, pos, out, tmp, pp, qq, ww, t },
    t = 1;
    While[ t <= nT,
      pp = RandomReal[];
      qq = RandomReal[];
      
      (* non-unitary evolution *)
      out = non[new];
      If[ pp < NormSquare[fac * out],
        new = Normalize @ out;
        AppendTo[res, new];
        t += 1;
        Continue[]
      ];
      
      (* quantum jumps *)
      out = Through[jmp[out]];

      prb = Chop @ Accumulate[NormSquare /@ out];
      Quiet[
        Check[
          prb /= Last[prb],
          (* error *)
          Message[NoisyWickSimulate::null];
          new = WickState[{0, n}]; (* null state *)
          AppendTo[res, new];
          t += 1;
          Continue[],
          {Divide::indet}
        ],
        {Divide::indet}
      ];

      pos = First @ FirstPosition[prb - qq, _?NonNegative];
      new = Normalize @ Part[out, pos];
      AppendTo[res, new];
      t += 1;
    ];
    Return[res]
  ]

(**** </NoisyWickSimulate> ****)


End[]

EndPackage[]
