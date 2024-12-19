BeginPackage["Q3`"]

{ VickLogarithmicNegativity, VickTimeReversalMoment };
{ VickEntropy, VickEntanglementEntropy, VickMutualInformation };

{ VickMatrix, VickElements };

{ VickState, VickGaussian, VickUnitary };
{ VickOperator, VickOperatorFrom };
{ VickGreenFunction, VickOccupation, VickExpectation };
{ FermiMeasurement };

{ RandomVickState, RandomVickGaussian, RandomVickUnitary, RandomVickOperator };

{ VickDensityMatrix };

{ VickCircuit, RandomVickCircuit, RandomVickCircuitSimulate };

{ VickSimulate, VickDampingOperator, 
  VickMonitor };

(* Namvo.wl *)
{ NamvoState, NamvoOperator, NamvoUnitary, NamvoGaussian,
  NamvoHermitian, NamvoGreen,  NamvoMatrix, NamvoMatrixQ }; 

(* vonNeumann.wl *)
{ QuantumLog };

Begin["`Private`"]

(**** <VickTimeReversalMoment> ****)

VickTimeReversalMoment::usage = "VickTimeReversalMoment[\[Alpha], {gg, ff}, {k1, k2, \[Ellipsis]}] returns the \[Alpha]th moment of partial time reversal over the fermion modes (species) k1, k2, \[Ellipsis] for the fermionic Gaussian state characterized by the matrices gg and ff (in an L\[Times]L matrix for L fermion modes) of normal and anomalous Green's funcitons, respectively, and anomalous Green's function anm (also in an L\[Times]L matrix).\nVickTimeReversalMoment[\[Alpha], grn, {k1,k2,\[Ellipsis]}] is equivalent to VickTimeReversalMoment[\[Alpha], {grn, 0}, {k1, k2, \[Ellipsis]}]."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

VickTimeReversalMoment::sing = "The matrix is tamed according to option \"Epsilon\"."

Options[VickTimeReversalMoment] = { "Epsilon" -> 1.25*^-5 } (* 1.0*^-8 is also a reasonable choice *)


VickTimeReversalMoment[alpha_, NamvoGreen[{g_?MatrixQ, f_?MatrixQ}, ___], rest__] := 
  VickTimeReversalMoment[alpha, {g, f}, rest]

VickTimeReversalMoment[alpha_, grn_?MatrixQ, kk:{__Integer}, opts___?OptionQ] :=
  VickTimeReversalMoment[alpha, {grn, Zero[Dimensions @ grn]}, kk, opts]

VickTimeReversalMoment[alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}, opts___?OptionQ] := 
  Quiet[theTimeReversalMoment[alpha, {grn, anm}, kk, opts], Inverse::luc]
(* 2024-08-11: Inverse::luc is silenced; the warning message does not seem to be serious in most cases, but goes off too often. *)

(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)
theTimeReversalMoment[
  alpha_, {grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer},
  OptionsPattern[VickTimeReversalMoment]
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
  gg = Normal @ NamvoHermitian[{gg, -anm}];
  
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
  Check[pf2 /= pf1, Message[VickTimeReversalMoment::infy, pf2/pf1]; pf2 = 0];

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

(**** </VickTimeReversalMoment> ****)


(**** <VickLogarithmicNegtivity> ****)

VickLogarithmicNegativity::usage = "VickLogarithmicNegativity[grn, {k1, k2, \[Ellipsis]}] returns the logarithmic entanglement negativity between the subsystem consisting of fermion modes {k1, k2,\[Ellipsis]}\[Subset]{1,2,\[Ellipsis],n} in the Vick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nVickLogarithmicNegativity[NamvoGreen[{grn, anm}], {k1, k2,\[Ellipsis]}] or VickLogarithmicNegativity[{grn, anm}, {k1, k2,\[Ellipsis]}] returns the logarithmic negativity in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nVickLogarithmicNegativity[state, {k1, k2, \[Ellipsis]}] is equivalent to VickLogarithmicNegativity[VickGreenFunction[state], {k1, k2,\[Ellipsis]}] for state = VickState or NamvoState."
(* SEE ALSO: Shapourian and Ryu (2017, 2019) *)

Options[VickLogarithmicNegativity] = Options[VickTimeReversalMoment]

VickLogarithmicNegativity[grn_?MatrixQ, kk:{}, ___?OptionQ] = 0

VickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___?OptionQ] := 0 /;
  Length[grn] == Length[kk]

(* canonical form for normal models *)
(* SEE ALSO: Shpurian and Ryu (2019b) and  Alba and Carollo (2023) *)
VickLogarithmicNegativity[grn_?MatrixQ, kk:{__Integer}, ___?OptionQ] := Module[
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
VickLogarithmicNegativity[kk:{__Integer}][any_] :=
  VickLogarithmicNegativity[any, kk, "Epsilon" -> OptionValue[VickLogarithmicNegativity, "Epsilon"]]

(* shortcut *)
VickLogarithmicNegativity[ws_VickState, kk:{__Integer}, ___] :=
  VickLogarithmicNegativity[VickGreenFunction @ ws, kk]

(**** </VickLogarithmicNegtivity> ****)


AddElaborationPatterns[_VickState, _VickGaussian, _VickUnitary, _VickOperator];


(**** <VickState> ****)

VickState::usage = "VickState[spec] represents a many-body state of non-interacting fermion modes."

VickState::trs = "Inconsistent transformations ``; each transformation must be specified either {mat, mat} or mat form."

VickState::mat = "Vick state `` is defined for `` fermion modes while `` includes `` fermion modes."

VickState::frm = "No fermion modes in ``."

VickState::null = "`` is the null state."

SetAttributes[VickState, NHoldAll]

VickState /:
MakeBoxes[ws:VickState[{flag_?VectorQ, trs_?MatrixQ}, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    VickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", Length @ Transpose @ trs },
      BoxForm`SummaryItem @ { "Depth: ", Length @ flag }
    },
    { BoxForm`SummaryItem @ { "Operator flags: ", ArrayShort @ flag },
      BoxForm`SummaryItem @ { "Operator transforms: ", ArrayShort @ trs }   
    },
    fmt,
    "Interpretable" -> Automatic
  ]

VickState /: (* vacuum state times a constant *)
MakeBoxes[ws:VickState[{z_?NumericQ, n_Integer}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    VickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", n },
      BoxForm`SummaryItem @ { "Type: ", Switch[z, 0, Null, _, Vacuum] }
    },
    { BoxForm`SummaryItem @ { "Norm: ", Abs[z] }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

(* vacuum state *)
(* VickState[{0, n}]: the null state  *)
(* VickState[{1, n}]: the vacuum state  *)
(* VickState[{z, n}]: the vacuum state times the overall constant z *)
VickState[n_Integer] := VickState[{1, n}] (* vacuum state *)

(* initialization *)
VickState[vv_/;VectorQ[vv, BinaryQ], n_Integer] := Module[
  { ww = PadRight[vv, n, vv],
    kk },
  kk = Flatten @ Position[ww, 1];
  If[ kk == {},
    VickState[{1, n}],
    VickState @ {
      ConstantArray[1, Length @ kk],
      One[n][[kk]]
    }
  ]
]

(* initialization *)
VickState[vv_/;VectorQ[vv, BinaryQ]] :=
  VickState[vv, Length @ vv]

(* initialization *)
VickState[Rule[n_Integer, vv_/;VectorQ[vv, BinaryQ]], ___] := 
  VickState[vv, n]

(* initialization *)
(* backward compatibility *)
VickState[Rule[cc:{__?FermionQ}, vv_/;VectorQ[vv, BinaryQ]], ___] := 
  VickState[vv, Length @ cc]

(* initialization *)
VickState[Ket[aa_Association]] := With[
  { cc = Select[Keys @ aa, FermionQ] },
  VickState[Lookup[aa, cc], Length @ cc]
]


VickState /:
NormSquare[VickState[jmp:{_?VectorQ, _?MatrixQ}]] := Module[
  { mat },
  mat = VickMatrix @ VickJoin[VickConjugateReverse @ jmp, jmp];
  If[ Length[mat] > MatrixRank[mat], 0,
    Quiet[Re @ Sqrt @ Det @ mat, Det::luc]
  ]
] 


VickState /:
NormSquare[VickState[{z_?NumericQ, n_Integer}]] :=
  AbsSquare[z]


VickState /:
Norm[ws_VickState] := Sqrt[NormSquare @ ws]


VickState /: (* vacuum state *)
Normalize[VickState[{z_?NumericQ, n_Integer}], ___] =
  VickState[{1, n}]

VickState /:
Normalize[ws:VickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  { tag = flag,
    new },
  Quiet @ Check[
    new = trs * Power[Norm @ ws, -1/Length[flag]],
    tag = 1;
    new = FermionCount[ws]
  ];
  VickState[{tag, new}]
]

(* NOTE: Just for tests. Equivalent to the above. *)
NormalizeQR[VickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  {qq, rr},
  {qq, rr} = QRDecomposition[Transpose @ trs];
  VickState[{flag, Conjugate @ qq}]
] /; ContainsOnly[flag, {1}]


VickState /: (* vacuum state *)
Times[z_?NumericQ, VickState[{x_?NumericQ, n_Integer}]] :=
  VickState[z x, n]

VickState /:
Times[z_?NumericQ, VickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  { new },
  new = trs * Power[z, 1/Length[flag]];
  VickState[{flag, new}]
]
(* NOTE: z must be real. *)
(* TODO: Extend it for complex z. *)


VickState /:
ExpressionFor[ws_VickState, cc:{__?FermionQ}] := Module[
  { ff = VickElements[ws, cc] },
  KetChop[ Multiply @@ Append[ff, Ket[cc]] ]
]

VickState /:
Matrix[ws:VickState[{flag_?VectorQ, trs_?MatrixQ}, ___], ss:{__?SpeciesQ}] :=
  With[
    { ff = VickElements[ws, Fermions @ ss] },
    SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ff, ss]
    ]
  ] /; If[ FermionCount[ws] === Length[Fermions @ ss], True,
      Message[VickState::mat, ws, FermionCount[ws], ss, Length @ Fermions @ ss]; False
    ]

VickState /:
Matrix[ws:VickState[{flag_?VectorQ, trs_?MatrixQ}]] := Module[
  { n = Last[Dimensions @ trs],
    c },
  Let[Fermion, c];
  Matrix[ws, c @ Range @ n]
]


VickState /:
NonCommutativeQ[_VickState] = True

VickState /:
MultiplyKind[_VickState] = Fermion

(**** </VickState> ****)


(**** <FermionCount> ****)

FermionCount::usage = "FermionCount[obj] returns the number of fermion modes that object obj is defined for."

FermionCount[mat_?MatrixQ] := Last[Dimensions @ mat]

FermionCount[obj_?NamvoMatrixQ] := Length[First @ obj]

FermionCount[VickState[{_?NumericQ, n_Integer}, ___]] = n

FermionCount[VickState[{_?VectorQ, trs_?MatrixQ}, ___]] := Last[Dimensions @ trs]

FermionCount[NamvoState[{u_?MatrixQ, _?MatrixQ}, ___]] := Length[u]

FermionCount[VickOperator[{_?VectorQ, trs_?MatrixQ}, ___]] := Last[Dimensions @ trs]

FermionCount[FermiMeasurement[k_Integer, ___?OptionQ]] = k

FermionCount[FermiMeasurement[kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[FermiMeasurement[{}, ___?OptionQ]] = 0

FermionCount[VickGaussian[{_?MatrixQ, _?MatrixQ}, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[VickGaussian[{mat_?MatrixQ, _?MatrixQ}, ___]] := Length[mat]

FermionCount[VickUnitary[_?MatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[VickUnitary[mat_?MatrixQ, ___]] := Length[mat]

FermionCount[NamvoUnitary[_?NamvoMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NamvoUnitary[uv_?NamvoMatrixQ, ___]] := Length[First @ uv]

FermionCount[NamvoHermitian[_?NamvoMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NamvoHermitian[ham_?NamvoMatrixQ, ___]] := Length[First @ ham]

FermionCount[NamvoGreen[_?NamvoMatrixQ, kk:{__Integer}, ___?OptionQ]] := Max[kk]

FermionCount[NamvoGreen[grn_?NamvoMatrixQ, ___]] := Length[First @ grn]

FermionCount[VickCircuit[gg_List, ___?OptionQ]] := Max[FermionCount /@ gg]

(**** </FermionCount> ****)


VickJoin::usage = "VickJoin[{flag1, mat1}, {flag2, mat2}, \[Ellipsis]] combines pairs of flag and matrix to an overall pair {flag and matrix}."

VickJoin[any_] = any

VickJoin[a:{_?VectorQ, _?MatrixQ}, b:{_?VectorQ, _?MatrixQ}..] :=
  Join @@@ Transpose[{a, b}]

VickJoin[ops__VickOperator] :=
  VickOperator @ Apply[VickJoin, First /@ {ops}]


VickSplit::usage = "VickSplit returns splits {flags, vectors} into individual pairs of flag and vector."

VickSplit[data:{_?VectorQ, _?MatrixQ}] := 
  MapThread[{{#1}, SparseArray @ {#2}}&, data]

VickSplit[VickOperator[data:{_?VectorQ, _?MatrixQ}]] :=
  VickOperator /@ VickSplit[data]

VickSplit[ops:{__VickOperator}] :=
  VickSplit[VickJoin @@ ops]


(**** <RandomVickState> ****)

RandomVickState::usage = "RandomVickState[k, n] randomly generates a depth k Vick state with half filling on n fermion modes.\nRandomVickState[n] chooses depth k randomly from {2, 4, \[Ellipsis], n}."

RandomVickState[cc:{__?FermionQ}] :=
  RandomVickState[Length @ cc]

RandomVickState[n_Integer] :=
  RandomVickState[RandomChoice @ Range[2, n, 2], n]

RandomVickState[k_Integer?Positive, n_Integer] := Module[
  { in, op },
  in = VickState[{1, 0}, n];
  op = RandomVickOperator[k, n];
  Normalize[op @ in]
]

(**** </RandomVickState> ****)


(**** <VickGaussian> ****)

VickGaussian::usage = "VickGaussian[{mat, inv}] represents a non-unitary operator of the Gaussian form that is specified by the pair {mat, inv} of mutually inverse matrices.\nVickGaussian[mat] is automatically converted to VickGaussian[{mat, inv}], where inv is the inverse of matrix mat."

VickGaussian::num = "Matrix `` needs to be numeric."

SetAttributes[VickGaussian, NHoldRest]

VickGaussian /:
MakeBoxes[VickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, rest___], fmt_] := Module[
  { kk = {rest} },
  kk = Which[
    Length[kk] == 0, All,
    MatchQ[First @ kk, {__Integer}], First[kk],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    VickGaussian, mat, None,
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
VickGaussian[mat_?MatrixQ, rest___] := VickGaussian[{mat, Inverse @ mat}, rest] /; 
  If[MatrixQ[mat, NumericQ], True, Message[VickGaussian::num, mat]; False]


VickGaussian[{mat_/;MatrixQ[mat, NumericQ], inv_/;MatrixQ[inv, NumericQ]}, ___][
  ws:VickState[{_?NumericQ, n_Integer}] (* vacuum state *)   
] = ws

VickGaussian[{mat_/;MatrixQ[mat, NumericQ], inv_/;MatrixQ[inv, NumericQ]}, ___?OptionQ][
  VickState[{flag_?VectorQ, trs_?MatrixQ}]
] := 
  Module[
    { kk = PositionIndex[flag],
      mm = trs},
    If[Not[MissingQ @ kk @ 0], mm[[kk @ 0]] = mm[[kk @ 0]] . inv];
    If[Not[MissingQ @ kk @ 1], mm[[kk @ 1]] = mm[[kk @ 1]] . Transpose[mat]];
    VickState[{flag, mm}]
  ]


VickGaussian /:
MatrixForm[op : VickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___]] :=
  MatrixForm /@ {mat, inv}

VickGaussian /:
ArrayShort[op : VickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___]] :=
  ArrayShort /@ {mat, inv}

VickGaussian /: 
NonCommutativeQ[_VickGaussian] = True

VickGaussian /:
MultiplyKind[_VickGaussian] = Fermion

VickGaussian /:
Multiply[pre___, op_VickGaussian, ws_VickState] := Multiply[pre, op @ ws]

VickGaussian /:
Multiply[pre___, op_VickGaussian, fs_Ket] := Multiply[pre, op @ VickState @ fs]

(* 
VickGaussian /:
Matrix[op:VickGaussian[{_?MatrixQ, _?MatrixQ}, cc:{__?FermionQ}, ___]] := Matrix[op, cc]
 *)
VickGaussian /:
Matrix[VickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___?OptionQ], ss:{__?SpeciesQ}] := Module[
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

VickGaussian /: (* fallback *)
Matrix[wu_VickGaussian, rest___] := wu * Matrix[1, rest]

(**** </VickGaussian> ****)


RandomVickGaussian::usage = "RandomVickGaussian[n] ..."

RandomVickGaussian[n_Integer, opts___?OptionQ] := With[
  { mat = RandomMatrix[n] },
  VickGaussian[{MatrixExp[+mat], MatrixExp[-mat]}, opts]
]


(**** <VickUnitary> ****)

VickUnitary::usage = "VickUnitary[u] represents the Gaussian-type unitary operator that transforms n fermion modes according to n\[Times]n unitary matrix u.\nVickUnitary[1, n] is equivalent to VickUnitary[I], where I is the n\[Times]n identity matrix."

SetAttributes[VickUnitary, NHoldRest]

VickUnitary /:
MakeBoxes[op:VickUnitary[trs_?MatrixQ, rest___], fmt_] := Module[
    { kk = {rest} },
  kk = Which[ 
    Length[kk] == 0, All,
    MatchQ[First @ kk, {__Integer}], First[kk],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    VickUnitary, op, None,
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
VickUnitary[{0, n_Integer}, rest___] :=
  VickUnitary[Zero[n*{1, 1}], rest]

(* identity operator *)
VickUnitary[{1, n_Integer}, rest___] :=
  VickUnitary[One[n], rest]


VickUnitary /:
Times[z_?CommutativeQ, VickUnitary[uu_, rest___]] := VickUnitary[z * uu, rest]

VickUnitary /:
Plus[VickUnitary[a_, kk_, opts___?OptionQ], VickUnitary[b_, kk_, more___?OptionQ]] :=
  VickUnitary[a + b, kk, Sequence @@ Flatten @ {opts, more}]

VickUnitary /:
Plus[VickUnitary[a_, opts___?OptionQ], VickUnitary[b_, more___?OptionQ]] :=
  VickUnitary[a + b, Sequence @@ Flatten @ {opts, more}]


VickUnitary /:
Dot[VickUnitary[a_, kk_, opts___?OptionQ], VickUnitary[b_, kk_, more___?OptionQ]] :=
  VickUnitary[Dot[a, b], kk, Sequence @@ Flatten @ {opts, more}]

VickUnitary /:
Dot[VickUnitary[a_, opts___?OptionQ], VickUnitary[b_, more___?OptionQ]] :=
  VickUnitary[Dot[a, b], Sequence @@ Flatten @ {opts, more}]

VickUnitary /:
Dagger[VickUnitary[mat_?MatrixQ, rest___]] := VickUnitary[Topple @ mat, rest]


VickUnitary /:
ExpressionFor[wu:VickUnitary[_?MatrixQ, ___], cc:{__?FermionQ}] :=
  ExpressionFor[Matrix @ wu, cc]

VickUnitary /: (* fallback *)
ExpressionFor[wu_VickUnitary, ___] = wu


VickUnitary /:
Matrix[VickUnitary[trs_?MatrixQ, ___?OptionQ], cc:{__?FermionQ}] := 
  Matrix[VickGaussian @ {trs, Topple @ trs}, cc]

VickUnitary /: (* fallback *)
Matrix[wu_VickUnitary, rest___] := wu * Matrix[1, rest]


VickUnitary /:
MatrixForm[VickUnitary[trs_?MatrixQ, ___], rest___] := MatrixForm[trs, rest]

VickUnitary /:
ArrayShort[VickUnitary[trs_?MatrixQ, ___], rest___] := ArrayShort[trs, rest]


VickUnitary /: 
NonCommutativeQ[_VickUnitary] = True

VickUnitary /:
MultiplyKind[_VickUnitary] = Fermion

VickUnitary /:
Multiply[pre___, wu_VickUnitary, ws_VickState] := Multiply[pre, wu @ ws]

VickUnitary /:
Multiply[pre___, wu_VickUnitary, fs_Ket] := Multiply[pre, wu @ VickState @ fs]


VickUnitary[{}, ___][any_] = any

VickUnitary[mat_/;MatrixQ[mat, NumericQ], ___][
  ws:VickState[_?NumericQ, n_Integer] (* vacuum state *)   
] = ws

VickUnitary[mat_/;MatrixQ[mat, NumericQ], ___][
  VickState[{flag_?VectorQ, trs_?MatrixQ}]
] := Module[
  { kk = PositionIndex[flag],
    mm = trs },
  If[Not[MissingQ @ kk @ 0], mm[[kk @ 0]] = mm[[kk @ 0]] . Topple[mat]];
  If[Not[MissingQ @ kk @ 1], mm[[kk @ 1]] = mm[[kk @ 1]] . Transpose[mat]];
  VickState[{flag, mm}]
]

VickUnitary[spec__][fs_Ket] := VickUnitary[spec][VickState @ fs]

(**** </VickUnitary> ****)


RandomVickUnitary::usage = "RandomVickUnitary[n] is a shortcut to VickUnitary[RandomMatrix[n]]."

RandomVickUnitary[n_Integer, opts___?OptionQ] :=
  VickUnitary[RandomMatrix @ n, opts]


(**** <VickConjugateReverse> ****)

VickConjugateReverse::usage = "VickConjugateReverse[mat] reverses the order of the rows and takes the complex conjugate of the elements of matrix mat.\nVickConjugateReverse[flags] interchanges each flag (0 <-> 1) and reverses the order of the entries of list flags.\nVickConjugateReverse[{flags, mat}] returns the pair {newFlags, newMat}."

VickConjugateReverse[trs_?MatrixQ] :=
  Reverse @ Conjugate @ trs

VickConjugateReverse[tag_?VectorQ] :=
  Reverse @ Mod[1 + tag, 2]

VickConjugateReverse[{tag_?VectorQ, trs_?MatrixQ}] := {
  VickConjugateReverse[tag],
  VickConjugateReverse[trs]
}

(**** </VickConjugateReverse> ****)


(**** <VickElements> ****)

VickElements::usage = "VickElements[spec, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion operators corresponding to specification spec."

VickElements::incmp = "Transformation matrix `` is intended for `` fermion modes while `` includes `` fermion modes."


VickElements[{flag_?VectorQ, trs_?MatrixQ}, cc:{__?FermionQ}] := Module[
  { kk = PositionIndex[flag],
    new = trs },
  If[Not[MissingQ @ kk @ 0], new[[kk @ 0]] = Dot[trs[[kk @ 0]], cc]];
  If[Not[MissingQ @ kk @ 1], new[[kk @ 1]] = Dot[trs[[kk @ 1]], Dagger @ cc]];
  new
] /; If[ Last[Dimensions @ trs] === Length[cc], True,
    Message[VickElements::incmp, trs, Last[Dimensions @ trs], cc, Length @ cc]; False
  ]

VickElements[VickState[{flag_?VectorQ, trs_?MatrixQ}], cc:{__?FermionQ}] :=
  VickElements[{flag, trs}, cc]

VickElements[VickState[{_?NumericQ, _Integer}], ___] = {}

VickElements[VickOperator[ops:{_?VectorQ, _?MatrixQ}, ___?OptionQ], cc:{__?FermionQ}] :=
  VickElements[ops, cc]

(**** </VickElements> ****)


(**** <VickOperator> ****)

VickOperator::usage = "VickOperator[{{flag1, flag2, \[Ellipsis]}, {cff1, cff2, \[Ellipsis]}}] represents a product of linear combinations of fermion annihilation (Subscript[flag, i]=0) or creation (Subscript[flag, i]=1) operators with coefficients Subscript[cff, i]={Subscript[z, i1],Subscript[z, i2],\[Ellipsis]}.\nVickOperator[{flag, cff}] is a shortcut for a single linear combination, and is automatically converted into the canonical form VickOperator[{{flag}, {cff}}].\nVickOperator[{{k1, f1}, {k2, f2}, \[Ellipsis]}, n] returns a VickOperator object representing a product of simple creation (Subscript[f, i]=1) or annihilation (Subscript[f, i]=0) operators of the Subscript[k, i]th fermion mode among overall n fermion modes."

VickOperator::flag = "`` is not a proper list of binary-coded flags."

SetAttributes[VickOperator, NHoldAll]

VickOperator /:
MakeBoxes[op:VickOperator[{flag_?VectorQ, trs_?MatrixQ}, rest___], fmt_] := Module[
  { kk = {rest} },
  kk = Which[ 
    Length[kk] == 0, All,
    MatchQ[First @ kk, {__Integer}], First[kk],
    True, All
  ];
  BoxForm`ArrangeSummaryBox[
    VickOperator, op, None,
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
VickOperator[{flag:(0|1), cff_?VectorQ}, rest___] :=
  VickOperator[{{flag}, {cff}}]

(* shortcut *)
VickOperator[spec:{{_Integer, _Integer}..}, n_Integer, opts___?OptionQ] := Module[
  {kk, flag},
  {kk, flag} = Transpose[spec];
  VickOperator[{flag, One[n][[kk]]}, opts] /;
  If[ VectorQ[flag, BinaryQ], True,
    Message[VickOperator::flag, flag]; False 
  ]
]

(* shortcut *)
VickOperator[spec:{_Integer, 0|1}, n_Integer, opts___?OptionQ] :=
  VickOperator[{spec}, n]


VickOperator[{}][any_] = any

VickOperator[jmp:{_?VectorQ, _?MatrixQ}, ___][VickState[trs:{_?VectorQ, _?MatrixQ}]] :=
  VickState @ VickJoin[jmp, trs]

VickOperator[jmp:{_?VectorQ, _?MatrixQ}, ___][VickState[{z_?NumericQ, n_Integer}]] :=
  z * VickState[jmp] /; Last[Dimensions @ Last @ jmp] == n


VickOperator /:
Dagger @ VickOperator[ops:{_?VectorQ, _?MatrixQ}, rest___] :=
  VickOperator[VickConjugateReverse @ ops, rest]


VickOperator /: 
NonCommutativeQ[_VickOperator] = True

VickOperator /:
MultiplyKind[_VickOperator] = Fermion

VickOperator /:
Multiply[pre___, aa_VickOperator, bb__VickOperator, post___] :=
  Multiply[pre, VickOperator[Join @@ Transpose[First /@ {aa, bb}]], post]

VickOperator /:
Multiply[pre___, op_VickOperator, ws_VickState] := Multiply[pre, op[ws]]

VickOperator /:
Multiply[pre___, op_VickOperator, fs_Ket] := Multiply[pre, op[VickState @ fs]]


VickOperator /:
Matrix[VickOperator[{flag_?VectorQ, trs_?MatrixQ}, ___], ss:{__?SpeciesQ}] := With[
  { cc = Select[ss, FermionQ] },
  Dot @@ Matrix[VickElements[{flag, trs}, cc], ss]
]

VickOperator /:
Matrix[op:VickOperator[{flag_?VectorQ, trs_?MatrixQ}, ___]] := Module[
  { n = Last[Dimensions @ trs],
    c },
  Let[Fermion, c];
  Matrix[op, c @ Range @ n]
]

VickOperator /: (* fallback *)
Matrix[op_VickOperator, rest___] := op * Matrix[1, rest]

VickOperator /:
ExpressionFor[VickOperator[trs:{_?VectorQ, _?MatrixQ}, ___], cc:{__?FermionQ}] :=
  Apply[Multiply, VickElements[trs, cc]]

VickOperator /: (* fallback *)
ExpressionFor[op_VickOperator, __] = op 


VickOperator /:
VacuumExpectation[VickOperator[jmp:{_?VectorQ, _?MatrixQ}, ___]] :=
  Pfaffian @ VickMatrix[jmp]

(**** </VickOperator> ****)


RandomVickOperator::usage = "RandomVickOperator[k, n] randomly generates a depth k Vick operator for n fermion modes.\nRandomVickOperator[n] selects k randomly from {2, 4, \[Ellipsis], n}."

(* backward compatibility *)
RandomVickOperator[cc:{__?FermionQ}] :=
  RandomVickOperator[Length @ cc]

RandomVickOperator[n_Integer] :=
  RandomVickOperator[RandomChoice @ Range[2, n, 2], n]

RandomVickOperator[k_Integer?Positive, n_Integer] := Module[
  { ff, mm },
  ff = RandomChoice[{{0, 1}, {1, 0}}];
  ff = RandomSample @ PadRight[ff, k, ff];
  mm = RandomMatrix[{k, n}];
  VickOperator[{ff, mm}]
]


(**** <VickOperatorFrom> ****)

(* NOTE: In principle, VickOperatorFrom may be integrated into VickOperator, but separating this feature keeps better the performance of VickOperator. *)

VickOperatorFrom::usage = "VickOperatorFrom[expr_, {c1, c2, \[Ellipsis]}] constructs a VickOperator object from linear combination (or a list of linear combinations) expr of fermion operators of fermion modes {c1, c2, \[Ellipsis]}."

VickOperatorFrom::mixed = "Mixed linear combination `` of creation and annihilation operators."

VickOperatorFrom::nlin = "`` is not a linear combination of the creation and annihilation operators of fermion modes ``."

VickOperatorFrom[cc:{__?FermionQ}][spec_] :=
  VickOperatorFrom[spec, cc]

VickOperatorFrom[expr_, cc:{__?FermionQ}] :=
  VickOperator[theVickOperator[expr, cc]] /;
  If[ theVickLinearQ[expr, cc], True,
    Message[VickOperatorFrom::nlin, expr, cc];
    False
  ]


theVickOperator::usage = "theVickOperator[expr, {c1, c2, \[Ellipsis]}] returns the coefficient list of expr in either creation or annihilation operators of fermion modes {c1, c2, \[Ellipsis]}. theVickOperator[expr, {c1, c2, \[Ellipsis], Dagger[c1], Dagger[c2], \[Ellipsis]}] returns the coefficients list of expr in {c1, c2, \[Ellipsis], Dagger[c1], Dagger[c2], \[Ellipsis]}."

theVickOperator[cc:{__?FermionQ}][any_] := theVickOperator[any, cc]

theVickOperator[expr_List, cc:{__?FermionQ}] :=
  VickJoin @@ Map[theVickOperator[cc], expr]

theVickOperator[expr_, cc:{__?FermionQ}] := Module[
  { aa = Coefficient[expr, cc],
    bb = Coefficient[expr, Dagger @ cc]},
  Which[
    ZeroQ @ Norm[aa, Infinity],
    {{1}, {bb}},
    ZeroQ @ Norm[bb, Infinity],
    {{0}, {aa}},
    True, Message[VickOperator::mixed, expr]; {{0}, {aa}}
  ]
]


theVickLinearQ::usage = "theVickLinearQ[expr, {c1, c2, \[Ellipsis]}] returns True if expr is a linear combination of the creation and annihilation operators of fermion modes {c1, c2, \[Ellipsis]}, and False otherwise."

theVickLinearQ[expr_List, cc : {__?FermionQ}] :=
  AllTrue[expr, theVickLinearQ[#, cc]&]

theVickLinearQ[expr_, cc : {__?FermionQ}] := TrueQ @ And[
   ZeroQ[ expr /. Thread[cc -> 0] ],
   FreeQ[ expr,
    HoldPattern[Multiply][___, Alternatives @@ Join[cc, Dagger @ cc], ___]
  ]
]

(**** </VickOperatorFrom> ****)


(**** <FermiMeasurement> ****)

FermiMeasurement::usage = "FermiMeasurement[k] represents a measurement of the occupation number on fermion mode k.\nFermiMeasurement[{k1, k2, \[Ellipsis]}] represents a sequence of measurements on fermion modes {k1, k2, \[Ellipsis]}.\nFermiMeasurement[spec][ws] simulates the measurement on Vick state ws, and returns the post-measurement state."

SetAttributes[FermiMeasurement, NHoldAll]

FermiMeasurement[k_Integer][ws:VickState[{_?NumericQ, n_Integer}]] := (
  $MeasurementOut[k] = 0;
  VickState[{1, n}]
)

FermiMeasurement[k_Integer][ws:VickState[trs:{_?VectorQ, _?MatrixQ}]] := Module[
  { n = FermionCount[ws],
    nrm = NormSquare[ws],
    msr, dgr, mat, prb },
  msr = First @ VickOperator[{{k, 0}, {k, 1}}, n]; (* c ** Dagger[c] *)
  dgr = VickConjugateReverse[trs];
  mat = VickMatrix @ VickJoin[dgr, msr, trs];
  prb = Quiet[Re @ Sqrt @ Det @ mat, Det::luc];
  (* NOTE: Here, the Pfaffian is supposed to be positive. *)
  (* 2024-08-11: Det[...] is enclosed in Quiet[..., Det::luc]. The warning message does not seem to be serious in most cases, but goes off too often. *)
  prb /= nrm;
  
  (* Simulate the measurement process. *)
  If[ RandomReal[] < prb,
    $MeasurementOut[k] = 0;
    VickOperator[{{k, 0}, {k, 1}}, n][ws] / Sqrt[prb*nrm],
    $MeasurementOut[k] = 1;
    VickOperator[{{k, 1}, {k, 0}}, n][ws] / Sqrt[(1-prb)*nrm]
  ]
]

FermiMeasurement[kk:{___Integer}][ws:(_VickState|_NamvoState)] :=
  Fold[FermiMeasurement[#2][#1]&, ws, kk]


FermiMeasurement /:
Multiply[pre___, msr_FermiMeasurement, ws_VickState] := 
  Multiply[pre, msr @ ws]

FermiMeasurement /:
Readout[FermiMeasurement[k_]] := Readout[k]

(**** </FermiMeasurement> ****)


(**** <VickExpectation> ****)

VickExpectation::usage = "VickExpectation[ws] represents an expectation value with respect to the Vick or Namvo state ws.\nVickState[ws][expr] returns the expectation value of expr, where expr may be either VickOperator or NamvoOperator consistent with ws."

VickExpectation[VickState[bb:{_?VectorQ, _?MatrixQ}]] @
  VickOperator[ops:{_?VectorQ, _?MatrixQ}, ___] := Module[
    { aa = VickConjugateReverse[bb],
      mat },
    mat = VickMatrix @ VickJoin[aa, ops, bb];
    Pfaffian[mat] (* NOTE: The Vick state is assumed to be normalized. *)
  ]

VickExpectation[VickState[{z_?NumericQ, n_Integer}]][op_VickOperator] :=
  AbsSquare[z] * VacuumExpectation[op]

(**** </VickExpectation> ****)


(**** <VickOccupation> ****)

VickOccupation::usage = "VickOccupation[in, {k1, k2, \[Ellipsis]}] returns a list of the expectation values of occupation on fermion modes in {k1, k2, \[Ellipsis]} with respect to VickState or NamvoState in.\nVickOccupation[in] is equivalent to VickOccupation[in, Range[n]], where n is the number of fermion modes for which input Vick or Namvo state in is defined for.\nVickOccupation[data] or VickOccupation[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating the occupation for an (typically large) array data of Vick or BdG states.\nVickOccupation[{k1, k2, \[Ellipsis]}] represents an operator form of VickOccupation to be applied to Vick or BdG state."

(* operator form *)
VickOccupation[kk:{___Integer}][in:(_VickState|_NamvoState)] :=
  VickOccupation[in, kk]

(* shortcut *)
VickOccupation[ws_VickState] :=
  VickOccupation[ws, Range @ FermionCount @ ws]

(* canonical form for normal models *)
VickOccupation[ws:VickState[qq:{_?VectorQ, _?MatrixQ}], kk:{___Integer}] := Module[
  { nc = FermionCount[ws],
    pp = VickConjugateReverse[qq],
    aa, bb, ab, gg, wm },
  bb = One[nc][[kk]];
  aa = VickSplit @ {ConstantArray[1, Length @ kk], bb};
  bb = VickSplit @ {ConstantArray[0, Length @ kk], bb};

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = VickMatrix[pp];
  wm[[1, 3]] = VickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = VickMatrix[qq];

  nc = Length[kk];
  gg = Normal @ Zero[nc];
  Table[
    ab = VickJoin[aa[[i]], bb[[i]]];
    wm[[1, 2]] = VickMatrix[pp, ab];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = VickMatrix[ab];
    wm[[2, 3]] = VickMatrix[ab, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    gg[[i]] = Sqrt @ Re @ Quiet[Det @ ArrayFlatten @ N @ wm, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, nc}
  ];
  Return[gg] (* NOTE: The Vick state is assumed to be normalized. *)
]

(* vacuum state *)
VickOccupation[VickState[{z_?NumericQ, n_Integer}], kk:{___Integer}] :=
  Zero[Length @ kk]


(* for large data *)
VickOccupation[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = N @ Aggregate @ Dimensions[data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickOccupation[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState | _NamvoState]&]

(**** </VickOccupation> ****)


(**** <VickGreenFunction> ****)

VickGreenFunction::usage = "VickGreenFunction[ws, {k1, k2, \[Ellipsis]}] returns m\[Times]m matrix of single-particle Green's functions among fermion modes in {k1, k2, \[Ellipsis]} with respect to VickState ws.\nVickGreenFunction[ns, {k1, k2, \[Ellipsis]}] returns NamvoGreen[{grn, anm}], where grn and anm are m\[Times]m matrix of single-particle normal and anomalous Green's functions, respectively, among fermion modes in {k1, k2, \[Ellipsis]} with respect to NamvoState ns.\nVickGreenFunction[in] is equivalent to VickGreenFunction[in, Range[n]], where n is the number of fermion modes for which input Vick or Namvo state in is defined for.\nVickGreenFunction[data] or VickGreenFunction[data, {k1, k2, \[Ellipsis]}] shows a dynamic progress indicator while calculating Green's functions for an (typically large) array data of Vick or BdG states.\nVickGreenFunction[{k1, k2, \[Ellipsis]}] represents an operator form of VickGreenFunction to be applied to Vick or Namvo state."

(* operator form *)
VickGreenFunction[kk:{___Integer}][in:(_VickState|_NamvoState)] :=
  VickGreenFunction[in, kk]

(* shortcut *)
VickGreenFunction[ws_VickState] :=
  VickGreenFunction[ws, Range @ FermionCount @ ws]

(* canonical form for normal models *)
VickGreenFunction[ws:VickState[qq:{_?VectorQ, _?MatrixQ}], kk:{___Integer}] := Module[
  { nn = FermionCount[ws],
    pp = VickConjugateReverse[qq],
    aa, bb, ab, gg, wm },
  bb = One[nn][[kk]];
  aa = VickSplit @ {ConstantArray[0, Length @ kk], bb};
  bb = VickSplit @ {ConstantArray[1, Length @ kk], bb};

  wm = Normal @ Zero[{3, 3}];
  wm[[1, 1]] = VickMatrix[pp];
  wm[[1, 3]] = VickMatrix[pp, qq];
  wm[[3, 1]] = -Transpose[ wm[[1, 3]] ];
  wm[[3, 3]] = VickMatrix[qq];

  nn = Length[kk];
  gg = Normal @ Zero[{nn, nn}];
  Table[
    ab = VickJoin[aa[[i]], bb[[i]]];
    wm[[1, 2]] = VickMatrix[pp, ab];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = VickMatrix[ab];
    wm[[2, 3]] = VickMatrix[ab, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    ab = ArrayFlatten[N @ wm];
    gg[[i, i]] = Re @ Sqrt @ Quiet[Det @ ab, Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, nn}
  ];
  Table[
    ab = VickJoin[aa[[i]], bb[[j]]];
    wm[[1, 2]] = VickMatrix[pp, ab];
    wm[[2, 1]] = -Transpose[ wm[[1, 2]] ];
    wm[[2, 2]] = VickMatrix[ab];
    wm[[2, 3]] = VickMatrix[ab, qq];
    wm[[3, 2]] = -Transpose[ wm[[2, 3]] ];
    ab = ArrayFlatten[N @ wm];
    gg[[i, j]] = Pfaffian[ab];
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, nn-1},
    {j, i+1, nn}
  ];
  Return[gg] (* NOTE: The Vick state is assumed to be normalized. *)
]

(* vacuum state *)
VickGreenFunction[VickState[{z_?NumericQ, n_Integer}], kk:{___Integer}] :=
  One[Length @ kk]


(* for large data *)
VickGreenFunction[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = Aggregate[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickGreenFunction[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState | _NamvoState]&]

(**** </VickGreenFunction> ****)


(**** <VickGreenFunctionQR> ****)

VickGreenFunctionQR::usage = "VickGreenFunctionQR[ws, {k1, k2, \[Ellipsis]}] returns ..."

VickGreenFunctionQR::dag = "Only 1 (corresponding to a creator) is allowed in a list of binary-coded flags."
(* NOTE: Just for tests. Equivalent to the above. *)

VickGreenFunctionQR[ws_VickState] :=
  VickGreenFunctionQR[ws, Range @ FermionCount @ ws]

VickGreenFunctionQR[VickState[{flag_?VectorQ, trs_?MatrixQ}], kk:{___Integer}] := Module[
  { cor = Transpose[trs],
    grn },
  grn = cor . Topple[cor];
  grn = One[Dimensions @ grn] - grn;
  grn[[kk, kk]]
] /; If[ ContainsOnly[flag, {1}], True,
    Message[VickGreenFunction::qr]; False
  ]

(* for large data *)
VickGreenFunctionQR[data_?ArrayQ, kk:Repeated[{___Integer}, {0, 1}]] := Module[
  { progress = i = 0,
    dim = Aggregate[N @ Dimensions @ data],
    dep = ArrayDepth[data]
  },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];
  Map[(progress = i++/dim; VickGreenFunctionQR[#, kk])&, data, {dep}]
] /; ArrayQ[data, _, MatchQ[#, _VickState | _NamvoState]&]

(**** </VickGreenFunctionQR> ****)


(**** <VickDensityMatrix> ****)

VickDensityMatrix::usage = "VickDensityMatrix[grn] returns the density matrix corresponding to the single-particle Green's function grn associated with a fermionic Gaussian state.\nVickDensityMatrix[ws] returns the density matrix corresponding to Vick state ws."

VickDensityMatrix::num = "Only numerical matrices are allowed."

VickDensityMatrix[grn_?MatrixQ] := Module[
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
  Message[VickDensityMatrix::num];
  False
]

(* shortcut *)
VickDensityMatrix[ws_VickState] := With[
  { v = Matrix[ws] },
  Dyad[v, v]
]

(**** </VickDensityMatrix> ****)


(**** <VickEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
VickEntropy::usage = "VickEntropy[grn] returns the von Neumann entropy of a fermionic Gaussian state characterized by the matrix grn of single-particle Green's functions. VickEntropy[NamvoGreen[{grn, anm}]] or VickEntropy[{grn, anm}] considers a fermionic Gaussian state characterized by matrices grn and anm of normal and anomalous Green's functions."

(* canonical form for normal models *)
VickEntropy[grn_?MatrixQ] :=
  QuantumLog[2, grn] + QuantumLog[2, One[Dimensions @ grn] - grn]

(* canonicalization for BdG models *)
VickEntropy[grn:NamvoGreen[{_?MatrixQ, _?MatrixQ}, ___]] :=
  theVickEntropy[Normal @ grn] / 2

(* canonicalization for BdG models *)
VickEntropy[grn:{_?MatrixQ, _?MatrixQ}] :=
  VickEntropy[NamvoGreen @ grn]


(* shortcut *)
VickEntropy[in:(_VickState|_NamvoState)] = 0

(**** </VickEntropy> ****)


(**** <VickEntanglementEntropy> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
VickEntanglementEntropy::usage = "VickEntanglementEntropy[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Vick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nVickEntanglementEntropy[NamvoGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or VickEntanglementEntropy[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nVickEntanglementEntropy[state, {k1, k2, \[Ellipsis]}] is equivalent to VickEntanglementEntropy[VickGreenFunction[state, {k1, k2, \[Ellipsis]}], {k1, k2, \[Ellipsis]}] for Vick or BdG state.\nVickEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of VickEntanglementEtropy to be applied to Green's functions, Vick or Namvo state."

(* special case for normal models *)
VickEntanglementEntropy[grn_?MatrixQ, {}] = 0

(* canonical form for normal models *)
VickEntanglementEntropy[grn_?MatrixQ, kk:{__Integer}] :=
  VickEntropy @ grn[[kk, kk]]

(* special case for normal models *)
VickEntanglementEntropy[_?NamvoMatrixQ, {}] = 0

(* canonical form for BdG models *)
VickEntanglementEntropy[{grn_?MatrixQ, anm_?MatrixQ}, kk:{__Integer}] := Module[
  { gg = Normal[grn][[kk, kk]],
    ff = Normal[anm][[kk, kk]] },
  (* NOTE: It seems that Part does not support properly SymmetrizedArray; hence, Normal in the above. *)
  VickEntropy @ Normal @ NamvoGreen[{gg, ff}] / 2
]

(* canonicalization for BdG models *)
VickEntanglementEntropy[grn:NamvoGreen[{_?MatrixQ, _?MatrixQ}, ___], kk:{__Integer}] :=
  VickEntanglementEntropy[First @ grn, kk]


(* operator form *)
VickEntanglementEntropy[kk:{___Integer}][any_] :=
  VickEntanglementEntropy[any, kk]

(* shortcut *)
VickEntanglementEntropy[in:(_VickState|_NamvoState), kk:{___Integer}] :=
  VickEntanglementEntropy[VickGreenFunction[in, kk], kk]

(**** </VickEntanglementEntropy> ****)


(**** <VickMutualInformation> ****)

(* See, e.g., Calabrese and Carday (2004) and Peschel (2003). *)
VickMutualInformation::usage = "VickMutualInformation[grn, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between the subsystem consisting of fermion modes {k1, k2, \[Ellipsis]}\[Subset]{1, 2, \[Ellipsis], n} in the Vick state characterized by n\[Times]n matrix grn of single-particle Green's functions.\nVickMutualInformation[NamvoGreen[{grn, anm}], {k1, k2, \[Ellipsis]}] or VickMutualInformation[{grn, anm}, {k1, k2, \[Ellipsis]}] returns the entanglement entropy in the BdG state characterized by n\[Times]n matrices grn and anm of normal and anomalous Green's functions, respectively.\nVickMutualInformation[state, {k1, k2, \[Ellipsis]}] is equivalent to VickMutualInformation[VickGreenFunction[state], {k1, k2, \[Ellipsis]}] for Vick or BdG state.\nVickMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of VickEntanglementEtropy to be applied to Green's functions, Vick or Namvo state."

(* canonical form for normal models *)
VickMutualInformation[gg_?MatrixQ, kk:{__Integer}] :=With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  VickEntropy[ gg[[kk, kk]] ] + VickEntropy[ gg[[ll, ll]] ] - VickEntropy[ gg ]
]

(* canonical form for BdG models *)
VickMutualInformation[{gg_?MatrixQ, ff_?MatrixQ}, kk:{__Integer}] := With[
  { ll = Supplement[Range @ Length @ gg, kk] },
  ( VickEntropy[Normal @ NamvoGreen @ {gg[[kk, kk]], ff[[kk, kk]]}] +
    VickEntropy[Normal @ NamvoGreen @ {gg[[ll, ll]], ff[[ll, ll]]}] -
    VickEntropy[Normal @ NamvoGreen @ {gg, ff}]
  ) / 2
]

(* canonicalization for BdG models *)
VickMutualInformation[NamvoGreen[{gg_?MatrixQ, ff_?MatrixQ}, ___], kk:{__Integer}] :=
  VickMutualInformation[{gg, ff}, kk]

(* operator form *)
VickMutualInformation[kk:{__Integer}][any_] :=
  VickMutualInformation[any, kk]

(* shortcut for normal models *)
VickMutualInformation[in:(_VickState|_NamvoState), kk:{__Integer}] := 
  VickMutualInformation[VickGreenFunction @ in, kk]

(**** </VickMutualInformation> ****)


(**** <VickMatrix> ****)

VickMatrix::usage= "VickMatrix[spec] constructs the so-called Vick matrix, an anti-symmetric matrix with elements of Vick contractions between two fermion operators."

(* for normal models *)
VickMatrix[{tag_?VectorQ, trs_?MatrixQ}] := Module[
  { kk, aa, bb, ij, rr },
  kk = PositionIndex[tag];
  If[ MissingQ[kk @ 0] || MissingQ[kk @ 1],
    Return @ Zero @ {Length @ tag, Length @ tag}
  ];
  aa = trs[[kk @ 0]];
  bb = trs[[kk @ 1]];
  rr = Dot[aa, Transpose @ bb];
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

(* for normal models *)
VickMatrix[{atag_?VectorQ, atrs_?MatrixQ}, {btag_?VectorQ, btrs_?MatrixQ}] :=
Module[
  { ii, jj, aa, bb, rr },
  ii = Lookup[PositionIndex @ atag, 0];
  jj = Lookup[PositionIndex @ btag, 1];
  If[ MissigQ[ii] || MissingQ[jj], 
    Return @ Zero @ {Length @ atag, Length @ btag}
  ];
  aa = atrs[[ii]];
  bb = btrs[[jj]];
  rr = Dot[aa, Transpose @  bb];
  (* NOTe: Mathematica 14.1 bug? This part causes a random crash of WolframKernel. *)
  rr = Thread[ Tuples[{ii, jj}] -> Flatten[rr] ];
  SparseArray[rr, {Length @ atag, Length @ btag}]
]


(* for BdG models *)
VickMatrix[jmp_?MatrixQ] := Module[
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

(* for BdG models *)
VickMatrix[ma_?MatrixQ, mb_?MatrixQ] := Module[
  { aa, bb },
  aa = First @ First @ PartitionInto[ma, {1, 2}];
  bb = Last  @ First @ PartitionInto[mb, {1, 2}];
  aa . Transpose[bb]
]

(**** </VickMatrix> ****)


(**** <VickCircuit> ****)

VickCircuit::usage = "VickCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit consisting of Vick gates (i.e., non-interacting fermionic gates) g1, g2, \[Ellipsis] on fermion modes."

VickCircuit /:
MakeBoxes[wc:VickCircuit[gg_List, ___], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    VickCircuit, wc, None,
    { BoxForm`SummaryItem @ { "Fermion modes: ", FermionCount @ wc },
      BoxForm`SummaryItem @ { "Circuit depth: ", Length @ gg }
    },
    { BoxForm`SummaryItem @ { "Some elements: ", Short @ gg }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

VickCircuit /: 
NonCommutativeQ[_VickCircuit] = True

VickCircuit /:
MultiplyKind[_VickCircuit] = Fermion

VickCircuit /:
Multiply[pre___, wc_VickCircuit, in:(_VickState|_NamvoState)] :=
  Multiply[pre, wc @ in]

VickCircuit[gg_List, ___][in:(_VickState|_NamvoState)] :=
  Fold[#2[#1]&, in, gg]


VickCircuit /:
Show[wc_VickCircuit, rest___] := Graphics[wc, rest]

VickCircuit /:
Graphics[wc:VickCircuit[gg_List], more___?OptionQ] := Module[
  { c },
  Let[Fermion, c];
  Graphics[wc, c, more]
]

VickCircuit /:
Graphics[wc:VickCircuit[gg_List, opts___?OptionQ], c_Symbol?FermionQ, more___?OptionQ] := Module[
  { n = FermionCount[wc],
    cc, qc },
  cc = c[Range @ n];
  qc = gg /. {
    VickCircuit[{}] -> "Spacer",
    ws_VickCircuit :> Graphics[ws],
    ws_VickState :> ExpressionFor[ws, cc],
    VickUnitary[_?MatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    VickUnitary[_?MatrixQ, any___?OptionQ] :> Gate[cc, any],
    VickUnitary[_?MatrixQ, _, any___?OptionQ] :> Gate[cc, any],
    NamvoUnitary[_?NamvoMatrixQ, kk:{__Integer}, any___?OptionQ] :> Gate[c[kk], any],
    NamvoUnitary[_?NamvoMatrixQ, any___?OptionQ] :> Gate[cc, any],
    NamvoUnitary[_?NamvoMatrixQ, _, any___?OptionQ] :> Gate[cc, any],
    FermiMeasurement[{}, ___] -> "Spacer",
    FermiMeasurement[k_Integer, any___?OptionQ] :> Gate[c @ {k}, any, "Shape" -> "Measurement"],
    FermiMeasurement[kk:{_Integer}, any___?OptionQ] :> Gate[c[kk], any, "Shape" -> "Measurement"],
    FermiMeasurement[kk:{_, __Integer}, any___?OptionQ] :> 
      Map[Gate[{c[#]}, any, "Shape" -> "Measurement"]&, kk]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]

(**** </VickCircuit> ****)


(**** <RandomVickCircuit> ****)

RandomVickCircuit::usage = "RandomVickCircuit[{uni, p}, dep] generate a random quantum circuit on non-interacting fermion modes, where layers of unitary gate uni (either VickUnitary[\[Ellipsis]] or NamvoUnitary[\[Ellipsis]]) alternate with layers of measurements (FermiMeasurement[\[Ellipsis]]) on fermion modes selected randomly with probability p to form an overall depth dep.\nRandomVickCircuit[{ham, pdf, p}, k] unitary layers of random unitary gate uni=Exp[-I ham \[Tau]] with single-particle Hamiltonian ham (either n\[Times]n Hermitian matrix or NamvoHermitian[\[Ellipsis]]) and the random evolution time \[Tau] distributed according to the probability distribution function pdf.\nRandomVickCircuit[{ham, p}, dep] assumes that the evolution time is uniformly distributed over the interval [0,2\[Pi] n/max], where max is the maximum of the absolute values of the entries of ham.\nRandomVickCircuit[ham, dep] generates a circuit for n fermion modes where each unitary layer corresponds to time evolution U=exp[-I ham \[Tau]] with the evolution time \[Tau] distributed by P(\[Tau])\[Proportional]exp[-n \[Tau]] and each measurement layer measures a fermion mode with probability p=1/n."

RandomVickCircuit[{uu:(_VickUnitary | _NamvoUnitary), p_?NumericQ}, k_Integer] :=
  Module[
    { mm },
    mm = RandomPick[Range @ FermionCount @ uu, p, k];
    VickCircuit @ Riffle[
      ConstantArray[uu, k],
      Map[FermiMeasurement, mm]
    ]
  ]

(* arbitrary distribution of evolution time *)
RandomVickCircuit[{ham:(_?MatrixQ|_?NamvoMatrixQ|_NamvoHermitian), pdf_, p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      ab, tt, uu, mm },
    tt = RandomVariate[pdf, k];
    uu = randomVickUnitaryLayer[ham, tt];
    mm = RandomPick[Range @ n, p, k];
    mm = Map[FermiMeasurement, mm];
    VickCircuit @ Riffle[uu, mm]
  ]

(* uniform distribution of evolution time *)
RandomVickCircuit[{ham:(_?MatrixQ|_?NamvoMatrixQ|_NamvoHermitian), p_?NumericQ}, k_Integer] :=
  Module[
    { n = FermionCount[ham],
      max, pdf },
    max = Max @ Abs @ If[Head[ham] === NamvoHermitian, First @ ham, ham];
    pdf = UniformDistribution[{0, N[2*Pi*n/max]}];
    RandomVickCircuit[{ham, pdf, p}, k]
  ]

(* exponential distribution of evolution time *)
(* P(\tau) = Exp[-n\gamma\tau]; choose a unit system such that \gamma\tau --> \tau *)
RandomVickCircuit[ham:(_?MatrixQ|_?NamvoMatrixQ|_NamvoHermitian), k_Integer] :=
  Module[
    { n = FermionCount[ham] },
    RandomVickCircuit[{ham, ExponentialDistribution[n], 1./n}, k]
  ]


randomVickUnitaryLayer[ham_?MatrixQ, tt_?VectorQ] :=
  Map[VickUnitary[MatrixExp[-I*ham*#]]&, tt]

randomVickUnitaryLayer[ham_?NamvoMatrixQ, tt_?VectorQ] :=
  randomVickUnitaryLayer[NamvoHermitian @ ham, tt]

randomVickUnitaryLayer[ham_NamvoHermitian, tt_?VectorQ] := With[
  { mat = Normal[ham] },
  Map[NamvoUnitary[MatrixExp[-I*mat*#]]&, tt]
]

(**** </RandomVickCircuit> ****)


(**** <RandomVickCircuitSimulate> ****)

RandomVickCircuitSimulate::usage = "RandomVickCircuitSimulate[in, spec, dep] simulates a random quantum circuit specified by spec (see RandomVickCircuit) on non-interacting fermion modes starting from initial state in, where layers of unitary gates alternate with layers of Fermi measurements to form an overall depth dep."

RandomVickCircuitSimulate::save = "The result could not be saved."

Options[RandomVickCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RWC"
}

$RandomVickCircuitPatterns = Alternatives[
  {_VickUnitary, _?NumericQ}, 
  {_NamvoUnitary, _?NumericQ},
  {_?MatrixQ, _, _?NumericQ},
  {_?MatrixQ, _?NumericQ},
  {_NamvoHermitian, _, _?NumericQ},
  {_NamvoHermitian, _?NumericQ},
  _?MatrixQ,
  _NamvoHermitian
];

RandomVickCircuitSimulate[
  in:(_VickState | _NamvoState),
  spec:$RandomVickCircuitPatterns,
  t_Integer, 
  opts:OptionsPattern[{RandomVickCircuit, RandomVickCircuitSimulate}]
] := 
Module[
  { progress = k = 0,
    data, more, qc, n, m },
  PrintTemporary[ProgressIndicator @ Dynamic @ progress];

  (* simulation *)
  {n, m} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    qc = RandomVickCircuit[spec, t];
    { Table[
        progress = ++k / N[n*m];
        FoldList[Construct[#2, #1]&, in, N @ First @ qc],
        (* NOTE: No explicit normalization here because both the unitary and measurement layers produce NORMALIZED states. *)
        m 
      ],
      qc
    },
    n
  ];

  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ RandomVickCircuitSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
]

(**** </RandomVickCircuitSimulate> ****)


(**** <VickDampingOperator> ****)

VickDampingOperator::usage = "VickDampingOperator[jmp] returns a pair {mat, const} of the quadratic kernel mat and remaining constant term const of the effective damping operator in the normal ordering that corresponds to the list jmp of quantum jump operators."

VickDampingOperator::jmp = "Invalid form of quantum jump operators ``."

VickDampingOperator[jmp_VickOperator] :=
  VickDampingOperator[First @ jmp]

VickDampingOperator[jmp:{__VickOperator}] :=
  VickDampingOperator[VickJoin @@ jmp]

VickDampingOperator[{flag_?VectorQ, trs_?MatrixQ}] := Module[
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

(**** </VickDampingOperator> ****)


(**** <VickSimulate> ****)

VickSimulate::usage = "VickSimulate[ham, jmp, in, {nt, dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian matrix ham and the list jmp of quantum jump operators. The simulation starts from the initial VickState in at time 0 and goes nt time steps by interval dt."

VickSimulate::null = "The null state is encountered."

VickSimulate::save = "The result could not be saved."

VickSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

Options[VickSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NWS"
}

VickSimulate[ ham_, jmp:(_VickOperator|{__VickOperator}),
  in_VickState, {nT_Integer, dt_},
  opts:OptionsPattern[]
] :=
  Module[
    { n = OptionValue["Samples"],
      progress = 0,
      dmp, fac, non, data, more },
    
    {dmp, fac} = VickDampingOperator[jmp];
    fac = Exp[-dt*fac];
    non = ham - I*dmp;
    non = VickGaussian @ {MatrixExp[-I*dt*non], MatrixExp[+I*dt*non]};

    PrintTemporary[ProgressIndicator @ Dynamic @ progress];
    data = Table[
      progress = k / N[n];
      altVickSimulate[N @ {non, fac}, VickSplit @ jmp, in, {nT, dt}],
      {k, n}
    ];

    If[ OptionValue["SaveData"],
      more = Join[{opts}, Options @ VickSimulate];
      SaveData[data, FilterRules[{more}, Options @ SaveData]]
    ];
    Return[data]
  ] /; If[ MatrixQ[ham, NumericQ], True,
    Message[VickSimulate::ham, ham];
    False
  ]

altVickSimulate[{non_VickGaussian, fac_}, jmp:{__VickOperator}, in_VickState, {nT_Integer, dt_}] :=
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
      out = Through[jmp[new]];

      prb = Chop @ Accumulate[NormSquare /@ out];
      Quiet[
        Check[
          prb /= Last[prb],
          (* error *)
          Message[VickSimulate::null];
          new = VickState[{0, n}]; (* null state *)
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

(**** </VickSimulate> ****)


(**** <VickMonitor> ****)

VickMonitor::usage = "VickMonitor[ham, in, {nt, dt}] solves the problem of continuous monitoring of the occupation number of a non-interacting many-fermion system by using the Monte Carlo simulation method. The model is specified by the single-particle Hamiltonian ham (an n\[Times]n Hermitian matrix for models without pairing or a pair {ham, del} of matrices or NamvoHermitian for BdG models). The simulation starts from the initial in (either VickState or NambState) at time 0 and goes nt time steps of size dt."

VickMonitor::save = "The result could not be saved."

VickMonitor::ham = "The Hamiltonian matrix `` needs to be numeric."

Options[VickMonitor] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "WM"
}

VickMonitor[ham_?NamvoMatrixQ, rest___] :=
  VickMonitor[NamvoHermitian @ ham, rest]

VickMonitor[
  ham:(_?MatrixQ|_NamvoHermitian),
  in:(_VickState|_NamvoState),
  {nT_Integer, dt_?NumericQ},
  opts:OptionsPattern[]
] :=
  Module[
    { n = OptionValue["Samples"],
      progress = 0,
      uni, data, more },
    uni = theVickEvolution[ham, dt];
    If[FailureQ[uni], Message[VickMonitor::ham]; Return @ $Failed];

    PrintTemporary[ProgressIndicator @ Dynamic @ progress];
    data = Table[
      progress = k / N[n];
      theVickMonitor[uni, in, {nT, dt}],
      {k, n}
    ];
    
    If[ OptionValue["SaveData"],
      more = Join[{opts}, Options @ VickMonitor];
      SaveData[data, FilterRules[{more}, Options @ SaveData]]
    ];
    Return[data]
  ]


theVickEvolution[ham_?MatrixQ, dt_] :=
  If[ MatrixQ[ham, NumericQ],
    VickUnitary @ MatrixExp[-I*ham*dt],
    $Failed
  ]

theVickEvolution[ham_?NamvoMatrixQ, dt_] :=
  theVickEvolution[NamvoHermitian @ ham, dt]

theVickEvolution[ham_NamvoHermitian, dt_] :=
  If[ ArrayQ[First @ ham, 3, NumericQ],
    NamvoUnitary @ MatrixExp[-I*Normal[ham]*dt],
    $Failed
  ]


theVickMonitor[uni:(_VickUnitary|_NamvoUnitary), in:(_VickState|_NamvoState), {nT_Integer, dt_?NumericQ}] :=
  Module[
    { n = FermionCount[uni],
      t = 1,
      res = {in},
      new = in,
      (* non = 0, *)
      nrm, prb, occ, pos },
    (* squared norm *)
    nrm = Exp[-n*dt];
    While[ t <= nT,      
      (* non-unitary evolution *)
      If[ RandomReal[] < nrm,
        (* non++; *)
        new = uni[new];
        AppendTo[res, new];
        t += 1;
        Continue[]
      ];
      
      (* quantum jumps *)
      occ = VickOccupation[new];
      prb = Riffle[1-occ, occ] / n;
      prb = Chop[Accumulate @ prb];
      prb = prb - RandomReal[];
      pos = First @ FirstPosition[prb, _?NonNegative];
      If[ OddQ[pos],
        pos = (pos + 1)/2;
        new = VickOperator[{{pos, 0}, {pos, 1}}, n][new] / Sqrt[1-occ[[pos]]],
        pos = pos/2;
        new = VickOperator[{{pos, 1}, {pos, 0}}, n][new] / Sqrt[occ[[pos]]]
      ];
      AppendTo[res, new];
      t += 1;
    ];
    (* Echo[N[non/nT], "non"]; *)
    Return[res]
  ]

(**** </VickMonitor> ****)


End[]

EndPackage[]
