BeginPackage["Q3`"]

{ NoisyWickState, WickElements };

{ WickGaussian };

{ NoisyWickSimulate };

Begin["`Private`"]

AddElaborationPatterns[_NoisyWickState, _WickGaussian];


(**** <NoisyWickState> ****)

NoisyWickState::usage = "NoisyWickState[spec, {c1, c2, \[Ellipsis]}] represents a noisy Wick state for fermions {c1, c2, \[Ellipsis]} that has undergone quantum decoherence processes specified by spec."

NoisyWickState::bad = "Unsupported form of NoisyWickState ``."


NoisyWickState /:
MakeBoxes[ws:NoisyWickState[ops:{___Rule}, cc:{___?FermionQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    NoisyWickState, ws, None,
    { BoxForm`SummaryItem @ { "Modes: ", cc },
      BoxForm`SummaryItem @ { "Particles: ", Count[Keys @ ops, Dagger] - Count[Keys @ ops, Identity] }
    },
    { BoxForm`SummaryItem @ { "Operator transforms: ", ArrayShort @ Values @ ops }    
    },
    fmt,
    "Interpretable" -> Automatic
  ]

NoisyWickState[cc:{__?FermionQ}] := NoisyWickState[{}, cc]

NoisyWickState[Ket[aa_Association]] := Module[
  { cc = Select[Keys @ aa, FermionQ],
    dd = Select[Keys @ Q3`Private`theKetTrim @ aa, FermionQ],
    pos, mat },
  pos = Map[First @ FirstPosition[cc, #]&, dd];
  mat = One[Length @ cc];
  NoisyWickState[Thread[Dagger -> mat[[pos]]], cc]
]

NoisyWickState[ops:{HoldPattern[Dagger[_?FermionQ]]..}, cc:{__?FermionQ}] :=
  NoisyWickState @ Ket[cc -> 0, Peel[ops] -> 1]

NoisyWickState[ops:{Rule[_, _?VectorQ]..}, cc:{___?FermionQ}] :=
  NoisyWickState[Thread[Map[Hood, Keys @ ops] -> Values[ops]], cc] /;
  AnyTrue[Keys @ ops, AnyFermionQ]


NoisyWickState /:
NormSquare[NoisyWickState[{}, cc:{___?FermionQ}]] = 1

NoisyWickState /:
NormSquare[NoisyWickState[ops:{__Rule}, cc:{__?FermionQ}]] := 
  Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[theConjugateReverse @ ops, ops], Det::luc]

NoisyWickState /:
Norm[ws:NoisyWickState[{___Rule}, {__?FermionQ}]] := Sqrt[NormSquare @ ws]


NoisyWickState /:
Normalize[ws:NoisyWickState[{}, {__?FermionQ}]] = ws

NoisyWickState /:
Normalize[ws:NoisyWickState[ops:{___Rule}, cc:{___?FermionQ}]] := Module[
  { new },
  new = Thread[Keys[ops] -> Values[ops] * Power[Norm @ ws, -1/Length[ops]]];
  NoisyWickState[new, cc]
]


NoisyWickState /:
Elaborate[ws_NoisyWickState] = ws (* fallback *)

NoisyWickState /:
Elaborate[ws:NoisyWickState[{___Rule}, cc:{__?FermionQ}]] := Module[
  { ff = WickElements[ws] },
  KetChop[ Multiply @@ Append[ff, Ket[cc]] ]
]


NoisyWickState /:
Matrix[ws_NoisyWickState, rest___] := (
  Message[NoisyWickState::bad, ws];
  Matrix[Ket[], rest]
)

NoisyWickState /:
Matrix[ws:NoisyWickState[{___Rule}, cc:{__?FermionQ}]] := Matrix[ws, cc]

NoisyWickState /:
Matrix[ws:NoisyWickState[ops:{___Rule}, cc:{__?FermionQ}], ss:{__?SpeciesQ}] :=
  With[
    { ff = WickElements[ops, cc] },
    SparseArray @ Fold[
      Dot[#2, #1]&,
      Matrix[Ket[], ss],
      Reverse @ Matrix[ff, ss]
    ]
  ]


NoisyWickState /:
NonCommutativeQ[_NoisyWickState] = True

NoisyWickState /:
MultiplyKind[_NoisyWickState] = Fermion

(**** </NoisyWickState> ****)


(**** <theConjugateReverse> ****)

theConjugateReverse::usage = "theConjugateReverse[{flag1 -> vec1, flag2 -> vec2, ...}] returns the reversed list of rules with the values complex conjugated and the flags interchanges (Idenity <-> Dagger)."

theConjugateReverse[ops:{Rule[Identity|Dagger, _?VectorQ]...}] :=
  Reverse @ Thread @ Rule[
    ReplaceAll[Keys @ ops, {Identity -> Dagger, Dagger -> Identity}],
    Conjugate[Values @ ops]
  ]

(**** </theConjugateReverse> ****)


(**** <WickElements> ****)

WickElements::usage = "WickElements[spec, {c1, c2, \[Ellipsis]}] returns a list of linear combinations of bare fermion operators corresponding to specification spec."

WickElements[ops:{___Rule}, cc:{__?FermionQ}] :=
  MapApply[#2 . #1[cc] &, ops]

WickElements[WickOperator[ops:{___Rule}], cc:{__?FermionQ}] :=
  WickElements[ops, cc]

WickElements[NoisyWickState[ops:{___Rule}, cc:{__?FermionQ}], ___] :=
  WickElements[ops, cc]

(**** </WickElements> ****)


(**** <WickEntanglementEntropy> ****)

NoisyWickState /:
WickEntanglementEntropy[dd:{__?FermionQ}][ws_NoisyWickState] :=
  WickEntanglementEntropy[ws, dd]

NoisyWickState /:
WickEntanglementEntropy[ws_NoisyWickState, dd:{__?FermionQ}] :=
  WickEntanglementEntropy[WickGreensFunction[ws, dd], Range[Length @ dd]]

(**** </WickEntanglementEntropy> ****)


(**** <WickGreensFunction> ****)

WickGreensFunction[ws_NoisyWickState] :=
  WickGreensFunction[ws, Last @ ws]

NoisyWickState /:
WickGreensFunction[ws_NoisyWickState, dd:{___?FermionQ}] := Module[
  { cc = Last[ws],
    qq = First[ws],
    pp = theConjugateReverse[First @ ws],
    aa, bb, gg, n },
  bb = Lookup[First /@ PositionIndex[cc], dd];
  bb = One[Length @ cc][[bb]];
  aa = Thread[Identity -> bb];
  bb = Thread[Dagger -> bb];

  n = Length[dd];
  gg = Zero[{n, n}];
  Table[
    gg[[i, i]] = Re @ Sqrt @ Quiet[Det @ WickMatrix @ Join[pp, {aa[[i]], bb[[i]]}, qq], Det::luc],
    (* NOTE: The Pfaffians here are supposed to be real positive. *)
    (* 2024-07-08: Det[...] is enclosed in Quiet[..., Det::luc] because the warning message does not seem to be serious in most cases but goes off too often. *)
    {i, 1, n}
  ];
  Table[
    gg[[i, j]] = Pfaffian @ WickMatrix @ Join[pp, {aa[[i]], bb[[j]]}, qq];
    gg[[j, i]] = Conjugate @ gg[[i, j]],
    {i, 1, n},
    {j, i+1, n}
  ];
  Return[gg]
  (* NOTE: The noisy Wick state is assumed normalized. *)
]

(**** </WickGreensFunction> ****)


(**** <WickOperator> ****)

WickOperator /:
Multiply[pre___, op_WickOperator, ws_NoisyWickState] := Multiply[pre, op[ws]]

WickOperator[rr:{Rule[_, _?VectorQ]..}, ___][ws_NoisyWickState] :=
  NoisyWickState[Join[rr, First @ ws], Last @ ws]

WickOperator[ops:{__?AnyFermionQ}, ___][in_NoisyWickState] := Module[
  { pos = Map[First @ FirstPosition[Last @ in, #]&, Peel @ ops],
    mat = One[Length @ Last @ in],
    new },
  new = Join[Thread[Hood[ops] -> mat[[pos]]], First @ in];
  NoisyWickState[new, Last @ in]
]

(**** </WickOperator> ****)


(**** <WickGaussian> ****)

WickGaussian::usage = "WickGaussian[{mat, inv}] represents a non-unitary operator of the Gaussian form that is specified by the pair {mat, inv} of mutually inverse matrices."

WickGaussian::num = "Matrix `` needs to be numeric."

WickGaussian /:
MakeBoxes[WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    WickGaussian, mat, None,
    { BoxForm`SummaryItem @ { "Modes: ", Length @ mat },
      BoxForm`SummaryItem @ { "Type: ", "Non-unitary" }
    },
    { BoxForm`SummaryItem @ { "Transform: ", ArrayShort /@ {mat, inv} }
    },
    fmt,
    "Interpretable" -> Automatic
  ]

WickGaussian[mat_?MatrixQ, rest___] := WickGaussian[{mat, Inverse @ mat}, rest] /; 
  If[MatrixQ[mat, NumericQ], True, Message[WickGaussian::num, mat]; False]

WickGaussian[{mat_/;MatrixQ[mat, NumericQ], inv_/;MatrixQ[inv, NumericQ]}, ___][ws_NoisyWickState] := 
  Module[
    { new },
    new = MapApply[
      #1 -> Switch[#1, Dagger, mat . #2, Identity, #2 . inv, _, $Failed] &,
      First @ ws
    ];
    NoisyWickState[new, Last @ ws]
  ]


WickGaussian /:
MatrixForm[op : WickGaussian[{mat_?MatrixQ, inv_?MatrixQ}, ___]] :=
  MatrixForm @ mat

WickGaussian /: 
NonCommutativeQ[_WickGaussian] = True

WickGaussian /:
MultiplyKind[_WickGaussian] = Fermion

WickGaussian /:
Multiply[pre___, op_WickGaussian, ws_NoisyWickState] := Multiply[pre, op @ ws]

WickGaussian /:
Multiply[pre___, op_WickGaussian, fs_Ket] := Multiply[pre, op @ NoisyWickState @ fs]

(**** </WickGaussian> ****)


(**** <NoisyWickSimulate> ****)

NoisyWickSimulate::usage = "NoisyWickSimulate[ham, jmp, in, {n, dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian matrix ham and the list jmp of quantum jump operators. The simulation starts from the initial NoisyWickState in at time 0 and goes n time steps by interval dt."

NoisyWickSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

NoisyWickSimulate::jmp = "Invalid form of quantum jump operators ``."

Options[NoisyWickSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NWS"
}

NoisyWickSimulate[ham_, jmp:{__WickOperator}, in_NoisyWickState, {nT_Integer, dt_}, OptionsPattern[]] :=
  Module[
    { dmp = GroupBy[Flatten[First /@ jmp], First, Values],
      n = OptionValue["Samples"],
      k = 0,
      progress = 0,
      aa, bb, non },
    
    If[ !ContainsOnly[Key @ dmp, {Identity, Dagger}] || !MatrixQ[Catenate @ dmp],
      Message[NoisyWickSimulate::jmp, Short @ jmp];
      Return[$Failed]
    ];
    
    aa = Topple[dmp[Identity]].dmp[Identity];
    bb = Topple[dmp[Dagger]].dmp[Dagger];
    dmp = (aa - Transpose[bb] + Tr[bb] One[Dimensions @ bb]) / 2;
    non = ham - I * dmp;
    non = WickGaussian @ {MatrixExp[-I*dt*non], MatrixExp[+I*dt*non]};

    PrintTemporary @ ProgressIndicator @ Dynamic[progress];
    data = Table[
      progress = ++k / n;
      theNoisyWickSimulate[non, jmp, in, {nT, dt}],
      n
    ];
    Return[data]
  ] /; If[ MatrixQ[ham, NumericQ], True,
      Message[NoisyWickSimulate::ham, ham];
      False
    ]

theNoisyWickSimulate[non_WickGaussian, jmp:{__WickOperator}, in_NoisyWickState, {nT_Integer, dt_}] :=
  Module[
    { res = {in},
      new = in,
      prb, pos, out, tmp, pp, qq, ww, t },
    t = 1;
    While[ t <= nT,
      pp = RandomReal[];
      qq = RandomReal[];
      
      (* non-unitary evolution *)
      While[ t <= nT,
        out = non[new];
        If[ pp < NormSquare[out],
          AppendTo[res, Normalize @ out];
          new = out;
          t += 1,
          Break[]
        ]
      ];
      
      If[t > nT, Break[]];

      (* quantum jumps *)
      out = Through[jmp[out]];

      prb = Chop @ Accumulate[NormSquare /@ out];
      prb /= Last[prb];

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
