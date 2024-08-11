BeginPackage["Q3`"]

{ NoisyWickSimulate };

Begin["`Private`"]

(**** <NoisyWickSimulate> ****)

NoisyWickSimulate::usage = "NoisyWickSimulate[ham, jmp, in, {n, dt}] solves the quantum master equation for a non-interacting dissipative fermionic many-body system by using the Monte Carlo simulation method (alos known as the quantum jump approach or quantum trajectory method). The model is specified by the single-particle Hamiltonian matrix ham and the list jmp of quantum jump operators. The simulation starts from the initial WickState in at time 0 and goes n time steps by interval dt."

NoisyWickSimulate::ham = "The Hamiltonian matrix `` needs to be numeric."

NoisyWickSimulate::jmp = "Invalid form of quantum jump operators ``."

Options[NoisyWickSimulate] = {
  "Samples" -> 500,
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "NWS"
}

NoisyWickSimulate[ham_, jmp:{__WickOperator}, in_WickState, {nT_Integer, dt_}, OptionsPattern[]] :=
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

theNoisyWickSimulate[non_WickGaussian, jmp:{__WickOperator}, in_WickState, {nT_Integer, dt_}] :=
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
