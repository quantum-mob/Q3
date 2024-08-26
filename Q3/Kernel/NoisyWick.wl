BeginPackage["Q3`"]

{ NoisyWickSimulate };
{ WickDampingOperator };

Begin["`Private`"]

(**** <WickDampingOperator> ****)

WickDampingOperator::usage = "WickDampingOperator[jmp] returns a pair {mat, const} of the quadratic kernel mat and remaining constant term const of the effective damping operator in the normal ordering that corresponds to the list jmp of quantum jump operators."

WickDampingOperator::jmp = "Invalid form of quantum jump operators ``."

WickDampingOperator[jmp:{__WickOperator}] :=
  WickDampingOperator @ Flatten[ First /@ jmp ]

WickDampingOperator[jmp:{Rule[_, _?VectorQ]..}] := Module[
  { dmp = GroupBy[jmp, First, Values],
    aa, bb },
  If[ !ContainsOnly[Keys @ dmp, {Identity, Dagger}] || !MatrixQ[Catenate @ dmp],
    Message[WickDampingOperator::jmp, Short @ jmp];
    Return[$Failed]
  ];
    
  aa = Topple[dmp[Identity]] . dmp[Identity];
  bb = Topple[dmp[Dagger]] . dmp[Dagger];
  { aa - Transpose[bb], Tr[bb] } / 2
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

NoisyWickSimulate[ham_, jmp:{__WickOperator}, in_WickState, {nT_Integer, dt_}, OptionsPattern[]] :=
  Module[
    { n = OptionValue["Samples"],
      k = 0,
      progress = 0,
      aa, bb, dmp, fac, non },
    
    {dmp, fac} = WickDampingOperator[jmp];
    fac = Exp[-dt*fac];
    non = ham - I * dmp;
    non = WickGaussian @ {MatrixExp[-I*dt*non], MatrixExp[+I*dt*non]};

    PrintTemporary @ ProgressIndicator @ Dynamic[progress];
    data = Table[
      progress = ++k / n;
      (* theNoisyWickSimulate[non, jmp, in, {nT, dt}], *)
      altNoisyWickSimulate[{non, fac}, jmp, in, {nT, dt}],
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
        Message[NoisyWickSimulate::save]
      ]
    ];
    Return[data]
  ] /; If[ MatrixQ[ham, NumericQ], True,
    Message[NoisyWickSimulate::ham, ham];
    False
  ]

altNoisyWickSimulate[{non_WickGaussian, fac_}, jmp:{__WickOperator}, in_WickState, {nT_Integer, dt_}] :=
  Module[
    { res = {in},
      new = N[in],
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
          new = WickState[0, Last @ in]; (* null state *)
          AppendTo[res, new];
          t += 1;
          Break[],
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

theNoisyWickSimulate[{non_WickGaussian, fac_}, jmp:{__WickOperator}, in_WickState, {nT_Integer, dt_}] :=
  Module[
    { res = {in},
      new = N[in],
      prb, pos, out, tmp, pp, qq, ww, t },
    t = 1;
    While[ t <= nT,
      pp = RandomReal[];
      qq = RandomReal[];
      
      (* non-unitary evolution *)
      While[ t <= nT,
        out = fac * non[new];
        If[ pp < NormSquare[out],
          (* then *)
          AppendTo[res, Normalize @ out];
          new = out;
          t += 1,
          (* else *)
          out = new;
          Break[]
        ]
      ];
      
      If[t > nT, Break[]];

      (* quantum jumps *)
      out = Through[jmp[out]];

      prb = Chop @ Accumulate[NormSquare /@ out];
      Quiet[
        Check[
          prb /= Last[prb],
          (* error *)
          Message[NoisyWickSimulate::null];
          new = WickState[0, Last @ in]; (* null state *)
          AppendTo[res, new];
          t += 1;
          Break[],
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
