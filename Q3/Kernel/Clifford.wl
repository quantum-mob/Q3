(* Clifford quantum circuits *)

BeginPackage["Q3`"]

{ CliffordState, RandomCliffordState };

{ CliffordUnitary, RandomCliffordUnitary };

{ PauliMeasurement, PauliDecoherence };

{ CliffordCircuit, RandomCliffordCircuit, RandomCliffordCircuitSimulate };

{ CliffordLogarithmicNegativity };

Begin["`Private`"]

(**** <CliffordState> ****)

CliffordState::usage = "CliffordState[data, {s1, s2, \[Ellipsis]}] represents a stabilizer state on qubits s1, s2, \[Ellipsis] with the generating set of stabilizer subgroup specified by data.\nThe data is a matrix each row of which is a full Gottesman vaector referring to the Pauli string corresponding to a stabilizer generator."

CliffordState::bad = "`` is not a proper set of Gottesman vectors."

CliffordState /:
MakeBoxes[cs:CliffordState[gnr_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[gnr];
  BoxForm`ArrangeSummaryBox[
    CliffordState, cs, None,
    { BoxForm`SummaryItem @ { "Qubits: ", (n-1)/2 },
      BoxForm`SummaryItem @ { "Generators: ", m}
    },
    { BoxForm`SummaryItem @ { "Gottesman vectors: ", ArrayShort @ Transpose @ Most @ Transpose @ gnr },
      BoxForm`SummaryItem @ { "Phase factors: ", ArrayShort @ Last @ Transpose @ gnr }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; If[ MatrixQ[Most @ Transpose @ gnr, BinaryQ], True,
  Message[CliffordState::bad, gnr]; False
]

(* canonicalization *)
CliffordState[data_, ss:{___?QubitQ}, rest___] :=
  CliffordState[data, FlavorCap @ ss, rest] /; Not[FlavorCapQ @ ss]

(* quick initialization *)
CliffordState[Ket[v_?VectorQ], rest___] := Module[
  { n = Length[v],
    vv, pp },
  vv = SparseArray @ NestList[RotateRight[#, 2]&, PadRight[{0, 1}, 2n], n-1];
  CliffordState[Transpose @ Append[Transpose @ vv, IntegerParity @ v], rest]
]

(* quick initialization *)
CliffordState[Ket[a_Association], rest___] :=
  CliffordState[ Ket @ Values @ KeySelect[a, QubitQ] ]


CliffordState /:
StabilizerGenerators[CliffordState[gnr_, ___?OptionQ]] :=
  Map[FromGottesmanVector[#, Pauli]&, gnr]

CliffordState /:
StabilizerGenerators[CliffordState[gnr_, ss:{__?QubitQ}, ___?OptionQ]] :=
  Map[FromGottesmanVector[#, ss]&, gnr]

CliffordState /:
Matrix @ CliffordState[data_?MatrixQ, ___] := Module[
  { mm = FromGottesmanVector /@ Most /@ data,
    m, n },
  {m, n} = Dimensions[data];
  n = Power[2, (n - 1)/2];
  mm *= Map[Last, data];
  Apply[Dot, ConstantArray[One[n], m] + mm] / n
]


CliffordState /:
CNOT[i_Integer, j_Integer][cs_CliffordState] :=
  ReplacePart[cs, 1 -> CNOT[i, j] @ First @ cs]

CliffordState /:
SWAP[i_Integer, j_Integer][cs_CliffordState] :=
  ReplacePart[cs, 1 -> SWAP[i, j] @ First @ cs]

CliffordState /:
Hadamard[kk:{__Integer}][cs_CliffordState] :=
  ReplacePart[cs, 1 -> Hadamard[kk] @ First @ cs]

CliffordState /:
Quadrant[kk:{__Integer}][cs_CliffordState] :=
  ReplacePart[cs, 1 -> Quadrant[kk] @ First @ cs]


CliffordState /:
CliffordUnitary[mat_, kk:{__Integer}, ___?OptionQ][cs_CliffordState] :=
  ReplacePart[cs, 1 -> GottesmanMap[mat, kk] @ First @ cs]

CliffordState /:
CliffordUnitary[mat_, ___?OptionQ][cs_CliffordState] := With[
  { new = GottesmanMap[mat] @ First @ cs },
  ReplacePart[cs, 1 -> new]
] /; GttsMatrixQ[Most @ Transpose @ mat]


CliffordState /:
Multiply[pre___, cu:(_CNOT|_SWAP|_Hadamard|_Quadrant|_CliffordUnitary), cs_CliffordState, post___] :=
  Multiply[pre, cu[cs], post]

(**** </CliffordState> ****)


RandomCliffordState::usage = "RandomCliffordState[n] returns a uniformly distributed random stabilizer pure state on n qubits."

RandomCliffordState[n_Integer] := Module[
  { op = RandomCliffordUnitary[n],
    in = PadRight[{0, 1}, 2n] },
  in = NestList[RotateRight[#, 2]&, in, n-1];
  in = Transpose @ SparseArray @ Append[Transpose @ in, ConstantArray[1, n]];
  op[CliffordState @ in]
]

RandomCliffordState[ss:{__?QubitQ}] :=
  Insert[RandomCliffordState[Length @ ss], ss, 2]


(**** <PauliMeasurement> ****)

PauliMeasurement::usage = "PauliMeasurement[vec] represents the Pauli measurement corresponding to Gottesman vector vec.\nPauliMeasurement[vec, {{k1, k2, \[Ellipsis]}, n}] represents the Pauli measurement on particular qubits numbered k1, k2, \[Ellipsis] among n qubits."

PauliMeasurement[msr_?GottesmanVectorQ, k_Integer] :=
  PauliMeasurement[msr, {k}]

PauliMeasurement[msr_?GottesmanVectorQ, kk:{___Integer}][cs_CliffordState] := Module[
  { ii = Riffle[2kk-1, 2kk],
    vv = First[cs], ch, new, gnr },
  vv = vv[[;;, ii]];
  ch = Map[GottesmanDot[msr, #]&, vv];
  If[ ArrayZeroQ[ch],
    $MeasurementOut[msr] = Indeterminate;
    Return[cs]
  ];
  (* Simulate the measurement process. *)
  ch = Position[ch, 1];
  Module[
    { gnr = First[cs],
      new, alt },
    If[ RandomReal[] < 0.5,
      $MeasurementOut[msr] = 0;
      new = Append[msr, +1],
      $MeasurementOut[msr] = 1;
      new = Append[msr, -1]
    ];
    new = GottesmanVectorEmbed[new, {kk, (Last[Dimensions @ gnr] - 1)/2}];
    alt = gnr[[First @ First @ ch]];
    gnr = ReplacePart[gnr, First[ch] -> new];
    gnr = ReplaceAt[gnr, v_?VectorQ :> GottesmanTimes[alt, v], Rest @ ch];
    ReplacePart[cs, 1 -> SparseArray[gnr]]
  ]
]

PauliMeasurement[msr_?GottesmanVectorQ][cs_CliffordState] := Module[
  { gnr = First[cs],
    chk, new },
  chk = Map[GottesmanDot[msr, #]&, Most /@ gnr];
  If[ ArrayZeroQ[chk],
    $MeasurementOut[msr] = Indeterminate;
    Return[cs]
  ];
  (* Simulate the measurement process. *)
  If[ RandomReal[] < 0.5,
    $MeasurementOut[msr] = 0;
    new = Append[msr, +1],
    $MeasurementOut[msr] = 1;
    new = Append[msr, -1]
  ];
  ReplacePart[cs, 1 -> UpdateStabilizerGenerators[gnr, new]]
]


PauliMeasurement /:
Multiply[pre___, msr_PauliMeasurement, cs_CliffordState] := 
  Multiply[pre, msr @ cs]

(**** </PauliMeasurement> ****)


(**** <PauliDecoherence> ****)

PauliDecoherence::usage = "PauliDecoherence[vec] represents the Pauli measurement corresponding to Gottesman vector vec.\nPauliDecoherence[vec, {{k1, k2, \[Ellipsis]}, n}] represents the Pauli measurement on particular qubits numbered k1, k2, \[Ellipsis] among n qubits."

PauliDecoherence[msr_?GottesmanVectorQ, k_Integer] :=
  PauliDecoherence[msr, {k}]

PauliDecoherence[msr_?GottesmanVectorQ, kk:{___Integer}][cs_CliffordState] := Module[
  { ii = Riffle[2kk-1, 2kk],
    vv = First[cs], ch, new, gnr },
  vv = vv[[;;, ii]];
  ch = Map[GottesmanDot[msr, #]&, vv];
  If[ArrayZeroQ[ch], Return[cs]];
  (* Simulate the deocherence process. *)
  ch = Position[ch, 1];
  Module[
    { gnr = First[cs],
      alt },
    alt = gnr[[First @ First @ ch]];
    gnr = ReplaceAt[gnr, v_?VectorQ :> GottesmanTimes[alt, v], Rest @ ch];
    gnr = Delete[gnr, First @ ch];
    If[gnr == {}, gnr = Zero @ {1, Length @ alt}]; (* the maximally-mixed state *)
    ReplacePart[cs, 1 -> SparseArray[gnr]]
  ]
]


PauliDecoherence /:
Multiply[pre___, msr_PauliDecoherence, cs_CliffordState] := 
  Multiply[pre, msr @ cs]

(**** </PauliDecoherence> ****)


(**** <CliffordUnitary> ****)

CliffordUnitary::usage = "CliffordUnitary[mat] represents a Clifford unitary operator."

CliffordUnitary::bad = "`` is not a proper Gottesman matrix."

CliffordUnitary /:
MakeBoxes[cu:CliffordUnitary[mat_?MatrixQ, ___?OptionQ], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[mat];
  BoxForm`ArrangeSummaryBox[
    CliffordUnitary, cu, None,
    { BoxForm`SummaryItem @ { "Qubits: ", m/2 },
      BoxForm`SummaryItem @ { "Dimensions: ", {m, m}}
    },
    { BoxForm`SummaryItem @ { "Gottesman matrix: ", ArrayShort @ Transpose @ Most @ Transpose @ mat },
      BoxForm`SummaryItem @ { "Sign bits: ", ArrayShort @ Last @ Transpose @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; If[ GttsMatrixQ[Most @ Transpose @ mat], True,
  Message[CliffordUnitary::bad, mat]; False
]

CliffordUnitary /:
MakeBoxes[cu:CliffordUnitary[mat_?MatrixQ, kk:{__Integer}, ___?OptionQ], fmt_] := 
  BoxForm`ArrangeSummaryBox[
    CliffordUnitary, cu, None,
    { BoxForm`SummaryItem @ { "Qubits: ", Indeterminate },
      BoxForm`SummaryItem @ { "Acting on: ", kk}
    },
    { BoxForm`SummaryItem @ { "Gottesman matrix: ", ArrayShort @ Transpose @ Most @ Transpose @ mat },
      BoxForm`SummaryItem @ { "Sign bits: ", ArrayShort @ Last @ Transpose @ mat }
    },
    fmt,
    "Interpretable" -> Automatic
  ] /; If[ GttsMatrixQ[Most @ Transpose @ mat], True,
    Message[CliffordUnitary::bad, mat]; False
  ]

CliffordUnitary[mat_, k_Integer, rest___] :=
  CliffordUnitary[mat, {k}, rest]


CliffordUnitary /:
Matrix[CliffordUnitary[mat_?MatrixQ, kk:{__Integer}, ___?OptionQ], n_Integer] :=
  MatrixEmbed[FromGottesmanMatrix[mat], kk, n]

CliffordUnitary /:
Matrix @ CliffordUnitary[mat_?MatrixQ, ___?OptionQ] :=
  FromGottesmanMatrix[mat]

(**** </CliffordUnitary> ****)


RandomCliffordUnitary::usage = "RandomCliffordUnitary[n] generates a uniformly distributed random Clifford unitary operator on n qubits."

RandomCliffordUnitary[n_Integer, spec___] :=
  CliffordUnitary[RandomFullGottesmanMatrix @ n, spec]


(**** <CliffordLogarithmicNegativity> ****)

CliffordLogarithmicNegativity::usage = "CliffordLogarithmicNegativity[cs, {k1, k2, \[Ellipsis]}] returns the logarithmic negativity between qubits {k1, k2, \[Ellipsis]} and the rest in Clifford state cs.\nCliffordLogarithmicNegativity[{k1, k2, \[Ellipsis]}] is an operator form of CliffordLogarithmicNegativity that can be applied to Clifford states."
(* SEE ALSO: Sang et at. (2021) and Weinstein et al. (2022) *)

CliffordLogarithmicNegativity[kk:{___Integer}][cs_CliffordState] :=
  CliffordLogarithmicNegativity[cs, kk]

CliffordLogarithmicNegativity[cs_CliffordState, kk:{___Integer}] := Module[
  { gnr = First[cs],
    chk },
  gnr = gnr[[ ;; , Riffle[2kk-1, 2kk] ]];
  chk = GottesmanDot[gnr, gnr];
  (* MatrixRank[IntegerParity @ chk] / 2 *)
  (* NOTE: The above line does not seem to work; hence, the following line instead. *)
  MatrixRank[chk, Modulus -> 2] / 2
]

(**** </CliffordLogarithmicNegativity> ****)


(**** <CliffordCircuit> ****)

CliffordCircuit::usage = "CliffordCircuit[{g1, g2, \[Ellipsis]}] represents a quantum circuit with Clifford unitary gates or Pauli measurements g1, g2, \[Ellipsis]."

CliffordCircuit /:
MakeBoxes[cc:CliffordCircuit[{}, ___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    CliffordCircuit, cc, None,
    { BoxForm`SummaryItem @ { "Qubits: ", Indeterminate },
      BoxForm`SummaryItem @ { "Depth: ", Length @ gg }
    },
    { },
    fmt,
    "Interpretable" -> Automatic
  ]

CliffordCircuit /:
MakeBoxes[cc:CliffordCircuit[gg:{__}, ___?OptionQ], fmt_] := Module[
  { n = numberOfQubits[First @ gg] },
  BoxForm`ArrangeSummaryBox[
    CliffordCircuit, cc, None,
    { BoxForm`SummaryItem @ { "Qubits: ", n },
      BoxForm`SummaryItem @ { "Depth: ", Length @ gg }
    },
    { },
    fmt,
    "Interpretable" -> Automatic
  ]
]

CliffordCircuit[{}][cs_CliffordState] = cs

CliffordCircuit[gg:{_CliffordState, ___}][cs_CliffordState] :=
  CliffordCircuit[Rest @ gg][cs]

CliffordCircuit[gg_List][cs_CliffordState] :=
  Fold[Construct[#2, #1]&, cs, Flatten @ gg]

CliffordCircuit /:
Elaborate @ CliffordCircuit[gg:{_CliffordState, ___}] :=
  Fold[Construct[#2, #1]&, Flatten @ gg]


CliffordCircuit /:
Show[cc_CliffordCircuit, S_Symbol?QubitQ, more___?OptionQ] :=
  Graphics[cc, S, more]

CliffordCircuit /:
Graphics[CliffordCircuit[gg_List], S_Symbol?QubitQ, more___?OptionQ] := Module[
  { n, cs, ss, qc },
  n = FirstCase[gg, g:_Symbol[__] :> numberOfQubits[g], Indeterminate, Infinity];
  If[n === Indeterminate, n = 1];
  ss = S[Range @ n, $];
  qc = gg /. {
    CliffordCircuit[{}] -> "Spacer",
    CliffordCircuit -> Identity,
    CliffordState[__] :> Ket[ss],
    CliffordUnitary[m_, kk_, opts___?OptionQ] :> Gate[S[kk, $], opts],
    CliffordUnitary[m_, opts___?OptionQ] :> Gate[ss, opts, "Label" -> "U"],
    PauliMeasurement[v_, kk_, opts___?OptionQ] :> Gate[S[kk, $], opts, "Shape" -> "Measurement"],
    PauliDecoherence[v_, kk_, opts___?OptionQ] :> Gate[S[kk, $], opts, "Label" -> "\[ScriptCapitalD]"],
    CNOT[i_, j_] :> Gate[{S[i,$]->1}, {S[j,$]}, "Shape" -> "CirclePlus"],
    SWAP[i_, j_] :> Gate[{S[i,$]->1}, {S[j,$]}, "Shape" -> "Cross", "ControlShape" -> "Cross"],
    Hadamard[kk_] :> Map[Gate[{#}, "Label" -> "H"]&, S[kk,$]],
    Quadrant[kk_] :> Map[Gate[{#}, "Label" -> "S"]&, S[kk,$]]
  };
  QuantumCircuit[Sequence @@ qc, "PostMeasurementDashes" -> False]
]


numberOfQubits[CliffordState[mat_?MatrixQ, ___]] := (Last[Dimensions @ mat] - 1)/2

numberOfQubits[CliffordUnitary[mat_?MatrixQ, ___?OptionQ]] := Length[mat] / 2

numberOfQubits[PauliMeasurement[vec_?VectorQ, ___?OptionQ]] := Length[vec] / 2

numberOfQubits[PauliDecoherence[vec_?VectorQ, ___?OptionQ]] := Length[vec] / 2

numberOfQubits[_] = Indeterminate

(**** </CliffordCircuit> ****)


(**** <RandomCliffordCircuit> ****)

RandomCliffordCircuit::usage = "RandomCliffordCircuit[{n, t}, p] generates a Clifford circuit of depth 3t on n qubits with alternating layers of randomly selected two-qubit Clifford unitary gates and single-qubit Pauli measurements, where each qubit is measured with probability p in the computational basis."

RandomCliffordCircuit[vol:{n_Integer, t_Integer}, pp:(_?NumericQ|{_?NumericQ, _?NumericQ})] :=
  CliffordCircuit @ Nest[
    Append[
      Join[#, randomCliffordUnitaryLayer @ n],
      randomPauliMeasurementLayer[n, pp]
    ]&,
    { CliffordState @ Ket @ Table[0, n] },
    t
  ]


randomPauliMeasurementLayer::usage = "randomPauliMeasurementLayer[n, p] generates a layer of single-qubit Pauli measurements on qubits selected randomly with probability p among n qubits."

randomPauliMeasurementLayer[n_Integer, p_?NumericQ] := Module[
  { kk = RandomPick[Range @ n, p] },
  CliffordCircuit @ Map[PauliMeasurement[{0, 1}, #]&, kk]
]

randomPauliMeasurementLayer[n_Integer, {0|0., p_?NumericQ}] := Module[
  { kk = RandomPick[Range @ n, p],
    mm = {{1, 0}, {0, 1}, {1, 1}} },
  CliffordCircuit @ Map[PauliDecoherence[RandomChoice @ mm, #]&, kk]
]

randomPauliMeasurementLayer[n_Integer, pp:{_?NumericQ, _?NumericQ}] := Module[
  { kk = RandomPick[Range @ n, Total @ pp],
    mm = PauliMeasurement[{0, 1}],
    dc = PauliDecoherence /@ {{1, 0}, {0, 1}, {1, 1}},
    pm = First[pp] / Total[pp] },
  CliffordCircuit @ Table[
    Append[If[RandomReal[] < pm, mm, RandomChoice @ dc], k],
    {k, kk}
  ]
]

randomCliffordUnitaryLayer::usage = "randomPauliMeasurementLayer[n] generates a layer of random two-qubit Clifford unitaries on every pair of nearest-neighbor qubits among n qubits."

randomCliffordUnitaryLayer[n_Integer] := {
  randomCliffordUnitaryLayer[n, 1],
  randomCliffordUnitaryLayer[n, 2]
}

randomCliffordUnitaryLayer[n_Integer, k_Integer] := Module[
  { kk, gg },
  kk = Partition[Range[k, n], 2];
  gg = Table[RandomFullGottesmanMatrix[2], Length @ kk];
  CliffordCircuit @ MapThread[CliffordUnitary, {gg, kk}]
]

(**** </RandomCliffordCircuit> ****)


(**** <RandomCliffordCircuitSimulate> ****)

RandomCliffordCircuitSimulate::usage = "RandomCliffordCircuitSimulate[{n, t}, p] simulates a Clifford quantum circuit of depth 3t on n qubits with alternating layers of randomly selected two-qubit Clifford unitary gates and single-qubit Pauli measurements, where each qubit is measured with probability p in the computational basis."

RandomCliffordCircuitSimulate::save = "The result could not be saved."

Options[RandomCliffordCircuitSimulate] = {
  "Samples" -> {10, 5},
  "SaveData" -> False,
  "Overwrite" -> True,
  "Filename" -> Automatic,
  "Prefix" -> "RCC"
}

RandomCliffordCircuitSimulate[
  {n_Integer, t_Integer},
  pp:(_?NumericQ|{_?NumericQ, _?NumericQ}), 
  OptionsPattern[]
] := Module[
  { k = 0,
    progress = 0,
    save, data, qc, sn, sm },
  PrintTemporary @ ProgressIndicator @ Dynamic[progress];

  (* simulation *)
  {sn, sm} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    qc = RandomCliffordCircuit[{n, t}, pp];
    { Table[
        progress = ++k / (sn*sm);
        FoldList[Construct[#2, #1]&, First @ qc],
        sm
      ],
      qc
    },
    sn
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
    (* NOTE: Clifford circuits are not saved. *)
    save = Export[file, Flatten[First @ data, 1]];
    If[ FailureQ[save],
      Message[RandomCliffordCircuitSimulate::save],
      Echo[file, "Saved to"]
    ]
  ];
  Return[data]
]

(**** </RandomCliffordCircuitSimulate> ****)


End[]

EndPackage[]
