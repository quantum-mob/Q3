(* Clifford quantum circuits *)

BeginPackage["Q3`"]

{ CliffordState, RandomCliffordState };

{ CliffordUnitary, RandomCliffordUnitary };

{ PauliMeasurement };

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

CliffordState[Ket[v_?VectorQ], rest___] := Module[
  { n = Length[v],
    vv, pp },
  vv = SparseArray @ NestList[RotateRight[#, 2]&, PadRight[{0, 1}, 2n], n-1];
  CliffordState[Transpose @ Append[Transpose @ vv, IntegerParity @ v], rest]
]


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
  ch = Map[GottesmanInner[msr, #]&, vv];
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
  chk = Map[GottesmanInner[msr, #]&, Most /@ gnr];
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

(**** </Measurement> ****)


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

CliffordLogarithmicNegativity::usage = "CliffordLogarithmicNegativity[cs, {k1, k2, \[Ellipsis]}] returns the logarithmic negativity cs between qubits {k1, k2, \[Ellipsis]} and the rest of Clifford state.\nCliffordLogarithmicNegativity[{k1, k2, \[Ellipsis]}] is an operator form of CliffordLogarithmicNegativity that can be applied to Clifford states."
(* SEE ALSO: Sang et at. (2021) and Weinstein et al. (2022) *)

CliffordLogarithmicNegativity[kk:{___Integer}][cs_CliffordState] :=
  CliffordLogarithmicNegativity[cs, kk]

CliffordLogarithmicNegativity[cs_CliffordState, kk:{___Integer}] := Module[
  { gnr = First[cs],
    chk },
  gnr = Map[Partition[#, 2]&, gnr];
  gnr = Flatten /@ gnr[[;;, kk]];
  (* chk = IntegerParity @ Outer[GottesmanInner, gnr, gnr, 1]; *)
  (* MatrixRank[chk] / 2 *)
  (* NOTE: The above two lines do not seem to work; hence, the following two lines instead. *)
  chk = Outer[GottesmanInner, gnr, gnr, 1];
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
  Fold[Construct[#2, #1]&, cs, gg]


numberOfQubits[CliffordState[mat_?MatrixQ, ___]] := (Last[Dimensions @ mat] - 1)/2

numberOfQubits[CliffordUnitary[_?MatrixQ, {_, n_Integer}, ___]] = n

numberOfQubits[CliffordUnitary[mat_?MatrixQ, ___?OptionQ]] := Length[mat] / 2

numberOfQubits[PauliMeasurement[_?VectorQ, {_, n_Integer}, ___]] = n

numberOfQubits[PauliMeasurement[vec_?VectorQ, ___?OptionQ]] := Length[vec] / 2

(**** </CliffordCircuit> ****)


(**** <RandomCliffordCircuit> ****)

RandomCliffordCircuit::usage = "RandomCliffordCircuit[{n, t}, p] generates a Clifford circuit of depth 3t on n qubits with alternating layers of randomly selected two-qubit Clifford unitary gates and single-qubit Pauli measurements, where each qubit is measured with probability p in the computational basis."

RandomCliffordCircuit[vol:{n_Integer, t_Integer}, p_?NumericQ] :=
  CliffordCircuit @ Nest[
    Append[
      Join[#, randomCliffordUnitaryLayer @ n],
      randomPauliMeasurementLayer[n, p]
    ]&,
    { CliffordState @ Ket @ Table[0, n] },
    t
  ]


randomPauliMeasurementLayer::usage = "randomPauliMeasurementLayer[n, p] generates a layer of single-qubit Pauli measurements on qubits selected randomly with probability p among n qubits."

randomPauliMeasurementLayer[n_Integer, p_?NumericQ] := Module[
  { kk = RandomPick[Range @ n, p] },
  CliffordCircuit @ Map[PauliMeasurement[{0, 1}, #]&, kk]
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

RandomCliffordCircuitSimulate[{n_Integer, t_Integer}, p_?NumericQ, OptionsPattern[]] := Module[
  { k = 0,
    progress = 0,
    save, data, qc, sn, sm },
  PrintTemporary @ ProgressIndicator @ Dynamic[progress];

  (* simulation *)
  {sn, sm} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    qc = RandomCliffordCircuit[{n, t}, p];
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
