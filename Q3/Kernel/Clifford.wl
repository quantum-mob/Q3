(* Clifford quantum circuits *)

BeginPackage["Q3`"]

{ CliffordState, RandomCliffordState,
  CliffordPureQ, CliffordProjectors };

{ CliffordUnitary, RandomCliffordUnitary };

{ PauliMeasurement, PauliDecoherence };

{ CliffordCircuit, RandomCliffordCircuit, RandomCliffordCircuitSimulate };

{ CliffordEntropy,
  CliffordEntanglementEntropy,
  CliffordMutualInformation,
  CliffordLogarithmicNegativity };

Begin["`Private`"]

(**** <CliffordState> ****)

CliffordState::usage = "CliffordState[data, {s1, s2, \[Ellipsis]}] represents a stabilizer state on qubits s1, s2, \[Ellipsis] with the generating set of stabilizer subgroup specified by data.\nThe data is a matrix each row of which is a full Gottesman vaector referring to the Pauli string corresponding to a stabilizer generator."

CliffordState::bad = "`` is not a proper set of Gottesman vectors."

SetAttributes[CliffordState, NHoldAll]

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

QubitCount[CliffordState[gnr_?MatrixQ, ___]] := (Last[Dimensions @ gnr] - 1)/2

CliffordState /:
StabilizerGenerators[CliffordState[gnr_, ___?OptionQ]] :=
  Map[FromGottesmanVector[#, Pauli]&, gnr]

CliffordState /:
StabilizerGenerators[CliffordState[gnr_, ss:{__?QubitQ}, ___?OptionQ]] :=
  Map[FromGottesmanVector[#, ss]&, gnr]


CliffordState /: (* mixed state *)
Matrix @ CliffordState[gnr_?MatrixQ, ___] := Module[
  { n = Last[Dimensions @ gnr],
    mm },
  n = Power[2, (n - 1)/2];
  mm = CliffordProjectors[gnr];
  mm = Prepend[mm, Table[1, n]];
  Normalize @ Apply[Dot, mm]
] /; CliffordPureQ[gnr]

CliffordState /: (* mixed state *)
Matrix @ CliffordState[gnr_?MatrixQ, ___] := 
  Apply[Dot, CliffordProjectors @ gnr]


CliffordState /:
Matrix[cs:CliffordState[_?MatrixQ, ___], ss:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix @ cs, Select[ss, Qubits], ss]


CliffordState /:
Elaborate[cs_CliffordState] :=
  ExpressionFor[Matrix @ cs]

CliffordState /:
ExpressionFor[cs_CliffordState] :=
  ExpressionFor[Matrix @ cs]

CliffordState /:
ExpressionFor[cs_CliffordState, ss:{___?SpeciesQ}] :=
  ExpressionFor[Matrix @ cs, ss]


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


RandomCliffordState::usage = "RandomCliffordState[n] returns a uniformly distributed random stabilizer pure state on n qubits.\nRandomCliffordState[k, n] returns a random stabilizer mixed state (n > k) characterized by k independent stabilizer generators."

RandomCliffordState[n_Integer] := Module[
  { op = RandomCliffordUnitary[n],
    in = PadRight[{0, 1}, 2n] },
  in = NestList[RotateRight[#, 2]&, in, n-1];
  in = Transpose @ SparseArray @ Append[Transpose @ in, ConstantArray[1, n]];
  op[CliffordState @ in]
]

RandomCliffordState[k_Integer, n_Integer] := With[
  { gnr = First[RandomCliffordState @ n] },
  CliffordState @ RandomSelection[gnr, k]
]

RandomCliffordState[ss:{__?QubitQ}] :=
  Insert[RandomCliffordState[Length @ ss], ss, 2]

RandomCliffordState[k_Integer, ss:{__?QubitQ}] := With[
  { gnr = First[RandomCliffordState @ Length @ ss] },
  CliffordState[RandomSelection[gnr, k], ss]
]


CliffordPureQ::usage = "CliffordPureQ[cs] returns True if the Clifford state cs is a pure state; Falsoe, otherwise."

CliffordPureQ[CliffordState[gnr_?MatrixQ, ___]] :=
  CliffordPureQ[gnr]

CliffordPureQ[gnr_?MatrixQ] := Module[
  {m, n},
  {m, n} = Dimensions[gnr];
  TrueQ[2m == n-1]
]


CliffordProjectors::usage = "CliffordProjectors[gnr] returns a list of projection operators corresponding to the stabilizer generators specified by the list of Gottesman vectors gnr."

CliffordProjectors[CliffordState[gnr_?MatrixQ, ___]] :=
  CliffordProjectors[gnr]

CliffordProjectors[gnr_?MatrixQ] := Module[
  { mm = SparseArray /@ FromGottesmanVector /@ Most /@ gnr,
    m, n },
  {m, n} = Dimensions[gnr];
  n = Power[2, (n - 1)/2];
  mm *= Last[Transpose @ gnr];
  mm += ConstantArray[One @ n, m];
  (* NOTE (Mathematica v14.1): For some unknown reason, the above statement converts mm to normal matrix; not keep the SparseArray object. *)
  Map[SparseArray, mm / 2]
]


(**** <PauliMeasurement> ****)

PauliMeasurement::usage = "PauliMeasurement[vec] represents the Pauli measurement corresponding to Gottesman vector vec.\nPauliMeasurement[vec, {{k1, k2, \[Ellipsis]}, n}] represents the Pauli measurement on particular qubits numbered k1, k2, \[Ellipsis] among n qubits."

SetAttributes[PauliMeasurement, NHoldAll]

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
  chk = Map[GottesmanDot[msr, #]&, Transpose @ Most @ Transpose @ gnr];
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

CliffordUnitary::usage = "CliffordUnitary[mat] represents a Clifford unitary operator corresponding to full Gottesman matrix mat."

CliffordUnitary::bad = "`` is not a proper Gottesman matrix."

SetAttributes[CliffordUnitary, NHoldAll]

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


(**** <CliffordEntropy> ****)

CliffordEntropy::usage = "CliffordEntropy[cs] returns the von Neumann entropy of Clifford state cs."
(* SEE ALSO: Li, Chen, Fisher (2019), Nahum et al. (2017), etc. *)

CliffordEntropy[cs_CliffordState] :=
  QubitCount[cs] - Length[First @ cs]

(**** </CliffordEntropy> ****)


(**** <CliffordEntanglementEntropy> ****)

CliffordEntanglementEntropy::usage = "CliffordEntanglementEntropy[cs, {k1, k2, \[Ellipsis]}] returns the entanglement entropy between qubits {k1, k2, \[Ellipsis]} and the rest in the stabilizer pure state cs.\nCliffordEntanglementEntropy[{k1, k2, \[Ellipsis]}] is an operator form of CliffordEntanglementEntropy that can be applied to Clifford states."
(* SEE ALSO: Li, Chen, Fisher (2019), Nahum et al. (2017), etc. *)

CliffordEntanglementEntropy[kk:{___Integer}][cs_CliffordState] :=
  CliffordEntanglementEntropy[cs, kk]

CliffordEntanglementEntropy[cs_CliffordState, kk:{___Integer}] := Module[
  { mm = First[cs],
    ll, m, n },
  {m, n} = Dimensions[mm];
  n = (n-1)/2; (* the number of qubits *)
  ll = Complement[Range @ n, kk];
  mm = mm[[ ;; , Riffle[2ll-1, 2ll] ]];
  Length[kk] + MatrixRank[mm, Modulus -> 2] - m
]

(**** </CliffordEntanglementEntropy> ****)


(**** <CliffordMutualInformation> ****)

CliffordMutualInformation::usage = "CliffordMutualInformation[cs, {k1, k2, \[Ellipsis]}] returns the mutual information between qubits {k1, k2, \[Ellipsis]} and the rest in Clifford state cs.\nCliffordMutualInformation[{k1, k2, \[Ellipsis]}] is an operator form of CliffordMutualInformation that can be applied to Clifford states."
(* SEE ALSO: Li, Chen, Fisher (2019), Nahum et al. (2017), etc. *)

CliffordMutualInformation[kk:{___Integer}][cs_CliffordState] :=
  CliffordMutualInformation[cs, kk]

CliffordMutualInformation[cs_CliffordState, kk:{___Integer}] := Module[
  { bb = First[cs],
    ll, m, n },
  {m, n} = Dimensions[bb];
  n = (n-1)/2; (* the number of qubits *)
  ll = Complement[Range @ n, kk];
  aa = bb[[ ;; , Riffle[2kk-1, 2kk] ]];
  bb = bb[[ ;; , Riffle[2ll-1, 2ll] ]];
  MatrixRank[aa, Modulus -> 2] + MatrixRank[bb, Modulus -> 2] - m
]

(**** </CliffordMutualInformation> ****)


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
  { n = QubitCount[First @ gg] },
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
Elaborate @ CliffordCircuit[gg:{_CliffordState, ___}, ___] :=
  Fold[Construct[#2, #1]&, Flatten @ gg]


CliffordCircuit /:
Show[cc_CliffordCircuit, rest___] := Graphics[cc, rest]

CliffordCircuit /:
Graphics[qc:CliffordCircuit[_List, ___?OptionQ], more___?OptionQ] := Module[
  { S },
  Let[Qubit,S];
  Graphics[qc, S, more]
]

CliffordCircuit /:
Graphics[CliffordCircuit[gg_List, opts___?OptionQ], S_Symbol?QubitQ, more___?OptionQ] := Module[
  { n, cs, ss, qc },
  n = FirstCase[gg, g:_Symbol[__] :> QubitCount[g], Indeterminate, Infinity];
  If[n === Indeterminate, n = 1];
  ss = S[Range @ n, $];
  qc = gg /. {
    CliffordCircuit[{}] -> "Spacer",
    CliffordCircuit -> Identity,
    cs_CliffordState :> ExpressionFor[cs, ss],
    CliffordUnitary[_, kk_, any___?OptionQ] :> Gate[S[kk, $], any],
    CliffordUnitary[_, any___?OptionQ] :> Gate[ss, any, "Label" -> "U"],
    PauliMeasurement[_, kk_, any___?OptionQ] :> Gate[S[kk, $], any, "Shape" -> "Measurement"],
    PauliDecoherence[gnr_, kk_, any___?OptionQ] :> Gate[ S[kk, $], any,
      "Label" -> Subscript["\[ScriptCapitalD]", FromGottesmanVector[gnr, Pauli]]
    ],
    CNOT[i_, j_] :> Gate[{S[i,$]->1}, {S[j,$]}, "Shape" -> "CirclePlus"],
    SWAP[i_, j_] :> Gate[{S[i,$]->1}, {S[j,$]}, "Shape" -> "Cross", "ControlShape" -> "Cross"],
    Hadamard[kk_] :> Map[Gate[{#}, "Label" -> "H"]&, S[kk,$]],
    Quadrant[kk_] :> Map[Gate[{#}, "Label" -> "S"]&, S[kk,$]]
  };
  QuantumCircuit[Sequence @@ qc, more, opts, "PostMeasurementDashes" -> False]
]


QubitCount[CliffordUnitary[mat_?MatrixQ, ___?OptionQ]] := Length[mat] / 2

QubitCount[PauliMeasurement[vec_?VectorQ, ___?OptionQ]] := Length[vec] / 2

QubitCount[PauliDecoherence[vec_?VectorQ, ___?OptionQ]] := Length[vec] / 2

QubitCount[_] = Indeterminate

(**** </CliffordCircuit> ****)


(**** <RandomCliffordCircuit> ****)

RandomCliffordCircuit::usage = "RandomCliffordCircuit[in, {n, t}, p] generates a Clifford circuit of depth 3t on n qubits with the initial state 'in' and with alternating layers of randomly selected two-qubit Clifford unitary gates and single-qubit Pauli measurements, where each qubit is measured with probability p in the computational basis.\nRandomCliffordState[{n, t}, p] assumes the conventional initial state |0,0,\[Ellipsis]>."

RandomCliffordCircuit[
  vol:{n_Integer, t_Integer},
  prb:(_?NumericQ|{_?NumericQ, _?NumericQ})
] := RandomCliffordCircuit[CliffordState @ Ket @ Table[0, n], vol, prb]

RandomCliffordCircuit[
  ics:(_Ket | _CliffordState | "Random"), 
  vol:{n_Integer, t_Integer}, 
  prb:(_?NumericQ | {_?NumericQ, _?NumericQ}),
  opts___?OptionQ
] := Module[
  { in },
  in = Switch[ ics,
    "Random", RandomCliffordState[n],
    _Ket, CliffordState[ics],
    _, ics
  ];
  CliffordCircuit[
    Nest[
      Append[
        Join[#, randomCliffordUnitaryLayer @ n],
        randomPauliMeasurementLayer[n, prb]
      ]&,
      { in },
      t
    ],
    opts
  ]
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

RandomCliffordCircuitSimulate::usage = "RandomCliffordCircuitSimulate[in, {n, t}, spec] simulates Clifford circuits randomly generated by RandomCliffordCircuit[in, {n, t}, spec].\n RandomCliffordCircuitSimulate[{n, t}, spec] assumes the conventional input state |0,0,\[Ellipsis]>."

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
  opts:OptionsPattern[]
] := RandomCliffordCircuitSimulate[CliffordState @ Ket @ Table[0, n], {n, t}, pp, opts]

RandomCliffordCircuitSimulate[
  in:(_Ket | _CliffordState | "Random"),
  {n_Integer, t_Integer},
  pp:(_?NumericQ|{_?NumericQ, _?NumericQ}), 
  opts:OptionsPattern[]
] := Module[
  { progress = k = 0,
    data, more, qc, sn, sm },
  PrintTemporary @ ProgressIndicator @ Dynamic[progress];

  (* simulation *)
  {sn, sm} = doAssureList[OptionValue["Samples"], 2];
  data = Transpose @ Table[
    qc = RandomCliffordCircuit[in, {n, t}, pp];
    { Table[
        progress = ++k / N[sn*sm];
        FoldList[Construct[#2, #1]&, First @ qc],
        sm
      ],
      qc
    },
    sn
  ];

  If[ OptionValue["SaveData"],
    more = Join[{opts}, Options @ RandomCliffordCircuitSimulate];
    SaveData[data, FilterRules[{more}, Options @ SaveData]]
  ];
  Return[data]
]

(**** </RandomCliffordCircuitSimulate> ****)


End[]

EndPackage[]
