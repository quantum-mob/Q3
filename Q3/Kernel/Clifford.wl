(* Clifford quantum circuits *)

BeginPackage["Q3`"]

{ CliffordState, CliffordUnitary };

{ RandomCliffordState };

{ RandomCliffordState,
  RandomCliffordUnitary };

Begin["`Private`"]

(**** <CliffordState> ****)

CliffordState::usage = "CliffordState[data, {s1, s2, \[Ellipsis]}] represents a stabilizer state on qubits s1, s2, \[Ellipsis] with the generating set of stabilizer subgroup specified by data.\nThe data is a matrix each row of which is a full Gottesman vaector referring to the Pauli string corresponding to a stabilizer generator."

CliffordState /:
MakeBoxes[cs:CliffordState[gnr_?MatrixQ, ___], fmt_] := Module[
  {m, n},
  {m, n} = Dimensions[gnr];
  BoxForm`ArrangeSummaryBox[
    CliffordState, cs, None,
    { BoxForm`SummaryItem @ { "Qubits: ", (n-1)/2 },
      BoxForm`SummaryItem @ { "Generators: ", m}
    },
    { BoxForm`SummaryItem @ { "Gottesman vectors: ", ArrayShort @ gnr }
    },
    fmt,
    "Interpretable" -> Automatic
  ]
]

CliffordState[data_, ss : {___?QubitQ}, rest___] :=
 CliffordState[data, FlavorCap @ ss, rest] /; Not[FlavorCapQ @ ss]

CliffordState /:
StabilizerGenerators[CliffordState[gnr_, ___?OptionQ]] :=
  Map[FromGottesmanVector, gnr]

CliffordState /:
StabilizerGenerators[CliffordState[gnr_, ss:{__?QubitQ}, ___?OptionQ]] :=
  Map[FromGottesmanVector[#, ss]&, gnr]

CliffordState /:
Matrix @ CliffordState[data_?MatrixQ, ___] := Module[
  { mm = FromGottesmanVector /@ Most /@ data,
    m, n },
  {m, n} = Dimensions[data];
  n = Power[2, (n - 1)/2];
  mm = Matrix[mm*Map[Last, data]];
  Apply[Dot, ConstantArray[One[n], m] + mm]/n
]

(**** </CliffordState> ****)


(**** <Measurement> ****)

CliffordState /:
Multiply[pre___, Measurement[msr_/;VectorQ[msr, BinaryQ]], cs_CliffordState] := 
  Multiply[pre, theMeasurement[cs, msr]]

CliffordState /:
Measurement[msr_/;VectorQ[msr, BinaryQ]][cs_CliffordState] := 
  theMeasurement[cs, msr]

theMeasurement[cs:CliffordState[gnr_, rest___], msr_] := Module[
  { chk, new },
  chk = Map[GottesmanInner[msr, #]&, Most /@ gnr];
  If[ ArrayZeroQ[chk],
    $MeasurementOut[msr] = Indeterminate;
    Return[cs]
  ];  

  (* Simulate the measurement process. *)
  If[ RandomReal[] < 0.5,
    $MeasurementOut[c] = 0;
    new = Append[msr, +1],
    $MeasurementOut[c] = 1;
    new = Append[msr, -1]
  ];
  CliffordState[UpdateStabilizerGenerators[gnr, new], rest]
] /; VectorQ[msr, BinaryQ]

(**** </Measurement> ****)


RandomCliffordState::usage = "RandomCliffordState[n] returns a uniformly distributed random stabilizer pure state on n qubits."

RandomCliffordState[n_Integer] := Module[
  { op = RandomCliffordUnitary[n],
    in = PadRight[{0, 1}, 2n] },
  in = NestList[RotateRight[#, 2]&, in, n-1];
  in = Transpose @ SparseArray @ Append[Transpose @ in, ConstantArray[1, n]];
  op[CliffordState @ in]
]


(**** <CliffordUnitary> ****)

CliffordUnitary::usage = "CliffordUnitary[mat] represents a Clifford unitary operator."

CliffordUnitary /:
MakeBoxes[cu:CliffordUnitary[mat_?MatrixQ, ___], fmt_] := Module[
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
]

CliffordUnitary[mat_, ___][cs_CliffordState] := With[
  { new = Map[GottesmanTimes[#, mat]&, First @ cs] },
  ReplacePart[cs, 1 -> new]
] /; MatrixQ[Most @ Transpose @ mat, BinaryQ]

(* 
Module[
  { vec = Most /@ First[cs],
    sig = Last /@ First[cs] },
   sig *= IntegerParity[vec . Last[mat]];
   vec = Mod[vec . Most[mat], 2];
   CliffordState[Transpose @ Append[Transpose @ vec, sig]]
] /; MatrixQ[Most @ Transpose @ mat, BinaryQ]
 *)
CliffordUnitary /:
Multiply[pre___, cu_CliffordUnitary, cs_CliffordState, post___] :=
  Multiply[pre, cu[cs], post]

CliffordUnitary /:
Matrix @ CliffordUnitary[mat_?MatrixQ, ___] :=
  Matrix @ FromGottesmanMatrix[mat]

(**** </CliffordUnitary> ****)


RandomCliffordUnitary::usage = "RandomCliffordUnitary[n] returns ..."

RandomCliffordUnitary[n_Integer, spec___] :=
  CliffordUnitary[RandomFullGottesmanMatrix @ n, spec]


(* SEE ALSO: Sang et at. (2021) and Weinstein et al. (2022) *)
CliffordLogarithmicNegativity[cs_CliffordState] := Module[
  {a},
  a
]


End[]

EndPackage[]
