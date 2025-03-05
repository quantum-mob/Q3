(* -*- mode:math -*- *)

BeginPackage["QuantumMob`Q3`", {"System`"}]

{ BasisEmbedding,
  BasisEmbeddingGate };

{ AmplitudeEmbedding,
  AmplitudeEmbeddingGate };

{ VertexEmbedding };

{ BlockEncoding };

{ QuantumGeometricTensor, FubiniStudyTensor };

Begin["`Private`"]

(**** <BasisEmbedding> ****)

BasisEmbedding::usage = "BasisEmbedding[data, {s1,s2,\[Ellipsis]}] returns computational basis states encoding data."

BasisEmbedding[vv:{__?BinaryQ}, ss:{__?QubitQ}] := 
  Ket[ss -> PadRight[vv, Length @ ss]]

BasisEmbedding[ss:{__?QubitQ}][vv:{__?BinaryQ}] := 
  BasisEmbedding[vv, ss]


BasisEmbeddingGate::usage = "BasisEmbeddingGate[data, {s1,s2,\[Ellipsis]}] represents the gate sequence implementing the basis embedding of data."

BasisEmbeddingGate::len = "The lengths of `` and `` must be the same."

BasisEmbeddingGate[vv:{__?BinaryQ}, ss:{__?QubitQ}] :=
  BasisEmbeddingGate[vv, FlavorCap @ ss] /;
  Not[FlavorCapQ @ ss]

BasisEmbeddingGate[vv:{__?BinaryQ}, ss:{__?QubitQ}] := (
  Message[BasisEmbeddingGate::len, vv, ss];
  BasisEmbeddingGate[PadRight[vv, Length @ ss], ss]
 ) /; Length[vv] != Length[ss]

BasisEmbeddingGate[vv:{__?BinaryQ}, ss:{__?QubitQ}] :=
  Multiply @@ MapThrough[ss, vv]
    
(**** </BasisEmbedding> ****)


(**** <AmplitudeEmbedding> ****)
(* SEE: Schuld and Pertruccione (2018), Mottonen et al. (2005) *)

AmplitudeEmbedding::usage = "AmplitudeEmbedding[data, {s1,s2,\[Ellipsis]}] returns a quantum state the amplitudes of which encode data on qubits s1, s2, \[Ellipsis]."

AmplitudeEmbedding[in_?VectorQ, ss:{__?QubitQ}] :=
  Basis[ss] . PadRight[in, Power[2, Length @ ss]]


AmplitudeEmbeddingGate::usage = "AmplitudeEmbedding[data, {s1,s2,\[Ellipsis]}] represents the gate that implement the amplitude embedding of data into a quantum state."

AmplitudeEmbeddingGate::negative = "Some elements of `` is not real non-negative."

AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  AmplitudeEmbeddingGate[in, FlavorCap @ ss] /;
  Not[FlavorCapQ @ ss]


AmplitudeEmbeddingGate /:
Matrix[AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}], rest___] :=
  Dot @@ Matrix[{ExpandAll @ AmplitudeEmbeddingGate[in, ss]}, rest]


AmplitudeEmbeddingGate /:
Elaborate @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  Elaborate @ ExpressionFor[Matrix[AmplitudeEmbeddingGate[in, ss], ss], ss]


AmplitudeEmbeddingGate /:
ExpandAll @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] :=
  Apply[QuantumCircuit, Expand @ Expand @ AmplitudeEmbeddingGate[in, ss]]


AmplitudeEmbeddingGate /:
Expand @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := Module[
  { yy = theAmplitudeEmbeddingY[in, Length @ ss],
    op, cc },
  cc = Table[Drop[ss, -k], {k, Length @ ss}];
  QuantumCircuit @@ Reverse @ Flatten @ MapThread[
    UniformlyControlledRotation,
    { cc, yy, Through[Reverse[ss][2]] }
   ]
 ] /; AllTrue[in, NonNegative]

AmplitudeEmbeddingGate /:
Expand @ AmplitudeEmbeddingGate[in_?VectorQ, ss:{__?QubitQ}] := Module[
  { yy = theAmplitudeEmbeddingY[in, Length @ ss],
    zz = theAmplitudeEmbeddingZ[in, Length @ ss],
    op, cc },
  cc = Table[Drop[ss, -k], {k, Length @ ss}];
  QuantumCircuit @@ Reverse @ Flatten @ {
    MapThread[UniformlyControlledRotation, {cc, zz, Through[Reverse[ss][3]]}],
    MapThread[UniformlyControlledRotation, {cc, yy, Through[Reverse[ss][2]]}]
   }
 ]

theAmplitudeEmbeddingY[in_?VectorQ, n_Integer] := Module[
  { dd, nn, ph },
  dd = PadRight[in, Power[2, n]];
  dd = Table[Partition[dd, Power[2, k]], {k, n}];
  nn = Map[Drop[#, Length[#]/2]&, dd, {2}];
  dd = Map[Norm, dd, {2}];
  nn = Map[Norm, nn, {2}];
  2 * ArcSin @ PseudoDivide[nn, dd]
 ]

theAmplitudeEmbeddingZ[in_?VectorQ, n_Integer] := Module[
  { dd, nn, ph },
  dd = Arg @ PadRight[in, Power[2, n]];
  dd = Map[Total, Table[Partition[dd, Power[2, k-1]], {k, n}], {2}];
  dd = Partition[#, 2]& /@ dd;
  -Map[Apply[Subtract], dd, {2}] / Power[2, Range[n]-1]
 ]


AmplitudeEmbeddingGate /:
Multiply[ pre___,
  op:AmplitudeEmbeddingGate[_?VectorQ, {__?QubitQ}, ___?OptionQ],
  in_Ket ] := With[
    { gg = {ExpandAll @ op} },
    Multiply[pre, Fold[Multiply[#2, #1]&, in, gg]]
   ]

Multiply[ pre___,
  op:AmplitudeEmbeddingGate[{__?QubitQ}, _, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
(* NOTE: DO NOT put "AmplitudeEmbeddingGate /:". Otherwise, the above rule with
   AmplitudeEmbeddingGate[...]**Ket[] is overridden. *)


AmplitudeEmbeddingGate /:
ParseGate[
  AmplitudeEmbeddingGate[_?VectorQ, ss:{__?QubitQ}, opts___?OptionQ],
  more___?OptionQ ] :=
  Gate[ss, "TargetShape" -> "CircleDot", opts, more]

(**** </AmplitudeEmbedding> ****)

(**** <VertexEmbedding> ****)

VertexEmbedding::usage = ""

VertexEmbedding[g_Graph, s_?QubitQ] :=
 VertexEmbedding[g, FlavorCap @ s] /; Not[FlavorCapQ @ s]

VertexEmbedding[g_Graph, s_?QubitQ] :=
  VertexEmbedding[g, s[Range @ Length @ VertexList @ g, $]]

VertexEmbedding[g_Graph, ss:{__?QubitQ}] :=
  VertexEmbedding[g, FlavorCap @ ss] /;
  Not[FlavorCapQ @ ss]

VertexEmbedding[g_Graph, ss:{__?QubitQ}] :=
  VertexReplace[g, Thread[VertexList[g] -> ss]]

(**** </VertexEmbedding> ****)


(**** <BlockEncoding> ****)

BlockEncoding::usage = "BlockEncoding[mat, {s1,s2,\[Ellipsis]}, {a1,a2,\[Ellipsis]}] represents the block encoding of matrix mat, which representing an operator on the system register {s1,s2,\[Ellipsis]}, using ancilla register {a1,a2,\[Ellipsis]}."

BlockEncoding /:
MakeBoxes[op:BlockEncoding[mat_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, ___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    BlockEncoding, vec, None,
    { BoxForm`SummaryItem @ {"System Register: ", ss},
      BoxForm`SummaryItem @ {"Ancilla Register: ", aa}
    },
    { BoxForm`SummaryItem @ {"Matrix: ", MatrixForm @ mat[[;;UpTo[4], ;;UpTo[4]]]}
    },
    fmt,
    "Interpretable" -> Automatic
  ]


BlockEncoding[mat_, ss:{__?QubitQ}, a_?QubitQ, opts___?OptionQ] :=
  BlockEncoding[mat, ss, a @ {$}, opts]

BlockEncoding[mat_, s_?QubitQ, aa:{__?QubitQ}, opts___?OptionQ] :=
  BlockEncoding[mat, s @ {$}, aa, opts]

BlockEncoding[mat_, s_?QubitQ, a_?QubitQ, opts___?OptionQ] :=
  BlockEncoding[mat, s @ {$}, a @ {$}, opts]

BlockEncoding[mat_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, opts___?OptionQ] :=
  BlockEncoding[mat, FlavorCap @ ss, FlavorCap @ aa, opts] /;
  Not @ FlavorCapQ @ Join[ss, aa]


BlockEncoding /:
ExpandAll[enc:BlockEncoding[_?MatrixQ, {__?QubitQ}, {__?QubitQ}, ___?OptionQ]] :=
  Expand[Expand @ enc]

BlockEncoding /:
Expand @ BlockEncoding[mat_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, opts___?OptionQ] := Module[
  { mint = {"V", "\[CapitalOmega]", "W"},
    text, uu, dd, vv },
  {uu, dd, vv} = SingularValueDecomposition[mat];
  dd = Diagonal[dd];
  dd = dd * (Last[aa][3]) + Sqrt[1-dd^2] * (Last[aa][1]);
  uu = ExpressionFor[uu, ss];
  vv = ExpressionFor[Topple @ vv, ss];

  (* Handle the "Label" option. *)
  text = OptionValue[ Gate,
    Append[{opts}, "Label" -> {"M", mint}],
    "Label"
  ];
  If[ ListQ[text], 
    If[Length[text] > 1, text = Last[text], text = mint],
    text = mint
  ];
  If[Not[ListQ[text] && Length[text] >= 3], text = mint];

  QuantumCircuit[
    {vv, "Label" -> Superscript[text[[3]], "\[Dagger]"]},
    UniformlyControlledGate[ss, dd, "Label" -> text[[2]], opts],
    {uu, "Label" -> text[[1]]},
    "Visible" -> aa
  ]
]


BlockEncoding /:
Matrix @ BlockEncoding[mat_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, ___?OptionQ] := Module[
  { uu, dd, vv, mm },
  {uu, dd, vv} = SingularValueDecomposition[mat];
  mm = DiagonalMatrix @ Sqrt[1 - Diagonal[dd]^2];
  dd = ArrayFlatten @ {
    {dd,  mm},
    {mm, -dd}
  };
  mm = CirclePlus[uu, uu] . dd . CirclePlus[Topple @ vv, Topple @ vv];
  CircleTimes[One @ Power[2, Length[aa]-1], mm]
]

BlockEncoding /:
Matrix[op:BlockEncoding[mat_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, ___?OptionQ], tt:{__?SpeciesQ}] :=
  MatrixEmbed[Matrix[op], Join[aa, ss], tt]

BlockEncoding /:
Elaborate[op:BlockEncoding[_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, ___?OptionQ]] :=
  ExpressionFor[Matrix[op], Join[aa, ss]]


BlockEncoding /:
ParseGate[ 
  BlockEncoding[_?MatrixQ, ss:{__?QubitQ}, aa:{__?QubitQ}, opts___?OptionQ], 
  more___?OptionQ
] := 
  Module[
    { txt, new },
    txt = OptionValue[Gate, Append[{opts}, "Label" -> "M"], "Label"];
    If[ListQ[txt], txt = First[txt]];
    new = FilterRules[
      { "Label" -> txt,
        more, opts,
        "ControlShape" -> "Oval",
        "ControlLabel" -> "enc",
        "ControlLabelAngle" -> Pi/2
      },
      Options @ Gate
    ];
    Gate[aa, ss, new]
  ]

(**** </BlockEncoding> ****)


(**** <QuantumGeometricTensor> ****)

QuantumGeometricTensor::usage = "QuantumGeometricTensor[vec, {x1, x2, \[Ellipsis]}] returns the quantum geometric tensor for the state vector vec parametrized with parameters x1, x2, \[Ellipsis]."

QuantumGeometricTensor[vec_?VectorQ, var:{(_Symbol|_Symbol[___])..}] := Module[
  { drv = Map[D[#, {var}]&, vec],
    bry },
  bry = Dot[Conjugate @ vec, drv];
  drv = Dot[ConjugateTranspose @ drv, drv];
  drv - KroneckerProduct[Conjugate @ bry, bry]
]
(* NOTE: vec is supposed to be normalized. *)

QuantumGeometricTensor[vec_?VectorQ, var:{(_Symbol|_Symbol[___])..}, val_?VectorQ] :=
Module[
  { drv = Map[D[#, {var}]&, vec],
    bry },
  bry = Dot[Conjugate @ vec, drv] /. Thread[var -> val];
  drv = drv /. Thread[var -> val];
  drv = Dot[ConjugateTranspose @ drv, drv];
  drv - KroneckerProduct[Conjugate @ bry, bry]  
]
(* NOTE: vec is supposed to be normalized. *)

(**** </QuantumGeometricTensor> ****)


(**** <FubiniStudyTensor> ****)

FubiniStudyTensor::usage = "FubiniStudyTensor[vec, {x1, x2, \[Ellipsis]}] returns the Fubini-Study metric tensor for the state vector vec parametrized with parameters x1, x2, \[Ellipsis]."

(* exact calculation *)

FubiniStudyTensor[vec_?VectorQ, var:{(_Symbol|_Symbol[___])..}] := 
  Re @ QuantumGeometricTensor[vec, var]

FubiniStudyTensor[vec_?VectorQ, var:{(_Symbol|_Symbol[___])..}, val_?VectorQ] :=
  Re @ QuantumGeometricTensor[vec, var, val]


(* block-diagonal approximation *)

FubiniStudyTensor[gnr_?ArrayQ][vec:(_?VectorQ|_?MatrixQ)] :=
  FubiniStudyTensor[gnr, vec] /; ArrayQ[gnr, 3]

FubiniStudyTensor[gnr_?ArrayQ, vec_?VectorQ] := Module[
  { gg, hh },
  gg = Dot[
    Dot[Conjugate @ vec, Transpose @ gnr],
    Transpose @ Dot[gnr, vec]
  ];
  hh = Map[Conjugate[vec].#.vec&, gnr];
  hh = KroneckerProduct[hh, hh];
  SparseArray[gg - hh]
] /; ArrayQ[gnr, 3, NumericQ]
(* NOTE: gnr is supposed to be a list of Hermitian matrices. *)

FubiniStudyTensor[gnr_?ArrayQ, mat_?MatrixQ] :=
  BlockDiagonalMatrix[
    FubiniStudyTensor[gnr] /@ mat,
    TargetStructure -> "Sparse"
  ] /; ArrayQ[gnr, 3]
(* NOTE: mat is supposed to be a list of normalized vectors. *)


FubiniStudyTensor::len = "The list of generators `` and the list of state vectors `` have different lengths."

FubiniStudyTensor[gnr:{__?(ArrayQ[#,3]&)}, mat_?MatrixQ] :=
  BlockDiagonalMatrix[
    MapThread[FubiniStudyTensor, {gnr, mat}],
    TargetStructure -> "Sparse"
  ] /; If[Length[gnr] == Length[mat], True,
    Message[FubiniStudyTensor::len, gnr, mat]; False
  ]
(* NOTE: gnr is supposed to be a list of Hermitian matrices. *)
(* NOTE: mat is supposed to be a list of normalized vectors. *)

(**** </FubiniStudyTensor> ****)

End[]

EndPackage[]
