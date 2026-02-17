(* -*- mode: math; -*- *)
BeginPackage["QuantumMob`Q3`", {"System`"}]

{ Unfold, UnfoldAll };

{ Qubit, QubitQ, Qubits, QubitCount };

{ PauliForm };

{ QubitAdd, QubitAddZ };

{ Rotation, EulerRotation, Phase };

{ ControlledGate, CNOT, CX = CNOT, CZ, CY, SWAP, iSWAP,
  Toffoli, Fredkin, Deutsch };

{ ControlledPower, ActOn };

{ UniformlyControlledRotation,
  UniformlyControlledGate };

{ Measurement, Measurements, MeasurementFunction,
  MeasurementOdds, Readout, $MeasurementOut = <||> };

{ Projector };

{ Oracle };

{ QFT, QBR, QCR };

{ ModMultiply, ModAdd, ModExp = ModPower };

{ Matchgate };

{ ProductState, BellState, GHZState, SmolinState,
  DickeState };

{ GraphState, GraphStateBasis };

(* Qudit *)

{ Qudit, QuditQ, Qudits };

{ TheQuditKet };

(**** <preload> ****)

{ Gate }; (* QuantumCircuit *)

(**** </preload> ****)


Begin["`Private`"]

$symb = Unprotect[CircleTimes, Dagger, Ket, Bra, Missing]

AddElaborationPatterns[
  _QFT, _QBR, _Oracle,
  _ControlledGate, _CZ, _CX, _CNOT, _SWAP, _iSWAP,
  _Toffoli, _Fredkin, _Deutsch, _Oracle,
  _Phase, _Rotation, _EulerRotation,
  _Projector, _ProductState,
  _ControlledPower,
  _ExchangeGate,
  _Matchgate
]

AddElaborationPatterns[
  G_?QubitQ[j___, 0] -> 1,
  G_?QubitQ[j___, 4] -> G[j, Raising],
  G_?QubitQ[j___, 5] -> G[j, Lowering],
  G_?QubitQ[j___, 6] -> G[j, Hadamard],
  G_?QubitQ[j___, 7] -> G[j, Quadrant],
  G_?QubitQ[j___, 8] -> G[j, Octant],
  G_?QubitQ[j___, 9] -> G[j, Hexadecant],
  G_?QubitQ[j___, 10] -> (1 + G[j,3]) / 2,
  G_?QubitQ[j___, 11] -> (1 - G[j,3]) / 2,
  G_?QubitQ[j___, n_Integer?Negative] :> Dagger[Elaborate @ G[j, -n]],
  G_?QubitQ[j___, C[n_Integer]] :>
    Elaborate @ Phase[2*Pi*Power[2,-n], G[j,3]],
  G_?QubitQ[j___, -C[n_Integer]] :>
    Elaborate @ Phase[-2*Pi*Power[2,-n], G[j,3]],
  G_?QuditQ[j___, 0 -> 0] :> 1 - Total @ Rest @ G[j, Diagonal],
  OTimes -> CircleTimes,
  OSlash -> CircleTimes
]


(**** <Qubit> ****)

Qubit::usage = "Qubit denotes a quantum two-level system or \"quantum bit\".\nLet[Qubit, S, T, ...] or Let[Qubit, {S, T,...}] declares that the symbols S, T, ... are dedicated to represent qubits and quantum gates operating on them. For example, S[j,..., $] represents the qubit located at the physical site specified by the indices j, .... On the other hand, S[j, ..., k] represents the quantum gate operating on the qubit S[j,..., $].\nS[..., 0] represents the identity operator.\nS[..., 1], S[..., 2] and S[..., 3] means the Pauli-X, Pauli-Y and Pauli-Z gates, respectively.\nS[..., 4] and S[..., 5] represent the raising and lowering operators, respectively.\nS[..., 6], S[..., 7], S[..., 8] represent the Hadamard, Quadrant (Pi/4) and Octant (Pi/8) gate, resepctively.\nS[..., 10] represents the projector into Ket[0].\nS[..., 11] represents the projector into Ket[1].\nS[..., (Raising|Lowering|Hadamard|Quadrant|Octant)] are equivalent to S[..., (4|5|6|7|8)], respectively, but expanded immediately in terms of S[..., 1] (Pauli-X), S[..., 2] (Y), and S[..., 3] (Z).\nS[..., $] represents the qubit."

Qubit /:
Let[Qubit, ss:{__Symbol}, ___?OptionQ] := (
  Let[NonCommutative, ss];
  Scan[setQubit, ss];
)

setQubit[x_Symbol] := (
  MultiplyKind[x] ^= Qubit;
  MultiplyKind[x[___]] ^= Qubit;
  
  Dimension[x] ^= 2;
  Dimension[x[___]] ^= 2;

  LogicalValues[x] ^= {0, 1};
  LogicalValues[x[___]] ^= {0, 1};

  QubitQ[x] ^= True;
  QubitQ[x[___]] ^= True;

  AgentQ[x] ^= True;
  AgentQ[x[___]] ^= True;

  x/: Dagger @ x[j___, k:(0|1|2|3|6|10|11)] = x[j, k];
  
  x/: Dagger @ x[j___, 4] = x[j, 5];
  x/: Dagger @ x[j___, 5] = x[j, 4];
  
  x/: Dagger @ x[j___, 7] = x[j, -7];
  x/: Dagger @ x[j___, 8] = x[j, -8];
  x/: Dagger @ x[j___, 9] = x[j, -9];
  x/: Dagger @ x[j___, -7] = x[j, 7];
  x/: Dagger @ x[j___, -8] = x[j, 8];
  x/: Dagger @ x[j___, -9] = x[j, 9];
  
  x/: Dagger @ x[j___,  C[k_Integer]] = x[j, -C[k]];
  x/: Dagger @ x[j___, -C[k_Integer]] = x[j,  C[k]];

  x/: Inverse[ x[j___, k_Integer] ] := x[j, -k];
  x/: Inverse[ x[j___, C[k_Integer] ] ] := x[j, -C[k]];

  (* for time reversal *)
  x/: Conjugate[ x[j___, k:(0|1|3|4|5|6)] ] := x[j, k];
  x/: Conjugate[ x[j___, 2] ] := -x[j, 2];
  x/: Conjugate[ x[j___, 7] ] := x[j, -7];
  x/: Conjugate[ x[j___, 8] ] := x[j, -8];
  x/: Conjugate[ x[j___, 9] ] := x[j, -9];
  x/: Conjugate[ x[j___, C[k_Integer] ] ] := x[j, -C[k]];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___, Raising] = (x[j,1] + I x[j,2]) / 2;
  x[j___, Lowering] = (x[j,1] - I x[j,2]) / 2;
  
  x[j___, Hadamard] = (x[j,1] + x[j,3]) / Sqrt[2];
  x[j___, Quadrant] = (1+I)/2 + x[j,3]*(1-I)/2;
  x[j___, Octant]   = (1+Exp[I*Pi/4])/2 + x[j,3]*(1-Exp[I*Pi/4])/2;
  x[j___, Hexadecant] = (1+Exp[I*Pi/8])/2 + x[j,3]*(1-Exp[I*Pi/8])/2;

  x[j___, -1] = x[j, 1];
  x[j___, -2] = x[j, 2];
  x[j___, -3] = x[j, 3];
  x[j___, -4] = x[j, 5];
  x[j___, -5] = x[j, 4];
  x[j___, -6] = x[j, 6];

  x[j___, C[n_Integer?NonPositive]] = x[j, 0];
  
  (* x[j___, C[1]] = x[j, 3]; *)
  (* x[j___, C[2]] = x[j, 7]; *)
  (* x[j___, C[3]] = x[j, 8]; *)
  (* x[j___, C[4]] = x[j, 9]; *)

  (* x[j___, 10] := (1 + x[j,3]) / 2; *)
  (* x[j___, 11] := (1 - x[j,3]) / 2; *)
  (* NOTE: It interferes, say, with Ket[] encountered with short-cut inputs. *)

  x[j___, 0 -> 0] = x[j, 10];
  x[j___, 1 -> 1] = x[j, 11];
  x[j___, 1 -> 0] = x[j, 4];
  x[j___, 0 -> 1] = x[j, 5];
  
  x[j___, All]  := Flatten @ x[j, {1, 2, 3}];
  x[j___, Full] := Flatten @ x[j, {0, 1, 2, 3}];
  
  Format @ x[j___, $] :=
    Interpretation[SpeciesBox[x, {j}, {}], x[j, $]];

  Format[ x[j___, n_Integer?Negative] ] :=
    Interpretation[Superscript[x[j, -n], "\[Dagger]"], x[j, n]];

  Format[ x[j___, C[n_Integer?Positive]] ] := Interpretation[
    SpeciesBox[x, {j}, {2 Pi / HoldForm[Power[2, n]]}],
    x[j, C[n]]
  ];
  
  Format[ x[j___, -C[n_Integer?Positive]] ] := Interpretation[
    SpeciesBox[x, {j}, {-2 Pi / HoldForm[Power[2, n]]}],
    x[j, -C[n]]
  ];
  
  Format @ x[j___, 0] := Interpretation[SpeciesBox[x, {j}, {0}], x[j, 0]];
  Format @ x[j___, 1] := Interpretation[SpeciesBox[x, {j}, {"X"}], x[j, 1]];
  Format @ x[j___, 2] := Interpretation[SpeciesBox[x, {j}, {"Y"}], x[j, 2]];
  Format @ x[j___, 3] := Interpretation[SpeciesBox[x, {j}, {"Z"}], x[j, 3]];
  Format @ x[j___, 4] := Interpretation[SpeciesBox[x, {j}, {"+"}], x[j, 4]];
  Format @ x[j___, 5] := Interpretation[SpeciesBox[x, {j}, {"-"}], x[j, 5]];
  Format @ x[j___, 6] := Interpretation[SpeciesBox[x, {j}, {"H"}], x[j, 6]];
  Format @ x[j___, 7] := Interpretation[SpeciesBox[x, {j}, {"S"}], x[j, 7]];
  Format @ x[j___, 8] := Interpretation[SpeciesBox[x, {j}, {"T"}], x[j, 8]];
  Format @ x[j___, 9] := Interpretation[SpeciesBox[x, {j}, {"F"}], x[j, 9]];
  
  Format @ x[j___, 10] := Interpretation[
    Subscript[Row @ {"(", Ket[0], Bra[0], ")"}, x[j, $]],
    x[j, 10]
   ];
  Format @ x[j___, 11] := Interpretation[
    Subscript[Row @ {"(", Ket[1], Bra[1], ")"}, x[j, $]],
    x[j, 11]
  ];
)

Missing["KeyAbsent", _Symbol?QubitQ[___, $]] = 0


(* Override the default definition of Format[Dagger[...]]
   NOTE: This is potentially dangerous because Fock also overides it. *)

Format @ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] =. ;

Format @ HoldPattern @ Dagger[ c_Symbol?QubitQ[j___, 7] ] :=
  Interpretation[
    SpeciesBox[c, {j}, {"S\[Dagger]"}],
    Dagger @ c[j, 7]
   ]

Format @ HoldPattern @ Dagger[ c_Symbol?QubitQ[j___, 8] ] :=
  Interpretation[
    SpeciesBox[c, {j}, {"T\[Dagger]"}],
    Dagger @ c[j, 8]
   ]

Format @ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] :=
  Interpretation[
    SpeciesBox[c, {j}, {"\[Dagger]"} ],
    Dagger @ c[j]
   ]

Format @ HoldPattern @ Dagger[ c_Symbol?SpeciesQ ] :=
  Interpretation[
    SpeciesBox[c, {}, {"\[Dagger]"} ],
    Dagger @ c
   ]

(**** </Qubit> ****)

QubitQ::usage = "QubitQ[S] or QubitQ[S[...]] returns True if S is declared as a Qubit through Let."

AddGarnerPatterns[_?QubitQ]

QubitQ[_] = False


Qubits::usage = "Qubits[expr] gives the list of all qubits (quantum bits) appearing in expr."

Qubits[expr_] := Select[Agents @ expr, QubitQ]


(**** <QubitCount> ****)

QubitCount::usage = "QubitCount[obj] returns the number of qubits involved in object obj."

QubitCount[ss:{__?SpeciesQ}] := Length @ Select[ss, QubitQ]

QubitCount[_] = Indeterminate

(**** </QubitCount> ****)


(**** <Multiply> ****)

(* Speical Rules: Involving identity *)

HoldPattern @ Multiply[pre___, _?QubitQ[___, 0], post___] := 
  Multiply[pre, post]

(* Multiply operators on Ket[] *)

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,4], Ket[b_Association], post___ ] :=
  Switch[ b @ a[j, $],
    0, 0,
    1, Ket @ KeySort @ Append[b, a[j,$] -> 0],
    _?BinaryQ, Garner[(a[j, 1] + I*a[j, 2]) ** Ket[b] / 2],
    _, Ket[b]
   ]

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,5], Ket[b_Association], post___ ] :=
  Switch[ b @ a[j, $],
    1, 0,
    0, Ket @ KeySort @ Append[b, a[j,$] -> 1],
    _?BinaryQ, Garner[(a[j, 1] - I*a[j, 2]) ** Ket[b] / 2],
    _, Ket[b]
   ]

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,1], Ket[b_Association], post___ ] :=
  With[
    { m = Mod[1 + b[a[j,$]], 2] },
    Multiply[
      pre,
      Ket @ KeySort @ Append[b, a[j,$]->m],
      post
     ]
   ]

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,2], Ket[b_Association], post___ ] :=
  With[
    { m = Mod[1 + b[a[j,$]], 2] },
    (2 m - 1) I Multiply[
      pre,
      Ket @ KeySort @ Append[b, a[j,$]->m],
      post
     ]
  ]

HoldPattern @
  Multiply[pre___, a_?QubitQ[j___,3], Ket[b_Association], post___] :=
    (1 - 2*b[a[j,$]]) * Multiply[pre, Ket @ b, post]


HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,6], Ket[b_Association], post___ ] :=
  Multiply[pre, a[j,Hadamard], Ket[b], post]


HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,7], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ I * (Pi/2) * b[a[j,$]] ] (* Quadrant *)

HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,8], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ I * (Pi/4) * b[a[j,$]] ] (* Octant *)

HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,9], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ I * (Pi/8) * b[a[j,$]] ] (* Hexadecant *)


HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,-7], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ -I * (Pi/2) * b[a[j,$]] ] (* Quadrant *)

HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,-8], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ -I * (Pi/4) * b[a[j,$]] ] (* Octant *)

HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,-9], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ -I * (Pi/8) * b[a[j,$]] ] (* Hexadecant *)


HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,C[n_Integer]], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ I * 2*Pi*Power[2, -n] * b[a[j,$]] ]

HoldPattern @ Multiply[ pre___, a_?QubitQ[j___,-C[n_Integer]], b:Ket[_Association], post___ ] :=
  Multiply[pre, b, post] * Exp[ -I * 2*Pi*Power[2, -n] * b[a[j,$]] ]


HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,10], Ket[b_Association], post___ ] :=
    Multiply[pre, Ket[b], post] /; b @ a[j, $] == 0

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,10], Ket[b_Association], post___ ] :=
    0 /; b @ a[j, $] == 1

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,11], Ket[b_Association], post___ ] :=
    Multiply[pre, Ket[b], post] /; b @ a[j, $] == 1

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,11], Ket[b_Association], post___ ] :=
    0 /; b @ a[j, $] == 0


HoldPattern @ Multiply[ pre___, op_?QubitQ, vec_Ket, post___] :=
  Multiply[pre, Elaborate @ op, vec, post]


(* Gates on Bra *)

HoldPattern @ Multiply[ x___, Bra[v_Association], G_?QubitQ, y___ ] :=
  Multiply[ x, Dagger[Dagger[G]**Ket[v]], y ]

HoldPattern @ Multiply[ x___, Bra[v_Association, s_List], G_?QubitQ, y___ ] :=
  Multiply[ x, Dagger[Dagger[G]**Ket[v,s]], y ]


(* Special rules for Pauli operators *)
 
HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,k:(1|2|3|6)], x_Symbol?QubitQ[j___,k:(1|2|3|6)],
  post___ ] := Multiply[pre, post]

HoldPattern @ Multiply[ ___,
  x_Symbol?QubitQ[j___,k:(4|5)], x_Symbol?QubitQ[j___,k:(4|5)],
  ___ ] := 0

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,7], x_Symbol?QubitQ[j___,7], post___ ] :=
  Multiply[pre, x[j,3], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,8], x_Symbol?QubitQ[j___,8], post___ ] :=
  Multiply[pre, x[j,7], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,9], x_Symbol?QubitQ[j___,9], post___ ] :=
    Multiply[pre, x[j,8], post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,-7], x_Symbol?QubitQ[j___,-7], post___ ] :=
  Multiply[pre, x[j,3], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,-8], x_Symbol?QubitQ[j___,-8], post___ ] :=
  Multiply[pre, x[j,-7], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,-9], x_Symbol?QubitQ[j___,-9], post___ ] :=
    Multiply[pre, x[j,-8], post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,C[n_Integer]], x_Symbol?QubitQ[j___,C[n_Integer]], post___ ] :=
    Multiply[pre, x[j,C[n-1]], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,-C[n_Integer]], x_Symbol?QubitQ[j___,-C[n_Integer]], post___ ] :=
    Multiply[pre, x[j,-C[n-1]], post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,2], post___ ] :=
    Multiply[pre, I x[j,3], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,3], post___ ] :=
    Multiply[pre, I x[j,1], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,1], post___ ] :=
    Multiply[pre, I x[j,2], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,1], post___ ] :=
    Multiply[pre, -I x[j,3], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,2], post___ ] :=
    Multiply[pre, -I x[j,1], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,3], post___ ] :=
    Multiply[pre, -I x[j,2], post]
(* Again, the last three definitions can be deduced from the commutation
   relations below, but explicit definition makes the evaluation much
   faster. *)


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,4], post___ ] :=
    Multiply[pre, 1/2 - x[j,3]/2, post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,1], post___ ] :=
    Multiply[pre, 1/2 + x[j,3]/2, post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,5], post___ ] :=
    Multiply[pre, 1/2 + x[j,3]/2, post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,1], post___ ] :=
    Multiply[pre, 1/2 - x[j,3]/2, post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,4], post___ ] :=
    Multiply[pre, I/2 - x[j,3]*I/2, post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,2], post___ ] :=
    Multiply[pre, I/2 + x[j,3]*I/2, post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,5], post___ ] :=
    Multiply[pre, -I/2 - x[j,3]*I/2, post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,2], post___ ] :=
    Multiply[pre, -I/2 + x[j,3]*I/2, post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,4], post___ ] :=
    Multiply[pre, +x[j,4], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,3], post___ ] :=
    Multiply[pre, -x[j,4], post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,5], post___ ] :=
    Multiply[pre, -x[j,5], post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,3], post___ ] :=
    Multiply[pre, +x[j,5], post]


HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,5], post___ ] :=
    Multiply[pre, 1/2 + x[j,3]/2, post]

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,4], post___ ] :=
    Multiply[pre, 1/2 - x[j,3]/2, post]


(* General Rules *)

HoldPattern @ Multiply[ 
  pre___,
  x_Symbol?QubitQ[j___,m_], x_Symbol?QubitQ[j___,n_], 
  post___ 
] :=
  Multiply[pre, post] /; m + n == 0

HoldPattern @ Multiply[ 
  pre___,
  x_Symbol?QubitQ[j___,m_], x_Symbol?QubitQ[j___,n_], 
  post___ 
] :=
  Multiply[pre, Elaborate @ x[j,m], Elaborate @ x[j,n], post]

(* 2023-01-26 17:54 This is very dangerous: For example, S[1,3]**T[1,1] hits
   the $IterationLimit. *)
(*
HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[i___, a_], y_Symbol?QubitQ[j___, b_],
  post___] :=
  Multiply[pre, Elaborate @ x[i, a], Elaborate @ y[j, b], post]
 *)

HoldPattern @ Multiply[pre___, x_?QubitQ, y_?QubitQ, post___] :=
  Multiply[pre, y, x, post] /;
  Not @ OrderedQ @ {x, y}

(**** </Multiply> ****)


(* MultiplyDegree for operators *)
MultiplyDegree[_?QubitQ] = 1


(* Base: See Abel *)

Base[ S_?QubitQ[j___, _] ] := S[j]
(* For Qubits, the final Flavor index is special. *)

(* FlavorCap: See Abel *)

FlavorCap[S_?QubitQ] := S[$]

(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?QubitQ] := S[$]

FlavorMute[S_Symbol?QubitQ[j___, _]] := S[j, $]

FlavorMute[S_Symbol?QubitQ[j___, _] -> m_] := S[j, $] -> m


$RaisingLoweringRules = Join[ $RaisingLoweringRules,
  { S_?QubitQ[j___,1] :> (S[j,4] + S[j,5]),
    S_?QubitQ[j___,2] :> (S[j,4] - S[j,5]) / I }
]


(**** <Ket for Qubit> ****)

theKetTrim[Rule[_?QubitQ, 0]] = Nothing

KetVerify::qubit = "Invalid value `` for qubit ``."

theKetVerify[Rule[key_?QubitQ, val_]] := (
  Message[KetVerify::qubit, val, key];
  Rule[key, val]
) /; Not[BinaryQ @ val]
(* NOTE: The following definition would not allow to assign a symbolic value:
   KetVerify[ _?QubitQ, Except[0|1] ] = Nothing *)

(**** </Ket for Qubit> ****)


(**** <Basis for Qubit> ****)

Basis[ S_?QubitQ ] := Ket /@ Thread[FlavorCap[S] -> {0, 1}]

(**** </Basis for Qubit> ****)


(**** <PauliForm> ****)

singleQubitGateQ::usage = "singleQubitGateQ[op] returns True if operator op is an 'elementary' single-qubit gate; and False, otherwise."

(* SetAttributes[singleQubitGateQ, ReadProtected] *)

HoldPattern @ singleQubitGateQ @ Dagger[_?QubitQ] = True

singleQubitGateQ[_?QubitQ] = True

singleQubitGateQ[Phase[_, _?QubitQ, ___]] = True

singleQubitGateQ[Rotation[_, {_, _, _}, _?QubitQ, ___]] = True

singleQubitGateQ[_] = False


thePauliForm::usage = "thePauliForm[op] or thePauliForm[Dagger[op]] rewrites op in a more conventional form, where the Pauli operators are denoted by I, X, Y, Z, H, S, and T."

HoldPattern @ thePauliForm @ Pauli[{k_Integer?Negative}] :=
  Superscript[thePauliForm @ Pauli[{-k}], "\[Dagger]"]

thePauliForm @ Pauli[{k_Integer}] := ReplaceAll[ k,
  { 0 -> "I", 1 -> "X", 2 -> "Y", 3 -> "Z",
    4 -> Superscript["X", "+"],
    5 -> Superscript["X", "-"],
    6 -> "H", 7 -> "S", 8 -> "T", 9 -> "F",
    10 -> Row @ {Ket @ {0}, Bra @ {0}},
    11 -> Row @ {Ket @ {1}, Bra @ {1}} }
 ]

thePauliForm @ Pauli[{-C[n_Integer]}] := Subsuperscript["Z", n, "\[Dagger]"]
  (* Superscript["Z", -2*Pi / HoldForm[Power[2, n]]] *)

thePauliForm @ Pauli[{+C[n_Integer]}] := Subscript["Z", n]
  (* Superscript["Z", +2*Pi / HoldForm[Power[2, n]]] *)

thePauliForm @ Pauli[{any_}] = Superscript["\[Sigma]", any]
(* NOTE: This is necessary to avoid infinite recursion Format[Paui[...]] may
   cause. *)

thePauliForm @ Pauli[kk_List] :=
  CircleTimes @@ Map[thePauliForm, Pauli /@ kk]

thePauliForm[_?QubitQ[___, k_]] := thePauliForm @ Pauli[{k}]

thePauliForm[Phase[phi_, S_?QubitQ, ___]] :=
  Superscript[thePauliForm @ S, phi]

thePauliForm[Rotation[phi_, v:{_, _, _}, S_?QubitQ, rest___]] :=
  DisplayForm @ RowBox @ { Exp,
    RowBox @ {"(", -I * (phi/2) * Dot[thePauliForm /@ S @ All, Normalize @ v], ")"}
  }

thePauliForm[op_?singleQubitGateQ, qq:{__?QubitQ}] := thePauliForm[{op}, qq]

thePauliForm[gg:{__?singleQubitGateQ}, qq:{__?QubitQ}] := Module[
  { kk },
  kk = GroupBy[gg, First @* Qubits, Row @* Map[thePauliForm]];
  kk = KeyReplace[kk, Normal @ PositionIndex @ FlavorCap @ qq];
  CircleTimes @@ ReplacePart[Table["I", Length @ qq], Normal @ kk]
]


PauliForm::usage = "PauliForm[expr] rewrites expr in a more conventional form, where the Pauli operators are denoted by I, X, Y, and Z."

PauliForm[z_?CommutativeQ, qq:{__?QubitQ}] :=
  Interpretation[z * CircleTimes @@ Table["I", Length @ qq], z]

HoldPattern @ PauliForm[op:Multiply[ss__?singleQubitGateQ], qq:{__?QubitQ}] :=
  Interpretation[thePauliForm[{ss}, qq], op]

PauliForm[op_?singleQubitGateQ, qq:{__?QubitQ}] :=
  Interpretation[thePauliForm[op, qq], op]

PauliForm[expr_Plus, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, expr]

PauliForm[expr_List, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, expr]

PauliForm[assc_Association, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, assc]

PauliForm[expr_, qq:{__?QubitQ}] := expr /. {
    HoldPattern[op:Multiply[__?singleQubitGateQ]] :> PauliForm[op, qq],
    HoldPattern[Multiply[op__]] :> Row[thePauliForm /@ {op}],
    op_Rotation :> thePauliForm[op],
    op_?singleQubitGateQ :> PauliForm[op, qq]
  }

PauliForm[expr_] := PauliForm[expr, Qubits @ expr] /; FreeQ[expr, _Pauli]


PauliForm[op_Pauli] := Interpretation[thePauliForm @ op, op]

PauliForm[assc_Association] := Map[PauliForm, assc]

PauliForm[expr_] := expr /. { op_Pauli :> PauliForm[op] }

(**** </PauliForm> ****)


(**** <Parity for Qubits> ****)

Parity[S_?QubitQ] := S[3]

ParityValue[v_Ket, a_?QubitQ] := 1 - 2*v[a]

ParityEvenQ[v_Ket, a_?QubitQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?QubitQ] := OddQ @ v @ a

(**** </Parity> ****)


(**** <Matrix for Qubits> ****)

TheMatrix[ _?QubitQ[___, +C[m_Integer?Positive]] ] :=
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[+I*2*Pi*Power[2, -m]]}, {2, 2}]

TheMatrix[ _?QubitQ[___, -C[m_Integer?Positive]] ] :=
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[-I*2*Pi*Power[2, -m]]}, {2, 2}]

TheMatrix[ _?QubitQ[___, m_] ] := ThePauli[m]

TheMatrix @ Ket @ Association[_?QubitQ -> s_] :=
  SparseArray @ TheKet[s]

(**** </Matrix> ****)


(**** <QubitAdd> ****)

QubitAddZ::usage = "QubitAddZ[S$1, S$2, ...] returns in an Association the irreducible basis of the total angular momentum S$1 + S$2 + ... invariant under the U(1) rotation around spin z-axis, regarding the qubits S$1, S$2, ... as 1/2 spins."

QubitAddZ::duplicate = "Duplicate angular momentum operators appear."


QubitAddZ[ ls:{(_?QubitQ|_Association)..} ] :=
  QubitAddZ @@ Map[QubitAddZ] @ ls

QubitAddZ[] := Association[ {0} -> {Ket[]} ]

QubitAddZ[irb_Association] := irb

QubitAddZ[a_?QubitQ] := Module[
  { aa = FlavorCap @ a,
    bs = Basis @ a },
  GroupBy[bs, (1/2-#[aa])&]
 ]

QubitAddZ[a___, b_?QubitQ, c___] := QubitAddZ[a, QubitAddZ[b], c]

QubitAddZ[irb_Association, irc_Association, ird__Association] :=
  QubitAddZ[ QubitAddZ[irb, irc], ird]

QubitAddZ[irb_Association, irc_Association] := Module[
  { kk = Flatten @ Outer[Plus, Keys[irb], Keys[irc]],
    vv = Map[Tuples] @ Tuples[{Values[irb], Values[irc]}],
    gb = Union @ Cases[Normal @ Values @ irb, _?QubitQ, Infinity],
    gc = Union @ Cases[Normal @ Values @ irc, _?QubitQ, Infinity],
    rr },
  If[ ContainsAny[gb, gc],
    Message[ QubitAddZ::duplicate ];
    Return[ irb ]
   ];

  vv = Apply[CircleTimes, vv, {2}];
  rr = Thread[kk -> vv];
  rr = Merge[rr, Catenate];
  Map[ReverseSort, rr]
 ]


QubitAdd::usage = "QubitAdd[S$1, S$2, ...] returns in an Association the irreducible basis of the total angular momentum S$1 + S$2 + ... that are invariant under arbitrary SU(2) rotations. Here, the qubits S$1, S$2, ... are regarded 1/2 spins."

QubitAdd::duplicate = "Duplicate angular momentum operators appear."

QubitAdd[ ls:{(_?QubitQ|_Association)..} ] :=
  QubitAdd @@ Map[QubitAdd] @ ls

QubitAdd[] := Association[ {0,0} -> {Ket[]} ]

QubitAdd[irb_Association] := irb

QubitAdd[a_?QubitQ] := Module[
  { aa = FlavorCap @ a,
    bs = Basis @ a },
  GroupBy[bs, { 1/2, (1/2 - #[aa]) }&]
 ]

QubitAdd[a___, b_?QubitQ, c___] := QubitAdd[a, QubitAdd[b], c]

QubitAdd[irb_Association, irc_Association, ird__Association] :=
  QubitAdd[ QubitAdd[irb, irc], ird]

QubitAdd[irb_Association, irc_Association] := Module[
  { S1 = Union @ Map[First] @ Keys[irb],
    S2 = Union @ Map[First] @ Keys[irc],
    SS,
    gb = Union @ Cases[Normal @ Values @ irb, _?QubitQ, Infinity],
    gc = Union @ Cases[Normal @ Values @ irc, _?QubitQ, Infinity],
    new },
  If[ ContainsAny[gb, gc],
    Message[ QubitAdd::duplicate ];
    Return[ irb ]
   ];
  SS = Flatten[
    Outer[Thread[{#1, #2, Range[Abs[#1 - #2], #1 + #2]}]&, S1, S2], 
    2];
  SS = Flatten[
    Map[Thread[{Sequence @@ #, Range[-Last@#, Last@#]}]&] @ SS,
    1];
  new = theQubitAdd[irb, irc, #]& /@ SS;
  Merge[new, Catenate]
 ]

theQubitAdd[irb_, irc_, {S1_, S2_, S_, Sz_}] := Module[
  { new, min, max },
  min = Max[-S1, Sz - S2, (Sz - (S1 + S2))/2];
  max = Min[S1, Sz + S2, (Sz + (S1 + S2))/2];
  new = Garner @ Sum[
    CircleTimes @@@ Tuples[{irb[{S1, m}], irc[{S2, Sz - m}]}]*
      ClebschGordan[{S1, m}, {S2, Sz - m}, {S, Sz}],
    {m, Range[min, max]}
   ];
  Association[ {S, Sz} -> new ]
 ]

(**** </QubitAdd> ****)


(**** <ExpressionFor> ****)

TheExpression[S_?QubitQ] := {
  {1/2 + S[3]/2, S[4]},
  {S[5], 1/2 - S[3]/2}
 }
(* NOTE: This makes ExpressionFor to generate an operator expression in terms
   of the Pauli raising and lowering operators instead of the Pauli X and Y
   operators. Many evaluations are faster with the raising and lowering
   operators rather than X and Y operators. When an expression in terms of the
   X and Y operators are necessary, one can use Elaborate. *)

(**** </ExpressionFor> ****)


(**** <Phase> ****)

Phase::usage = "Phase[\[Phi], S[\[Ellipsis],n]] represents the relative phase shift by \[Phi] between the posiive and negative eigenstates of S[\[Ellipsis],n]."

Phase::bad = "Phase gate is defined only for three axis, X (1), Y (2), and Z (3). You enterned ``."

Format[op:Phase[phi_, S_?QubitQ, ___]] :=
  Interpretation[TraditionalForm @ HoldForm[S[phi]], op]

Phase[0, __] = 1

Phase[phi_, S_?QubitQ, ___] :=
  (Message[Phase::bad, S]; 1) /;
  Not @ MemberQ[{1, 2, 3}, FlavorLast @ S]

Phase[aa_List, S_?QubitQ, opts___?OptionQ] :=
  Map[Phase[#, S, opts]&, aa]

Phase[phi_, qq:{__?QubitQ}, opts___?OptionQ] :=
  Map[Phase[phi, #, opts]&, qq]

Phase[aa_List, ss:{__?QubitQ}, opts___?OptionQ] :=
  MapThread[Phase[#1, #2, opts]&, {aa, ss}]


Phase /:
Dagger @ Phase[phi_, S_?QubitQ, opts___?OptionQ] :=
  Phase[-Conjugate[phi], S, ReplaceRulesBy[{opts}, "Label" -> auxSuperDagger]]
  

Phase /:
Elaborate @ Phase[phi_, S_?QubitQ, ___] :=
  Garner[ (1 + Exp[I*phi])/2 + S * (1 - Exp[I*phi])/2 ]

Phase /:
Elaborate[op_Phase] = op (* fallback *)


Phase /:
Matrix[op:Phase[_, _?QubitQ, ___], rest__] := 
  Matrix[Elaborate @ op, rest]

Phase /:
Matrix[op:Phase[___], __] = op (* fallback *)


Phase /:
Multiply[pre___, op_Phase, in_Ket, post___] :=
  Multiply[pre, Multiply[Elaborate @ op, in], post]


(* NOTE: The following code makes many calculations significantly slow. It is far better to use the high-level feature as those given below for MultiplyPower and Multiply. *)
(*
Phase /:
Multiply[pre___, op_Phase, post___] := Multiply[pre, Elaborate @ op, post]
 *)

Phase /:
MultiplyPower[Phase[phi_, rest__], n_Integer] :=
  Phase[n * phi, rest]

Phase /:
Multiply[
  pre___, 
  Phase[a_, ss_, opts___?OptoinQ],
  Phase[b_, ss_, more___?OptoinQ],
  post___
] :=
  Multiply[pre, Phase[a+b, ss, more, opts], post]

(**** </Phase> ****)


(**** <Rotation> ****)

Format[ op:Rotation[phi_, v:{_, _, _}, S_?QubitQ, rest___] ] :=
  Interpretation[
    DisplayForm @ RowBox @ { Exp,
      RowBox @ {"(", -I * (phi/2) * Dot[S @ All, Normalize @ v], ")"}
    },
    op 
  ]

Rotation /:
Elaborate @ Rotation[phi_, v:{_, _, _}, S_?QubitQ, ___] :=
  Garner[ Cos[phi/2] - I*Sin[phi/2]*Dot[S @ All, Normalize @ v] ]

Rotation /:
Multiply[pre___, op:Rotation[_, {_, _, _}, S_?QubitQ, ___], in_Ket, post___] :=
  Garner @ Multiply[pre, Garner @ Multiply[Elaborate @ op, in], post]

(**** </Rotation> ****)


(**** <EulerRotation> ****)

EulerRotation /:
Unfold[EulerRotation[{a_,b_,c_}, S_?QubitQ, opts___?OptionQ], ___] :=
  QuantumCircuit[
    Rotation[c, S[3], opts],
    Rotation[b, S[2], opts],
    Rotation[a, S[3], opts]
  ]

EulerRotation /:
Multiply[pre___, op:EulerRotation[{_, _, _}, S_?QubitQ, ___], in_Ket, post___] :=
  Garner @ Multiply[pre, Garner @ Multiply[Elaborate @ op, in], post]

(**** </EulerRotation> ****)


(**** <CNOT> ****)

CX::usage = "CX is an alias for CNOT."

CNOT::usage = "CNOT[C, T] represents the CNOT gate on the two qubits C and T, which are the control and target qubits, respectively. Note that it does not expand until necessary (e.g., multiplied to a Ket); use Elaborate in order to expand it."

CNOT::incmp = "Control register `` and control values set `` have unequal lengths."

SetAttributes[CNOT, NHoldFirst]

SyntaxInformation[CNOT] = {
  "ArgumentsPattern" -> {_, _}
}

CNOT[cc:(_?QubitQ|{__?QubitQ})] := (
  CheckArguments[CNOT[cc], 2];
  CNOT[cc, 1]
)


CNOT[c_?QubitQ, t_] := CNOT[{c[$] -> 1}, t]

CNOT[c_, t_?QubitQ] := CNOT[c, t @ {$}]

CNOT[cc:{__?QubitQ}, tt_] :=
  CNOT[Thread[cc -> 1], tt]


CNOT[Rule[c_?QubitQ, v_], tt_] := CNOT[{c -> v}, tt]

CNOT[Rule[cc:{__?QubitQ}, v_], tt_] :=
  CNOT[Thread[cc -> v], tt]


CNOT[Rule[cc:{__?QubitQ}, vv_List], tt_] := (
  Message[CNOT::incmp, cc, vv];
  CNOT[cc -> PadRight[vv, Length @ cc, 1], tt]
 ) /; Length[cc] != Length[vv]


CNOT[cc:{Rule[_?QubitQ, _]..}, tt:{__?QubitQ}] :=
  CNOT[FlavorCap @ cc, FlavorCap @ tt] /;
  Not[FlavorCapQ @ Join[Keys @ cc, tt]]


CNOT /: Dagger[ op_CNOT ] = op

CNOT /:
Elaborate[op_CNOT] = op (* fallback *)

CNOT /:
Elaborate @
  CNOT[cc:{Rule[_?QubitQ, _?BinaryQ]..}, tt:{__?QubitQ}] := Module[
    { prj = Through[Keys[cc][3]],
      not = Multiply @@ Through[tt[1]] },
    prj = Multiply @@ Garner[(1+prj)/2 - Values[cc]*prj];
    Garner @ Elaborate[(1-prj) + prj ** not]
  ]

CNOT /:
Multiply[pre___, CNOT[cc:{__Rule}, tt_], in_Ket] := Module[
  { op = Multiply @@ Through[tt[1]],
    xx },
  If[ in[Keys @ cc] == Values[cc],
    Multiply[pre, op ** in],
    Multiply[pre, in],
    xx = Mod[in[tt] + Apply[Times, Mod[in[Keys @ cc]+Values[cc]+1, 2]], 2];
    Multiply[pre, in[tt -> xx]]
  ]
]

CNOT /:
Multiply[in_Bra, op_CNOT, post___] :=
  Multiply[ Dagger[op ** Dagger[in]], post ]

CNOT /:
Multiply[pre___, op:CNOT[cc_List, tt_List], Dyad[a_Association, b_Association], post___] :=
  Multiply[pre, op ** Ket[a], Bra[b], post] /; ContainsAll[Keys @ a, Join[Keys @ cc, tt]]

CNOT /:
Multiply[pre___, Dyad[a_Association, b_Association], op:CNOT[cc_List, tt_List], post___] :=
  Multiply[pre, Ket[a], Bra[b] ** op, post] /; ContainsAll[Keys @ b, Join[Keys @ cc, tt]]

(*
HoldPattern @ Multiply[pre___, op_CNOT, post___] :=
  Multiply[pre, Elaborate[op], post]
  *)
(* NOTE: DO NOT put "CNOT /:". *)

CNOT /:
Matrix[op:CNOT[{Rule[_?QubitQ, _]..}, {__?QubitQ}], rest___] :=
  Matrix[Elaborate @ op, rest]

CNOT /: (* for FromGottesmanMatrix and CliffordFactor *)
Matrix[op:CNOT[c_Integer, t_Integer], n_Integer] := 
  MatrixEmbed[CirclePlus[ThePauli[0], ThePauli[1]], {c, t}, n]

CNOT /: (* fallback *)
Matrix[op_CNOT, ss:{__?SpeciesQ}] := op * One[Whole @ Dimension @ ss]


(* See also Smolin and DiVincenzo (1996) for the optimization of the Fredkin gate. *)
CNOT /:
Unfold[CNOT[{a_?QubitQ -> 1, b_?QubitQ -> 1}, {c_?QubitQ}], opts___?OptionQ] :=
  Prepend[Append[Unfold[CZ @ {a,b,c}, opts], c[6]], c[6]]

(**** </CNOT> ****)


(**** <CZ> ****)

CZ::usage = "CZ[{c1, c2, \[Ellipsis]}, t] represents the single-target controlled-Z gate with multiple control qubits {c1, c2, \[Ellipsis]} and a single target qubit t.\noCZ[{s1,s2,\[Ellipsis],sn}] is equivalent to CZ[{s1, s2, \[Ellipsis]}, sn]."

CZ::few = "CZ gate requires two or more qubits; `` is returned."

CZ[c_?QubitQ, t_?QubitQ] := CZ[FlavorCap @ c, FlavorCap @ t] /;
  Not[FlavorCapQ @ {c, t}]

CZ /:
Dagger[ op_CZ ] := op

CZ[c_?QubitQ, t_?QubitQ] := CZ @ FlavorCap @ {c, t}

CZ[cc:{__?QubitQ}, t_?QubitQ] := CZ @ FlavorCap @ Append[cc, t]

CZ[ss:{__?QubitQ}] := CZ[FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

CZ[ss:{S_?QubitQ}] := (Message[CZ::few, S[3]]; S[3])

CZ /:
Elaborate @ CZ[any___] := 1 (* fallback *)

CZ /:
Elaborate @ CZ[ss:{_?QubitQ, __?QubitQ}] := Garner @ With[
  { n = Power[2, Length[ss]-1],
    sub = Rest @ Subsets[Through[ss[3]]] },
    (Multiply @@@ sub) . (2 * Mod[Length /@ sub, 2] - 1) / n + (n-1)/n
]


CZ /:
Matrix[CZ[ss:{__?QubitQ}], tt:{___?SpeciesQ}] := With[
  { n = Power[2, Length @ ss] },
  MatrixEmbed[ReplacePart[One[n], {n, n} -> -1], ss, tt]
]


(* NOTE: Multiply[..., CZ, ...] does NOT Elaborate CZ automatically because
   Elaborate[CZ] cannot take advantage of the simplicity of CZ[...] ** Ket
   [...]. *)
CZ /:
Multiply[pre___, CZ[ss:{__?QubitQ}], Ket[a_Association]] := (* performance booster *)
  Multiply[pre,
    Switch[ Whole @ Lookup[a, ss],
      1, -Ket[a],
      _,  Ket[a]
    ]    
  ]

CZ /:
Multiply[in_Bra, op_CZ, post___] :=
  Multiply[ Dagger[op ** Dagger[in]], post ]

CZ /:
Multiply[pre___, op:CZ[ss_List], Dyad[a_Association, b_Association], post___] :=
  Multiply[pre, op ** Ket[a], Bra[b], post] /; ContainsAll[Keys @ a, ss]

CZ /:
Multiply[pre___, Dyad[a_Association, b_Association], op:CZ[ss_List], post___] :=
  Multiply[pre, Ket[a], Bra[b] ** op, post] /; ContainsAll[Keys @ b, ss]


(* See also Smolin and DiVincenzo (1996) for the optimization of the Fredkin gate. *)
CZ /:
Unfold[CZ[ss:{_?QubitQ, _?QubitQ, _?QubitQ}], OptionsPattern[]] := 
  Switch[ OptionValue[Method],
    Default, theSmolinCZ[ss],
    "Gray", theGrayCZ[ss],
    _, Message[Unfold::unknown, OptionValue @ Method]; theSmolinCZ[ss]
  ]

(* See also Smolin and DiVincenzo (1996) for the optimization of the Fredkin gate. *)
theSmolinCZ[{a_, b_, c_}] := QuantumCircuit[
  CNOT[a, b],
  ControlledGate[b, c[-7]],
  CNOT[a, b],
  ControlledGate[a, c[7]],
  ControlledGate[b, c[7]]
]

(* Based on the Gray-code method. *)
theGrayCZ[{a_, b_, c_}] := QuantumCircuit[
  ControlledGate[a, c[7]],
  CNOT[a, b],
  ControlledGate[b, c[-7]],
  CNOT[a, b],
  ControlledGate[b, c[7]]
]

(**** </CZ> ****)


(**** <SWAP> ****)

SWAP::usage = "SWAP[A, B] operates the SWAP gate on the two qubits A and B."

SetAttributes[SWAP, Listable]

SWAP[a_?QubitQ, b_?QubitQ] := SWAP @@ FlavorCap @ {a, b} /;
  Not[FlavorCapQ @ {a, b}]

SWAP[a_?QubitQ, b_?QubitQ] := SWAP[b, a] /;
  Not @ OrderedQ @ FlavorCap @ {a, b}

SWAP /:
Dagger[ op_SWAP ] = op


SWAP /: (* for FromGottesmanMatrix and CliffordFactor *)
Matrix[op:SWAP[c_Integer, t_Integer], n_Integer] := 
  MatrixEmbed[CirclePlus[{{1}}, ThePauli[1], {{1}}], {c, t}, n]

SWAP /:
Matrix[op_SWAP, rest___] := Matrix[Elaborate[op], rest]


SWAP /:
Elaborate @ SWAP[x_?QubitQ, y_?QubitQ] := Module[
  { a = Most @ x,
    b = Most @ y },
  Garner[ (1 + a[1]**b[1] + a[2]**b[2] + a[3]**b[3]) / 2 ]
]

SWAP /:
Unfold[SWAP[s_?QubitQ, t_?QubitQ], ___] := QuantumCircuit[
  CNOT[s, t], CNOT[t, s], CNOT[s, t]
]


SWAP /:
Multiply[pre___, SWAP[s_?QubitQ, t_?QubitQ], Ket[a_Association]] :=
  Multiply[ pre,
    Ket @ KeySort @ Join[a, AssociationThread[{s, t} -> Lookup[a, {t, s}]]]
  ]

SWAP /:
Multiply[in_Bra, op_SWAP, post___] :=
  Multiply[ Dagger[op ** Dagger[in]], post ]

SWAP /:
Multiply[pre___, op:SWAP[s_, t_], Dyad[a_Association, b_Association], post___] :=
  Multiply[pre, op ** Ket[a], Bra[b], post] /; ContainsAll[Keys @ a, {s, t}]

SWAP /:
Multiply[pre___, Dyad[a_Association, b_Association], op:SWAP[s_, t_], post___] :=
  Multiply[pre, Ket[a], Bra[b] ** op, post] /; ContainsAll[Keys @ b, {s, t}]

(**** </SWAP> ****)


(**** <iSWAP> ****)

iSWAP::usage = "iSWAP[A, B] operates the iSWAP gate on the two qubits A and B."

SetAttributes[iSWAP, Listable]

iSWAP[a_?QubitQ, b_?QubitQ] := iSWAP @@ FlavorCap @ {a, b} /;
  Not[FlavorCapQ @ {a, b}]

iSWAP[a_?QubitQ, b_?QubitQ] := iSWAP[b, a] /;
  Not @ OrderedQ @ FlavorCap @ {a, b}

iSWAP /:
Matrix[op_iSWAP, rest___] := Matrix[Elaborate[op], rest]

iSWAP /:
Elaborate @ iSWAP[a_?QubitQ, b_?QubitQ] :=
  Garner[ (1 + I*a[1]**b[1] + I*a[2]**b[2] + a[3]**b[3]) / 2 ]

iSWAP /:
Multiply[pre___, iSWAP[s_?QubitQ, t_?QubitQ], Ket[a_Association]] := With[
  { ts = Lookup[a, {t, s}] },
  If[OddQ[Total @ ts], I, 1] *
  Multiply[ pre,
    Ket @ KeySort @ Join[a, AssociationThread[{s, t} -> ts]]
  ]
]

iSWAP /:
Unfold[iSWAP[s_?QubitQ, t_?QubitQ], ___] := QuantumCircuit[
  {s[7], t[7]}, s[6], CNOT[s, t], CNOT[t, s], t[6]
]

Unfold[HoldPattern @ Dagger[op_iSWAP], ___] := 
  Dagger[Unfold @ op]

(**** </iSWAP> ****)


(**** <Toffoli> ****)

Toffoli::usage = "Toffoli[A, B, C] operates the Toffoli gate, i.e., the three-qubit controlled-note gate on C controlled by A and B."

SetAttributes[Toffoli, Listable]

Toffoli[a_?QubitQ, b_?QubitQ, c_?QubitQ] :=
  Toffoli @@ FlavorCap @ {a, b, c} /;
  Not[FlavorCapQ @ {a, b, c}]

Toffoli /:
Dagger[ op_Toffoli ] := op

Toffoli /:
HoldPattern @ Elaborate @ Toffoli[a_?QubitQ, b_?QubitQ, c_?QubitQ] := Garner[
  ( 3 + a[3] + b[3] + c[1] -
      a[3]**b[3] - a[3]**c[1] - b[3]**c[1] +
      a[3]**b[3]**c[1]
  ) / 4
]

Toffoli /:
HoldPattern @ Multiply[pre___, op_Toffoli, post___] :=
  Multiply[pre, Elaborate[op], post]

Toffoli /:
HoldPattern @ Matrix[op_Toffoli, rest___] := Matrix[Elaborate[op], rest]

(* See also Smolin and DiVincenzo (1996) for the optimization of the Fredkin gate. *)
Toffoli /:
Unfold[Toffoli[a_?QubitQ, b_?QubitQ, c_?QubitQ], opts___?OptionQ] :=
  Prepend[Append[Unfold[CZ @ {a,b,c}, opts], c[6]], c[6]]

(**** </Toffoli> ****)


(**** <Fredkin> ****)

Fredkin::usage = "Fredkin[a, {b, c}] represents the Fredkin gate, i.e., the SWAP gate on b and c controlled by a."

SyntaxInformation[Fredkin] = {
  "ArgumentsPattern" -> {_, _}
 }

Fredkin[a_?QubitQ, {b_?QubitQ, c_?QubitQ}] :=
  Fredkin[FlavorCap @ a, FlavorCap @ {b, c}] /;
  Not[FlavorCapQ @ {a, b, c}]

Fredkin /:
Dagger[ op_Fredkin ] := op

Fredkin /:
Elaborate @ Fredkin[a_?QubitQ, {b_?QubitQ, c_?QubitQ}] :=
  Garner @ Elaborate[ a[10] + a[11] ** SWAP[b, c] ]

(*
Fredkin /:
HoldPattern @ Multiply[pre___, op_Fredkin, post___] :=
  Multiply[pre, Elaborate[op], post]
 *)

Fredkin /:
Matrix[op_Fredkin, rest___] := Matrix[Elaborate[op], rest]


(* Change in input format *)
Fredkin[a_?QubitQ, b_?QubitQ, c_?QubitQ] := (
  CheckArguments[Fredkin[a, b, c], 2];
  Fredkin[a, {b, c}]
 )

Fredkin /: (* fallback *)
Unfold[op_Fredkin, ___] = op

Fredkin /:
Unfold[Fredkin[a_?QubitQ, {b_?QubitQ, c_?QubitQ}, ___], ___] := 
  QuantumCircuit[
    CNOT[c, b],
    CNOT[{a, b}, c],
    CNOT[c, b]
  ]

(**** </Fredkin> ****)


(**** <Deutsch> ****)

Deutsch::usage = "Deutsch[angle, {a, b, c}] represents the Deutsch gate, i.e., \[ImaginaryI] times the rotation by angle around the x-axis on qubit c controlled by two qubits a and b."

Deutsch[ph_, qq:{__?QubitQ}, opts___?OptionQ] :=
  Deutsch[ph, FlavorCap @ qq, opts] /;
  Not[FlavorCapQ @ qq]

(*
Deutsch /:
Dagger[ Deutsch[ph_, qq:{__?QubitQ}, opts___?OptionQ] ] :=
  2*Elaborate[1 - Multiply@@Through[Most[qq][11]]] - Deutsch[-ph, qq, opts]
 *)

Deutsch /:
HoldPattern @ Elaborate @
  Deutsch[ph_, {a_?QubitQ, b_?QubitQ, c_?QubitQ}, opts___?OptionQ] := With[
    { P = a[11]**b[11] },
    Garner @ Elaborate[(1-P) + I*P**Rotation[ph, c[1]]]
   ]

Deutsch /:
HoldPattern @ Multiply[pre___, op_Deutsch, post___] :=
  Multiply[pre, Elaborate[op], post]

Deutsch /:
HoldPattern @ Matrix[op_Deutsch, rest___] := Matrix[Elaborate[op], rest]

Dagger /:
HoldPattern @ Multiply[pre___, Dagger[op_Deutsch], post___] :=
  Multiply[pre, Dagger[Elaborate @ op], post]

Dagger /:
HoldPattern @ Matrix[Dagger[op_Deutsch], rest___] :=
  Topple @ Matrix[Elaborate[op], rest]

(**** </Deutsch> ****)


(**** <ControlledGate> ****)

ControlledGate::usage = "ControlledGate[{C1, C2, ...}, T[j, ..., k]] represents a multi-qubit controlled-U gate. It operates the gate T[j, ..., k] on the qubit T[j, ..., $] controlled by the qubits C1, C2.\nControlledGate[C, T] is equivalent to ControlledGate[{C}, T].\nControlledGate[{C1, C2, ...}, expr] represents a general controlled gate operating expr on the qubits involved in it."

ControlledGate::unitary = "The operator `` is not unitary."

ControlledGate::incmp =  "Control register `` and value set `` have unequal lengths."

SetAttributes[ControlledGate, NHoldFirst]

SyntaxInformation[ControlledGate] = {
  "ArgumentsPattern" -> {_, __}
}

AddGarnerPatterns[_ControlledGate]


ControlledGate[cc_] := (
  CheckArguments[ControlledGate[cc], 2];
  ControlledGate[cc, 1]
)


ControlledGate[{}, op_, ___] = op (* fallback *)

ControlledGate[S_?QubitQ, rest__] :=
  ControlledGate[{S[$]->1}, rest]

ControlledGate[ss:{___?QubitQ}, rest__] :=
  ControlledGate[Thread[FlavorCap[ss] -> 1], rest]
(* NOTE: ___ not __; see fallback below. *)


ControlledGate[Rule[c_?QubitQ, v_], rest__] :=
  ControlledGate[{c -> v}, rest]

ControlledGate[Rule[cc:{___?QubitQ}, v_], rest__] :=
  ControlledGate[Thread[cc -> v], rest]
(* NOTE: ___ not __; see fallback below. *)

ControlledGate[Rule[cc:{__?QubitQ}, vv_List], rest__] := (
  Message[ControlledGate::incmp, cc, vv];
  ControlledGate[cc -> PadRight[vv, Length @ cc, 1], rest]
) /; Length[cc] != Length[vv]


ControlledGate[cc:{Rule[_?QubitQ, _]..}, rest__] :=
  ControlledGate[FlavorCap @ cc, rest] /;
  Not[FlavorCapQ @ Keys @ cc]


ControlledGate[cc:{__Rule}, z_?CommutativeQ, opts___?OptionQ] :=
  Module[
    { ff, op },
    ff = If[Last[Values @ cc] == 0, -1, 1, 1];
    op = Phase[ff*Arg[z], Last[Keys @ cc][3], opts];
    If[Abs[z] != 1, Message[ControlledGate::unitary, z]];
    If[Length[cc] > 1, ControlledGate[Most @ cc, op], op]
  ]


ControlledGate /:
Unfold[
  ControlledGate[cc:{__Rule}, ActOn[z_?CommutativeQ, ___], ___?OptionQ],
  ___
] :=
  ControlledGate[cc, z]

ControlledGate /:
Unfold[
  ControlledGate[ cc:{__Rule},
    HoldPattern @ Multiply[ss__?QubitQ],
    opts___?OptionQ 
  ], 
  ___
] := With[
  { new = Normal @ KeyDrop[Flatten @ {opts}, "Label"] },
  QuantumCircuit @@ Map[ControlledGate[cc, #, new]&, {ss}]
]

ControlledGate /:
Unfold[ControlledGate[cc:{__Rule}, op_, ___?OptionQ], ___] := Module[
  { tt = First[Qubits @ op],
    mm = Matrix[op],
    ff },
  Which[
    CommutativeQ[ff = Elaborate[op / tt[1]]],
    Return @ {CNOT[cc, tt], ControlledGate[cc, ff]},
    CommutativeQ[ff = Elaborate[op / tt[2]]],
    Return @ {tt[-7], CNOT[cc, tt], tt[7], ControlledGate[cc, ff]},
    CommutativeQ[ff = Elaborate[op / tt[3]]],
    Return @ {tt[6], CNOT[cc, tt], tt[6], ControlledGate[cc, ff]}
  ];
  If[ Chop[Tr @ mm] == 0,
    Module[
      {val, vec},
      {val, vec} = Eigensystem[mm];
      vec = Transpose[Normalize /@ vec] . ThePauli[1] . ThePauli[6];
      vec = Elaborate @ ExpressionFor[vec, tt];
      Return @ {
        {vec, "Label" ->"A"},
        CNOT[cc, tt],
        {Dagger[vec], "Label" -> Superscript["A","\[Dagger]"]}
       }
     ]
  ];
  ff = Sqrt[Det @ mm];
  Module[
    {a, b, c},
    {a, b, c} = TheEulerAngles[mm / ff];
    QuantumCircuit[
      Rotation[-(a-c)/2, tt[3], "Label" -> "C"],
      CNOT[cc, tt],
      EulerRotation[{0, -b/2, -(a+c)/2}, tt, "Label" -> "B"],
      CNOT[cc, tt],
      EulerRotation[{a, b/2, 0}, tt, "Label" -> "A"],
      ControlledGate[cc, ff]
    ]
  ]
] /; Length[Qubits @ op] == 1


ControlledGate /:
Dagger @ ControlledGate[cc:{__Rule}, expr_, opts___?OptionQ] :=
  ControlledGate[cc, Dagger @ expr, ReplaceRulesBy[{opts}, "Label" -> auxSuperDagger]]


ControlledGate /:
Elaborate[op_ControlledGate] = op (* fallback *)

ControlledGate /:
Elaborate @
  ControlledGate[cc:{Rule[_?QubitQ, _?BinaryQ]..}, op_, ___?OptionQ] :=
  Module[
    { rr = Thread[Values[cc] -> Values[cc]],
      prj },
    prj = Multiply @@ Elaborate @ MapThread[Construct, {Keys @ cc, rr}];
    Garner[prj ** Elaborate[op] + (1 - prj)]
  ]


ControlledGate /:
Matrix[
  ControlledGate[cc:{Rule[_?QubitQ, _?BinaryQ]..}, op_, ___?OptionQ],
  ss:{__?SpeciesQ} ]:= Module[
    { rr = Thread[Values[cc] -> Values[cc]],
      prj },
    prj = Dot @@ Matrix[MapThread[Construct, {Keys @ cc, rr}], ss];
    Dot[prj, Matrix[op, ss]] + (One[Whole @ Dimension @ ss] - prj)
  ]

ControlledGate /:
Matrix[op_ControlledGate, ss:{__?SpeciesQ}] :=
  op * One[Whole @ Dimension @ ss] (* fallback *)


ControlledGate /:
Multiply[ pre___,
  ControlledGate[cc:{Rule[_?QubitQ, _?BinaryQ]..}, op_, ___?OptionQ],
  in_Ket
] :=
  If[ in[Keys @ cc] == Values[cc],
    Multiply[pre, op ** in],
    Multiply[pre, in],
    Multiply[pre, in]
  ]

(* NOTE: The following code makes many calculations significantly slow. It is far better to use high-level features instead. *)
(* NOTE: DO NOT put "ControlledGate /:". Otherwise, the above rule with
   ControlledGate[...]**Ket[] is overridden. *)
(* 
Multiply[ pre___,
  op:ControlledGate[{Rule[_?QubitQ, _?BinaryQ]..}, _, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
 *)

(**** </ControlledGate> ****)


(**** <ControlledPower> ****)

ControlledPower::usage = "ControlledPower[{c1, c2, ...}, op] represents a controlled exponentiation gate."

ControlledPower[S_?QubitQ, expr_, opts___?OptionQ] :=
  ControlledPower[{S[$]}, expr, opts]

ControlledPower[ss:{__?QubitQ}, expr_, opts___?OptionQ] :=
  ControlledPower[FlavorCap @ ss, expr, opts] /;
  Not[FlavorCapQ @ ss]


ControlledPower /:
Dagger @ ControlledPower[ss:{__?QubitQ}, expr_, opts___?OptionQ] :=
  ControlledPower[ ss,
    Dagger[expr],
    ReplaceRulesBy[{opts}, "Label" -> auxSuperDagger]
  ]


ControlledPower /:
Elaborate[op_ControlledPower] = op (* fallback *)

ControlledPower /:
Elaborate @ ControlledPower[cc:{__?QubitQ}, op_, ___] :=
  Module[
    { xx, mm },
    xx = Dyad[#, #, cc]& /@ Basis[cc];
    mm = NestList[Multiply[op, #]&, 1, Power[2, Length @ cc]-1];
    Elaborate @ Total @ Multiply[xx, mm]
  ]


ControlledPower /: (* fallback *)
Matrix[op_ControlledPower, ss:{__?SpeciesQ}] :=
  op * One[Whole @ Dimension @ ss]

ControlledPower /:
Matrix[ControlledPower[cc_, op_, ___], ss:{__?SpeciesQ}] :=
  Module[
    { L = Power[2, Length @ cc],
      tt = Qubits[op],
      mm },
    mm = Matrix[op, tt];
    mm = CirclePlus @@ NestList[Dot[mm, #]&, One @ Power[2, Length @ tt], L-1];
    MatrixEmbed[mm, Join[cc, tt], ss]
  ]


ControlledPower /:
Multiply[pre___, ControlledPower[cc_, op_, ___], in_Ket] := With[
  { x = FromDigits[in[cc], 2] },
  (* Multiply[pre, Nest[Multiply[op, #]&, in, x]] *)
  (* NOTE: The following method is faster than the above. It is probably because MultiplyPower calculates recursively and makes better use of the caching capabilities. *)
  Multiply[pre, Elaborate[MultiplyPower[op, x] ** in]]
]

(* NOTE: The following code makes many calculations significantly slow. It is far better to use high-level features instead. *)
(* NOTE: DO NOT put "ControlledPower /:". *)
(*
HoldPattern @ Multiply[pre___, op_ControlledPower, post___] :=
  Multiply[pre, Elaborate @ op, post]
*)

ControlledPower /:
Unfold[ControlledPower[ss:{__?QubitQ}, op_, opts:OptionsPattern[Gate]], ___] :=
  Module[
    { n = Length @ ss,
      tt = Qubits[op],
      pwr, txt, new },
    pwr = ActOn[tt] /@ Table[MultiplyPower[op, Power[2, n-k]], {k, n}];
    (* NOTE: Without ActOn, some elements in pwr may be 1. *)

    txt = OptionValue[Gate, {opts, Options @ op, "Label" -> gateLabel @ op}, "Label"];
    txt = Table["Label" -> auxSuperscript[txt, Superscript[2, n-k]], {k, n}];
    new = ReplaceAll[
      MapThread[ControlledGate, {ss, pwr, txt}],
      HoldPattern @ ControlledGate[args__] ->
        ControlledGate[args, "LabelSize" -> 0.65, opts]
    ];
    QuantumCircuit @@ new
  ]

(**** </ControlledPower> ****)


(**** <ActOn> ****)

ActOn::usage = "ActOn[op, {s1, s2, \[Ellipsis]}] represents an operator acting on the system of species {s1, s2, \[Ellipsis]}.\nActOn[{s1, s2, \[Ellipsis]}] represents the operator form of ActOn.\nActOn is a low-level function intended for internal use."

AddElaborationPatterns[_ActOn]

ActOn[S_?SpeciesQ, opts___?OptionQ] := 
  ActOn[{S[$]}, opts]

ActOn[ss:{___?SpeciesQ}, opts___?OptionQ] :=
  ActOn[FlavorCap @ ss, opts] /; Not[FlavorCapQ @ ss]

ActOn[ss:{___?SpeciesQ}, opts___?OptionQ][op_] := 
  ActOn[op, ss, opts]

ActOn[op_, ss:{___?SpeciesQ}, opts___] := Module[
  { tt = Agents[op] },
  ActOn[op, Union[ss, tt], opts] /; Not @ ContainsAll[ss, tt]
]

ActOn[op_, S_?SpeciesQ, opts___] := ActOn[op, {S[$]}, opts]

ActOn[op_, ss:{___?SpeciesQ}, opts___] :=
  ActOn[op, FlavorCap @ ss, opts] /; Not[FlavorCapQ @ ss]


ActOn /:
Elaborate @ ActOn[op_, ss:{___?SpeciesQ}, ___] = op

ActOn /:
Matrix[ActOn[op_, ss:{___?SpeciesQ}, ___], rest___] :=
  Matrix[op, rest]

(* 
ActOn /:
Multiply[pre___, ActOn[op_, {___?SpeciesQ}, ___], post___] :=
  Multiply[pre, op, post]
 *)

(**** </ActOn> ****)


(**** <UniformlyControlledRotation> ****)

(* SEE: Schuld and Pertruccione (2018), Mottonen et al. (2005) *)

UniformlyControlledRotation::usage = "UniformlyControlledRotation[{c1,c2,\[Ellipsis],cn}, {a1,a2,\[Ellipsis],a2n}, s[\[Ellipsis],k]] represents the uniformly controlled rotation on qubit s[\[Ellipsis],$] around the k-axis by andles a1, a2, \[Ellipsis], a2n  depending on all possible bit sequences of control qubits c1, c2, \[Ellipsis], cn."

UniformlyControlledRotation::list = "The length of `` is not an integer power of 2."

SyntaxInformation[UniformlyControlledRotation] = {
  "ArgumentsPattern" -> {_, _, _, ___}
 }

AddElaborationPatterns[_UniformlyControlledRotation]


UniformlyControlledRotation[
  cc:{___?QubitQ}, aa_?VectorQ, S_?QubitQ,
  opts___?OptionQ ] :=
  UniformlyControlledRotation[ cc, aa,
    UnitVector[3, FlavorLast @ S], FlavorMute @ S,
    opts ]

UniformlyControlledRotation[
  cc:{___?QubitQ}, aa_List, vv_List, S_?QubitQ, opts___?OptionQ ] :=
  UniformlyControlledRotation[FlavorCap @ cc, aa, vv, FlavorCap @ S, opts] /;
  Not[FlavorCapQ @ Append[cc, S]]

UniformlyControlledRotation[
  cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, opts___?OptionQ ] := (
    Message[UniformlyControlledRotation::list, aa];
    UniformlyControlledRotation[ cc,
      PadRight[aa, Power[2, Length @ cc]], vv, S, opts ]
   ) /; Power[2, Length @ cc] != Length[aa]

UniformlyControlledRotation[
  {}, {a_}, v:{_, _, _}, S_?QubitQ, opts___?OptionQ] :=
  Rotation[a, v, S, opts]


UniformlyControlledRotation /:
Dagger @ UniformlyControlledRotation[
  cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, opts___?OptionQ ] :=
  UniformlyControlledRotation[ cc, -aa, vv, S,
    ReplaceRulesBy[{opts}, "Label" -> auxSuperDagger]
  ]


UniformlyControlledRotation /:
Matrix[
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ ],
  rest___ ] := Matrix[Unfold @ op, rest]


UniformlyControlledRotation /:
Elaborate @
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ ] :=
  With[ {qq = Qubits @ op}, Elaborate @ ExpressionFor[Matrix[op, qq], qq] ]


UniformlyControlledRotation /:
Multiply[ pre___,
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ],
  in_Ket
] := 
  With[
    { gg = List @@ Unfold[op] },
    Multiply[pre, Fold[Multiply[#2, #1]&, in, gg]]
  ]

(*
Multiply[ pre___,
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
 *)
(* NOTE: DO NOT put "UniformlyControlledRotation /:". Otherwise, the above
   rule with UniformlyControlledRotation[...]**Ket[] is overridden. *)


UniformlyControlledRotation /:
Unfold[
  UniformlyControlledRotation[
    cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, opts___?OptionQ
  ],
  ___
] := 
  QuantumCircuit @@ ReleaseHold @ Thread @
    ControlledGate[
      Thread[Hold[cc] -> Tuples[{0, 1}, Length @ cc]],
      Rotation[aa, vv, S],
      Sequence @@ Flatten @ {opts}
    ]


(* SEE: Schuld and Pertruccione (2018), Mottonen et al. (2005) *)
UniformlyControlledRotation /:
UnfoldAll[
  UniformlyControlledRotation[
    cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ,
    opts___?OptionQ
  ],
  ___
] := 
  Module[
    { n = Length[cc],
      bb, gg, mm, tt },
    bb = Tuples[{0, 1}, n];
    gg = BinaryToGray /@ bb;
    mm = Power[2, -n] * Power[-1, Outer[Dot, gg, bb, 1]];
    tt = Rotation[mm.aa, vv, S, opts];
    gg = ReleaseHold @ Thread[Hold[CNOT][sequenceCNOT @ cc, S]];
    QuantumCircuit @@ Riffle[tt, gg]
  ] /; Chop[First @ vv] == 0


sequenceCNOT::usage = "Returns a list of control qubits of CNOT gates to be used to efficiently factorize a uniformly-controlled gate."

sequenceCNOT[{c_}] := {c, c}

sequenceCNOT[cc:{_, __}] := With[
  { new = ReplacePart[sequenceCNOT[Rest@cc], -1 -> First[cc]] },
  Join[new, new]
]

(**** </UniformlyControlledRotation> ****)


(**** <UniformlyControlledGate> ****)

UniformlyControlledGate::usage = "UniformlyControlledGate[{c1,c2,\[Ellipsis],cn}, {op1,op2,\[Ellipsis],op2n}] represents the uniformly-controlled unitary gate operating op1, op2, \[Ellipsis], op2n depending on all possible bit sequences of control qubits c1, c2, \[Ellipsis], cn."

UniformlyControlledGate::list = "The length of `` is not an integer power of 2."

SyntaxInformation[UniformlyControlledGate] = {
  "ArgumentsPattern" -> {_, _, ___}
 }

AddElaborationPatterns[_UniformlyControlledGate]


UniformlyControlledGate[cc:{__?QubitQ}, tt_List, opts___?OptionQ] :=
  UniformlyControlledGate[FlavorCap @ cc, tt, opts] /;
  Not[FlavorCapQ @ cc]

UniformlyControlledGate[cc:{__?QubitQ}, tt_List, opts___?OptionQ] := (
  Message[UniformlyControlledGate::list, tt];
  UniformlyControlledGate[cc, PadRight[tt, Power[2, Length @ cc], 1], opts]
 ) /; Power[2, Length @ cc] != Length[tt]

UniformlyControlledGate[{}, {op_}] = op


UniformlyControlledGate /:
Dagger @ UniformlyControlledGate[cc:{__?QubitQ}, tt_List, opts___?OptionQ ] :=
  UniformlyControlledGate[cc, Dagger[Reverse @ tt], opts]

UniformlyControlledGate /:
Unfold[
  UniformlyControlledGate[cc:{__?QubitQ}, tt_List, opts___?OptionQ],
  ___ 
] := Module[
  { nn = Power[2, Length @ cc],
    mint = Lookup[Flatten @ {opts}, "Label"] },
  mint = Switch[ mint,
    None, Table[None, nn],
    _?MissingQ, {},
    _List, PadRight[mint, nn, mint],
    Automatic, Thread @ Subscript["U", Range[nn]-1],
    _, Thread @ Subscript[mint, Range[nn]-1]
  ];
  QuantumCircuit @@ ReleaseHold @ Thread @
  ControlledGate[
    Thread[Hold[cc] -> Tuples[{0, 1}, Length @ cc]],
    tt,
    If[mint == {}, Hold[], Thread["Label" -> mint]],
    Hold[opts]
  ]
]

UniformlyControlledGate /:
Matrix[
  op:UniformlyControlledGate[{__?QubitQ}, _List, ___],
  rest___ ] := Matrix[Unfold @ op, rest]


UniformlyControlledGate /:
Elaborate @
  op:UniformlyControlledGate[{__?QubitQ}, _List, ___?OptionQ] :=
  With[{qq = Qubits @ op}, Elaborate @ ExpressionFor[Matrix[op, qq], qq]]


UniformlyControlledGate /:
Multiply[ pre___,
  op:UniformlyControlledGate[{__?QubitQ}, _List, ___?OptionQ],
  in_Ket ] := With[
    { gg = List @@ Unfold[op] },
    Multiply[pre, Fold[Multiply[#2, #1]&, in, gg]]
   ]

(*
Multiply[ pre___,
  op:UniformlyControlledGate[{__?QubitQ}, _List, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
 *)
(* NOTE: DO NOT put "UniformlyControlledGate /:". Otherwise, the above
   rule with UniformlyControlledGate[...]**Ket[] is overridden. *)

(**** </UniformlyControlledGate> ****)


(**** <Oracle/Classical> ****)

Oracle::range = "Input value `` is out of the domain of function `` from ``-bit string to ``-bit string; Mod[`1`,Power[2,`3`]] is used.";

Oracle::undef = "Function `` from ``-bit string to ``-bit string is ill-defined at ``.";

Oracle[f_, m_Integer, n_Integer][x_Integer] :=
  Oracle[f, m, n][IntegerDigits[x, 2, m]] /;
  0 <= x < Power[2, m]

Oracle[f_, m_Integer, n_Integer][x_Integer] := (
  Message[Oracle::range, x, f, m, n];
  Oracle[f, m, n][IntegerDigits[x, 2, m]]
 )

Oracle[f_, m_Integer, n_Integer][x:{(0|1) ..}] := Module[
  { y = f[x] },
  Switch[y,
    {Repeated[0|1, {n}]}, y,
    _Integer, IntegerDigits[y, 2, n],
    _, (
      y = f[FromDigits[x, 2]];
      Switch[y,
        {Repeated[0|1, {n}]}, y,
        _Integer, IntegerDigits[y, 2, n],
        _, Message[Oracle::undef, f, m, n, x]; 0]
     )
   ]
 ]

(**** </Oracle/Classical> ****)


(**** <Oracle> ****)

Oracle::usage = "Oracle[f, control, target] represents the quantum oracle which maps Ket[x]\[CircleTimes]Ket[y] to Ket[x]\[CircleTimes]Ket[f(x)\[CirclePlus]y]. Each control and target can be list of qubits.\nOracle[f, m, n] represents the classical oracle f:{0,1}^m \[RightArrow] {0,1}^n that provides the flexibility for input form while keeping the consistency of output form."

Oracle /:
NonCommutativeQ[ Oracle[___] ] = True

Oracle[f_, c_?QubitQ, t_?QubitQ, opts___?OptionQ] :=
  Oracle[f, {c}, {t}, opts]

Oracle[f_, c_?QubitQ, tt:{__?QubitQ}, opts___?OptionQ] :=
  Oracle[f, {c}, tt, opts]

Oracle[f_, cc:{__?QubitQ}, t_?QubitQ, opts___?OptionQ] :=
  Oracle[f, cc, {t}, opts]

Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  Oracle[f, FlavorCap @ cc, FlavorCap @ tt, opts] /;
  Not[FlavorCapQ @ Join[cc, tt]]

Oracle /:
Dagger[op_Oracle] := op

Oracle /:
HoldPattern @ Multiply[pre___, op_Oracle, post___] :=
  Multiply[pre, Elaborate[op], post]


Oracle /:
Elaborate @ Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, ___] := Module[
  { bb = Range[Power[2, Length @ cc]] },
  bb = GroupBy[
    IntegerDigits[bb-1, 2, Length @ cc],
    Oracle[f, Length @ cc, Length @ tt]
  ] /. {0 -> 10, 1 -> 11};
  bb = Total /@ Map[Apply[Multiply], Map[FlavorThread[cc], bb], {2}];
  bb = KeyMap[Apply[Multiply] @* FlavorThread[tt], bb];
  Elaborate @ Total @ KeyValueMap[Multiply, bb]
 ]


Oracle /:
Matrix[op:Oracle[_, cc:{__?QubitQ}, tt:{__?QubitQ}], qq:{__?QubitQ}] :=
  MatrixEmbed[Matrix @ op, Join[cc, tt], qq]

Oracle /:
Matrix @ Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, ___] := Module[
  { bb = Range[Power[2, Length @ cc]] }, 
  bb = GroupBy[
    IntegerDigits[bb-1, 2, Length @ cc], 
    Oracle[f, Length @ cc, Length @ tt]
  ] /. {0 -> 10, 1 -> 11};
  bb = KeyMap[
    ThePauli,
    Total /@ Map[ThePauli, bb, {2}]
  ];
  Total @ KeyValueMap[KroneckerProduct[#2, #1]&, bb]
]

(**** </Oracle> ****)


(**** <QFT> ****)

QFT::usage = "QFT[{S1, S2, \[Ellipsis]}] represents the quantum Fourier transform on the qubits S1, S2, \[Ellipsis].\nDagger[QFT[\[Ellipsis]]] represents the inverse quantum Fourier transform.\nElaborate[QFT[\[Ellipsis]]] returns the explicit expression of the operator in terms of the Pauli operators."

QFT::mat = "Some elements of `` do not appear in `` for Matrix[QFT[\[Ellipsis]]]."

SetAttributes[QFT, NHoldAll];

Options[QFT] = {
  "Label" -> "QFT",
  "ApproximationLevel" -> Full,
  "Numeric" -> False,
  "Reversed" -> False,
  "Pushed" -> False
}

QFT /:
NonCommutativeQ[ QFT[___] ] = True

QFT /:
MultiplyKind @ QFT[_, {__?QubitQ}, ___?OptionQ] = Qubit


QFT[S_?QubitQ, rest___] := QFT[1, {S}, rest]

QFT[type_, S_?QubitQ, rest___] := QFT[type, S @ {$}, rest]

QFT[ss:{___?QubitQ}, rest___] := QFT[1, FlavorCap @ ss, rest]

QFT[type_, ss:{__?QubitQ}, rest___] :=
  QFT[type, FlavorCap @ ss, rest] /; Not[FlavorCapQ @ ss]

QFT[-1|1, {}, ___] = 1

QFT /:
N[ QFT[type_, ss:{___?QubitQ}, opts___?OptionQ] ] :=
  QFT[type, ss, "Numeric" -> True, opts] /; 
  Not["Numeric" /. {opts} /. Options[QFT]]

QFT /:
Dagger[ op:QFT[type:-1|1, rest___] ] := QFT[-type, rest]

QFT /: 
Elaborate[op_QFT] = op (* fallback *)

QFT /:
Elaborate[op:QFT[_, ss:{__?QubitQ}, ___]] :=
  Elaborate @ ExpressionFor[Matrix[op, ss], ss]


QFT /:
Matrix[op_QFT, tt:{___?QubitQ}] := 
  op * One @ Power[2, Length @ tt] (* fallback *)

QFT /:
Matrix[QFT[type:(-1|1), ss:{__?QubitQ}, opts___?OptionQ], tt:{__?QubitQ}] := 
  Module[
    { mat },
    mat = FourierMatrix[
      Power[2, Length @ ss],
      FourierParameters -> {0, type}
    ];
    If[OptionValue[QFT, {opts}, "Numeric"], mat = N[mat]];
    MatrixEmbed[mat, ss, FlavorCap @ tt]
  ] /; ContainsAll[FlavorCap @ tt, ss]
(* TODO: Handle the "ApproximationLevel" option. *)

QFT /:
Matrix[QFT[_, ss:{__?QubitQ}, ___], tt:{__?QubitQ}] := (
  Message[QFT::mat, ss, FlavorCap @ tt];
  One @ Power[2, Length @ tt]
)


QFT /:
MultiplyPower[op:QFT[_, ss_List, ___], n_Integer] :=
  Switch[ Mod[n, 4],
    0, 1,
    1, op,
    2, QCR[ss],
    3, Dagger[op]
  ]


QFT /:
Multiply[pre___, QFT[type_, ss_List, ___], QFT[type_, ss_List, ___], post___] :=
  Multiply[pre, QCR[ss], post]

QFT /:
Multiply[pre___, QFT[m:(-1|1), ss_, ___], QFT[n:(-1|1), ss_, ___], post___] :=
  Multiply[pre, post] /; m + n == 0

QFT /:
HoldPattern @ Multiply[pre___, QCR[ss_List, ___], op:QFT[_, ss_List, ___], post___] :=
  Multiply[pre, Dagger @ op, post]

QFT /:
HoldPattern @ Multiply[pre___, op:QFT[_, ss_List, ___], QCR[ss_List, ___], post___] :=
  Multiply[pre, Dagger @ op, post]


QFT /:
Multiply[pre___, op:QFT[type_, ss:{__?QubitQ}, opts___?OptionQ], in_Ket] :=
  Garner @ Module[
    { k = FromDigits[in[ss], 2],
      L = Power[2, Length @ ss],
      v },
    v = Exp[type * (2*Pi*I) * Range[0, L-1] * k / L] / Sqrt[L];
    If[OptionValue[QFT, {opts}, "Numeric"], v = N[v]];
    Dot[Basis[ss], v] ** Ket[KeyDrop[First @ in, ss]]
  ]
(* TODO: Handle the "ApproximationLevel" option. *)

QFT /:
Multiply[in_Bra, op_QFT, post___] :=
  Multiply[ Dagger[Dagger[op] ** Dagger[in]], post ]

QFT /:
Multiply[pre___, op:QFT[_, ss_List, ___], Dyad[a_Association, b_Association], post___] :=
  Multiply[pre, Multiply[op ** Ket[a], Bra[b]], post] /; ContainsAll[Keys @ a, ss]

QFT /:
Multiply[pre___, Dyad[a_Association, b_Association], op:QFT[_, ss_List, ___], post___] :=
  Multiply[pre, Multiply[Ket[a], Bra[b] ** op], post] /; ContainsAll[Keys @ b, ss]


QFT /:
Unfold[op_QFT, ___] = op (* fallback *)

QFT /:
Unfold[QFT[type:(-1|1), ss:{__?QubitQ}, opts___?OptionQ], more___?OptionQ] := 
  Module[
    { flag = OptionValue[QFT, {more, opts}, "Numeric"],
      rvrs = OptionValue[QFT, {more, opts}, "Reversed"],
      elm },
    elm = qftCtrlPower[flag, type, ss][All];
    If[ rvrs,
      elm = QBR[ss] /@ Reverse[elm] /. {
        cp_ControlledPower :> ReplaceRulesBy[cp, "ControlLabel" -> OverTilde]
      }
    ];
    Append[QuantumCircuit @@ elm, QBR @ ss]
  ]


qftCtrlPower[flag_, type_, ss:{__?QubitQ}][All] := Flatten @
  Map[qftCtrlPower[flag, type, ss], Range @ Length @ ss]

qftCtrlPower[flag_, _, ss:{__?QubitQ}][k_Integer] := 
  { Last[ss][6] } /; Length[ss] == k

qftCtrlPower[flag_, -1, ss:{__?QubitQ}][k_Integer] :=
  Dagger[ qftCtrlPower[flag, 1, ss][k] ]

qftCtrlPower[flag_, 1, ss:{__?QubitQ}][k_Integer] := With[
  { n = Length[ss],
    T = ss[[k]] },
  { T[6],
    ControlledPower[
      Drop[ss, k],
      If[ flag, 
        Phase[ N[2*Pi/Power[2, n-k+1]], T[3], 
          "Label" -> thePauliForm @ T[C[n-k+1]] 
        ], 
        T[C[n-k+1]] 
      ],
      "ControlLabel" -> "x"
    ]
  }
]


QFT /:
UnfoldAll[op_QFT, ___] = op (* fallback *)

QFT /:
UnfoldAll[
  op:QFT[type:(-1|1), ss:{__?QubitQ}, opts___?OptionQ], 
  more___?OptionQ
] :=
Module[
  { flag = OptionValue[QFT, {more, opts}, "Numeric"],
    rvrs = OptionValue[QFT, {more, opts}, "Reversed"],
    push = OptionValue[QFT, {more, opts}, "Pushed"],
    aprx = OptionValue[QFT, {more, opts}, "ApproximationLevel"],
    elm },
  If[aprx === Full, aprx = Length[ss]];
  elm = If[ push,
    qftPushPhase[type, ss, flag, aprx][All],
    qftCtrlPhase[type, ss, flag, aprx][All]
  ];
  If[rvrs, elm = QBR[ss] /@ Reverse[elm]];
  Append[QuantumCircuit @@ elm, QBR @ ss]
]


qftCtrlPhase[type_, ss:{__?QubitQ}, flag_, m_Integer][All] := Flatten @
  Map[qftCtrlPhase[type, ss, flag, m], Range @ Length @ ss]

qftCtrlPhase[-1, ss:{__?QubitQ}, flag_, m_Integer][k_Integer] :=
  Dagger[ qftCtrlPhase[1, ss, flag, m][k] ]

qftCtrlPhase[+1, ss:{__?QubitQ}, flag_, m_Integer][k_Integer] :=
  Module[
    { n = Length[ss],
      T = ss[[k]] },
    Prepend[
      Table[
        ControlledGate[
          ss[[{j}]] -> {1},
          If[ flag, 
            Phase[ N[2*Pi*Power[2, k-j-1]], T[3], "Label" -> thePauliForm @ T[C[j-k+1]] ], 
            T[C[j-k+1]]
          ]
        ],
        {j, k+1, Min[k+m-1, n]} ],
      T[6]
    ]
  ]

(* See Coppersmith (1994) *)
qftPushPhase[type_, ss:{__?QubitQ}, flag_, m_Integer][All] := Flatten @
  Map[qftPushPhase[type, ss, flag, m], Range @ Length @ ss]

qftPushPhase[-1, ss:{__?QubitQ}, flag_, m_Integer][k_Integer] :=
  Dagger[ qftPushPhase[1, ss, flag, m][k] ]

qftPushPhase[+1, ss:{__?QubitQ}, flag_, m_Integer][k_Integer] :=
  Module[
    { n = Length @ ss,
      T },
    Append[
      Table[
        T = ss[[j]];
        ControlledGate[
          ss[[{k}]] -> {1},
          If[ flag,
            Phase[ N[2*Pi/Power[2, k-j+1]], T[3], "Label" -> thePauliForm @ T[C[k-j+1]] ], 
            T[C[k-j+1]]
          ]
        ],
        {j, Max[1, k-m+1], k-1} ],
      ss[[k]][6]
    ]
  ]

(**** </QFT> ****)


(**** <QBR> ****)

QBR::usage = "QBR[{s1, s2, \[Ellipsis]}] represents the quantum bit-reversal transform on the qubits s1, s2, \[Ellipsis].\nQBR is a generalization of the SWAP gate for more than two qubits."

QBR::mat = "Some elements of `` do not appear in `` for Matrix[QBR[\[Ellipsis]]]."

QBR /: 
NonCommutativeQ[ QBR[___] ] = True

QBR /:
MultiplyKind @ QBR[{__?QubitQ}] = Qubit


QBR /:
Dagger[ op_QBR ] := op


QBR[{}] = 1

QBR[S_?QubitQ, ___] = 1

QBR[{S_?QubitQ}, ___] = 1

QBR[qq:{__?QubitQ}, opts___] :=
  QBR[FlavorCap @ qq, opts] /;
  Not[FlavorCapQ @ qq]


QBR /: 
Elaborate[op_QBR] = op (* fallback *)

QBR /:
Elaborate[op:QBR[{__?QubitQ}, ___]] :=
  Elaborate @ ExpressionFor[Matrix[op], Qubits @ op]


QBR /:
Matrix[QBR[ss:{__?QubitQ}, ___], tt:{__?QubitQ}] := Module[
  { L = Power[2, Length @ ss],
    ii, jj, mm },
  ii = Range[L] - 1;
  jj = FromDigits[#, 2]& /@ Reverse /@ IntegerDigits[ii, 2, Length @ ss];
  mm = SparseArray[Thread @ Rule[Transpose @ {ii+1, jj+1}, 1], {L, L}];
  MatrixEmbed[mm, ss, tt]
] /; ContainsAll[tt, ss]

QBR /:
Matrix[QBR[qq:{__?QubitQ}, ___], ss:{__?QubitQ}] := (
  Message[QBR::mat, FlavorCap @ qq, FlavorCap @ ss];
  One @ Power[2, Length @ ss]
)


QBR /:
Multiply[pre___, QBR[ss_List, ___], QBR[ss_List, ___], post___] :=
  Multiply[pre, post]


QBR /:
Multiply[pre___, op:QBR[ss:{__?QubitQ}, ___], in:Ket[aa_Association]] :=
  Multiply[ pre, Ket[in, ss -> Reverse[Lookup[aa, ss]]] ]

QBR /:
Multiply[in_Bra, op_QBR, post___] :=
  Multiply[ Dagger[op ** Dagger[in]], post ]

QBR /:
Multiply[pre___, op:QBR[ss_List, ___], Dyad[a_Association, b_Association], post___] :=
  Multiply[pre, Multiply[op ** Ket[a], Bra[b]], post] /; ContainsAll[Keys @ a, ss]

QBR /:
Multiply[pre___, Dyad[a_Association, b_Association], op:QBR[ss_List, ___], post___] :=
  Multiply[pre, Ket[a], Multiply[Bra[b] ** op], post] /; ContainsAll[Keys @ b, ss]


QBR /:
Multiply[pre___, QBR[ss_List, ___], aa__, QBR[ss_List, ___], post___] :=
  Multiply[pre, Multiply @@ Map[QBR[ss], {aa}], post]

QBR[ss:{___?QubitQ}, ___][qc_QuantumCircuit] :=
  Map[QBR[ss], qc]

QBR[ss:{___?QubitQ}, ___][expr_] := Module[
  { rr },
  rr = Thread[ Through[ss[k_]] -> Reverse @ Through[ss[k]] ];
  expr /. rr
]


QBR /:
Unfold[op_QBR, ___] = op (* fallback *)

QBR /:
Unfold[QBR[ss:{__?QubitQ}, ___], ___] :=
  QuantumCircuit @@ Table[ SWAP[ss[[k]], ss[[-k]]], {k, Length[ss]/2} ]


QBR /:
UnfoldAll[op_QBR, ___] = op (* fallback *)

QBR /:
UnfoldAll[op:QBR[ss:{__?QubitQ}, ___], ___] := 
  Unfold[Unfold @ op]

(**** </QBR> ****)


(**** <QCR> ****)

QCR::usage = "QCR[{s1, s2, \[Ellipsis]}] represents the quantum circle reflection on the qubits s1, s2, \[Ellipsis]."

QCR::mat = "Some elements of `` do not appear in `` for Matrix[QCR[\[Ellipsis]]]."

QCR /: 
NonCommutativeQ[ QCR[___] ] = True

QCR /:
MultiplyKind @ QCR[{__?QubitQ}] = Qubit


QCR /:
Dagger[ op_QCR ] := op


QCR[{}] = 1

QCR[S_?QubitQ, ___] = 1

QCR[{S_?QubitQ}, ___] = 1

QCR[qq:{__?QubitQ}, opts___] :=
  QCR[FlavorCap @ qq, opts] /;
  Not[FlavorCapQ @ qq]


QCR /: 
Elaborate[op_QCR] = op (* fallback *)

QCR /:
Elaborate[op:QCR[{__?QubitQ}, ___]] :=
  Elaborate @ ExpressionFor[Matrix[op], Qubits @ op]


QCR /:
Matrix[QCR[ss:{__?QubitQ}, ___], tt:{__?QubitQ}] := Module[
  { L = Power[2, Length @ ss],
    ii, jj, mm },
  ii = Range[L];
  jj = Prepend[Reverse @ Rest @ ii, 1];
  mm = SparseArray[Thread @ Rule[Transpose @ {ii, jj}, 1], {L, L}];
  MatrixEmbed[mm, ss, tt]
] /; ContainsAll[tt, ss]

QCR /:
Matrix[QCR[qq:{__?QubitQ}, ___], ss:{__?QubitQ}] := (
  Message[QCR::mat, FlavorCap @ qq, FlavorCap @ ss];
  One @ Power[2, Length @ ss]
)


QCR /:
Multiply[pre___, QCR[ss_List, ___], QCR[ss_List, ___], post___] :=
  Multiply[pre, post]


QCR /:
Multiply[pre___, op:QCR[ss:{__?QubitQ}, ___], in:Ket[aa_Association]] :=
  With[
    { vv = Power[2, Length @ ss] - FromDigits[Lookup[aa, ss], 2] },
    Multiply[ pre, Ket[in, ss -> IntegerDigits[vv, 2, Length @ ss]] ]
  ]

QCR /:
Multiply[in_Bra, op_QCR, post___] :=
  Multiply[ Dagger[op ** Dagger[in]], post ]

QCR /:
Multiply[pre___, op:QCR[ss_List, ___], Dyad[a_Association, b_Association], post___] :=
  Multiply[pre, Multiply[op ** Ket[a], Bra[b]], post] /; ContainsAll[Keys @ a, ss]

QCR /:
Multiply[pre___, Dyad[a_Association, b_Association], op:QCR[ss_List, ___], post___] :=
  Multiply[pre, Ket[a], Multiply[Bra[b] ** op], post] /; ContainsAll[Keys @ b, ss]


QCR /:
Unfold[op_QCR, ___] = op (* fallback *)

QCR /:
Unfold[op:QCR[ss:{__?QubitQ}, ___], ___] := With[
  { qft = Drop[Unfold[QFT @ ss], -2] },
  QuantumCircuit[qft, Reverse @ qft]
]


QCR /:
UnfoldAll[op_QCR, ___] = op (* fallback *)

QCR /:
UnfoldAll[op:QCR[ss:{__?QubitQ}, ___], ___] := With[
  { qft = Drop[UnfoldAll[QFT @ ss], -2] },
  QuantumCircuit[qft, Reverse @ qft]
]

(**** </QCR> ****)


(**** <Projector> ****)

Projector::usage = "Projector[state, {q1, q2, ...}] represents the projection operator on the qubits {q1, q2, ...} into state, which is given in the Ket expression.\nProjector[expr] automatically extracts the list of qubits from expr."

Projector::noket = "No Ket expression found for projection in the provided expression ``. Identity operator is returned."

Projector /:
Dagger[ op_Projector ] = op

Projector /:
Unfold[Projector[v_, qq_List], ___] := Dyad[v, v, qq]

Projector /:
DyadForm[ Projector[v_, qq_List] ] := Dyad[v, v, qq]

Projector /:
Elaborate[ op:Projector[_, _List] ] := Elaborate[Unfold @ op]

Projector /:
Matrix[ op:Projector[_, _List], qq:{__?SpeciesQ}] :=
  Matrix[Elaborate[op], qq]


Projector[expr_, {}] = 1

Projector[expr_] := Projector[expr, Qubits @ expr]

Projector[expr_, q_?QubitQ] := Projector[expr, q @ {$}]

Projector[expr_, qq:{__?QubitQ}] :=
  Projector[expr, FlavorCap @ qq] /; Not[FlavorCapQ @ qq]

Projector[expr_, qq:{__?QubitQ}] :=
  (Message[Projector::noket, expr]; 1) /; FreeQ[expr, _Ket]

(**** </Projector> ****)


(**** <MeasurementOdds> ****)

MeasurementOdds::usage = "MeasurementOdds[op][vec] theoretically analyzes the process of meauring operator op on state vec and returns an association of elements of the form value->{probability, state}, where value is one of the possible measurement outcomes 0 and 1 (which correspond to eitemvalues +1 and -1, respectively, of op), probability is the probability for value to be actually observed, and state is the post-measurement state when value is actually observed."

MeasurementOdds::pauli = "`` is not an observable Pauli operator."

SyntaxInformation[MeasurementOdds] = { "ArgumentsPattern" -> {_} }

MeasurementOdds[Measurement[op_]] := MeasurementOdds[op]

(* NOTE: DO NOT use op_?PauliQ; it will inerfere with mat_?MatrixQ below.
   NOTE ADDED: Maybe not any longer (v3.4.4) because PauliQ and PauliMatrixQ are now separate. *)
MeasurementOdds[op_][vec:(_State|_?fKetQ)] := Module[
  { ss = Qubits[{vec, op}],
    aa, ff },
  If[ Not[obsPauliQ @ op],
    Message[MeasurementOdds::pauli, op];
    Return[<|0 -> {1, Ket[]}, 1 -> {0, 0}|>]
  ];
  aa = MeasurementOdds[Matrix[op, ss]][Matrix[vec, ss]];
  ff = If[Head[vec] === State, State, ExpressionFor];
  aa[0] = {First @ aa[0], ff[Last @ aa[0], ss]};
  aa[1] = {First @ aa[1], ff[Last @ aa[1], ss]};
  Return[aa]
]

MeasurementOdds[mat_?MatrixQ][vec_?VectorQ] := Module[
  { new = mat . vec,
    pls, mns, p0, p1 },
  pls = (vec + new)/2;
  mns = (vec - new)/2;
  p0 = Simplify @ Norm[pls]^2;
  p1 = Simplify @ Norm[mns]^2;
  If[ AllTrue[vec, NumericQ],
    pls = Normalize @ pls;
    mns = Normalize @ mns
  ];
  Association[
    0 -> {p0/(p0+p1), pls},
    1 -> {p1/(p0+p1), mns}
  ]
] (* /; PauliMatrixQ[mat] *)
(* NOTE: Test PauliMatrixQ[mat] may take long for 8 or more qubits. *)
(* NOTE:
   1. vec, pls, or mns may be 0 (null vector).
   2. The norms of pls and mns may have imaginary parts numerically.
   3. When the vector components are symbolic,
      the post-measurement states are NOT normalized.
   *)


obsPauliQ::usage = "obsPauliQ[op] returns True if op is a Pauli string (without any factor of \[PlusMinus]I); and False, otherwise.\nSuch an 'observable' Pauli operator has eigenvalue \[PlusMinus]1; hence 'observable'."

obsPauliQ[Pauli[(0|1|2|3)..]] = True

obsPauliQ[_?QubitQ[___, 0|1|2|3]] = True

obsPauliQ[HoldPattern @ Multiply[(_?QubitQ[___, 0|1|2|3])..]] = True

obsPauliQ[expr_] := obsPauliQ[Elaborate @ expr] /;
  Not @ FreeQ[expr, _?QubitQ[___, 4|5|6|7|8|9|10|11]]

obsPauliQ[_] = False

(**** </MeasurementOdds> ****)


(***** <Measurement> ****)

Measurement::usage = "Measurement[op] represents the measurement of Pauli operator op. Pauli operators include tensor products of the single-qubit Pauli operators.\nMeasurement[{op1, op2, \[Ellipsis]}] represents consecutive measurement of Pauli operators op1, op2, \[Ellipsis] in the reverse order."

Measurement::num = "Probability half is assumed for a state without explicitly numeric coefficients."

Measurement::non = "Matrix `` does not represent a Pauli string."

SyntaxInformation[Measurement] = { "ArgumentsPattern" -> {_} }

Measurement /:
MakeBoxes[msr:Measurement[mat_?MatrixQ, ___], fmt_] := Module[
  { mm = First @ Keys @ PauliCoefficients[mat] },
  BoxForm`ArrangeSummaryBox[
    Measurement, msr, None,
    { BoxForm`SummaryItem @ { Pauli @ DeleteCases[mm, 0] },
      BoxForm`SummaryItem @ { 
        Flatten @ Position[mm, Except[0], {1}, Heads -> False],
        " of ",
        Length[mm]
      }
    },
    { },
    fmt,
    "Interpretable" -> Automatic
  ]
] /; If[ PauliMatrixQ[mat], True,
    Message[Measurement::non, mat];
    False
  ]

Measurement[op_?MatrixQ][in_?VectorQ] := theMeasurement[in, op]

Measurement[op_List][in_] := Fold[theMeasurement, in , Reverse @ op]
(* NOTE: Here, Reverse is for backward compatibility. *)

Measurement[op_][in_] := theMeasurement[in, op]


theMeasurement::usage = "The actual workhorse."

theMeasurement[in_, op_] := Module[
  { odds = MeasurementOdds[op][in],
    rand = RandomReal[],
    prob },
  prob = If[ NumericQ[First @ odds[0]],
    Re[First @ odds[0]],
    Message[Measurement::num];
    0.5
  ];
  Garner @ If[ rand < prob,
    $MeasurementOut[op] = 0; Last @ odds[0],
    $MeasurementOut[op] = 1; Last @ odds[1]
  ]
]


Measurement /:
Dot[Measurement[mm:(_?MatrixQ|{___?MatrixQ})], vec_?VectorQ] :=
  Measurement[mm] @ vec

Measurement /:
Multiply[pre___, msr_Measurement, post__] :=
  Multiply[pre, msr @ Multiply[post]] /; 
  Not @ FreeQ[Last @ {post}, _Ket|_State]

Measurement /:
Multiply[pre___, msr_Measurement, post___] :=
  MeasurementFunction[pre, msr, post]

Measurement /:
Matrix[Measurement[op_], ss:{___?SpeciesQ}] :=
  Measurement[Matrix[op, ss]]

(**** </Measurement> ****)


(**** <MeasurementFunction> ****)

MeasurementFunction::usage = "MeasurementFunction[{m1,m2,\[Ellipsis]}] represents a sequence of operations or measurements m1, m2, \[Ellipsis]."

Format[fun:MeasurementFunction[gg:(_?MatrixQ|Measurement[_?MatrixQ]|Measurement[{__?MatrixQ}])..]] := With[
  { dim = Riffle[Dimensions @ FirstCase[{gg}, _?MatrixQ, {{1}}, 3], "\[Times]"] },
  Interpretation[
    StringForm["MeasurementFunction[{``\[Ellipsis]}]", ToString @ Row @ dim],
    fun
  ]
]

Format[fun:MeasurementFunction[gg__]] := 
  Interpretation[
    StringForm["MeasurementFunction[``]", Qubits @ {gg}],
    fun
  ]

MeasurementFunction[mm:(_Measurement|_?MatrixQ)..][in_?VectorQ] :=
  Fold[Dot[#2, #1]&, in, Reverse @ {mm}]

MeasurementFunction[mm__][in_] :=
  Fold[Garner[Multiply[#2, #1]]&, in, Reverse @ {mm}] /;
  Not @ FreeQ[in, Ket[_Association]|_ProductState]


MeasurementFunction /:
Dot[MeasurementFunction[mm:(_Measurement|_?MatrixQ)..], in_?VectorQ] :=
  MeasurementFunction[mm][in]

MeasurementFunction /:
Multiply[pre___, spr_MeasurementFunction, post___] :=
  Multiply[pre, Sequence @@ spr, post]

(**** </MeasurementFunction> ****)


(**** <Readout> ****)

$MeasurementOut::usage = "$MeasurementOut gives the measurement results in an Association of elements op$j->value$j."


Readout::usage = "Readout[expr, S] or Readout[expr, {S1, S2, ...}] reads the measurement result from the expr that is supposed to be the state vector after measurements."

Readout::notob = "`` (or some of its elements if it is a list) has never been measured. First use Measurement before using Readout."

SyntaxInformation[Readout] = { "ArgumentsPattern" -> {_} }

Readout[Measurement[op_]] := Readout[op]

Readout[op_?MatrixQ] := $MeasurementOut[op] /; KeyExistsQ[$MeasurementOut, op]

Readout[op_List] := Lookup[$MeasurementOut, op] /; ContainsAll[Keys @ $MeasurementOut, op]
(* NOTE: op may be a list of matrices or operators. *)

Readout[op_] := $MeasurementOut[op] /; KeyExistsQ[$MeasurementOut, op]


Readout[op_] := (
  Message[Readout::notob, op];
  $Failed
)

(**** </Readout> ****)


Measurements::usage = "Measurments[expr] returns a list of Pauli operators (including the tensor products of single-qubit Pauli operators) measured during the process of expression expr."

Measurements[expr_] := Union @ Flatten @
  Cases[{expr}, Measurement[m_] -> m, Infinity, Heads -> False]


(**** <ProductState> ****)

ProductState::usage = "ProductState[<|...|>] is similar to Ket[...] but reserved only for product states. ProductState[<|..., S -> {a, b}, ...|>] represents the qubit S is in a linear combination of a Ket[0] + b Ket[1]."

ProductState::pair = "The value must be a pair of complex numbers or a list of such pairs instead of ``."

Options[ProductState] = {"Label" -> None}

AddGarnerPatterns[_ProductState]

Format @ ProductState[assoc:Association[], rest___] :=
  Interpretation[Ket[Any], ProductState[assoc, rest]]

Format @ ProductState[assoc_Association, rest___] := Interpretation[
  CircleTimes @@ KeyValueMap[
    DisplayForm @ Subscript[RowBox @ {"(", {Ket[0], Ket[1]}.#2, ")"}, #1]&,
    assoc
  ],
  ProductState[assoc, rest]
]

ProductState /:
KetRegulate[ProductState[a_Association, opts___?OptionQ], gg_List] :=
  Module[
    { ss = Union[Keys @ a, FlavorCap @ gg] },
    Block[
      { Missing },
      Missing["KeyAbsent", _Symbol?QubitQ[___, $]] := {1, 0};
      ProductState[AssociationThread[ss -> Lookup[a, ss]], opts]
    ]
  ]


ProductState /:
Unfold[ProductState[aa_Association, opts___?OptionQ], ___] :=
  State[CircleTimes @@ Values[aa], Keys @ aa]

ProductState /:
Elaborate[ vec:ProductState[_Association, ___] ] :=
  Elaborate[Unfold @ vec]

ProductState /:
Matrix[ ket_ProductState, rest___ ] :=
  Matrix[Unfold @ ket, rest]


ProductState /:
NonCommutativeQ[ ProductState[___] ] = True

ProductState /:
MultiplyKind[ ProductState[___] ] = Ket

ProductState /:
MultiplyGenus[ ProductState[___] ] = "Ket"


ProductState /:
Multiply[pre___, ps:ProductState[aa_Association, ___], Ket[bb_Association], post___] :=
  Multiply[ pre,
    ProductState[ps, Sequence @@ Normal @ Map[TheKet, bb]],
    post ]

ProductState /:
Multiply[pre___, Ket[bb_Association], ps:ProductState[aa_Association, ___], post___] :=
  Multiply[ pre,
    ProductState[ps, Sequence @@ Normal @ Map[TheKet, bb]],
    post ]

ProductState /:
Multiply[pre___, S_?QubitQ, in:ProductState[_Association, ___], post___] :=
  Multiply[ pre, 
    ProductState[in, FlavorMute[S] -> TheMatrix[S] . in[FlavorMute @ S]],
    post ]

ProductState /:
Multiply[ pre___, 
  op:Rotation[_, _List, S_?QubitQ, ___],
  in:ProductState[aa_Association, ___], 
  post___
] :=
  Multiply[ 
    pre, 
    ProductState[in, S -> Matrix[op] . Lookup[aa, S]],
    post 
  ]

ProductState /:
Multiply[ pre___,
  op:Phase[_, S_?QubitQ, ___],
  in:ProductState[aa_Association, ___], 
  post___
] :=
  Multiply[ 
    pre,
    ProductState[in, FlavorMute[S] -> Matrix[op] . Lookup[aa, FlavorMute @ S]],
    post 
  ]

ProductState /:
Multiply[pre___, op_Measurement, in_ProductState, post___] :=
  Multiply[pre, op[Unfold @ in], post]

ProductState /:
Multiply[pre___, op_, in_ProductState, post___] :=
  Multiply[pre, Multiply[op, Unfold @ in], post]

(* 
HoldPattern @
  Multiply[pre___, vec:ProductState[_Association, ___], post___] :=
  Garner @ Multiply[pre, Elaborate[vec], post]
 *)


(* input specifications *)

ProductState[spec___Rule, ss:{__?QubitQ}, opts___?OptionQ] :=
  KetRegulate[ProductState[spec, opts], ss]

ProductState[v:ProductState[_Association, ___], spec___Rule, ss:{__?QubitQ}] :=
  KetRegulate[ProductState[v, spec], ss]


ProductState[] = ProductState[<||>]

ProductState[spec___Rule] := ProductState[ProductState[<||>], spec]

ProductState[v:ProductState[_Association, ___], spec_Rule, more__Rule] :=
  Fold[ProductState, v, {spec, more}]


ProductState[v:ProductState[_Association, ___], spec:Rule[_String, _]] :=
  Append[v, spec] /; Not[AgentQ @ First @ spec]

ProductState[ ProductState[a_Association, opts___],
  rule:Rule[_?QubitQ, {_, _}] ] :=
  ProductState[KeySort @ Append[a, FlavorCap @ rule], opts]

ProductState[
  ProductState[a_Association, opts___],
  rule:Rule[{__?QubitQ}, {{_, _}..}]
 ] := ProductState[
   KeySort @ Join[a, AssociationThread[FlavorCap /@ rule]],
   opts
  ]

ProductState[
  ProductState[a_Association, opts___],
  Rule[gg:{__?QubitQ}, v:{_, _}]
 ] := With[
   { b = AssociationMap[(v)&, FlavorCap @ gg] },
   ProductState[ KeySort @ Join[a, b], opts ]
  ]


ProductState[ a:ProductState[_Association, ___], Rule[_?QubitQ, v_] ] :=
  (Message[ProductState::pair, v]; a)

ProductState[ a:ProductState[_Association, ___], Rule[{__?QubitQ}, v_List]] :=
  (Message[ProductState::pair, v]; a)

ProductState[ a:ProductState[_Association, ___], Rule[{__?QubitQ}, v_]] :=
  (Message[ProductState::pair, v]; a)

(* Resetting the qubit values *)

ProductState[a_Association, otps___][v__Rule] :=
  ProductState[ ProductState[a, opts], v ]

(* Assessing the qubit values *)

ProductState[a_Association, opts___][qq:(_?QubitQ | {__?QubitQ})] :=
  Block[
    { Missing },
    Missing["KeyAbsent", _Symbol?QubitQ[___, $]] := {1, 0};
    Lookup[a, FlavorCap @ qq]
   ]

(**** </ProductState> ****)


BellState::usage = "BellState[{S$1, S$2}, n] with n=0,1,2,3 gives the nth Bell states on the two qubits S$1 and S$2.
  BellState[{S$1, S$2}] returns the list of all Bell states."

BellState[g:{_?QubitQ, _?QubitQ}] :=
  Table[ BellState[g, j], {j, 0, 3} ]

BellState[g:{_?QubitQ, _?QubitQ}, 0] :=
  ( Ket[g->{0,0}] + Ket[g->{1,1}] ) / Sqrt[2]

BellState[g:{_?QubitQ, _?QubitQ}, 1] :=
  ( Ket[g->{0,1}] + Ket[g->{1,0}] ) / Sqrt[2]

BellState[g:{_?QubitQ, _?QubitQ}, 2] :=
  ( Ket[g->{0,1}] - Ket[g->{1,0}] ) / Sqrt[2]

BellState[g:{_?QubitQ, _?QubitQ}, 3] :=
  ( Ket[g->{0,0}] - Ket[g->{1,1}] ) / Sqrt[2]


(**** <DickeState> ****)

DickeState::usage = "DickeState[qubits, n] gives the generalized Dicke state for the qubits, where n qubits are in the state Ket[1]."

DickeState[ss:{__?QubitQ}, n_] := Module[
  { byte = ConstantArray[1, n] },
  byte = PadRight[byte, Length @ ss];
  byte = Permutations[byte];
  Total[ Map[Ket[ss -> #]&, byte] ] / Sqrt[Length[byte]]
]

DickeState[ss:{__?QubitQ}] := Table[DickeState[ss, n], {n, 0, Length @ ss}]

(**** </DickeState> ****)


(**** <GHZState for Qubits> ****)

GHZState::usage = "GHZState[{s1,s2,\[Ellipsis]}, k] returns the kth generalized GHZ state for species {s1,s2,\[Ellipsis]}.\nGHZState[{s1,s2,\[Ellipsis]}] returns the list of all GHZ states of species {s1,s2,\[Ellipsis]}.\nSee also Wolf (2003).";

GHZState[ss:{__?QubitQ}] := GHZState[ss, 0]

GHZState[ss:{__?QubitQ}, k_Integer] := Module[
  { kk = IntegerDigits[k, 2, Length @ ss],
    nn },
  nn =  Mod[kk+1, 2];
  (Ket[ss->kk] + Ket[ss->nn]*Power[-1, First @ kk]) / Sqrt[2]
]

GHZState[ss:{__?QubitQ}, kk:{___Integer}] := Map[GHZState[ss, #]&, kk]

GHZState[ss:{__?QubitQ}, All] :=
  GHZState[ss, Range[0, Power[2, Length @ ss] - 1]]

(**** </GHZState> ****)


(**** <SmolinState> ****)

SmolinState::usage = "SmolinState[{s1,s2,\[Ellipsis]}] returns the generalized Smolin state for qubits {s1,s2,\[Ellipsis]}. See also Augusiak and Horodecki (2006).";

SmolinState::badsys = "A generalized Smolin state is defined only for an even number of qubits: `` has an odd number of qubits. Returning the generalized Smolin state for the qubits excluding the last."

SmolinState[ss:{__?QubitQ}] := (
  Message[SmolinState::badsys, FlavorCap @ ss];
  SmolinState[Most @ ss]
 ) /; OddQ[Length @ ss]

SmolinState[ss:{__?QubitQ}] :=
  (1 + Power[-1, Length[ss]/2] *
      Total @ MapThread[Multiply, Through[ss[All]]]) /
  Power[2, Length @ ss]

(**** </SmolinState> ****)


(**** <GraphState> ****)

GraphState::usage = "GraphState[g] gives the graph state correponding to the graph g."

GraphState::msmtch = "The number of vertices in `` is not the same as the number of qubits in ``."

GraphState[g_Graph] := GraphState[g, FlavorCap @ VertexList @ g] /;
  AllTrue[VertexList @ g, QubitQ]

GraphState[g_Graph, ss:{__?QubitQ}] := (
  Message[GraphState::msmtch, g, FlavorCap @ ss];
  Ket[]
 ) /; Length[VertexList @ g] != Length[ss]

GraphState[g_Graph, ss:{__?QubitQ}] := Module[
  { dd = Power[2, Length @ ss],
    vv = VertexList[g],
    cz = EdgeList[g],
    in, rr },
  rr = Thread[vv -> FlavorCap[ss]];
  vv = vv /. rr;
  cz = cz /. rr;
  in = Table[1, dd] / Sqrt[dd];
  cz = Dot @@ Matrix[CZ @@@ cz, vv];
  ExpressionFor[cz . in, vv]
 ]


GraphState[g_Graph] := GraphState[g, Length @ VertexList @ g] /;
  AllTrue[VertexList @ g, IntegerQ]

GraphState[g_Graph, n_Integer] := Module[
  { dd = Power[2, n],
    cz = EdgeList[g],
    in },
  in = Table[1, dd] / Sqrt[dd];
  cz = Dot @@ theCZ[n] @@@ cz;
  ExpressionFor[cz . in]
 ] /; AllTrue[VertexList @ g, (#<=n)&]


theCZ[n_Integer][i_Integer, j_Integer] := Module[
  { pp = Tuples[{0, 1}, n] },
  pp = 1 + Map[FromDigits[#, 2]&, Select[pp, Part[#, {i, j}] == {1, 1} &]];
  DiagonalMatrix @ ReplacePart[Table[1, Power[2, n]], Thread[pp -> -1]]
 ]


GraphStateBasis::usage = "GraphStateBasis[g] returns the graph state basis for the system of qubits on the vertices of graph g."

GraphStateBasis::msmtch = "The number of vertices in `` is not the same as the number of qubits in ``."

GraphStateBasis[g_Graph] := GraphStateBasis[g, FlavorCap @ VertexList @ g] /;
  AllTrue[VertexList @ g, QubitQ]

GraphStateBasis[g_Graph, ss:{__?QubitQ}] := (
  Message[GraphStateBasis::msmtch, g, FlavorCap @ ss];
  Ket[]
 ) /; Length[VertexList @ g] != Length[ss]

GraphStateBasis[g_Graph, ss:{__?QubitQ}] := Module[
  { gs = GraphState[g, ss],
    ww },
  ww = Tuples[{0, 1}, Length @ ss];
 ]


GraphStateBasis[g_Graph] := GraphStateBasis[g, Length @ VertexList @ g] /;
  AllTrue[VertexList @ g, IntegerQ]

GraphStateBasis[g_Graph, n_Integer] := Module[
  { dd = Power[2, n],
    cz = EdgeList[g],
    in },
  in = Table[1, dd] / Sqrt[dd];
  cz = Dot @@ theCZ[n] @@@ cz;
  ExpressionFor[cz . in]
 ] /; AllTrue[VertexList @ g, (#<=n)&]

(**** </GraphState> ****)


(**** <ModMultiply> ****)

ModMultiply::usage = "ModMultiply[n, {c1,c2,\[Ellipsis]}, {t1,t2,\[Ellipsis]}] represents the modular multiplication between two quantum registers {c1,c2,\[Ellipsis]} and {t1,t2,\[Ellipsis]}."

ModMultiply::order = "`` cannot be larger than ``."

AddElaborationPatterns[_ModMultiply];

ModMultiply /: NonCommutativeQ[_ModMultiply] = True

ModMultiply /: MultiplyKind[_ModMultiply] = Qubit


ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] := (
  Message[ModMultiply::order, n, Power[2, Length @ tt]];
  ModMultiply[Power[2, Length @ tt], cc, tt, opts]
 ) /; n > Power[2, Length @ tt]

ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  ModMultiply[n, FlavorCap @ cc, FlavorCap @ tt, opts] /;
  Not[FlavorCapQ @ Join[cc, tt]]


ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ},
  ___?OptionQ][Ket[aa_Association]] :=
  Ket[ Ket @ aa,
    tt -> IntegerDigits[
      Mod[
        Times[
          FromDigits[Lookup[aa, cc], 2], 
          FromDigits[Lookup[aa, tt], 2] ],
        n ],
      2, Length @ tt ]
   ]


ModMultiply[n_Integer, x_?IntegerQ, tt:{__?QubitQ}, opts___?OptionQ] :=
  ModMultiply[n, x, FlavorCap @ tt, opts] /;
  Not[FlavorCapQ @ tt]

ModMultiply[n_Integer, x_?IntegerQ, tt:{__?QubitQ},
  ___?OptionQ][Ket[aa_Association]] :=
  Ket[ Ket @ aa,
    tt -> IntegerDigits[
      Mod[x * FromDigits[Lookup[aa, tt], 2], n],
      2, Length @ tt ]
  ]


ModMultiply /:
Multiply[pre___,
  op:ModMultiply[_Integer, {__?QubitQ}, {__?QubitQ}, ___?OptionQ],
  v:Ket[_Association], post___] :=
  Multiply[pre, op[v], post]

ModMultiply /:
Multiply[pre___,
  op:ModMultiply[_Integer, _?IntegerQ, {__?QubitQ}, ___?OptionQ],
  v:Ket[_Association], post___] :=
  Multiply[pre, op[v], post]


ModMultiply /:
Elaborate[
  op:ModMultiply[_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, ___?OptionQ]
 ] := Elaborate @ ExpressionFor[Matrix @ op, Join[cc, tt]]

ModMultiply /:
Elaborate[
  op:ModMultiply[_Integer, _?IntegerQ, tt:{__?QubitQ}, ___?OptionQ]
] := Elaborate @ ExpressionFor[Matrix @ op, tt]


ModMultiply /:
Matrix @ ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, ___?OptionQ] :=
  Module[
    { xy, xz },
    xy = Tuples @ {
      Range[0, Power[2, Length @ cc]-1],
      Range[0, Power[2, Length @ tt]-1]
     };
    xz = Transpose @ {First /@ xy, Mod[Times @@@ xy, n]};
    SparseArray[
      MapIndexed[Rule[Flatten[{#1, #2}], 1]&, Map[FirstPosition[xy, #]&, xz]],
      Table[Length @ xy, 2]
     ]
   ]

ModMultiply /:
Matrix @ ModMultiply[n_Integer, x_Integer, tt:{__?QubitQ}, ___?OptionQ] :=
  Module[
    { yy, zz },
    yy = Range[0, Power[2, Length @ tt]-1];
    zz = Mod[x ** yy, n];
    SparseArray[
      MapIndexed[Rule[Flatten[{#1, #2}], 1]&, Map[FirstPosition[yy, #]&, zz]],
      Table[Length @ yy, 2]
     ]
   ]

ModMultiply /:
Matrix[
  op:ModMultiply[_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, ___?OptionQ],
  qq:{__?SpeciesQ} ]:=
  MatrixEmbed[Matrix @ op, Join[cc, tt], qq]
  
ModMultiply /:
Matrix[
  op:ModMultiply[_Integer, _Integer, tt:{__?QubitQ}, ___?OptionQ],
  qq:{__?SpeciesQ} ]:=
  MatrixEmbed[Matrix @ op, tt, qq]
  
(**** </ModMultiply> ****)


(**** <ModPower> ****)

ModExp::usage = "ModExp is an alias of ModPower and refers to the modular exponentiation."

ModPower::usage = "ModPower represents the modular power or modular exponentiation."

(**** </ModPower> ****)


(**** <ExchangeGate> ****)

ExchangeGate::usage = "ExchangeGate[array,{s1,s2,\[Ellipsis]}] represents the unintary gate governed by the exchange coupling Hamiltoinan between qubits or spins s1,s2,\[Ellipsis].\nFor the connectivity of the coupling, see Chain or ChainBy."

SetAttributes[ExchangeGate, NHoldRest]

ExchangeGate /:
MakeBoxes[op:ExchangeGate[gg_?ArrayQ, ss_List, opts___?OptionQ], fmt_] :=
  BoxForm`ArrangeSummaryBox[
    ExchangeGate, op, None,
    { BoxForm`SummaryItem @ {"Species: ", Flatten @ ss},
      BoxForm`SummaryItem @ {"Coupling constants: ", ArrayShort @ gg} },
    { BoxForm`SummaryItem @ {"Options: ", Flatten @ {opts}} },
    fmt, 
    "Interpretable" -> Automatic 
  ] /; Or[
    AllTrue[Flatten @ ss, QubitQ],
    AllTrue[Flatten @ ss, SpinQ]
  ]


ExchangeGate /:
NonCommutativeQ[ ExchangeGate[_, __] ] = True

ExchangeGate /:
MultiplyKind[ ExchangeGate[_, ss:{___?SpeciesQ}, ___] ] := 
  MultiplyKind[First @ Flatten @ ss]

ExchangeGate /:
MultiplyGenus[ ExchangeGate[_, __] ] = "Singleton"


ExchangeGate[gg_, ss_List, rest___] :=
  ExchangeGate[gg, FlavorCap @ ss, rest] /; Not[FlavorCapQ @ ss]


ExchangeGate /:
Elaborate[op:ExchangeGate[_?ArrayQ, ss_List, ___]] :=
  Elaborate @ ExpressionFor[Matrix @ op, Flatten @ ss] 

ExchangeGate /:
Matrix[ExchangeGate[gg_?ArrayQ, ss_List, ___]] := 
  MatrixExp[-I*Matrix[Exchange[gg, ss]]]

ExchangeGate /:
Matrix[op:ExchangeGate[gg_?ArrayQ, ss_List, ___], tt:{___?SpeciesQ}] := 
  MatrixEmbed[Matrix @ op, Flatten @ ss, tt]


ExchangeGate /:
Unfold[ExchangeGate[{0, 0, phi_}, ss:{_?QubitQ, _?QubitQ}, ___]] := With[
  { cn = CNOT @@ ss },
  QuantumCircuit[cn, Rotation[2*phi, Last[ss][3]], cn]
]

ExchangeGate /:
Unfold[ExchangeGate[{phi_, phi_, 0}, {a_?QubitQ, b_?QubitQ}, ___]] :=
  QuantumCircuit[
    CNOT[a, b],
    ControlledGate[b, Rotation[4*phi, a[1]]],
    CNOT[a, b]
  ]

ExchangeGate /:
Unfold[ExchangeGate[{phi_, phi_, phi_}, {a_?QubitQ, b_?QubitQ}, ___]] :=
  QuantumCircuit[
    CNOT[a, b],
    ControlledGate[b, Rotation[4*phi, a[1]]],
    Rotation[2*phi, b[3]],
    CNOT[a, b]
  ]

(* NOTE: Put it at the end; otherwise, HoldPattern is required everywhere. *)
ExchangeGate[phi:Except[_List], rest__] := ExchangeGate[{0, 0, phi}, rest]

(**** </ExchangeGate> ****)


(**** <Exchange> ****)

Exchange::usage = "Exchange[array,{s1,s2,\[Ellipsis]}] represents the exchange coupling Hamiltoinan between qubits or spins s1,s2,\[Ellipsis].\nFor the connectivity of the coupling, see Chain or ChainBy."

SetAttributes[Exchange, NHoldRest];

Exchange /: 
NonCommutativeQ[ _Exchange ] = True

Exchange /: 
MultiplyKind[ op_Exchange ] := MultiplyKind[ op[[2]] ]

Exchange /: 
MultiplyGenus[ _Exchange ] = "Singleton"


Exchange[gg_, ss_List, rest___] :=
  Exchange[gg, FlavorCap @ ss, rest] /; Not[FlavorCapQ @ ss]

Exchange /:
OperatorExp[op:Exchange[gg_?ArrayQ, ss_List, rest___], more___] := 
  OperatorExp[Matrix @ op, Flatten @ ss, rest, more]

Exchange /:
Matrix[op:Exchange[gg_?ArrayQ, ss_List, ___]] := 
  Matrix[Elaborate @ op, Flatten @ ss]

Exchange /:
Matrix[op:Exchange[gg_?ArrayQ, ss_List, ___], tt:{___?SpeciesQ}] := 
  MatrixEmbed[Matrix @ op, Flatten @ ss, tt]

Exchange /:
Elaborate @ Exchange[gg_?ArrayQ, ss_List, ___] := Total[
  ChainBy[FlavorCap @ ss, theExchange @ gg]
] /; Or[
  AllTrue[Flatten @ ss, SpinQ],
  AllTrue[Flatten @ ss, QubitQ]
]

theExchange[gg_?VectorQ][a_, b_] := MultiplyDot[a[All], gg * b[All]]

theExchange[gg_?MatrixQ][a_, b_] := MultiplyDot[a[All], gg . b[All]]

(* NOTE: Put it at the end; otherwise, HoldPattern is required everywhere. *)
Exchange[phi:Except[_List], rest__] := Exchange[{0, 0, phi}, rest]

(**** </Exchange> ****)


(**** <Matchgate> ****)

Matchgate::usage = "Matchgate[{a1,b1,c1}, {a2,b2,c2}, {s1,s2}] represents the matchgate on two qubits s1 and s2 parametrized by two sets, {a1,b1,c1} and {a2,b2,c2}, of Euler angles."

Matchgate[aa_, bb_, ss:{__?QubitQ}] :=
  Matchgate[aa, bb, FlavorCap @ ss] /; Not[FlavorCapQ @ ss]

Matchgate /:
Elaborate @ Matchgate[aa:{_, _, _}, bb:{_, _, _}, ss:{_?QubitQ, _?QubitQ}] :=
  Elaborate[
    GivensRotation[TheEulerRotation[aa], {1, 4}, ss] **
      GivensRotation[TheEulerRotation[bb], {2, 3}, ss] ]

Matrix /:
Matrix[
  Matchgate[aa:{_, _, _}, bb:{_, _, _}, ss:{_?QubitQ, _?QubitQ}],
  rest___ ] :=
  Matrix[
    GivensRotation[TheEulerRotation[aa], {1, 4}, ss] **
      GivensRotation[TheEulerRotation[bb], {2, 3}, ss],
    rest
  ]


Matchgate[aa:{_, _, _}, bb:{_, _, _}] := Dot[
  Matrix @ GivensRotation[TheEulerRotation[aa], {1, 4}, 4],
  Matrix @ GivensRotation[TheEulerRotation[bb], {2, 3}, 4]
]

(**** </Matchgate> ****)

Protect[Evaluate @ $symb]

End[] (* Qubits *)



Begin["`Private`"]

$symb = Unprotect[Missing]

Qudit::usage = "Qudit represents a multidimensional system."

Qudit::range = "The quantum level specification s should be within the range 0 \[LessEqual] s < d, where the dimension d = `` for ``."

Options[Qudit] = { Dimension -> 3 }

Qudit /:
Let[Qudit, {ls__Symbol}, opts___?OptionQ] := Module[
  { dim },
  dim = Dimension /. {opts} /. Options[Qudit];

  Let[NonCommutative, {ls}];
    
  Scan[ setQudit[#, dim]&, {ls} ];
 ]

setQudit[x_Symbol, dim_Integer] := (
  QuditQ[x] ^= True;
  QuditQ[x[___]] ^= True;

  AgentQ[x] ^= True;
  AgentQ[x[___]] ^= True;

  MultiplyKind[x] ^= Qudit;
  MultiplyKind[x[___]] ^= Qudit;
  
  Dimension[x] ^= dim;
  Dimension[x[___]] ^= dim;

  LogicalValues[x] ^= Range[0, dim-1];
  LogicalValues[x[___]] ^= Range[0, dim-1];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___, ij:Rule[_List, _]] := x[j, Thread @ ij];
  x[j___, ij:Rule[_, _List]] := x[j, Thread @ ij];
  
  x[j___, All] := x[j, Rule @@@ Tuples[Range[0, dim-1], 2]];
  x[j___, Diagonal] := x[j, Thread @ Rule[Range[0, dim-1], Range[0, dim-1]]];
  
  x /: Dagger[ x[j___, Rule[a_Integer, b_Integer]] ] := x[j, Rule[b,a]];

  x[j___, Rule[a_Integer, b_Integer]] := (
    Message[Qudit::range, dim, x[j,$]];
    0
  ) /; Or[ a < 0, a >= Dimension[x], b < 0, b >= Dimension[x] ];

  Format @ x[j___, $] :=
    Interpretation[SpeciesBox[x, {j}, {}], x[j, $]];  
  Format @ x[j___, 0] :=
    Interpretation[SpeciesBox[1, {j}, {0}], x[j, 0]];
  Which[
    $VersionNumber < 13.3,
    Format @ x[j___, a_ -> b_] := Interpretation[
      SpeciesBox[ Row @ {"(", Ket[b], Bra[a], ")"}, {j}, {}],
      x[j, a -> b]
    ],
    True,
    Format @ x[j___, a_ -> b_] := Interpretation[
      SpeciesBox[ Row @ {Ket @ {b}, Bra @ {a}}, {j}, {}],
      x[j, a -> b]
    ]
  ];

  (* See Gross (2006) and Singal et al. (2023) *)
  Format[x[j___, $[{m_Integer, n_Integer}]]] := Row @ Thread @ Subsuperscript[
    {"X", "Z"},
    {Row @ Riffle[{j}, ","], Row @ Riffle[{j}, ","]},
    {m, n}
  ];
)


QuditQ::usage = "QuditQ[op] returns True if op is a species representing a qudit and False otherwise."

AddGarnerPatterns[_?QuditQ]

QuditQ[_] = False

Missing["KeyAbsent", _Symbol?QuditQ[___, $]] := 0


Qudits::usage = "Qudits[expr] gives the list of all qudits appearing in expr."

Qudits[expr_] := Select[Agents @ expr, QuditQ]


(* MultiplyDegree for operators *)
MultiplyDegree[_?QuditQ] = 1


(* NOTE: The input arguments syntax for Dyad has been changed. *)
(* Dyad[a_Association, b_Association, {A_?QuditQ}] := A[b[A] -> a[A]] *)
(* For a single Qudit, Dyad is meaningless. *)


Base[ S_?QuditQ[k___, _] ] := S[k]
(* For Qudits, the final Flavor index is special. *)


(* FlavorCap: See Cauchy *)

FlavorCap[S_?QuditQ] := S[$]


(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?QuditQ] := S[$]

FlavorMute[S_Symbol?QuditQ[k___, _]] := S[k, $]

FlavorMute[S_Symbol?QuditQ[k___, _] -> m_] := S[k, $] -> m


(**** <Ket for Qudits> ****)

theKetTrim[Rule[_?QuditQ, 0]] = Nothing

KetVerify::qudit = "Invalid value `` for qudit ``."

theKetVerify[Rule[a_?QuditQ, v_]] := (
  Message[KetVerify::qudit, v, a];
  Nothing
) /; Not[0 <= v < Dimension[a]]
(* NOTE: The following definition would not allow to assign a symbolic value:
   theKetVerify[Rule[_?QuditQ, Except[0|1]]] = Nothing *)

(**** </Ket for Qubits> ****)


(**** <GHZState> ****)
(*  for arbitray species *)

GHZState[ss:{__?SpeciesQ}, rest___] := KetMutate[
  GHZState[{First @ Dimension @ ss, Length @ ss}, rest],
  ss
]


GHZState[{dim_Integer?Positive, n_Integer?Positive}, k_Integer?NonNegative] := Module[
  { xx, kk, ww, vv },
  xx = Range[0, dim-1];
  kk = IntegerDigits[k, dim, n];
  vv = Map[Mod[kk + #, dim]&,  xx];
  ww = Exp[I* 2*Pi * xx * First[kk] / dim] / Sqrt[dim];
  Map[Ket, vv] . ww
]

GHZState[{dim_Integer?Positive, n_Integer?Positive}] := GHZState[{dim, n}, 0]

GHZState[{dim_Integer?Positive, n_Integer?Positive}, All] := Map[
  GHZState[{dim, n}, #]&,
  Range[0, Power[dim, n]-1]
]

(**** </GHZState> ****)


(* Qudit on Ket *)

HoldPattern @
  Multiply[ pre___,
    S_?QuditQ[k___, Rule[x_,y_]], v:Ket[_Association],
    post___ ] :=
  Multiply[pre, v[S[k,$] -> y], post] /; v[S[k,$]] == x
(* TODO: handle symbolic flavors x*)

HoldPattern @
  Multiply[a___, S_?QuditQ[j___, Rule[x_,y_]], v:Ket[_Association], b___] :=
  0 /; v[S[j,$]] != x
(* TODO: handle symbolic flavors x*)


(* Qudit Operator Algebra *)

HoldPattern @ Multiply[pre___, _?QuditQ[___, 0], post___] :=
  Multiply[pre, post]

HoldPattern @ Multiply[pre___,
  A_Symbol?QuditQ[j___, y_->z_], A_Symbol?QuditQ[j___, x_->y_],
  post___] := Multiply[pre, A[j, x->z], post]

HoldPattern @ Multiply[
  pre___,
  A_Symbol?QuditQ[j___, z_->w_], A_Symbol?QuditQ[j___, x_->y_],
  post___
] := Multiply[pre, A[j, x->w], post] * KroneckerDelta[y, z]


(* See Gross (2006) and Singal et al. (2023) *)
HoldPattern @ Multiply[pre___,
  A_Symbol?QuditQ[j___, $ @ {a_, b_}],
  A_Symbol?QuditQ[j___, $ @ {c_, d_}],
  post___] := Multiply[ pre,
    A[j, $ @ {Mod[a+c, Dimension @ A], Mod[b+d, Dimension @ A]}],
    post ] *
  Exp[2*Pi*I * b*c / Dimension[A]]

HoldPattern @ Multiply[pre___,
  A_Symbol?QuditQ[j___, $ @ {x_, z_}],
  v:Ket[a_Association] ] := With[
    { s = a[A[j, $]] },
    Multiply[ pre,
      Ket[v, A[j, $] -> Mod[s+x, Dimension @ A]] ] *
      Exp[2*Pi*I * z*s / Dimension[A]]
   ]

HoldPattern @ Multiply[pre___, A_?QuditQ, B_?QuditQ, post___] :=
  Multiply[pre, B, A, post] /; Not @ OrderedQ @ {A, B}


(**** <Basis> ****)

Basis[ S_?QuditQ ] :=
  Ket /@ Thread[FlavorCap[S] -> Range[0, Dimension[S]-1]]

(**** </Basis> ****)


TheQuditKet::usage = "TheQuditKet[{j,m}] returns the (m+1)th unit column vector in the j-dimensional complex vector space.\nTheQuditKet[{j1,m1}, {j2,m2}, ...] returns the direct product of vectors.\nTheQuditKet[j, {m1, m2, ...}] is equivalent to TheQuditKet[{j,m1}, {j,m2}, ...]."

TheQuditKet[ {dim_Integer, m_Integer} ] :=
  SparseArray[{(m+1) -> 1}, dim] /; 0 <= m < dim

TheQuditKet[ dim_Integer, mm:{__Integer} ] :=
  TheQuditKet @@ Thread @ {dim, mm}

TheQuditKet[ cc:{_Integer, _Integer}.. ] := Module[
  { aa = Transpose @ {cc},
    dd, pwrs, bits, p},
  dd = First @ aa;
  pwrs = Reverse @ FoldList[ Times, 1, Reverse @ Rest @ dd ];
  bits = Last @ aa;
  p = 1 + bits.pwrs;
  SparseArray[{p -> 1}, Whole @ dd]
]


(**** <Parity> ****)

Parity[A_?QuditQ] := Module[
  { jj = Range[0, Dimension[A]-1],
    op },
  op = A /@ Thread[jj->jj];
  Power[-1, jj] . op
]

ParityValue[v_Ket, a_?QuditQ] := IntegerParity[v[a]]

ParityEvenQ[v_Ket, a_?QuditQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?QuditQ] := OddQ @ v @ a

(**** </Parity> ****)


(**** <Matrix for Qudits> ****)

TheMatrix[A_?QuditQ[___, i_ -> j_]] :=
  SparseArray[{1+j, 1+i} -> 1, Dimension[A]*{1, 1}]

TheMatrix @ Ket @ Association[A_?QuditQ -> n_Integer] := SparseArray[
  If[0 <= n < Dimension[A], {n+1} -> 1, {}, {}],
  Dimension[A]
 ]

TheMatrix[A_?QuditQ[___, $ @ {x_Integer, z_Integer}]] :=
  TheWeyl[{x, z, Dimension @ A}]

(**** </Matrix> *****)


(**** <TransformByFourier for Qudits> ****)

TransformBy[a__?QuditQ, mat_?MatrixQ] :=
  TransformBy[Sequence @@ Thread[{a} -> {a}], mat]

TransformBy[old_?QuditQ -> new_?QuditQ, mat_?MatrixQ] := Module[
  { ij = Range[0, Dimension[old]-1],
    aa, bb },  
  aa = old[All];
  bb = Outer[new[#1 -> #2]&, ij, ij];
  bb = Flatten[ Topple[mat] . bb . mat ];
  Thread[aa -> bb]
]

TransformBy[
  a:Rule[_?QuditQ, _?QuditQ],
  b:Rule[_?QuditQ, _?QuditQ]..,
  mat_?MatrixQ ] := Map[ TransformBy[#, mat]&, {a, b} ]

TransformBy[expr_, old_?QuditQ -> new_?QuditQ, mat_?MatrixQ] :=
  Garner[ expr /. TransformBy[old -> new, mat] ]


TransformByFourier[a__?QuditQ, mat_?MatrixQ] :=
  TransformByFourier[Sequence @@ Thread[{a} -> {a}], mat]

TransformByFourier[old_?QuditQ -> new_?QuditQ, opts___?OptionQ] := With[
  { mat = FourierMatrix[Dimension @ old, opts] },
  TransformBy[old -> new, mat]
]

TransformByFourier[
  a:Rule[_?QuditQ, _?QuditQ],
  b:Rule[_?QuditQ, _?QuditQ]..,
  opts___?OptionQ] := Map[ TransformByFourier[#, opts]&, {a, b} ]

TransformByFourier[expr_, old_?QuditQ -> new_?QuditQ, opts___?OptionQ] :=
  Garner[ expr /. TransformByFourier[old -> new, opts] ]

(**** </TransformByFourier for Qudits> ****)

Protect[Evaluate @ $symb]

End[] (* Qudits *)


Begin["`Private`"]

(**** <Unfold> ****)

Unfold::usage = "Unfold[gate] gives an unfolded form of gate."

Unfold::unknown = "Unknown method ``."

Options[Unfold] = {
  Method -> Default, (* CZ, CNOT, Toffoli  *)
  "ApproximationLevel" -> Full, (* QFT *)
  "Numeric" -> False, (* QFT *)
  "Reversed" -> False, (* QFT *)
  "Pushed" -> False (* QFT *)
}

SyntaxInformation[Unfold] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]}
}

Unfold[any_?CommutativeQ op_, opts___?OptionQ] := any * Unfold[op, opts]

Unfold[any_, ___?OptionQ] = any

(**** </Unfold> ****)


(**** <UnfoldAll> ****)

UnfoldAll::usage = "UnfoldAll[gate] gives a fully unfolded form of gate."

UnfoldAll::unknown = "Unknown method ``."

Options[UnfoldAll] = Options[Unfold]

SyntaxInformation[UnfoldAll] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]}
}

UnfoldAll[any_?CommutativeQ op_, opts___?OptionQ] := any * UnfoldAll[op, opts]

UnfoldAll[any_, ___?OptionQ] = any

(**** </UnfoldAll> ****)

End[] (* Untilities *)


EndPackage[]
