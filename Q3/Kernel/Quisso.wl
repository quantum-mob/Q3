(* -*- mode: math; -*- *)

BeginPackage["Q3`"]

`Quisso`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 6.11 $"][[2]], " (",
  StringSplit["$Date: 2023-07-18 23:13:46+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ];

{ Qubit, QubitQ, Qubits };

{ PauliForm };

{ QubitAdd, QubitAddZ };

{ Rotation, EulerRotation, Phase };

{ ControlledGate, CNOT, CX = CNOT, CZ, SWAP,
  Toffoli, Fredkin, Deutsch };

{ ControlledExp = ControlledPower, OperatorOn };

{ UniformlyControlledRotation };

{ Measurement, Measurements, MeasurementFunction,
  MeasurementOdds, Readout, $MeasurementOut = <||> };

{ Projector };

{ Oracle };

{ QFT, ModExp, ModAdd, ModMultiply };

{ ProductState, BellState, GHZState, SmolinState,
  DickeState, RandomState };

{ GraphState, GraphStateBasis };

(* Qudit *)

{ Qudit, QuditQ, Qudits };

{ TheQuditKet };

{ WeylHeisenbergBasis };

(* Obsolete Symbols *)

{ VerifyOracle }; (* excised *)

{ ControlledU }; (* renamed *)
{ QuissoAdd, QuissoAddZ }; (* renamed *)

{ Dirac }; (* OBSOLETE *)


Begin["`Private`"]

$symb = Unprotect[CircleTimes, Dagger, Ket, Bra, Missing]

AddElaborationPatterns[
  _QFT,
  _ControlledGate, _CZ, _CX, _CNOT, _SWAP,
  _Toffoli, _Fredkin, _Deutsch, _Oracle,
  _Phase, _Rotation, _EulerRotation,
  _Projector, _ProductState,
  _ControlledPower
 ]

AddElaborationPatterns[
  G_?QubitQ[j___, 0] -> 1,
  G_?QubitQ[j___, 4] -> G[j, Raise],
  G_?QubitQ[j___, 5] -> G[j, Lower],
  G_?QubitQ[j___, 6] -> G[j, Hadamard],
  G_?QubitQ[j___, 7] -> G[j, Quadrant],
  G_?QubitQ[j___, 8] -> G[j, Octant],
  G_?QubitQ[j___, 9] -> G[j, Hexadecant],
  G_?QubitQ[j___, 10] -> (1 + G[j,3]) / 2,
  G_?QubitQ[j___, 11] -> (1 - G[j,3]) / 2,
  G_?QubitQ[j___, n_Integer?Negative] :> Dagger[Elaborate @ G[j, -n]],
  G_?QubitQ[j___, C[n_Integer]] :>
    Elaborate @ Phase[2*Pi*Power[2,n], G[j,3]],
  G_?QubitQ[j___, -C[n_Integer]] :>
    Elaborate @ Phase[-2*Pi*Power[2,n], G[j,3]],
  G_?QuditQ[j___, 0 -> 0] :> 1 - Total @ Rest @ G[j, Diagonal],
  OTimes -> CircleTimes,
  OSlash -> CircleTimes
 ]


Qubit::usage = "Qubit denotes a quantum two-level system or \"quantum bit\".\nLet[Qubit, S, T, ...] or Let[Qubit, {S, T,...}] declares that the symbols S, T, ... are dedicated to represent qubits and quantum gates operating on them. For example, S[j,..., $] represents the qubit located at the physical site specified by the indices j, .... On the other hand, S[j, ..., k] represents the quantum gate operating on the qubit S[j,..., $].\nS[..., 0] represents the identity operator.\nS[..., 1], S[..., 2] and S[..., 3] means the Pauli-X, Pauli-Y and Pauli-Z gates, respectively.\nS[..., 4] and S[..., 5] represent the raising and lowering operators, respectively.\nS[..., 6], S[..., 7], S[..., 8] represent the Hadamard, Quadrant (Pi/4) and Octant (Pi/8) gate, resepctively.\nS[..., 10] represents the projector into Ket[0].\nS[..., 11] represents the projector into Ket[1].\nS[..., (Raise|Lower|Hadamard|Quadrant|Octant)] are equivalent to S[..., (4|5|6|7|8)], respectively, but expanded immediately in terms of S[..., 1] (Pauli-X), S[..., 2] (Y), and S[..., 3] (Z).\nS[..., $] represents the qubit."

Qubit /:
Let[Qubit, {ls__Symbol}, opts___?OptionQ] := (
  Let[NonCommutative, {ls}];
  Scan[setQubit, {ls}];
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
  
  x/: Dagger @ x[j___, C[k_Integer]] = x[j, -C[k]];
  x/: Dagger @ x[j___, -C[k_Integer]] = x[j, C[k]];

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

  x[j___, Raise] = (x[j,1] + I x[j,2]) / 2;
  x[j___, Lower] = (x[j,1] - I x[j,2]) / 2;
  
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

  x[j___, C[n_Integer?NonNegative]] = x[j, 0];
  
  x[j___, C[-1]] = x[j, 3];
  x[j___, C[-2]] = x[j, 7];
  x[j___, C[-3]] = x[j, 8];
  x[j___, C[-4]] = x[j, 9];

  (* x[j___, 10] := (1 + x[j,3]) / 2; *)
  (* x[j___, 11] := (1 - x[j,3]) / 2; *)
  (* NOTE: It interferes, say, with Ket[] encountered with short-cut inputs *)

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

  Format[ x[j___, C[n_Integer?Negative]] ] := Interpretation[
    With[ {m = -n}, SpeciesBox[x, {j}, {2 Pi / HoldForm[Power[2, m]]}] ],
    x[j, C @ n]
   ];
  
  Format[ x[j___, -C[n_Integer?Negative]] ] := Interpretation[
    With[ {m = -n}, SpeciesBox[x, {j}, {-2 Pi / HoldForm[Power[2, m]]}] ],
    x[j, C @ n]
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

Missing["KeyAbsent", _Symbol?QubitQ[___, $]] := 0


Raise[S_?QubitQ] := S[4]

Lower[S_?QubitQ] := S[5]

Hadamard[S_?QubitQ] := S[6]

Quadrant[S_?QubitQ] := S[7]

Octant[S_?QubitQ] := S[8]

Hexadecant[S_?QubitQ] := S[9]


(* Override the default definition of Format[Dagger[...]]
   NOTE: This is potentially dangerous because Fock also overides it. *)

Format @ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] =. ;

(* Obsolete:
   S[..., -n] now has a different meaning than before. *)
(*
Format @ HoldPattern @ Dagger[ c_Symbol?QubitQ[j___, n_Integer?Negative] ] :=
  Interpretation[
    Superscript[Row @ {"(", c[j,n], ")"}, "\[Dagger]"],
    Dagger @ c[j, n]
   ]
 *)

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


QubitQ::usage = "QubitQ[S] or QubitQ[S[...]] returns True if S is declared as a Qubit through Let."

AddGarnerPatterns[_?QubitQ]

QubitQ[_] = False


Qubits::usage = "Qubits[expr] gives the list of all qubits (quantum bits) appearing in expr."

Qubits[expr_] := Select[Agents @ expr, QubitQ]


(**** <Multiply> ****)

(* Speical Rules: Involving identity *)

HoldPattern @ Multiply[a___, _?QubitQ[___, 0], b___] := Multiply[a, b]

(* Multiply operators on Ket[] *)

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,4], Ket[b_Association], post___ ] :=
  0 /; b @ a[j, $] == 0

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,4], Ket[b_Association], post___ ] :=
  Multiply[
    pre,
    Ket @ KeyDrop[b, a[j, $]],
    post
   ] /; b @ a[j, $] == 1

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,5], Ket[b_Association], post___ ] :=
  0 /; b @ a[j, $] == 1

HoldPattern @
  Multiply[ pre___, a_?QubitQ[j___,5], Ket[b_Association], post___ ] :=
  Multiply[
    pre,
    Ket[b][a[j, $] -> 1],
    post
   ] /; b @ a[j, $] == 0

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

(*
HoldPattern @ Multiply[ x___, a_?QubitQ[j___,4], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Raise], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,5], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Lower], Ket[b], y]
 *)

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,6], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Hadamard], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,7], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Quadrant], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,8], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Octant], Ket[b], y]


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

(* Gates on Bra *)

HoldPattern @ Multiply[ x___, Bra[v_Association], G_?QubitQ, y___ ] :=
  Multiply[ x, Dagger[Dagger[G]**Ket[v]], y ]

HoldPattern @ Multiply[ x___, Bra[v_Association, s_List], G_?QubitQ, y___ ] :=
  Multiply[ x, Dagger[Dagger[G]**Ket[v,s]], y ]


(* Special rules for Pauli matrices *)
 
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

HoldPattern @ Multiply[ pre___,
  x_Symbol?QubitQ[j___,m_], x_Symbol?QubitQ[j___,n_], post___ ] :=
  Multiply[pre, Elaborate @ x[j,m], Elaborate @ x[j,n], post]


(* General Rules *)

HoldPattern @ Multiply[ pre___, op_?QubitQ, vec_Ket, post___] :=
  Multiply[pre, Elaborate @ op, vec, post]

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

(* FlavorNone: See Abel *)

FlavorNone[S_?QubitQ] := S[$]

(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?QubitQ] := S[$]

FlavorMute[S_Symbol?QubitQ[j___, _]] := S[j, $]

FlavorMute[S_Symbol?QubitQ[j___, _] -> m_] := S[j, $] -> m


$RaiseLowerRules = Join[ $RaiseLowerRules,
  { S_?QubitQ[j___,1] :> (S[j,4] + S[j,5]),
    S_?QubitQ[j___,2] :> (S[j,4] - S[j,5]) / I
   }
 ]


(**** <Ket for Qubit> ****)

theKetTrim[Rule[_?QubitQ, 0]] = Nothing

KetVerify::qubit = "Invalid value `` for qubit ``."

KetVerify[a_?QubitQ, v_] := (
  Message[KetVerify::qubit, v, a];
  $Failed
 ) /; Or[ Negative[v], v > 1 ]
(* NOTE: The following definition would not allow to assign a symbolic value:
   KetVerify[ _?QubitQ, Except[0|1] ] = $Failed *)

(**** </Ket for Qubit> ****)


(**** <Basis for Qubit> ****)

Basis[ S_?QubitQ ] := Ket /@ Thread[FlavorNone[S] -> {0, 1}]

(**** </Basis for Qubit> ****)


(**** <SpinForm> ****)

SpinForm[vec:Ket[_Association], qq:{__?QubitQ}] := Module[
  { ss },
  ss = vec[FlavorNone @ qq] /. {
    0 -> "\[UpArrow]",
    1 -> "\[DownArrow]"
   };
  Ket[vec, qq -> ss]
 ]

(**** </SpinForm> ****)


(**** <PauliForm> ****)

singleQubitGateQ::usage = "singleQubitGateQ[op] returns True if operator op is an 'elementary' single-qubit gate; and False, otherwise."

(* SetAttributes[singleQubitGateQ, ReadProtected] *)

HoldPattern @ singleQubitGateQ @ Dagger[_?QubitQ] = True

singleQubitGateQ[_?QubitQ] = True

singleQubitGateQ[Phase[_, _?QubitQ, ___]] = True

singleQubitGateQ[_] = False


thePauliForm::usage = "thePauliForm[op] or thePauliForm[Dagger[op]] rewrites op in a more conventional form, where the Pauli operators are denoted by I, X, Y, Z, H, S, and T."

HoldPattern @ thePauliForm @ Pauli[k_Integer?Negative] :=
  Superscript[thePauliForm @ Pauli[-k], "\[Dagger]"]

thePauliForm @ Pauli[k_Integer] := ReplaceAll[ k,
  { 0 -> "I", 1 -> "X", 2 -> "Y", 3 -> "Z",
    4 -> Superscript["X", "+"],
    5 -> Superscript["X", "-"],
    6 -> "H", 7 -> "S", 8 -> "T", 9 -> "F",
    10 -> Row @ {Ket[0], Bra[0]},
    11 -> Row @ {Ket[1], Bra[1]} }
 ]

thePauliForm @ Pauli[-C[n_Integer]] :=
  With[{m = -n}, Superscript["Z", -2 Pi / HoldForm[Power[2, m]]]]

thePauliForm @ Pauli[+C[n_Integer]] :=
  With[{m = -n}, Superscript["Z", +2 Pi / HoldForm[Power[2, m]]]]

thePauliForm @ Pauli[any_] = Superscript["\[Sigma]", any]
(* NOTE: This is necessary to avoid infinite recursion Format[Paui[...]] may
   cause. *)

thePauliForm @ Pauli[a_, bc__] :=
  CircleTimes @@ Map[thePauliForm, Pauli @ {a, bc}]


(* NOTE: This should not occur. *)
(*
HoldPattern @ thePauliForm @ Dagger @ S_?QubitQ[___, k_] :=
  thePauliForm @ Dagger @ Pauli[k]
 *)

thePauliForm @ _?QubitQ[___, k_] := thePauliForm @ Pauli[k]

thePauliForm @ Phase[phi_, S_?QubitQ, ___] :=
  Superscript[thePauliForm @ S, phi]

thePauliForm[ss__?singleQubitGateQ, qq:{__?QubitQ}] := Module[
  { kk, mm },
  kk = Lookup[PositionIndex[FlavorNone @ qq], Flatten[Qubits /@ {ss}]];
  mm = FlavorLast @ {ss};
  CircleTimes @@ ReplacePart[
    Table["I", Length @ qq],
    Flatten[ Thread /@ Thread[kk -> Map[thePauliForm, {ss}]] ]
   ]
 ]


PauliForm::usage = "PauliForm[expr] rewrites expr in a more conventional form, where the Pauli operators are denoted by I, X, Y, and Z."

PauliForm[z_?CommutativeQ, qq:{__?QubitQ}] :=
  Interpretation[z * CircleTimes @@ Table["I", Length @ qq], z]

HoldPattern @ PauliForm[op:Multiply[ss__?singleQubitGateQ], qq:{__?QubitQ}] :=
  Interpretation[thePauliForm[ss, qq], op]

PauliForm[op_?singleQubitGateQ, qq:{__?QubitQ}] :=
  Interpretation[thePauliForm[op, qq], op]

PauliForm[expr_Plus, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, expr]

PauliForm[expr_List, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, expr]

PauliForm[assc_Association, qq:{__?QubitQ}] := Map[PauliForm[#, qq]&, assc]

PauliForm[expr_, qq:{__?QubitQ}] := expr /. {
    HoldPattern[op:Multiply[__?singleQubitGateQ]] :> PauliForm[op, qq],
    op_?singleQubitGateQ :> PauliForm[op, qq]
   }

PauliForm[expr_] := PauliForm[expr, Qubits @ expr] /; FreeQ[expr, _Pauli]


PauliForm[op_Pauli] := Interpretation[thePauliForm @ op, op]

PauliForm[assc_Association] := Map[PauliForm, assc]

PauliForm[expr_] := expr /. { op_Pauli :> PauliForm[op] }

(**** </PauliForm> ****)


(**** <Dirac> ****)

Dirac::usage = "Dirac is OBSOLETE. Instead, use Dyad."

Dirac[expr__] := (
  Message[Q3General::obsolete, Dirac, Dyad];
  Dyad[expr]
 )

(**** </Dirac> ****)


(**** <Parity for Qubits> ****)

Parity[S_?QubitQ] := S[3]

ParityValue[v_Ket, a_?QubitQ] := 1 - 2*v[a]

ParityEvenQ[v_Ket, a_?QubitQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?QubitQ] := OddQ @ v @ a

(**** </Parity> ****)


(**** <Matrix for Qubits> ****)

TheMatrix[ _?QubitQ[___, +C[m_Integer?Negative]] ] :=
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[+I*2*Pi*Power[2, m]]}, {2, 2}]

TheMatrix[ _?QubitQ[___, -C[m_Integer?Negative]] ] :=
  SparseArray[{{1, 1} -> 1, {2, 2} -> Exp[-I*2*Pi*Power[2, m]]}, {2, 2}]

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
  { aa = FlavorNone @ a,
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
  { aa = FlavorNone @ a,
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


QuissoAdd::usage = "QuissoAdd has been renamed QubitAdd."

QuissoAdd[args__] := (
  Message[Q3General::renamed, "QuissoAdd", "QubitAdd"];
  QubitAdd[args]
 )

QuissoAddZ::usage = "QuissoAddZ has been renamed QubitAddZ."

QuissoAddZ[args__] := (
  Message[Q3General::renamed, "QuissoAddZ", "QubitAddZ"];
  QubitAddZ[args]
 )

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

Phase[phi_, S_?QubitQ, opts___?OptionQ] :=
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
  Phase[-Conjugate[phi], S, opts]
  
Phase /:
Elaborate @ Phase[phi_, S_?QubitQ, ___] :=
  Garner[ (1 + Exp[I*phi])/2 + S * (1 - Exp[I*phi])/2 ]

Phase /:
Elaborate[op_Phase] = op (* fallback *)

Phase /:
HoldPattern @ Multiply[pre___, op_Phase, in_Ket] :=
  Multiply[pre, Multiply[Elaborate @ op, in]]

(* Automatic expansion may be delayed until necessary. *)
(*
Phase /:
HoldPattern @ Multiply[pre___, op_Phase, post___] :=
  Multiply[pre, Elaborate @ op, post]
 *)

Phase /:
Matrix[op:Phase[_, _?QubitQ, ___], rest__] := Matrix[Elaborate[op], rest]

Phase /:
Matrix[op:Phase[___], __] = op


Phase[q_?QubitQ, phi_, rest___] := (
  Message[Q3General::angle, Phase];
  Phase[phi, q, rest]
 )

Phase[qq:{__?QubitQ}, phi_, rest___] := (
  Message[Q3General::angle, Phase];
  Phase[phi, qq, rest]
 )

(**** </Phase> ****)


(**** <Rotation> ****)

Rotation /:
Elaborate @ Rotation[phi_, v:{_, _, _}, S_?QubitQ, ___] :=
  Garner[ Cos[phi/2] - I*Sin[phi/2]*Dot[S @ All, Normalize @ v] ]

(**** </Rotation> ****)


(**** <EulerRotation> ****)

EulerRotation /:
Expand @ EulerRotation[{a_,b_,c_}, S_?QubitQ, opts___?OptionQ] :=
  Sequence[
    Rotation[c, S[3], opts],
    Rotation[b, S[2], opts],
    Rotation[a, S[3], opts]
   ]

(**** </EulerRotation> ****)


(**** <CNOT> ****)

CX::usage = "CX is an alias to CNOT."

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


CNOT[c_?QubitQ, t_] := CNOT[c @ {$} -> {1}, t]

CNOT[c_, t_?QubitQ] := CNOT[c, t @ {$}]

CNOT[cc:{__?QubitQ}, tt_] :=
  CNOT[cc -> Table[1, Length @ cc], tt]


CNOT[Rule[c_?QubitQ, v_], tt_] := CNOT[{c} -> {v}, tt]

CNOT[Rule[cc:{__?QubitQ}, v_], tt_] :=
  CNOT[cc -> Table[v, Length @ cc], tt] /; Not[ListQ @ v]


CNOT[Rule[cc:{__?QubitQ}, vv_List], tt_] := (
  Message[CNOT::incmp, cc, vv];
  CNOT[cc -> PadRight[vv, Length @ cc, 1], tt]
 ) /; Length[cc] != Length[vv]


CNOT[Rule[cc:{__?QubitQ}, vv_], tt:{__?QubitQ}] :=
  CNOT[FlavorNone[cc] -> vv, FlavorNone @ tt] /;
  Not[FlavorNoneQ @ Join[cc, tt]]


CNOT /: Dagger[ op_CNOT ] = op

CNOT /:
Elaborate[op_CNOT] = op (* fallback *)

CNOT /:
Elaborate @
  CNOT[Rule[cc:{__?QubitQ}, vv:{__?BinaryQ}], tt:{__?QubitQ}] := Module[
    { prj = Through[cc[3]],
      not = Multiply @@ Through[tt[1]] },
    prj = Multiply @@ Garner[(1+prj)/2 - Boole[OddQ @ vv]*prj];
    Garner @ Elaborate[(1-prj) + prj ** not]
   ]

CNOT /:
Multiply[pre___, CNOT[Rule[cc_, vv_], tt_], in_Ket] := Module[
  { op = Multiply @@ Through[tt[1]],
    xx },
  If[ in[cc] == vv,
    Multiply[pre, op ** in],
    Multiply[pre, in],
    xx = Mod[in[tt] + Apply[Times, Mod[in[cc]+vv+1, 2]], 2];
    Multiply[pre, in[tt -> xx]]
   ]
 ]

HoldPattern @ Multiply[pre___, op_CNOT, post___] :=
  Multiply[pre, Elaborate[op], post]
(* NOTE: DO NOT put "CNOT /:". *)

CNOT /:
Matrix[op:CNOT[Rule[{__?QubitQ}, _List], {__?QubitQ}], rest___] :=
  Matrix[Elaborate @ op, rest]

CNOT /: (* fallback *)
Matrix[op_CNOT, ss:{__?SpeciesQ}] := op * One[Times @@ Dimension @ ss]

(**** </CNOT> ****)


(**** <CZ> ****)

CZ::usage = "CZ[C, T] represents the controlled-Z gate on the two qubits associated with C and T. C and T are the control and target qubits, respectively; in fact, contol and target qubits are symmetric for this gate.\nC[{c1,c2,\[Ellipsis]}, {t1,t2,\[Ellipsis]}] represents the multi-control Z gate."

CZ[c_?QubitQ, t_] := CZ[{c}, t]

CZ[c_, t_?QubitQ] := CZ[c, {t}]

CZ[cc:{__?QubitQ}, tt:{__?QubitQ}] :=
  CZ[FlavorNone @ cc, FlavorNone @ tt] /;
  Not[FlavorNoneQ @ Join[cc, tt]]

CZ /:
Dagger[ op_CZ ] := op

CZ /:
HoldPattern @ Elaborate @ CZ[cc:{__?QubitQ}, tt:{__?QubitQ}] := Module[
  { prj = Multiply @@ Through[cc[11]],
    opz = Multiply @@ Through[tt[3]] },
  Garner @ Elaborate[(1-prj) + prj ** opz]
 ]

CZ /:
HoldPattern @ Multiply[pre___, op_CZ, post___] :=
  Multiply[pre, Elaborate[op], post]

CZ /:
HoldPattern @ Matrix[op_CZ, rest___] := Matrix[Elaborate[op], rest]

(**** </CZ> ****)


(**** <SWAP> ****)

SWAP::usage = "SWAP[A, B] operates the SWAP gate on the two qubits A and B."

SetAttributes[SWAP, Listable]

SWAP[a_?QubitQ, b_?QubitQ] := SWAP @@ FlavorNone @ {a, b} /;
  Not[FlavorNoneQ @ {a, b}]

SWAP[a_?QubitQ, b_?QubitQ] := SWAP[b, a] /;
  Not @ OrderedQ @ FlavorNone @ {a, b}

SWAP /:
Dagger[ op_SWAP ] := op

SWAP /:
HoldPattern @ Elaborate @ SWAP[x_?QubitQ, y_?QubitQ] := Module[
  { a = Most @ x,
    b = Most @ y },
  Garner[ (1 + a[1]**b[1] + a[2]**b[2] + a[3]**b[3]) / 2 ]
 ]

SWAP /:
HoldPattern @ Multiply[pre___, op_SWAP, post___] :=
  Multiply[pre, Elaborate[op], post]

SWAP /:
HoldPattern @ Matrix[op_SWAP, rest___] := Matrix[Elaborate[op], rest]

(**** </SWAP> ****)


(**** <Toffoli> ****)

Toffoli::usage = "Toffoli[A, B, C] operates the Toffoli gate, i.e., the three-qubit controlled-note gate on C controlled by A and B."

SetAttributes[Toffoli, Listable]

Toffoli[a_?QubitQ, b_?QubitQ, c_?QubitQ] :=
  Toffoli @@ FlavorNone @ {a, b, c} /;
  Not[FlavorNoneQ @ {a, b, c}]

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

(**** </Toffoli> ****)


(**** <Fredkin> ****)

Fredkin::usage = "Fredkin[a, b, c] represents the Fredkin gate, i.e., the SWAP gate on b and c controlled by a."

SetAttributes[Fredkin, Listable]

Fredkin[ a_?QubitQ, b_?QubitQ, c_?QubitQ ] :=
  Fredkin @@ FlavorNone @ {a,b,c} /;
  Not[FlavorNoneQ @ {a, b, c}]

Fredkin /:
Dagger[ op_Fredkin ] := op

Fredkin /:
HoldPattern @ Elaborate @ Fredkin[a_?QubitQ, b_?QubitQ, c_?QubitQ] :=
  Garner @ Elaborate[ a[10] + a[11] ** SWAP[b, c] ]

Fredkin /:
HoldPattern @ Multiply[pre___, op_Fredkin, post___] :=
  Multiply[pre, Elaborate[op], post]

Fredkin /:
HoldPattern @ Matrix[op_Fredkin, rest___] := Matrix[Elaborate[op], rest]

(**** </Fredkin> ****)


(**** <Deutsch> ****)

Deutsch::usage = "Deutsch[angle, {a, b, c}] represents the Deutsch gate, i.e., \[ImaginaryI] times the rotation by angle around the x-axis on qubit c controlled by two qubits a and b."

Deutsch[ph_, qq:{__?QubitQ}, opts___?OptionQ] :=
  Deutsch[ph, FlavorNone @ qq, opts] /;
  Not[FlavorNoneQ @ qq]

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

ControlledGate::nonuni = "The operator `` is not unitary."

ControlledGate::incmp =  "Control register `` and value set `` have unequal lengths."

SetAttributes[ControlledGate, NHoldFirst]

SyntaxInformation[ControlledGate] = {
  "ArgumentsPattern" -> {_, __}
 }

ControlledGate[cc:(_?QubitQ|{__?QubitQ})] := (
  CheckArguments[ControlledGate[cc], 2];
  ControlledGate[cc, 1]
 )


ControlledGate[S_?QubitQ, rest__] :=
  ControlledGate[S @ {$} -> {1}, rest]

ControlledGate[ss:{___?QubitQ}, rest__] :=
  ControlledGate[FlavorNone[ss] -> Table[1, Length @ ss], rest]
(* NOTE: ___ not __; see fallback below. *)


ControlledGate[Rule[c_?QubitQ, v_], rest__] :=
  ControlledGate[{c} -> {v}, rest]

ControlledGate[Rule[cc:{___?QubitQ}, v_], rest__] :=
  ControlledGate[cc -> Table[v, Length @ cc], rest] /; Not[ListQ @ v]
(* NOTE: ___ not __; see fallback below. *)

ControlledGate[Rule[cc:{__?QubitQ}, vv_List], rest__] := (
  Message[ControlledGate::incmp, cc, vv];
  ControlledGate[cc -> PadRight[vv, Length @ cc, 1], rest]
 ) /; Length[cc] != Length[vv]


ControlledGate[Rule[cc:{__?QubitQ}, vv_], rest__] :=
  ControlledGate[FlavorNone[cc] -> vv, rest] /;
  Not[FlavorNoneQ @ cc]


ControlledGate[{} -> {}, op_] := op (* fallback *)


ControlledGate[Rule[ss:{__?QubitQ}, vv_], z_?CommutativeQ, opts___?OptionQ] :=
  With[
    { ff = If[Last[vv] == 0, -1, 1, 1] },
    If[ Abs[z] != 1, Message[ControlledGate::nonuni, z] ];
    If[ Length[ss] > 1,
      ControlledGate[ Rule[Most @ ss, Most @ vv],
        Phase[ff*Arg[z], Last[ss][3], opts] ],
      Phase[ff*Arg[z], Last[ss][3], opts]
     ]
   ]


theControlledGate[cc_Rule, op_] := Module[
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
    Garner @ {
      Rotation[-(a-c)/2, tt[3], "Label" -> "C"],
      CNOT[cc, tt],
      EulerRotation[{0, -b/2, -(a+c)/2}, tt, "Label" -> "B"],
      CNOT[cc, tt],
      EulerRotation[{a, b/2, 0}, tt, "Label" -> "A"],
      ControlledGate[cc, ff] }
   ]
 ]

ControlledGate /:
Expand @ ControlledGate[cc_Rule, op_, ___?OptionQ] :=
  Sequence @@ theControlledGate[cc, op] /; Length[Qubits @ op] == 1


ControlledGate /:
Dagger @ ControlledGate[sv_Rule, expr_, opts___?OptionQ] :=
  ControlledGate[sv, Dagger[expr], opts]


ControlledGate /:
Elaborate[op_ControlledGate] = op (* fallback *)

ControlledGate /:
Elaborate @
  ControlledGate[Rule[ss:{__?QubitQ}, vv:{__?BinaryQ}], op_, ___?OptionQ] :=
  Module[
    { rr = Thread[vv -> vv],
      prj },
    prj = Multiply @@ Elaborate @ MapThread[Construct, {ss, rr}];
    Garner[prj ** Elaborate[op] + (1 - prj)]
   ]


ControlledGate /:
Matrix[
  op:ControlledGate[Rule[{__?QubitQ}, {__?BinaryQ}], _, ___?OptionQ],
  rest___ ] := Matrix[Elaborate[op], rest]

ControlledGate /:
Matrix[op_ControlledGate, ss:{__?SpeciesQ}] :=
  op * One[Times @@ Dimension @ ss]


ControlledGate /:
Multiply[ pre___,
  ControlledGate[Rule[cc:{__?QubitQ}, vv:{__?BinaryQ}], op_, ___?OptionQ],
  in_Ket ] := With[
    { xx = in[cc] },
    If[ xx == vv,
      Multiply[pre, op ** in],
      Multiply[pre, in],
      Multiply[pre, in]
     ]
   ]

Multiply[ pre___,
  op:ControlledGate[Rule[{__?QubitQ}, {__?BinaryQ}], _, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
(* NOTE: DO NOT put "ControlledGate /:". Otherwise, the above rule with
   ControlledGate[...]**Ket[] is overridden. *)


ControlledU::usage = "ControlledU[...] is obsolete. Use Elaborate[ControlledGate[...]] instead."

ControlledU[args___] := (
  Message[
    Q3General::obsolete,
    "ControlledU",
    "Elaborate[ControlledGate[...]]"
   ];
  Elaborate @ ControlledGate[args]
 )

(**** </ControlledGate> ****)


(**** <ControlledPower> ****)

ControlledExp::usage = "ControlledExp is an alias of ControlledPower."

ControlledPower::usage = "ControlledPower[{c1, c2, ...}, op] represents a controlled exponentiation gate."


Options[ControlledPower] = {
  "Label" -> {"x", "U"}
 }

ControlledPower[S_?QubitQ, expr_, opts___?OptionQ] :=
  ControlledPower[{S[$]}, expr, opts]

ControlledPower[ss:{__?QubitQ}, expr_, opts___?OptionQ] :=
  ControlledPower[FlavorNone @ ss, expr, opts] /;
  Not[FlavorNoneQ @ ss]


ControlledPower /:
Dagger @ ControlledPower[ss:{__?QubitQ}, expr_, opts___?OptionQ] :=
  ControlledPower[ss, Dagger[expr], opts]


ControlledPower /:
Elaborate[op_ControlledPower] = op (* fallback *)

ControlledPower /:
Elaborate @ ControlledPower[cc:{__?QubitQ}, op_, ___] :=
  Module[
    { bs = Dyad[#, #, cc]& /@ Basis[cc],
      xx = Range[Power[2, Length @ cc]] - 1,
      yy },
    yy = MultiplyPower[op, #]& /@ xx;
    Elaborate @ Total @ Multiply[bs, yy]
   ]


ControlledPower /: (* fallback *)
Matrix[op_ControlledPower, ss:{__?SpeciesQ}] :=
  op * One[Times @@ Dimension @ ss]

If[ And[$VersionNumber == 13.2, $ReleaseNumber == 0],
  (* NOTE: Because of a BUG in MatrixPower of Mathematica 13.2,
     which crashes the kernel, this is a temporary work around. *)
  (* for v13.2.0 *)
  ControlledPower /:
  Matrix[ControlledPower[cc_, op_, ___], ss:{__?SpeciesQ}] :=
    Matrix[Elaborate @ ControlledPower[cc, op], ss],
  (* for other versions of Mathematica *)
  ControlledPower /:
  Matrix[ControlledPower[cc_, op_, ___], ss:{__?SpeciesQ}] :=
    Module[
      { tt = Qubits @ {cc, op},
        mat },
      mat = theCtrlExp[Length @ cc, Matrix[op]];
      Matrix[ExpressionFor[mat, tt], ss]
     ]
 ]


ControlledPower /:
Multiply[pre___, ControlledPower[cc_, op_, ___], in_Ket] :=
  With[
    { x = FromDigits[in[cc], 2] },
    Multiply[pre, Elaborate[MultiplyPower[op, x] ** in]]
   ]

HoldPattern @ Multiply[pre___, op_ControlledPower, post___] :=
  Multiply[pre, Elaborate @ op, post]
(* NOTE: DO NOT put "ControlledPower /:". *)

ControlledPower /:
Expand @ ControlledPower[ss:{__?QubitQ}, op_, opts:OptionsPattern[]] :=
  Module[
    { n = Length @ ss,
      tt = Qubits[op],
      pwr, txt, new },
    pwr = OperatorOn[tt] /@ Table[MultiplyPower[op, Power[2, n-k]], {k, n}];
    (* NOTE: Without OperatorOn, some elements in pwr may be 1. *)

    txt = OptionValue[ControlledPower, opts, "Label"];
    If[ListQ[txt], txt = Last @ txt];
    txt = Table["Label" -> Superscript[txt, Superscript[2, n-k]], {k, n}];
    
    new = ReplaceAll[
      MapThread[ControlledGate, {ss, pwr, txt}],
      ControlledGate[args__] -> ControlledGate[args, "LabelSize" -> 0.65, opts]
     ];
    Sequence @@ new
   ]

theCtrlExp::usage = "theCtrlExp[n, m] is the matrix version of ControlledPower."

theCtrlExp[n_Integer, mat_?MatrixQ] := Module[
  { bb = Tuples[{0, 1}, n], xx, mm },
  xx = FromDigits[#, 2] & /@ bb;
  mm = MatrixPower[mat, #] & /@ xx;
  bb = Dyad[#, #] & /@ One @ Power[2, n];
  Total @ MapThread[CircleTimes, {bb, mm}]
 ]


OperatorOn::usage = "OperatorOn[op, {s1, s2, \[Ellipsis]}] represents an operator acting on the system of species {s1, s2, \[Ellipsis]}.\nOperatorOn is a low-level function intended for internal use."

OperatorOn[ss:{___?SpeciesQ}] :=
  OperatorOn[FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

OperatorOn[ss:{___?SpeciesQ}][op_] := OperatorOn[op, ss]

OperatorOn[op_, ss:{___?SpeciesQ}] := Module[
  { tt = Agents[op] },
  Union[ss, tt] /; Not @ ContainsAll[ss, tt]
 ]

OperatorOn[op_, ss:{___?SpeciesQ}] :=
  OperatorOn[op, FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

OperatorOn /:
Multiply[pre___, OperatorOn[op_, {___?SpeciesQ}], post___] :=
  Multiply[pre, op, post]

(**** </ControlledPower> ****)


(**** <UniformlyControlledRotation> ****)

(* SEE: Schuld and Pertruccione (2018), Mottonen et al. (2005) *)

UniformlyControlledRotation::usage = "UniformlyControlledRotation[{c1,c2,\[Ellipsis],cn}, {a1,a2,\[Ellipsis],a2n}, s[\[Ellipsis],k]] represents the uniformly controlled rotation on qubit s[\[Ellipsis],$] around the k-axis by andles a1, a2, \[Ellipsis], a2n  depending on all possible bit sequences of control qubits c1, c2, \[Ellipsis], cn."

UniformlyControlledRotation::list = "The length of `` is not an integer power of 2."

SyntaxInformation[UniformlyControlledRotation] = {
  "ArgumentsPattern" -> {_, _, _, __}
 }

AddElaborationPatterns[_UniformlyControlledRotation]


UniformlyControlledRotation[
  cc:{___?QubitQ}, aa_?VectorQ, S_?QubitQ,
  opts___?OptionQ ] :=
  UniformlyControlledRotation[ cc, aa,
    UnitVector[3, FlavorLast @ S], FlavorMute @ S,
    opts ]

UniformlyControlledRotation[
  cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, ___?OptionQ ] := (
    Message[UniformlyControlledRotation::list, aa];
    UniformlyControlledRotation[cc, PadRight[aa, Power[2, Length @ cc]], vv, S]
   ) /; Power[2, Length @ cc] != Length[aa]

UniformlyControlledRotation[{}, {a_}, v:{_, _, _}, S_?QubitQ] :=
  Rotation[a, v, S]


UniformlyControlledRotation /:
Dagger @ UniformlyControlledRotation[
  cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, ___?OptionQ ] :=
  UniformlyControlledRotation[cc, -aa, vv, S]

UniformlyControlledRotation /:
Expand @ UniformlyControlledRotation[
  cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ, ___?OptionQ ] :=
  Sequence @@ Thread @ ReleaseHold @
  ControlledGate[
    Thread[Hold[cc] -> Tuples[{0, 1}, Length @ cc]],
    Rotation[aa, vv, S]
   ]

UniformlyControlledRotation /:
Matrix[
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ ],
  rest___ ] := Dot @@ Matrix[{Expand @ op}, rest]


UniformlyControlledRotation /:
Elaborate @
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ ] :=
  With[ {qq = Qubits @ op}, Elaborate @ ExpressionFor[Matrix[op, qq], qq] ]


UniformlyControlledRotation /:
Multiply[ pre___,
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ],
  in_Ket ] := With[
    { gg = {Expand @ op} },
    Multiply[pre, Fold[Multiply[#2, #1]&, in, gg]]
   ]

Multiply[ pre___,
  op:UniformlyControlledRotation[
    {__?QubitQ}, _?VectorQ, {_, _, _}, _?QubitQ, ___?OptionQ],
  post___ ] :=
  Multiply[pre, Elaborate[op], post]
(* NOTE: DO NOT put "UniformlyControlledRotation /:". Otherwise, the above
   rule with UniformlyControlledRotation[...]**Ket[] is overridden. *)

(**** </UniformlyControlledRotation> ****)


(**** <GateFactor> ****)

UniformlyControlledRotation /:
GateFactor @ UniformlyControlledRotation[
  cc:{__?QubitQ}, aa_?VectorQ, vv:{_, _, _}, S_?QubitQ,
  opts___?OptionQ ] := Module[
    { n = Length[cc],
      bb, gg, mm, tt },
    bb = Tuples[{0, 1}, n];
    gg = BinaryToGray /@ bb;
    mm = Power[2, -n] * Power[-1, Outer[Dot, gg, bb, 1]];
    tt = Rotation[mm.aa, vv, S];
    gg = ReleaseHold @ Thread[Hold[CNOT][sequenceCNOT @ cc, S]];
    Sequence @@ Riffle[tt, gg]
   ] /; Chop[First @ vv] == 0


sequenceCNOT::usage = "Returns a list of control qubits of CNOT gates to be used to efficiently factorize a uniformly-controlled gate."

sequenceCNOT[{c_}] := {c, c}

sequenceCNOT[cc:{_, __}] := With[
  { new = ReplacePart[sequenceCNOT[Rest@cc], -1 -> First[cc]] },
  Join[new, new]
 ]

(**** </GateFactor> ****)


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

Oracle::usage = "Oracle[f, control, target] represents the quantum oracle which maps Ket[x]\[CircleTimes]Ket[y] to Ket[x]\[CircleTimes]Ket[f(x)\[CirclePlus]y]. Each control and target can be list of qubits."

Oracle /:
NonCommutativeQ[ Oracle[___] ] = True

Oracle[f_, c_?QubitQ, t_?QubitQ, opts___?OptionQ] :=
  Oracle[f, {c}, {t}, opts]

Oracle[f_, c_?QubitQ, tt:{__?QubitQ}, opts___?OptionQ] :=
  Oracle[f, {c}, tt, opts]

Oracle[f_, cc:{__?QubitQ}, t_?QubitQ, opts___?OptionQ] :=
  Oracle[f, cc, {t}, opts]

Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  Oracle[f, FlavorNone @ cc, FlavorNone @ tt, opts] /;
  Not[FlavorNoneQ @ Join[cc, tt]]

Oracle /:
Dagger[op_Oracle] := op

Oracle /:
HoldPattern @ Multiply[pre___, op_Oracle, post___] :=
  Multiply[pre, Elaborate[op], post]


Oracle /:
Elaborate @ Oracle[f_, cc : {__?QubitQ}, tt : {__?QubitQ}] := Module[
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
Matrix @ Oracle[f_, cc:{__?QubitQ}, tt:{__?QubitQ}] := Module[
  { bb = Range[Power[2, Length @ cc]] }, 
  bb = GroupBy[
    IntegerDigits[bb-1, 2, Length @ cc], 
    Oracle[f, Length @ cc, Length @ tt]
   ] /. {0 -> 10, 1 -> 11};
  bb = KeyMap[
    Apply[ThePauli],
    Total /@ Map[Apply[ThePauli], bb, {2}]
   ];
  Total @ KeyValueMap[CircleTimes[#2, #1]&, bb]
 ]


VerifyOracle::usage = "VerifyOracle has been excises since Q3 v2.12.1."

VerifyOracle[args___] := Message[Q3General::excised, "VerifyOracle"]

(**** </Oracle> ****)


(**** <QFT> ****)

QFT::usage = "QFT[{S1, S2, \[Ellipsis]}] represents the quantum Fourier transform on the qubits S1, S2, \[Ellipsis].\nDagger[QFT[\[Ellipsis]]] represents the inverse quantum Fourier transform.\nElaborate[QFT[\[Ellipsis]]] returns the explicit expression of the operator in terms of the Pauli operators."

QFT::badmat = "Some elements of `` does not appear in `` for Matrix[QFT[\[Ellipsis]]]."

Options[QFT] = {N -> False}

QFT /: NonCommutativeQ[ QFT[___] ] = True

QFT /:
MultiplyKind @ QFT[{__?QubitQ}] = Qubit

QFT /:
MultiplyGenus @ QFT[___] := "Singleton"


QFT[{}] = 1

QFT[S_?QubitQ, ___?OptionQ] := S[6]

QFT[{S_?QubitQ}, ___?OptionQ] := S[6]

QFT[qq:{__?QubitQ}, opts___?OptionQ] :=
  QFT[FlavorNone @ qq, opts] /;
  Not[FlavorNoneQ @ qq]


QFT /: Elaborate[op_QFT] = op (* fallback *)

QFT /:
Elaborate[op:QFT[{__?QubitQ}, ___?OptionQ]] :=
  Elaborate @ ExpressionFor[Matrix[op], Qubits @ op]

QFT /:
Multiply[pre___, op:QFT[{__?QubitQ}, ___?OptionQ], post___] :=
  Multiply[pre, Elaborate[op], post]

HoldPattern @
  Multiply[pre___, Dagger[op:QFT[{__?QubitQ}, ___?OptionQ]], post___] :=
  Multiply[pre, Dagger[Elaborate @ op], post]


QFT /:
Matrix @ QFT[qq:{__?QubitQ}, opts___?OptionQ] := With[
  { mat = FourierMatrix @ Power[2, Length @ qq] },
  If[TrueQ[N /. {opts} /. Options[QFT]], N @ mat, mat]
 ]

QFT /:
Matrix[QFT[qq:{__?QubitQ}, opts___?OptionQ], ss:{__?QubitQ}] :=
  Matrix @ QFT[qq, opts] /;
  FlavorNone[qq] == FlavorNone[ss]

QFT /:
Matrix[QFT[qq:{__?QubitQ}, opts___?OptionQ], ss:{__?QubitQ}] :=
  MatrixEmbed[FourierMatrix @ Power[2, Length @ qq], qq, ss] /;
  ContainsAll[FlavorNone @ ss, FlavorNone @ qq]

QFT /:
Matrix[QFT[qq:{__?QubitQ}, opts___?OptionQ], ss:{__?QubitQ}] := (
  Message[QFT::badmat, FlavorNone @ qq, FlavorNone @ ss];
  One @ Length[ss]
 )

HoldPattern @ Matrix[Dagger[op_QFT], rest___] :=
  Topple @ Matrix[op, rest]


QFT /:
Expand[op_QFT] = op (* fallback *)

QFT /:
Expand @ QFT[ss:{__?QubitQ}, ___] := Sequence @@ Join[
  qftCtrlPhase[ss][All],
  With[{n = Length[ss]}, Table[SWAP[ss[[j]],ss[[n-j+1]]], {j, n/2}]]
 ]

qftCtrlPhase[ss:{__?QubitQ}] := 
  qftCtrlPhase[FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

qftCtrlPhase[ss:{__?QubitQ}][All] :=
  Map[qftCtrlPhase[ss], Range @ Length @ ss]

qftCtrlPhase[ss:{__?QubitQ}][k_Integer] := Sequence @@ With[
  { T = ss[[k]] },
  Append[
    Table[
      ControlledGate[ ss[[{j}]] -> {1}, T[C[j-k-1]], 
        "Label" -> Subscript["T", k-j] ],
      {j, k-1} ],
    T[6]]
 ]


Dagger /:
Expand[HoldPattern @ Dagger[op_QFT]] = Dagger[op] (* fallback *)

Dagger /:
HoldPattern @ Expand @ Dagger @ QFT[ss:{__?QubitQ}, ___] :=
  Sequence @@ Join[
    invCtrlPhase[ss][All],
    With[{n = Length[ss]}, Table[SWAP[ss[[j]],ss[[n-j+1]]], {j, n/2}]]
   ]

invCtrlPhase[ss:{__?QubitQ}] := 
  invCtrlPhase[FlavorNone @ ss] /; Not[FlavorNoneQ @ ss]

invCtrlPhase[ss:{__?QubitQ}][All] :=
  Map[invCtrlPhase[ss], Range @ Length @ ss]

invCtrlPhase[ss:{__?QubitQ}][k_Integer] := Sequence @@ With[
  { T = ss[[k]] },
  Append[
    Table[
      ControlledGate[ ss[[{j}]] -> {1}, Dagger @ T[C[j-k-1]], 
        "Label" -> Subsuperscript["T", k-j, "\[Dagger]"] ],
      {j, k-1} ],
    T[6]]
 ]

(**** </QFT> ****)


(**** <Projector> ****)

Projector::usage = "Projector[state, {q1, q2, ...}] represents the projection operator on the qubits {q1, q2, ...} into state, which is given in the Ket expression.\nProjector[expr] automatically extracts the list of qubits from expr."

Projector::noket = "No Ket expression found for projection in the provided expression ``. Identity operator is returned."

Projector /:
Dagger[ op_Projector ] = op

Projector /:
Expand[ Projector[v_, qq_List] ] := Dyad[v, v, qq]

Projector /:
DyadForm[ Projector[v_, qq_List] ] := Dyad[v, v, qq]

Projector /:
Elaborate[ op:Projector[_, _List] ] := Elaborate[Expand @ op]

Projector /:
Matrix[ op:Projector[_, _List], qq:{__?SpeciesQ}] :=
  Matrix[Elaborate[op], qq]


Projector[expr_, {}] = 1

Projector[expr_] := Projector[expr, Qubits @ expr]

Projector[expr_, q_?QubitQ] := Projector[expr, q @ {$}]

Projector[expr_, qq:{__?QubitQ}] :=
  Projector[expr, FlavorNone @ qq] /; Not[FlavorNoneQ @ qq]

Projector[expr_, qq:{__?QubitQ}] :=
  (Message[Projector::noket, expr]; 1) /; FreeQ[expr, _Ket]

(**** </Projector> ****)


(***** <Measurement> ****)

Measurement::usage = "Measurement[op] represents the measurement of Pauli operator op. Pauli operators include tensor products of the single-qubit Pauli operators.\nMeasurement[{op1, op2, \[Ellipsis]}] represents consecutive measurement of Pauli operators op1, op2, \[Ellipsis] in the reverse order."

Measurement::nonum = "Probability half is assumed for a state without explicitly numeric coefficients."

Measurement::novec = "The expression `` does not seem to be a valid Ket expression. Null vector is returned."

SyntaxInformation[Measurement] = {
  "ArgumentsPattern" -> {_}
 }

Measurement[op_List][vec_] :=
  Construct[Composition @@ Map[Measurement, op], vec]

Measurement[op_][vec_] := Module[
  { odds = MeasurementOdds[op][vec],
    rand = RandomReal[] },
  Garner @ If[ rand < Re @ First @ odds[0],
    $MeasurementOut[op] = 0; Last @ odds[0],
    $MeasurementOut[op] = 1; Last @ odds[1],
    Message[Measurement::nonum];
    If[ rand < 1/2,
      $MeasurementOut[op] = 0; Last @ odds[0],
      $MeasurementOut[op] = 1; Last @ odds[1]
     ]
   ]
 ]


Measurement /:
Dot[Measurement[mat_?MatrixQ], vec_?VectorQ] :=
  Measurement[mat] @ vec

Measurement /:
Dot[Measurement[mm:{__?MatrixQ}], vec_?VectorQ] :=
  Measurement[mm] @ vec

Measurement /:
Multiply[pre___, spr_Measurement, expr_] :=
  Multiply[pre, spr @ expr] /; Not @ FreeQ[expr, _Ket]

Measurement /:
Matrix[Measurement[op_], ss:{__?QubitQ}] :=
  Measurement[Matrix[op, ss]]


$MeasurementOut::usage = "$MeasurementOut gives the measurement results in an Association of elements op$j->value$j."


Readout::usage = "Readout[expr, S] or Readout[expr, {S1, S2, ...}] reads the measurement result from the expr that is supposed to be the state vector after measurements."

Readout::nopauli = "`` is not a Pauli operator. Only Pauli operators (including tensor products of single-qubit Pauli operators) can be measured and readout."

Readout::notob = "`` (or some of its elements if it is a list) has never been measured. First use Measurement before using Readout."

SyntaxInformation[Readout] = {
  "ArgumentsPattern" -> {_}
 }

Readout[Measurement[op_]] := Readout[op]

Readout[op_] := (
  If[ Not @ KeyExistsQ[$MeasurementOut, op],
    Message[Readout::notob, op]
   ];
  $MeasurementOut[op]
 )
(* NOTE: op may be a matrix or an operator expression. *)

Readout[op_List] := (
  If[ Not @ AllTrue[op, KeyExistsQ[$MeasurementOut, #]&],
    Message[Readout::notob, op]
   ];
  Lookup[$MeasurementOut, op]
 )
(* NOTE: op may be a list of matrices or operator expressions. *)


MeasurementOdds::usage = "MeasurementOdds[op][vec] theoretically analyzes the process of meauring operator op on state vec and returns an association of elements of the form value->{probability, state}, where value is one of the possible measurement outcomes 0 and 1 (which correspond to eitemvalues +1 and -1, respectively, of op), probability is the probability for value to be actually observed, and state is the post-measurement state when value is actually observed."

MeasurementOdds::pauli = "`` is not an observable Pauli operator."

SyntaxInformation[MeasurementOdds] = {
  "ArgumentsPattern" -> {_}
 }

(* NOTE: DO NOT use op_?PauliQ; it will inerfere with mat_?MatrixQ below. *)
MeasurementOdds[op_][vec_?fKetQ] := Module[
  { ss = Qubits[{vec, op}],
    aa },
  If[ Not[obsPauliQ @ op],
    Message[MeasurementOdds::pauli, op];
    Return[<|0 -> {1, Ket[]}, 1 -> {0, 0}|>]
   ];
  aa = MeasurementOdds[Matrix[op, ss]][Matrix[vec, ss]];
  aa[0] = {First @ aa[0], ExpressionFor[Last @ aa[0], ss]};
  aa[1] = {First @ aa[1], ExpressionFor[Last @ aa[1], ss]};
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
 ] (* /; PauliQ[mat] *)

(* NOTE: Test PauliQ[mat] may take long for 8 or more qubits. *)
(* NOTE:
   1. vec, pls, or mns may be 0 (null vector).
   2. The norms of pls and mns may have imaginary parts numerically.
   3. When the vector components are symbolic,
      the post-measurement states are NOT normalized.
   *)


obsPauliQ::usage = "obsPauliQ[op] returns True if op is either a single-qubit Pauli operator or a tensor product of single-qubit Pauli operators (without any factor of \[PlusMinus]I); and False, otherwise.\nSuch an 'observable' Pauli operator has eigenvalue \[PlusMinus]1; hence 'observable'."

obsPauliQ[Pauli[(0|1|2|3)..]] = True

obsPauliQ[_?QubitQ[___, 0|1|2|3]] = True

obsPauliQ[HoldPattern @ Multiply[(_?QubitQ[___, 0|1|2|3])..]] = True

obsPauliQ[expr_] := obsPauliQ[Elaborate @ expr] /;
  Not @ FreeQ[expr, _?QubitQ[___, 4|5|6|7|8|9|10|11]]

obsPauliQ[_] = False


Measurements::usage = "Measurments[expr] returns a list of Pauli operators (including the tensor products of single-qubit Pauli operators) measured during the process of expression expr."

Measurements[expr_] := Union @ Flatten @
  Cases[{expr}, Measurement[m_] -> m, Infinity, Heads -> False]

(**** </Measurement> ****)


(**** <MeasurementFunction> ****)

MeasurementFunction::usage = "MeasurementFunction[{m1,m2,\[Ellipsis]}] represents a sequence of operations or measurements m1, m2, \[Ellipsis]."

Format[fun:MeasurementFunction[gg:{(_Measurement|_?MatrixQ)..}]] := With[
  { dim = Riffle[Dimensions @ FirstCase[gg, _?MatrixQ], "\[Times]"] },
  Interpretation[
    StringForm["MeasurementFunction[{``\[Ellipsis]}]", ToString @ Row @ dim],
    fun ]
 ]

Format[fun:MeasurementFunction[gg:{__}]] := 
  Interpretation[
    StringForm["MeasurementFunction[``]", Qubits @ gg],
    fun
   ]

MeasurementFunction[gg:{(_Measurement|_?MatrixQ)..}][v_?VectorQ] :=
  Fold[Dot[#2, #1]&, v, gg]

MeasurementFunction[gg:{__}][expr_] :=
  Fold[Garner[Multiply[#2, #1]]&, expr, gg] /;
  Not @ FreeQ[expr, Ket[_Association]|_ProductState]


MeasurementFunction /:
Dot[MeasurementFunction[mm:{(_Measurement|_?MatrixQ)..}], vec_?VectorQ] :=
  MeasurementFunction[mm][vec]

MeasurementFunction /:
Multiply[pre___, spr_MeasurementFunction, expr_] :=
  Multiply[pre, spr @ expr] /; Not @ FreeQ[expr, _Ket|_ProductoState]

(**** </MeasurementFunction> ****)


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
    { ss = Union[Keys @ a, FlavorNone @ gg] },
    Block[
      { Missing },
      Missing["KeyAbsent", _Symbol?QubitQ[___, $]] := {1, 0};
      ProductState[AssociationThread[ss -> Lookup[a, ss]], opts]
     ]
   ]

ProductState /:
Elaborate[ ProductState[a_Association, ___] ] := Garner[
  CircleTimes @@ KeyValueMap[ExpressionFor[#2, #1]&, a]
 ]

ProductState /:
Matrix[ ket_ProductState ] :=
  Matrix[Elaborate @ ket]

ProductState /:
Matrix[ ket_ProductState, qq:{__?QubitQ} ] :=
  Matrix[Elaborate @ ket, qq]

ProductState /:
NonCommutativeQ[ ProductState[___] ] = True

ProductState /:
MultiplyKind[ ProductState[___] ] = Ket

ProductState /:
MultiplyGenus[ ProductState[___] ] = "Ket"

HoldPattern @
  Multiply[pre___, vec:ProductState[_Association, ___], post___] :=
  Garner @ Multiply[pre, Elaborate[vec], post]


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
  Append[v, spec] /; KeyExistsQ[Options[ProductState], First @ spec]

ProductState[ ProductState[a_Association, opts___],
  rule:Rule[_?QubitQ, {_, _}] ] :=
  ProductState[KeySort @ Append[a, FlavorNone @ rule], opts]

ProductState[
  ProductState[a_Association, opts___],
  rule:Rule[{__?QubitQ}, {{_, _}..}]
 ] := ProductState[
   KeySort @ Join[a, AssociationThread[FlavorNone /@ rule]],
   opts
  ]

ProductState[
  ProductState[a_Association, opts___],
  Rule[gg:{__?QubitQ}, v:{_, _}]
 ] := With[
   { b = AssociationMap[(v)&, FlavorNone @ gg] },
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
    Lookup[a, FlavorNone @ qq]
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


DickeState::usage = "DickeState[qubits, n] gives the generalized Dicke state for the qubits, where n qubits are in the state Ket[1]."

DickeState[ss:{__?QubitQ}, n_] := Module[
  { byte = ConstantArray[1, n] },
  byte = PadRight[byte, Length @ ss];
  byte = Permutations[byte];
  Total[ Map[Ket[ss -> #]&, byte] ] / Sqrt[Length[byte]]
 ]

DickeState[ss:{__?QubitQ}] := Table[DickeState[ss, n], {n, 0, Length @ ss}]


RandomState::usage = "RandomState[{S1,S2,...}] gives a normalized random state for the system of multiple qubits {S1,S2,...}.
  RandomState[{S1,S2,...}, n] gives n mutually orthogonal normalized random states."

RandomState[S_?QubitQ] := RandomState[{S}]

RandomState[S_?QubitQ, n_Integer] := RandomState[{S}, n]

RandomState[qq : {__?QubitQ}] := Module[
  { cc = RandomComplex[{-1 - I, 1 + I}, Power[2, Length[qq]]] },
  cc = Normalize[cc];
  cc.Basis[qq]
 ]

RandomState[qq : {__?QubitQ}, n_Integer] := Module[
  { bb = Basis[qq],
    dd = Power[2, Length[qq]],
    cc },
  cc = RandomComplex[{-1 - I, 1 + I}, n * dd];
  cc = Partition[cc, dd];
  cc = Orthogonalize[cc];
  Map[ (#.bb)&, cc ]
 ]


(**** <GHZState for Qubits> ****)

GHZState::usage = "GHZState[{s1,s2,\[Ellipsis]}, k] returns the kth generalized GHZ state for species {s1,s2,\[Ellipsis]}.\nGHZState[{s1,s2,\[Ellipsis]}] returns the list of all GHZ states of species {s1,s2,\[Ellipsis]}.\nSee also Wolf (2003).";

GHZState[ss:{__?QubitQ}] :=
  Map[GHZState[ss, #]&, Range[0, Power[2, Length @ ss] - 1]]

GHZState[ss:{__?QubitQ}, k_Integer] := Module[
  { kk = IntegerDigits[k, 2, Length @ ss],
    nn },
  nn =  Mod[kk+1, 2];
  (Ket[ss->kk] + Ket[ss->nn]*Power[-1, First @ kk]) / Sqrt[2]
 ]

(**** </GHZState> ****)


(**** <SmolinState> ****)

SmolinState::usage = "SmolinState[{s1,s2,\[Ellipsis]}] returns the generalized Smolin state for qubits {s1,s2,\[Ellipsis]}. See also Augusiak and Horodecki (2006).";

SmolinState::badsys = "A generalized Smolin state is defined only for an even number of qubits: `` has an odd number of qubits. Returning the generalized Smolin state for the qubits excluding the last."

SmolinState[ss:{__?QubitQ}] := (
  Message[SmolinState::badsys, FlavorNone @ ss];
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

GraphState[g_Graph] := GraphState[g, FlavorNone @ VertexList @ g] /;
  AllTrue[VertexList @ g, QubitQ]

GraphState[g_Graph, ss:{__?QubitQ}] := (
  Message[GraphState::msmtch, g, FlavorNone @ ss];
  Ket[]
 ) /; Length[VertexList @ g] != Length[ss]

GraphState[g_Graph, ss:{__?QubitQ}] := Module[
  { dd = Power[2, Length @ ss],
    vv = VertexList[g],
    cz = EdgeList[g],
    in, rr },
  rr = Thread[vv -> FlavorNone[ss]];
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

GraphStateBasis[g_Graph] := GraphStateBasis[g, FlavorNone @ VertexList @ g] /;
  AllTrue[VertexList @ g, QubitQ]

GraphStateBasis[g_Graph, ss:{__?QubitQ}] := (
  Message[GraphStateBasis::msmtch, g, FlavorNone @ ss];
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

AddElaborationPatterns[_ModMultily];

ModMultiply /: NonCommutativeQ[_ModMultiply] = True

ModMultiply /: MultiplyKind[_ModMultiply] = Qubit

ModMultiply /: MultiplyGenus[_ModMultiply] = "Singleton"

ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] := (
  Message[ModMultiply::order, n, Power[2, Length @ tt]];
  ModMultiply[Power[2, Length @ tt], cc, tt, opts]
 ) /; n > Power[2, Length @ tt]

ModMultiply[n_Integer, cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ] :=
  ModMultiply[n, FlavorNone @ cc, FlavorNone @ tt, opts] /;
  Not[FlavorNoneQ @ Join[cc, tt]]


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
  ModMultiply[n, x, FlavorNone @ tt, opts] /;
  Not[FlavorNoneQ @ tt]

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
  op:ModMultiply[_Integer, _IntegerQ, tt:{__?QubitQ}, ___?OptionQ]
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
  If[ $VersionNumber < 13.3,
    Format @ x[j___, a_ -> b_] := Interpretation[
      SpeciesBox[ Row @ {"(", Ket[b], Bra[a], ")"}, {j}, {}],
      x[j, a -> b]
     ],
    Format @ x[j___, a_ -> b_] := Interpretation[
      SpeciesBox[ Row @ {"(", Ket @ {b}, Bra @ {a}, ")"}, {j}, {}],
      x[j, a -> b]
     ]
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


(* FlavorNone: See Cauchy *)

FlavorNone[S_?QuditQ] := S[$]


(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?QuditQ] := S[$]

FlavorMute[S_Symbol?QuditQ[k___, _]] := S[k, $]

FlavorMute[S_Symbol?QuditQ[k___, _] -> m_] := S[k, $] -> m


(**** <Ket for Qudits> ****)

theKetTrim[Rule[_?QuditQ, 0]] = Nothing

KetVerify::qudit = "Invalid value `` for qudit ``."

KetVerify[a_?QuditQ, v_] := (
  Message[KetVerify::qudit, v, a];
  $Failed
 ) /; Not[0 <= v < Dimension[a]]
(* NOTE: The following definition would not allow to assign a symbolic value:
   KetVerify[ _?QuditQ, Except[0|1] ] = $Failed *)

(**** </Ket for Qubits> ****)


(**** <GHZState for Qudits> ****)

GHZState[ss:{__?QuditQ}] := Map[
  GHZState[ss, #]&,
  Range[0, Power[Dimension @ First @ ss, Length @ ss]-1]
 ]

GHZState[ss:{__?QuditQ}, k_Integer] := Module[
  { dim = Dimension[First @ ss],
    xx, kk, ww, vv },
  xx = Range[0, dim-1];
  kk = IntegerDigits[k, dim, Length @ ss];
  vv = Map[Mod[kk + #, dim]&,  xx];
  ww = Exp[I* 2*Pi * xx * First[kk] / dim] / Sqrt[dim];
  Map[Ket[ss -> #]&, vv] . ww
 ]

(**** </GHZState> ****)


(**** <WeylHeisenbergBasis> ****)

WeylHeisenbergBasis::usage = "WeylHeisenbergBasis[n] returns a generating set of matrices in GL(n).\nSee also Lie basis."

WeylHeisenbergBasis[d_Integer] := Module[
  { dd = Range[0, d-1],
    ww, ij },
  Z = SparseArray @ DiagonalMatrix @ Exp[I 2 Pi*dd/d];
  X = RotateRight @ One[d];
  MapApply[
    (MatrixPower[Z, #1] . MatrixPower[X, #2]) &,
    Tuples[dd, 2]
   ]
 ]

(**** </WeylHeisenbergBasis> ****)


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

HoldPattern @ Multiply[pre___,
  A_Symbol?QuditQ[j___, z_->w_], A_Symbol?QuditQ[j___, x_->y_],
  post___] := Multiply[pre, A[j, x->w], post] KroneckerDelta[y, z]

HoldPattern @ Multiply[pre___, A_?QuditQ, B_?QuditQ, post___] :=
  Multiply[pre, B, A, post] /; Not @ OrderedQ @ {A, B}


(**** <Basis> ****)

Basis[ S_?QuditQ ] :=
  Ket /@ Thread[FlavorNone[S] -> Range[0, Dimension[S]-1]]

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
  SparseArray[ {p -> 1}, Times @@ dd ]
 ]


(**** <Parity> ****)

Parity[A_?QuditQ] := Module[
  { jj = Range[0, Dimension[A]-1],
    op },
  op = A /@ Thread[jj->jj];
  Power[-1, jj] . op
 ]

ParityValue[v_Ket, a_?QuditQ] := 1 - 2*Mod[v[a], 2]

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

(**** </Matrix> *****)


(**** <TransformByFourier for Qudits> ****)

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


EndPackage[]
