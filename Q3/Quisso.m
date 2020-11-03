(* -*- mode: math; -*- *)

(****
  Mathematica Package to facilitate simulation of quantum information
  processing.
 
  Mahn-Soo Choi (Korea Univ, mahnsoo.choi@gmail.com)
  $Date: 2020-11-04 02:16:15+09 $
  $Revision: 1.4 $
  ****)

BeginPackage[ "Q3`Quisso`", { "Q3`Pauli`", "Q3`Cauchy`" } ]

Unprotect[Evaluate[$Context<>"*"]]

Print @ StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.4 $"][[2]], " (",
  StringSplit["$Date: 2020-11-04 02:16:15+09 $"][[2]], ") ",
  "Mahn-Soo Choi"
 ]


{ Qubit, QubitQ, Qubits,
  Classical, ClassicalQ };

{ SpinForm };

{ Dirac };

{ QuissoCollect, QuissoExpand };

{ QuissoExpression };

{ DensityMatrix, DensityOperator };

{ QuissoReduced, QuissoFactor,
  ReducedDensityMatrix };

{ QuissoCoefficientTensor, QuissoAssemble };

{ CommonEigensystem };

{ QuissoAdd, QuissoAddZ };

{ QuissoPhase, Phase,
  QuissoRotation, Rotation,
  QuissoEulerRotation, EulerRotation };

{ QuissoControlled, Controlled,
  QuissoCZ, CZ,
  QuissoCNOT, CNOT,
  QuissoSWAP, SWAP,
  QuissoToffoli, Toffoli,
  QuissoProjector, Projector,
  Measure, Readout };

{ ProductState, BellState, GraphState, DickeState, RandomState };

{ QuissoCircuit, QuissoIn, QuissoOut };

{ QuissoCorrelationTensor, QuissoCorrelationMatrix,
  QuissoNormalState };

(* Qudit *)

{ Qudit, QuditQ, Qudits };

{ TheQuditKet };

{ QuditExpression };


Begin["`Prelude`"]

$symbs = Unprotect[
  Multiply, MultiplyDegree, CircleTimes, OTimes, Dagger, Dyad,
  KetTrim, KetRule, Ket, Bra, BraKet, Basis,
  $GarnerHeads, $GarnerTests, $RepresentableTests, $RaiseLowerRules,
  DefaultForm, LogicalForm,
  Base, FlavorNone, FlavorMute, Missing,
  Rotation, EulerRotation,
  Matrix, Parity, ParityEvenQ, ParityOddQ
 ]

Quisso::obsolete = "`` is OBSOLETE, use `` instead."


Qubit::usage = "Qubit denotes a quantum two-level system or \"quantum bit\". A Qubit is declared by Let.\nLet[Qubit, S, T, ...] or Let[Qubit, {S, T,...}] declares that the symbols S, T, ... are dedicated to represent qubits and quantum gates operating on them. For example, S[j,..., None] or S[j,..., ] for short represents the qubit located at the physical site specified by the indices j, .... In the StandardForm, S[j,..., None] is formatted as S$j... . On the other hand S[j, ..., k] represents the quantum gate operating on the qubit S[j,..., None]. In the StandardForm, S[j, ..., k] is formatted as \*SubsuperscriptBox[S, RowBox[{j,\", ...\"}], k].\nS[..., 0] represents the identity operator.\nS[..., 1], S[..., 2] and S[..., 3] means the Pauli-X, Pauli-Y and Pauli-Z gates, respectively.\nS[..., 4] and S[..., 5] represent the raising and lowering operators, respectively.\nS[..., 6], S[..., 7], S[..., 8] represent the Hadamard, Quadrant (Pi/4) and Octant (Pi/8) gate, resepctively.\nS[..., (Raise|Lower|Hadamard|Quadrant|Octant)] are equivalent to S[..., (4|5|6|7|8)], respectively, but expanded immediately in terms of S[..., 1] (Pauli-X), S[..., 2] (Y), and S[..., 3] (Z).\nS[..., None] represents the qubit."

Options[Qubit] = { Classical -> False }

Qubit /:
Let[Qubit, {ls__Symbol}, opts___?OptionQ] := Module[
  { classic },
  classic = Classical /. {opts} /. Options[Qubit];

  Let[NonCommutative, {ls}];
  
  Scan[setQubit, {ls}];
 ]

setQubit[x_Symbol] := (
  Kind[x] ^= Qubit;
  Kind[x[___]] ^= Qubit;
  
  Dimension[x] ^= 2;
  Dimension[x[___]] ^= 2;  

  QubitQ[x] ^= True;
  QubitQ[x[___]] ^= True;

  x/: Dagger[ x[j___, k:(0|1|2|3|6)] ] := x[j, k];
  x/: Dagger[ x[j___, 4] ] := x[j,5];
  x/: Dagger[ x[j___, 5] ] := x[j,4];

  x/: Conjugate[ x[j___, k:(0|1|3|4|5|6)] ] := x[j, k];
  x/: Conjugate[ x[j___, 2] ] := -x[j, 2];
  x/: Conjugate[ x[j___, 7] ] := Dagger @ x[j, 7];
  x/: Conjugate[ x[j___, 8] ] := Dagger @ x[j, 8];

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___, Raise] := (x[j,1] + I x[j,2]) / 2;
  x[j___, Lower] := (x[j,1] - I x[j,2]) / 2;
  
  x[j___, Hadamard] := (x[j,1] + x[j,3]) / Sqrt[2];
  x[j___, Quadrant] := (1+I)/2 + x[j,3] (1-I)/2;
  x[j___, Octant]   := (1+Exp[I Pi/4])/2 + x[j,3] (1-Exp[I Pi/4])/2;

  x[j___, 10] := (x[j,0] + x[j,3]) / 2;
  x[j___, 11] := (x[j,0] - x[j,3]) / 2;
  
  x[j___, All]  := Flatten @ x[j, {1,2,3}];

  x[j___, Full] := Flatten @ x[j, {0,1,2,3}];
  
  x[j___, Null] := x[j, None];
  
  x[j___, None, k_] := x[j, k];
  (* In particular, x[j,None,None] = x[j,None]. *)
  
  Format[ x[j___,None] ] := DisplayForm @ SpeciesBox[x, {j}, {}];
  
  Format[ x[j___,0] ] := DisplayForm @ SpeciesBox[x, {j}, {0}];
  Format[ x[j___,1] ] := DisplayForm @ SpeciesBox[x, {j}, {"x"}];
  Format[ x[j___,2] ] := DisplayForm @ SpeciesBox[x, {j}, {"y"}];
  Format[ x[j___,3] ] := DisplayForm @ SpeciesBox[x, {j}, {"z"}];
  Format[ x[j___,4] ] := DisplayForm @ SpeciesBox[x, {j}, {"+"}];
  Format[ x[j___,5] ] := DisplayForm @ SpeciesBox[x, {j}, {"-"}];
  Format[ x[j___,6] ] := DisplayForm @ SpeciesBox[x, {j}, {"H"}];
  Format[ x[j___,7] ] := DisplayForm @ SpeciesBox[x, {j}, {"S"}];
  Format[ x[j___,8] ] := DisplayForm @ SpeciesBox[x, {j}, {"T"}];
 )

Missing["KeyAbsent", _Symbol?QubitQ[___, None]] := 0


(* Override the default definition of Format[Dagger[...]]
   NOTE: This is potentially dangerous because Fock also overides it. *)

Format[ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] ] =. ;

Format[ HoldPattern @ Dagger[ c_Symbol?QubitQ[j___, 7] ] ] :=
  DisplayForm @ SpeciesBox[c, {j}, {"S\[Dagger]"}] /; $FormatSpecies

Format[ HoldPattern @ Dagger[ c_Symbol?QubitQ[j___, 8] ] ] :=
  DisplayForm @ SpeciesBox[c, {j}, {"T\[Dagger]"}] /; $FormatSpecies

Format[ HoldPattern @ Dagger[ c_Symbol?SpeciesQ[j___] ] ] := 
  DisplayForm @ SpeciesBox[c, {j}, {"\[Dagger]"} ] /; $FormatSpecies

Format[ HoldPattern @ Dagger[ c_Symbol?SpeciesQ ] ] := 
  DisplayForm @ SpeciesBox[c, {}, {"\[Dagger]"} ] /; $FormatSpecies


QubitQ::usage = "QubitQ[S] or QubitQ[S[...]] returns True if S is declared as a Qubit through Let."

QubitQ[_] = False


Qubits::usage = "Qubits[expr] gives the list of all qubits (quantum bits) appearing in expr."

Qubits[ expr_ ] := FlavorNone @ Union @ Map[Most] @
  Cases[ { Normal[expr, Association] }, _?QubitQ, Infinity ]
(* NOTE 1: The outermost { } is necessary around expr; otherwise,
   Qubits[S[1,2]] does not give the trivial result. *)
(* NOTE 2: Normal[{expr}, Association] is not enough as nested Association[]s
   are not converted properly. This is due to the HoldAllComplete Attribute of
   Association. *)


Dyad[S_?QubitQ][0 -> 0] := (1 + S[3]) / 2

Dyad[S_?QubitQ][0 -> 1] := S[5]

Dyad[S_?QubitQ][1 -> 0] := S[4]

Dyad[S_?QubitQ][1 -> 1] := (1 - S[3]) / 2


(* <Multiply> *)

(* Speical Rules: Involving identity *)

HoldPattern @ Multiply[a___, _?QubitQ[___, 0], b___] := Multiply[a, b]

(* Gates on Ket *)
(* NOTE: Put this code before Gates on Gates rules so that Gates on Ket[] are
   handled with higher priority? *)

(* Multiply for restricted Ket and Bra *)

HoldPattern @
  Multiply[ x___, a_?QubitQ, Ket[b_Association, c_List], y___ ] := With[
  { new = Restrict[ Multiply[a, Ket[b]], c ] },
  Multiply[x, new, y]
 ] /; MemberQ[c, FlavorMute @ a]

HoldPattern @ Multiply[ pre___,
  op_?QubitQ, Dyad[a_Association, b_Association, c_List], post___ ] := With[
  { new = Multiply[op, Ket[a]] },
  Garner @ Multiply[pre, Dyad[new, Ket @ b, c] post]
 ] /; MemberQ[c, FlavorMute @ op]

HoldPattern @ Multiply[ pre___,
  Dyad[a_Association, b_Association, c_List], op_?QubitQ, post___ ] := With[
  { new = Multiply[Bra[b], op] },
  Garner @ Multiply[pre, Dyad[Ket @ a, Dagger @ new, c] post]
 ] /; MemberQ[c, FlavorMute @ op]


(* Multiply operators on Ket[] *)

HoldPattern @
  Multiply[ x___, a_?QubitQ[j___,1], Ket[b_Association], y___ ] := With[
    { m = Mod[ 1 + b[ a[j,None] ], 2 ] },
    Multiply[
      x,
      Ket @ KeySort @ KetTrim @ Append[ b, a[j,None]->m ],
      y
     ]
   ]

HoldPattern @
  Multiply[ x___, a_?QubitQ[j___,2], Ket[b_Association], y___ ] := With[
    { m = Mod[ 1 + b[ a[j,None] ], 2 ] },
    (2 m - 1) I Multiply[
      x,
      Ket @ KeySort @ KetTrim @ Append[ b, a[j,None]->m ],
      y
     ]
   ]

HoldPattern @
  Multiply[ x___, a_?QubitQ[j___,3], Ket[b_Association], y___ ] :=
  (1 - 2 b[a[j,None]]) *
  Multiply[x, Ket @ KetTrim @ b, y]


HoldPattern @ Multiply[ x___, a_?QubitQ[j___,4], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Raise], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,5], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Lower], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,6], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Hadamard], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,7], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Quadrant], Ket[b], y]

HoldPattern @ Multiply[ x___, a_?QubitQ[j___,8], Ket[b_Association], y___ ] :=
  Multiply[x, a[j,Octant], Ket[b], y]


(* Gates on Bra *)

HoldPattern @ Multiply[ x___, Bra[v_Association], G_?QubitQ, y___ ] :=
  Multiply[ x, Dagger[Dagger[G]**Ket[v]], y ]

HoldPattern @ Multiply[ x___, Bra[v_Association, s_List], G_?QubitQ, y___ ] :=
  Multiply[ x, Dagger[Dagger[G]**Ket[v,s]], y ]


(* Special rules for Pauli matrices *)
 
HoldPattern @ Multiply[
  a___,
  x_Symbol?QubitQ[j___,k:(1|2|3|6)], x_Symbol?QubitQ[j___,k:(1|2|3|6)],
  b___ ] := Multiply[a, b]

HoldPattern @ Multiply[ a___,
  x_Symbol?QubitQ[j___,k:(4|5)], x_Symbol?QubitQ[j___,k:(4|5)],
  b___ ] := 0

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,7], x_Symbol?QubitQ[j___,7], b___ ] :=
  Multiply[a, x[j,3], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,8], x_Symbol?QubitQ[j___,7], b___ ] :=
  Multiply[a, x[j,7], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,2], b___ ] :=
  Multiply[a, I x[j,3], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,3], b___ ] :=
  Multiply[a, I x[j,1], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,1], b___ ] :=
  Multiply[a, I x[j,2], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,1], b___ ] :=
  Multiply[a, -I x[j,3], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,2], b___ ] :=
  Multiply[a, -I x[j,1], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,3], b___ ] :=
  Multiply[a, -I x[j,2], b]
(* Again, the last three definitions can be deduced from the commutation
   relations below, but explicit definition makes the evaluation much
   faster. *)


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,4], b___ ] :=
  Multiply[a, (1-x[j,3])/2, b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,1], b___ ] :=
  Multiply[a, (1+x[j,3])/2, b]


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,1], x_Symbol?QubitQ[j___,5], b___ ] :=
  Multiply[a, (1+x[j,3])/2, b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,1], b___ ] :=
  Multiply[a, (1-x[j,3])/2, b]


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,4], b___ ] :=
  Multiply[a, (1-x[j,3])I/2, b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,2], b___ ] :=
  Multiply[a, (1+x[j,3])I/2, b]


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,2], x_Symbol?QubitQ[j___,5], b___ ] :=
  Multiply[a, -(1+x[j,3])I/2, b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,2], b___ ] :=
  Multiply[a, -(1-x[j,3])I/2, b]


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,4], b___ ] :=
  Multiply[a, +x[j,4], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,3], b___ ] :=
  Multiply[a, -x[j,4], b]


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,3], x_Symbol?QubitQ[j___,5], b___ ] :=
  Multiply[a, -x[j,5], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,3], b___ ] :=
  Multiply[a, +x[j,5], b]


HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,4], x_Symbol?QubitQ[j___,5], b___ ] :=
  Multiply[a, (1+x[j,3])/2, b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,5], x_Symbol?QubitQ[j___,4], b___ ] :=
  Multiply[a, (1-x[j,3])/2, b]


(* Hadamard, Quadrant, Octant *)

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,6], b___ ] := Multiply[a, x[j,Hadamard], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,7], b___ ] := Multiply[a, x[j,Quadrant], b]

HoldPattern @ Multiply[ a___, x_Symbol?QubitQ[j___,8], b___ ] := Multiply[a, x[j,Octant], b]


(* General Rules *)

HoldPattern @ Multiply[a___, x1_?QubitQ, x2_?QubitQ, b___] := Multiply[a, x2, x1, b] /;
  Not @ OrderedQ @ {x1,x2}

(* </Multiply> *)


(* MultiplyDegree for operators *)
MultiplyDegree[_?QubitQ] = 1


(* Base: See Cauchy *)

Base[ S_?QubitQ[j___, _] ] := S[j]
(* For Qubits, the final Flavor index is special. *)


(* FlavorNone: See Cauchy *)

FlavorNone[S_?QubitQ] := S[None]

FlavorNone[S_?QubitQ -> m_] := S[None] -> m


(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?QubitQ] := S[None]

FlavorMute[S_Symbol?QubitQ[j___, _]] := S[j, None]

FlavorMute[S_Symbol?QubitQ[j___, _] -> m_] := S[j, None] -> m


Once[
  $GarnerTests = Union @ Join[$GarnerTests, {QubitQ}];
  $RepresentableTests = Union @ Join[$RepresentableTests, {QubitQ}];
 ]


QuissoCollect::usage = "QuissoCollect[expr] collects together terms involving the same Quisso operators. It is an alias to Garner."

QuissoCollect = Garner


Once[
  $RaiseLowerRules = Join[ $RaiseLowerRules,
    { S_?QubitQ[j___,1] :> (S[j,4] + S[j,5]),
      S_?QubitQ[j___,2] :> (S[j,4] - S[j,5]) / I
     }
   ]
 ]


QuissoExpand::usage = "QuissoExpand[expr] expands the expression expr revealing the explicit forms of various operator or state-vector expressions."

QuissoExpand[ expr_ ] := Garner[
  expr //. $QuissoExpandRules /. { MultiplyExp -> Exp }
 ]

$QuissoExpandRules = {
  G_?QubitQ[j___,0] -> 1,
  G_?QubitQ[j___,4] -> G[j, Raise],
  G_?QubitQ[j___,5] -> G[j, Lower],
  G_?QubitQ[j___,6] -> G[j, Hadamard],
  G_?QubitQ[j___,7] -> G[j, Quadrant],
  G_?QubitQ[j___,8] -> G[j, Octant],
  HoldPattern[ Projector[v_] ] :> Dirac[v, Dagger[v]],
  Exp[a_] /; Not[FreeQ[a,_?QubitQ]] -> MultiplyExp[a],
  v_ProductState :> Expand[v],
  OTimes -> DefaultForm @* CircleTimes,
  OSlash -> DefaultForm @* CircleTimes,
  Controlled -> QuissoControlled,
  Phase -> QuissoPhase,
  Rotation -> QuissoRotation,
  EulerRotation -> QuissoEulerRotation,
  CNOT -> QuissoCNOT,
  SWAP -> QuissoSWAP,
  CZ -> QuissoCZ,
  Toffoli -> QuissoToffoli
 }


ProductState::usage = "ProductState[...] is similar to Ket[...] but reserved only for product states. ProductState[..., S -> {a, b}, ...] expresses the qubit S has a linear combination of a Ket[0] + b Ket[1]."

Format[ ProductState[Association[]] ] := Ket[Any]

Format[ ProductState[a_Association] ] := Module[
  { aa = Map[ Dot[{Ket[0], Ket[1]}, #]&, a ],
    vv },
  vv = KeyValueMap[
    DisplayForm @ SubscriptBox[ RowBox[{"(",#2,")"}], #1 ]&,
    aa
   ];
  CircleTimes @@ vv
 ]

ProductState /:
HoldPattern[ Expand[ ProductState[a_Association] ] ] := 
  Simplify[ CircleTimes @@ KeyValueMap[QuissoExpression[#2,#1]&, a] ]

HoldPattern @ Multiply[ a___, b:ProductState[_Association], c___ ] :=
  Simplify @ Multiply[ a, Expand[b], c ]

ProductState[] = ProductState[Association[]]

ProductState[ set:(_?QubitQ|{__?QubitQ}|_Rule).. ] :=
  Fold[ ProductState, ProductState[], {set} ]

ProductState[
  v:ProductState[_Association],
  aa:(_?QubitQ|{__?QubitQ}|_Rule),
  bb:(_?QubitQ|{__?QubitQ}|_Rule).. ] :=
  Fold[ ProductState, v, {aa, bb} ]

ProductState[ ProductState[a_Association], rule:( _?QubitQ -> {_, _} ) ] :=
  ProductState @ KeySort @ Append[a, FlavorNone @ rule]

ProductState[ ProductState[a_Association], G_?QubitQ] :=
  ProductState[ProductState[a], G -> {1, 0}]

ProductState[
  ProductState[a_Association],
  rule:( {__?QubitQ} -> {(Null|{_, _})..} )
 ] := Module[
   {rr = rule /. {Null -> {1, 0}}},
   ProductState @ KeySort @ Append[ a, FlavorNone @ Thread[rr] ]
  ]

ProductState[ ProductState[a_Association], gg:{__?QubitQ} -> v:{_, _} ] := Module[
  { rr = Map[Rule[#, v]&, gg] },
  ProductState @ KeySort @ Append[a, FlavorNone @ rr]
 ]

ProductState[ ProductState[a_Association], gg:{__?QubitQ} ] :=
  ProductState[ ProductState[a], gg -> {1, 0} ]

(* Resetting the qubit values *)

ProductState[a_Association][v__Rule] := ProductState[ ProductState[a], v ]

(* Assessing the qubit values *)

ProductState[a_Association][S:{__?QubitQ}] := With[
  { SS = FlavorNone @ S },
  Lookup[a, SS]
 ]

ProductState[a_Association][S_?QubitQ] := With[
  { SS = S[None] },
  a[SS]
 ]


(* ******************************************************************* *)
(* Ket in Quisso *)

KetRule[ r:Rule[_?QubitQ, _] ] := FlavorNone[r]

KetRule[ r:Rule[{__?QubitQ}, _] ] := FlavorNone @ Thread[r]

KetRule[ Rule["Span", qq:{__?QubitQ}] ] := Rule["Span", FlavorNone @ qq]

KetTrim[_?QubitQ, 0] = Nothing


Once[ Ket::usage = Ket::usage <> "\nKet[S$1 -> m$1, S$2 -> m$2, ...] sets and returns a state vector, where S$j represent different qubits and m$j their corresponding values.\nKet[<|...|>] produced by Ket[...] provides a convenient way of accessing the values. For example, Ket[<|S$j -> m$j, ...|>][S$j] gives m$j, Ket[<|S$1 -> m$1, S$2 -> m$2, ...|>][{S$1, S$2}] gives {m$1, m$2}, and so on.\nKet[<|...|>][S$1 -> m$1, S$2 -> m$2, ...] resets the values of S$1, S$2, ... if already exit; otherwise, newly set." ]

(* ******************************************************************* *)

Basis[ S_?QubitQ ] := Basis[ {S} ]

Basis[ ss:{__?QubitQ} ] := Module[
  { tt = FlavorNone[ss],
    nS = Length[ss] },
  Map[ Ket[tt->#]&, Tuples[{0,1}, nS] ]
 ]

(* ******************************************************************* *)

QuissoFactor::usage = "QuissoFactor takes two dfiferent forms resulting in different results.\nQuissoFactor[expr] tries to factorize the Ket expression expr and, if successful at all, returns the result in the form of OTimes[...]. Otherwise it just throws expr out.\nQuissoFactor[expr, S] or QuissoFactor[expr, {S$1, S$2, ...}] factors out the state concerning the specified qubits and returns the result in OSlash[...]."

OTimes[a___, b_?ComplexQ, c___] := b OTimes[a, c]

splitState[ Ket[a_Association] ] := 
  Times @@ Map[ Ket @* Association, Normal @ a ]

splitState[ Bra[a_Association] ] := 
  Times @@ Map[ Bra @* Association, Normal @ a ]


QuissoFactor[ expr_ ] := Module[
  { new },
  new = Factor[ LogicalForm[expr] /. {
      v_Ket :> splitState[v],
      v_Bra :> splitState[v]
     } ];
  new = Replace[new, Times -> OTimes, 1, Heads -> True];
  new /. Times[a___, b_Ket, c__Ket, d___] :> 
    Times[a, CircleTimes[b, c], d]
 ]


QuissoFactor[ a_ + b_ , qq:(_?QubitQ|{__?QubitQ}) ] :=
  QuissoFactor[a, qq] + QuissoFactor[b, qq]

QuissoFactor[ z_?ComplexQ a_ , qq:(_?QubitQ|{__?QubitQ}) ] :=
  z QuissoFactor[a, qq]

QuissoFactor[ Ket[a_Association], S_?QubitQ ] := QuissoFactor[Ket[a], {S}]

QuissoFactor[ Ket[a_Association], S:{__?QubitQ} ] := Module[
  { SS = FlavorNone[S] },
  OSlash[ LogicalForm[ Ket[KeyTake[a, SS]], SS ], Ket[KeyDrop[a, SS]]]
 ]


SpinForm::usage = "SpinForm[expr, qq] converts Qubit value 0 tp \[UpArrow] and 1 to \[DownArrow] in every Ket appearing in expr."

SpinForm[v_Ket, {}] := v

SpinForm[v_Ket, qq:{__?QubitQ}] := Module[
  { ss },
  ss = v[qq] /. {0 -> "\[UpArrow]", 1 -> "\[DownArrow]"};
  Ket[v, qq -> ss]
 ]

SpinForm[expr_, qq:{___?QubitQ}] := 
  expr /. { v_Ket :> SpinForm[v, FlavorNone@qq] }

SpinForm[expr_, q_?QubitQ] := SpinForm[expr, {q}]

SpinForm[expr_] := SpinForm[expr, Qubits @ expr]


Dirac::usage = "Dirac[Ket[a], Bra[b], qq] returns the operator corresponding to |a\[RightAngleBracket]**\[LeftAngleBracket]b|, operating on the Qubits qq.\nDirac[Ket[a], Bra[b]] extracts the list of Qubits from Ket[a] and Bra[b] automatically."

Dirac[ a_, b_ ] := theDirac[ Garner @ a, Garner @ Dagger @ b, Qubits @ {a, b} ]

Dirac[ a_, b_, qq:{__?QubitQ} ] :=
  theDirac[ Garner @ a, Garner @ Dagger @ b, FlavorNone @ qq ]


theDirac[a_Plus, b_Plus, qq_] :=
  Garner @ Total @ Flatten @ Outer[theDirac[#1, #2, qq]&, List @@ a, List @@ b]

theDirac[a_Plus, b_, qq_] :=
  Garner @ Total @ Flatten @ Outer[theDirac[#1, #2, qq]&, List @@ a, List @ b]

theDirac[a_, b_Plus, qq_] :=
  Garner @ Total @ Flatten @ Outer[theDirac[#1, #2, qq]&, List @ a, List @@ b]

theDirac[ z_?ComplexQ a_, b_, qq_ ] := Garner[ z theDirac[a, b, qq] ]

theDirac[ a_, z_?ComplexQ b_, qq_ ] := Garner[ z theDirac[a, b, qq] ]

theDirac[ a:Ket[_Association], b:Ket[_Association], qq_ ] := Module[
  { aa = a[qq],
    bb = b[qq],
    op },
  op = Map[theDirac] @ Transpose @ {qq, aa, bb};
  Garner[ Multiply @@ op ]
 ]

theDirac[ {S:_Symbol?QubitQ[___,None], 0, 0} ] := (1 + S[3]) / 2

theDirac[ {S:_Symbol?QubitQ[___,None], 1, 1} ] := (1 - S[3]) / 2

theDirac[ {S:_Symbol?QubitQ[___,None], 0, 1} ] := S[4]

theDirac[ {S:_Symbol?QubitQ[___,None], 1, 0} ] := S[5]

Dirac/:
Dagger[ Dirac[ a_Ket, b_Bra, qq:{__?QubitQ} ] ] :=
  Dirac[ Dagger[b], Dagger[a], qq ]
(* Normally, such an operation is not necessary. *)


QuissoReduced::usage = "QuissoReduced[v, {S}] gives the reduced density operator (in the Ket[...]**Bra[...] form) for the qubits in {S}. For the single-qubit reduced density operator, QuissoReduced[v, S] can be used.
  QuissoReduced[v, {n}] for an integer n gives all n-qubit reduced densitry operators.
  QuissoReduced[v, n] for an integer n gives all k-qubit reduced densitry operators up to k = n.
  QuissoReduced[v] gives all n-qubit reduced densitry operators up to n = the number of qubits in v."

QuissoReduced[v_, S_?QubitQ] :=
  wReduced @ QuissoFactor[ Garner @ v, {S} ]

QuissoReduced[v_, S:{__?QubitQ}] :=
  wReduced @ QuissoFactor[ Garner @ v, S ]

wReduced[ OSlash[a_Ket, b_] ] :=
  Dirac[a, Dagger[a]] * Conjugate[ Dagger[b] ** b ]

wReduced[ expr_Plus ] := Module[
  { vv = List @@ expr,
    aa, bb, qq },
  { aa, bb } = Transpose[vv /. {OSlash -> List}];
  qq = Qubits[aa];
  aa = Outer[ Dirac[#1, #2, qq]&, aa, Dagger[aa] ];
  bb = Outer[ Multiply, Dagger[bb], bb ];
  Total @ Flatten[ Conjugate[bb] * aa ]
 ]


QuissoReduced[v_] := With[
  { ss = Qubits @ v },
  QuissoReduced[ v, Length[ss]-1 ]
 ]

QuissoReduced[v_, n_Integer] :=
  Join @@ Table[ QuissoReduced[v, {k}], {k, 1, n} ]

QuissoReduced[v_, {n_Integer}] := Module[
  { ss = Qubits @ v,
    rr },
  ss = Subsets[ss, {n}];
  rr = Map[QuissoReduced[v,#]&, ss];
  Association[ Thread[ss->rr] ] /; n < Length[ss]
 ]

(* This is not really necessary, but just for completeness. *)
QuissoReduced[v_, {n_Integer}] := Module[
  { ss = Qubits @ v,
    rr },
  rr = v ** Dagger[v];
  Association[ ss -> rr ] /; n >= Length[ss]
 ]


ReducedDensityMatrix::usage = "ReducedDensityMatrix is almost the same as QuissoReduced, but returns the matrix representations."


ReducedDensityMatrix[v_, S_?QubitQ] :=
  Matrix[ QuissoReduced[v, {S}], {S} ]

ReducedDensityMatrix[v_, S:{__?QubitQ}] :=
  Matrix[ QuissoReduced[v, S], S ]

ReducedDensityMatrix[v_] := With[
  { ss = Qubits @ v },
  ReducedDensityMatrix[ v, Length[ss]-1 ]
 ]

ReducedDensityMatrix[v_, n_Integer] :=
  Join @@ Table[ ReducedDensityMatrix[v, {k}], {k, 1, n} ]

ReducedDensityMatrix[v_, {n_Integer}] := Module[
  { ss = Qubits @ v,
    rr },
  ss = Subsets[ss, {n}];
  rr = Map[ ReducedDensityMatrix[v,#]&, ss ];
  Association[ Thread[ss->rr] ] /; n < Length[ss]
 ]

ReducedDensityMatrix[v_, {n_Integer}] := Module[
  { ss = Qubits @ v,
    rr },
  rr = Matrix[ v ** Dagger[v], ss ];
  Association[ ss -> rr ] /; n >= Length[ss]
 ]


DensityMatrix::usage = "DensityMatrix[v] constructs the density matrix (in the matrix form) for the pure state v."

DensityMatrix[v_] := Module[
  { vv = Matrix[v] },
  vv = SparseArray[ ArrayRules[vv], Dimensions[vv] ];
  Outer[Times, vv, Conjugate[vv]]
 ]

DensityOperator::usage = "DensityOperator[v] constructs the operator expression for the density matrix corresponding to the pure state v."

DensityOperator[v_] := 
  QuissoExpression[DensityMatrix @ v, Qubits @ v]

(* ******************************************************************** *)

Parity[S_?QubitQ] := S[3]


ParityEvenQ[v_Ket, a_?QubitQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?QubitQ] := OddQ @ v @ a

(* ******************************************************************** *)

(* Matrix[] for Qubits *)

Matrix[ _?QubitQ[___,j_] ] := ThePauli[j]

Matrix[ Ket[ Association[_?QubitQ -> s:(0|1)] ] ] := SparseArray @ TheKet[s]

(* ******************************************************************** *)


QuissoAddZ::usage = "QuissoAddZ[S$1, S$2, ...] returns in an Association the irreducible basis of the total angular momentum S$1 + S$2 + ... invariant under the U(1) rotation around spin z-axis, regarding the qubits S$1, S$2, ... as 1/2 spins."

QuissoAddZ::duplicate = "Duplicate angular momentum operators appear."


QuissoAddZ[ ls:{(_?QubitQ|_Association)..} ] :=
  QuissoAddZ @@ Map[QuissoAddZ] @ ls

QuissoAddZ[] := Association[ {0} -> {Ket[]} ]

QuissoAddZ[irb_Association] := irb

QuissoAddZ[a_?QubitQ] := Module[
  { aa = FlavorNone @ a,
    bs = Basis @ a },
  GroupBy[bs, (1/2-#[aa])&]
 ]

QuissoAddZ[a___, b_?QubitQ, c___] := QuissoAddZ[a, QuissoAddZ[b], c]

QuissoAddZ[irb_Association, irc_Association, ird__Association] :=
  QuissoAddZ[ QuissoAddZ[irb, irc], ird]

QuissoAddZ[irb_Association, irc_Association] := Module[
  { kk = Flatten @ Outer[Plus, Keys[irb], Keys[irc]],
    vv = Map[Tuples] @ Tuples[{Values[irb], Values[irc]}],
    gb = Union @ Cases[Normal @ Values @ irb, _?QubitQ, Infinity],
    gc = Union @ Cases[Normal @ Values @ irc, _?QubitQ, Infinity],
    rr },
  If[ ContainsAny[gb, gc],
    Message[ QuissoAddZ::duplicate ];
    Return[ irb ]
   ];

  vv = Apply[CircleTimes, vv, {2}];
  rr = Thread[kk -> vv];
  rr = Merge[rr, Catenate];
  Map[ReverseSort, rr]
 ]

QuissoAdd::usage = "QuissoAdd[S$1, S$2, ...] returns in an Association the irreducible basis of the total angular momentum S$1 + S$2 + ... that are invariant under arbitrary SU(2) rotations. Here the qubits S$1, S$2, ... are regarded 1/2 spins."

QuissoAdd::duplicate = "Duplicate angular momentum operators appear."

QuissoAdd[ ls:{(_?QubitQ|_Association)..} ] :=
  QuissoAdd @@ Map[QuissoAdd] @ ls

QuissoAdd[] := Association[ {0,0} -> {Ket[]} ]

QuissoAdd[irb_Association] := irb

QuissoAdd[a_?QubitQ] := Module[
  { aa = FlavorNone @ a,
    bs = Basis @ a },
  GroupBy[bs, { 1/2, (1/2 - #[aa]) }&]
 ]

QuissoAdd[a___, b_?QubitQ, c___] := QuissoAdd[a, QuissoAdd[b], c]

QuissoAdd[irb_Association, irc_Association, ird__Association] :=
  QuissoAdd[ QuissoAdd[irb, irc], ird]

QuissoAdd[irb_Association, irc_Association] := Module[
  { S1 = Union @ Map[First] @ Keys[irb],
    S2 = Union @ Map[First] @ Keys[irc],
    SS,
    gb = Union @ Cases[Normal @ Values @ irb, _?QubitQ, Infinity],
    gc = Union @ Cases[Normal @ Values @ irc, _?QubitQ, Infinity],
    new },
  If[ ContainsAny[gb, gc],
    Message[ QuissoAdd::duplicate ];
    Return[ irb ]
   ];
  SS = Flatten[
    Outer[Thread[{#1, #2, Range[Abs[#1 - #2], #1 + #2]}]&, S1, S2], 
    2];
  SS = Flatten[
    Map[Thread[{Sequence @@ #, Range[-Last@#, Last@#]}]&] @ SS,
    1];
  new = doQuissoAdd[irb, irc, #]& /@ SS;
  Merge[new, Catenate]
 ]

doQuissoAdd[irb_, irc_, {S1_, S2_, S_, Sz_}] := Module[
  { new, min, max },
  min = Max[-S1, Sz - S2, (Sz - (S1 + S2))/2];
  max = Min[S1, Sz + S2, (Sz + (S1 + S2))/2];
  new = Simplify @ Sum[
    CircleTimes @@@ Tuples[{irb[{S1, m}], irc[{S2, Sz - m}]}]*
      ClebschGordan[{S1, m}, {S2, Sz - m}, {S, Sz}],
    {m, Range[min, max]} ];
  Association[ {S, Sz} -> new ]
 ]


QuissoExpression::usage = "QuissoExpression[expr] converts Ket[...]**Bra[...]  for in the expression expr to the form in terms of the Gate operators.
  QuissoExpression[m, {S$1, S$2, ...}] converts the square matrix m into a Quisso expression.
  QuissoExpression[v, {S$1, S$2, ...}] converts the column vector v into a Ket expression."

(* Let[LinearMap, QuissoExpression] *)
(* NOTE: When there are many terms, larger than 512?,
   strange $RecursionLimit::reclim2 error occurs.*)

QuissoExpression[ a_ + b_ ] := QuissoExpression[a] + QuissoExpression[b] 

QuissoExpression[ z_?ComplexQ ] := z

QuissoExpression[ z_?ComplexQ a_ ] := z QuissoExpression[a]

QuissoExpression::incon = "The matrix/vector `1` is not compatible with the Qubit list `2`."

QuissoExpression[ m_?MatrixQ, S_?QubitQ ] := QuissoExpression[ m, {S} ]

QuissoExpression[ m_?MatrixQ, ss:{__?QubitQ} ] := Module[
  { nL = Power[2, Length @ ss] {1, 1},
    mm = SparseArray[ ArrayRules[m], Dimensions[m] ],
    tt, op, tensor, HoldTimes },

  If[ Dimensions[m] != nL,
    Message[QuissoExpression::incon, m, FlavorNone @ ss];
    Return[0]
   ];
  
  tensor = Tensorize[mm];
  tt = Map[
    Function[ {S},
      { {1/2+S[3]/2, S[Raise]},
        {S[Lower], 1/2-S[3]/2} } ],
    ss ];
  op = Outer[ HoldTimes, Sequence @@ tt ];
  Expand[ Total @ Flatten[tensor * op] /. {HoldTimes -> Multiply} ]
 ]

QuissoExpression[ v_?VectorQ, S_?QubitQ ] := QuissoExpression[ v, {S} ]

QuissoExpression[ v_?VectorQ, ss:{__?QubitQ} ] := Module[
  { nL = Length[ss],
    tt = FlavorNone[ss],
    basis },

  If[ Length[v] != Power[2, nL],
    Message[QuissoExpression::incon, v, FlavorNone @ ss];
    Return[{0}]
   ];
  
  basis = Basis[tt];
  Dot[v, basis]
 ]

QuissoExpression[ expr_ ] := expr


(* QuissoCoefficientTensor *)

QuissoCoefficientTensor::usage = "QuissoCoefficientTensor[expr] gives the Pauli decomposition of the Quisso expression expr, by finding the coefficients to operators."


(* Method 1: One can use a similar method as in PauliDecompose[]. But it
   becomse very slow as the number of qubits increases. *)

(* Method 2: This results in "Recursion depth of 1024 exceeded
   during evaluation of ..." error when the state vector includes many terms
   for a large number of qubits. *)

QuissoCoefficientTensor[op_] := With[
  { ss = Qubits @ op },
  QuissoCoefficientTensor[op, Length[ss]]
 ]

QuissoCoefficientTensor[op_, n_Integer] :=
  Join @@ Table[ QuissoCoefficientTensor[op, {k}], {k, 0, n} ]

QuissoCoefficientTensor[op_, {0}] := With[
  { cn = QuissoExpand[op] /. {_Symbol?QubitQ[___,(1|2|3)] -> 0} },
  Association[ {1} -> cn ]
 ]

QuissoCoefficientTensor[expr_, {n_Integer}] := Module[
  { ss = Qubits @ expr,
    op = QuissoExpand @ expr,
    kk, cc },
  ss = Subsets[ss, {n}];
  kk = Map[ (#[{1,2,3}])&, ss, {2} ];
  ss = Map[ (#[None])&, ss, {2} ];
  cc = Map[ CoefficientTensor[op, Sequence @@ #]&, kk ];
  Association[ Thread[ss->cc] ]
 ]


(* QuissoAssemble *)

QuissoAssemble::usage = "QuissoAssemble[a] reassembles the operator expression in terms of operators from the coefficient tensors in the Association a. The association a is usually generated by QuissoCoefficientTensor[] or QuissoCorrelationTensor[]."

QuissoAssemble[ a_Association ] := Total @ KeyValueMap[ QuissoAssemble, a ]

QuissoAssemble[ {1}, m_ ] := m

QuissoAssemble[ ss:{__?QubitQ}, m_?TensorQ ] := Module[
  { kk, op, vv, nL },
  nL = Length[ss]; (* the level of Quisso decomposition *)
  kk = Outer[List, Sequence @@ Table[{1, 2, 3}, {nL}]];
  op = Map[ ( Multiply @@ MapThread[Construct, {ss, #}] )&, kk, {nL} ];
  vv = op * m;
  Total @ Flatten[vv]
 ]

(* QuissoPhase, Phase *)

QuissoPhase::usage = "QuissoPhase[G, \[Phi]] operates the relative phase shift by \[Phi] on the qubit G.
  Unlike Phase[G, \[Phi]], it expands immediately in terms of the elementary Pauli gates."

QuissoPhase[ a__, opts__?OptionQ ] := QuissoPhase[ a ]
(* NOTE: opts__, NOT opts___; just for the interface with Phase[]. *)

QuissoPhase[ S_?QubitQ[j___,None], a_ ] :=
  (1+Exp[I a])/2 + S[j,3] (1-Exp[I a])/2
(* Phase[...] can results in this case. *)

QuissoPhase[ G_?QubitQ, phi_ ] := QuissoPhase[ G[None], phi ] /;
  FlavorLast[G] =!= None

Phase::usage = "Phase[G, \[Phi]] represents the relative phase shift by \[Phi] on the qubit G."

Options[Phase] = { Label -> "\[CapitalPhi]" }

Phase /:
Dagger[ Phase[ G_?QubitQ, phi_, opts___?OptionQ ] ] :=
  Phase[ G, -Conjugate[phi], opts ]
  
Phase[ G_?QubitQ, phi_, opts___?OptionQ ] :=
  Phase[ G[None], phi, opts ] /; FlavorLast[G] =!= None

Phase[ qq:{__?QubitQ}, phi_, opts___?OptionQ ] :=
  Map[ Phase[#, phi, opts]&, FlavorNone @ qq ]

HoldPattern @ Multiply[
  a___,
  Phase[g_?QubitQ, phi_, opts___?OptionQ ],
  b___ ] := Multiply[ a, QuissoPhase[g, phi], b ]
(* Options are for QuissoCircuit[] and ignore in calculations. *)


(* QuissoRotation, Rotation, QuissoEulerRotation, EulerRotation *)

QuissoRotation::usage = "QuissoRotation[G[j,...,k], angle] gives the operator corresonding to the rotation by angle angle around the axis k on the qubit G[j, ..., None]."

QuissoRotation[ a__, opts__?OptionQ ] := QuissoRotation[ a ]
(* NOTE: opts__, NOT opts___; just for the interface with Rotation[]. *)

QuissoRotation[S_?QubitQ[j___,k:(1|2|3)], a_] :=
  Cos[a/2] - I Sin[a/2] S[j,k]

QuissoRotation[S_?QubitQ[j___, None], a_, v:{_,_,_}] :=
  Cos[a/2] - I Sin[a/2] Dot[ S[j,{1,2,3}], Normalize[v] ]
(* Rotation[...] can results in this case. *)

QuissoRotation[S_?QubitQ, a_, v:{_,_,_}] :=
  Cos[a/2] - I Sin[a/2] Dot[ S[{1,2,3}], Normalize[v] ] /;
  FlavorLast[S] =!= None

QuissoRotation[SS:{__?QubitQ}, a_] :=
  Multiply @@ Map[ QuissoRotation[#,a]&, SS ]


Once[ Rotation::usage = Rotation::usage <> "\nRotation[G[j, ..., k], angle] represents the rotation by angle angle around the axis k on the qubit G[j, ..., None]." ]

Options[Rotation] = { Label -> Automatic }

Rotation[ qq:{__?QubitQ}, rest__ ] :=
  Map[ Rotation[#,rest]&, FlavorNone @ qq ]

Rotation /:
HoldPattern @ Multiply[a___, Rotation[g_?QubitQ, rest__], b___ ] :=
  Multiply[ a, QuissoRotation[g, rest], b ]
(* Options are for QuissoCircuit[] and ignored in calculations. *)

Rotation /:
Dagger[ Rotation[S_?QubitQ, ang_, rest___] ] :=
  Rotation[S, -Conjugate[ang], rest]


QuissoEulerRotation::usage = "QuissoEulerRotation[G[j, ..., None], {a, b, c}] operates the Euler rotation by the angles a,  b and c on the qubit G[j, ..., None].\nUnlike EulerRotation[G[j, ..., None], {a, b, c}] it expands immediately in terms of the elementary Pauli gates."

QuissoEulerRotation[ a__, opts__?OptionQ ] := QuissoEulerRotation[ a ]
(* NOTE: opts__, NOT opts___; just for the interface with Rotation[]. *)

QuissoEulerRotation[SS:{__?QubitQ}, a_List] :=
  Multiply @@ Map[ QuissoEulerRotation[#,a]&, SS ]

QuissoEulerRotation[ S_?QubitQ[j___,None], {a_, b_, c_} ] := Multiply[
  QuissoRotation[S[j,3],a],
  QuissoRotation[S[j,2],b],
  QuissoRotation[S[j,3],c]
 ]
(* EulerRotation[...] can results in this case. *)

QuissoEulerRotation[ S_?QubitQ, {a_, b_, c_} ] := Multiply[
  QuissoRotation[S[3],a],
  QuissoRotation[S[2],b],
  QuissoRotation[S[3],c]
 ] /; FlavorLast[S] =!= None

Once[ EulerRotation::usage = EulerRotation::usage <> "\nEulerRotation[G[j, ..., None], {a, b, c}] operates the Euler rotation by the angles a,  b and c on the qubit G[j, ..., None]." ]

Options[EulerRotation] = { Label -> Automatic }

EulerRotation[ qq:{__?QubitQ}, rest__ ] :=
  Map[ EulerRotation[#,rest]&, FlavorNone @ qq ]

EulerRotation[ G_?QubitQ, angles:{_, _, _}, opts___?OptionQ ] :=
  EulerRotation[ G[None], angles, opts ] /; FlavorLast[G] =!= None
  
HoldPattern @ Multiply[
  a___,
  EulerRotation[g_?QubitQ, angles:{_, _, _}, opts___?OptionQ ],
  b___ ] := Multiply[ a, QuissoEulerRotation[g, angles], b ]
(* Options are for QuissoCircuit[] and ignore in calculations. *)


(* *************************************************************
   * Quantum Computation
   ************************************************************* *)

CNOT::usage = "CNOT[C, T] represents the CNOT gate on the two qubits C and T, which are the control and target qubits, respectively. Note that it does not expand until necessary (e.g., multiplied to a Ket); use QuissoCNOT or QuissoExpand in order to expand it immediately."

QuissoCNOT::usage = "QuissoCNOT[C, T] operates the CNOT gate on the two qubits C and T, which are the control and target qubits, respectively. See also CNOT."

SetAttributes[CNOT, Listable]

SetAttributes[QuissoCNOT, Listable]

CNOT[ c_?QubitQ, t_?QubitQ ] := CNOT @@ FlavorNone @ {c,t} /;
  FlavorLast[{c,t}] =!= {None, None}

CNOT /: Dagger[ op_CNOT ] := op

CNOT /: HoldPattern @ Multiply[a___, CNOT[b__], c___] := Multiply[a, QuissoCNOT[b], c]

QuissoCNOT[ c_?QubitQ, t_?QubitQ ] :=
  QuissoCNOT @@ FlavorNone @ {c,t} /; FlavorLast[{c,t}] =!= {None, None}

QuissoCNOT[ c_?QubitQ, t_?QubitQ ] := Module[
  { cc = Most @ c,
    tt = Most @ t },
  ExpandAll[ (1 + cc[3] + tt[1] - cc[3]**tt[1]) / 2 ]
 ]


CZ::usage = "CZ[C, T] operates the controlled-Z gate on the two qubits associated with C and T. C and T are the control and target qubits, respectively; in fact, contol and target qubits are symmetric for this gate."

QuissoCZ::usage = "QuissoCZ[C, T] operates the controlled-Z gate on the two qubits associated with C and T. C and T are the control and target qubits, respectively; in fact, contol and target qubits are symmetric for this gate."

SetAttributes[CZ, Listable]

SetAttributes[QuissoCZ, Listable]

CZ[ c_?QubitQ, t_?QubitQ ] := CZ @@ FlavorNone @ {c,t} /;
  FlavorLast[{c,t}] =!= {None, None}

CZ /: Dagger[ op_CZ ] := op

CZ /: HoldPattern @ Multiply[a___, CZ[b__], c___] := Multiply[a, QuissoCZ[b], c]

QuissoCZ[ c_?QubitQ, t_?QubitQ ] := QuissoCZ @@ FlavorNone @ {c,t} /;
  FlavorLast[{c,t}] =!= {None, None}

QuissoCZ[ c_?QubitQ, t_?QubitQ ] := Module[
  { a = Most @ c,
    b = Most @ t },
  ExpandAll[ (1 - a[3]**b[3] + a[3] + b[3]) / 2 ]
 ]



SWAP::usage = "SWAP[A, B] operates the SWAP gate on the two qubits A and B."

QuissoSWAP::usage = "QuissoSWAP[A, C] operates the SWAP gate on the two qubits A and B. Unlike SWAP, QuissoSWAPS expands immediately in terms of the elementary Pauli gates."

SetAttributes[SWAP, Listable]

SetAttributes[QuissoSWAP, Listable]

SWAP[ a_?QubitQ, b_?QubitQ ] := SWAP @@ FlavorNone @ {a,b} /;
  FlavorLast[{a,b}] =!= {None, None}

SWAP /: Dagger[ op_SWAP ] := op

SWAP /: HoldPattern @ Multiply[a___, SWAP[b__], c___] := Multiply[a, QuissoSWAP[b], c]

QuissoSWAP[ a_?QubitQ, b_?QubitQ ] := QuissoSWAP @@ FlavorNone @ {a,b} /;
  FlavorLast[{a,b}] =!= {None, None}

QuissoSWAP[ x_?QubitQ, y_?QubitQ ] := Module[
  { a = Most @ x,
    b = Most @ y },
  ExpandAll[ (1 + a[1]**b[1] + a[2]**b[2] + a[3]**b[3]) / 2 ]
 ]


Toffoli::usage = "Toffoli[A, B, C] operates the Toffoli gate, i.e., the three-qubit controlled-note gate on C controlled by A and B."

QuissoToffoli::usage = "QuissoToffoli[A, B, C] is the same as Toffoli[A, B, B], but unlike it expands immediately in terms of elementary Pauli gates."

SetAttributes[Toffoli, Listable]

SetAttributes[QuissoToffoli, Listable]

Toffoli[ a_?QubitQ, b_?QubitQ, c_?QubitQ ] :=
  Toffoli @@ FlavorNone @ {a,b,c} /;
  FlavorLast[{a,b,c}] =!= {None, None, None}

Toffoli /: Dagger[ op_Toffoli ] := op

Toffoli /: HoldPattern @ Multiply[a___, Toffoli[b__], c___] :=
  Multiply[a, QuissoToffoli[b], c]

QuissoToffoli[ a_?QubitQ, b_?QubitQ, c_?QubitQ ] :=
  QuissoToffoli @@ FlavorNone @ {a,b,c} /;
  FlavorLast[{a,b,c}] =!= {None, None, None}

QuissoToffoli[ a_?QubitQ, b_?QubitQ, c_?QubitQ ] := Module[
  { aa = Most @ a,
    bb = Most @ b,
    cc = Most @ c },
  
  ExpandAll[ 3 + aa[3] + bb[3] + cc[1] -
      aa[3]**bb[3] - aa[3]**cc[1] - bb[3]**cc[1] +
      aa[3]**bb[3]**cc[1] ] / 4
 ]


Controlled::usage = "Controlled[{C$1, C$2, ...}, T[j, ..., k]] represents a multi-qubit controlled gate. It operates the gate T[j, ..., k] on the qubit T[j, ..., None] controlled by the qubits C$1, C$2.\nControlled[C, T] is equivalent to Controlled[{C}, T]."

Controlled[ S_?QubitQ, expr_, opts___?OptionQ ] :=
  Controlled[ { S[None] }, expr, opts ]

Controlled[ ss:{__?QubitQ}, expr_, opts___?OptionQ ] :=
  Controlled[ FlavorNone @ ss, expr, opts ] /;
  Not @ ContainsOnly[ FlavorLast[ss], {None} ]

Controlled /:
Dagger[ Controlled[ S_?QubitQ, expr_, opts___?OptionQ ] ] :=
  Controlled[ { S[None] }, Dagger[expr], opts ]

Controlled /:
Dagger[ Controlled[ ss:{__?QubitQ}, expr_, opts___?OptionQ ] ] :=
  Controlled[ss, Dagger[expr], opts]

Controlled /:
HoldPattern @ Multiply[a___, Controlled[b__, opts___?OptionQ], c___] :=
  Multiply[a, QuissoControlled[b], c]
(* Options are for QuissoCircuit[] and ignore in calculations. *)


QuissoControlled::usage = "QuissoControlled[...] is the same as Controlled[...], but unlike the latter, it exapands immediately in terms of the elementary Pauli gates."

QuissoControlled[ a_, b_, __?OptionQ ] := QuissoControlled[a, b]

QuissoControlled[ S_?QubitQ, expr_ ] :=
  QuissoControlled[ { S[None] }, expr ]

QuissoControlled[ ss:{__?QubitQ}, expr_ ] :=
  QuissoControlled[ FlavorNone @ ss, expr ] /;
  Not @ ContainsOnly[ FlavorLast[ss], {None} ]

QuissoControlled[ ss:{__?QubitQ}, expr_ ] := Module[
  { P = Multiply @@ Map[ ((1-#[3])/2)&, Most /@ ss ] },
  ExpandAll[ P ** expr + (1-P) ]
 ]


Projector::usage = "Projector[state] represents the projection operator onto the state, which is given in the Ket expression."

Projector::noKet = "No Ket expression found for projection in the provided expression ``. Identity operator is returned."

SetAttributes[Projector, Listable]

Projector /:
Dagger[ op_Projector ] := op

Projector /:
QuissoExpression[ HoldPattern @ Projector[v_] ] :=
  Dirac[v, Dagger @ v, Qubits @ v]

Projector[v_] := (
  Message[Projector::noKet, v];
  1
 ) /; FreeQ[v, _Ket]


QuissoProjector::usage = "QuissoProjector[state] gives the projection operator onto the state, which is given in the Ket expression."

QuissoProjector::noKet = "No Ket expression found for projection in the provided expression ``. Identity operator is returned."

SetAttributes[QuissoProjector, Listable]

QuissoProjector[v_] := QuissoExpression @ Dirac[ v, Dagger @ v, Qubits @ v ]

QuissoProjector[v_] := (
  Message[QuissoProjector::noKet, v];
  1
 ) /; FreeQ[v, _Ket]


Measure::usage = "Measure[G][expr] represents a measurement on the qubit G for the state vector in expr, which is supposed to be a Ket exrepssion. The resulting state vector is returned in a Ket expression."

Measure::nonum = "Cannot perform a measurement on a non-numeric state vector. Probability half is assumed."

Measure::novec = "The expression `` does not seem to be a valid Quisso Ket expression. Null vector is returned."

SetAttributes[Measure, Listable]

Measure[ gg:{__?QubitQ} ] := Measure /@ FlavorNone @ gg

Measure[ g_?QubitQ ] := Measure @ FlavorNone @ g /;
  FlavorLast[g] =!= None
(* This is for the interface with QuissoCircuit[]. *)

Measure[ b_?QubitQ ][ vec_ ] := Module[
  { r = RandomReal[],
    expr = QuissoExpand @ vec,
    vx, v0, v1, p0, p1 },
  vx = Cases[expr, v:Ket[_Association] :> v[b], Infinity];
  vx = DeleteCases[ vx, (0|1) ];
  If[ vx == {},
    Null,
    Message[Measure::novec, expr]; Return[0],
    Message[Measure::novec, expr]; Return[0]
   ];

  v0 = expr /. { v:Ket[_Association] :> (1-v[b]) v };
  v1 = expr /. { v:Ket[_Association] :> (v[b]) v };

  p0 = Simplify[ Dagger[v0] ** v0 ];
  p1 = Simplify[ Dagger[v1] ** v1 ];
  
  If [ r < N[p0 / (p0 + p1)],
    v0 / Sqrt[p0],
    v1 / Sqrt[p1],
    Message[Measure::nonum];
    If[ r < 0.5, v0, v1 ]
   ]
 ]

Readout::usage = "Readout[S, expr] or Readout[{S1, S2, ...}, expr] reads the measurement result from the expr that is supposed to be the Quisso Ket[] expression corresponding to the wave function after measurements."

Readout::badout = "Multiple measurement results: ``. The Qubit may not have been measured; or, it may have been corrupted after measurement."

Readout[S_?QubitQ, expr_] := First @ Readout[{S}, expr]

Readout[ss:{__?QubitQ}, expr_] := Module[
  { vv = Cases[{expr}, Ket[_Association], Infinity] },
  vv = Union @ Map[#[ss]&, vv];
  If[ Length[vv] > 1, Message[Readout::badout, vv] ];
  First @ vv
 ]


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

DickeState[ss : {__?QubitQ}, n_] := Module[
  { byte = ConstantArray[1, n] },
  byte = PadRight[byte, Length[ss]];
  byte = Permutations[byte];
  Total[ Map[Ket[ss -> #]&, byte] ] / Sqrt[Length[byte]]
 ]

DickeState[ ss:{__?QubitQ} ] := Table[ DickeState[ss, n], {n, 0, Length[ss]} ]


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


GraphState::usage = "GraphState[g] gives the graph state (aka cluster state) correponding to the graph g."

GraphState[ g_Graph ] := Module[
  { vv = VertexList[g],
    cz = EdgeList[g],
    hh },
  hh = Multiply @@ Map[#[6]&, vv];
  cz = Multiply @@ QuissoCZ @@@ cz; 
  Simplify[ cz ** (hh ** Ket[]) ]
  /; AllTrue[ vv, QubitQ ]
 ]


Protect[ Evaluate @ $symbs ]

End[] (* `Prelude` *)



Begin["`Circuit`"]

QuissoCircuit::usage = "QuissoCircuit[a, b, ...] represents the quantum circuit model consisting of the gate operations a, b, ....
  Inside Graphics function, e.g., Graphics[QuissoCircuit[...]], displays the circuit in a graphical form.
  QuissoExpression[ QuissoCircuit[...] ] takes the non-commutative product of the elements in the quantum circuit; namely, converts the quantum circuit to a Quisso expression."

QuissoIn::usage = "QuissoIn is a holder for input expression in QuissoCircuit.
  See also QuissoOut."

QuissoOut::usage = "QuissoOut is a holder for expected output expressions in QuissoCircuit. Note that the output expressions are just expected output and may be different from the actual output. They are used only for output label and ignored by QuissoExpression.
  See also QuissoIn."


SetAttributes[ {QuissoOut, QuissoIn}, Flat ]


$CircuitSize = 1

$GateDistance = 1

$GateSize := 0.8 $GateDistance

$DotSize := 0.09 $GateDistance

$InOutOffset := 0.1 $GateDistance

$BraceWidth := 0.1 $GateDistance


Format[ qc:QuissoCircuit[___, opts___?OptionQ] ] := Graphics[qc, opts]

(*
 * User Interface
 *)

QuissoCircuit[ a___, QuissoCircuit[b___], c___] := QuissoCircuit[a, b, c]
(* Similar effect as the Flat attribute. *)

QuissoCircuit[ a__?qKetQ ] := QuissoCircuit[ QuissoIn[a] ]

QuissoCircuit[ a__?qKetQ, b:Except[_?qKetQ], c___ ] := QuissoCircuit[ QuissoIn[a], b, c]

QuissoCircuit[ a___, b__?qKetQ, opts___?OptionQ ] := QuissoCircuit[ a, QuissoOut[b], opts ]

QuissoCircuit[ a___, b__?OptionQ, c:Except[_?OptionQ].. ] := QuissoCircuit[a, c, b]

QuissoCircuit[ x___, a_QuissoOut, b__QuissoOut, y___ ] := QuissoCircuit[x, QuissoOut[a, b], y]

QuissoCircuit[ x___, a_QuissoIn, b__QuissoIn, y___ ] := QuissoCircuit[x, QuissoIn[a, b], y]

QuissoCircuit[ a__, b_QuissoIn, c___ ] := QuissoCircuit[ b, a, c ]

QuissoCircuit[ a___, b_QuissoOut, c:Except[_?OptionQ].., opts___?OptionQ ] := QuissoCircuit[a, c, b, opts]

qKetQ[expr_] := And[
  FreeQ[expr, _QuissoIn | _QuissoOut | _Projector],
  !FreeQ[expr, _Ket | _ProductState]
 ]

(* See also GraphState[] *)
QuissoCircuit[a___, g_Graph, b___] := Module[
  { qubits = VertexList[g],
    links  = EdgeList[g] },
  links = links /. { UndirectedEdge -> CZ };
  QuissoCircuit[a, Map[#[6]&] @ qubits, Sequence @@ links, b]
  /; AllTrue[ qubits, QubitQ ]
 ]

(*
 * QuissoCircuit to QuissoExpression
 *)

QuissoCircuit /:
QuissoExpand[ qc_QuissoCircuit ] := QuissoExpand @ QuissoExpression[ qc ]

QuissoCircuit /:
QuissoExpression[ QuissoCircuit[ gg__, ___?OptionQ ] ] := Module[
  { expr = Flatten @ qSansDecor @ {gg} },
  Garner @ QuissoExpand @ QuissoExpression[ qCircuitOperate @@ expr ]
 ]
(* NOTE: This makes the evaluation much faster, especially, when the initial
   state is specified in the circuit. *)

QuissoCircuit /:
Matrix[ QuissoCircuit[ gg__, ___?OptionQ ] ] := Module[
  { expr = Flatten @ qSansDecor @ {gg} },
  qCircuitMatrix[ Qubits @ expr, Sequence @@ expr ]
 ]

QuissoCircuit /:
Matrix[ QuissoCircuit[ gg__, ___?OptionQ ] ] := Module[
  { expr = Flatten @ qSansDecor @ {gg} },
  qcMatrix[ Qubits @ expr, Sequence @@ expr ]
 ]


qCircuitOperate::usage = "..."

qCircuitOperate[a___, M_Measure, b___] := 
  qCircuitOperate[ M @ qCircuitOperate[a], b ]

(* qCircuitOperate[a___, M_Measure, b___] := {qCircuitOperate[a], M, Y[b]} *)

qCircuitOperate[ op:Except[_Measure].. ] := 
  Fold[ Garner @ Multiply[#2, #1]&, 1, {op} ]


qCircuitMatrix::usage = "Based on Matrix[] ..."

qCircuitMatrix[ qq:{__?QubitQ}, a___, M_Measure, b___ ] := With[
  { ss = Qubits @ {a, M} },
  qCircuitMatrix[ qq,
    M @ QuissoExpression[ qCircuitMatrix[ss, a], ss ],
    b ]
 ]

qCircuitMatrix[ qq:{__?QubitQ}, op:Except[_Measure].. ] := Module[
  { new },
  new = Map[Topple] @ Map[Matrix[#, qq]&] @ QuissoExpand @ {op};
  Topple[ Dot @@ new ]
 ]


qcMatrix::usage = "Based on Matrix[] ... "

qcMatrix[ qq:{__?QubitQ}, a___, M_Measure, b___ ] := With[
  { ss = Qubits @ {a, M} },
  qCircuitMatrix[ qq,
    M @ QuissoExpression[ qcMatrix[ss, a], ss ],
    b ]
 ]
qcMatrix[ qq:{__?QubitQ}, op:Except[_Measure].. ] := Module[
  { new },
  new = Map[Topple] @ Map[Matrix[#, qq]&] @ QuissoExpand @ {op};
  Topple[ Dot @@ new ]
 ]


qSansDecor::usage = "..."

SetAttributes[ qSansDecor, Listable ];

(* qSansDecor[ QuissoIn[a__] ]  := qSansDecor @ {a} *)

qSansDecor[ QuissoIn[a__] ]  := Multiply @@ qSansDecor[ {a} ]
(* NOTE: Useful to apply Matrix directly to QuissoCircuit.  *)

qSansDecor[ _QuissoOut ] = Nothing

qSansDecor[ _?OptionQ ] = Nothing

qSansDecor[ Gate[expr_, ___?OptionQ ] ] := expr

qSansDecor[ Projector[v_, ___?OptionQ] ] := Dirac[v, Dagger[v], Qubits @ v]

qSansDecor[ v:ProductState[_Association] ] := Expand[v]

qSansDecor[ g_?NumericQ ] := g

qSansDecor[ g_ ] := Nothing /; FreeQ[ g, _?QubitQ | _Ket | _ProductState ]

qSansDecor[ g_ ] := g


(*
 * Graphical display of circuit
 *)

QuissoCircuit /:
Graphics[
  QuissoCircuit[ gg__, qcOpts___?OptionQ ],
  grOpts___?OptionQ
 ] := Module[
   { ss = ss = Qubits @ {gg},
     (* NOTE: Pure Qubits should be given None index properly. *)
     cc = qCircuitElement @ gg,
     xx, yy, nodes, lines, in, out },

   If[ !ListQ[cc], cc = List @ cc ];
   (* It happens when there is only one circuit element. *)

   If[ cc == {}, cc = {"Spacer"} ];
   (* There could be only input elements for temporary. *)
   
   xx  = Accumulate @ Boole[ qGateQ /@ cc ];
   xx *= $GateDistance;
   $CircuitSize = 1 + Max[xx];
   
   yy = Range[ Length @ ss ] $GateDistance;
   yy = AssociationThread[ss, -yy];
   
   nodes = qCircuitNodes[ cc, xx, yy ];
   lines = qCircuitLines[ cc, xx, yy ];

   in = FirstCase[ {gg}, QuissoIn[kk___] :> {kk} ];
   in = qCircuitInput[ in, xx, yy ];

   out = FirstCase[ {gg}, QuissoOut[kk___] :> {kk} ];
   out = qCircuitOutput[ out, xx, yy ];

   Graphics[ Join[lines, in, nodes, out], qcOpts, grOpts,
     PlotRangePadding -> {$GateDistance/2,0} ]
  ]

qGateQ::usage = "qGateQ[expr] is True if expr is an expression of operators."

qGateQ[expr_] := !FreeQ[expr, _?QubitQ | "Separator" | "Spacer" ]
(* Recall that FreeQ[ Ket[<|...|>], _?QubitQ] = True . *)


qCircuitElement::usage = "Handles various circuit elements."

(* NOTE: Do not set Listable attribute for qCircuitElement. *)

Options[ qCircuitElement ] = {
  "TargetFunction"  -> qGatePane,
  "ControlFunction" -> qGateDot,
  "LabelSize" -> 1, (* RELATIVE size *)
  Label -> None
 }

(* Gate *)
qCircuitElement[ _QuissoIn | _QuissoOut, opts___?OptionQ ] = Nothing
  
qCircuitElement[ S_?QubitQ, opts___?OptionQ ] :=
  Gate[ Qubits @ S, opts, Label -> qGateLabel[S] ]

qCircuitElement[ Measure[ S_?QubitQ ], opts___?OptionQ ] :=
  Gate[ {S}, "TargetFunction" -> qGateMeasure, Label -> None, opts ]

qCircuitElement[ p_Projector, opts___?OptionQ ] :=
  Gate[ Qubits @ p, "TargetFunction" -> qGateProjector, Label -> None, opts ]

qCircuitElement[ Phase[ G_?QubitQ, ang_, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ Qubits @ G, opts, more, Label -> qGateLabel[ Phase[G, ang] ] ]

qCircuitElement[ Rotation[ G_?QubitQ, ang_, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ Qubits @ G, opts, more, Label -> qGateLabel[ Rotation[G, ang] ] ]

qCircuitElement[ EulerRotation[ G_?QubitQ, ang:{_,_,_}, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ {G}, opts, more, Label -> qGateLabel[ EulerRotation[G, ang] ] ]


qCircuitElement[ Controlled[ cc:{__?QubitQ}, S_?QubitQ, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ cc, Qubits @ S, opts, more, Label -> qGateLabel[S] ]

qCircuitElement[ Controlled[ cc:{__?QubitQ}, op:(Phase|Rotation|EulerRotation)[j__, optsA___?OptionQ], optsB___?OptionQ ], optsC___?OptionQ ] :=
  Gate[ cc, Qubits @ op, optsA, optsB, optsC, Label -> qGateLabel[op] ]

qCircuitElement[ Controlled[ cc:{__?QubitQ}, expr_, opts___?OptionQ ], more___?OptionQ ] :=
  Gate[ cc, Qubits[expr], opts, more ] /; !FreeQ[expr, _?QubitQ]


qCircuitElement[ CNOT[c_?QubitQ, t_?QubitQ], opts___?OptionQ ] :=
  Gate[ {c}, {t}, "TargetFunction" -> qGateCirclePlus ]

qCircuitElement[ Toffoli[a_?QubitQ, b__?QubitQ, c_?QubitQ], opts___?OptionQ ] :=
  Gate[ {a, b}, {c}, "TargetFunction" -> qGateCirclePlus ]

qCircuitElement[ CZ[c_?QubitQ, t_?QubitQ], opts___?OptionQ ] :=
  Gate[ {c}, {t}, "ControlFunction" -> qGateDot, "TargetFunction" -> qGateDot ]

qCircuitElement[ SWAP[c_?QubitQ, t_?QubitQ], opts___?OptionQ ] :=
  Gate[ {c}, {t}, "ControlFunction" -> qGateCross, "TargetFunction" -> qGateCross ]

qCircuitElement[ expr:Except[_List|_?(FreeQ[#,_?QubitQ]&)], opts___?OptionQ ] :=
  Gate[ Qubits @ expr, opts ]

qCircuitElement[ z_?NumericQ, opts___?OptinQ ] := "Spacer"

qCircuitElement[ gate:("Separator" | "Spacer"), opts___?OptinQ ] := gate

qCircuitElement[ expr_, opts___?OptinQ ] := expr /; FreeQ[expr, _?QubitQ]
(* Graphics primitives corresponds to this case. *)

qCircuitElement[ a_List, opts___?OptionQ ] := qCircuitElement @@ Join[ a, {opts} ]

qCircuitElement[ a_, b__, opts___?OptionQ ] := Map[ qCircuitElement[#, opts]&, {a, b} ]


qGateLabel::usage = "qGateLabel[G] returns the label of the circuit element to be displayed in the circuit diagram."

qGateLabel[ S_?QubitQ ] := Last[S] /. {
  0 -> "I",
  1 -> "X", 2 -> "Y", 3 -> "Z",
  6 -> "H", 7 -> "S", 8 -> "T" }

qGateLabel[ gate_Phase ] := "\[CapitalPhi]"

qGateLabel[ Rotation[S_?QubitQ, __] ] :=
  Subscript[ "U", FlavorLast[S] /. {1->"x",2->"y",3->"z"} ]

qGateLabel[ EulerRotation[S_?QubitQ, __] ] := Subscript["U", "E"]

qGateCirclePlus::usage = "..."

qGateCirclePlus[ x_, y_, ___ ] := Module[
  { circ, crss },
  circ = Circle[ {x, y}, $GateSize / 3 ];
  crss = Line[ {
      { {x-$GateSize/3,y}, {x+$GateSize/3,y} },
      { {x,y-$GateSize/3}, {x,y+$GateSize/3} }
     } ];
  { circ, crss }
 ]

qGateCross::usage = "..."

qGateCross[ x_, y_, ___ ] := Line[{
    { {x,y}+{-1,-1}$DotSize, {x,y}+{+1,+1}$DotSize },
    { {x,y}+{-1,+1}$DotSize, {x,y}+{+1,-1}$DotSize }
   }]

qGateMeasure::usage = "..."

qGateMeasure[ x_, y_, ___ ] := Module[
  { arc, needle },
  pane = qGatePane[x, y];
  arc = Circle[ {x, y - 0.25 $GateSize}, .5 $GateSize, {1,5} Pi/6 ];
  needle = Line[{ {x, y - 0.25 $GateSize}, {x,y} + .3{1,1}$GateSize }];
  { pane, arc, needle }
 ]

qGateProjector::usage = "..."

qGateProjector[ x_, y1_, y2_, ___ ] := Module[
  { pane, symb },
  pane = Polygon[{
      {x, y2} + $GateSize {+1,+1}/2,
      {x, y2} + $GateSize {-1,+1}/2,
      {x, y1} + $GateSize {-1,-1}/2,
      {x, y1} + $GateSize {+1,-1}/2 }];
  symb = Polygon[{
      {x, y2} + $GateSize {+1,+1}/2,
      {x, y1} + $GateSize {-1,-1}/2,
      {x, y2} + $GateSize {-1,+1}/2,
      {x, y1} + $GateSize {+1,-1}/2 }];
  { White, EdgeForm[], pane, EdgeForm[Black], White, symb }
 ]

qGateDot::usage = " ... "

qGateDot[ x_, y_, ___, opts___?OptionQ ] := Disk[ {x, y}, $DotSize ];

qGatePane::usage = " ... "

qGatePane[ x_, y_, opts___?OptionQ ] := qGatePane[ x, y, y, opts ]

qGatePane[ x_, y1_, y2_, opts___?OptionQ ] := Module[
  { pane },
  pane = Rectangle[
    {x, y1} - 0.5{1,1}$GateSize,
    {x, y2} + 0.5{1,1}$GateSize ];
  { EdgeForm[Black], White, pane }
 ]

qGateText::usage = " ... "

qGateText[ label_, {x_, y_}, opts___?OptionQ ] := With[
  { factor = "LabelSize" /. {opts} /. Options[qCircuitElement] },
  Text[
    Style[ label, Italic, opts,
      FontWeight -> "Light",
      FontSize   -> Scaled[(0.6 $GateSize / $CircuitSize) factor] ],
    {x, y},
    {0, 0.2} (* Notice the y-offset; y-offset=0 shifts a bit upward. *)
   ]
 ]

qCircuitNodes::usage = "qCircuitNodes[ ... ] takes circuit elements and construct them as nodes of the circuit diagram by assigning horizontal and vertical coordinates to them."

qCircuitNodes[ gg_List, xx_List, yy_Association ] := Module[
  { ff, F },
  
  ff = Thread[ F[ gg, xx, yy ] ];
  ff = ff /. { F -> qDrawElement };

  Return[ff];
 ]

qDrawElement::uage = "..."

qDrawElement[ gg_List, x_, yy_Association ] := Map[ qDrawElement[#, x, yy]&, gg ]

qDrawElement[ Gate[cc:{__?QubitQ}, tt:{__?QubitQ}, opts___?OptionQ], x_, yy_Association ] := Module[
  { yc = Lookup[yy, cc],
    yt = Lookup[yy, tt],
    control, dots, link, pane },

  control = "ControlFunction" /. {opts} /. Options[qCircuitElement];
  
  dots = control @@@ Thread[ {x, yc} ];
  
  link = Line @ Join[ Thread[ {x, yc} ], Thread[ {x, yt} ] ];

  pane = qDrawElement[ Gate[tt, opts], x, yy ];
  
  Join[ dots, {link}, pane]
 ]


qDrawElement[ Gate[tt:{__?QubitQ}, opts___?OptionQ], x_, yy_Association ] := Module[
  { zz = MinMax @ Lookup[yy, tt],
    target, label, pane, text },
  { target, label } = { "TargetFunction", Label } /. {opts} /. Options[qCircuitElement];
  
  pane = target[x, Sequence @@ zz];
  
  text = If[ label === None, Nothing, qGateText[label, {x, Mean @ zz}, opts] ];
  
  {pane, text}
 ]

qDrawElement[ "Spacer", _, _Association ] = Nothing

qDrawElement[ "Separator", x_, yy_Association ] := Module[
  { xy = Tuples[{{x}, MinMax @ yy }] },
  { Dotted, Line[{ {0,-$GateDistance/2} + First @ xy, {0,+$GateDistance/2} + Last @ xy }] }
 ]

qDrawElement[ g_, x_, yy_Association ] := g


qCircuitLines::usage = "qCircuitLines[xmax, x, y] finds when Measure occurs in the QuissoCircuit and renders the qubit line after Measure in dashes."

qCircuitLines[ gg_List, xx_List, yy_Association ] := Module[
  { mm, zz, dashed, plain },
  
  (* mm = Map[ Cases[{#}, Measure[___,S_?QubitQ] -> S, Infinity]&, gg ]; *)
  mm = Map[ Cases[{#}, Gate[{S_?QubitQ}, "TargetFunction" -> qGateMeasure, ___?OptionQ] -> S, Infinity]&, gg ];
  mm = Flatten[ Thread /@ Thread[ mm -> xx ] ];
  mm = KeySort @ Association @ mm;
  
  zz = Lookup[yy, Keys @ mm];
  dashed = Line @ Transpose @ {
    Thread[ {Values @ mm, zz} ],
    Thread[ {1+Max[xx], zz} ] };

  plain = Association @ Thread[ Keys[yy] -> 1+Max[xx] ];
  plain = Join[ plain, mm ];
  plain = Line @ Transpose @ {
    Thread[{0, Values @ yy}],
    Transpose @ {Values @ plain, Values @ yy} };

  {{Dashed, dashed}, plain}
 ]


qCircuitOutput::usage = "It draws the output states behind the scene."

qCircuitOutput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitOutput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{$CircuitSize + $InOutOffset, #}&, yy],
    ff = List @ qCircuitPort @ gg },
  Map[ qDrawPort[#, xy]&, ff ]
 ]


qCircuitInput::usage = "It draws the input states behind the scene."

qCircuitInput[ Missing["NotFound"], xx_List, yy_Association ] = {}

qCircuitInput[ gg:{___}, xx_List, yy_Association ] := Module[
  { xy = Map[{-$InOutOffset, #}&, yy],
    ff },
  
  (* ff = Join[ff, {"Pivot" -> {1,0}, "Type" -> -1} ]; *)
  ff = Join[gg, {"Pivot" -> {1,0}, "Type" -> -1} ];
  ff = List @ qCircuitPort @ ff;

  Map[ qDrawPort[#, xy]&, ff ]
 ]


qCircuitPort::usage = "Handles various input and output forms of QuissoCircuit."

Options[ qCircuitPort ] = {
  Label -> Automatic,
  "Pivot" -> {-1, 0},
  "Type"  -> 1 (* 1: input, -1: output *)
 }

qCircuitPort[ v_Ket, opts___?OptionQ ] := Port[v, opts]

qCircuitPort[ v_ProductState, opts___?OptionQ ] := Port[v, opts]

qCircuitPort[ expr:Except[_List|_?(FreeQ[#,_Ket]&)], opts___?OptionQ ] := Port[expr, opts]

qCircuitPort[ a_List, opts___?OptionQ ] := qCircuitPort @@ Join[a, {opts}]

qCircuitPort[ g_, opts___?OptionQ ] := g /; FreeQ[g, _Ket | _ProductState]

qCircuitPort[ a_, b__, opts___?OptionQ ] :=
  Map[ qCircuitPort[#, opts]&, {a, b} ]


qCircuitPort[ v_Ket ] := Port @ v

qCircuitPort[ v_ProductState ] := Port @ v


qCircuitPort[ expr:Except[_List|_?(FreeQ[#,_Ket]&)] ] := Port @ expr


qDrawPort::usage = "..."

qDrawPort[ gg_List, xy_Association ] := Map[ qDrawPort[#, xy]&, gg ]

qDrawPort[ Port[ Ket[v_], opts___?OptionQ ], xy_Association ] := Module[
  { vv = Ket /@ v,
    tt, label, pivot },
  { label, pivot } = {Label, "Pivot"} /. {opts} /. Options[qCircuitPort];
  
  tt = If [ label === Automatic, vv,
    If[ Not @ ListQ @ label, label = {label} ];
    AssociationThread[ Keys[v] -> PadRight[label, Length[v], label] ]
   ];
  
  Values @ MapThread[ Text[#1, #2, pivot]&, KeyIntersection[{tt, xy}] ]
 ]

qDrawPort[ Port[ ProductState[v_Association], opts___?OptionQ ],
  xy_Association ] := Module[
  { label, pivot, tt },
  { label, pivot } = {Label, "Pivot"} /. {opts} /. Options[qCircuitPort];

  tt = If [ label === Automatic,
    Map[ Simplify @ Dot[{Ket[0], Ket[1]}, #]&, v ],
    If[ Not @ ListQ @ label, label = {label} ];
    AssociationThread[ Keys[v] -> PadRight[label, Length[v], label] ]
   ];
  
  Values @ MapThread[ Text[#1, #2, pivot]&, KeyIntersection[{tt, xy}] ]
 ]

QuissoCircuit::noqubit = "No Qubit found in the expression ``. Use LogicalForm to specify the Qubits explicitly."

qDrawPort[ Port[ expr_, opts___?OptionQ ], xy_Association ] := Module[
  { qq = Qubits @ expr,
    label, pivot, dir, brace, text, zz },

  { label, pivot, dir } = { Label, "Pivot", "Type" } /. {opts} /. Options[qCircuitPort];
  
  If[ qq == {},
    Message[QuissoCircuit::noqubit, expr];
    Return[ {} ];
   ];
  
  text = If [ label === Automatic, qNormalKet[expr], label ];
  
  zz = Transpose[ MinMax /@ Transpose @ Lookup[xy, qq] ];
  
  If[ Length[qq] > 1,
    brace = qPortBrace[dir, zz];
    zz = Mean @ zz + ($InOutOffset + $BraceWidth) {dir, 0};
    { brace, Text[text, zz, pivot] },
    Text[text, Mean @ zz, pivot]
   ]
 ]

qDrawPort[ g_, xy_Association ] := g


qPortBrace[ dir:(-1|1), { a:{_, _}, b:{_, _} } ] :=
  Line[{ a, a + $BraceWidth {dir, 0}, b + $BraceWidth {dir, 0}, b }]

qNormalKet[ expr_ ] := LogicalForm[expr] /. { Ket[a_Association] :> Ket @@ Values[a] }

End[] (* `Circuit`*)



Begin["`Special`"]

(* QuissoNormalState *)

QuissoNormalState::usage = "QuissoNormalState[expr] or QuissoNormalState[expr, {S1, S2, ...}] gives the normal form (also known as standard form) of the given state specified by expr. See, e.g., Kraus (PRL, 2010; PRA, 2010). In Martins (PRA, 2015), it is called a reference form."

QuissoNormalState[ expr_ ] := Module[
  (* expr: Ket[] expression *)
  { ss = Qubits @ expr },
  Fold[ QuissoNormalState, expr, ss ]
 ]

QuissoNormalState[v_, S_?QubitQ] := Module[
  { p, u, m, op },
  m = Matrix @ QuissoReduced[v, {S}];
  {p, u} = Eigensystem[m];
  u = Transpose[ Normalize /@ u ];
  op = QuissoExpression[ u, {S} ];
  Simplify[ Dagger[op] ** v ]
 ]

(* QuissoCorrelationTensor *)

QuissoCorrelationTensor::usage = "QuissoCorrelationTensor[v] gives the Association of the Pauli decomposition coefficients for the density matrix corresponding to the pure state a. The pure state vector should be given in a Ket expression."

(* Method 1: This is fast, but results in "Recursion depth of 1024 exceeded
   during evaluation of ..." error when the state vector includes many terms
   for a large number of qubits. *)

(*
QuissoCorrelationTensor[v_] :=
  QuissoCoefficientTensor[ QuissoExpression @ Dirac[v, Dagger[v]] ]

QuissoCorrelationTensor[v_, n_Integer] :=
  QuissoCoefficientTensor[ QuissoExpression @ Dirac[v, Dagger[v]], n ]

QuissoCorrelationTensor[v_, {n_Integer}] :=
  QuissoCoefficientTensor[ QuissoExpression @ Dirac[v, Dagger[v]], {n} ]
 *)

(* Method 2: This is slower than Method 1 above, but does not suffer from the
   recursion limit error. *)

QuissoCorrelationTensor[v_] :=  With[
  { qq = Qubits @ v },
  QuissoCorrelationTensor[v, Length[qq]]
 ]

QuissoCorrelationTensor[v_, n_Integer] := 
 Join @@ Table[ QuissoCorrelationTensor[v, {k}], {k, 0, n} ]

QuissoCorrelationTensor[v_, {0}] := With[
  { qq = Qubits @ v },
  Association[{1} -> Multiply[Dagger[v], v] Power[2, -Length[qq]]]
 ]

QuissoCorrelationTensor[v_, {n_Integer}] := Module[
  { qq = Qubits @ v,
    nn, op, jj, cc },
  nn = Length @ qq;
  qq = FlavorNone @ Subsets[qq, {n}];
  jj = Map[(#[All]) &, qq, {2}];
  op = Map[Outer[Multiply, Sequence @@ #, 1] &, jj];
  cc = Dagger[v] ** op ** v;
  Association[Thread[qq -> cc]] Power[2, -nn]
 ]


(* QuissoCorrelationMatrix *)

QuissoCorrelationMatrix::usage = "QuissoCorrelationMatrix[a] analyses the correlation tesnor in the Association a; it takes the product of each tensor with itself and contract over the indices but two belonging to the same quibt. The result is an Association of 3x3 matrices describing the transformation of the state vector (associated with the Association a) under local unitary (LU) transformations. The association a is usually generated by QuissoCoefficientTensor[] or QuissoCorrelationTensor[]."

QuissoCorrelationMatrix[a_Association] := Module[
  { aa },
  aa = DeleteCases[ QuissoCorrelationMatrix /@ a, Nothing ];
  aa = Merge[ KeyValueMap[Thread[#1 -> #2]&, aa], Join ];
  (* DeleteCases[ aa, (ZeroMatrix[3] | IdentityMatrix[3]), 2 ] *)
  Return[aa];
 ]

QuissoCorrelationMatrix[T_] := Nothing /; TensorRank[T] < 2 

QuissoCorrelationMatrix[T_] := Module[
  { n = TensorRank[T],
    TT = TensorProduct[T, T],
    kk, CC },
  kk = Reverse @ Subsets[Range[n], {n - 1}];
  kk = Map[Transpose[{#, # + n}] &, kk];
  CC = TensorContract[TT, #] & /@ kk;
  Power[2,2n] CC (* make elements order of unity *)
 ]


CommonEigensystem::usage = "CommonEigensystem[{m$1, m$2, ...}] finds the simultaneous eigenvectors and corresponding eigenvales of the mutually commuting square matrices."

CommonEigensystem[ mm:{__?MatrixQ} ] := Module[
  { val, U },
  U = Fold[ CommonEigensystem, IdentityMatrix[Length @ First @ mm], mm ];
  (* Print[ Det[U] ]; *)
  If[ Det[U] < 0, U[[All,3]] *= -1 ];
  val = Map[ Diagonal[ Topple[U].#.U ]&, mm ];
  {val, U}
 ]

CommonEigensystem[U_?MatrixQ, m_?MatrixQ] := Module[
  { val, vec },
  { val, vec } = Eigensystem[ Topple[U].m.U ];
  U.Transpose[vec]
 ]

End[] (* `Special` *)


Begin["`Qudit`"]

$symbs = Unprotect[
  Multiply, MultiplyDegree, Dyad,
  Basis, Matrix, Parity, ParityEvenQ, ParityOddQ,
  $GarnerHeads, $GarnerTests, $RepresentableTests,
  Base, FlavorNone, FlavorMute,
  KetRule, KetTrim, Missing,
  ReplaceByFourier, ReplaceByInverseFourier
 ]

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

  Kind[x] ^= Qudit;
  Kind[x[___]] ^= Qudit;
  
  Dimension[x] ^= dim;
  Dimension[x[___]] ^= dim;

  x /: Power[x, n_Integer] := MultiplyPower[x, n];
  x /: Power[x[j___], n_Integer] := MultiplyPower[x[j], n];

  x[j___, ij:Rule[_List, _List]] := x[j, Thread @ ij];
  x[j___, All] := x[j, Rule @@@ Tuples[Range[0, dim-1], 2]];
  
  x[j___, Null] := x[j, None];
  x[j___, None, k_] := x[j, k];
  (* In particular, x[j,None,None] = x[j,None]. *)

  x /: Dagger[ x[j___, Rule[a_Integer, b_Integer]] ] := x[j, Rule[b,a]];

  x[j___, Rule[a_Integer, b_Integer]] := (
    Message[Qudit::range, dim, x[j,None]];
    0
   ) /; Or[ a < 0, a >= Dimension[x], b < 0, b >= Dimension[x] ];

  Format[ x[j___, None] ] := DisplayForm @ SpeciesBox[x, {j}, {}];  
  Format[ x[j___, 0] ] := DisplayForm @ SpeciesBox[1, {j}, {0}];  
  Format[ x[j___, a_->b_] ] :=
    DisplayForm @ SpeciesBox[ RowBox @ {"(",Ket[b],Bra[a],")"}, {j}, {}];  
 )

QuditQ[_] = False

Missing["KeyAbsent", _Symbol?QuditQ[___, None]] := 0


Qudits::usage = "Qudits[expr] gives the list of all qudits appearing in expr."

Qudits[ expr_ ] := FlavorNone @ Union @ Map[Most] @
  Cases[ Normal[{expr}, Association], _?QuditQ, Infinity ]
(* NOTE: { } are necessary around expr; otherwise, Qudits[S[1,2]] does
   not give the trivial result. *)


(* MultiplyDegree for operators *)
MultiplyDegree[_?QuditQ] = 1


Dyad[A_?QuditQ][m_Integer -> n_Integer] := A[m->n]


(* Base: See Cauchy *)

Base[ S_?QuditQ[j___, _] ] := S[j]
(* For Qudits, the final Flavor index is special. *)


(* FlavorNone: See Cauchy *)

FlavorNone[S_?QuditQ] := S[None]

FlavorNone[S_?QuditQ -> m_] := S[None] -> m


(* FlavorMute: See Cauchy *)

FlavorMute[S_Symbol?QuditQ] := S[None]

FlavorMute[S_Symbol?QuditQ[j___, _]] := S[j, None]

FlavorMute[S_Symbol?QuditQ[j___, _] -> m_] := S[j, None] -> m


(* Ket[] for Qudits *)

KetRule[ r:Rule[_?QuditQ, _] ] := FlavorNone[r]

KetRule[ r:Rule[{__?QuditQ}, _] ] := FlavorNone @ Thread[r]

KetTrim[_?QuditQ, 0] = Nothing

KetTrim[A_?QuditQ, s_Integer] := (
  Message[Qudit::range, Dimension[A], FlavorNone @ A];
  Nothing
 ) /; s >= Dimension[A]


(* Qudit on Ket *)

HoldPattern @
  Multiply[pre___, op_?QuditQ, Ket[a_Association, b_List], post___] :=
  With[
    { new = Restrict[ Multiply[op, Ket[a]], b ] },
    Multiply[pre, new, post]
   ] /; MemberQ[b, FlavorMute @ op]


HoldPattern @
  Multiply[a___, S_?QuditQ[j___, Rule[x_,y_]], v:Ket[_Association], b___] :=
  Multiply[a, v[S[j,None] -> y], b] /; v[S[j,None]] == x
(* TODO: handle symbolic flavors x*)

HoldPattern @
  Multiply[a___, S_?QuditQ[j___, Rule[x_,y_]], v:Ket[_Association], b___] :=
  0 /; v[S[j,None]] != x
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


Once[
  $GarnerTests = Join[$GarnerTests, {QuditQ}];
  $RepresentableTests = Join[$RepresentableTests, {QuditQ}];
 ]


Basis[ S_?QuditQ ] := Basis @ {S}

Basis[ qq : {__?QuditQ} ] := Module[
  { rr = FlavorNone @ qq,
    dd = Dimension @ qq  },
  dd = Tuples @ Map[ Range[0,#-1]&, dd ];
  Map[ Ket[rr->#]&, dd ]
 ]


TheQuditKet::usage = "TheQuditKet[{J,M,th,ph}] is the rotated-frame version of TheQuditKet[{J,M}].\nTheQuditKet[{j1,m1,t1,p1}, {j2,m2,t2,p2}, ...] returns CircleTimes of the vectors  indicated by the indices.\nTheQuditKet[{J, {m1,m2,...}, th, ph}] = TheQuditKet[{J,m1,th,ph}, {J,m2,th,ph}, ...]."

TheQuditKet[ {dim_Integer, val_Integer} ] :=
  UnitVector[dim, val+1] /; 0 <= val < dim

TheQuditKet[ {dim_Integer, m:{__Integer}} ] :=
  TheQuditKet @@ Tuples[ {{dim}, m} ]

TheQuditKet[ a:{_Integer, _Integer} .. ] := Module[
  { aa = Transpose @ {a},
    dd, pwrs, bits, p},
  dd = First @ aa;
  pwrs = Reverse @ FoldList[ Times, 1, Reverse @ Rest @ dd ];
  bits = Last @ aa;
  p = 1 + bits.pwrs;
  Normal @ SparseArray[ {p -> 1}, Times @@ dd ]
 ]


(* ******************************************************************** *)

Parity[A_?QuditQ] := Module[
  { jj = Range[0, Dimension[A]-1],
    op },
  op = A /@ Thread[jj->jj];
  Power[-1, jj] . op
 ]


ParityEvenQ[v_Ket, a_?QuditQ] := EvenQ @ v @ a

ParityOddQ[v_Ket, a_?QuditQ] := OddQ @ v @ a


(* ******************************************************************* *)

(* Matrix[] for Qudits *)

Matrix[ S_?QuditQ[___, i_ -> j_] ] :=
  SparseArray[ {1+j,1+i} -> 1, Dimension[S] {1, 1} ]

Matrix[ Ket[ Association[ S_?QuditQ -> n_Integer] ] ] := SparseArray[
  If[ 0 <= n < Dimension[S], n+1 -> 1, {}, {} ],
  Dimension[S]
 ]

(* ******************************************************************** *)


QuditExpression::usage = "QuditExpression[expr] converts Ket[...]**Bra[...]  for in the expression expr to the form in terms of the Gate operators.\nQuditExpression[m, {S$1, S$2, ...}] converts the square matrix m into a Qudit expression.\nQuditExpression[v, {S$1, S$2, ...}] converts the column vector v into a Ket expression."

(* Let[LinearMap, QuditExpression] *)
(* NOTE: When there are many terms, larger than 512?,
   strange $RecursionLimit::reclim2 error occurs.*)

QuditExpression[ a_ + b_ ] := QuditExpression[a] + QuditExpression[b] 

QuditExpression[ z_?ComplexQ ] := z

QuditExpression[ z_?ComplexQ a_ ] := z QuditExpression[a]

QuditExpression::incon = "The matrix/vector `1` is not compatible with the Qudit list `2`."

QuditExpression[ m_?MatrixQ, S_?QuditQ ] := QuditExpression[ m, {S} ]

QuditExpression[ m_?MatrixQ, ss:{__?QuditQ} ] := Module[
  { nL = Times @@ Dimension @ ss,
    mm = SparseArray[ ArrayRules[m], Dimensions[m] ],
    tt, op, tensor, HoldTimes },

  If[ Dimensions[m] != {nL, nL},
    Message[QuditExpression::incon, m, FlavorNone @ ss];
    Return[0]
   ];
  
  tensor = Tensorize[ mm, Join[Dimension @ ss, Dimension @ ss] ];
  tt = Map[
    Function[ {S},
      Table[ S[j->i], {i, 0, Dimension[S]-1}, {j, 0, Dimension[S]-1}]
     ],
    ss ];
  op = Outer[ HoldTimes, Sequence @@ tt ];
  Expand[ Total @ Flatten[tensor * op] /. {HoldTimes -> Multiply} ]
 ]

QuditExpression[ v_?VectorQ, S_?QuditQ ] := QuditExpression[ v, {S} ]

QuditExpression[ v_?VectorQ, ss:{__?QuditQ} ] := Module[
  { nL = Times @@ Dimension @ ss,
    tt = FlavorNone[ss],
    basis },

  If[ Length[v] != nL,
    Message[QuditExpression::incon, v, FlavorNone @ ss];
    Return[{0}]
   ];
  
  basis = Basis[tt];
  Dot[v, basis]
 ]

QuditExpression[ expr_ ] := expr


ReplaceByFourier[old_?QuditQ -> new_?QuditQ, opts___?OptionQ] := Module[
  { mm = FourierMatrix[Dimension @ old, opts],
    ij = Range[0, Dimension[old]-1],
    aa, bb },  
  aa = old[All];
  bb = Outer[new[#1 -> #2]&, ij, ij];
  bb = Flatten[ Topple[mm] . bb . mm ];
  Thread[aa -> bb]
 ]

ReplaceByFourier[
  a:Rule[_?QuditQ, _?QuditQ],
  b:Rule[_?QuditQ, _?QuditQ]..,
  opts___?OptionQ] := Map[ ReplaceByFourier[#, opts]&, {a, b} ]

ReplaceByFourier[expr_, old_?QuditQ -> new_?QuditQ, opts___?OptionQ] :=
  Garner[ expr /. ReplaceByFourier[old -> new, opts] ]


Protect[ Evaluate @ $symbs ]

End[] (* `Qudit` *)



Q3`Quisso`Prelude`symbs = Protect[Evaluate[$Context<>"*"]]

SetAttributes[Evaluate[Q3`Quisso`Prelude`symbs], ReadProtected]

EndPackage[]
